#!/usr/bin/env python3
# encoding: utf-8

from __future__ import annotations

__author__ = "ChenyangGao <https://chenyanggao.github.io>"
__all__ = ["FileResource", "FolderResource", "P123FileSystemProvider"]

from collections import defaultdict
from re import compile as re_compile
from threading import Lock
from time import time
from urllib.parse import parse_qsl, quote, urlsplit

from cachedict import LRUDict, TLRUDict
from p123client import P123Client
from p123client.tool import iterdir, share_iterdir, share_iter
from property import locked_cacheproperty
from wsgidav.wsgidav_app import WsgiDAVApp # type: ignore
from wsgidav.dav_error import DAVError # type: ignore
from wsgidav.dav_provider import DAVCollection, DAVNonCollection, DAVProvider # type: ignore


CRE_MAYBE_SHARE_match = re_compile("[a-zA-Z0-9]{4,}-[a-zA-Z0-9]{4,}(?::.{4})?").fullmatch
INSTANCE_CACHE: LRUDict[str, FileResource | FolderResource] = LRUDict(65536)
URL_CACHE: TLRUDict[tuple[str, int], str] = TLRUDict(1024)


class DavPathBase:

    def __getattr__(self, attr: str, /):
        try:
            return self.attr[attr]
        except KeyError as e:
            raise AttributeError(attr) from e

    @locked_cacheproperty
    def creationdate(self, /) -> float:
        return self.attr.get("ctime") or 0

    @locked_cacheproperty
    def md5(self, /) -> str:
        return self.attr.get("md5") or ""

    @locked_cacheproperty
    def id(self, /) -> int:
        return self.attr.get("id") or 0

    @locked_cacheproperty
    def mtime(self, /) -> float:
        return self.attr.get("mtime") or 0

    @locked_cacheproperty
    def name(self, /) -> str:
        return self.attr.get("name") or ""

    @locked_cacheproperty
    def share_key(self, /) -> str:
        return self.attr.get("share_key") or ""

    @locked_cacheproperty
    def share_pwd(self, /) -> str:
        return self.attr.get("share_pwd") or ""

    @locked_cacheproperty
    def size(self, /) -> int:
        return self.attr.get("size") or 0

    def get_creation_date(self, /) -> float:
        return self.creationdate

    def get_display_name(self, /) -> str:
        return self.name

    def get_last_modified(self, /) -> float:
        return self.mtime

    def is_link(self, /) -> bool:
        return False


class FileResource(DavPathBase, DAVNonCollection):

    def __init__(
        self, 
        /, 
        path: str, 
        environ: dict, 
        attr: dict, 
    ):
        super().__init__(path, environ)
        self.attr = attr
        INSTANCE_CACHE[path] = self

    @property
    def url(self, /) -> str:
        key = (self.md5, self.size)
        if pair := URL_CACHE.get(key):
            return pair[1]
        url = self.environ["client"].download_url({
            "Etag": self.md5, 
            "Size": self.size, 
            "S3KeyFlag": self.attr["s3keyflag"], 
            "FileName": self.name, 
        })
        expire_ts = int(next(v for k, v in parse_qsl(urlsplit(url).query) if k == "t")) - 60 * 5
        URL_CACHE[key] = (expire_ts, url)
        return url

    def get_content(self, /):
        raise DAVError(302, add_headers=[("location", self.url)])

    def get_content_length(self, /) -> int:
        return self.size

    def get_etag(self, /) -> str:
        return self.md5

    def support_content_length(self, /) -> bool:
        return True

    def support_etag(self, /) -> bool:
        return True

    def support_ranges(self, /) -> bool:
        return True


class FolderResource(DavPathBase, DAVCollection):

    def __init__(
        self, 
        /, 
        path: str, 
        environ: dict, 
        attr: dict, 
    ):
        super().__init__(path, environ)
        self.attr = attr
        INSTANCE_CACHE[path] = self
        self._children_lock = Lock()
        self._last_children_ts: float = 0

    @property
    def children(self, /) -> dict[str, FileResource | FolderResource]:
        environ = self.environ
        with self._children_lock:
            cached_children = self.__dict__.get("children")
            if cached_children and (self._last_children_ts + environ["ttl"]) > time():
                return cached_children
            children: dict[str, FileResource | FolderResource] = {}
            dirname = self.path
            if dirname == "/":
                children["0"] = FolderResource("/0", environ, {
                    "id": 0, 
                    "parent_id": 0, 
                    "name": "0", 
                    "is_dir": 1, 
                })
                for attr in share_iter(environ["client"]):
                    name = attr["share_key"]
                    if share_pwd := attr["share_pwd"]:
                        name += ":" + share_pwd
                    attr.update({
                        "is_dir": 1, 
                        "id": 0, 
                        "parent_id": 0, 
                        "name": name, 
                    })
                    children[name] = FolderResource("/" + name, environ, attr)
            else:
                dirname += "/"
                if not environ["refresh"] and cached_children:
                    if self.share_key:
                        it = share_iterdir(
                            self.share_key, 
                            self.share_pwd, 
                            {"parentFileId": self.id, "orderBy": "update_at", "orderDirection": "desc"}, 
                        )
                    else:
                        it = iterdir(
                            environ["client"], 
                            {"parentFileId": self.id, "orderBy": "update_at", "orderDirection": "desc"}, 
                            list_method="list_new", 
                        )
                    seen_ids: set[int] = set()
                    cached_ids: set[int] = {inst.attr["id"] for inst in cached_children.values()}
                    children_grouped: dict[int, dict[int, FolderResource | FileResource]] = defaultdict(dict)
                    for inst in cached_children.values():
                        children_grouped[inst.attr["mtime"]][inst.attr["id"]] = inst
                    his_it = iter(children_grouped.items())
                    his_mtime, his_items = next(his_it)
                    remains = len(cached_children)
                    n = 0
                    for attr in it:
                        cur_id = attr["id"]
                        seen_ids.add(cur_id)
                        name = attr["name"]
                        path = dirname + name
                        if attr["is_dir"]:
                            children[name] = FolderResource(path, environ, attr)
                        else:
                            children[name] = FileResource(path, environ, attr)
                        if remains:
                            n += 1
                            cur_mtime = attr["mtime"]
                            try:
                                while his_mtime > cur_mtime:
                                    remains -= len(his_items)
                                    cached_ids.difference_update(his_items)
                                    his_mtime, his_items = next(his_it)
                            except StopIteration:
                                continue
                            if total_siblings := attr.get("total_siblings"):
                                if his_mtime == cur_mtime:
                                    if cur_id in his_items:
                                        his_items.pop(cur_id)
                                        cached_ids.discard(cur_id)
                                        remains -= 1
                                    if n + remains == total_siblings and not (seen_ids & cached_ids):
                                        for inst in his_items.values():
                                            children[inst.attr["name"]] = inst
                                        for his_mtime, his_items in his_it:
                                            for inst in his_items.values():
                                                children[inst.attr["name"]] = inst
                                        break
                            elif cur_mtime == his_mtime and seen_ids & cached_ids == {cur_id}:
                                his_items.pop(cur_id)
                                for inst in his_items.values():
                                    children[inst.attr["name"]] = inst
                                for his_mtime, his_items in his_it:
                                    for inst in his_items.values():
                                        children[inst.attr["name"]] = inst
                                break
                else:
                    if self.share_key:
                        it = share_iterdir(self.share_key, self.share_pwd, self.id)
                    else:
                        it = iterdir(environ["client"], self.id)
                    for attr in it:
                        name = attr["name"]
                        path = dirname + name
                        if attr["is_dir"]:
                            children[name] = FolderResource(path, environ, attr)
                        else:
                            children[name] = FileResource(path, environ, attr)
            self.__dict__["children"] = children
            self._last_children_ts = time()
            return children

    def get_member(self, /, name: str) -> None | FileResource | FolderResource:
        if obj := self.children.get(name):
            return obj
        return None

    def get_member_list(self, /) -> list[FileResource | FolderResource]:
        return list(self.children.values())

    def get_member_names(self, /) -> list[str]:
        return list(self.children)

    def get_property_value(self, /, name: str):
        if name == "{DAV:}getcontentlength":
            return 0
        elif name == "{DAV:}iscollection":
            return True
        return super().get_property_value(name)


class P123FileSystemProvider(DAVProvider):

    def __init__(
        self, 
        /, 
        username: str = "", 
        password: str = "", 
        token: None | str = None, 
        ttl: float = 10, 
        refresh: bool = False, 
    ):
        super().__init__()
        self.client = P123Client(username, password, token=token)
        self.ttl = ttl
        self.refresh = refresh

    def get_resource_inst(
        self, 
        /, 
        path: str, 
        environ: dict, 
    ) -> None | FolderResource | FileResource:
        share_key = share_pwd = ""
        query = environ["QUERY_STRING"]
        if query and query.startswith(("http://", "https://")):
            urlp = urlsplit(query)
            share_key = urlp.path.rsplit("/", 1)[-1]
            if not share_pwd:
                query = urlp.query
                if "pwd=" in query:
                    for k, v in parse_qsl(query):
                        if k == "pwd":
                            share_pwd = v[:4]
                if not share_pwd:
                    maybe_pwd = urlp.query.rpartition(":")[-1]
                    if len(maybe_pwd) == 4:
                        share_pwd = maybe_pwd
        parts = [p for p in path.split("/") if p]
        if share_key:
            part = share_key
            if share_pwd:
                part += ":" + share_pwd
            parts.insert(0, part)
        path = "/" + "/".join(parts)
        if query:
            raise DAVError(302, add_headers=[("location", quote(path))])
        if inst := INSTANCE_CACHE.get(path):
           return inst
        environ["client"] = self.client
        environ["ttl"] = self.ttl
        environ["refresh"] = self.refresh
        if not parts:
            return FolderResource("/", environ, {
                "id": 0, 
                "parent_id": 0, 
                "name": "", 
                "is_dir": 1, 
            })
        scope = parts[0]
        if len(parts) == 1 and scope in ("favicon.ico", "service-worker.js"):
            return None
        if CRE_MAYBE_SHARE_match(scope):
            share_key, _, share_pwd = scope.partition(":")
            top_attr = {
                "share_key": share_key, 
                "share_pwd": share_pwd, 
                "id": 0, 
                "parent_id": 0, 
                "name": scope, 
                "is_dir": 1, 
            }
        else:
            if scope != "0":
                parts.insert(0, "0")
                path = "/0" + path
                scope = "0"
            top_attr = {
                "id": 0, 
                "parent_id": 0, 
                "name": "0", 
                "is_dir": 1, 
            }
        top_inst = FolderResource("/" + scope, environ, top_attr)
        if len(parts) == 1:
            return top_inst
        for i in range(1, len(parts))[::-1]:
            dir_ = "/" + "/".join(parts[:i])
            if inst := INSTANCE_CACHE.get(dir_):
                if not isinstance(inst, FolderResource):
                    return None
                break
        inst = inst or top_inst
        for name in parts[i:]:
            if not isinstance(inst, FolderResource):
                return None
            inst = inst.get_member(name)
        return inst

# TODO: 数据缓存到数据库中，很多地方参照 p115servedb
# TODO: 支持扫码登录
# TODO: 可以指定配置文件、服务器、端口等配置
# TODO: 让 p115dav 也可以用这种办法挂载任意分享链接
# TODO: 支持 fuse 挂载
# TODO: 支持除了上传外的所有方法（不支持上传，因为这个操作会极大影响性能）
