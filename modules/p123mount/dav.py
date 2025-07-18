#!/usr/bin/env python3
# encoding: utf-8

from __future__ import annotations

__author__ = "ChenyangGao <https://chenyanggao.github.io>"
__version__ = (0, 0, 0)

from argparse import ArgumentParser, RawTextHelpFormatter

parser = ArgumentParser(description="123 WebDav", formatter_class=RawTextHelpFormatter, epilog="""\
✈️ 关于登录

登录时，可以选择其一：
    1. 账号密码（-u/--user 和 -p/--password）
    2. 访问令牌（-t/--token）

🔨 关于使用

当你访问首页时，会罗列你的网盘入口（路径为 /0）和所有分享入口（路径为 /分享码 或 /分享码:密码）

    http://localhost:8123/

当你访问这个链接路径之下，就是你自己网盘的文件

    http://localhost:8123/0/网盘下的路径

当你访问这个路径之下，则是这个分享下的文件

    http://localhost:8123/分享码/分享下的路径
    http://localhost:8123/分享码:密码/分享下的路径

你可以随意指定一个有效的分享码和路径，而不用管这个分享是不是你自己创建的
""")
parser.add_argument("-u", "--user", default="", help="登录账号，手机号或邮箱")
parser.add_argument("-p", "--password", default="", help="登录密码")
parser.add_argument("-t", "--token", default="", help="123 网盘的 access_token")

args = parser.parse_args()

from datetime import datetime
from re import compile as re_compile
from urllib.parse import parse_qsl, urlsplit

from cachedict import LRUDict, TLRUDict
from p123client import P123Client
from p123client.tool import iterdir, share_iterdir
from property import locked_cacheproperty
from wsgidav.wsgidav_app import WsgiDAVApp # type: ignore
from wsgidav.dav_error import DAVError # type: ignore
from wsgidav.dav_provider import DAVCollection, DAVNonCollection, DAVProvider # type: ignore
from wsgidav.server.server_cli import SUPPORTED_SERVERS # type: ignore


CRE_MAYBE_SHARE_match = re_compile("[a-zA-Z0-9]{4,}-[a-zA-Z0-9]{4,}(?::.{4})?").fullmatch
INSTANCE_CACHE: LRUDict[str, FileResource | FolderResource] = LRUDict(65536)
URL_CACHE: LRUDict[(str, int), str] = TLRUDict(1024)

client = P123Client(passport=args.user, password=args.password, token=args.token)


class DavPathBase:

    def __getattr__(self, attr: str, /):
        try:
            return self.attr[attr]
        except KeyError as e:
            raise AttributeError(attr) from e

    @locked_cacheproperty
    def creationdate(self, /) -> float:
        return datetime.fromisoformat(self.attr["CreateAt"]).timestamp()

    @locked_cacheproperty
    def etag(self, /) -> str:
        return self.attr["Etag"]

    @locked_cacheproperty
    def id(self, /) -> str:
        return self.attr["FileId"]

    @locked_cacheproperty
    def mtime(self, /) -> int | float:
        return datetime.fromisoformat(self.attr["UpdateAt"]).timestamp()

    @locked_cacheproperty
    def name(self, /) -> str:
        return self.attr.get("FileName") or ""

    @locked_cacheproperty
    def share_key(self, /) -> str:
        return self.attr.get("ShareKey") or ""

    @locked_cacheproperty
    def share_pwd(self, /) -> str:
        return self.attr.get("SharePwd") or ""

    @locked_cacheproperty
    def size(self, /) -> int:
        return self.attr.get("Size") or 0

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
        key = (self.etag, self.size)
        if pair := URL_CACHE.get(key):
            return pair[1]
        url = client.download_url(self.attr)
        expire_ts = int(next(v for k, v in parse_qsl(urlsplit(url).query) if k == "t")) - 60 * 5
        URL_CACHE[key] = (expire_ts, url)
        return url

    def get_content(self, /):
        raise DAVError(302, add_headers=[("Location", self.url)])

    def get_content_length(self, /) -> int:
        return self.size

    def get_etag(self, /) -> str:
        return self.attr["Etag"]

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

    @locked_cacheproperty
    def children(self, /) -> dict[str, FileResource | FolderResource]:
        children: dict[str, FileResource | FolderResource] = {}
        environ = self.environ
        dirname = self.path
        if dirname == "/":
            children["0"] = FolderResource("/0", environ, {
                "FileId": 0, 
                "ParentFileId": 0, 
                "FileName": "0", 
                "Etag": "", 
                "CreateAt": "1970-01-01T08:00:00+08:00", 
                "UpdateAt": "1970-01-01T08:00:00+08:00", 
                "Type": 1, 
            })
            payload = {"next": 0}
            while True:
                resp = client.share_list(payload)
                if resp["code"]:
                    raise DAVError(500, resp)
                data = resp["data"]
                for info in data["InfoList"]:
                    if info["Status"] or info["Expired"]:
                        continue
                    share_key = name = info["ShareKey"]
                    share_pwd = info["SharePwd"]
                    if share_pwd:
                        name = share_key + ":" + share_pwd
                    attr = {
                        "ShareKey": share_key, 
                        "SharePwd": share_pwd, 
                        "FileId": 0, 
                        "ParentFileId": 0, 
                        "FileName": name, 
                        "Etag": "", 
                        "CreateAt": info["CreateAt"], 
                        "UpdateAt": info["UpdateAt"], 
                        "Type": 1, 
                    }
                    children[name] = FolderResource("/" + name, environ, attr)
                if data["Next"] == "-1":
                    break
                payload["next"] = data["Next"]
        else:
            dirname += "/"
            if self.share_key:
                it = share_iterdir(self.share_key, self.share_pwd, self.id)
            else:
                it = iterdir(client, self.id)
            for attr in it:
                name = attr["FileName"]
                path = dirname + name
                if attr["Type"]:
                    children[name] = FolderResource(path, environ, attr)
                else:
                    children[name] = FileResource(path, environ, attr)
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

    def get_resource_inst(
        self, 
        /, 
        path: str, 
        environ: dict, 
    ) -> None | FolderResource | FileResource:
        parts = [p for p in path.split("/") if p]
        path = "/" + "/".join(parts)
        if inst := INSTANCE_CACHE.get(path):
           return inst
        if not parts:
            return FolderResource("/", environ, {
                "FileId": 0, 
                "ParentFileId": 0, 
                "FileName": "", 
                "Etag": "", 
                "CreateAt": "1970-01-01T08:00:00+08:00", 
                "UpdateAt": "1970-01-01T08:00:00+08:00", 
                "Type": 1, 
            })
        scope = parts[0]
        if len(parts) == 1 and scope in ("favicon.ico",):
            return None
        if CRE_MAYBE_SHARE_match(scope):
            share_key, _, share_pwd = scope.partition(":")
            top_attr = {
                "ShareKey": share_key, 
                "SharePwd": share_pwd, 
                "FileId": 0, 
                "ParentFileId": 0, 
                "FileName": scope, 
                "Etag": "", 
                "CreateAt": "1970-01-01T08:00:00+08:00", 
                "UpdateAt": "1970-01-01T08:00:00+08:00", 
                "Type": 1, 
            }
        else:
            if scope != "0":
                parts.insert(0, "0")
                path = "/0" + path
                scope = "0"
            top_attr = {
                "FileId": 0, 
                "ParentFileId": 0, 
                "FileName": "0", 
                "Etag": "", 
                "CreateAt": "1970-01-01T08:00:00+08:00", 
                "UpdateAt": "1970-01-01T08:00:00+08:00", 
                "Type": 1, 
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


config = {
    "server": "cheroot", 
    "host": "0.0.0.0", 
    "port": 8123, 
    "mount_path": "", 
    "simple_dc": {"user_mapping": {"*": True}}, 
    "provider_mapping": {"/": P123FileSystemProvider()}, 
}
app = WsgiDAVApp(config)
server = config["server"]
handler = SUPPORTED_SERVERS.get(server)
if not handler:
    raise RuntimeError(
        "Unsupported server type {!r} (expected {!r})".format(
            server, "', '".join(SUPPORTED_SERVERS.keys())
        )
    )
print("""
💥 Welcome to 123 WebDAV 😄
""")
handler(app, config, server)

# TODO: 数据缓存到数据库中
# TODO: 很多地方参照 p115servedb
# TODO: 支持扫码登录
# TODO: 当 token 失效时，自动重新再扫码登录（或者每隔一段时间，更新一下token，比如每天零点）
# TODO: 可以指定配置文件、服务器、端口等配置
# TODO: p115dav也可以用这种办法挂载任意分享链接
# TODO: 支持 fuse 挂载
# TODO: 支持除了上传外的所有方法
