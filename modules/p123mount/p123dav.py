#!/usr/bin/env python3
# encoding: utf-8

from __future__ import annotations

__author__ = "ChenyangGao <https://chenyanggao.github.io>"
__version__ = (0, 0, 0)
__all__ = [""]

import errno

from collections.abc import Mapping
from datetime import datetime
from shutil import SameFileError
from tempfile import NamedTemporaryFile
from io import BytesIO
from itertools import count
from posixpath import join as joinpath, split as splitpath
from sqlite3 import connect, register_adapter, register_converter, PARSE_DECLTYPES
from uuid import uuid4

from cachedict import LRUDict
from orjson import dumps, loads
from p123 import check_response, P123Client
from property import locked_cacheproperty
from sqlitetools import find
from wsgidav.wsgidav_app import WsgiDAVApp # type: ignore
from wsgidav.dav_error import DAVError, HTTP_NOT_FOUND # type: ignore
from wsgidav.dav_provider import DAVCollection, DAVNonCollection, DAVProvider # type: ignore
from wsgidav.server.server_cli import SUPPORTED_SERVERS # type: ignore


register_adapter(list, dumps)
register_adapter(dict, dumps)
register_converter("JSON", loads)


# TODO: 修改为自己的账户和密码
client = P123Client(passport="", password="")
con = connect(f"123-{client.passport}.db", check_same_thread=False, autocommit=True, detect_types=PARSE_DECLTYPES)
con.executescript("""\
PRAGMA journal_mode = WAL;
CREATE TABLE IF NOT EXISTS data (
    id INTEGER NOT NULL PRIMARY KEY, -- 文件或目录的 id
    attr JSON, -- 文件或目录的信息
    parent_id INTEGER AS (CAST(attr->>'ParentFileId' AS INT)) STORED, -- 父目录 id
    is_dir INT AS (attr->'Type') STORED, -- 是否目录
    name TEXT AS (attr->>'FileName') STORED, -- 名字
    abspath TEXT AS (attr->>'AbsPath') STORED -- 各级目录 id
);
CREATE INDEX IF NOT EXISTS idx_data_pid ON data(parent_id);
CREATE INDEX IF NOT EXISTS idx_data_name ON data(name);
CREATE INDEX IF NOT EXISTS idx_data_abspath ON data(abspath);
""")
cache: LRUDict[int, FileResource] = LRUDict()


# TODO: 再返回一个信息，目标是文件还是目录
# TODO: 在数据库中不存在，不代表真的不存在，还需要在实际的文件系统中进行找寻
def get_id_to_path(path: str) -> tuple[int, list[str]]:
    path = path.strip("/")
    if not path:
        return 0, []
    sql = "SELECT id, is_dir FROM data WHERE parent_id = ? AND name = ? LIMIT 1"
    parent_id = 0
    parts = path.split("/")
    end = len(parts) - 1
    for i, name in enumerate(parts):
        if not name:
            continue
        id, is_dir = find(con, sql, (parent_id, name), default=(0, 1))
        if not id or not is_dir and i < end:
            return parent_id, parts[i:]
        parent_id = id
    return id, []


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
    def id(self, /) -> str:
        return self.attr["FileId"]

    @locked_cacheproperty
    def mtime(self, /) -> int | float:
        return datetime.fromisoformat(self.attr["UpdateAt"]).timestamp()

    @locked_cacheproperty
    def name(self, /) -> str:
        return self.attr["FileName"]

    @locked_cacheproperty
    def size(self, /) -> int:
        return self.attr.get("Size") or 0

    @locked_cacheproperty
    def user_info(self, /) -> dict:
        return check_response(client.user_info())["data"]

    def copy_move_single(self, /, dest_path: str, *, is_move: bool):
        if is_move:
            self.move_recursive(dest_path)
        else:
            path = "/" + dest_path.strip("/")
            if path == self.path:
                raise SameFileError(path)
            _, remains = get_id_to_path(path)
            if not remains:
                raise FileExistsError(errno.EEXIST, path)
            dir_, name = splitpath(path)
            pid, remains = get_id_to_path(dir_)
            if remains:
                raise FileNotFoundError(errno.ENOENT, dir_)
            check_response(client.fs_copy({"fileList": [{**self.attr, "FileName": name}]}, parent_id=pid))

    def delete(self, /):
        check_response(client.fs_trash(self.id))
        cur = con.execute("DELETE FROM data WHERE id=? RETURNING is_dir, abspath", (self.id,))
        ret = cur.fetchone()
        if ret and ret[0]:
            con.execute("DELETE FROM data WHERE abspath LIKE ? || '/%'", (ret[1],))

    def get_creation_date(self, /) -> float:
        return self.creationdate

    def get_display_name(self, /) -> str:
        return self.name

    def get_last_modified(self, /) -> float:
        return self.mtime

    def is_link(self, /) -> bool:
        return False

    def move_recursive(self, dest_path: str):
        path = "/" + dest_path.strip("/")
        if path == self.path:
            return
        _, remains = get_id_to_path(path)
        if not remains:
            raise FileExistsError(errno.EEXIST, path)
        dir_, name = splitpath(path)
        old_dir, old_name = splitpath(self.path)
        if old_dir == dir_ and name != old_name:
            resp = check_response(client.fs_rename({"FileId": self.id, "fileName": name}))
            info = resp["data"]["Info"]
            con.execute("REPLACE INTO data(id, attr) VALUES (?,?)", (self.id, info))
            return
        pid, remains = get_id_to_path(dir_)
        if remains:
            raise FileNotFoundError(errno.ENOENT, dir_)
        if old_name == name:
            resp = check_response(client.fs_move(self.id, parent_id=pid))
            info = resp["data"]["Info"][0]
            con.execute("REPLACE INTO data(id, attr) VALUES (?,?)", (self.id, info))
        else:
            check_response(client.fs_rename({"FileId": self.id, "fileName": str(uuid4())}))
            try:
                check_response(client.fs_move(self.id, parent_id=pid))
                try:
                    resp = check_response(client.fs_rename({"FileId": self.id, "fileName": name}))
                    info = resp["data"]["Info"][0]
                    con.execute("REPLACE INTO data(id, attr) VALUES (?,?)", (self.id, info))
                except:
                    check_response(client.fs_move(self.id, parent_id=int(self.attr["ParentFileId"])))
                    raise
            except:
                client.fs_rename({"FileId": self.id, "fileName": old_name})
                raise

    def support_modified(self, /) -> bool:
        return True

    def support_recursive_delete(self, /) -> bool:
        return True

    def support_recursive_move(self, /, dest_path: str) -> bool:
        return True


class TempFileResource(DAVNonCollection):

    def __init__(
        self, 
        /, 
        path: str, 
        environ: dict, 
        parent_id: int = 0, 
    ):
        super().__init__(path, environ)
        self.parent_id = parent_id

    def begin_write(self, /, content_type: None | str = None):
        self._file = NamedTemporaryFile(delete_on_close=False)
        return self._file

    def end_write(self, /, *, with_errors):
        if not with_errors:
            resp = client.upload_file(
                self._file.name, 
                file_name=self.name, 
                parent_id=self.parent_id, 
                duplicate=2, 
            )
            data = check_response(resp)["data"]
            info = data.get("Info") or data["file_info"]
            con.execute("REPLACE INTO data(id, attr) VALUES (?,?)", (int(info["FileId"]), info))

    def get_content(self, /):
        return BytesIO()

    def get_content_length(self, /):
        return 0

    def get_etag(self, /) -> str:
        return "d41d8cd98f00b204e9800998ecf8427e"

    def support_etag(self, /) -> bool:
        return True

    def support_modified(self, /) -> bool:
        return False

    def support_ranges(self, /) -> bool:
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
        if (f := cache.get(self.id)) and (url := f.__dict__.get("url")):
            self.__dict__["url"] = url
        cache[self.id] = self

    @locked_cacheproperty
    def url(self, /) -> str:
        resp = check_response(client.download_info(self.attr))
        return resp["data"]["DownloadUrl"]

    def begin_write(self, /, content_type: None | str = None):
        self._file = NamedTemporaryFile(delete_on_close=False)
        return self._file

    def end_write(self, /, *, with_errors):
        if not with_errors:
            resp = client.upload_file(
                self._file.name, 
                file_name=self.name, 
                parent_id=self.attr["ParentFileId"], 
                duplicate=2, 
            )
            data = check_response(resp)["data"]
            info = data.get("Info") or data["file_info"]
            self.attr.update(info)
            con.execute("DELETE FROM data WHERE id=?", (self.id,))
            con.execute("REPLACE INTO data(id, attr) VALUES (?,?)", (int(info["FileId"]), info))

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

    @locked_cacheproperty
    def children(self, /) -> dict[str, FileResource | FolderResource]:
        # TODO: 先用，如果有风控，后面会加入分流机制
        # TODO: 一页获取 100 条实在太慢，后面加上并发机制
        children: dict[str, FileResource | FolderResource] = {}
        environ = self.environ
        dirname = self.path
        if not dirname.endswith("/"):
            dirname += "/"
        parent_id = self.id
        payload = {"parentFileId": parent_id}
        for i in count(1):
            payload["Page"] = i
            resp = check_response(client.fs_list_new(payload))
            for attr in resp["data"]["InfoList"]:
                name = attr["FileName"]
                path = dirname + name
                if attr["Type"]:
                    children[name] = FolderResource(path, environ, attr)
                else:
                    children[name] = FileResource(path, environ, attr)
            if resp["data"]["Next"] == "-1":
                break
        con.execute("DELETE FROM data WHERE parent_id = ?", (parent_id,))
        con.executemany("REPLACE INTO data(id, attr) VALUES (?,?)", ((f.id, f.attr) for f in children.values()))
        return children

    def create_collection(self, /, name: str) -> FolderResource:
        resp = check_response(client.fs_mkdir(name, parent_id=self.id))
        info = resp["data"]["Info"]
        con.execute("REPLACE INTO data(id, attr) VALUES (?,?)", (int(info["FileId"]), info))
        return FolderResource(joinpath(self.path, name), self.environ, info)

    def create_empty_resource(self, /, name: str) -> FileResource:
        resp = check_response(client.upload_file_fast(file_name=name, parent_id=self.id, duplicate=1))
        info = resp["data"]["Info"]
        con.execute("REPLACE INTO data(id, attr) VALUES (?,?)", (int(info["FileId"]), info))
        return FolderResource(joinpath(self.path, name), self.environ, info)

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
        if path in ("/favicon.ico", ):
            return None
        path = "/" + path.strip("/")
        fid, remains = get_id_to_path(path)
        if remains:
            parent_id = fid
            for i, name in enumerate(remains, 1):
                payload = {"parentFileId": parent_id}
                ls: list[dict] = []
                for i in count(1):
                    payload["Page"] = i
                    resp = check_response(client.fs_list_new(payload))
                    ls += resp["data"]["InfoList"]
                    if resp["data"]["Next"] == "-1":
                        break
                con.execute("DELETE FROM data WHERE parent_id = ?", (parent_id,))
                con.executemany("REPLACE INTO data(id, attr) VALUES (?,?)", ((int(a["FileId"]), a) for a in ls))
                for attr in ls:
                    if attr["FileName"] == name:
                        if not attr["Type"] and i < len(remains):
                            return None
                        parent_id = attr["FileId"]
                        break
                else:
                    return TempFileResource(path, environ, parent_id)
        elif fid:
            attr = find(con, "SELECT attr FROM data WHERE id=? LIMIT 1", fid)
        else:
            attr = {
                "FileId": 0, 
                "ParentFileId": 0, 
                "FileName": "", 
                "Etag": "", 
                "CreateAt": "1970-01-01T08:00:00+08:00", 
                "UpdateAt": "1970-01-01T08:00:00+08:00", 
                "Type": 1, 
            }
        if attr["Type"]:
            return FolderResource(path, environ, attr)
        else:
            return FileResource(path, environ, attr)


if __name__ == "__main__":
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

# TODO: 插入用单独线程
# TODO: 缓存一定量的文件列表
