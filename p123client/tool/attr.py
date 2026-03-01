#!/usr/bin/env python3
# encoding: utf-8

__author__ = "ChenyangGao <https://chenyanggao.github.io>"
__all__ = ["get_ancestors", "get_id"]

import errno

from collections.abc import Coroutine
from typing import overload, Any, Literal

from iterutils import run_gen_step, with_iter_next

from ..client import check_response, P123Client
from .iterdir import iterdir


@overload
def get_ancestors(
    client: P123Client, 
    path: str, 
    parent_id: int = 0, 
    is_absolute: bool = False, 
    use_search: bool = False, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> list[dict]:
    ...
@overload
def get_ancestors(
    client: P123Client, 
    path: str, 
    parent_id: int = 0, 
    is_absolute: bool = False, 
    use_search: bool = False, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> Coroutine[Any, Any, list[dict]]:
    ...
def get_ancestors(
    client: P123Client, 
    path: str, 
    parent_id: int = 0, 
    is_absolute: bool = False, 
    use_search: bool = False, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> list[dict] | Coroutine[Any, Any, list[dict]]:
    """获取某个路径所对应的各节点的简略信息

    :param client: 123 网盘的客户端对象
    :param path: 文件或目录的路径
    :param parent_id: 顶层目录的 id
    :param is_absolute: 是否绝对路径
    :param use_search: 是否使用搜索接口加速
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 绝对路径或相对路径（相对于 ``parent_id``）的各节点的简略信息

        .. code:: python

            {
                "id": int,        # 节点的 id
                "parent_id": int, # 父目录的 id
                "name": str,      # 节点的名字
                "is_dir": bool,   # 是否目录
            }
    """
    if path.startswith("/"):
        is_absolute = True
        parent_id = 0
    error = FileNotFoundError(errno.ENOENT, {"path": path, "parent_id": parent_id})
    def gen_step():
        nonlocal parent_id
        parts = path.strip("/").split("/")
        if is_absolute:
            ancestors: list[dict] = [{"id": 0, "parent_id": 0, "name": "", "is_dir": True}]
            if parent_id:
                resp = yield client.fs_get_path_history(parent_id, async_=async_, **request_kwargs)
                check_response(resp)
                data = resp["data"]["list"][str(parent_id)]
                if not data:
                    raise error
                ancestors.extend({
                    "id": info["FileId"], 
                    "parent_id": info["ParentFileId"], 
                    "name": info["FileName"], 
                    "is_dir": not info["Etag"]
                } for info in data)
        else:
            ancestors = []
        if parts:
            if use_search:
                name = parts[-1]
                with with_iter_next(iterdir(
                    client, 
                    {"parentFileId": parent_id, "searchData": name}, 
                    keep_raw=True, 
                    async_=async_, 
                    **request_kwargs, 
                )) as get_next:
                    while True:
                        info = yield get_next()
                        if info["name"] == name:
                            pids = tuple(map(int, info["raw"]["AbsPath"][1:].split("/")))
                            if parent_id:
                                pids = pids[pids.index(parent_id)+1:]
                            if len(pids) == len(parts):
                                if len(parts) > 1:
                                    resp = yield client.fs_info(pids[:-1], async_=async_, **request_kwargs)
                                    check_response(resp)
                                    ok = True
                                    for pname, pinfo in zip(parts, resp["data"]["infoList"]):
                                        if pinfo["FileName"] != pname:
                                            ok = False
                                            break
                                        ancestors.append({
                                            "id": pinfo["FileId"], 
                                            "parent_id": pinfo["ParentFileId"], 
                                            "name": pname, 
                                            "is_dir": not pinfo["Etag"], 
                                        })
                                    if not ok:
                                        continue
                                ancestors.append({
                                    "id": info["id"], 
                                    "parent_id": parent_id, 
                                    "name": name, 
                                    "is_dir": info["is_dir"], 
                                })
                                return ancestors
                raise error
            else:
                for name in parts:
                    ok = False
                    with with_iter_next(iterdir(
                        client, 
                        parent_id, 
                        async_=async_, 
                        **request_kwargs, 
                    )) as get_next:
                        while True:
                            info = yield get_next()
                            if info["name"] == name:
                                ancestors.append({
                                    "id": info["id"], 
                                    "parent_id": parent_id, 
                                    "name": name, 
                                    "is_dir": info["is_dir"], 
                                })
                                parent_id = info["id"]
                                ok = True
                                break
                    if not ok:
                        raise error
        return ancestors
    return run_gen_step(gen_step, async_)


@overload
def get_id(
    client: P123Client, 
    path: str, 
    parent_id: int = 0, 
    use_search: bool = False, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> int:
    ...
@overload
def get_id(
    client: P123Client, 
    path: str, 
    parent_id: int = 0, 
    use_search: bool = False, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> Coroutine[Any, Any, int]:
    ...
def get_id(
    client: P123Client, 
    path: str, 
    parent_id: int = 0, 
    use_search: bool = False, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> int | Coroutine[Any, Any, int]:
    """获取某个路径所对应的 id

    :param client: 123 网盘的客户端对象
    :param path: 文件或目录的路径
    :param parent_id: 顶层目录的 id
    :param use_search: 是否使用搜索接口加速
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 路径所对应的 id
    """
    def gen_step():
        ancestors = yield get_ancestors(
            client, 
            path, 
            parent_id, 
            use_search=use_search, 
            async_=async_, 
            **request_kwargs, 
        )
        return ancestors[-1]["id"]
    return run_gen_step(gen_step, async_)

