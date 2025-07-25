#!/usr/bin/env python3
# encoding: utf-8

__author__ = "ChenyangGao <https://chenyanggao.github.io>"
__all__ = ["iterdir", "share_iterdir", "share_iter"]

from asyncio import sleep as async_sleep
from collections import deque
from collections.abc import AsyncIterator, Callable, Iterable, Iterator, Mapping
from datetime import datetime
from itertools import count
from time import sleep, time
from typing import overload, Any, Literal
from urllib.parse import parse_qsl, urlsplit

from encode_uri import encode_uri_component_loose
from iterutils import run_gen_step_iter, Yield
from p123client import check_response, P123Client
from undefined import undefined


def get_first(m: Mapping, *keys, default=undefined):
    for k in keys:
        if k in m:
            return m[k]
    if default is not undefined:
        return default
    raise KeyError(*keys)


# TODO: _iterdir 支持深度优先遍历
# TODO: 失败时，报错信息支持返回已经成功和未成功的列表，并且形式上也要利于断点重试
@overload
def _iterdir(
    fs_files: Callable, 
    payload: dict | int | str = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    keep_raw: bool = False, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    default_data: None | Mapping | Iterable[tuple[str, Any]] = None, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> Iterator[dict]:
    ...
@overload
def _iterdir(
    fs_files: Callable, 
    payload: dict | int | str = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    keep_raw: bool = False, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    default_data: None | Mapping | Iterable[tuple[str, Any]] = None, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> AsyncIterator[dict]:
    ...
def _iterdir(
    fs_files: Callable, 
    payload: dict | int | str = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    keep_raw: bool = False, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    default_data: None | Mapping | Iterable[tuple[str, Any]] = None, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> Iterator[dict] | AsyncIterator[dict]:
    """遍历文件列表

    :param fs_files: 调用以获取一批文件或目录信息的列表
    :param payload: 父目录 id 或查询参数
    :param parent_id: 父目录 id，默认是根目录
    :param min_depth: 最小深度，小于此深度的不会输出
    :param max_depth: 最大深度，大于此深度的不会输出，如果小于 0 则无限
    :param predicate: 以迭代出的信息（是原始数据，而不是输出的数据）作为参数进行调用，并以返回值作为筛选条件

        - 如果返回值是 0 或 None，则跳过此节点以及位于此节点之下的所有节点
        - 如果返回值是 1，则输出此节点，但跳过位于此节点之下的所有节点
        - 如果返回值是 False，则跳过此节点（但依然会继续处理位于此节点之下的节点）
        - 如果返回值是 True，则输出此节点

    :param keep_raw: 是否保留原始数据，如果为 True，则会保存到 "raw" 字段
    :param cooldown: 两次调用之间，冷却的时间（用两次调用开始时的时间差，而不是一次完成到下一次开始的时间差）
    :param base_url: 基地址，如果为空，则用默认
    :param default_data: 附加数据
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 迭代器，产生文件或目录的信息
    """
    if not isinstance(payload, dict):
        payload = {"parentFileId": payload}
    payload.setdefault("parentFileId", 0)
    page_size = int(payload.setdefault("limit", 100))
    if not (0 < page_size <= 100):
        page_size = payload["limit"] = 100
    if base_url:
        request_kwargs["base_url"] = base_url
    default_payload = payload
    def gen_step():
        parent_id = default_payload["parentFileId"]
        dq: deque[tuple[int, int, str]] = deque()
        get, put = dq.popleft, dq.append
        put((0, parent_id, ""))
        last_ts: float = 0
        while dq:
            depth, parent_id, dirname = get()
            depth += 1
            payload = {**default_payload, "parentFileId": parent_id}
            for i in count(1):
                payload["Page"] = i
                if last_ts and cooldown > 0 and (remains := last_ts + cooldown - time()) > 0:
                    if async_:
                        yield async_sleep(remains)
                    else:
                        sleep(remains)
                    last_ts = time()
                resp = yield fs_files(payload, async_=async_, **request_kwargs)
                check_response(resp)
                data = resp["data"]
                file_list = get_first(data, "InfoList", "fileList", default=None)
                if not file_list:
                    break
                total: int = get_first(data, "Total", "total", default=0)
                is_list_share = "ShareId" in file_list[0]
                for info in file_list:
                    if predicate is None:
                        pred = True
                    else:
                        pred = yield predicate(info)
                    if pred in (0, None):
                        continue
                    if not is_list_share:
                        is_dir  = bool(get_first(info, "Type", "type"))
                        fid     = int(get_first(info, "FileId", "fileID", "fileId", "fileid"))
                        name    = get_first(info, "FileName", "filename")
                        relpath = dirname + name
                        if is_dir and pred is not 1 and (max_depth < 0 or depth < max_depth):
                            put((depth, fid, relpath + "/"))
                        pred = pred and depth >= min_depth
                    if pred:
                        attr = dict(default_data or ())
                        if is_list_share:
                            attr.update({
                                "share_id": info["ShareId"], 
                                "share_key": info["ShareKey"], 
                                "share_pwd": info["SharePwd"], 
                                "share_name": info["ShareName"], 
                                "file_id_list": list(map(int, info["FileIdList"].split(","))), 
                            })
                        else:
                            if total:
                                attr["total_siblings"] = total
                            attr["is_dir"] = is_dir
                            attr["id"] = fid
                            attr["name"] = name
                            attr["parent_id"] = parent_id
                            attr["relpath"] = relpath
                            if not is_dir:
                                name = encode_uri_component_loose(name, quote_slash=False)
                                etag = attr["md5"] = get_first(info, "Etag", "etag")
                                size = attr["size"] = int(get_first(info, "Size", "size"))
                                s3_key_flag = attr["s3keyflag"] = get_first(info, "S3KeyFlag", "s3KeyFlag", "s3keyflag")
                                attr["uri"] = f"123://{name}|{size}|{etag}?{s3_key_flag}"
                        if ctime := get_first(info, "CreateAt", "createAt", default=""):
                            ctime = attr["ctime_datetime"] = datetime.fromisoformat(ctime)
                            attr["ctime"] = int(ctime.timestamp())
                        if mtime := get_first(info, "UpdateAt", "updateAt", default=""):
                            mtime = attr["mtime_datetime"] = datetime.fromisoformat(mtime)
                            attr["mtime"] = int(mtime.timestamp())
                        if keep_raw:
                            attr["raw"] = info
                        yield Yield(attr)
                if (len(file_list) < page_size or 
                    data.get("Next") == "-1" or
                    data.get("lastFileId") == -1
                ):
                    break
                if next_id := data.get("Next"):
                    payload["next"] = next_id
                elif lastFileId := data.get("lastFileId"):
                    payload["lastFileId"] = lastFileId
    return run_gen_step_iter(gen_step, async_)


@overload
def iterdir(
    client: P123Client, 
    payload: dict | int | str = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    keep_raw: bool = False, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    list_method: Literal["list", "list_new", "list_v1", "list_v2"] | Callable = "list_new", 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> Iterator[dict]:
    ...
@overload
def iterdir(
    client: P123Client, 
    payload: dict | int | str = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    keep_raw: bool = False, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    list_method: Literal["list", "list_new", "list_v1", "list_v2"] | Callable = "list_new", 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> AsyncIterator[dict]:
    ...
def iterdir(
    client: P123Client, 
    payload: dict | int | str = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    keep_raw: bool = False, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    list_method: Literal["list", "list_new", "list_v1", "list_v2"] | Callable = "list_new", 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> Iterator[dict] | AsyncIterator[dict]:
    """遍历文件列表

    :param client: 123 网盘的客户端对象
    :param payload: 父目录 id 或查询参数
    :param min_depth: 最小深度，小于此深度的不会输出
    :param max_depth: 最大深度，大于此深度的不会输出，如果小于 0 则无限
    :param predicate: 以文件或目录的信息（是原始数据，而不是输出的数据）作为参数进行调用，并以返回值作为筛选条件

        - 如果返回值是 0 或 None，则跳过此节点以及位于此节点之下的所有节点
        - 如果返回值是 1，则输出此节点，但跳过位于此节点之下的所有节点
        - 如果返回值是 False，则跳过此节点（但依然会继续处理位于此节点之下的节点）
        - 如果返回值是 True，则输出此节点

    :param keep_raw: 是否保留原始数据，如果为 True，则会保存到 "raw" 字段
    :param cooldown: 两次调用之间，冷却的时间（用两次调用开始时的时间差，而不是一次完成到下一次开始的时间差）
    :param base_url: 基地址，如果为空，则用默认
    :param list_method: 使用哪个罗列目录的方法

        - "list": 使用 ``P123Client.fs_list``
        - "list_new": 使用 ``P123Client.fs_list_new``
        - "list_v1": 使用 ``P123Client.fs_list_v1_open``
        - "list_v2": 使用 ``P123Client.fs_list_v2_open``

    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 迭代器，产生文件或目录的信息
    """
    if callable(list_method):
        method: Callable = list_method
    else:
        match list_method:
            case "list_new":
                method = client.fs_list_new
            case "list_v1":
                method = client.fs_list_v1_open
            case "list_v2":
                method = client.fs_list_v2_open
            case _:
                method = client.fs_list
    return _iterdir(
        method, 
        payload=payload, 
        min_depth=min_depth, 
        max_depth=max_depth, 
        predicate=predicate, 
        keep_raw=keep_raw, 
        cooldown=cooldown, 
        base_url=base_url, 
        async_=async_, 
        **request_kwargs, 
    )


@overload
def share_iterdir(
    share_key: str = "", 
    share_pwd: str = "", 
    payload: dict | int | str = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    keep_raw: bool = False, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> Iterator[dict]:
    ...
@overload
def share_iterdir(
    share_key: str = "", 
    share_pwd: str = "", 
    payload: dict | int | str = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    keep_raw: bool = False, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> AsyncIterator[dict]:
    ...
def share_iterdir(
    share_key: str = "", 
    share_pwd: str = "", 
    payload: dict | int | str = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    keep_raw: bool = False, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> Iterator[dict] | AsyncIterator[dict]:
    """遍历分享的文件列表

    :param share_key: 分享码或者分享链接（可以携带提取码）

        .. note::
            在分享链接中的位置形如 f"https://www.123pan.com/s/{share_key}"

            如果携带提取码，要写成

                f"https://www.123pan.com/s/{share_key}?提取码:{share_pwd}"

            或者
                f"https://www.123pan.com/s/{share_key}?pwd={share_pwd}"

            上面的基地址不必是 "https://www.123pan.com"

    :param share_pwd: 提取码（4个文字），可以为空
    :param payload: 父目录 id 或查询参数
    :param min_depth: 最小深度，小于此深度的不会输出
    :param max_depth: 最大深度，大于此深度的不会输出，如果小于 0 则无限
    :param predicate: 以文件或目录的信息（是原始数据，而不是输出的数据）作为参数进行调用，并以返回值作为筛选条件

        - 如果返回值是 0 或 None，则跳过此节点以及位于此节点之下的所有节点
        - 如果返回值是 1，则输出此节点，但跳过位于此节点之下的所有节点
        - 如果返回值是 False，则跳过此节点（但依然会继续处理位于此节点之下的节点）
        - 如果返回值是 True，则输出此节点

    :param keep_raw: 是否保留原始数据，如果为 True，则会保存到 "raw" 字段
    :param cooldown: 两次调用之间，冷却的时间（用两次调用开始时的时间差，而不是一次完成到下一次开始的时间差）
    :param base_url: 基地址，如果为空，则用默认
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 迭代器，产生文件或目录的信息
    """
    if not isinstance(payload, dict):
        payload = {"parentFileId": payload}
    if share_key and share_key.startswith(("http://", "https://")):
        urlp = urlsplit(share_key)
        # if not base_url:
        #     base_url = f"{urlp.scheme}://{urlp.netloc}"
        share_key = urlp.path.rsplit("/", 1)[-1]
        if not share_pwd:
            query = urlp.query
            if "pwd=" in query:
                for k, v in parse_qsl(query):
                    if k == "pwd":
                        share_pwd = v
            if not share_pwd:
                maybe_pwd = urlp.query.rpartition(":")[-1]
                if len(maybe_pwd) == 4:
                    share_pwd = maybe_pwd
    if share_key:
        payload["ShareKey"] = share_key
    else:
        share_key = payload.setdefault("ShareKey", share_key)
    if share_pwd:
        payload["SharePwd"] = share_pwd
    else:
        share_pwd = payload.setdefault("SharePwd", share_pwd)
    share_key_pwd = {"share_key": share_key, "share_pwd": share_pwd}
    return _iterdir(
        P123Client.share_fs_list, 
        payload, 
        min_depth=min_depth, 
        max_depth=max_depth, 
        predicate=predicate, 
        keep_raw=keep_raw, 
        cooldown=cooldown, 
        base_url=base_url, 
        default_data=share_key_pwd, 
        async_=async_, 
        **request_kwargs, 
    )


@overload
def share_iter(
    client: P123Client, 
    predicate: None | Callable[[dict], bool] = lambda info: not (info["Status"] or info["Expired"]), 
    keep_raw: bool = True, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> Iterator[dict]:
    ...
@overload
def share_iter(
    client: P123Client, 
    predicate: None | Callable[[dict], bool] = lambda info: not (info["Status"] or info["Expired"]), 
    keep_raw: bool = True, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> AsyncIterator[dict]:
    ...
def share_iter(
    client: P123Client, 
    predicate: None | Callable[[dict], bool] = lambda info: not (info["Status"] or info["Expired"]), 
    keep_raw: bool = True, 
    cooldown: float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> Iterator[dict] | AsyncIterator[dict]:
    """遍历用户的分享列表

    :param client: 123 网盘的客户端对象
    :param predicate: 以分享信息（是原始数据，而不是输出的数据）作为参数进行调用，并以返回值作为筛选条件
    :param keep_raw: 是否保留原始数据，如果为 True，则会保存到 "raw" 字段
    :param cooldown: 两次调用之间，冷却的时间（用两次调用开始时的时间差，而不是一次完成到下一次开始的时间差）
    :param base_url: 基地址，如果为空，则用默认
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 迭代器，产生文件或目录的信息
    """
    return _iterdir(
        client.share_list, 
        predicate=predicate, 
        keep_raw=keep_raw, 
        cooldown=cooldown, 
        base_url=base_url, 
        async_=async_, 
        **request_kwargs, 
    )

