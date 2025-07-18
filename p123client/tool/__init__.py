#!/usr/bin/env python3
# encoding: utf-8

__author__ = "ChenyangGao <https://chenyanggao.github.io>"
__all__ = ["make_uri", "upload_uri", "get_downurl", "iterdir", "share_iterdir"]

import errno

from asyncio import sleep as async_sleep
from collections import deque
from collections.abc import AsyncIterator, Callable, Coroutine, Iterable, Iterator, Mapping
from functools import partial
from itertools import count
from time import sleep, time
from typing import Literal
from typing import overload, Any, Literal
from urllib.parse import unquote, urlsplit

from encode_uri import encode_uri_component_loose
from iterutils import run_gen_step, run_gen_step_iter, Yield
from p123client import check_response, P123Client


@overload
def make_uri(
    client: P123Client, 
    file_id: int, 
    ensure_ascii: bool = False, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> str:
    ...
@overload
def make_uri(
    client: P123Client, 
    file_id: int, 
    ensure_ascii: bool = False, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> Coroutine[Any, Any, str]:
    ...
def make_uri(
    client: P123Client, 
    file_id: int, 
    ensure_ascii: bool = False, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> str | Coroutine[Any, Any, str]:
    """创建自定义 uri，格式为 f"123://{name}|{size}|{md5}?{s3_key_flag}"

    :param client: 123 网盘的客户端对象
    :param file_id: 文件 id
    :param ensure_ascii: 是否要求全部字符在 ASCII 范围内
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 自定义 uri
    """
    def gen_step():
        resp = yield client.fs_info(file_id, async_=async_, **request_kwargs)
        check_response(resp)
        resp["payload"] = file_id
        info_list = resp["data"]["infoList"]
        if not info_list:
            raise FileNotFoundError(errno.ENOENT, resp)
        info = info_list[0]
        if info["Type"]:
            raise IsADirectoryError(errno.EISDIR, resp)
        md5 = info["Etag"]
        name = encode_uri_component_loose(info["FileName"], ensure_ascii=ensure_ascii, quote_slash=False)
        size = info["Size"]
        s3_key_flag = info["S3KeyFlag"]
        return f"123://{name}|{size}|{md5}?{s3_key_flag}"
    return run_gen_step(gen_step, async_)


@overload
def upload_uri(
    client: P123Client, 
    uri: str, 
    parent_id: int = 0, 
    duplicate: Literal[0, 1, 2] = 0, 
    quoted: bool = True, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> dict:
    ...
@overload
def upload_uri(
    client: P123Client, 
    uri: str, 
    parent_id: int = 0, 
    duplicate: Literal[0, 1, 2] = 0, 
    quoted: bool = True, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> Coroutine[Any, Any, dict]:
    ...
def upload_uri(
    client: P123Client, 
    uri: str, 
    parent_id: int = 0, 
    duplicate: Literal[0, 1, 2] = 0, 
    quoted: bool = True, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> dict | Coroutine[Any, Any, dict]:
    """使用自定义链接进行秒传

    :param client: 123 网盘的客户端对象
    :param uri: 链接，格式为 f"123://{name}|{size}|{md5}?{s3_key_flag}"，前面的 "123://" 和后面的 "?{s3_key_flag}" 都可省略
    :param parent_id: 上传到此 id 对应的目录中
    :param duplicate: 处理同名：0: 提醒/忽略 1: 保留两者 2: 替换
    :param quoted: 说明链接已经过 quote 处理，所以使用时需要 unquote 回来
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 接口响应，来自 `P123Client.upload_request`，当响应信息里面有 "Reuse" 的值为 "true"，说明秒传成功
    """
    uri = uri.removeprefix("123://").rsplit("?", 1)[0]
    if quoted:
        uri = unquote(uri)
    name, size, md5 = uri.rsplit("|", 2)
    return client.upload_file_fast(
        file_md5=md5, 
        file_name=unquote(name), 
        file_size=int(size), 
        parent_id=parent_id, 
        duplicate=duplicate, 
        async_=async_, 
        **request_kwargs, 
    )


@overload
def get_downurl(
    client: P123Client, 
    uri: int | str, 
    quoted: bool = True, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> str:
    ...
@overload
def get_downurl(
    client: P123Client, 
    uri: int | str, 
    quoted: bool = True, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> Coroutine[Any, Any, str]:
    ...
def get_downurl(
    client: P123Client, 
    uri: int | str, 
    quoted: bool = True, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> str | Coroutine[Any, Any, str]:
    """获取下载链接

    :param client: 123 网盘的客户端对象
    :param uri: 如果是 int，则视为文件 id（必须存在你网盘）；如果是 str，则视为自定义链接

        .. note::
            自定义链接的格式为 f"123://{name}|{size}|{md5}?{s3_key_flag}"，前面的 "123://" 和后面的 "?{s3_key_flag}" 都可省略

            如果省略 "?{s3_key_flag}"，则会尝试先秒传到你的网盘的 "/我的秒传" 目录下，名字为 f"{md5}-{size}" 的文件，然后再获取下载链接
    :param quoted: 说明链接已经过 quote 处理，所以使用时需要 unquote 回来
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 下载链接
    """
    def gen_step():
        nonlocal uri
        if isinstance(uri, int):
            payload: int | dict = uri
        else:
            uri, _, s3_key_flag = uri.removeprefix("123://").rpartition("?")
            if not uri:
                uri, s3_key_flag = s3_key_flag, uri
            if quoted:
                uri = unquote(uri)
            name, size_s, md5 = uri.rsplit("|", 2)
            size = int(size_s)
            if s3_key_flag:
                payload = {
                    "FileName": name, 
                    "Etag": md5, 
                    "Size": size, 
                    "S3KeyFlag": s3_key_flag, 
                }
            else:
                resp = yield client.upload_file_fast(
                    file_name=".tempfile", 
                    file_md5=md5, 
                    file_size=size, 
                    duplicate=2, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                payload = resp["data"]["Info"]
        resp = yield client.download_info(payload, async_=async_, **request_kwargs)
        check_response(resp)
        return resp["data"]["DownloadUrl"]
    return run_gen_step(gen_step, async_)


# TODO: _iterdir 支持广度优先遍历
# TODO: 失败时，报错信息支持返回已经成功和未成功的列表，并且形式上也要利于断点重试
# TODO: 支持传入其它自定义的查询参数
@overload
def _iterdir(
    fs_files: Callable, 
    payload: dict = {}, 
    parent_id: int = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    cooldown: int | float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    extra_data: None | Mapping | Iterable[tuple[str, Any]] = None, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> Iterator[dict]:
    ...
@overload
def _iterdir(
    fs_files: Callable, 
    payload: dict = {}, 
    parent_id: int = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    cooldown: int | float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    extra_data: None | Mapping | Iterable[tuple[str, Any]] = None, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> AsyncIterator[dict]:
    ...
def _iterdir(
    fs_files: Callable, 
    payload: dict = {}, 
    parent_id: int = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    cooldown: int | float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    extra_data: None | Mapping | Iterable[tuple[str, Any]] = None, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> Iterator[dict] | AsyncIterator[dict]:
    """遍历文件列表

    :param fs_files: 调用以获取一批文件或目录信息的列表
    :param payload: 基本的查询参数
    :param parent_id: 父目录 id，默认是根目录
    :param min_depth: 最小深度，小于此深度的不会输出
    :param max_depth: 最大深度，大于此深度的不会输出，如果小于 0 则无限
    :param predicate: 以文件或目录的信息作为参数进行调用，并以返回值作为筛选条件

        - 如果返回值是 0 或 None，则跳过此节点以及位于此节点之下的所有节点
        - 如果返回值是 1，则输出此节点，但跳过位于此节点之下的所有节点
        - 如果返回值是 False，则跳过此节点（但依然会继续处理位于此节点之下的节点）
        - 如果返回值是 True，则输出此节点

    :param cooldown: 两次调用之间，冷却的时间（用两次调用开始时的时间差，而不是一次完成到下一次开始的时间差）
    :param base_url: 基地址，如果为空，则用默认
    :param extra_data: 附加数据
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 迭代器，产生文件或目录的信息
    """
    default_payload = payload
    page_size = int(payload.setdefault("limit", 100))
    if base_url:
        request_kwargs["base_url"] = base_url
    def gen_step():
        nonlocal parent_id
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
                resp = yield fs_files(payload, async_=async_, **request_kwargs)
                if cooldown > 0:
                    last_ts = time()
                check_response(resp)
                info_list = resp["data"]["InfoList"]
                for info in info_list:
                    is_dir = info["is_dir"] = bool(info["Type"])
                    fid = info["id"] = int(info["FileId"])
                    info["parent_id"] = parent_id
                    name = info["name"] = info["FileName"]
                    relpath = info["relpath"] = dirname + name
                    if not is_dir:
                        name = encode_uri_component_loose(name, quote_slash=False)
                        size = info["size"] = int(info["Size"])
                        md5 = info["md5"] = info["Etag"]
                        s3_key_flag = info["S3KeyFlag"]
                        info["uri"] = f"123://{name}|{size}|{md5}?{s3_key_flag}"
                    if predicate is None:
                        pred = True
                    else:
                        pred = yield partial(predicate, info)
                    if pred is None:
                        continue
                    elif pred:
                        if depth >= min_depth:
                            if extra_data:
                                info = dict(extra_data, **info)
                            yield Yield(info)
                        if pred is 1:
                            continue
                    if is_dir and (max_depth < 0 or depth < max_depth):
                        put((depth, fid, relpath + "/"))
                if (
                    not info_list or 
                    len(info_list) < page_size or 
                    resp["data"]["Next"] == "-1"
                ):
                    break
                if next_id := resp["data"]["Next"]:
                    payload["next"] = next_id
    return run_gen_step_iter(gen_step, async_)


@overload
def iterdir(
    client: P123Client, 
    parent_id: int = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    cooldown: int | float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    use_list_new: bool = False, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> Iterator[dict]:
    ...
@overload
def iterdir(
    client: P123Client, 
    parent_id: int = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    cooldown: int | float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    use_list_new: bool = False, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> AsyncIterator[dict]:
    ...
def iterdir(
    client: P123Client, 
    parent_id: int = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    cooldown: int | float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    use_list_new: bool = False, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> Iterator[dict] | AsyncIterator[dict]:
    """遍历文件列表

    :param client: 123 网盘的客户端对象
    :param parent_id: 父目录 id，默认是根目录
    :param min_depth: 最小深度，小于此深度的不会输出
    :param max_depth: 最大深度，大于此深度的不会输出，如果小于 0 则无限
    :param predicate: 以文件或目录的信息作为参数进行调用，并以返回值作为筛选条件

        - 如果返回值是 0 或 None，则跳过此节点以及位于此节点之下的所有节点
        - 如果返回值是 1，则输出此节点，但跳过位于此节点之下的所有节点
        - 如果返回值是 False，则跳过此节点（但依然会继续处理位于此节点之下的节点）
        - 如果返回值是 True，则输出此节点

    :param cooldown: 两次调用之间，冷却的时间（用两次调用开始时的时间差，而不是一次完成到下一次开始的时间差）
    :param base_url: 基地址，如果为空，则用默认
    :param use_list_new: 使用 `P123Client.fs_list_new` 而不是 `P123Client.fs_list`
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 迭代器，产生文件或目录的信息
    """
    return _iterdir(
        client.fs_list_new if use_list_new else client.fs_list, 
        parent_id=parent_id, 
        min_depth=min_depth, 
        max_depth=max_depth, 
        predicate=predicate, 
        cooldown=cooldown, 
        base_url=base_url, 
        async_=async_, 
        **request_kwargs, 
    )


@overload
def share_iterdir(
    share_key: str, 
    share_pwd: str = "", 
    parent_id: int = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    cooldown: int | float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    *, 
    async_: Literal[False] = False, 
    **request_kwargs, 
) -> Iterator[dict]:
    ...
@overload
def share_iterdir(
    share_key: str, 
    share_pwd: str = "", 
    parent_id: int = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    cooldown: int | float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    *, 
    async_: Literal[True], 
    **request_kwargs, 
) -> AsyncIterator[dict]:
    ...
def share_iterdir(
    share_key: str, 
    share_pwd: str = "", 
    parent_id: int = 0, 
    min_depth: int = 1, 
    max_depth: int = 1, 
    predicate: None | Callable[[dict], Literal[None, 0, 1, False, True]] = None, 
    cooldown: int | float = 0, 
    base_url: None | str | Callable[[], str] = None, 
    *, 
    async_: Literal[False, True] = False, 
    **request_kwargs, 
) -> Iterator[dict] | AsyncIterator[dict]:
    """遍历分享的文件列表

    :param share_key: 分享码或者分享链接（可以携带提取码）

        .. note::
            在分享链接中的位置形如 f"https://www.123pan.com/s/{share_key}"

            如果携带提取码，要写成 f"https://www.123pan.com/s/{share_key}?提取码:{share_pwd}"

            上面的基地址不必是 "https://www.123pan.com"

    :param share_pwd: 提取码（4个文字），可以为空
    :param parent_id: 父目录 id，默认是根目录
    :param min_depth: 最小深度，小于此深度的不会输出
    :param max_depth: 最大深度，大于此深度的不会输出，如果小于 0 则无限
    :param predicate: 以文件或目录的信息作为参数进行调用，并以返回值作为筛选条件

        - 如果返回值是 0 或 None，则跳过此节点以及位于此节点之下的所有节点
        - 如果返回值是 1，则输出此节点，但跳过位于此节点之下的所有节点
        - 如果返回值是 False，则跳过此节点（但依然会继续处理位于此节点之下的节点）
        - 如果返回值是 True，则输出此节点

    :param cooldown: 两次调用之间，冷却的时间（用两次调用开始时的时间差，而不是一次完成到下一次开始的时间差）
    :param base_url: 基地址，如果为空，则用默认
    :param async_: 是否异步
    :param request_kwargs: 其它请求参数

    :return: 迭代器，产生文件或目录的信息
    """
    if share_key.startswith(("http://", "https://")):
        urlp = urlsplit(share_key)
        # if not base_url:
        #     base_url = f"{urlp.scheme}://{urlp.netloc}"
        share_key = urlp.path.rsplit("/", 1)[-1]
        if not share_pwd:
            share_pwd = urlp.query.rpartition(":")[-1]
            if len(share_pwd) != 4:
                share_pwd = ""
    return _iterdir(
        P123Client.share_fs_list, 
        {"ShareKey": share_key, "SharePwd": share_pwd}, 
        parent_id=parent_id, 
        min_depth=min_depth, 
        max_depth=max_depth, 
        predicate=predicate, 
        cooldown=cooldown, 
        base_url=base_url, 
        extra_data={"ShareKey": share_key, "SharePwd": share_pwd}, 
        async_=async_, 
        **request_kwargs, 
    )

