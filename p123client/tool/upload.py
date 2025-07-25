#!/usr/bin/env python3
# encoding: utf-8

__author__ = "ChenyangGao <https://chenyanggao.github.io>"
__all__ = ["upload_uri"]

from collections.abc import Coroutine

from typing import Literal
from typing import overload, Any, Literal
from urllib.parse import unquote

from p123client import P123Client


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

