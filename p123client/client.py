#!/usr/bin/env python3
# encoding: utf-8

from __future__ import annotations

__all__ = ["check_response", "P123OpenClient", "P123Client"]

import errno

from asyncio import Lock as AsyncLock
from base64 import urlsafe_b64decode
from collections.abc import (
    AsyncIterable, Awaitable, Buffer, Callable, Coroutine, 
    Iterable, MutableMapping, 
)
from contextlib import contextmanager
from datetime import datetime
from functools import partial
from hashlib import md5
from http.cookiejar import CookieJar
from inspect import isawaitable
from itertools import count
from os import fsdecode, fstat, isatty, PathLike
from os.path import basename
from pathlib import Path, PurePath
from re import compile as re_compile, MULTILINE
from string import digits, hexdigits, ascii_uppercase
from sys import _getframe
from tempfile import TemporaryFile
from threading import Lock
from typing import cast, overload, Any, Final, Literal, Self
from urllib.parse import parse_qsl, urlsplit
from uuid import uuid4
from warnings import warn

from asynctools import ensure_async
from dicttools import dict_key_to_lower_merge, dict_map
from filewrap import (
    bio_chunk_iter, bio_chunk_async_iter, buffer_length, 
    bytes_iter_to_reader, bytes_iter_to_async_reader, 
    copyfileobj, copyfileobj_async, SupportsRead, 
)
from hashtools import file_digest, file_digest_async
from http_request import SupportsGeturl
from iterutils import run_gen_step
from orjson import loads
from property import locked_cacheproperty
from yarl import URL

from .const import CLIENT_API_METHODS_MAP, CLIENT_METHOD_API_MAP
from .exception import (
    P123Warning, P123OSError, P123BrokenUpload, P123LoginError, 
    P123AuthenticationError, P123FileNotFoundError, 
)


# 可以使用的域名（http 和 https 都可以，并可以加后缀 /a 或 /b，但加了后缀不一定可用（可能会报 401 错误））
# https://123pan.com
# https://123pan.cn
# https://www.123pan.com
# https://www.123pan.cn
# https://login.123pan.com
# https://www.123684.com
# https://www.123865.com
# https://www.123912.com
# https://123912.com
DEFAULT_BASE_URL: Final = "https://www.123pan.com/b"
DEFAULT_LOGIN_BASE_URL: Final = "https://login.123pan.com"
DEFAULT_OPEN_BASE_URL: Final = "https://open-api.123pan.com"
# 默认的请求函数
_httpx_request = None


def get_default_request():
    global _httpx_request
    if _httpx_request is None:
        from httpx_request import request
        _httpx_request = partial(request, timeout=(5, 60, 60, 5))
    return _httpx_request


def default_parse(_, content: Buffer, /):
    if isinstance(content, (bytes, bytearray, memoryview)):
        return loads(content)
    else:
        return loads(memoryview(content))


def complete_url(
    path: str, 
    base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
) -> str:
    if path.startswith("//"):
        return "https:" + path
    elif path.startswith(("http://", "https://")):
        return path
    if not base_url:
        base_url = DEFAULT_BASE_URL
    elif callable(base_url):
        base_url = base_url()
    if not path.startswith("/"):
        path = "/api/" + path
    return base_url + path


def update_headers_in_kwargs(
    request_kwargs: dict, 
    /, 
    *args, 
    **kwargs, 
):
    if headers := request_kwargs.get("headers"):
        headers = dict(headers)
    else:
        headers = {}
    headers.update(*args, **kwargs)
    request_kwargs["headers"] = headers


def escape_filename(
    s: str, 
    /, 
    table: dict[int, int | str] = {c: chr(c+65248) for c in b'"\\/:*?|><'}, # type: ignore
) -> str:
    return s.translate(table)


@contextmanager
def temp_globals(f_globals: None | dict = None, /, **ns):
    if f_globals is None:
        f_globals = _getframe(2).f_globals
    old_globals = f_globals.copy()
    if ns:
        f_globals.update(ns)
    try:
        yield f_globals
    finally:
        f_globals.clear()
        f_globals.update(old_globals)


@overload
def check_response(resp: dict, /) -> dict:
    ...
@overload
def check_response(resp: Awaitable[dict], /) -> Coroutine[Any, Any, dict]:
    ...
def check_response(resp: dict | Awaitable[dict], /) -> dict | Coroutine[Any, Any, dict]:
    """检测 123 的某个接口的响应，如果成功则直接返回，否则根据具体情况抛出一个异常，基本上是 OSError 的实例
    """
    def check(resp, /) -> dict:
        if not isinstance(resp, dict):
            raise P123OSError(errno.EIO, resp)
        code = resp.get("code", 0)
        if code in (0, 200):
            return resp
        match code:
            case 1: # 内部错误
                raise P123AuthenticationError(errno.EIO, resp)
            case 401: # access_token 失效
                raise P123AuthenticationError(errno.EAUTH, resp)
            case 429: # 请求太频繁
                raise P123OSError(errno.EBUSY, resp)
            case 5066: # 文件不存在
                raise P123FileNotFoundError(errno.ENOENT, resp)
            case 5113: # 流量超限
                raise P123OSError(errno.EIO, resp)
            case _:
                raise P123OSError(errno.EIO, resp)
    if isawaitable(resp):
        async def check_await() -> dict:
            return check(await resp)
        return check_await()
    else:
        return check(resp)


class P123OpenClient:
    """123 网盘客户端，仅使用开放接口

    .. admonition:: Reference

        https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced

    :param client_id: 应用标识，创建应用时分配的 appId
    :param client_secret: 应用密钥，创建应用时分配的 secretId
    :param token: 123 的访问令牌
    :param refresh_token: 刷新令牌
    :param check_for_relogin: 当 access_token 失效时，是否重新登录
    """
    client_id: str = ""
    client_secret: str = ""
    refresh_token: str = ""
    token_path: None | PurePath = None
    check_for_relogin: bool = False

    def __init__(
        self, 
        /, 
        client_id: str | PathLike = "", 
        client_secret: str = "", 
        token: None | str | PathLike = None, 
        refresh_token: str = "", 
        check_for_relogin: bool = True, 
    ):
        self.init(
            client_id=client_id, 
            client_secret=client_secret, 
            token=token, 
            refresh_token=refresh_token, 
            check_for_relogin=check_for_relogin, 
            instance=self, 
        )

    @overload
    @classmethod
    def init(
        cls, 
        /, 
        client_id: str | PathLike = "", 
        client_secret: str = "", 
        token: None | str | PathLike = None, 
        refresh_token: str = "", 
        check_for_relogin: bool = True, 
        instance: None | Self = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> P123OpenClient:
        ...
    @overload
    @classmethod
    def init(
        cls, 
        /, 
        client_id: str | PathLike = "", 
        client_secret: str = "", 
        token: None | str | PathLike = None, 
        refresh_token: str = "", 
        check_for_relogin: bool = True, 
        instance: None | Self = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, P123OpenClient]:
        ...
    @classmethod
    def init(
        cls, 
        /, 
        client_id: str | PathLike = "", 
        client_secret: str = "", 
        token: None | str | PathLike = None, 
        refresh_token: str = "", 
        check_for_relogin: bool = True, 
        instance: None | Self = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> P123OpenClient | Coroutine[Any, Any, P123OpenClient]:
        def gen_step():
            nonlocal token
            if instance is None:
                self = cls.__new__(cls)
            else:
                self = instance
            if isinstance(client_id, PathLike):
                token = client_id
            else:
                self.client_id = client_id
            self.client_secret = client_secret
            self.refresh_token = refresh_token
            if token is None:
                if client_id and client_secret or refresh_token:
                    yield self.login_open(async_=async_, **request_kwargs)
            elif isinstance(token, str):
                self.token = token.removeprefix("Bearer ")
            else:
                if isinstance(token, PurePath) and hasattr(token, "open"):
                    self.token_path = token
                else:
                    self.token_path = Path(fsdecode(token))
                self._read_token()
                if not self.token and (client_id and client_secret or refresh_token):
                    yield self.login_open(async_=async_, **request_kwargs)
            self.check_for_relogin = check_for_relogin
            return self
        return run_gen_step(gen_step, async_)

    @locked_cacheproperty
    def request_lock(self, /) -> Lock:
        return Lock()

    @locked_cacheproperty
    def request_alock(self, /) -> AsyncLock:
        return AsyncLock()

    @property
    def cookies(self, /):
        """请求所用的 Cookies 对象（同步和异步共用）
        """
        try:
            return self.__dict__["cookies"]
        except KeyError:
            from httpx import Cookies
            cookies = self.__dict__["cookies"] = Cookies()
            return cookies

    @property
    def cookiejar(self, /) -> CookieJar:
        """请求所用的 CookieJar 对象（同步和异步共用）
        """
        return self.cookies.jar

    @property
    def headers(self, /) -> MutableMapping:
        """请求头，无论同步还是异步请求都共用这个请求头
        """
        try:
            return self.__dict__["headers"]
        except KeyError:
            from multidict import CIMultiDict
            headers = self.__dict__["headers"] = CIMultiDict({
                "accept": "*/*", 
                "accept-encoding": "gzip, deflate", 
                "app-version": "3", 
                "connection": "keep-alive", 
                "platform": "open_platform", 
                "user-agent": "Mozilla/5.0 AppleWebKit/600 Safari/600 Chrome/124.0.0.0 Edg/124.0.0.0", 
            })
            return headers

    @locked_cacheproperty
    def session(self, /):
        """同步请求的 session 对象
        """
        import httpx_request
        from httpx import Client, HTTPTransport, Limits
        session = Client(
            limits=Limits(max_connections=256, max_keepalive_connections=64, keepalive_expiry=10), 
            transport=HTTPTransport(retries=5), 
            verify=False, 
        )
        setattr(session, "_headers", self.headers)
        setattr(session, "_cookies", self.cookies)
        return session

    @locked_cacheproperty
    def async_session(self, /):
        """异步请求的 session 对象
        """
        import httpx_request
        from httpx import AsyncClient, AsyncHTTPTransport, Limits
        session = AsyncClient(
            limits=Limits(max_connections=256, max_keepalive_connections=64, keepalive_expiry=10), 
            transport=AsyncHTTPTransport(retries=5), 
            verify=False, 
        )
        setattr(session, "_headers", self.headers)
        setattr(session, "_cookies", self.cookies)
        return session

    @property
    def token(self, /) -> str:
        return self.__dict__.get("token", "")

    @token.setter
    def token(self, token: str, /):
        if token != self.token:
            self._write_token(token)
            ns = self.__dict__
            ns["token"] = token
            if token:
                self.headers["authorization"] = f"Bearer {token}"
            else:
                self.headers.pop("authorization", None)
                ns.pop("token_user_info", None)
                ns.pop("user_id", None)

    @token.deleter
    def token(self, /):
        self.token = ""

    @locked_cacheproperty
    def token_user_info(self, /) -> dict:
        return loads(urlsafe_b64decode(self.token.split(".", 2)[1] + "=="))

    @locked_cacheproperty
    def user_id(self, /) -> dict:
        return self.token_user_info["id"]

    def _read_token(
        self, 
        /, 
        encoding: str = "latin-1", 
    ) -> None | str:
        if token_path := self.token_path:
            try:
                with token_path.open("rb") as f: # type: ignore
                    token = str(f.read().strip(), encoding)
                self.token = token.removeprefix("Bearer ")
                return token
            except OSError:
                pass
        return self.token

    def _write_token(
        self, 
        token: None | str = None, 
        /, 
        encoding: str = "latin-1", 
    ):
        if token_path := self.token_path:
            if token is None:
                token = self.token
            token_bytes = bytes(token, encoding)
            with token_path.open("wb") as f: # type: ignore
                f.write(token_bytes)

    def can_relogin(self, /) -> bool:
        return self.check_for_relogin and bool(
            self.client_id and self.client_secret or 
            getattr(self, "refresh_token")
        )

    def request(
        self, 
        /, 
        url: str, 
        method: str = "GET", 
        request: None | Callable = None, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        headers = None, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ):
        """执行 HTTP 请求，默认为 GET 方法
        """
        if not url.startswith(("http://", "https://")):
            url = complete_url(url, base_url)
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request_kwargs["session"] = self.async_session if async_ else self.session
            request_kwargs["async_"] = async_
            request = get_default_request()
        request_headers = dict(self.headers)
        if isinstance(headers, str):
            request_headers["platform"] = headers
        elif headers:
            request_headers.update(headers)
        request_kwargs["headers"] = request_headers
        if not self.check_for_relogin:
            return request(
                url=url, 
                method=method, 
                **request_kwargs, 
            )
        request_headers.setdefault("authorization", "")
        def gen_step():
            if async_:
                lock: Lock | AsyncLock = self.request_alock
            else:
                lock = self.request_lock
            for i in count(0):
                token = request_headers["authorization"].removeprefix("Bearer ")
                resp = yield cast(Callable, request)(
                    url=url, 
                    method=method, 
                    **request_kwargs, 
                )
                if not (isinstance(resp, dict) and resp.get("code") == 401):
                    return resp
                yield lock.acquire()
                try:
                    token_new: str = self.token
                    if token == token_new:
                        if self.__dict__.get("token_path"):
                            token_new = self._read_token() or ""
                            if token != token_new:
                                request_headers["authorization"] = "Bearer " + self.token
                                continue
                        if i or not self.can_relogin():
                            return resp
                        user_id = getattr(self, "user_id", None)
                        warn(f"relogin to refresh token: {user_id=}", category=P123Warning)
                        yield self.login(replace=True, async_=async_)
                        request_headers["authorization"] = "Bearer " + self.token
                    else:
                        request_headers["authorization"] = "Bearer " + token_new
                finally:
                    lock.release()
        return run_gen_step(gen_step, async_)

    @overload
    def login(
        self, 
        /, 
        client_id: str = "", 
        client_secret: str = "", 
        refresh_token: str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def login(
        self, 
        /, 
        client_id: str = "", 
        client_secret: str = "", 
        refresh_token: str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def login(
        self, 
        /, 
        client_id: str = "", 
        client_secret: str = "", 
        refresh_token: str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """登录以获取 access_token

        :param client_id: 应用标识，创建应用时分配的 appId
        :param client_secret: 应用密钥，创建应用时分配的 secretId
        :param refresh_token: 刷新令牌
        :param base_url: 接口的基地址
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口的响应信息
        """
        if client_id:
            self.client_id = client_id
        else:
            client_id = self.client_id
        if client_secret:
            self.client_secret = client_secret
        else:
            client_secret = self.client_secret
        if refresh_token:
            self.refresh_token = refresh_token
        else:
            refresh_token = self.refresh_token
        def gen_step():
            if refresh_token:
                resp = yield self.login_with_refresh_token(
                    refresh_token, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                self.token = resp["access_token"]
                self.refresh_token = resp["refresh_token"]
                return resp
            else:
                resp = yield self.login_token_open( # type: ignore
                    {"clientID": client_id, "clientSecret": client_secret}, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                self.token = resp["data"]["accessToken"]
                return resp
        return run_gen_step(gen_step, async_)

    @overload
    def login_another_oauth(
        self, 
        /, 
        redirect_uri: str, 
        client_id: str = "", 
        client_secret: str = "", 
        replace: bool | Self = False, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> Self:
        ...
    @overload
    def login_another_oauth(
        self, 
        /, 
        redirect_uri: str, 
        client_id: str = "", 
        client_secret: str = "", 
        replace: bool | Self = False, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, Self]:
        ...
    def login_another_oauth(
        self, 
        /, 
        redirect_uri: str, 
        client_id: str = "", 
        client_secret: str = "", 
        replace: bool | Self = False, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> Self | Coroutine[Any, Any, Self]:
        """第三方应用授权登录

        :param redirect_uri: 回调链接
        :param client_id: 应用标识，创建应用时分配的 appId
        :param client_secret: 应用密钥，创建应用时分配的 secretId
        :param replace: 替换某个 client 对象的 token

            - 如果为 P123Client, 则更新到此对象
            - 如果为 True，则更新到 `self``
            - 如果为 False，否则返回新的 ``P123Client`` 对象

        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应
        """
        if client_id:
            self.client_id = client_id
        else:
            client_id = self.client_id
        if client_secret:
            self.client_secret = client_secret
        else:
            client_secret = self.client_secret
        def gen_step():
            resp = yield self.login_with_oauth(
                client_id, 
                client_secret, 
                redirect_uri=redirect_uri, 
                token=self.token, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
            token = resp["access_token"]
            refresh_token = resp["refresh_token"]
            if replace is False:
                return type(self)(
                    client_id=client_id, 
                    client_secret=client_secret, 
                    token=token, 
                    refresh_token=refresh_token, 
                )
            elif replace is True:
                inst = self
            else:
                inst = replace
            inst.token = token
            inst.refresh_token = refresh_token
            return inst
        return run_gen_step(gen_step, async_)

    @overload
    def login_another_refresh_token(
        self, 
        /, 
        refresh_token: str = "", 
        replace: bool | Self = False, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> Self:
        ...
    @overload
    def login_another_refresh_token(
        self, 
        /, 
        refresh_token: str = "", 
        replace: bool | Self = False, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, Self]:
        ...
    def login_another_refresh_token(
        self, 
        /, 
        refresh_token: str = "", 
        replace: bool | Self = False, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> Self | Coroutine[Any, Any, Self]:
        """登录以获取 access_token

        :param refresh_token: 刷新令牌
        :param replace: 替换某个 client 对象的 token

            - 如果为 P123Client, 则更新到此对象
            - 如果为 True，则更新到 `self``
            - 如果为 False，否则返回新的 ``P123Client`` 对象

        :param base_url: 接口的基地址
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口的响应信息
        """
        if refresh_token:
            self.refresh_token = refresh_token
        else:
            refresh_token = self.refresh_token
        def gen_step():
            nonlocal refresh_token
            resp = yield self.login_with_refresh_token(
                refresh_token, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
            token = resp["access_token"]
            refresh_token = resp["refresh_token"]
            if replace is False:
                return type(self)(
                    token=token, 
                    refresh_token=refresh_token, 
                )
            elif replace is True:
                inst = self
            else:
                inst = replace
            inst.token = token
            inst.refresh_token = refresh_token
            return inst
        return run_gen_step(gen_step, async_)

    @overload
    def login_with_oauth(
        cls, 
        /, 
        client_id: str, 
        client_secret: str, 
        redirect_uri: str, 
        token: str, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def login_with_oauth(
        cls, 
        /, 
        client_id: str, 
        client_secret: str, 
        redirect_uri: str, 
        token: str, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def login_with_oauth(
        cls, 
        /, 
        client_id: str, 
        client_secret: str, 
        redirect_uri: str, 
        token: str, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """第三方应用授权登录

        :param client_id: 应用标识，创建应用时分配的 appId
        :param client_secret: 应用密钥，创建应用时分配的 secretId
        :param redirect_uri: 回调链接
        :param token: 访问令牌
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应
        """
        def gen_step():
            resp = yield cls.login_oauth_authorize(
                {"accessToken": token, "client_id": client_id, "redirect_uri": redirect_uri}, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
            check_response(resp)
            authorization_code = resp["data"]["code"]
            return cls.login_oauth_token(
                {
                    "client_id": client_id, 
                    "client_secret": client_secret, 
                    "code": authorization_code, 
                    "grant_type": "authorization_code", 
                    "redirect_uri": redirect_uri, 
                }, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
        return run_gen_step(gen_step, async_)

    @overload
    def login_with_refresh_token(
        cls, 
        /, 
        refresh_token: str, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def login_with_refresh_token(
        cls, 
        /, 
        refresh_token: str, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def login_with_refresh_token(
        cls, 
        /, 
        refresh_token: str, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """通过刷新令牌登录

        :param refresh_token: 刷新令牌
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应
        """
        return cls.login_oauth_token(
            {"grant_type": "refresh_token", "refresh_token": refresh_token}, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    ########## Developer API ##########

    @overload
    def developer_config_forbide_ip_list(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def developer_config_forbide_ip_list(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def developer_config_forbide_ip_list(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """ip黑名单列表

        GET https://open-api.123pan.com/api/v1/developer/config/forbide-ip/list

        .. admonition:: Reference

            /API列表/直链/IP黑名单配置/ip黑名单列表

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/mxldrm9d5gpw5h2d

        .. caution::
            获取用户配置的黑名单     
        """
        api = complete_url("/api/v1/developer/config/forbide-ip/list", base_url)
        return self.request(api, async_=async_, **request_kwargs)

    @overload
    def developer_config_forbide_ip_switch(
        self, 
        payload: dict | Literal[1, 2] = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def developer_config_forbide_ip_switch(
        self, 
        payload: dict | Literal[1, 2] = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def developer_config_forbide_ip_switch(
        self, 
        payload: dict | Literal[1, 2] = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """开启关闭ip黑名单

        POST https://open-api.123pan.com/api/v1/developer/config/forbide-ip/switch

        .. admonition:: Reference

            /API列表/直链/IP黑名单配置/开启关闭ip黑名单

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/xwx77dbzrkxquuxm

        .. caution::
            此接口需要开通开发者权益

        :payload:
            - Status: 1 | 2 = 1 💡 状态：1:启用 2:禁用 
        """
        api = complete_url("/api/v1/developer/config/forbide-ip/switch", base_url)
        if not isinstance(payload, dict):
            payload = {"Status": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def developer_config_forbide_ip_update(
        self, 
        payload: dict | Iterable[str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def developer_config_forbide_ip_update(
        self, 
        payload: dict | Iterable[str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def developer_config_forbide_ip_update(
        self, 
        payload: dict | Iterable[str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """更新ip黑名单列表

        POST https://open-api.123pan.com/api/v1/developer/config/forbide-ip/update

        .. admonition:: Reference

            /API列表/直链/IP黑名单配置/更新ip黑名单列表

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/tt3s54slh87q8wuh

        .. caution::
            此接口需要开通开发者权益

        :payload:
            - IpList: list[str] 💡 IP 地址列表，最多 500 个 IPv4 地址
        """
        api = complete_url("/api/v1/developer/config/forbide-ip/update", base_url)
        if not isinstance(payload, dict):
            if not isinstance(payload, (list, tuple)):
                payload = list(payload)
            payload = {"IpList": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    ########## Direct Link API ##########

    @overload
    def dlink_disable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_disable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_disable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """禁用直链空间

        POST https://open-api.123pan.com/api/v1/direct-link/disable

        .. admonition:: Reference

            /API列表/直链/禁用直链空间

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/ccgz6fwf25nd9psl

        :payload:
            - fileID: int 💡 目录 id
        """
        api = complete_url("/api/v1/direct-link/disable", base_url)
        if not isinstance(payload, dict):
            payload = {"fileID": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def dlink_enable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_enable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_enable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """启用直链空间

        POST https://open-api.123pan.com/api/v1/direct-link/enable

        .. admonition:: Reference

            /API列表/直链/启用直链空间

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/cl3gvdmho288d376

        :payload:
            - fileID: int 💡 目录 id
        """
        api = complete_url("/api/v1/direct-link/enable", base_url)
        if not isinstance(payload, dict):
            payload = {"fileID": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def dlink_log(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_log(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_log(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取直链日志

        GET https://open-api.123pan.com/api/v1/direct-link/log

        .. admonition:: Reference

            /API列表/直链/获取直链日志

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/agmqpmu0dm0iogc9

        .. caution::
            此接口需要开通开发者权益，并且仅限查询近 3 天的日志数据

        :payload:
            - pageNum: int                           💡 第几页
            - pageSize: int  = 100                   💡 分页大小
            - startTime: str = "0001-01-01 00:00:00" 💡 开始时间，格式：YYYY-MM-DD hh:mm:ss
            - endTime: str.  = "9999-12-31 23:59:59" 💡 结束时间，格式：YYYY-MM-DD hh:mm:ss
        """
        api = complete_url("/api/v1/direct-link/log", base_url)
        if not isinstance(payload, dict):
            payload = {"pageNum": payload}
        payload = dict_key_to_lower_merge(payload, {
            "pageSize": 100, 
            "startTime": "0001-01-01 00:00:00", 
            "endTime": "9999-12-31 23:59:59", 
        })
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def dlink_m3u8(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_m3u8(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_m3u8(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取直链转码链接

        GET https://open-api.123pan.com/api/v1/direct-link/get/m3u8

        :payload:
            - fileID: int 💡 文件 id

        :return:
            响应数据的 data 字段是一个字典，键值如下：

            +-------------------------+--------+----------+----------------------------------------------------------------+
            | 名称                    | 类型   | 是否必填 | 说明                                                           |
            +=========================+========+==========+================================================================+
            | ``list``                | array  | 必填     | 响应列表                                                       |
            +-------------------------+--------+----------+----------------------------------------------------------------+
            | ``list[*].resolutions`` | string | 必填     | 分辨率                                                         |
            +-------------------------+--------+----------+----------------------------------------------------------------+
            | ``list[*].address``     | string | 必填     | | 播放地址。请将播放地址放入支持的 hls 协议的播放器中进行播放。|
            |                         |        |          | | 示例在线播放地址: https://m3u8-player.com/                   |
            |                         |        |          | | 请注意：转码链接播放过程中将会消耗您的直链流量。             |
            |                         |        |          | | 如果您开启了直链鉴权,也需要将转码链接根据鉴权指引进行签名。  |
            +-------------------------+--------+----------+----------------------------------------------------------------+
        """
        api = complete_url("/api/v1/direct-link/get/m3u8", base_url)
        if not isinstance(payload, dict):
            payload = {"fileID": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def dlink_offline_log(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_offline_log(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_offline_log(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取直链离线日志

        GET https://open-api.123pan.com/api/v1/direct-link/offline/logs

        .. admonition:: Reference

            /API列表/直链/获取直链离线日志

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/yz4bdynw9yx5erqb

        .. caution::
            此接口需要开通开发者权益，并且仅限查询近30天的日志数据

        :payload:
            - pageNum: int                  💡 第几页
            - pageSize: int  = 100          💡 分页大小
            - startHour: str = "0001010100" 💡 开始时间，格式：YYYYMMDDhh
            - endHour: str.  = "9999123123" 💡 结束时间，格式：YYYYMMDDhh
        """
        api = complete_url("/api/v1/direct-link/offline/logs", base_url)
        if not isinstance(payload, dict):
            payload = {"pageNum": payload}
        payload = dict_key_to_lower_merge(payload, {
            "pageSize": 100, 
            "startTime": "0001010100", 
            "endTime": "9999123123", 
        })
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def dlink_transcode(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_transcode(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_transcode(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """发起直链转码

        POST https://open-api.123pan.com/api/v1/direct-link/doTranscode

        :payload:
            - ids: list[int] 💡 视频文件 id 列表
        """
        api = complete_url("/api/v1/direct-link/doTranscode", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"ids": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def dlink_transcode_query(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_transcode_query(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_transcode_query(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """查询直链转码进度

        POST https://open-api.123pan.com/api/v1/direct-link/queryTranscode

        :payload:
            - ids: str 💡 视频文件 id 列表

        :return:
            响应数据的 data 字段是一个字典，键值如下：

            +-----------+-------+----------+-------------------------------------------+
            | 名称      | 类型  | 是否必填 | 说明                                      |
            +===========+=======+==========+===========================================+
            | noneList  | array | 必填     | 未发起过转码的 ID                         |
            | errorList | array | 必填     | 错误文件ID列表,这些文件ID无法进行转码操作 |
            | success   | array | 必填     | 转码成功的文件ID列表                      |
            +-----------+-------+----------+-------------------------------------------+
        """
        api = complete_url("/api/v1/direct-link/queryTranscode", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"ids": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def dlink_url(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_url(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_url(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取直链链接

        GET https://open-api.123pan.com/api/v1/direct-link/url

        .. admonition:: Reference

            /API列表/直链/获取直链链接

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/tdxfsmtemp4gu4o2

        :payload:
            - fileID: int 💡 文件 id
        """
        api = complete_url("/api/v1/direct-link/url", base_url)
        if not isinstance(payload, dict):
            payload = {"fileID": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    ########## Download API ##########

    @overload
    def download_info(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def download_info(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def download_info(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """下载

        GET https://open-api.123pan.com/api/v1/file/download_info

        .. admonition:: Reference

            /API列表/文件管理/下载

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/fnf60phsushn8ip2

        :payload:
            - fileId: int 💡 文件 id
        """
        api = complete_url("/api/v1/file/download_info", base_url)
        update_headers_in_kwargs(request_kwargs, platform="android")
        if not isinstance(payload, dict):
            payload = {"fileId": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    ########## File System API ##########

    @overload
    def fs_copy(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_copy(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_copy(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """批量复制文件

        POST https://open-api.123pan.com/api/v1/file/async/copy

        .. admonition:: Reference

            /API列表/文件管理/复制/批量复制文件

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/pik0i4lvxw4lkkc7

        :payload:
            - fileIDs: list[int] 💡 文件 id 列表，单级最多支持 3000 个
            - targetDirId: int = 0 💡 要复制到的目标文件夹 id

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "taskId": int, # 任务 id，后续用来查询任务进度
                }
        """
        api = complete_url("/api/v1/file/async/copy", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIDs": payload}
        payload = dict_key_to_lower_merge(payload, targetDirId=parent_id)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def fs_copy_one(
        self, 
        payload: dict | int | str, 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_copy_one(
        self, 
        payload: dict | int | str, 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_copy_one(
        self, 
        payload: dict | int | str, 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """复制单个文件

        POST https://open-api.123pan.com/api/v1/file/copy

        .. admonition:: Reference

            /API列表/文件管理/复制/复制单个文件

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/thpz0w9er500pob9

        :payload:
            - fileId: int 💡 文件 id
            - targetDirId: int = 0 💡 要复制到的目标文件夹 id
        """
        api = complete_url("/api/v1/file/copy", base_url)
        if not isinstance(payload, dict):
            payload = {"fileId": payload}
        payload = dict_key_to_lower_merge(payload, targetDirId=parent_id)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def fs_copy_process(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_copy_process(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_copy_process(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """批量复制文件进度

        GET https://open-api.123pan.com/api/v1/file/async/copy/process

        .. admonition:: Reference

            /API列表/文件管理/复制/批量复制文件进度

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/fqh9vk1esg4uomly

        :payload:
            - taskId: int 💡 任务 id

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "taskId": int, # 任务 id
                    "status": int, # 任务状态：0-待处理 1-进行中 2-已完成 3-失败
                }
        """
        api = complete_url("/api/v1/file/async/copy/process", base_url)
        if not isinstance(payload, dict):
            payload = {"taskId": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def fs_delete(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_delete(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_delete(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """彻底删除文件

        POST https://open-api.123pan.com/api/v1/file/delete

        .. attention::
            彻底删除文件前，文件必须要在回收站中，否则无法删除        

        .. admonition:: Reference

            /API列表/文件管理/删除/彻底删除文件

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/sg2gvfk5i3dwoxtg

        :payload:
            - fileIDs: list[int] 💡 文件 id 列表，最多 100 个
        """
        api = complete_url("/api/v1/file/delete", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIDs": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def fs_detail(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_detail(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_detail(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取单个文件详情

        GET https://open-api.123pan.com/api/v1/file/detail

        .. admonition:: Reference

            /API列表/文件管理/文件详情/获取单个文件详情

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/owapsz373dzwiqbp

        .. note::
            支持查询单文件夹包含文件大小            

        :payload:
            - fileID: int 💡 文件 id
        """
        api = complete_url("/api/v1/file/detail", base_url)
        if not isinstance(payload, dict):
            payload = {"fileID": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def fs_info(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_info(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_info(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取多个文件详情

        POST https://open-api.123pan.com/api/v1/file/infos

        .. admonition:: Reference

            /API列表/文件管理/文件详情/获取多个文件详情

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/cqqayfuxybegrlru

        :payload:
            - fileIds: list[int] 💡 文件 id 列表
        """
        api = complete_url("/api/v1/file/infos", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIds": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def fs_list(
        self, 
        payload: dict | int | str = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_list(
        self, 
        payload: dict | int | str = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_list(
        self, 
        payload: dict | int | str = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取文件列表（推荐）

        GET https://open-api.123pan.com/api/v2/file/list

        .. admonition:: Reference

            /API列表/文件管理/文件列表/获取文件列表（推荐）

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/zrip9b0ye81zimv4

            /API列表/视频转码/上传视频/云盘上传/获取云盘视频文件

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/yqyi3rqrmrpvdf0d

            /API列表/视频转码/获取视频信息/获取转码空间文件列表

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/ux9wct58lvllxm1n

        .. note::
            如果返回信息中，"lastFileId" 字段的值为 "-1"，代表最后一页（无需再翻页查询）。
            其它则代表下一页开始的文件 id，携带到请求参数中，可查询下一页。

        .. caution::
            此接口查询结果包含回收站的文件，需自行根据字段 ``trashed`` 判断处理

            此接口不支持排序

        :payload:
            - businessType: int = <default> 💡 业务类型：2:转码空间
            - category: int = <default>     💡 分类代码：0:未知 1:音频 2:视频 3:图片 4:音频 5:其它 6:保险箱 7:收藏夹
            - lastFileId: int = <default>   💡 上一页的最后一条记录的 FileID，翻页查询时需要填写
            - limit: int = 100              💡 分页大小，最多 100
            - parentFileId: int | str = 0   💡 父目录 id，根目录是 0
            - searchData: str = <default>   💡 搜索关键字
            - searchMode: 0 | 1 = 0         💡 搜索模式

                - 0: 模糊搜索（将会根据搜索项分词，查找出相似的匹配项）
                - 1: 精准搜索（精准搜索需要提供完整的文件名）

            - trashed: bool  = False 💡 是否查看回收站的文件
        """
        api = complete_url("/api/v2/file/list", base_url)
        if isinstance(payload, (int, str)):
            payload = {"parentFileId": payload}
        payload = dict_key_to_lower_merge(payload, {
            "limit": 100, 
            "parentFileId": 0, 
            "searchMode": 0, 
            "trashed": False, 
        })
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    fs_list_v2 = fs_list

    @overload
    def fs_list_v1(
        self, 
        payload: dict | int | str = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_list_v1(
        self, 
        payload: dict | int | str = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_list_v1(
        self, 
        payload: dict | int | str = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取文件列表（旧）

        GET https://open-api.123pan.com/api/v1/file/list

        .. admonition:: Reference

            /API列表/文件管理/文件列表/获取文件列表（旧）

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/hosdqqax0knovnm2

        .. note::
            是否有下一页需要自行判断。如果返回的列表大小 < ``limit``，或者根据返回值里的 "total"，如果 = ``page * limit``，都说明没有下一页

        :payload:
            - limit: int = 100         💡 分页大小，最多 100
            - orderBy: str = "file_name" 💡 排序依据

                - "file_id": 文件 id
                - "file_name": 文件名
                - "size":  文件大小
                - "create_at": 创建时间
                - "update_at": 创建时间
                - "update_time": 更新时间
                - "share_id": 分享 id
                - ...（其它可能值）

            - orderDirection: "asc" | "desc" = "asc" 💡 排序顺序

                - "asc": 升序，从小到大
                - "desc": 降序，从大到小

            - page: int = 1               💡 第几页，从 1 开始（可传 0 或不传，视为 1）
            - parentFileId: int | str = 0 💡 父目录 id，根目录是 0
            - trashed: bool  = False 💡 是否查看回收站的文件
            - searchData: str = <default> 💡 搜索关键字
        """
        api = complete_url("/api/v1/file/list", base_url)
        if isinstance(payload, (int, str)):
            payload = {"parentFileId": payload}
        payload = dict_key_to_lower_merge(payload, {
            "limit": 100, 
            "orderBy": "file_name", 
            "orderDirection": "asc", 
            "page": 1, 
            "parentFileId": 0, 
            "trashed": False, 
        })
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def fs_mkdir(
        self, 
        payload: dict | str, 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_mkdir(
        self, 
        payload: dict | str, 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_mkdir(
        self, 
        payload: dict | str, 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建目录

        POST https://open-api.123pan.com/upload/v1/file/mkdir

        .. admonition:: Reference

            /API列表/文件管理/上传/创建目录

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/ouyvcxqg3185zzk4

        :payload:
            - name: str 💡 文件名，不能重名
            - parentID: int = 0 💡 父目录 id，根目录是 0
        """
        api = complete_url("/upload/v1/file/mkdir", base_url)
        if not isinstance(payload, dict):
            payload = {"name": payload}
        payload = dict_key_to_lower_merge(payload, parentID=parent_id)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def fs_move(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_move(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_move(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """移动

        POST https://open-api.123pan.com/api/v1/file/move

        .. admonition:: Reference

            /API列表/文件管理/移动

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/rsyfsn1gnpgo4m4f

        :payload:
            - fileIDs: list[int] 💡 文件 id 列表，最多 100 个
            - toParentFileID: int = 0 💡 要移动到的目标目录 id，根目录是 0
        """
        api = complete_url("/api/v1/file/move", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIDs": payload}
        payload = dict_key_to_lower_merge(payload, toParentFileID=parent_id)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def fs_recover(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_recover(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_recover(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """从回收站恢复文件

        POST https://open-api.123pan.com/api/v1/file/recover

        .. note::
            将回收站的文件恢复至删除前的位置

        .. admonition:: Reference

            /API列表/文件管理/删除/从回收站恢复文件

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/kx9f8b6wk6g55uwy

        :payload:
            - fileIDs: list[int] 💡 文件 id 列表，最多 100 个

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "abnormalFileIDs": list[int], # 异常文件目录 id（父级目录不存在），可使用还原文件到指定目录接口；无异常文件则为空
                }
        """
        api = complete_url("/api/v1/file/recover", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIDs": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def fs_recover_by_path(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_recover_by_path(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_recover_by_path(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """还原文件到指定目录

        POST https://open-api.123pan.com/api/v1/file/recover/by_path

        .. note::
            将回收站的文件恢复至指定位置

        .. admonition:: Reference

            /API列表/文件管理/删除/还原文件到指定目录

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/cl24atug2sviq12z

        :payload:
            - fileIDs: list[int] 💡 文件 id 列表，最多 100 个
            - parentFileID: int = 0 💡 指定目录 id
        """
        api = complete_url("/api/v1/file/recover/by_path", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIDs": payload}
        payload = dict_key_to_lower_merge(payload, toParentFileID=parent_id)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def fs_rename(
        self, 
        payload: dict | str | tuple[int | str, str] | Iterable[str | tuple[int | str, str]], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_rename(
        self, 
        payload: dict | str | tuple[int | str, str] | Iterable[str | tuple[int | str, str]], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_rename(
        self, 
        payload: dict | str | tuple[int | str, str] | Iterable[str | tuple[int | str, str]], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """批量文件重命名

        POST https://open-api.123pan.com/api/v1/file/rename

        .. admonition:: Reference

            /API列表/文件管理/重命名/批量文件重命名

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/imhguepnr727aquk

        :payload:
            - renameList: list[str] 💡 列表，每个成员的格式为 f"{fileId}|{fileName}"，最多 30 个
        """
        api = complete_url("/api/v1/file/rename", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, str):
                payload = [payload]
            elif isinstance(payload, tuple):
                payload = ["%s|%s" % payload]
            else:
                payload = [s if isinstance(s, str) else "%s|%s" % s for s in payload]
            payload = {"renameList": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def fs_rename_one(
        self, 
        payload: dict | str | tuple[int | str, str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_rename_one(
        self, 
        payload: dict | str | tuple[int | str, str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_rename_one(
        self, 
        payload: dict | str | tuple[int | str, str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """单个文件重命名

        PUT https://open-api.123pan.com/api/v1/file/name

        .. admonition:: Reference

            /API列表/文件管理/重命名/单个文件重命名

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/ha6mfe9tteht5skc

        :payload:
            - fileId: int   💡 文件 id
            - fileName: str 💡 文件名
        """
        api = complete_url("/api/v1/file/name", base_url)
        if not isinstance(payload, dict):
            fid: int | str
            if isinstance(payload, str):
                fid, name = payload.split("|", 1)
            else:
                fid, name = payload
            payload = {"fileId": fid, "fileName": name}
        return self.request(api, "PUT", json=payload, async_=async_, **request_kwargs)

    @overload
    def fs_trash(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_trash(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_trash(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """删除文件至回收站

        POST https://open-api.123pan.com/api/v1/file/trash

        .. admonition:: Reference

            /API列表/文件管理/删除/删除文件至回收站

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/en07662k2kki4bo6

        :payload:
            - fileIDs: list[int] 💡 文件 id 列表，最多 100 个
        """
        api = complete_url("/api/v1/file/trash", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIDs": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    ########## Login API ##########

    @overload
    @staticmethod
    def login_token(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def login_token(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def login_token(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取access_token

        POST https://open-api.123pan.com/api/v1/access_token

        .. attention::
            此接口有访问频率限制。请获取到 ``access_token`` 后本地保存使用，并在 `access_token `过期前及时重新获取。``access_token`` 有效期根据返回的 "expiredAt" 字段判断。

        .. note::
            通过这种方式授权得到的 ``access_token``，各个接口分别允许一个较低的 QPS

            /接入指南/开发者接入/开发须知

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/txgcvbfgh0gtuad5

        .. admonition:: Reference

            /接入指南/开发者接入/获取access_token

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/gn1nai4x0v0ry9ki

        :payload:
            - clientID: str     💡 应用标识，创建应用时分配的 appId
            - clientSecret: str 💡 应用密钥，创建应用时分配的 secretId
        """
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            if headers := request_kwargs.get("headers"):
                headers = dict(headers, platform="open_platform")
            else:
                headers = {"platform": "open_platform"}
            request_kwargs["headers"] = headers
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("/api/v1/access_token", base_url), 
            method="POST", 
            json=payload, 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def login_oauth_authorize(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def login_oauth_authorize(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def login_oauth_authorize(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """授权以获取和 ``accessToken`` 绑定的 ``code``

        GET https://open-api.123pan.com/api/v1/oauth2/user/authorize

        .. admonition:: Reference

            /接入指南/第三方挂载应用接入/授权地址

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/gr7ggimkcysm18ap

        :payload:
            - accessToken: str  💡 访问令牌
            - client_id: str    💡 应用标识，创建应用时分配的 appId
            - redirect_uri: str 💡 回调链接
            - scope: str = "user:base,file:all:read,file:all:write" 💡 权限
            - response_type: str = "code"
            - state: str = <default>
        """
        def parse(resp, _, /):
            url = resp.headers["location"]
            data = dict(parse_qsl(urlsplit(url).query))
            if "code" in data:
                code = 0
                message = "ok"
            else:
                code = 1
                message = data.get("error_description") or "error"
            return {
                "code": code, 
                "message": message, 
                "url": url, 
                "data": data, 
                "headers": dict(resp.headers), 
            }
        request_kwargs.setdefault("parse", parse)
        request_kwargs["follow_redirects"] = False
        payload = dict_key_to_lower_merge(
            payload, 
            response_type="code", 
            scope="user:base,file:all:read,file:all:write", 
        )
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("/api/v1/oauth2/user/authorize", base_url), 
            params=payload, 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def login_oauth_token(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def login_oauth_token(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def login_oauth_token(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """通过 ``authorization_code`` 或 ``refresh_token`` 获取新的 ``access_token`` 和 ``refresh_token``

        POST https://open-api.123pan.com/api/v1/oauth2/access_token

        .. note::
            通过这种方式授权得到的 ``access_token``，各个接口分别允许更高的 QPS

            /接入指南/第三方挂载应用接入/授权须知

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/kf05anzt1r0qnudd

        .. admonition:: Reference

            /接入指南/第三方挂载应用接入/授权code获取access_token

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/gammzlhe6k4qtwd9

        :payload:
            - client_id: str        💡 应用标识，创建应用时分配的 appId
            - client_secret: str    💡 应用密钥，创建应用时分配的 secretId
            - code: str = <default> 💡 授权码
            - grant_type: "authorization_code" | "refresh_token" = <default> 💡 身份类型
            - redirect_uri: str = <default>  💡 应用注册的回调地址，``grant_type`` 为 "authorization_code" 时必携带
            - refresh_token: str = <default> 💡 刷新 token，单次请求有效
        """
        request_kwargs.setdefault("parse", default_parse)
        payload = dict_map(payload, key=str.lower)
        if not payload.get("grant_type"):
            if payload.get("refresh_token"):
                payload["grant_type"] = "refresh_token"
            else:
                payload["grant_type"] = "authorization_code"
        if request is None:
            if headers := request_kwargs.get("headers"):
                headers = dict(headers, platform="open_platform")
            else:
                headers = {"platform": "open_platform"}
            request_kwargs["headers"] = headers
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("/api/v1/oauth2/access_token", base_url), 
            method="POST", 
            params=payload, 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def login_oauth_verify(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def login_oauth_verify(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def login_oauth_verify(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """检查 ``appId`` 对应的 ``redirectUri`` 是否可用

        POST https://open-api.123pan.com/api/v1/oauth2/app/verify

        .. admonition:: Reference

            /接入指南/第三方挂载应用接入/授权地址

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/gr7ggimkcysm18ap

        :payload:
            - appId: str 💡 应用标识，创建应用时分配的 appId
            - redirectUri: str 💡 回调链接
            - scope: str = "user:base,file:all:read,file:all:write" 💡 权限
        """
        request_kwargs.setdefault("parse", default_parse)
        payload = dict_key_to_lower_merge(payload, scope="user:base,file:all:read,file:all:write")
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("/api/v1/oauth2/app/verify", base_url), 
            method="POST", 
            json=payload, 
            **request_kwargs, 
        )

    ########## Offline Download API ##########

    @overload
    def offline_download(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def offline_download(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def offline_download(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建离线下载任务

        POST https://open-api.123pan.com/api/v1/offline/download

        .. admonition:: Reference

            /API列表/离线下载/创建离线下载任务

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/he47hsq2o1xvgado

        :payload:
            - callBackUrl: str = <default> 💡 回调地址，任务结束时调用以推送通知，需要支持 POST 并接受 JSON 数据，格式为

                .. code:: js

                    {
                        url: string,     // 下载资源地址
                        status: 0 | 1,   // 是否失败
                        fileReason: str, // 失败原因
                        fileID: int,     // 成功后，该文件在云盘上的 id
                    }

            - dirID: int = <default> 💡 指定下载到的目录的 id。默认会下载到 "/来自:离线下载" 目录中
            - fileName: str = ""     💡 自定义文件名称
            - url: str               💡 下载链接，支持 http/https
        """
        api = complete_url("/api/v1/offline/download", base_url)
        if not isinstance(payload, dict):
            payload = {"url": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def offline_process(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def offline_process(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def offline_process(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取离线下载进度

        GET https://open-api.123pan.com/api/v1/offline/download/process

        .. admonition:: Reference

            /API列表/离线下载/获取离线下载进度

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/sclficr3t655pii5

        :payload:
            - taskID: int 💡 离线下载任务 id
        """
        api = complete_url("/api/v1/offline/download/process", base_url)
        if not isinstance(payload, dict):
            payload = {"taskID": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    ########## Oss API ##########

    @overload
    def oss_copy(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_copy(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_copy(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建复制任务

        POST https://open-api.123pan.com/api/v1/oss/source/copy

        .. note::
            图床复制任务创建（可创建的任务数：3，fileIDs 长度限制：100，当前一个任务处理完后将会继续处理下个任务）。

            该接口将会复制云盘里的文件或目录对应的图片到对应图床目录，每次任务包含的图片总数限制 1000 张，图片格式：png, gif, jpeg, tiff, webp,jpg,tif,svg,bmp，图片大小限制：100M，文件夹层级限制：15层。

            如果图床目录下存在相同 etag、size 的图片将会视为同一张图片，将覆盖原图片

        .. admonition:: Reference

            /API列表/图床/复制云盘图片/创建复制任务

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/trahy3lmds4o0i3r

        :payload:
            - fileIDs: list[int]      💡 文件 id 列表
            - toParentFileID: int = 0 💡 要移动到的目标目录 id，默认为根目录
            - sourceType: int = 1     💡 复制来源：1:云盘
            - type: int = 1           💡 业务类型，固定为 1
        """
        api = complete_url("/api/v1/oss/source/copy", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIDs": payload}
        payload = dict_key_to_lower_merge(payload, {
            "toParentFileID": parent_id, 
            "sourceType": 1, 
            "type": 1, 
        })
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def oss_copy_process(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_copy_process(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_copy_process(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取复制任务详情

        GET https://open-api.123pan.com/api/v1/oss/source/copy/process

        .. admonition:: Reference

            /API列表/图床/复制云盘图片/获取复制任务详情

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/rissl4ewklaui4th

        :payload:
            - taskID: str 💡 复制任务 id
        """
        api = complete_url("/api/v1/oss/source/copy/process", base_url)
        if not isinstance(payload, dict):
            payload = {"taskID": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def oss_copy_fail(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_copy_fail(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_copy_fail(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取复制失败文件列表

        GET https://open-api.123pan.com/api/v1/oss/source/copy/fail

        .. admonition:: Reference

            /API列表/图床/复制云盘图片/获取复制失败文件列表

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/tlug9od3xlw2w23v

        :payload:
            - taskID: str      💡 复制任务 id
            - limit: int = 100 💡 每页条数，最多 100 个
            - page: int = 1    💡 第几页
        """
        api = complete_url("/upload/v1/oss/file/mkdir", base_url)
        if not isinstance(payload, dict):
            payload = {"taskID": payload}
        payload = dict_key_to_lower_merge(payload, limit=100, page=1)
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def oss_delete(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_delete(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_delete(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """删除图片

        POST https://open-api.123pan.com/api/v1/oss/file/delete

        .. attention::
            彻底删除文件前，文件必须要在回收站中，否则无法删除        

        .. admonition:: Reference

            /API列表/图床/删除图片

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/ef8yluqdzm2yttdn

        :payload:
            - fileIDs: list[int] 💡 文件 id 列表，最多 100 个
        """
        api = complete_url("/api/v1/oss/file/delete", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIDs": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def oss_detail(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_detail(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_detail(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取图片详情

        GET https://open-api.123pan.com/api/v1/oss/file/detail

        .. admonition:: Reference

            /API列表/图床/获取图片信息/获取图片详情

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/rgf2ndfaxc2gugp8

        :payload:
            - fileID: int 💡 文件 id
        """
        api = complete_url("/api/v1/oss/file/detail", base_url)
        if not isinstance(payload, dict):
            payload = {"fileID": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def oss_list(
        self, 
        payload: dict | int | str = "", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_list(
        self, 
        payload: dict | int | str = "", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_list(
        self, 
        payload: dict | int | str = "", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取图片列表

        POST https://open-api.123pan.com/api/v1/oss/file/list

        .. note::
            如果返回信息中，"lastFileId" 字段的值为 "-1"，代表最后一页（无需再翻页查询）。
            其它则代表下一页开始的文件 id，携带到请求参数中，可查询下一页

        .. admonition:: Reference

            /API列表/图床/获取图片信息/获取图片列表

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/zayr72q8xd7gg4f8

        :payload:
            - endTime: int = <default>    💡 筛选结束时间，时间戳格式，单位：秒
            - lastFileId: int = <default> 💡 上一页的最后一条记录的 FileID，翻页查询时需要填写
            - limit: int = 100            💡 分页大小，最多 100
            - parentFileId: int | str = 0 💡 父目录 id，默认为根目录
            - startTime: int = <default>  💡 筛选开始时间，时间戳格式，单位：秒
            - type: int = 1               💡 业务类型，固定为 1
        """
        api = complete_url("/api/v1/oss/file/list", base_url)
        if isinstance(payload, (int, str)):
            payload = {"parentFileId": payload}
        payload = dict_key_to_lower_merge(payload, limit=100, type=1)
        return self.request(api, "POST", data=payload, async_=async_, **request_kwargs)

    @overload
    def oss_mkdir(
        self, 
        payload: dict | str, 
        /, 
        parent_id: int | str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_mkdir(
        self, 
        payload: dict | str, 
        /, 
        parent_id: int | str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_mkdir(
        self, 
        payload: dict | str, 
        /, 
        parent_id: int | str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建目录

        POST https://open-api.123pan.com/upload/v1/oss/file/mkdir

        .. admonition:: Reference

            /API列表/图床/上传图片/创建目录

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/tpqqm04ocqwvonrk

        :payload:
            - name: str 💡 文件名，不能重名
            - parentID: int = 0 💡 父目录 id，默认为根目录
            - type: int = 1 💡 业务类型，固定为 1
        """
        api = complete_url("/upload/v1/oss/file/mkdir", base_url)
        if not isinstance(payload, dict):
            payload = {"name": payload}
        payload = dict_key_to_lower_merge(payload, parentID=parent_id, type=1)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def oss_move(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_move(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_move(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = "", 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """移动图片

        POST https://open-api.123pan.com/api/v1/oss/file/move

        .. admonition:: Reference

            /API列表/图床/移动图片

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/eqeargimuvycddna

        :payload:
            - fileIDs: list[int] 💡 文件 id 列表，最多 100 个
            - toParentFileID: int = 0 💡 要移动到的目标目录 id，默认是根目录
        """
        api = complete_url("/api/v1/oss/file/move", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIDs": payload}
        payload = dict_key_to_lower_merge(payload, toParentFileID=parent_id)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def oss_offline_download(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_offline_download(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_offline_download(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建离线迁移任务

        POST https://open-api.123pan.com/api/v1/oss/offline/download

        .. admonition:: Reference

            /API列表/图床/图床离线迁移/创建离线迁移任务

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/ctigc3a08lqzsfnq

        :payload:
            - businessDirID: int = <default> 💡 指定下载到的目录的 id。默认会下载到 "/来自:离线下载" 目录中
            - callBackUrl: str = <default> 💡 回调地址，任务结束时调用以推送通知，需要支持 POST 并接受 JSON 数据，格式为

                .. code:: js

                    {
                        url: string,     // 下载资源地址
                        status: 0 | 1,   // 是否失败
                        fileReason: str, // 失败原因
                        fileID: int,     // 成功后，该文件在云盘上的 id
                    }

            - fileName: str = "" 💡 自定义文件名称
            - type: int = 1 💡 业务类型，固定为 1
            - url: str 💡 下载链接，支持 http/https
        """
        api = complete_url("/api/v1/oss/offline/download", base_url)
        if not isinstance(payload, dict):
            payload = {"url": payload}
        payload = dict_key_to_lower_merge(payload, type=1)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def oss_offline_process(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_offline_process(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_offline_process(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取离线迁移任务

        GET https://open-api.123pan.com/api/v1/oss/offline/download/process

        .. admonition:: Reference

            /API列表/图床/图床离线迁移/获取离线迁移任务

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/svo92desugbyhrgq

        :payload:
            - taskID: int 💡 离线下载任务 id
        """
        api = complete_url("/api/v1/oss/offline/download/process", base_url)
        if not isinstance(payload, dict):
            payload = {"taskID": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def oss_upload_create(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_upload_create(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_upload_create(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建文件

        POST https://open-api.123pan.com/upload/v1/oss/file/create

        .. note::
            - 文件名要小于 256 个字符且不能包含以下字符：``"\\/:*?|><``
            - 文件名不能全部是空格
            - 不会重名

        .. admonition:: Reference

            /API列表/图床/上传图片/创建文件

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/xwfka5kt6vtmgs8r

        :payload:
            - filename: str 💡 文件名
            - duplicate: 0 | 1 | 2 = 0 💡 处理同名：0: 跳过/报错 1: 保留/后缀编号 2: 替换/覆盖
            - etag: str 💡 文件 md5
            - parentFileID: int = 0 💡 父目录 id，默认为根目录
            - size: int 💡 文件大小，单位：字节
            - type: int = 1 💡 业务类型，固定为 1

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "fileID": str, # 上传后的文件 id。当已有相同 ``size`` 和 ``etag`` 的文件时，会发生秒传
                    "preuploadID": str, # 预上传 id。当 ``reuse`` 为 "true" 时，该字段不存在
                    "reuse": bool, # 是否秒传，返回 "true" 时表示文件已上传成功
                    "sliceSize": int, # 分片大小，必须按此大小生成文件分片再上传。当 ``reuse`` 为 "true" 时，该字段不存在
                }
        """
        api = complete_url("/upload/v1/oss/file/create", base_url)
        payload = dict_key_to_lower_merge(payload, type=1)
        if "duplicate" in payload and not payload["duplicate"]:
            del payload["duplicate"]
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def oss_upload_url(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_upload_url(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_upload_url(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取上传地址&上传分片

        POST https://open-api.123pan.com/upload/v1/oss/file/get_upload_url

        .. note::
            有多个分片时，轮流分别根据序号获取下载链接，然后 PUT 方法上传分片。由于上传链接会过期，所以没必要提前获取一大批

        .. admonition:: Reference

            /API列表/图床/上传图片/获取上传地址&上传分片

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/pyfo3a39q6ac0ocd

        :payload:
            - preuploadID: str 💡 预上传 id
            - sliceNo: int     💡 分片序号，从 1 开始自增
        """
        api = complete_url("/upload/v1/oss/file/get_upload_url", base_url)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def oss_upload_list(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_upload_list(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_upload_list(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """列举已上传分片

        POST https://open-api.123pan.com/upload/v1/oss/file/list_upload_parts

        .. note::
            此接口用于罗列已经上传的分片信息，以供比对

        :payload:
            - preuploadID: str 💡 预上传 id
        """
        api = complete_url("/upload/v1/oss/file/list_upload_parts", base_url)
        if not isinstance(payload, dict):
            payload = {"preuploadID": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def oss_upload_complete(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_upload_complete(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_upload_complete(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """上传完毕

        POST https://open-api.123pan.com/upload/v1/oss/file/upload_complete

        .. admonition:: Reference

            /API列表/图床/上传图片/上传完毕

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/yhgo0kt3nkngi8r2

        :payload:
            - preuploadID: str 💡 预上传 id

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "async": bool, # 是否需要异步查询上传结果
                    "completed": bool, # 上传是否完成
                    "fileID": int, # 上传的文件 id
                }
        """
        api = complete_url("/upload/v1/oss/file/upload_complete", base_url)
        if not isinstance(payload, dict):
            payload = {"preuploadID": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def oss_upload_result(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_upload_result(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_upload_result(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """异步轮询获取上传结果

        POST https://open-api.123pan.com/upload/v1/oss/file/upload_async_result

        .. admonition:: Reference

            /API列表/图床/上传图片/异步轮询获取上传结果

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/lbdq2cbyzfzayipu

        :payload:
            - preuploadID: str 💡 预上传 id

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "completed": bool, # 上传合并是否完成，如果为 False，请至少 1 秒后再发起轮询
                    "fileID": int, # 上传的文件 id
                }
        """
        api = complete_url("/upload/v1/oss/file/upload_async_result", base_url)
        if not isinstance(payload, dict):
            payload = {"preuploadID": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def oss_upload_file(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] ), 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = "", 
        duplicate: Literal[0, 1, 2] = 0, 
        preupload_id: None | str = None, 
        slice_size: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def oss_upload_file(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer] ), 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = "", 
        duplicate: Literal[0, 1, 2] = 0, 
        preupload_id: None | str = None, 
        slice_size: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def oss_upload_file(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer] ), 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = "", 
        duplicate: Literal[0, 1, 2] = 0, 
        preupload_id: None | str = None, 
        slice_size: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """上传文件

        .. note::
            如果文件名中包含字符 ``"\\/:*?|><``，则转换为对应的全角字符

        .. admonition:: Reference

            /API列表/图床/上传图片/💡上传流程说明

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/di0url3qn13tk28t

        :param file: 待上传的文件

            - 如果为 ``collections.abc.Buffer``，则作为二进制数据上传
            - 如果为 ``filewrap.SupportsRead``，则作为可读的二进制文件上传
            - 如果为 ``str`` 或 ``os.PathLike``，则视为路径，打开后作为文件上传
            - 如果为 ``yarl.URL`` 或 ``http_request.SupportsGeturl`` (``pip install python-http_request``)，则视为超链接，打开后作为文件上传
            - 如果为 ``collections.abc.Iterable[collections.abc.Buffer]`` 或 ``collections.abc.AsyncIterable[collections.abc.Buffer]``，则迭代以获取二进制数据，逐步上传

        :param file_md5: 文件的 MD5 散列值
        :param file_name: 文件名
        :param file_size: 文件大小
        :param parent_id: 要上传的目标目录，默认为根目录
        :param duplicate: 处理同名：0: 提示/忽略 1: 保留两者 2: 替换
        :param preupload_id: 预上传 id，用于断点续传，提供此参数，则会忽略 ``file_md5``、``file_name``、``file_size``、``parent_id`` 和 ``duplicate``
        :param slice_size: 分块大小，断点续传时，如果只上传过少于 2 个分块时，会被使用
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应
        """
        def gen_step():
            nonlocal file, file_md5, file_name, file_size, preupload_id, slice_size
            def do_upload(file):
                return self.oss_upload_file_open(
                    file=file, 
                    file_md5=file_md5, 
                    file_name=file_name, 
                    file_size=file_size, 
                    parent_id=parent_id, 
                    duplicate=duplicate, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
            try:
                file = getattr(file, "getbuffer")()
            except (AttributeError, TypeError):
                pass
            if isinstance(file, Buffer):
                file_size = buffer_length(file)
                if not file_md5:
                    file_md5 = md5(file).hexdigest()
            elif isinstance(file, (str, PathLike)):
                path = fsdecode(file)
                if not file_name:
                    file_name = basename(path)
                return do_upload(open(path, "rb"))
            elif isinstance(file, SupportsRead):
                seek = getattr(file, "seek", None)
                seekable = False
                curpos = 0
                if callable(seek):
                    if async_:
                        seek = ensure_async(seek, threaded=True)
                    try:
                        seekable = getattr(file, "seekable")()
                    except (AttributeError, TypeError):
                        try:
                            curpos = yield seek(0, 1)
                            seekable = True
                        except Exception:
                            seekable = False
                if not file_md5:
                    if not seekable:
                        fsrc = file
                        file = TemporaryFile()
                        if async_:
                            yield copyfileobj_async(fsrc, file)
                        else:
                            copyfileobj(fsrc, file)
                        file.seek(0)
                        return do_upload(file)
                    try:
                        if async_:
                            file_size, hashobj = yield file_digest_async(file)
                        else:
                            file_size, hashobj = file_digest(file)
                    finally:
                        yield cast(Callable, seek)(curpos)
                    file_md5 = hashobj.hexdigest()
                if file_size < 0:
                    try:
                        fileno = getattr(file, "fileno")()
                        file_size = fstat(fileno).st_size - curpos
                    except (AttributeError, TypeError, OSError):
                        try:
                            file_size = len(file) - curpos # type: ignore
                        except TypeError:
                            if seekable:
                                try:
                                    file_size = (yield cast(Callable, seek)(0, 2)) - curpos
                                finally:
                                    yield cast(Callable, seek)(curpos)
                            else:
                                raise ValueError("unable to get `file_size`")
            elif isinstance(file, (URL, SupportsGeturl)):
                if isinstance(file, URL):
                    url = str(file)
                else:
                    url = file.geturl()
                if async_:
                    from httpfile import AsyncHttpxFileReader
                    async def request():
                        file = await AsyncHttpxFileReader.new(url)
                        async with file:
                            return await do_upload(file)
                    return request()
                else:
                    from httpfile import HTTPFileReader
                    with HTTPFileReader(url) as file:
                        return do_upload(file)
            elif not file_md5 or file_size < 0:
                if async_:
                    file = bytes_iter_to_async_reader(file) # type: ignore
                else:
                    file = bytes_iter_to_reader(file) # type: ignore
                return do_upload(file)
            if not file_name:
                file_name = getattr(file, "name", "")
                file_name = basename(file_name)
            if file_name:
                file_name = escape_filename(file_name)
            else:
                file_name = str(uuid4())
            if file_size < 0:
                file_size = getattr(file, "length", 0)
            next_slice_no = 1
            if preupload_id:
                resp = yield self.oss_upload_list_open(
                    preupload_id, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                parts = resp["data"].get("parts")
                if not parts:
                    if not slice_size:
                        preupload_id = None
                elif len(parts) == 1:
                    if slice_size:
                        next_slice_no = slice_size == parts[0]["size"]
                    else:
                        warn("only one block was uploaded before, but it's not sure if it's complete", parts)
                        slice_size = parts[0]["size"]
                        next_slice_no = 2
                else:
                    slice_size = parts[0]["size"]
                    next_slice_no = len(parts) + (slice_size == parts[-1]["size"])
            if next_slice_no > 1:
                file_seek = getattr(file, "seek", None)
                if not callable(file_seek):
                    raise AttributeError(f"resume upload on an unseekable stream {file}")
                if async_:
                    file_seek = ensure_async(file_seek, threaded=True)
                yield file_seek(slice_size * (next_slice_no - 1))
            if not preupload_id:
                resp = yield self.oss_upload_create_open(
                    {
                        "etag": file_md5, 
                        "filename": file_name, 
                        "size": file_size, 
                        "parentFileID": parent_id, 
                        "duplicate": duplicate, 
                        "containDir": file_name.startswith("/"), 
                    }, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                upload_data = resp["data"]
                if upload_data["reuse"]:
                    return resp
                preupload_id = upload_data["preuploadID"]
                slice_size = int(upload_data["sliceSize"])
            upload_request_kwargs = {
                **request_kwargs, 
                "method": "PUT", 
                "headers": {"authorization": ""}, 
                "parse": ..., 
            }
            try:
                if async_:
                    async def request():
                        chunks = bio_chunk_async_iter(file, chunksize=slice_size) # type: ignore
                        slice_no = next_slice_no
                        async for chunk in chunks:
                            resp = await self.oss_upload_url_open(
                                {"preuploadID": preupload_id, "sliceNo": slice_no}, 
                                base_url=base_url, 
                                async_=True, 
                                **request_kwargs, 
                            )
                            check_response(resp)
                            upload_url = resp["data"]["presignedURL"]
                            await self.request(
                                upload_url, 
                                data=chunk, 
                                async_=True, 
                                **upload_request_kwargs, 
                            )
                            slice_no += 1
                    yield request()
                else:
                    chunks = bio_chunk_iter(file, chunksize=slice_size) # type: ignore
                    for slice_no, chunk in enumerate(chunks, next_slice_no):
                        resp = self.oss_upload_url_open(
                            {"preuploadID": preupload_id, "sliceNo": slice_no}, 
                            base_url=base_url, 
                            **request_kwargs, 
                        )
                        check_response(resp)
                        upload_url = resp["data"]["presignedURL"]
                        self.request(upload_url, data=chunk, **upload_request_kwargs)
                return (yield self.oss_upload_complete_open(
                    preupload_id, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                ))
            except BaseException as e:
                raise P123BrokenUpload({
                    "preupload_id": preupload_id, 
                    "file_md5": file_md5, 
                    "file_name": file_name, 
                    "file_size": file_size, 
                    "parent_id": parent_id, 
                    "duplicate": duplicate, 
                    "slice_size": slice_size, 
                }) from e
        return run_gen_step(gen_step, async_)

    ########## Share API ##########

    @overload
    def share_create(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_create(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_create(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建分享链接

        POST https://open-api.123pan.com/api/v1/share/create

        .. admonition:: Reference

            /API列表/分享管理/创建分享链接

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/dwd2ss0qnpab5i5s

        :payload:
            - fileIDList: str 💡 分享文件 id 列表，最多 100 个，用逗号,分隔连接
            - shareExpire: 0 | 1 | 7 | 30 = 0 💡 分享链接有效期天数，0 为永久
            - shareName: str 💡 分享链接名称，须小于 35 个字符且不能包含特殊字符 ``"\\/:*?|><``
            - sharePwd: str = "" 💡 提取码（不区分大小写）
            - trafficLimit: int = <default> 💡 免登陆限制流量，单位：字节
            - trafficLimitSwitch: 1 | 2 = <default> 💡 免登录流量限制开关：1:关闭 2:打开
            - trafficSwitch: 1 | 2 | 3 | 4 = <default> 💡 免登录流量包开关

                - 1: 游客免登录提取（关） 超流量用户提取（关）
                - 2: 游客免登录提取（开） 超流量用户提取（关）
                - 3: 游客免登录提取（关） 超流量用户提取（开）
                - 4: 游客免登录提取（开） 超流量用户提取（开）
        """
        api = complete_url("/api/v1/share/create", base_url)
        payload = dict_key_to_lower_merge(payload, {"shareExpire": 0, "sharePwd": ""})
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def share_create_payment(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_create_payment(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_create_payment(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建付费分享链接

        POST https://open-api.123pan.com/api/v1/share/content-payment/create

        .. admonition:: Reference

            /API列表/分享管理/创建付费分享链接

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/qz30c5k2npe8l98r

        :payload:
            - fileIDList: str        💡 分享文件 id 列表，最多 100 个，用逗号,分隔连接
            - shareName: str         💡 分享链接名称，须小于 35 个字符且不能包含特殊字符 ``"\\/:*?|><``
            - isReward: 0 | 1 = 0    💡 是否开启打赏
            - payAmount: int = 1     💡 金额，从 1 到 99，单位：元
            - resourceDesc: str = "" 💡 资源描述
            - trafficLimit: int = <default> 💡 免登陆限制流量，单位：字节
            - trafficLimitSwitch: 1 | 2 = <default> 💡 免登录流量限制开关：1:关闭 2:打开
            - trafficSwitch: 1 | 2 | 3 | 4 = <default> 💡 免登录流量包开关

                - 1: 游客免登录提取（关） 超流量用户提取（关）
                - 2: 游客免登录提取（开） 超流量用户提取（关）
                - 3: 游客免登录提取（关） 超流量用户提取（开）
                - 4: 游客免登录提取（开） 超流量用户提取（开）
        """
        api = complete_url("/api/v1/share/content-payment/create", base_url)
        payload = dict_key_to_lower_merge(payload, {"payAmount": 1, "isReward": 0, "resourceDesc": ""})
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def share_edit(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_edit(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_edit(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """修改分享链接

        PUT https://open-api.123pan.com/api/v1/share/list/info

        .. admonition:: Reference

            /API列表/分享管理/修改分享链接

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/ga6hhca1u8v9yqx0

        :payload:
            - shareIdList: list[int] 💡 分享链接 id 列表，最多 100 个
            - trafficLimit: int = <default> 💡 免登陆限制流量，单位：字节
            - trafficLimitSwitch: 1 | 2 = <default> 💡 免登录流量限制开关：1:关闭 2:打开
            - trafficSwitch: 1 | 2 | 3 | 4 = <default> 💡 免登录流量包开关

                - 1: 游客免登录提取（关） 超流量用户提取（关）
                - 2: 游客免登录提取（开） 超流量用户提取（关）
                - 3: 游客免登录提取（关） 超流量用户提取（开）
                - 4: 游客免登录提取（开） 超流量用户提取（开）
        """
        api = complete_url("/api/v1/share/list/info", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"shareIdList": payload}
        return self.request(api, "PUT", json=payload, async_=async_, **request_kwargs)

    @overload
    def share_edit_payment(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_edit_payment(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_edit_payment(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """修改付费分享链接

        PUT https://open-api.123pan.com/api/v1/share/list/payment/info

        .. admonition:: Reference

            /API列表/分享管理/修改付费分享链接

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/euz8kc7fcyye496g

        :payload:
            - shareIdList: list[int] 💡 分享链接 id 列表，最多 100 个
            - trafficLimit: int = <default> 💡 免登陆限制流量，单位：字节
            - trafficLimitSwitch: 1 | 2 = <default> 💡 免登录流量限制开关：1:关闭 2:打开
            - trafficSwitch: 1 | 2 | 3 | 4 = <default> 💡 免登录流量包开关

                - 1: 游客免登录提取（关） 超流量用户提取（关）
                - 2: 游客免登录提取（开） 超流量用户提取（关）
                - 3: 游客免登录提取（关） 超流量用户提取（开）
                - 4: 游客免登录提取（开） 超流量用户提取（开）
        """
        api = complete_url("/api/v1/share/list/payment/info", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"shareIdList": payload}
        return self.request(api, "PUT", json=payload, async_=async_, **request_kwargs)

    @overload
    def share_list(
        self, 
        payload: dict | int = 100, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_list(
        self, 
        payload: dict | int = 100, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_list(
        self, 
        payload: dict | int = 100, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取分享链接列表

        GET https://open-api.123pan.com/api/v1/share/list

        .. admonition:: Reference

            /API列表/分享管理/获取分享链接列表

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/ixg0arldi61fe7av

        :payload:
            - limit: int = 100     💡 每页文件数量，最多 100 个
            - lastShareId: int = 0 💡 从此分享 id 之后开始，默认为 0，即从头开始
        """
        api = complete_url("/api/v1/share/list", base_url)
        if not isinstance(payload, int):
            payload = {"limit": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def share_list_payment(
        self, 
        payload: dict | int = 100, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_list_payment(
        self, 
        payload: dict | int = 100, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_list_payment(
        self, 
        payload: dict | int = 100, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取付费分享链接列表

        GET https://open-api.123pan.com/api/v1/share/payment/list

        .. admonition:: Reference

            /API列表/分享管理/获取付费分享链接列表

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/mxc7eq2x3la72mwg

        :payload:
            - limit: int = 100     💡 每页文件数量，最多 100 个
            - lastShareId: int = 0 💡 从此分享 id 之后开始，默认为 0，即从头开始
        """
        api = complete_url("/api/v1/share/payment/list", base_url)
        if not isinstance(payload, int):
            payload = {"limit": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    ########## Transcode API ##########

    @overload
    def transcode_delete(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_delete(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_delete(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """删除转码视频

        POST https://open-api.123pan.com/api/v1/transcode/delete

        .. admonition:: Reference

            /API列表/视频转码/删除视频/删除转码视频

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/tg2xgotkgmgpulrp

        :payload:
            - fileId: int           💡 文件 id
            - businessType: int = 2 💡 业务类型：2:转码空间
            - trashed: int = 2      💡 删除范围：1:删除原文件 2:删除原文件+转码后的文件
        """
        api = complete_url("/api/v1/transcode/delete", base_url)
        if not isinstance(payload, dict):
            payload = {"fileId": payload}
        payload = dict_key_to_lower_merge(payload, businessType=2, trashed=2)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def transcode_download(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_download(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_download(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """原文件下载

        POST https://open-api.123pan.com/api/v1/transcode/file/download

        .. admonition:: Reference

            /API列表/视频转码/视频文件下载/原文件下载

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/mlltlx57sty6g9gf

        :payload:
            - fileId: int 💡 文件 id
        """
        api = complete_url("/api/v1/transcode/file/download", base_url)
        if not isinstance(payload, dict):
            payload = {"fileId": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def transcode_download_all(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_download_all(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_download_all(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """某个视频全部转码文件下载

        POST https://open-api.123pan.com/api/v1/transcode/file/download/all

        .. attention::
            该接口需要轮询去查询结果，建议 10s 一次

        .. admonition:: Reference

            /API列表/视频转码/视频文件下载/某个视频全部转码文件下载

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/yb7hrb0x2gym7xic

        :payload:
            - fileId: int 💡 文件 id
            - zipName: str = f"转码{file_id}.zip" 💡 下载 zip 文件的名字
        """
        api = complete_url("/api/v1/transcode/file/download/all", base_url)
        if not isinstance(payload, dict):
            payload = {"fileId": payload}
        payload = dict_key_to_lower_merge(payload, zipName=f"转码{payload.get('fileid', '')}.zip")
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def transcode_m3u8_ts_download(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_m3u8_ts_download(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_m3u8_ts_download(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """单个转码文件下载（m3u8或ts）

        POST https://open-api.123pan.com/api/v1/transcode/m3u8_ts/download

        .. admonition:: Reference

            /API列表/视频转码/视频文件下载/单个转码文件下载（m3u8或ts）

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/yf97p60yyzb8mzbr

        :payload:
            - fileId: int     💡 文件 id
            - resolution: str 💡 分辨率
            - type: int       💡 文件类型：1:m3u8 2:ts
            - tsName: str     💡 下载 ts 文件时必须要指定名称，请参考查询某个视频的转码结果
        """
        api = complete_url("/api/v1/transcode/m3u8_ts/download", base_url)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def transcode_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取转码空间文件夹信息

        POST https://open-api.123pan.com/api/v1/transcode/folder/info

        .. admonition:: Reference

            /API列表/视频转码/获取视频信息/获取转码空间文件夹信息

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/kaalgke88r9y7nlt
        """
        api = complete_url("/api/v1/transcode/folder/info", base_url)
        return self.request(api, "POST", async_=async_, **request_kwargs)

    @overload
    def transcode_list(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_list(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_list(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """视频转码列表（三方挂载应用授权使用）

        GET https://open-api.123pan.com/api/v1/video/transcode/list

        .. attention::
            此接口仅限授权 ``access_token`` 调用

        .. admonition:: Reference

            /API列表/视频转码/获取视频信息/视频转码列表（三方挂载应用授权使用）

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/tgg6g84gdrmyess5

        :payload:
            - fileId: int 💡 文件 id
        """
        api = complete_url("/api/v1/video/transcode/list", base_url)
        if not isinstance(payload, dict):
            payload = {"fileId": payload}
        return self.request(api, params=payload, async_=async_, **request_kwargs)

    @overload
    def transcode_record(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_record(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_record(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """查询某个视频的转码记录

        POST https://open-api.123pan.com/api/v1/transcode/video/record

        .. admonition:: Reference

            /API列表/视频转码/查询转码信息/查询某个视频的转码记录

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/ost1m82sa9chh0mc

        :payload:
            - fileId: int 💡 文件 id
        """
        api = complete_url("/api/v1/transcode/video/record", base_url)
        if not isinstance(payload, dict):
            payload = {"fileId": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def transcode_resolutions(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_resolutions(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_resolutions(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取视频文件可转码的分辨率

        .. attention::
            该接口需要轮询去查询结果，建议 10s 一次

        POST https://open-api.123pan.com/api/v1/transcode/video/resolutions

        .. admonition:: Reference

            /API列表/视频转码/获取视频信息/获取视频文件可转码的分辨率

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/apzlsgyoggmqwl36

        :payload:
            - fileId: int 💡 文件 id
        """
        api = complete_url("/api/v1/transcode/video/resolutions", base_url)
        if not isinstance(payload, dict):
            payload = {"fileId": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def transcode_result(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_result(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_result(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """查询某个视频的转码结果

        POST https://open-api.123pan.com/api/v1/transcode/video/result

        .. admonition:: Reference

            /API列表/视频转码/查询转码信息/查询某个视频的转码结果

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/iucbqgge0dgfc8sv

        :payload:
            - fileId: int 💡 文件 id
        """
        api = complete_url("/api/v1/transcode/video/result", base_url)
        if not isinstance(payload, dict):
            payload = {"fileId": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def transcode_upload(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_upload(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_upload(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """从云盘空间上传

        POST https://open-api.123pan.com/api/v1/transcode/upload/from_cloud_disk

        .. admonition:: Reference

            /API列表/视频转码/上传视频/云盘上传/从云盘空间上传

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/tqy2xatoo4qmdbz7

        :payload:
            - fileId: list[FileID] 💡 云盘空间文件 id，最多 100 个

                .. code:: python

                    FileID = {
                        "fileId": int # 文件 id
                    }
        """
        api = complete_url("/api/v1/transcode/upload/from_cloud_disk", base_url)
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                fids = [{"fileId": payload}]
            else:
                fids = [{"fileId": fid} for fid in payload]
            payload = {"fileId": fids}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def transcode_video(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def transcode_video(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def transcode_video(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """视频转码操作

        POST https://open-api.123pan.com/api/v1/transcode/video

        .. admonition:: Reference

            /API列表/视频转码/视频转码/视频转码操作

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/xy42nv2x8wav9n5l

        :payload:
            - fileId: int      💡 文件 id
            - codecName: str   💡 编码方式
            - videoTime: int   💡 视频时长，单位：秒
            - resolutions: str 💡 要转码的分辨率（例如 1080P，P大写），多个用逗号,分隔连接，如："2160P,1080P,720P"
        """
        api = complete_url("/api/v1/transcode/video", base_url)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    ########## Upload API ##########

    @overload
    def upload_complete(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_complete(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_complete(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """上传完毕

        POST https://open-api.123pan.com/upload/v1/file/upload_complete

        .. admonition:: Reference

            /API列表/文件管理/上传/V1（旧）/上传完毕

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/hkdmcmvg437rfu6x

        :payload:
            - preuploadID: str 💡 预上传 id

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "async": bool, # 是否需要异步查询上传结果
                    "completed": bool, # 上传是否完成
                    "fileID": int, # 上传的文件 id
                }
        """
        api = complete_url("/upload/v1/file/upload_complete", base_url)
        if not isinstance(payload, dict):
            payload = {"preuploadID": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def upload_complete_v2(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_complete_v2(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_complete_v2(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """上传完毕

        POST https://open-api.123pan.com/upload/v2/file/upload_complete

        .. admonition:: Reference

            /API列表/文件管理/上传/V2（推荐）/上传完毕

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/fzzc5o8gok517720

        :payload:
            - preuploadID: str 💡 预上传 id

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "completed": bool, # 上传是否完成
                    "fileID": int,     # 上传的文件 id
                }
        """
        api = complete_url("/upload/v2/file/upload_complete", base_url)
        if not isinstance(payload, dict):
            payload = {"preuploadID": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def upload_create(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_create(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_create(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建文件

        POST https://open-api.123pan.com/upload/v1/file/create

        .. note::
            - 文件名要小于 256 个字符且不能包含以下字符：``"\\/:*?|><``
            - 文件名不能全部是空格
            - 开发者上传单文件大小限制 10 GB
            - 不会重名

        .. note::
            /API列表/文件管理/上传/V1（旧）/💡上传流程说明

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/il16qi0opiel4889

            1. 请求创建文件接口，接口返回的 "reuse" 为 "true" 时，表示秒传成功，上传结束。
            2. 非秒传情况将会返回预上传ID ``preuploadID`` 与分片大小 ``sliceSize``，请将文件根据分片大小切分。            

        .. admonition:: Reference

            /API列表/文件管理/上传/V1（旧）/创建文件

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/lrfuu3qe7q1ul8ig

        :payload:
            - containDir: bool  = False 💡 上传文件是否包含路径
            - filename: str 💡 文件名，但 ``containDir`` 为 "true" 时，视为路径
            - duplicate: 0 | 1 | 2 = 0 💡 处理同名：0: 跳过/报错 1: 保留/后缀编号 2: 替换/覆盖
            - etag: str 💡 文件 md5
            - parentFileID: int = 0 💡 父目录 id，根目录是 0
            - size: int 💡 文件大小，单位：字节

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "fileID": str, # 上传后的文件 id。当已有相同 ``size`` 和 ``etag`` 的文件时，会发生秒传
                    "preuploadID": str, # 预上传 id。当 ``reuse`` 为 "true" 时，该字段不存在
                    "reuse": bool, # 是否秒传，返回 "true" 时表示文件已上传成功
                    "sliceSize": int, # 分片大小，必须按此大小生成文件分片再上传。当 ``reuse`` 为 "true" 时，该字段不存在
                }
        """
        api = complete_url("/upload/v1/file/create", base_url)
        payload = dict_key_to_lower_merge(payload, {
            "parentFileId": 0, 
            "containDir": False, 
        })
        if "duplicate" in payload and not payload["duplicate"]:
            del payload["duplicate"]
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def upload_create_v2(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_create_v2(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_create_v2(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建文件

        POST https://open-api.123pan.com/upload/v2/file/create

        .. note::
            - 文件名要小于 256 个字符且不能包含以下字符：``"\\/:*?|><``
            - 文件名不能全部是空格
            - 开发者上传单文件大小限制 10 GB
            - 不会重名

        .. note::
            /API列表/文件管理/上传/V2（推荐）/💡上传流程说明

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/xogi45g7okqk7svr#uqhyW

            1. 调用创建文件接口，接口返回的 "reuse" 为 "true" 时，表示秒传成功，上传结束。
            2. 非秒传情况将会返回预上传ID ``preuploadID`` 与分片大小 ``sliceSize``，请将文件根据分片大小切分。
            3. 非秒传情况下返回 "servers" 为后续上传文件的对应域名（重要），多个任选其一。            

        .. admonition:: Reference

            /API列表/文件管理/上传/V2（推荐）/创建文件

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/txow0iqviqsgotfl

        :payload:
            - containDir: bool  = False 💡 上传文件是否包含路径
            - filename: str 💡 文件名，但 ``containDir`` 为 "true" 时，视为路径
            - duplicate: 0 | 1 | 2 = 0 💡 处理同名：0: 跳过/报错 1: 保留/后缀编号 2: 替换/覆盖
            - etag: str 💡 文件 md5
            - parentFileID: int = 0 💡 父目录 id，根目录是 0
            - size: int 💡 文件大小，单位：字节

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "fileID": str, # 上传后的文件 id。当已有相同 ``size`` 和 ``etag`` 的文件时，会发生秒传
                    "preuploadID": str, # 预上传 id。当 ``reuse`` 为 "true" 时，该字段不存在
                    "reuse": bool, # 是否秒传，返回 "true" 时表示文件已上传成功
                    "sliceSize": int, # 分片大小，必须按此大小生成文件分片再上传。当 ``reuse`` 为 "true" 时，该字段不存在
                    "servers": list[str], # 上传地址，多个任选其一
                }
        """
        api = complete_url("/upload/v2/file/create", base_url)
        payload = dict_key_to_lower_merge(payload, {
            "parentFileId": 0, 
            "containDir": False, 
        })
        if "duplicate" in payload and not payload["duplicate"]:
            del payload["duplicate"]
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def upload_domain(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_domain(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_domain(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取上传域名

        GET https://open-api.123pan.com/upload/v2/file/domain

        .. admonition:: Reference

            /API列表/文件管理/上传/V2（推荐）/获取上传域名

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/agn8lolktbqie7p9

        :payload:
            - preuploadID: str 💡 预上传 id
        """
        api = complete_url("/upload/v2/file/domain", base_url)
        return self.request(api, async_=async_, **request_kwargs)

    @overload
    def upload_list(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_list(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_list(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """列举已上传分片

        POST https://open-api.123pan.com/upload/v1/file/list_upload_parts

        .. note::
            此接口用于罗列已经上传的分片信息，以供比对

        .. admonition:: Reference

            /API列表/文件管理/上传/V1（旧）/列举已上传分片（非必需）

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/dd28ws4bfn644cny

        :payload:
            - preuploadID: str 💡 预上传 id
        """
        api = complete_url("/upload/v1/file/list_upload_parts", base_url)
        if not isinstance(payload, dict):
            payload = {"preuploadID": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def upload_result(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_result(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_result(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """异步轮询获取上传结果

        POST https://open-api.123pan.com/upload/v1/file/upload_async_result

        .. admonition:: Reference

            /API列表/文件管理/上传/V1（旧）/异步轮询获取上传结果

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/qgcosr6adkmm51h7

        :payload:
            - preuploadID: str 💡 预上传 id

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "completed": bool, # 上传合并是否完成，如果为 False，请至少 1 秒后再发起轮询
                    "fileID": int, # 上传的文件 id
                }
        """
        api = complete_url("/upload/v1/file/upload_async_result", base_url)
        if not isinstance(payload, dict):
            payload = {"preuploadID": payload}
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    @overload
    def upload_sha1_reuse(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = "https://open-api.123pan.com", 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_sha1_reuse(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = "https://open-api.123pan.com", 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_sha1_reuse(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = "https://open-api.123pan.com", 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """sha1哈希值文件上传

        POST https://open-api.123pan.com/upload/v2/file/sha1_reuse

        .. note::
            - 文件名要小于 256 个字符且不能包含以下任何字符：``"\\/:*?|><``
            - 文件名不能全部是空格

        .. admonition:: Reference

            /API列表/文件管理/上传/sha1哈希值文件上传

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/de0et33ct3uhdfqs

        :payload:
            - sha1: str 💡 文件 sha1
            - size: int 💡 文件大小，单位：字节
            - filename: str 💡 文件名，默认为 f"{sha1}-{size}"
            - parentFileID: int = 0 💡 父目录 id，根目录是 0
            - duplicate: 0 | 1 | 2 = 0 💡 处理同名：0: 跳过/报错 1: 保留/后缀编号 2: 替换/覆盖

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "fileID": int, # 文件 ID。当 123 云盘已有该文件,则会发生秒传。此时会将文件 ID 字段返回。唯一
                    "reuse": bool, # 是否秒传，返回true时表示文件已上传成功
                }
        """
        payload = dict_key_to_lower_merge(payload, {
            "filename": "{sha1}-{size}".format_map(payload), 
            "parentFileId": "0", 
        })
        return self.request(
            "/upload/v2/file/sha1_reuse", 
            "POST", 
            data=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def upload_single(
        self, 
        payload: dict, 
        /, 
        file: Buffer | SupportsRead[Buffer] | Iterable[Buffer], 
        base_url: str | Callable[[], str] = "https://open-api.123pan.com", 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_single(
        self, 
        payload: dict, 
        /, 
        file: Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer], 
        base_url: str | Callable[[], str] = "https://open-api.123pan.com", 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_single(
        self, 
        payload: dict, 
        /, 
        file: Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer], 
        base_url: str | Callable[[], str] = "https://open-api.123pan.com", 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """单步上传

        POST https://open-api.123pan.com/upload/v2/file/single/create

        .. note::
            - 文件名要小于 256 个字符且不能包含以下任何字符：``"\\/:*?|><``
            - 文件名不能全部是空格
            - 请求头包含 ``Content-Type: multipart/form-data``
            - 此接口限制开发者上传单文件大小为 1 GB
            - 上传域名是 ``client.upload_domain_open`` 响应中的域名
            - 此接口用于实现小文件单步上传一次 HTTP 请求交互即可完成上传

        .. admonition:: Reference

            /API列表/文件管理/上传/V2（推荐）/单步上传

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/xhiht1uh3yp92pzc

        :payload:
            - containDir: bool  = False 💡 上传文件是否包含路径
            - filename: str 💡 文件名，但 ``containDir`` 为 "true" 时，视为路径
            - duplicate: 0 | 1 | 2 = 0 💡 处理同名：0: 跳过/报错 1: 保留/后缀编号 2: 替换/覆盖
            - etag: str 💡 文件 md5
            - parentFileID: int = 0 💡 父目录 id，根目录是 0
            - size: int 💡 文件大小，单位：字节
            - file: Any 💡 分片二进制流（请单独传递 ``file`` 参数）

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "completed": bool, # 是否上传完成（如果 "completed" 为 "true" 时，则说明上传完成）
                    "fileID": int, # 文件 ID。当 123 云盘已有该文件,则会发生秒传。此时会将文件 ID 字段返回。唯一
                }
        """
        payload = dict_key_to_lower_merge(payload, {
            "parentFileId": "0", 
            "containDir": False, 
        })
        return self.request(
            "/upload/v2/file/single/create", 
            "POST", 
            data=payload, 
            files={"file": file}, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def upload_slice(
        self, 
        payload: dict, 
        /, 
        slice: Buffer | SupportsRead[Buffer] | Iterable[Buffer], 
        base_url: str | Callable[[], str] = "https://open-api.123pan.com", 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_slice(
        self, 
        payload: dict, 
        /, 
        slice: Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer], 
        base_url: str | Callable[[], str] = "https://open-api.123pan.com", 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_slice(
        self, 
        payload: dict, 
        /, 
        slice: Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer], 
        base_url: str | Callable[[], str] = "https://open-api.123pan.com", 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """上传文件文件

        POST https://open-api.123pan.com/upload/v2/file/slice

        .. note::
            - 上传域名是创建文件接口响应中的 "servers"
            - 请求头包含 ``Content-Type: multipart/form-data``

        .. admonition:: Reference

            /API列表/文件管理/上传/V2（推荐）/上传分片

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/txow0iqviqsgotfl

        :payload:
            - preuploadID: str 💡 预上传ID
            - sliceNo: int     💡 分片序号，从 1 开始自增
            - sliceMD5: str    💡 当前分片 md5
            - slice: Any       💡 分片二进制流（请单独传递 ``slice`` 参数）
        """
        payload["sliceNo"] = str(payload.get("sliceNo", 1))
        return self.request(
            "/upload/v2/file/slice", 
            "POST", 
            data=payload, 
            files={"slice": slice}, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def upload_url(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_url(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_url(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取上传地址&上传分片

        POST https://open-api.123pan.com/upload/v1/file/get_upload_url

        .. note::
            有多个分片时，轮流分别根据序号获取下载链接，然后 PUT 方法上传分片。由于上传链接会过期，所以没必要提前获取一大批

        .. admonition:: Reference

            /API列表/文件管理/上传/V1（旧）/获取上传地址&上传分片

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/sonz9n085gnz0n3m

        :payload:
            - preuploadID: str 💡 预上传 id
            - sliceNo: int     💡 分片序号，从 1 开始自增
        """
        api = complete_url("/upload/v1/file/get_upload_url", base_url)
        return self.request(api, "POST", json=payload, async_=async_, **request_kwargs)

    # TODO: 如果已经有 md5 和 大小，则先尝试直接上传，而不是打开文件，等确定不能妙传，再打开文件
    # TODO: 支持 v2 接口，以及上传单个文件的接口（可以设定一个参数，是否优先用 upload_single，只要文件大小在 1 GB 内）
    @overload
    def upload_file(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] ), 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        preupload_id: None | str = None, 
        slice_size: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_file(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer] ), 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        preupload_id: None | str = None, 
        slice_size: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_file(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer] ), 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        preupload_id: None | str = None, 
        slice_size: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """上传文件

        .. note::
            如果文件名中包含字符 ``"\\/:*?|><``，则转换为对应的全角字符

        .. admonition:: Reference

            /API列表/文件管理/上传/V1（旧）/💡上传流程说明

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/il16qi0opiel4889

            /API列表/视频转码/上传视频/本地上传/上传流程

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/kh4ovskpumzn8r07

        :param file: 待上传的文件

            - 如果为 ``collections.abc.Buffer``，则作为二进制数据上传
            - 如果为 ``filewrap.SupportsRead``，则作为可读的二进制文件上传
            - 如果为 ``str`` 或 ``os.PathLike``，则视为路径，打开后作为文件上传
            - 如果为 ``yarl.URL`` 或 ``http_request.SupportsGeturl`` (``pip install python-http_request``)，则视为超链接，打开后作为文件上传
            - 如果为 ``collections.abc.Iterable[collections.abc.Buffer]`` 或 ``collections.abc.AsyncIterable[collections.abc.Buffer]``，则迭代以获取二进制数据，逐步上传

        :param file_md5: 文件的 MD5 散列值
        :param file_name: 文件名
        :param file_size: 文件大小
        :param parent_id: 要上传的目标目录
        :param duplicate: 处理同名：0: 提示/忽略 1: 保留两者 2: 替换
        :param preupload_id: 预上传 id，用于断点续传，提供此参数，则会忽略 ``file_md5``、``file_name``、``file_size``、``parent_id`` 和 ``duplicate``
        :param slice_size: 分块大小，断点续传时，如果只上传过少于 2 个分块时，会被使用
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应
        """
        def gen_step():
            nonlocal file, file_md5, file_name, file_size, preupload_id, slice_size
            def do_upload(file):
                return self.upload_file_open(
                    file=file, 
                    file_md5=file_md5, 
                    file_name=file_name, 
                    file_size=file_size, 
                    parent_id=parent_id, 
                    duplicate=duplicate, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
            try:
                file = getattr(file, "getbuffer")()
            except (AttributeError, TypeError):
                pass
            if isinstance(file, Buffer):
                file_size = buffer_length(file)
                if not file_md5:
                    file_md5 = md5(file).hexdigest()
            elif isinstance(file, (str, PathLike)):
                path = fsdecode(file)
                if not file_name:
                    file_name = basename(path)
                return do_upload(open(path, "rb"))
            elif isinstance(file, SupportsRead):
                seek = getattr(file, "seek", None)
                seekable = False
                curpos = 0
                if callable(seek):
                    if async_:
                        seek = ensure_async(seek, threaded=True)
                    try:
                        seekable = getattr(file, "seekable")()
                    except (AttributeError, TypeError):
                        try:
                            curpos = yield seek(0, 1)
                            seekable = True
                        except Exception:
                            seekable = False
                if not file_md5:
                    if not seekable:
                        fsrc = file
                        file = TemporaryFile()
                        if async_:
                            yield copyfileobj_async(fsrc, file)
                        else:
                            copyfileobj(fsrc, file)
                        file.seek(0)
                        return do_upload(file)
                    try:
                        if async_:
                            file_size, hashobj = yield file_digest_async(file)
                        else:
                            file_size, hashobj = file_digest(file)
                    finally:
                        yield cast(Callable, seek)(curpos)
                    file_md5 = hashobj.hexdigest()
                if file_size < 0:
                    try:
                        fileno = getattr(file, "fileno")()
                        file_size = fstat(fileno).st_size - curpos
                    except (AttributeError, TypeError, OSError):
                        try:
                            file_size = len(file) - curpos # type: ignore
                        except TypeError:
                            if seekable:
                                try:
                                    file_size = (yield cast(Callable, seek)(0, 2)) - curpos
                                finally:
                                    yield cast(Callable, seek)(curpos)
            elif isinstance(file, (URL, SupportsGeturl)):
                if isinstance(file, URL):
                    url = str(file)
                else:
                    url = file.geturl()
                if async_:
                    from httpfile import AsyncHttpxFileReader
                    async def request():
                        file = await AsyncHttpxFileReader.new(url)
                        async with file:
                            return await do_upload(file)
                    return request()
                else:
                    from httpfile import HTTPFileReader
                    with HTTPFileReader(url) as file:
                        return do_upload(file)
            elif not file_md5 or file_size < 0:
                if async_:
                    file = bytes_iter_to_async_reader(file) # type: ignore
                else:
                    file = bytes_iter_to_reader(file) # type: ignore
                return do_upload(file)
            if not file_name:
                file_name = getattr(file, "name", "")
                file_name = basename(file_name)
            if file_name:
                file_name = escape_filename(file_name)
            else:
                file_name = str(uuid4())
            if file_size < 0:
                file_size = getattr(file, "length", 0)
            next_slice_no = 1
            if preupload_id:
                resp = yield self.upload_list_open(
                    preupload_id, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                parts = resp["data"].get("parts")
                if not parts:
                    if not slice_size:
                        preupload_id = None
                elif len(parts) == 1:
                    if slice_size:
                        next_slice_no = slice_size == parts[0]["size"]
                    else:
                        warn("only one block was uploaded before, but it's not sure if it's complete", parts)
                        slice_size = parts[0]["size"]
                        next_slice_no = 2
                else:
                    slice_size = parts[0]["size"]
                    next_slice_no = len(parts) + (slice_size == parts[-1]["size"])
            if next_slice_no > 1:
                file_seek = getattr(file, "seek", None)
                if not callable(file_seek):
                    raise AttributeError(f"resume upload on an unseekable stream {file}")
                if async_:
                    file_seek = ensure_async(file_seek, threaded=True)
                yield file_seek(slice_size * (next_slice_no - 1))
            if not preupload_id:
                resp = yield self.upload_create_open(
                    {
                        "etag": file_md5, 
                        "filename": file_name, 
                        "size": file_size, 
                        "parentFileID": parent_id, 
                        "duplicate": duplicate, 
                        "containDir": file_name.startswith("/"), 
                    }, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                upload_data = resp["data"]
                if upload_data["reuse"]:
                    return resp
                preupload_id = upload_data["preuploadID"]
                slice_size = int(upload_data["sliceSize"])
            upload_request_kwargs = {
                **request_kwargs, 
                "method": "PUT", 
                "headers": {"authorization": ""}, 
                "parse": ..., 
            }
            try:
                if async_:
                    async def request():
                        chunks = bio_chunk_async_iter(file, chunksize=slice_size) # type: ignore
                        slice_no = next_slice_no
                        async for chunk in chunks:
                            resp = await self.upload_url_open(
                                {"preuploadID": preupload_id, "sliceNo": slice_no}, 
                                base_url=base_url, 
                                async_=True, 
                                **request_kwargs, 
                            )
                            check_response(resp)
                            upload_url = resp["data"]["presignedURL"]
                            await self.request(
                                upload_url, 
                                data=chunk, 
                                async_=True, 
                                **upload_request_kwargs, 
                            )
                            slice_no += 1
                    yield request()
                else:
                    chunks = bio_chunk_iter(file, chunksize=slice_size) # type: ignore
                    for slice_no, chunk in enumerate(chunks, next_slice_no):
                        resp = self.upload_url_open(
                            {"preuploadID": preupload_id, "sliceNo": slice_no}, 
                            base_url=base_url, 
                            **request_kwargs, 
                        )
                        check_response(resp)
                        upload_url = resp["data"]["presignedURL"]
                        self.request(upload_url, data=chunk, **upload_request_kwargs)
                return (yield self.upload_complete_open(
                    preupload_id, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                ))
            except BaseException as e:
                raise P123BrokenUpload({
                    "preupload_id": preupload_id, 
                    "file_md5": file_md5, 
                    "file_name": file_name, 
                    "file_size": file_size, 
                    "parent_id": parent_id, 
                    "duplicate": duplicate, 
                    "slice_size": slice_size, 
                }) from e
        return run_gen_step(gen_step, async_)

    ########## User API ##########

    @overload
    def user_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def user_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def user_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_OPEN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取用户信息

        GET https://open-api.123pan.com/api/v1/user/info

        .. admonition:: Reference

            /API列表/用户管理/获取用户信息

            https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/fa2w0rosunui2v4m

        :payload:
            - preuploadID: str 💡 预上传 id

        :return:
            返回的数据说明如下：

            .. code:: python

                {
                    "async": bool, # 是否需要异步查询上传结果
                    "completed": bool, # 上传是否完成
                    "fileID": int, # 上传的文件 id
                }
        """
        api = complete_url("/api/v1/user/info", base_url)
        return self.request(api, async_=async_, **request_kwargs)

    ########## API Aliases ##########

    login_open = login
    dlink_disable_open = dlink_disable
    dlink_enable_open = dlink_enable
    dlink_log_open = dlink_log
    dlink_m3u8_open = dlink_m3u8
    dlink_transcode_open = dlink_transcode
    dlink_transcode_query_open = dlink_transcode_query
    dlink_url_open = dlink_url
    download_info_open = download_info
    fs_copy_open = fs_copy
    fs_copy_one_open = fs_copy_one
    fs_copy_process_open = fs_copy_process
    fs_delete_open = fs_delete
    fs_detail_open = fs_detail
    fs_info_open = fs_info
    fs_list_open = fs_list
    fs_list_v2_open = fs_list_v2
    fs_list_v1_open = fs_list_v1
    fs_mkdir_open = fs_mkdir
    fs_move_open = fs_move
    fs_recover_open = fs_recover
    fs_recover_by_path_open = fs_recover_by_path
    fs_rename_open = fs_rename
    fs_rename_one_open = fs_rename_one
    fs_trash_open = fs_trash
    login_token_open = login_token
    login_oauth_authorize_open = login_oauth_authorize
    login_oauth_token_open = login_oauth_token
    login_oauth_verify_open = login_oauth_verify
    offline_download_open = offline_download
    offline_process_open = offline_process
    oss_copy_open = oss_copy
    oss_copy_fail_open = oss_copy_fail
    oss_copy_process_open = oss_copy_process
    oss_delete_open = oss_delete
    oss_detail_open = oss_detail
    oss_list_open = oss_list
    oss_mkdir_open = oss_mkdir
    oss_move_open = oss_move
    oss_offline_download_open = oss_offline_download
    oss_offline_process_open = oss_offline_process
    oss_upload_complete_open = oss_upload_complete
    oss_upload_create_open = oss_upload_create
    oss_upload_file_open = oss_upload_file
    oss_upload_list_open = oss_upload_list
    oss_upload_result_open = oss_upload_result
    oss_upload_url_open = oss_upload_url
    share_create_open = share_create
    share_create_payment_open = share_create_payment
    share_edit_open = share_edit
    share_edit_payment_open = share_edit_payment
    share_list_open = share_list
    share_list_payment_open = share_list_payment
    transcode_delete_open = transcode_delete
    transcode_download_open = transcode_download
    transcode_download_all_open = transcode_download_all
    transcode_m3u8_ts_download_open = transcode_m3u8_ts_download
    transcode_info_open = transcode_info
    transcode_list_open = transcode_list
    transcode_record_open = transcode_record
    transcode_resolutions_open = transcode_resolutions
    transcode_result_open = transcode_result
    transcode_upload_open = transcode_upload
    transcode_video_open = transcode_video
    upload_complete_open = upload_complete
    upload_complete_v2_open = upload_complete_v2
    upload_create_open = upload_create
    upload_create_v2_open = upload_create_v2
    upload_domain_open = upload_domain
    upload_file_open = upload_file
    upload_list_open = upload_list
    upload_result_open = upload_result
    upload_sha1_reuse_open = upload_sha1_reuse
    upload_single_open = upload_single
    upload_slice_open = upload_slice
    upload_url_open = upload_url
    user_info_open = user_info


class P123Client(P123OpenClient):
    """123 的客户端对象

    .. caution::
        优先级为：token > passport+password > refresh_token > client_id+client_secret > 扫码

        使用 refresh_token（或者说 oauth 登录），只允许访问 open 接口

    :param passport: 手机号或邮箱
    :param password: 密码
    :param token: 123 的访问令牌
    :param client_id: 应用标识，创建应用时分配的 appId
    :param client_secret: 应用密钥，创建应用时分配的 secretId
    :param refresh_token: 刷新令牌
    """
    passport: int | str = ""
    password: str = ""

    def __init__(
        self, 
        /, 
        passport: int | str | PathLike = "", 
        password: str = "", 
        token: None | str | PathLike = None, 
        client_id: str = "", 
        client_secret: str = "", 
        refresh_token: str = "", 
        check_for_relogin: bool = True, 
    ):
        self.init(
            passport=passport, 
            password=password, 
            token=token, 
            client_id=client_id, 
            client_secret=client_secret, 
            refresh_token=refresh_token, 
            check_for_relogin=check_for_relogin, 
            instance=self, 
        )

    @overload # type: ignore
    @classmethod
    def init(
        cls, 
        /, 
        passport: int | str | PathLike = "", 
        password: str = "", 
        token: None | str | PathLike = None, 
        client_id: str = "", 
        client_secret: str = "", 
        refresh_token: str = "", 
        check_for_relogin: bool = True, 
        instance: None | Self = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> P123Client:
        ...
    @overload
    @classmethod
    def init(
        cls, 
        /, 
        passport: int | str | PathLike = "", 
        password: str = "", 
        token: None | str | PathLike = None, 
        client_id: str = "", 
        client_secret: str = "", 
        refresh_token: str = "", 
        check_for_relogin: bool = True, 
        instance: None | Self = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, P123Client]:
        ...
    @classmethod
    def init(
        cls, 
        /, 
        passport: int | str | PathLike = "", 
        password: str = "", 
        token: None | str | PathLike = None, 
        client_id: str = "", 
        client_secret: str = "", 
        refresh_token: str = "", 
        check_for_relogin: bool = True, 
        instance: None | Self = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> P123Client | Coroutine[Any, Any, P123Client]:
        def gen_step():
            nonlocal token, refresh_token, client_id, client_secret
            if instance is None:
                self = cls.__new__(cls)
            else:
                self = instance
            if (isinstance(passport, PathLike) or
                not token and 
                isinstance(passport, str) and 
                len(passport) >= 128
            ):
                token = passport
            elif (not refresh_token and 
                isinstance(passport, str) and 
                len(passport) >= 48 and 
                not passport.strip(digits+ascii_uppercase)
            ):
                refresh_token = passport
            elif (not client_id and 
                isinstance(passport, str) and 
                len(passport) >= 32 and 
                not passport.strip(digits+"abcdef")
            ):
                client_id = passport
            else:
                self.passport = passport
            if (not client_secret and 
                isinstance(password, str) 
                and len(password) >= 32 and 
                not password.strip(digits+"abcdef")
            ):
                client_secret = password
            else:
                self.password = password
            self.client_id = client_id
            self.client_secret = client_secret
            self.refresh_token = refresh_token
            if token is None:
                yield self.login(async_=async_, **request_kwargs)
            elif isinstance(token, str):
                self.token = token.removeprefix("Bearer ")
            else:
                if isinstance(token, PurePath) and hasattr(token, "open"):
                    self.token_path = token
                else:
                    self.token_path = Path(fsdecode(token))
                self._read_token()
                if not self.token:
                    yield self.login(async_=async_, **request_kwargs)
            if not self.passport:
                try:
                    self.passport = self.token_user_info["username"]
                except (AttributeError, LookupError):
                    pass
            self.check_for_relogin = check_for_relogin
            return self
        return run_gen_step(gen_step, async_)

    def can_relogin(self, /) -> bool:
        return self.check_for_relogin and bool(
            self.passport and self.password or
            self.client_id and self.client_secret or 
            getattr(self, "refresh_token")
        )

    @overload # type: ignore
    def login(
        self, 
        /, 
        passport: int | str = "", 
        password: str = "", 
        client_id: str = "", 
        client_secret: str = "", 
        refresh_token: str = "", 
        remember: bool = True, 
        platform: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def login(
        self, 
        /, 
        passport: int | str = "", 
        password: str = "", 
        client_id: str = "", 
        client_secret: str = "", 
        refresh_token: str = "", 
        remember: bool = True, 
        platform: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def login(
        self, 
        /, 
        passport: int | str = "", 
        password: str = "", 
        client_id: str = "", 
        client_secret: str = "", 
        refresh_token: str = "", 
        remember: bool = True, 
        platform: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """登录以获取 access_token

        :param passport: 账号
        :param password: 密码
        :param remember: 是否记住密码（不用管）
        :param platform: 用哪个设备平台扫码
        :param base_url: 接口的基地址
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口的响应信息
        """
        if passport:
            self.passport = passport
        else:
            passport = self.passport
        if password:
            self.password = password
        else:
            password = self.password
        if client_id:
            self.client_id = client_id
        else:
            client_id = self.client_id
        if client_secret:
            self.client_secret = client_secret
        else:
            client_secret = self.client_secret
        if refresh_token:
            self.refresh_token = refresh_token
        else:
            refresh_token = self.refresh_token
        def gen_step():
            if passport and password:
                resp = yield self.login_passport(
                    {"passport": passport, "password": password, "remember": remember}, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                self.token = resp["data"]["token"]
                return resp
            elif client_id and client_secret or refresh_token:
                return self.login_open(
                    client_id, 
                    client_secret, 
                    refresh_token, 
                    async_=async_, 
                    **request_kwargs, 
                )
            else:
                resp = yield self.login_with_qrcode(
                    platform=platform, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                self.token = resp["data"]["token"]
                return resp
        return run_gen_step(gen_step, async_)

    @overload
    def login_another(
        self, 
        /, 
        replace: bool | Self = False, 
        platform: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> Self:
        ...
    @overload
    def login_another(
        self, 
        /, 
        replace: bool | Self = False, 
        platform: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, Self]:
        ...
    def login_another(
        self, 
        /, 
        replace: bool | Self = False, 
        platform: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> Self | Coroutine[Any, Any, Self]:
        """再执行一次登录

        :param replace: 替换某个 client 对象的 token

            - 如果为 P123Client, 则更新到此对象
            - 如果为 True，则更新到 `self``
            - 如果为 False，否则返回新的 ``P123Client`` 对象

        :param platform: 用哪个设备平台扫码
        :param base_url: 接口的基地址
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 客户端实例
        """
        def gen_step():
            resp = yield self.login_qrcode_auto(
                platform=platform, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
            if resp["code"] != 200:
                raise P123LoginError(errno.EAUTH, resp)
            token = resp["data"]["token"]
            if replace is False:
                return type(self)(passport=self.passport, password=self.password, token=token)
            elif replace is True:
                inst = self
            else:
                inst = replace
            inst.token = token
            return inst
        return run_gen_step(gen_step, async_)

    @overload
    def login_qrcode_auto(
        self, 
        /, 
        platform: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def login_qrcode_auto(
        self, 
        /, 
        platform: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def login_qrcode_auto(
        self, 
        /, 
        platform: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """执行一次自动扫码，但并不因此更新 ``self.token``

        .. caution::
            非会员目前只支持同时在线 3 台登录设备，VIP 则支持同时在线 10 台

        :param platform: 用哪个设备平台扫码
        :param base_url: 接口的基地址
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应
        """
        def gen_step():
            resp = yield self.login_qrcode_generate(
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
            check_response(resp)
            uniID = resp["data"]["uniID"]
            if platform:
                resp = yield self.login_qrcode_scan(
                    {"uniID": uniID, "scanPlatform": platform}, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
            resp = yield self.login_qrcode_confirm(
                uniID, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
            check_response(resp)
            resp = yield self.login_qrcode_result(
                uniID, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
            check_response(resp)
            if resp["code"] == 200 or resp["data"]["loginStatus"] not in (0, 1, 3):
                return resp
        return run_gen_step(gen_step, async_)

    @overload
    @classmethod
    def login_with_qrcode(
        cls, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @classmethod
    def login_with_qrcode(
        cls, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @classmethod
    def login_with_qrcode(
        cls, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """二维码扫码登录

        :param base_url: 接口的基地址
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应
        """
        def gen_step():
            resp = yield cls.login_qrcode_generate(
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
            check_response(resp)
            uniID = resp["data"]["uniID"]
            qrcode_url = f"{resp['data']['url']}?env=production&uniID={uniID}&source=123pan&type=login"
            from qrcode import QRCode # type: ignore
            qr = QRCode(border=1)
            qr.add_data(qrcode_url)
            qr.print_ascii(tty=isatty(1))
            while True:
                resp = yield cls.login_qrcode_result(
                    uniID, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                if resp["code"] == 200:
                    return resp
                match resp["data"]["loginStatus"]:
                    case 0:
                        print("\r\x1b[K[loginStatus=0] qrcode: waiting", end="")
                    case 1:
                        print("\r\x1b[K[loginStatus=1] qrcode: scanned", end="")
                    case 2:
                        print("\r\x1b[K[loginStatus=2] qrcode: cancelled", end="")
                        raise P123LoginError(errno.EAUTH, f"qrcode: cancelled with {resp!r}")
                    case 3:
                        print("\r\x1b[K[loginStatus=3] qrcode: login", end="")
                    case 4:
                        print("\r\x1b[K[loginStatus=4] qrcode: expired", end="")
                        raise P123LoginError(errno.EAUTH, f"qrcode: expired with {resp!r}")
                    case _:
                        raise P123LoginError(errno.EAUTH, f"qrcode: aborted with {resp!r}")
        return run_gen_step(gen_step, async_)

    ########## App API ##########

    @overload
    def app_config(
        self, 
        payload: dict | str = "OfflineDownload", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def app_config(
        self, 
        payload: dict | str = "OfflineDownload", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def app_config(
        self, 
        payload: dict | str = "OfflineDownload", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取配置信息

        POST https://www.123pan.com/api/config/get

        :payload:
            - business_key: str 💡 配置键名（字段）
        """
        if not isinstance(payload, dict):
            payload = {"business_key": payload}
        return self.request(
            "config/get", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def app_dydomain(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def app_dydomain(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def app_dydomain(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取 123 网盘的各种域名

        GET https://www.123pan.com/api/dydomain
        """
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("/api/dydomain", base_url), 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def app_id_get(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def app_id_get(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def app_id_get(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取 app-id

        GET https://www.123pan.com/api/v3/3rd/app-id
        """
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("/api/v3/3rd/app-id", base_url), 
            **request_kwargs, 
        )

    @overload
    def app_permission_delete(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def app_permission_delete(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def app_permission_delete(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """第三方挂载工具登录授权列表

        DELETE https://www.123pan.com/api/restful/goapi/v1/oauth2/app_permission

        :payload:
            - appId: str 💡 应用 id，也就是 ``client_id``
        """
        if not isinstance(payload, dict):
            payload = {"appId": payload}
        return self.request(
            "restful/goapi/v1/oauth2/app_permission", 
            "DELETE", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def app_permission_list(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def app_permission_list(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def app_permission_list(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """第三方挂载工具登录授权列表

        GET https://www.123pan.com/api/restful/goapi/v1/oauth2/app_permission/list

        :payload:
            - page: int = 1 💡 第几页
            - pageSize: int = 100 💡 分页大小
        """
        if not isinstance(payload, dict):
            payload = {"page": payload}
        payload.setdefault("pageSize", 100)
        return self.request(
            "restful/goapi/v1/oauth2/app_permission/list", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def app_server_time(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def app_server_time(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def app_server_time(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取 123 网盘的服务器时间戳

        GET https://www.123pan.com/api/get/server/time
        """
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("/api/get/server/time", base_url), 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def app_transfer_metrics(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def app_transfer_metrics(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def app_transfer_metrics(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取和传输有关的配置信息

        GET https://www.123pan.com/api/transfer/metrics/whether/report
        """
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("/api/transfer/metrics/whether/report", base_url), 
            **request_kwargs, 
        )

    ########## Download API ##########

    @overload
    def dlink_disable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_disable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_disable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """禁用直链空间

        POST https://www.123pan.com/api/cdn-link/disable

        :payload:
            - fileID: int | str 💡 目录 id
        """
        if not isinstance(payload, dict):
            payload = {"fileID": payload}
        return self.request(
            "cdn-link/disable", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def dlink_enable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_enable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_enable(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """启用直链空间

        POST https://www.123pan.com/api/cdn-link/enable

        :payload:
            - fileID: int | str 💡 目录 id
        """
        if not isinstance(payload, dict):
            payload = {"fileID": payload}
        return self.request(
            "cdn-link/enable", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def dlink_url(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def dlink_url(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def dlink_url(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取直链链接

        GET https://www.123pan.com/api/cdn-link/url

        :payload:
            - fileID: int | str 💡 文件 id
        """
        if not isinstance(payload, dict):
            payload = {"fileID": payload}
        return self.request(
            "cdn-link/url", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    ########## Download API ##########

    @overload
    def download_info(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def download_info(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def download_info(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取下载信息

        POST https://www.123pan.com/api/file/download_info

        .. hint::
            即使文件已经被删除，只要还有 S3KeyFlag 和 Etag （即 MD5） 就依然可以下载

            你完全可以构造这样的查询参数

            .. code:: python

                payload = {
                    "Etag": "...", # 必填，文件的 MD5
                    "FileID": 0, # 可以随便填
                    "FileName": "a", # 随便填一个名字
                    "S3KeyFlag": str # 必填，格式为 f"{UID}-0"，UID 就是上传此文件的用户的 UID，如果此文件是由你上传的，则可从 ``P123Client.user_info`` 的响应中获取
                    "Size": 0, # 可以随便填，填了可能搜索更准确
                }

        .. note::
            获取的直链有效期是 24 小时

        :payload:
            - Etag: str 💡 文件的 MD5 散列值
            - S3KeyFlag: str
            - FileName: str = <default> 💡 默认用 Etag（即 MD5）作为文件名
            - FileID: int | str = 0
            - Size: int = <default>
            - Type: int = 0
            - driveId: int | str = 0
            - ...
        """
        def gen_step():
            nonlocal payload
            update_headers_in_kwargs(request_kwargs, platform="android")
            if not isinstance(payload, dict):
                resp = yield self.fs_info(
                    payload, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                resp["payload"] = payload
                check_response(resp)
                if not (info_list := resp["data"]["infoList"]):
                    raise FileNotFoundError(errno.ENOENT, resp)
                payload = cast(dict, info_list[0])
                if payload["Type"]:
                    raise IsADirectoryError(errno.EISDIR, resp)
            payload = dict_key_to_lower_merge(
                payload, {"driveId": 0, "Type": 0, "FileID": 0})
            if "filename" not in payload:
                payload["filename"] = payload["etag"]
            return self.request(
                "file/download_info", 
                "POST", 
                json=payload, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
        return run_gen_step(gen_step, async_)

    @overload
    def download_info_batch(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def download_info_batch(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def download_info_batch(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取批量下载信息

        POST https://www.123pan.com/api/file/batch_download_info

        .. attention::
            会把一些文件或目录以 zip 包的形式下载，但非会员有流量限制，所以还是推荐用 ``P123Client.download_info`` 逐个获取下载链接并下载

        :payload:
            - fileIdList: list[FileID]

                .. code:: python

                    FileID = {
                        "FileId": int | str
                    }
        """
        if isinstance(payload, (int, str)):
            payload = {"fileIdList": [{"FileId": payload}]}
        elif not isinstance(payload, dict):
            payload = {"fileIdList": [{"FileId": fid} for fid in payload]}
        return self.request(
            "file/batch_download_info", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def download_url(
        self, 
        payload: dict | int | str, 
        /, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> str:
        ...
    @overload
    def download_url(
        self, 
        payload: dict | int | str, 
        /, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, str]:
        ...
    def download_url(
        self, 
        payload: dict | int | str, 
        /, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> str | Coroutine[Any, Any, str]:
        """获取下载链接

        .. note::
            ``payload`` 支持多种格式的输入，按下面的规则按顺序进行判断：

            1. 如果是 ``int`` 或 ``str``，则视为文件 id，必须在你的网盘中存在此文件
            2. 如果是 ``dict`` （不区分大小写），有 "S3KeyFlag", "Etag" 和 "Size" 的值，则直接获取链接，文件不必在你网盘中
            3. 如果是 ``dict`` （不区分大小写），有 "Etag" 和 "Size" 的值，则会先秒传（临时文件路径为 /.tempfile）再获取链接，文件不必在你网盘中
            4. 如果是 ``dict`` （不区分大小写），有 "FileID"，则会先获取信息，再获取链接，必须在你的网盘中存在此文件
            5. 否则会报错 ValueError

        :param payload: 文件 id 或者文件信息，文件信息必须包含的信息如下：

            - FileID: int | str 💡 下载链接
            - S3KeyFlag: str    💡 s3 存储名
            - Etag: str         💡 文件的 MD5 散列值
            - Size: int         💡 文件大小
            - FileName: str     💡 默认用 Etag（即 MD5）作为文件名，可以省略

        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 下载链接
        """
        def gen_step():
            nonlocal payload
            if isinstance(payload, dict):
                payload = dict_map(payload, key=str.lower)
                if not ("size" in payload and "etag" in payload):
                    if fileid := payload.get("fileid"):
                        resp = yield self.fs_info(fileid, async_=async_, **request_kwargs)
                        check_response(resp)
                        if not (info_list := resp["data"]["infoList"]):
                            raise P123OSError(errno.ENOENT, resp)
                        info = info_list[0]
                        if info["Type"]:
                            raise IsADirectoryError(errno.EISDIR, resp)
                        payload = dict_key_to_lower_merge(payload, info)
                    else:
                        raise ValueError("`Size` and `Etag` must be provided")
                if "s3keyflag" not in payload:
                    resp = yield self.upload_request(
                        {
                            "filename": ".tempfile", 
                            "duplicate": 2, 
                            "etag": payload["etag"], 
                            "size": payload["size"], 
                            "type": 0, 
                        }, 
                        async_=async_, 
                        **request_kwargs, 
                    )
                    check_response(resp)
                    if not resp["data"]["Reuse"]:
                        raise P123OSError(errno.ENOENT, resp)
                    payload["s3keyflag"] = resp["data"]["Info"]["S3KeyFlag"]
                resp = yield self.download_info(
                    payload, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                return resp["data"]["DownloadUrl"]
            else:
                resp = yield self.download_info_open(
                    payload, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                return resp["data"]["downloadUrl"]
        return run_gen_step(gen_step, async_)

    ########## File System API ##########

    @overload
    def fs_abnormal_count(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_abnormal_count(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_abnormal_count(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取异常文件数

        GET https://www.123pan.com/b/api/file/abnormal/count
        """
        return self.request(
            "file/abnormal/count", 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_archive_list(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_archive_list(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_archive_list(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """推送【云解压】任务

        GET https://www.123pan.com/api/restful/goapi/v1/archive/file/list

        .. note::
            后台异步执行，任务结果请从 ``client.fs_archive_status()`` 接口获取

        :payload:
            - fileId: int | str 💡 压缩包的文件 id
            - password: int | str = "" 💡 解压密码
        """
        if not isinstance(payload, dict):
            payload = {"fileId": payload}
        return self.request(
            "restful/goapi/v1/archive/file/list", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_archive_status(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_archive_status(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_archive_status(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """推送云解压任务

        GET https://www.123pan.com/api/restful/goapi/v1/archive/file/status

        .. note::
            响应结果中包含 "state" 字段，具体含义为

            - 0: 未运行或不存在
            - 1: 运行中
            - 2: 成功
            - 3: 失败

        :payload:
            - fileId: int | str 💡 压缩包的文件 id
            - taskId: int | str 💡 任务 id
            - taskType: int = <default> 💡 任务类型。目前已知：1:云解压 2:解压到
        """
        return self.request(
            "restful/goapi/v1/archive/file/status", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_archive_uncompress(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_archive_uncompress(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_archive_uncompress(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """推送【解压到】任务

        POST https://www.123pan.com/api/restful/goapi/v1/archive/file/uncompress

        :payload:
            - fileId: int | str           💡 压缩包的文件 id
            - password: int | str = ""    💡 解压密码
            - targetFileId: int | str = 0 💡 保存到的目录 id
            - taskId: int                 💡 任务 id
            - list: list[FileInfo]        💡 选择要解压的文件列表，信息来自 ``client.fs_archive_status()`` 接口的响应

                .. code:: python

                    FileInfo: {
                        "fontId": str, 
                        "fileName": str, 
                        "parentFile": str, 
                        "filePath": str, 
                        "fileSize": int, 
                        "fileType": 0 | 1, 
                        "createTime": str, 
                        "category": int, 
                        "childFiles": None | list[FileInfo], 
                    }
        """
        payload.setdefault("targetFileId", 0)
        return self.request(
            "restful/goapi/v1/archive/file/uncompress", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_copy(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_copy(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_copy(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """复制

        POST https://www.123pan.com/api/restful/goapi/v1/file/copy/async

        :payload:
            - fileList: list[File] 💡 信息可以取自 ``P123Client.fs_info`` 接口

                .. code:: python

                    File = { 
                        "FileId": int | str, 
                        ...
                    }

            - targetFileId: int | str = 0
        """
        def gen_step():
            nonlocal payload
            if not isinstance(payload, dict):
                resp = yield self.fs_info(
                    payload, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                resp["payload"] = payload
                check_response(resp)
                info_list = resp["data"]["infoList"]
                if not info_list:
                    raise FileNotFoundError(errno.ENOENT, resp)
                payload = {"fileList": info_list}
            payload = dict_key_to_lower_merge(payload, targetFileId=parent_id)
            return self.request(
                "restful/goapi/v1/file/copy/async", 
                "POST", 
                json=payload, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
        return run_gen_step(gen_step, async_)

    @overload
    def fs_copy_task(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_copy_task(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_copy_task(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """复制：任务进度

        GET https://www.123pan.com/api/restful/goapi/v1/file/copy/task

        :payload:
            - taskId: int 💡 任务 id
        """
        def gen_step():
            nonlocal payload
            if not isinstance(payload, dict):
                payload = {"taskId": payload}
            return self.request(
                "restful/goapi/v1/file/copy/task", 
                params=payload, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
        return run_gen_step(gen_step, async_)

    @overload
    def fs_detail(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_detail(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_detail(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取文件或目录详情（文件数、目录数、总大小）

        GET https://www.123pan.com/api/file/detail

        :payload:
            - fileID: int | str
        """
        if isinstance(payload, (int, str)):
            payload = {"fileID": payload}
        return self.request(
            "file/detail", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_details(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_details(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_details(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取文件或目录详情（文件数、目录数、总大小等）

        POST https://www.123pan.com/api/restful/goapi/v1/file/details

        :payload:
            - file_ids: list[int] 💡 文件或目录的 id 列表
        """
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"file_ids": payload}
        return self.request(
            "restful/goapi/v1/file/details", 
            method="POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_delete(
        self, 
        payload: dict | int | str | Iterable[int | str] = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_delete(
        self, 
        payload: dict | int | str | Iterable[int | str] = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_delete(
        self, 
        payload: dict | int | str | Iterable[int | str] = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """彻底删除

        POST https://www.123pan.com/api/file/delete

        .. hint::
            彻底删除文件前,文件必须要在回收站中,否则无法删除

        :payload:
            - fileIdList: list[FileID]

                .. code:: python

                    FileID = {
                        "FileId": int | str
                    }

            - event: str = "recycleDelete"
        """
        if isinstance(payload, (int, str)):
            payload = {"fileIdList": [{"FileId": payload}]}
        elif not isinstance(payload, dict):
            payload = {"fileIdList": [{"FileId": fid} for fid in payload]}
        payload = cast(dict, payload)
        payload.setdefault("event", "recycleDelete")
        return self.request(
            "file/delete", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_export_tree(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_export_tree(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_export_tree(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """导出目录树

        POST https://www.123pan.com/api/restful/goapi/v1/file/export-tree

        .. caution::
            单次最多支持导出 100 万条目录数据

        :payload:
            - fileIds: list[int] 💡 文件或目录的 id 列表
            - exportLayer: int = 0 💡 导出层级：0-导出全部 n-导出1级到n级
            - exportName: str = <default> 💡 存储为（文本文件名）：默认为 f"目录树_{datetime.datetime.now().strftime("%FT%T")}.txt"
            - exportParentId: int = 0 💡 存储位置
            - exportStyle: 1 | 2 = 2 💡 导出目录样式：1-目录树 2-目录列表
            - exportType: 1 | 2 | 3 = 3 💡 导出类型：1-包含文件 2-包含文件夹 3-包含文件和文件夹
            - treeRootType: 1 | 2 = 1 💡 目录树根：1-当前目录 2-网盘根目录
        """
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIds": payload}
        payload = dict_key_to_lower_merge(payload, {
            "exportLayer": 0, 
            "exportName": f"目录树_{datetime.now().strftime("%FT%T")}.txt", 
            "exportParentId": 0, 
            "treeRootType": 1, 
            "exportStyle": 2, 
            "exportType": 3, 
        })
        return self.request(
            "restful/goapi/v1/file/export-tree", 
            method="POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_get_path(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_get_path(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_get_path(
        self, 
        payload: dict | int, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取某个 id 对应的祖先节点列表

        POST https://www.123pan.com/api/file/get_path

        .. note::
            随后你可以把这组祖先节点 id 传给 ``client.fs_info()`` 接口，即可获得具体的节点信息

        :payload:
            - fileId: int 💡 文件 id
        """
        if isinstance(payload, int):
            payload = {"fileId": payload}
        return self.request(
            "file/get_path", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_get_path_history(
        self, 
        payload: dict | int | str | Iterable[int | str] = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_get_path_history(
        self, 
        payload: dict | int | str | Iterable[int | str] = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_get_path_history(
        self, 
        payload: dict | int | str | Iterable[int | str] = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """分别获取一组 id 对应的祖先节点信息（此接口是 ``client.fs_get_path()`` 的加强版）

        POST https://www.123pan.com/api/file/get_path_history

        :payload:
            - fileIdList: list[int]
        """
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIdList": payload}
        return self.request(
            "file/get_path_history", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_info(
        self, 
        payload: dict | int | str | Iterable[int | str] = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_info(
        self, 
        payload: dict | int | str | Iterable[int | str] = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_info(
        self, 
        payload: dict | int | str | Iterable[int | str] = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取文件信息

        POST https://www.123pan.com/api/file/info

        :payload:
            - fileIdList: list[FileID]

                .. code:: python

                    FileID = {
                        "FileId": int | str
                    }
        """
        if isinstance(payload, (int, str)):
            payload = {"fileIdList": [{"FileId": payload}]}
        elif not isinstance(payload, dict):
            payload = {"fileIdList": [{"FileId": fid} for fid in payload]}
        return self.request(
            "file/info", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload # type: ignore
    def fs_list(
        self, 
        payload: dict | int | str = 0, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_list(
        self, 
        payload: dict | int | str = 0, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_list(
        self, 
        payload: dict | int | str = 0, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取文件列表（可搜索）

        GET https://www.123pan.com/api/file/list

        .. note::
            如果返回信息中，"Next" 字段的值为 "-1"，代表最后一页（无需再翻页查询）

        .. caution::
            返回信息中的 "Total" 字段固定为 0， 所以获取不了目录内的子节点数

        :payload:
            - driveId: int | str = 0
            - limit: int = 100 💡 分页大小，最多 100 个
            - next: int = 0    💡 下一批拉取开始的 id
            - orderBy: str = "file_id" 💡 排序依据（⚠️ 不可用，固定等同于 "file_id"）
            - orderDirection: "asc" | "desc" = "asc" 💡 排序顺序（⚠️ 固定等同于 "asc"，且填入 "desc" 会返回空列表）
            - Page: int = <default> 💡 第几页，从 1 开始，可以是 0（⚠️ 不可用）
            - parentFileId: int | str = 0 💡 父目录 id
            - trashed: bool = <default> 💡 是否查看回收站的文件
            - inDirectSpace: bool  = False
            - event: str = "homeListFile" 💡 事件名称

                - "homeListFile": 全部文件
                - "recycleListFile": 回收站
                - "syncFileList": 同步空间

            - operateType: int | str = <default> 💡 操作类型，如果在同步空间，则需要指定为 "SyncSpacePage"
            - SearchData: str = <default> 💡 搜索关键字
            - OnlyLookAbnormalFile: int = <default>
        """
        if isinstance(payload, (int, str)):
            payload = {"parentFileId": payload}
        payload = dict_key_to_lower_merge(payload, {
            "driveId": 0, 
            "limit": 100, 
            "next": 0, 
            "orderDirection": "asc", 
            "parentFileId": 0, 
            "inDirectSpace": False, 
            "event": event, 
        })
        if payload.get("trashed") is None:
            payload["trashed"] = payload["event"] == "recycleListFile"
        return self.request(
            "file/list", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_list_by_type(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_list_by_type(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_list_by_type(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """按类型获取文件列表

        GET https://www.123pan.com/api/restful/goapi/v1/file/category/list-by-type

        .. note::
            如果返回信息中，"Next" 字段的值为 "-1"，代表最后一页（无需再翻页查询）

        .. caution::
            目前，返回信息中并无 "Total" 字段，所以不能直接知道文件总数

        :payload:
            - driveId: int | str = 0
            - limit: int = 100  💡 分页大小，最多 100 个
            - next: int = 0     💡 下一批拉取开始的 id（⚠️ 不可用）
            - category: int = 1 💡 分类代码

                - 1: 视频
                - 2: 图片
                - 3: 文档
                - 4: 音频
                - 5: 其它

            - dateGranularity: int = <default> 💡 按时间分组展示

                - 1: 日
                - 2: 月
                - 3: 年
    
            - orderBy: str = "file_name" 💡 排序依据

                - "file_name":   文件名
                - "size":        文件大小
                - "create_at":   创建时间
                - "update_at":   创建时间
                - "update_time": 更新时间
                - ...（其它可能值）

            - orderDirection: "asc" | "desc" = "asc" 💡 排序顺序
            - Page: int = 1 💡 第几页，从 1 开始
            - parentFileId: int | str = 0 💡 父目录 id
            - trashed: bool = <default> 💡 是否查看回收站的文件
            - inDirectSpace: bool  = False
            - event: str = "homeListFile" 💡 事件名称

                - "homeListFile": 全部文件
                - "recycleListFile": 回收站
                - "syncFileList": 同步空间

            - operateType: int | str = <default> 💡 操作类型，如果在同步空间，则需要指定为 "SyncSpacePage"

                .. note::
                    这个值似乎不影响结果，所以可以忽略。我在浏览器中，看到罗列根目录为 1，搜索（指定 ``SearchData``）为 2，同步空间的根目录为 3，罗列其它目录大多为 4，偶尔为 8，也可能是其它值

            - isSearchOrder: bool = <default>
            - SearchData: str = <default> 💡 搜索关键字
            - OnlyLookAbnormalFile: int = 0 💡 大概可传入 0 或 1
        """
        if not isinstance(payload, dict):
            payload = {"Page": payload}
        payload = dict_key_to_lower_merge(payload, {
            "driveId": 0, 
            "limit": 100, 
            "next": 0, 
            "category": 1, 
            "orderBy": "file_name", 
            "orderDirection": "asc", 
            "parentFileId": 0, 
            "inDirectSpace": False, 
            "event": event, 
            "OnlyLookAbnormalFile": 0, 
            "Page": 1, 
        })
        if payload.get("trashed") is None:
            payload["trashed"] = payload["event"] == "recycleListFile"
        return self.request(
            "restful/goapi/v1/file/category/list-by-type", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_list_new(
        self, 
        payload: dict | int | str = 0, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_list_new(
        self, 
        payload: dict | int | str = 0, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_list_new(
        self, 
        payload: dict | int | str = 0, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取文件列表（可搜索）

        GET https://www.123pan.com/api/file/list/new

        .. note::
            如果返回信息中，"Next" 字段的值为 "-1"，代表最后一页（无需再翻页查询）

        :payload:
            - driveId: int | str = 0
            - limit: int = 100 💡 分页大小，最多 100 个（如果 "SearchData" 为空且请求头的 "platform" 字段为 "web"，则固定为 500）
            - orderBy: str = "file_id" 💡 排序依据

                - "file_id": 文件 id，也可以写作 "fileId"
                - "file_name":   文件名
                - "size":        文件大小
                - "create_at":   创建时间
                - "update_at":   创建时间
                - "update_time": 更新时间
                - "trashed_at":  删除时间
                - "remain_days": 剩余保留天数
                - "share_id":    分享 id
                - ...（其它可能值）

            - orderDirection: "asc" | "desc" = "asc" 💡 排序顺序
            - Page: int = 1 💡 第几页，从 1 开始
            - parentFileId: int | str = 0 💡 父目录 id
            - parentFileName: str = <default> 💡 父目录名
            - trashed: bool = <default> 💡 是否查看回收站的文件
            - inDirectSpace: bool  = False
            - fileCategory: int = 0 💡 文件类型：0-全部 1-图片 2-视频 3-音频 4-文档 5-文件夹 6-压缩包 7-其它
            - event: str = "homeListFile" 💡 事件名称

                - "homeListFile": 全部文件
                - "recycleListFile": 回收站
                - "syncFileList": 同步空间

            - operateType: int | str = <default> 💡 操作类型，如果在同步空间，则需要指定为 "SyncSpacePage"

                .. note::
                    这个值似乎不影响结果，所以可以忽略。我在浏览器中，看到罗列根目录为 1，搜索（指定 ``SearchData``）为 2，同步空间的根目录为 3，罗列其它目录大多为 4，偶尔为 8，也可能是其它值

            - isSearchOrder: bool = <default>
            - SearchData: str = <default> 💡 搜索关键字（最多能搜出 1 万条）
            - OnlyLookAbnormalFile: int = 0 💡 大概可传入 0 或 1
            - RequestSource: int = <default> 💡 浏览器中，在同步空间中为 1
        """
        if isinstance(payload, (int, str)):
            payload = {"parentFileId": payload}
        payload = dict_key_to_lower_merge(payload, {
            "driveId": 0, 
            "limit": 100, 
            "orderBy": "file_id", 
            "orderDirection": "asc", 
            "parentFileId": 0, 
            "inDirectSpace": False, 
            "fileCategory": 0, 
            "event": event, 
            "OnlyLookAbnormalFile": 0, 
            "Page": 1, 
        })
        if payload.get("trashed") is None:
            payload["trashed"] = payload["event"] == "recycleListFile"
        return self.request(
            "file/list/new", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload # type: ignore
    def fs_mkdir(
        self, 
        name: str, 
        /, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_mkdir(
        self, 
        name: str, 
        /, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_mkdir(
        self, 
        name: str, 
        /, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建目录，此接口是 ``client.upload_request()`` 的封装

        :param name: 目录名
        :param parent_id: 父目录 id
        :param duplicate: 处理同名：0: 复用 1: 保留两者 2: 替换
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应
        """
        payload = {"filename": name, "parentFileId": parent_id}
        if duplicate:
            payload["NotReuse"] = True
            payload["duplicate"] = duplicate
        return self.upload_request(
            payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_move(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_move(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_move(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """移动

        POST https://www.123pan.com/api/file/mod_pid

        :payload:
            - fileIdList: list[FileID]

                .. code:: python

                    FileID = {
                        "FileId": int | str
                    }

            - parentFileId: int | str = 0
            - event: str = "fileMove"
        """
        if isinstance(payload, (int, str)):
            payload = {"fileIdList": [{"FileId": payload}]}
        elif not isinstance(payload, dict):
            payload = {"fileIdList": [{"FileId": fid} for fid in payload]}
        payload = dict_key_to_lower_merge(payload, {"parentFileId": parent_id, "event": "fileMove"})
        return self.request(
            "file/mod_pid", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_refresh(
        self, 
        payload: dict = {}, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_refresh(
        self, 
        payload: dict = {}, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_refresh(
        self, 
        payload: dict = {}, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """刷新列表和直链缓存

        POST https://www.123pan.com/api/restful/goapi/v1/cdnLink/cache/refresh
        """
        return self.request(
            "restful/goapi/v1/cdnLink/cache/refresh", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload # type: ignore
    def fs_rename(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_rename(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_rename(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """（单个）改名

        POST https://www.123pan.com/api/file/rename

        :payload:
            - FileId: int | str
            - fileName: str
            - driveId: int | str = 0
            - duplicate: 0 | 1 | 2 = 0 💡 处理同名：0: 提示/忽略 1: 保留两者 2: 替换
            - event: str = "fileRename"
        """
        payload = dict_key_to_lower_merge(payload, {
            "driveId": 0, 
            "duplicate": 0, 
            "event": "fileRename", 
        })
        return self.request(
            "file/rename", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_safe_box_lock(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_safe_box_lock(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_safe_box_lock(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """锁定保险箱

        POST https://www.123pan.com/api/restful/goapi/v1/file/safe_box/auth/lock
        """
        return self.request(
            "restful/goapi/v1/file/safe_box/auth/lock", 
            "POST", 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_safe_box_unlock(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_safe_box_unlock(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_safe_box_unlock(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """解锁保险箱

        .. note::
            保险箱的 id，可以用 ``client.user_info()`` 接口获得，字段为 "SafeBoxFileId"

        POST https://www.123pan.com/api/restful/goapi/v1/file/safe_box/auth/unlockbox

        :payload:
            - password: int | str 💡 6 位密码
        """
        if not isinstance(payload, dict):
            payload = {"password": payload}
        return self.request(
            "restful/goapi/v1/file/safe_box/auth/unlockbox", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_star(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        star: bool = True, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_star(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        star: bool = True, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_star(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        star: bool = True, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """给文件或目录，设置或取消星标（收藏）

        POST https://www.123pan.com/api/restful/goapi/v1/file/starred

        :payload:
            - fileIdList: list[int | str] 💡 id 列表
            - starredStatus: int = 255    💡 是否设置星标：1:取消 255:设置
        """
        if isinstance(payload, (int, str)):
            payload = {"fileIdList": [payload], "starredStatus": 255}
        elif not isinstance(payload, dict):
            if not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIdList": payload, "starredStatus": 255}
        else:
            payload.setdefault("starredStatus", 255 if star else 1)
        return self.request(
            "restful/goapi/v1/file/starred", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_star_list(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_star_list(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_star_list(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "homeListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """罗列已星标的文件或目录

        GET https://www.123pan.com/api/restful/goapi/v1/file/starred/list

        :payload:
            - driveId: int | str = 0
            - next: int = 0    💡 下一批拉取开始的 id
            - orderBy: str = "file_name" 💡 排序依据

                - "file_id": 文件 id，也可以写作 "fileId"
                - "file_name":   文件名
                - "size":        文件大小
                - "create_at":   创建时间
                - "update_at":   创建时间
                - "update_time": 更新时间
                - "trashed_at":  删除时间
                - "share_id":    分享 id
                - "remain_days": 剩余保留天数
                - ...（其它可能值）

            - orderDirection: "asc" | "desc" = "asc" 💡 排序顺序
            - Page: int = 1 💡 第几页，从 1 开始
            - pageSize: int = 100 💡 分页大小，最多 100 个
            - parentFileId: int | str = 0 💡 父目录 id
            - trashed: bool = <default> 💡 是否查看回收站的文件
            - inDirectSpace: bool  = False
            - fileCategory: int = 0 💡 文件类型：0-全部 1-图片 2-视频 3-音频 4-文档 5-文件夹 6-压缩包 7-其它
            - event: str = "homeListFile" 💡 事件名称

                - "homeListFile": 全部文件
                - "recycleListFile": 回收站
                - "syncFileList": 同步空间

            - operateType: int | str = <default> 💡 操作类型，如果在同步空间，则需要指定为 "SyncSpacePage"

                .. note::
                    这个值似乎不影响结果，所以可以忽略。我在浏览器中，看到罗列根目录为 1，搜索（指定 ``SearchData``）为 2，同步空间的根目录为 3，罗列其它目录大多为 4，偶尔为 8，也可能是其它值

            - isSearchOrder: bool = <default>
            - SearchData: str = <default> 💡 搜索关键字
            - OnlyLookAbnormalFile: int = 0 💡 大概可传入 0 或 1
        """
        if not isinstance(payload, dict):
            payload = {"Page": payload}
        payload = dict_key_to_lower_merge(payload, {
            "driveId": 0, 
            "next": 0, 
            "orderBy": "file_name", 
            "orderDirection": "asc", 
            "Page": 1, 
            "pageSize": 100, 
            "parentFileId": 0, 
            "inDirectSpace": False, 
            "fileCategory": 0, 
            "event": event, 
            "OnlyLookAbnormalFile": 0, 
        })
        if payload.get("trashed") is None:
            payload["trashed"] = payload["event"] == "recycleListFile"
        return self.request(
            "restful/goapi/v1/file/starred/list", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_sync_log(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_sync_log(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_sync_log(
        self, 
        payload: dict | int = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取同步空间的操作记录

        GET https://www.123pan.com/api/restful/goapi/v1/sync-disk/file/log

        :payload:
            - page: int = 1               💡 第几页
            - pageSize: int = 100         💡 每页大小
            - searchData: str = <default> 💡 搜索关键字
        """
        if not isinstance(payload, dict):
            payload = {"page": payload, "pageSize": 100}
        return self.request(
            "restful/goapi/v1/sync-disk/file/log", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload # type: ignore
    def fs_trash(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        event: str = "intoRecycle", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_trash(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        event: str = "intoRecycle", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_trash(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        event: str = "intoRecycle", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """操作回收站

        POST https://www.123pan.com/api/file/trash

        :payload:
            - fileTrashInfoList: list[File] 💡 信息可以取自 ``P123Client.fs_info`` 接口，也可以仅文件 id

                .. code:: python

                    File = { 
                        "FileId": int | str, 
                        ...
                    }

            - driveId: int = 0
            - event: str = "intoRecycle" 💡 事件类型

                - "intoRecycle": 移入回收站
                - "recycleRestore": 移出回收站

            - operation: bool = <default>
            - operatePlace: int = <default>
            - RequestSource: int = <default> 💡 浏览器中，在同步空间中为 1
            - safeBox: bool = <default>
        """
        if isinstance(payload, (int, str)):
            payload = {"fileTrashInfoList": [{"FileId": payload}]}
        elif not isinstance(payload, dict):
            payload = {"fileTrashInfoList": [{"FileId": fid} for fid in payload]}
        payload = dict_key_to_lower_merge(payload, {"driveId": 0, "event": event})
        if payload.get("operation") is None:
            payload["operation"] = payload["event"] != "recycleRestore"
        return self.request(
            "file/trash", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_trash_clear(
        self, 
        payload: dict = {"event": "recycleClear"}, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_trash_clear(
        self, 
        payload: dict = {"event": "recycleClear"}, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_trash_clear(
        self, 
        payload: dict = {"event": "recycleClear"}, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """清空回收站

        POST https://www.123pan.com/api/file/trash_delete_all

        :payload:
            - event: str = "recycleClear"
        """
        payload.setdefault("event", "recycleClear")
        return self.request(
            "file/trash_delete_all", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_trash_recover_by_path(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_trash_recover_by_path(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_trash_recover_by_path(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        parent_id: int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """回收站：还原到指定位置

        POST https://www.123pan.com/api/file/recover/by_path

        :payload:
            - fileIds: list[int] 💡 文件或目录的 id 列表
            - parentFileId: int = 0 💡 父目录 id
        """
        if not isinstance(payload, dict):
            if isinstance(payload, (int, str)):
                payload = [payload]
            elif not isinstance(payload, (tuple, list)):
                payload = list(payload)
            payload = {"fileIds": payload}
        payload = dict_key_to_lower_merge(payload, parentFileId=parent_id)
        return self.request(
            "file/recover/by_path", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def fs_video_play_conf(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def fs_video_play_conf(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def fs_video_play_conf(
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取视频播放列表的配置信息

        GET https://www.123pan.com/api/video/play/conf
        """
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("/api/get/server/time", base_url), 
            **request_kwargs, 
        )

    @overload
    def fs_video_play_list(
        self, 
        payload: dict | int | str = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_video_play_list(
        self, 
        payload: dict | int | str = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_video_play_list(
        self, 
        payload: dict | int | str = 0, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取某个目录下的视频列表

        GET https://www.123pan.com/api/file/video/play/list

        :payload:
            - page: int = 1
            - page_size: int = 100
            - parent_file_id: int = 0
        """
        if not isinstance(payload, dict):
            payload = {"parent_file_id": payload}
        payload.setdefault("page", 1)
        payload.setdefault("page_size", 100)
        return self.request(
            "file/video/play/list", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_webdav_account_create(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_webdav_account_create(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_webdav_account_create(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """WebDAV 添加应用

        POST https://www.123pan.com/api/restful/goapi/v1/webdav/account/create

        .. caution::
            密码不能自己设置，只会自动生成

        :payload:
            - app: str 💡 应用名字
        """
        if not isinstance(payload, dict):
            payload = {"app": payload}
        return self.request(
            "restful/goapi/v1/webdav/account/create", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_webdav_account_delete(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_webdav_account_delete(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_webdav_account_delete(
        self, 
        payload: dict | int | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """WebDAV 删除应用（解除授权）

        GET https://www.123pan.com/api/restful/goapi/v1/webdav/account/del

        :payload:
            - id: int | str 💡 应用 id
        """
        if not isinstance(payload, dict):
            payload = {"id": payload}
        return self.request(
            "restful/goapi/v1/webdav/account/del", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def fs_webdav_account_list(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def fs_webdav_account_list(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def fs_webdav_account_list(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """WebDAV 授权列表

        GET https://www.123pan.com/api/restful/goapi/v1/webdav/account/list
        """
        return self.request(
            "restful/goapi/v1/webdav/account/list", 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    ########## Qrcode API ##########

    @overload
    @staticmethod
    def login_passport(
        payload: dict, 
        /, 
        request: None | Callable = None, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def login_passport(
        payload: dict, 
        /, 
        request: None | Callable = None, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def login_passport(
        payload: dict, 
        /, 
        request: None | Callable = None, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """使用账号和密码登录

        POST https://www.123pan.com/api/user/sign_in

        .. note::
            获取的 token 有效期 30 天

        :payload:
            - passport: int | str   💡 手机号或邮箱
            - password: str         💡 密码
            - remember: bool = True 💡 是否记住密码（不用管）
        """
        api = complete_url("user/sign_in", base_url)
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(url=api, method="POST", json=payload, **request_kwargs)

    @overload
    @staticmethod
    def login_qrcode_bind_wx_code(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def login_qrcode_bind_wx_code(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def login_qrcode_bind_wx_code(
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """绑定微信号

        POST https://login.123pan.com/api/user/qr-code/bind_wx_code

        :payload:
            - uniID: str  💡 二维码 id
            - wxcode: str 💡 微信码
        """
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("user/qr-code/bind_wx_code", base_url), 
            method="POST", 
            json=payload, 
            **request_kwargs, 
        )

    @overload
    def login_qrcode_confirm(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def login_qrcode_confirm(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def login_qrcode_confirm(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """确认扫码登录

        POST https://login.123pan.com/api/user/qr-code/login

        :payload:
            - uniID: str 💡 二维码 id
        """
        if not isinstance(payload, dict):
            payload = {"uniID": payload}
        return self.request(
            "user/qr-code/login", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def login_qrcode_deny(
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def login_qrcode_deny(
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def login_qrcode_deny(
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """更新扫码状态为：已取消（loginStatus=2）

        POST https://login.123pan.com/api/user/qr-code/deny

        :payload:
            - uniID: str 💡 二维码 id
        """
        if not isinstance(payload, dict):
            payload = {"uniID": payload}
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("user/qr-code/deny", base_url), 
            method="POST", 
            json=payload, 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def login_qrcode_generate(
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def login_qrcode_generate(
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def login_qrcode_generate(
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """产生二维码

        GET https://login.123pan.com/api/user/qr-code/generate
        """
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("user/qr-code/generate", base_url), 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def login_qrcode_result(
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def login_qrcode_result(
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def login_qrcode_result(
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取扫码结果

        GET https://login.123pan.com/api/user/qr-code/result

        .. note::
            返回值中有个 "loginStatus" 字段，值为数字，分别表示的意思为：

            - 0: 等待扫码
            - 1: 已扫码
            - 2: 已取消
            - 3: 已登录
            - 4: 已失效

        :payload:
            - uniID: str 💡 二维码 id
        """
        if not isinstance(payload, dict):
            payload = {"uniID": payload}
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("user/qr-code/result", base_url), 
            params=payload, 
            **request_kwargs, 
        )

    @overload
    @staticmethod
    def login_qrcode_scan(
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    @staticmethod
    def login_qrcode_scan(
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    @staticmethod
    def login_qrcode_scan(
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_LOGIN_BASE_URL, 
        request: None | Callable = None, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """更新扫码状态为：已扫码（loginStatus=1）

        POST https://login.123pan.com/api/user/qr-code/scan

        :payload:
            - uniID: str 💡 二维码 id
            - scanPlatform: int = 0 💡 扫码的平台代码，部分已知：4:微信 7:android
        """
        if not isinstance(payload, dict):
            payload = {"uniID": payload}
        payload.setdefault("scanPlatform", 0)
        request_kwargs.setdefault("parse", default_parse)
        if request is None:
            request = get_default_request()
            request_kwargs["async_"] = async_
        return request(
            url=complete_url("user/qr-code/scan", base_url), 
            method="POST", 
            json=payload, 
            **request_kwargs, 
        )

    @overload
    def logout(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def logout(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def logout(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """退出登录

        POST https://www.123pan.com/api/user/logout
        """
        return self.request(
            "user/logout", 
            "POST", 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    ########## Offline Download API ##########

    @overload
    def offline_task_abort(
        self, 
        payload: int | Iterable[int] | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def offline_task_abort(
        self, 
        payload: int | Iterable[int] | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def offline_task_abort(
        self, 
        payload: int | Iterable[int] | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """取消离线下载任务

        POST https://www.123pan.com/api/offline_download/task/abort

        :payload:
            - task_ids: list[int]   💡 任务 id 列表
            - is_abort: bool = True 💡 是否取消
            - all: bool = False     💡 是否全部
        """
        if isinstance(payload, int):
            payload = {"task_ids": [payload]}
        elif not isinstance(payload, dict):
            if not isinstance(payload, (list, tuple)):
                payload = tuple(payload)
            payload = {"task_ids": payload}
        payload = cast(dict, payload)
        payload.setdefault("is_abort", True)
        payload.setdefault("all", False)
        return self.request(
            "offline_download/task/abort", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def offline_task_delete(
        self, 
        payload: int | Iterable[int] | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def offline_task_delete(
        self, 
        payload: int | Iterable[int] | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def offline_task_delete(
        self, 
        payload: int | Iterable[int] | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """删除离线下载任务

        POST https://www.123pan.com/api/offline_download/task/delete

        :payload:
            - task_ids: list[int] 💡 任务 id 列表
            - status_arr: list[ 0 | 1 | 2 | 3 | 4 ] = [] 💡 状态列表：0:进行中 1:下载失败 2:下载成功 3:重试中
        """
        if isinstance(payload, int):
            payload = {"task_ids": [payload], "status_arr": []}
        elif not isinstance(payload, dict):
            if not isinstance(payload, (list, tuple)):
                payload = tuple(payload)
            payload = {"task_ids": payload, "status_arr": []}
        return self.request(
            "offline_download/task/delete", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def offline_task_list(
        self, 
        payload: dict | int | list[int] | tuple[int] = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def offline_task_list(
        self, 
        payload: dict | int | list[int] | tuple[int] = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def offline_task_list(
        self, 
        payload: dict | int | list[int] | tuple[int] = 1, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """离线下载任务列表

        POST https://www.123pan.com/api/offline_download/task/list

        :payload:
            - current_page: int = 1
            - page_size: 100
            - status_arr: list[ 0 | 1 | 2 | 3 | 4 ] = [0, 1, 2, 3, 4] 💡 状态列表：0:进行中 1:下载失败 2:下载成功 3:重试中 4:等待中
        """
        if isinstance(payload, int):
            payload = {"current_page": payload}
        elif isinstance(payload, (list, tuple)):
            payload = { "status_arr": payload}
        payload = {"current_page": 1, "page_size": 100, "status_arr": [0, 1, 2, 3, 4], **payload}
        return self.request(
            "offline_download/task/list", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def offline_task_resolve(
        self, 
        payload: str | Iterable[str] | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def offline_task_resolve(
        self, 
        payload: str | Iterable[str] | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def offline_task_resolve(
        self, 
        payload: str | Iterable[str] | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """解析下载链接

        POST https://www.123pan.com/api/v2/offline_download/task/resolve

        :payload:
            - urls: str = <default> 💡 下载链接，多个用 "\\n" 隔开（用于新建链接下载任务）
            - info_hash: str = <default> 💡 种子文件的 info_hash（用于新建BT任务）
        """
        if isinstance(payload, str):
            payload = {"urls": payload.strip("\n")}
        elif not isinstance(payload, dict):
            payload = {"urls": "\n".join(payload)}
        return self.request(
            "v2/offline_download/task/resolve", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def offline_task_status(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def offline_task_status(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def offline_task_status(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """离线下载速度等信息

        POST https://www.123pan.com/api/offline_download/task/status
        """
        return self.request(
            "offline_download/task/status", 
            "POST", 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def offline_task_submit(
        self, 
        payload: dict | Iterable[dict], 
        /, 
        upload_dir: None | int | str = None, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def offline_task_submit(
        self, 
        payload: dict | Iterable[dict], 
        /, 
        upload_dir: None | int | str = None, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def offline_task_submit(
        self, 
        payload: dict | Iterable[dict], 
        /, 
        upload_dir: None | int | str = None, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """提交离线下载任务

        POST https://www.123pan.com/api/v2/offline_download/task/submit

        .. note::
            提交信息来自 ``client.offline_task_resolve()`` 接口的响应，假设响应为 ``resp``，那么

            .. code:: python

                payload = {
                    "resource_list": [{
                        "resource_id": resource["id"], 
                        "select_file_id": [info["id"] for info in resource["files"]], 
                    } for resource in resp["data"]["list"]]
                }

        :payload:
            - resource_list: list[Task] 💡 资源列表

                .. code:: python

                    File = {
                        "resource_id": int,          # 资源 id
                        "select_file_id": list[int], # 此资源内的文件 id
                    }

            - upload_dir: int 💡 保存到目录的 id
        """
        if not isinstance(payload, dict):
            payload = {
                "resource_list": [{
                    "resource_id": resource["id"], 
                    "select_file_id": [info["id"] for info in resource["files"]], 
                } for resource in payload]
            }
        payload = cast(dict, payload)
        if upload_dir is not None:
            payload["upload_dir"] = upload_dir
        return self.request(
            "v2/offline_download/task/submit", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def offline_task_upload_seed(
        self, 
        /, 
        file: Buffer | SupportsRead[Buffer] | Iterable[Buffer], 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def offline_task_upload_seed(
        self, 
        /, 
        file: Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer], 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def offline_task_upload_seed(
        self, 
        /, 
        file: Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer], 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """上传种子，以作解析

        POST https://www.123pan.com/api/offline_download/upload/seed
        """
        return self.request(
            "offline_download/upload/seed", 
            "POST", 
            files={"upload-torrent": file}, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def offline_add(
        self, 
        /, 
        url: str | Iterable[str], 
        upload_dir: None | int | str = None, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def offline_add(
        self, 
        /, 
        url: str | Iterable[str], 
        upload_dir: None | int | str = None, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def offline_add(
        self, 
        /, 
        url: str | Iterable[str], 
        upload_dir: None | int | str = None, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """添加离线下载任务

        POST https://www.123pan.com/api/offline_download/upload/seed

        :param url: info_hash（只允许单个）、下载链接（多个用 "\n" 分隔）或者多个下载链接的迭代器
        :param upload_dir: 保存到目录的 id
        :param base_url: API 链接的基地址
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应信息
        """
        def gen_step():
            if isinstance(url, str):
                if len(url) == 40 and not url.strip(hexdigits):
                    payload: dict = {"info_hash": url}
                else:
                    payload = {"urls": url}
            else:
                payload = {"urls": "\n".join(url)}
            resp = yield self.offline_task_resolve(
                payload, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
            check_response(resp)
            return self.offline_task_submit(
                resp["data"]["list"], 
                upload_dir, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
        return run_gen_step(gen_step, async_)

    ########## Share API ##########

    @overload
    def share_cancel(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_cancel(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_cancel(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """取消分享

        POST https://www.123pan.com/api/share/delete

        :payload:
            - shareInfoList: list[ShareID] 💡 信息可以取自 ``P123Client.fs_info`` 接口

                .. code:: python

                    ShareID = { 
                        "shareId": int | str, 
                    }

            - driveId: int = 0
            - event: str = "shareCancel" 💡 事件类型
            - isPayShare: bool = False 💡 是否付费分享
        """
        if isinstance(payload, (int, str)):
            payload = {"shareInfoList": [{"shareId": payload}]}
        elif not isinstance(payload, dict):
            payload = {"shareInfoList": [{"shareId": sid} for sid in payload]}
        payload = dict_key_to_lower_merge(payload, {
            "driveId": 0, 
            "event": "shareCancel", 
            "isPayShare": False, 
        })
        return self.request(
            "share/delete", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def share_clear(
        self, 
        payload: dict = {"event": "shareClear"}, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_clear(
        self, 
        payload: dict = {"event": "shareClear"}, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_clear(
        self, 
        payload: dict = {"event": "shareClear"}, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """清理全部失效链接

        GET https://www.123pan.com/api/share/clean_expire

        :payload:
            - event: str = "shareClear"
        """
        return self.request(
            "share/clean_expire", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def share_commission_set(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        amount: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_commission_set(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        amount: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_commission_set(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        amount: int = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """分佣设置

        POST https://www.123pan.com/api/share/update

        :payload:
            - shareIds: int | str 💡 分享 id，多个用 "," 隔开
            - noLoginStdAmount: int = 0  💡 文件体积单价（如果为 0 则是关闭），单位：1 分钱
        """
        if isinstance(payload, (int, str)):
            payload = {"shareIds": payload}
        elif not isinstance(payload, dict):
            payload = {"ids": ",".join(map(str, payload))}
        payload = cast(dict, payload)
        payload.setdefault("noLoginStdAmount", amount)
        return self.request(
            "share/update", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def share_create(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_create(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_create(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """创建分享

        POST https://www.123pan.com/api/share/create

        :payload:
            - fileIdList: int | str 💡 文件或目录的 id，多个用逗号 "," 分隔
            - displayStatus: int = 2     💡 默认展示：1:平铺 2:列表
            - driveId: int = 0
            - event: str = "shareCreate" 💡 事件类型
            - expiration: "9999-12-31T23:59:59+08:00" 💡 有效期，日期用 ISO 格式
            - fileNum: int = <default>   💡 文件数
            - fillPwdSwitch: 0 | 1 = 1   💡 是否自动填充提取码
            - isPayShare: bool = False   💡 是否付费分享
            - isReward: 0 | 1 = 0        💡 是否开启打赏
            - payAmount: int = 0         💡 付费金额，单位：分
            - renameVisible: bool = False
            - resourceDesc: str = ""     💡 资源描述
            - shareModality: int = <default>
            - shareName: str = <default> 💡 分享名称
            - sharePwd: str = ""         💡 提取码（不区分大小写）
            - trafficLimit: int = 0      💡 流量限制额度，单位字节
            - trafficLimitSwitch: 1 | 2 = 1 💡 是否开启流量限制：1:关闭 2:开启
            - trafficSwitch: 1 | 2 | 3 | 4 = <default> 💡 免登录流量包开关

                - 1: 游客免登录提取（关） 超流量用户提取（关）
                - 2: 游客免登录提取（开） 超流量用户提取（关）
                - 3: 游客免登录提取（关） 超流量用户提取（开）
                - 4: 游客免登录提取（开） 超流量用户提取（开）
        """
        if isinstance(payload, (int, str)):
            payload = {"fileIdList": payload}
        elif not isinstance(payload, dict):
            payload = {"fileIdList": ",".join(map(str, payload))}
        payload = dict_key_to_lower_merge(payload, {
            "displayStatus": 2, 
            "driveId": 0, 
            "event": "shareCreate", 
            "expiration": "9999-12-31T23:59:59+08:00", 
            "fillPwdSwitch": 1, 
            "isPayShare": False, 
            "isReward": 0, 
            "payAmount": 0, 
            "renameVisible": False, 
            "resourceDesc": "", 
            "sharePwd": "", 
            "trafficLimit": 0, 
            "trafficLimitSwitch": 1, 
            "trafficSwitch": 1, 
        })
        if "fileidlist" not in payload:
            raise ValueError("missing field: 'fileIdList'")
        if "sharename" not in payload:
            payload["sharename"] = "%d 个文件或目录" % (str(payload["fileidlist"]).count(",") + 1)
        return self.request(
            "share/create", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def share_download_info(
        self: None | dict | P123Client = None, 
        payload: None | dict = None, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_download_info(
        self: None | dict | P123Client = None, 
        payload: None | dict = None, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_download_info(
        self: None | dict | P123Client = None, 
        payload: None | dict = None, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取分享中的下载信息

        POST https://www.123pan.com/api/share/download/info

        .. note::
            可以作为 staticmethod 使用，此时第 1 个位置参数要传入 None 或者 dict

            如果文件在 100MB 以内，下载时是不需要登录的；如果超过 100 MB，但分享者设置的免登录流量包未告罄，下载时也不需要登录

            你也可以使用 ``P123Client.download_info`` 来获取下载链接，则不需要提供 "ShareKey" 和 "SharePwd"

        :payload:
            - ShareKey: str 💡 分享码
            - SharePwd: str = <default> 💡 提取码（不区分大小写）
            - Etag: str
            - S3KeyFlag: str
            - FileID: int | str
            - Size: int = <default>
            - ...
        """
        if isinstance(self, dict):
            payload = self
            self = None
        assert payload is not None
        update_headers_in_kwargs(request_kwargs, platform="android")
        api = complete_url("share/download/info", base_url)
        if self is None:
            request_kwargs.setdefault("parse", default_parse)
            request = request_kwargs.pop("request", None)
            if request is None:
                request = get_default_request()
                request_kwargs["async_"] = async_
            return request(url=api, method="POST", json=payload, **request_kwargs)
        else:
            return self.request(
                api, 
                "POST", 
                json=payload, 
                async_=async_, 
                **request_kwargs, 
            )

    @overload
    def share_download_info_batch(
        self: None | dict | P123Client = None, 
        payload: None | dict = None, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_download_info_batch(
        self: None | dict | P123Client = None, 
        payload: None | dict = None, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_download_info_batch(
        self: None | dict | P123Client = None, 
        payload: None | dict = None, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取分享中的批量下载信息

        POST https://www.123pan.com/api/file/batch_download_share_info

        .. note::
            可以作为 staticmethod 使用，此时第 1 个位置参数要传入 None 或者 dict

        :payload:
            - ShareKey: str 💡 分享码
            - SharePwd: str = <default> 💡 提取码（不区分大小写）
            - fileIdList: list[FileID]

                .. code:: python

                    FileID = {
                        "FileId": int | str
                    }
        """
        if isinstance(self, dict):
            payload = self
            self = None
        assert payload is not None
        api = complete_url("file/batch_download_share_info", base_url)
        if self is None:
            request_kwargs.setdefault("parse", default_parse)
            request = request_kwargs.pop("request", None)
            if request is None:
                request = get_default_request()
                request_kwargs["async_"] = async_
            return request(url=api, method="POST", json=payload, **request_kwargs)
        else:
            return self.request(
                api, 
                "POST", 
                json=payload, 
                async_=async_, 
                **request_kwargs, 
            )

    @overload
    def share_fs_copy(
        self, 
        payload: dict, 
        /, 
        parent_id: None | int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_fs_copy(
        self, 
        payload: dict, 
        /, 
        parent_id: None | int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_fs_copy(
        self, 
        payload: dict, 
        /, 
        parent_id: None | int | str = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """转存

        POST https://www.123pan.com/api/file/copy/async

        .. caution::
            这个函数的字段名，使用 snake case，而不是 camel case

        :payload:
            - share_key: str 💡 分享码
            - share_pwd: str = <default> 💡 密码，如果没有就不用传
            - current_level: int = 1
            - event: str = "transfer"
            - file_list: list[File]

                .. code:: python

                    File = {
                        "file_id": int | str, 
                        "file_name": str, 
                        "etag": str, 
                        "parent_file_id": int | str = 0, 
                        "drive_id": int | str = 0, 
                        ...
                    }
        """
        def to_snake_case(
            payload: dict[str, Any], 
            /, 
            *, 
            _map = {
                "sharekey": "share_key", 
                "sharepwd": "share_pwd", 
                "filelist": "file_list", 
                "fileid": "file_id", 
                "filename": "file_name", 
                "parentfileid": "parent_file_id", 
                "driveid": "drive_id", 
                "currentlevel": "current_level", 
            }.get, 
            _sub = re_compile("(?<!^)[A-Z]").sub, 
        ):
            d: dict[str, Any] = {}
            for k, v in payload.items():
                if "_" in k:
                    d[k.lower()] = v
                elif k2 := _map(k.lower()):
                    d[k2] = v
                elif (k2 := _sub(r"_\g<0>", k)) != k:
                    d[k2.lower()] = v
                else:
                    d[k] = v
            if "file_list" in d:
                ls = d["file_list"]
                for i, d2 in enumerate(ls):
                    ls[i] = {"drive_id": 0, **to_snake_case(d2)}
                    if parent_id is not None:
                        ls[i]["parent_file_id"] = parent_id
            return d
        payload = {"current_level": 1, "event": "transfer", **to_snake_case(payload)}
        return self.request(
            "file/copy/async", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def share_fs_list(
        self: None | dict | P123Client = None, 
        payload: None | dict = None, 
        /, 
        request: None | Callable = None, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_fs_list(
        self: None | dict | P123Client = None, 
        payload: None | dict = None, 
        /, 
        request: None | Callable = None, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_fs_list(
        self: None | dict | P123Client = None, 
        payload: None | dict = None, 
        /, 
        request: None | Callable = None, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取分享中的文件列表

        GET https://www.123pan.com/api/share/get

        .. note::
            如果返回信息中，"Next" 字段的值为 "-1"，代表最后一页（无需再翻页查询）

        .. note::
            有个 Bug，如果 ``parentFileId`` 是你网盘中的某个目录的 id，则总是能拉取到，即便不在此分享中       

        :payload:
            - ShareKey: str 💡 分享码
            - SharePwd: str = <default> 💡 提取码（不区分大小写）
            - limit: int = 100 💡 分页大小，最多 100 个
            - next: int = 0    💡 下一批拉取开始的 id（⚠️ 不可用）
            - orderBy: str = "file_name" 💡 排序依据

                - "file_name": 文件名
                - "size":  文件大小
                - "create_at": 创建时间
                - "update_at": 创建时间
                - "update_time": 更新时间
                - ...（其它可能值）

            - orderDirection: "asc" | "desc" = "asc" 💡 排序顺序
            - Page: int = 1 💡 第几页，从 1 开始，可以是 0
            - parentFileId: int | str = 0 💡 父目录 id
            - event: str = "homeListFile" 💡 事件名称
            - operateType: int | str = <default> 💡 操作类型
        """
        if isinstance(self, dict):
            payload = self
            self = None
        assert payload is not None
        payload = dict_key_to_lower_merge(cast(dict, payload), {
            "limit": 100, 
            "next": 0, 
            "orderBy": "file_name", 
            "orderDirection": "asc", 
            "Page": 1, 
            "parentFileId": 0, 
            "event": "homeListFile", 
        })
        request_kwargs.setdefault("parse", default_parse)
        api = complete_url("share/get", base_url)
        if self is None:
            if request is None:
                request = get_default_request()
                request_kwargs["async_"] = async_
            return request(url=api, method="GET", params=payload, **request_kwargs)
        else:
            return self.request(
                api, 
                params=payload, 
                request=request, 
                async_=async_, 
                **request_kwargs, 
            )

    @overload # type: ignore
    def share_list(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "shareListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_list(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "shareListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_list(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "shareListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取免费分享列表（可搜索）

        GET https://www.123pan.com/api/share/list

        .. note::
            如果返回信息中，"Next" 字段的值为 "-1"，代表最后一页（无需再翻页查询）

        :payload:
            - driveId: int | str = 0
            - limit: int = 100 💡 分页大小，最多 100 个
            - next: int = 0    💡 下一批拉取开始的 id
            - orderBy: str = "fileId" 💡 排序依据："fileId", ...
            - orderDirection: "asc" | "desc" = "desc" 💡 排序顺序
            - Page: int = <default> 💡 第几页，从 1 开始，可以是 0
            - event: str = "shareListFile"
            - operateType: int | str = <default>
            - SearchData: str = <default> 💡 搜索关键字
        """
        if isinstance(payload, int):
            payload = {"Page": payload}
        payload = dict_key_to_lower_merge(payload, {
            "driveId": 0, 
            "limit": 100, 
            "next": 0, 
            "orderBy": "fileId", 
            "orderDirection": "desc", 
            "event": event, 
        })
        return self.request(
            "share/list", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def share_payment_list(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "shareListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_payment_list(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "shareListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_payment_list(
        self, 
        payload: dict | int = 1, 
        /, 
        event: str = "shareListFile", 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """获取付费分享列表（可搜索）

        GET https://www.123pan.com/api/restful/goapi/v1/share/content/payment/list

        .. note::
            如果返回信息中，"Next" 字段的值为 "-1"，代表最后一页（无需再翻页查询）

        :payload:
            - driveId: int | str = 0
            - limit: int = 100 💡 分页大小，最多 100 个
            - next: int = 0    💡 下一批拉取开始的 id
            - orderBy: str = "fileId" 💡 排序依据："fileId", ...
            - orderDirection: "asc" | "desc" = "desc" 💡 排序顺序
            - Page: int = <default> 💡 第几页，从 1 开始，可以是 0
            - event: str = "shareListFile"
            - operateType: int | str = <default>
            - SearchData: str = <default> 💡 搜索关键字
        """
        if isinstance(payload, int):
            payload = {"Page": payload}
        payload = dict_key_to_lower_merge(payload, {
            "driveId": 0, 
            "limit": 100, 
            "next": 0, 
            "orderBy": "fileId", 
            "orderDirection": "desc", 
            "event": event, 
        })
        return self.request(
            "restful/goapi/v1/share/content/payment/list", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def share_reward_set(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        is_reward: bool = False, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_reward_set(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        is_reward: bool = False, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_reward_set(
        self, 
        payload: dict | int | str | Iterable[int | str], 
        /, 
        is_reward: bool = False, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """开启或关闭打赏

        POST https://www.123pan.com/api/restful/goapi/v1/share/reward/status

        :payload:
            - ids: list[int | str] 💡 分享 id
            - isReward: 0 | 1 = 1  💡 是否开启打赏
        """
        if isinstance(payload, (int, str)):
            payload = {"ids": [payload]}
        elif not isinstance(payload, dict):
            payload = {"ids": list(payload)}
        payload = dict_key_to_lower_merge(payload, is_reward=int(is_reward))
        return self.request(
            "restful/goapi/v1/share/reward/status", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def share_traffic(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_traffic(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_traffic(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """分享提取流量包的信息

        GET https://www.123pan.com/api/share/traffic-info
        """
        return self.request(
            "share/traffic-info", 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def share_traffic_set(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_traffic_set(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_traffic_set(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """流量包设置

        PUT https://www.123pan.com/api/restful/goapi/v1/share/info

        :payload:
            - shareId: int | str
            - trafficLimit: int = <default>         💡 流量限制额度，单位字节
            - trafficLimitSwitch: 1 | 2 = <default> 💡 是否开启流量限制：1:关闭 2:开启
            - trafficSwitch: 1 | 2 | 3 | 4 = <default> 💡 免登录流量包开关

                - 1: 游客免登录提取（关） 超流量用户提取（关）
                - 2: 游客免登录提取（开） 超流量用户提取（关）
                - 3: 游客免登录提取（关） 超流量用户提取（开）
                - 4: 游客免登录提取（开） 超流量用户提取（开）
        """
        return self.request(
            "restful/goapi/v1/share/info", 
            "PUT", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def share_update(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def share_update(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def share_update(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """编辑分享

        PUT https://www.123pan.com/api/restful/goapi/v1/share/update

        :payload:
            - shareId: int 💡 分享 id
            - shareName: str = <default> 💡 分享名称
            - expiration: str = <default> 💡 过期时间
            - trafficLimit: int = <default> 💡 免登陆限制流量，单位：字节
            - trafficLimitSwitch: 1 | 2 = <default> 💡 免登录流量限制开关：1:关闭 2:打开
            - trafficSwitch: 1 | 2 | 3 | 4 = <default> 💡 免登录流量包开关

                - 1: 游客免登录提取（关） 超流量用户提取（关）
                - 2: 游客免登录提取（开） 超流量用户提取（关）
                - 3: 游客免登录提取（关） 超流量用户提取（开）
                - 4: 游客免登录提取（开） 超流量用户提取（开）
        """
        return self.request(
            "restful/goapi/v1/share/update", 
            "PUT", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    ########## Upload API ##########

    @overload
    def upload_auth(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_auth(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_auth(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """认证上传信息，获取上传链接

        POST https://www.123pan.com/api/file/s3_upload_object/auth

        .. note::
            只能获取 1 个上传链接，用于非分块上传

        :payload:
            - bucket: str
            - key: str
            - storageNode: str
            - uploadId: str
        """
        return self.request(
            "file/s3_upload_object/auth", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload # type: ignore
    def upload_complete(
        self, 
        payload: dict, 
        /, 
        is_multipart: bool = False, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_complete(
        self, 
        payload: dict, 
        /, 
        is_multipart: bool = False, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_complete(
        self, 
        payload: dict, 
        /, 
        is_multipart: bool = False, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """完成上传

        POST https://www.123pan.com/api/file/upload_complete/v2

        :payload:
            - FileId: int 💡 文件 id
            - bucket: str 💡 存储桶
            - key: str
            - storageNode: str
            - uploadId: str
            - isMultipart: bool = True 💡 是否分块上传
        """
        payload = dict_key_to_lower_merge(payload, isMultipart=is_multipart)
        return self.request(
            "file/upload_complete/v2", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def upload_prepare(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_prepare(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_prepare(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """认证上传信息，获取上传链接

        POST https://www.123pan.com/api/file/s3_repare_upload_parts_batch

        .. note::
            一次可获取 `partNumberEnd - partNumberStart` 个上传链接，用于分块上传

        :payload:
            - bucket: str
            - key: str
            - storageNode: str
            - uploadId: str
            - partNumberStart: int = 1 💡 开始的分块编号（从 0 开始编号）
            - partNumberEnd: int = <default> 💡 结束的分块编号（不含）
        """
        if "partNumberStart" not in payload:
            payload["partNumberStart"] = 1
        if "partNumberEnd" not in payload:
            payload["partNumberEnd"] = int(payload["partNumberStart"]) + 1
        return self.request(
            "file/s3_repare_upload_parts_batch", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload # type: ignore
    def upload_list(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_list(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_list(
        self, 
        payload: dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """罗列已经上传的分块

        POST https://www.123pan.com/api/file/s3_list_upload_parts

        :payload:
            - bucket: str
            - key: str
            - storageNode: str
            - uploadId: str
        """
        return self.request(
            "file/s3_list_upload_parts", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def upload_request(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_request(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_request(
        self, 
        payload: str | dict, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """请求上传，获取一些初始化信息

        POST https://www.123pan.com/api/file/upload_request

        .. note::
            当响应信息里面有 "Reuse" 的值为 "true"，说明已经存在目录或者文件秒传

        :payload:
            - fileName: str 💡 文件或目录的名字
            - driveId: int | str = 0
            - duplicate: 0 | 1 | 2 = 0 💡 处理同名：0: 提示/忽略 1: 保留两者 2: 替换
            - etag: str = "" 💡 文件的 MD5 散列值
            - parentFileId: int | str = 0 💡 父目录 id
            - size: int = 0 💡 文件大小，单位：字节
            - type: 0 | 1 = 1 💡 类型，如果是目录则是 1，如果是文件则是 0
            - NotReuse: bool = False 💡 不要重用（仅在 `type=1` 时有效，如果为 False，当有重名时，立即返回，此时 ``duplicate`` 字段无效）
            - ...
        """
        if isinstance(payload, str):
            payload = {"fileName": payload}
        payload = dict_key_to_lower_merge(payload, {
            "driveId": 0, 
            "duplicate": 0, 
            "etag": "", 
            "parentFileId": 0,
            "size": 0, 
            "type": 1, 
            "NotReuse": False, 
        })
        if payload["size"] or payload["etag"]:
            payload["type"] = 0
        return self.request(
            "file/upload_request", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    # TODO: 支持断点续传，也就是传入复传信息
    # TODO: 支持如果文件未曾打开，则可等尝试秒传失败之后，再行打开（因为如果能秒传，则根本不必打开）
    @overload # type: ignore
    def upload_file(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] ), 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_file(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer] ), 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_file(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer] ), 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """上传文件

        .. note::
            如果文件名中包含字符 ``"\\/:*?|><``，则转换为对应的全角字符

        :param file: 待上传的文件

            - 如果为 ``collections.abc.Buffer``，则作为二进制数据上传
            - 如果为 ``filewrap.SupportsRead``，则作为可读的二进制文件上传
            - 如果为 ``str`` 或 ``os.PathLike``，则视为路径，打开后作为文件上传
            - 如果为 ``yarl.URL`` 或 ``http_request.SupportsGeturl`` (``pip install python-http_request``)，则视为超链接，打开后作为文件上传
            - 如果为 ``collections.abc.Iterable[collections.abc.Buffer]`` 或 ``collections.abc.AsyncIterable[collections.abc.Buffer]``，则迭代以获取二进制数据，逐步上传

        :param file_md5: 文件的 MD5 散列值
        :param file_name: 文件名
        :param file_size: 文件大小
        :param parent_id: 要上传的目标目录
        :param duplicate: 处理同名：0: 提示/忽略 1: 保留两者 2: 替换
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应
        """ 
        def gen_step():
            nonlocal file, file_md5, file_name, file_size
            def do_upload(file):
                return self.upload_file(
                    file=file, 
                    file_md5=file_md5, 
                    file_name=file_name, 
                    file_size=file_size, 
                    parent_id=parent_id, 
                    duplicate=duplicate, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
            try:
                file = getattr(file, "getbuffer")()
            except (AttributeError, TypeError):
                pass
            if isinstance(file, Buffer):
                file_size = buffer_length(file)
                if not file_md5:
                    file_md5 = md5(file).hexdigest()
            elif isinstance(file, (str, PathLike)):
                path = fsdecode(file)
                if not file_name:
                    file_name = basename(path)
                return do_upload(open(path, "rb"))
            elif isinstance(file, SupportsRead):
                seek = getattr(file, "seek", None)
                seekable = False
                curpos = 0
                if callable(seek):
                    if async_:
                        seek = ensure_async(seek, threaded=True)
                    try:
                        seekable = getattr(file, "seekable")()
                    except (AttributeError, TypeError):
                        try:
                            curpos = yield seek(0, 1)
                            seekable = True
                        except Exception:
                            seekable = False
                if not file_md5:
                    if not seekable:
                        fsrc = file
                        file = TemporaryFile()
                        if async_:
                            yield copyfileobj_async(fsrc, file)
                        else:
                            copyfileobj(fsrc, file)
                        file.seek(0)
                        return do_upload(file)
                    try:
                        if async_:
                            file_size, hashobj = yield file_digest_async(file)
                        else:
                            file_size, hashobj = file_digest(file)
                    finally:
                        yield cast(Callable, seek)(curpos)
                    file_md5 = hashobj.hexdigest()
                if file_size < 0:
                    try:
                        fileno = getattr(file, "fileno")()
                        file_size = fstat(fileno).st_size - curpos
                    except (AttributeError, TypeError, OSError):
                        try:
                            file_size = len(file) - curpos # type: ignore
                        except TypeError:
                            if seekable:
                                try:
                                    file_size = (yield cast(Callable, seek)(0, 2)) - curpos
                                finally:
                                    yield cast(Callable, seek)(curpos)
            elif isinstance(file, (URL, SupportsGeturl)):
                if isinstance(file, URL):
                    url = str(file)
                else:
                    url = file.geturl()
                if async_:
                    from httpfile import AsyncHttpxFileReader
                    async def request():
                        file = await AsyncHttpxFileReader.new(url)
                        async with file:
                            return await do_upload(file)
                    return request()
                else:
                    from httpfile import HTTPFileReader
                    with HTTPFileReader(url) as file:
                        return do_upload(file)
            elif not file_md5 or file_size < 0:
                if async_:
                    file = bytes_iter_to_async_reader(file) # type: ignore
                else:
                    file = bytes_iter_to_reader(file) # type: ignore
                return do_upload(file)
            if not file_name:
                file_name = getattr(file, "name", "")
                file_name = basename(file_name)
            if file_name:
                file_name = escape_filename(file_name)
            else:
                file_name = str(uuid4())
            if file_size < 0:
                file_size = getattr(file, "length", 0)
            resp = yield self.upload_request(
                {
                    "etag": file_md5, 
                    "fileName": file_name, 
                    "size": file_size, 
                    "parentFileId": parent_id, 
                    "type": 0, 
                    "duplicate": duplicate, 
                }, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
            if resp.get("code", 0) not in (0, 200):
                return resp
            upload_data = resp["data"]
            if upload_data["Reuse"]:
                return resp
            slice_size = int(upload_data["SliceSize"])
            upload_request_kwargs = {
                **request_kwargs, 
                "method": "PUT", 
                "headers": {"authorization": ""}, 
                "parse": ..., 
            }
            if file_size > slice_size:
                if async_:
                    async def request():
                        chunks = bio_chunk_async_iter(file, chunksize=slice_size) # type: ignore
                        slice_no = 1
                        async for chunk in chunks:
                            upload_data["partNumberStart"] = slice_no
                            upload_data["partNumberEnd"]   = slice_no + 1
                            resp = await self.upload_prepare(
                                upload_data, 
                                base_url=base_url, 
                                async_=True, 
                                **request_kwargs, 
                            )
                            check_response(resp)
                            await self.request(
                                resp["data"]["presignedUrls"][str(slice_no)], 
                                data=chunk, 
                                async_=True, 
                                **upload_request_kwargs, 
                            )
                            slice_no += 1
                    yield request()
                else:
                    chunks = bio_chunk_iter(file, chunksize=slice_size) # type: ignore
                    for slice_no, chunk in enumerate(chunks, 1):
                        upload_data["partNumberStart"] = slice_no
                        upload_data["partNumberEnd"]   = slice_no + 1
                        resp = self.upload_prepare(
                            upload_data, 
                            base_url=base_url, 
                            **request_kwargs, 
                        )
                        check_response(resp)
                        self.request(
                            resp["data"]["presignedUrls"][str(slice_no)], 
                            data=chunk, 
                            **upload_request_kwargs, 
                        )
            else:
                resp = yield self.upload_auth(
                    upload_data, 
                    base_url=base_url, 
                    async_=async_, 
                    **request_kwargs, 
                )
                check_response(resp)
                yield self.request(
                    resp["data"]["presignedUrls"]["1"], 
                    data=file, 
                    async_=async_, 
                    **upload_request_kwargs, 
                )
            upload_data["isMultipart"] = file_size > slice_size
            return self.upload_complete(
                upload_data, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
        return run_gen_step(gen_step, async_)

    @overload
    def upload_file_fast(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] ) = b"", 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def upload_file_fast(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer] ) = b"", 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def upload_file_fast(
        self, 
        /, 
        file: ( str | PathLike | URL | SupportsGeturl | 
                Buffer | SupportsRead[Buffer] | Iterable[Buffer] | AsyncIterable[Buffer] ) = b"", 
        file_md5: str = "", 
        file_name: str = "", 
        file_size: int = -1, 
        parent_id: int | str = 0, 
        duplicate: Literal[0, 1, 2] = 0, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """尝试秒传文件，如果失败也直接返回

        :param file: 待上传的文件

            - 如果为 ``collections.abc.Buffer``，则作为二进制数据上传
            - 如果为 ``filewrap.SupportsRead``，则作为可读的二进制文件上传
            - 如果为 ``str`` 或 ``os.PathLike``，则视为路径，打开后作为文件上传
            - 如果为 ``yarl.URL`` 或 ``http_request.SupportsGeturl`` (``pip install python-http_request``)，则视为超链接，打开后作为文件上传
            - 如果为 ``collections.abc.Iterable[collections.abc.Buffer]`` 或 ``collections.abc.AsyncIterable[collections.abc.Buffer]``，则迭代以获取二进制数据，逐步上传

        :param file_md5: 文件的 MD5 散列值
        :param file_name: 文件名
        :param file_size: 文件大小
        :param parent_id: 要上传的目标目录
        :param duplicate: 处理同名：0: 提示/忽略 1: 保留两者 2: 替换
        :param async_: 是否异步
        :param request_kwargs: 其它请求参数

        :return: 接口响应
        """ 
        def gen_step():
            nonlocal file, file_md5, file_name, file_size
            if file_md5 and file_size >= 0:
                pass
            elif file:
                def do_upload(file):
                    return self.upload_file_fast(
                        file=file, 
                        file_md5=file_md5, 
                        file_name=file_name, 
                        file_size=file_size, 
                        parent_id=parent_id, 
                        duplicate=duplicate, 
                        base_url=base_url, 
                        async_=async_, 
                        **request_kwargs, 
                    )
                try:
                    file = getattr(file, "getbuffer")()
                except (AttributeError, TypeError):
                    pass
                if isinstance(file, Buffer):
                    file_size = buffer_length(file)
                    if not file_md5:
                        file_md5 = md5(file).hexdigest()
                elif isinstance(file, (str, PathLike)):
                    path = fsdecode(file)
                    if not file_name:
                        file_name = basename(path)
                    return do_upload(open(path, "rb"))
                elif isinstance(file, SupportsRead):
                    if not file_md5 or file_size < 0:
                        if async_:
                            file_size, hashobj = yield file_digest_async(file)
                        else:
                            file_size, hashobj = file_digest(file)
                        file_md5 = hashobj.hexdigest()
                elif isinstance(file, (URL, SupportsGeturl)):
                    if isinstance(file, URL):
                        url = str(file)
                    else:
                        url = file.geturl()
                    if async_:
                        from httpfile import AsyncHttpxFileReader
                        async def request():
                            file = await AsyncHttpxFileReader.new(url)
                            async with file:
                                return await do_upload(file)
                        return request()
                    else:
                        from httpfile import HTTPFileReader
                        with HTTPFileReader(url) as file:
                            return do_upload(file)
                elif not file_md5 or file_size < 0:
                    if async_:
                        file = bytes_iter_to_async_reader(file) # type: ignore
                    else:
                        file = bytes_iter_to_reader(file) # type: ignore
                    return do_upload(file)
            else:
                file_md5 = "d41d8cd98f00b204e9800998ecf8427e"
                file_size = 0
            if not file_name:
                file_name = getattr(file, "name", "")
                file_name = basename(file_name)
            if file_name:
                file_name = escape_filename(file_name)
            if not file_name:
                file_name = str(uuid4())
            if file_size < 0:
                file_size = getattr(file, "length", 0)
            return self.upload_request(
                {
                    "etag": file_md5, 
                    "fileName": file_name, 
                    "size": file_size, 
                    "parentFileId": parent_id, 
                    "type": 0, 
                    "duplicate": duplicate, 
                }, 
                base_url=base_url, 
                async_=async_, 
                **request_kwargs, 
            )
        return run_gen_step(gen_step, async_)

    ########## User API ##########

    @overload
    def user_device_list(
        self, 
        payload: dict | str = "deviceManagement", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def user_device_list(
        self, 
        payload: dict | str = "deviceManagement", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def user_device_list(
        self, 
        payload: dict | str = "deviceManagement", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """用户设备列表

        GET https://www.123pan.com/api/user/device_list

        :payload:
            - event: str = "deviceManagement" 💡 事件类型，"deviceManagement" 为管理登录设备列表
            - operateType: int = <default>
        """
        if not isinstance(payload, dict):
            payload = {"event": payload}
        return self.request(
            "user/device_list", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def user_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def user_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def user_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """用户信息

        GET https://www.123pan.com/api/user/info
        """
        return self.request(
            "user/info", 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def user_modify_info(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def user_modify_info(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def user_modify_info(
        self, 
        payload: dict | str, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """修改用户信息，默认行为是 修改用户昵称

        POST https://www.123pan.com/api/user/modify_info

        :payload:
            - event: str 💡 事件类型
            - nickname: str = <default> 💡 用户昵称
            - operateType: int = <default>
            - ...
        """
        if not isinstance(payload, dict):
            payload = {"nickname": payload, "event": "userDataOperate", "operateType": 2}
        return self.request(
            "user/modify_info", 
            "POST", 
            json=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def user_referral_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def user_referral_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def user_referral_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """用户拉新返佣信息

        GET https://www.123pan.com/api/referral/my-info
        """
        return self.request(
            "referral/my-info", 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def user_report_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def user_report_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def user_report_info(
        self, 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """用户推送消息配置

        GET https://www.123pan.com/b/api/restful/goapi/v1/user/report/info
        """
        return self.request(
            "restful/goapi/v1/user/report/info", 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def user_use_history(
        self, 
        payload: dict | str = "loginRecord", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def user_use_history(
        self, 
        payload: dict | str = "loginRecord", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def user_use_history(
        self, 
        payload: dict | str = "loginRecord", 
        /, 
        base_url: str | Callable[[], str] = DEFAULT_BASE_URL, 
        *, 
        async_: Literal[False, True] = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        """用户使用记录

        GET https://www.123pan.com/api/user/use_history

        :payload:
            - event: str = "loginRecord" 💡 事件类型，"loginRecord" 为登录记录
        """
        if not isinstance(payload, dict):
            payload = {"event": payload}
        return self.request(
            "user/use_history", 
            params=payload, 
            base_url=base_url, 
            async_=async_, 
            **request_kwargs, 
        )


with temp_globals():
    CRE_CLIENT_API_search: Final = re_compile(r"^ +((?:GET|POST|PUT|DELETE|PATCH) .*)", MULTILINE).search
    for name in dir(P123Client):
        method = getattr(P123Client, name)
        if not (callable(method) and method.__doc__):
            continue
        match = CRE_CLIENT_API_search(method.__doc__)
        if match is not None:
            api = match[1]
            name = "P123Client." + name
            CLIENT_METHOD_API_MAP[name] = api
            try:
                CLIENT_API_METHODS_MAP[api].append(name)
            except KeyError:
                CLIENT_API_METHODS_MAP[api] = [name]


# TODO: upload_file 目前断点续传有些问题
# TODO: upload_file 需要极度简化，并且整合几种上传接口
# TODO: 所有静态方法都进行处理，支持静态和实例两种调用方式
