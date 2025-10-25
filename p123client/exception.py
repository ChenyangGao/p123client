#!/usr/bin/env python3
# encoding: utf-8

__all__ = [
    "P123Warning", "P123OSError", "P123AuthenticationError", "P123AccessTokenError", 
    "P123BrokenUpload", "P123DataError", "P123LoginError", "P123NotSupportedError", 
    "P123OperationalError", "P123FileExistsError", "P123FileNotFoundError", 
    "P123IsADirectoryError", "P123NotADirectoryError", "P123PermissionError", 
    "P123TimeoutError", 
]

import warnings

from itertools import count
from collections.abc import Mapping
from functools import cached_property


warnings.filterwarnings("always", category=UserWarning)
warnings.filterwarnings("ignore", category=SyntaxWarning)
setattr(warnings, "formatwarning", lambda message, category, filename, lineno, line=None, _getid=count(1).__next__:
    f"\r\x1b[K\x1b[1;31;43m{category.__qualname__}\x1b[0m(\x1b[32m{_getid()}\x1b[0m) @ \x1b[3;4;34m{filename}\x1b[0m:\x1b[36m{lineno}\x1b[0m \x1b[5;31m➜\x1b[0m \x1b[1m{message}\x1b[0m\n"
)


class P123Warning(UserWarning):
    """本模块的最基础警示类
    """


class P123OSError(OSError):
    """本模块的最基础异常类
    """
    def __getattr__(self, attr, /):
        try:
            return self[attr]
        except KeyError as e:
            raise AttributeError(attr) from e

    def __getitem__(self, key, /):
        message = self.message
        if isinstance(message, Mapping):
            return message[key]
        raise KeyError(key)

    @cached_property
    def message(self, /):
        if args := self.args:
            if len(args) >= 2 and isinstance(args[0], int):
                return args[1]
            return args[0]


class P123AuthenticationError(P123OSError):
    """当登录状态无效时抛出
    """


class P123AccessTokenError(P123AuthenticationError):
    """access_token 错误或者无效
    """


class P123BrokenUpload(P123OSError):
    """当上传文件中被打断时抛出
    """


class P123DataError(P123OSError):
    """当响应数据解析失败时抛出
    """


class P123LoginError(P123AuthenticationError):
    """当登录失败时抛出
    """


class P123NotSupportedError(P123OSError):
    """当调用不存在的接口或者接口不支持此操作时抛出
    """


class P123OperationalError(P123OSError):
    """当接口使用方法错误时抛出，例如参数错误、空间不足、超出允许数量范围等
    """


class P123FileExistsError(P123OSError, FileExistsError):
    """扩展 FileExistsError，同时是 P123OSError 的子类
    """


class P123FileNotFoundError(P123OSError, FileNotFoundError):
    """扩展 FileNotFoundError，同时是 P123OSError 的子类
    """


class P123IsADirectoryError(P123OSError, IsADirectoryError):
    """扩展 IsADirectoryError，同时是 P123OSError 的子类
    """


class P123NotADirectoryError(P123OSError, NotADirectoryError):
    """扩展 NotADirectoryError，同时是 P123OSError 的子类
    """


class P123PermissionError(P123OSError, PermissionError):
    """扩展 PermissionError，同时是 P123OSError 的子类
    """


class P123TimeoutError(P123OSError, TimeoutError):
    """扩展 TimeoutError，同时是 P123OSError 的子类
    """

