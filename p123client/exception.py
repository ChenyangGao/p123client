#!/usr/bin/env python3
# encoding: utf-8

__all__ = [
    "P123Warning", "P123OSError", "P123BrokenUpload", 
    "P123AccessTokenError", "P123AuthenticationError", 
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


class P123BrokenUpload(P123OSError):
    pass


class P123AccessTokenError(P123OSError):
    pass


class P123AuthenticationError(P123OSError):
    pass

