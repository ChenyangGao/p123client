#!/usr/bin/env python3
# encoding: utf-8

__all__ = ["CLIENT_METHOD_API_MAP", "CLIENT_API_METHODS_MAP"]

from typing import Final


#: 所有已封装的方法名和对应的 123 接口
CLIENT_METHOD_API_MAP: Final[dict[str, str]] = {}

#: 所有已封装的 123 接口和对应的方法名
CLIENT_API_METHODS_MAP: Final[dict[str, list[str]]] = {}
