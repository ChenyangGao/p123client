#!/usr/bin/env python3
# encoding: utf-8

__author__ = "ChenyangGao <https://chenyanggao.github.io>"
__version__ = (0, 0, 3)
__license__ = "GPLv3 <https://www.gnu.org/licenses/gpl-3.0.txt>"

__FALSE = False
if __FALSE:
    from .dav import *

def __getattr__(attr, /):
    from importlib import import_module

    dav = import_module('.dav', package=__package__)
    all = {"__all__": dav.__all__}
    for name in dav.__all__:
        all[name] = getattr(dav, name)
    globals().update(all)
    del globals()["__getattr__"]
    return getattr(dav, attr)
