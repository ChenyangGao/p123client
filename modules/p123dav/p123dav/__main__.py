#!/usr/bin/env python3
# encoding: utf-8

__author__ = "ChenyangGao <https://chenyanggao.github.io>"

from argparse import ArgumentParser, Namespace, RawTextHelpFormatter

parser = ArgumentParser(
    description="  📺 123 WebDav 🎬", 
    formatter_class=RawTextHelpFormatter, 
    epilog="""\
✈️ 关于登录

登录时，可以选择其一：
    1. 账号和密码，或 client_id 和 client_secret（-u/--user 和 -p/--password）
    2. 访问令牌（-t/--token）

🔨 关于使用

当你访问首页时，会罗列你的网盘入口（路径为 /0）和所有分享入口（路径为 /分享码 或 /分享码:密码）

    http://localhost:8123/

当你访问这个链接路径之下，就是你自己网盘的文件

    http://localhost:8123/0/网盘下的路径

当你访问这个路径之下，则是这个分享下的文件

    http://localhost:8123/分享码/分享下的路径
    http://localhost:8123/分享码:密码/分享下的路径

你可以随意指定一个有效的分享码和路径，而不用管这个分享是不是你自己创建的
""")
parser.add_argument("-u", "--username", default="", help="登录账号，手机号或邮箱，或者 client_id")
parser.add_argument("-p", "--password", default="", help="登录密码，或者 client_secret")
parser.add_argument("-t", "--token", help="123 网盘的 access_token")
parser.add_argument("--ttl", type=float, default=10, help="文件列表缓存时间，默认值：10，单位：秒")
parser.add_argument("-r", "--refresh", action="store_true", help="更新文件列表缓存时，强制更新全部，如果不指定此参数，则会用一种预写的算法，尽量少地拉取数据以更新缓存（但可能出错）")
parser.add_argument("-H", "--host", default="0.0.0.0", help="ip 或 hostname，默认值：'0.0.0.0'")
parser.add_argument("-P", "--port", type=int, default=8123, help="端口号，默认值：8123")
parser.add_argument("-v", "--version", action="store_true", help="输出版本号")
parser.add_argument("-l", "--license", action="store_true", help="输出授权信息")


def parse_args(argv: None | list[str] = None, /) -> Namespace:
    args = parser.parse_args(argv)
    if args.version:
        from p123dav import __version__
        print(".".join(map(str, __version__)))
        raise SystemExit(0)
    elif args.license:
        from p123dav import __license__
        print(__license__)
        raise SystemExit(0)
    return args


def main(argv: None | list[str] | Namespace = None, /):
    if isinstance(argv, Namespace):
        args = argv
    else:
        args = parse_args(argv)

    from p123dav import P123FileSystemProvider

    davfs = P123FileSystemProvider(
        args.username, 
        args.password, 
        args.token, 
        ttl=args.ttl, 
        refresh=args.refresh, 
    )

    from wsgidav.wsgidav_app import WsgiDAVApp # type: ignore
    from wsgidav.server.server_cli import SUPPORTED_SERVERS # type: ignore

    config = {
        "server": "cheroot", 
        "host": args.host, 
        "port": args.port, 
        "mount_path": "", 
        "simple_dc": {"user_mapping": {"*": True}}, 
        "provider_mapping": {"/": davfs}, 
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


if __name__ == "__main__":
    from pathlib import Path
    from sys import path

    path[0] = str(Path(__file__).parents[1])
    main()

