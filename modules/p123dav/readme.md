# 123 WebDAV

## 安装

你可以通过 [pypi](https://pypi.org/project/p123dav/) 安装

```console
pip install -U p123dav
```

## 用法

### 作为模块

```python
from p123client import P123Client
from p123dav import P123FileSystemProvider
from wsgidav.wsgidav_app import WsgiDAVApp
from wsgidav.server.server_cli import SUPPORTED_SERVERS

config = {
    "server": "cheroot", 
    "host": "0.0.0.0", 
    "port": 8123, 
    "mount_path": "", 
    "simple_dc": {"user_mapping": {"*": True}}, 
    "provider_mapping": {"/": P123FileSystemProvider(
        username="", 
        password="", 
        ttl=10, 
        refresh=False, 
    )}, 
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
handler(app, config, server)
```

### 作为命令

```console
usage: p123dav [-h] [-u USERNAME] [-p PASSWORD] [-t TOKEN] [--ttl TTL] [-r]
               [-H HOST] [-P PORT] [-v] [-l]

  📺 123 WebDav 🎬

options:
  -h, --help            show this help message and exit
  -u USERNAME, --username USERNAME
                        登录账号，手机号或邮箱，或者 client_id
  -p PASSWORD, --password PASSWORD
                        登录密码，或者 client_secret
  -t TOKEN, --token TOKEN
                        123 网盘的 access_token
  --ttl TTL             文件列表缓存时间，默认值：10，单位：秒
  -r, --refresh         更新文件列表缓存时，强制更新全部，如果不指定此参数，则会用一种预写的算法，尽量少地拉取数据以更新缓存（但可能出错）
  -H HOST, --host HOST  ip 或 hostname，默认值：'0.0.0.0'
  -P PORT, --port PORT  端口号，默认值：8123
  -v, --version         输出版本号
  -l, --license         输出授权信息

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
```
