# Python 123 网盘客户端

![PyPI - Python Version](https://img.shields.io/pypi/pyversions/p123client)
![PyPI - Version](https://img.shields.io/pypi/v/p123client)
![PyPI - Downloads](https://img.shields.io/pypi/dm/p123client)
![PyPI - Format](https://img.shields.io/pypi/format/p123client)
![PyPI - Status](https://img.shields.io/pypi/status/p123client)

## 0. 安装

你可以从 [pypi](https://pypi.org/project/p123client/) 安装最新版本

```console
pip install -U p123client
```

## 1. 导入模块和创建实例

首先导入模块

```python
from p123client import P123Client
```

### 1. 用 token 创建实例

创建客户端对象，需要传入 JWT <kbd>token</kbd>，也就是 `access_token`

```python
# TODO: 访问令牌
token = "..."

client = P123Client(token=token)
```

或者直接写作

```python
client = P123Client(token)
```

不过我更推荐把 <kbd>token</kbd> 写入一个文件中，例如在 `~/123-token.txt`

```python
from pathlib import Path

client = P123Client(token=Path("~/123-token.txt").expanduser())
```

或者直接写作

```python
client = P123Client(Path("~/123-token.txt").expanduser())
```

### 2. 账号和密码登录

```python
# TODO: 手机号或者邮箱
passport = "..." 
# TODO: 密码
password = "..."

client = P123Client(passport=passport, password=passport)
```

或者直接写作

```python
client = P123Client(passport, passport)
```

### 3. client_id 和 client_secret 登录

需要先申请成为开发者

https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/hpengmyg32blkbg8

```python
# TODO: 应用标识，创建应用时分配的 appId
client_id = "..." 
# TODO: 应用密钥，创建应用时分配的 secretId
client_secret = "..."

client = P123Client(client_id=client_id, client_secret=client_secret)
```

或者直接写作

```python
client = P123Client(client_id, client_secret)
```

### 4. refresh_token 登录

```python
# TODO: 刷新令牌
refresh_token = "..."

client = P123Client(refresh_token=refresh_token)
```

或者直接写作

```python
client = P123Client(refresh_token)
```

**注意**：使用 refresh_token（或者说 oauth 登录），只允许访问 open 接口

### 5. oauth 登录

需要先去开发者后台设置一下回调链接，审核通过后才可用

```python
# TODO: 应用标识，创建应用时分配的 appId
client_id = "..." 
# TODO: 应用密钥，创建应用时分配的 secretId
client_secret = "..."
# TODO: 回调链接
redirect_uri = "..."
# TODO: 访问令牌
token = "..."

resp = P123Client.login_with_oauth(
    client_id=client_id, 
    client_secret=client_secret, 
    redirect_uri=redirect_uri, 
    token=token, 
)
client = P123Client(
    client_id=client_id, 
    client_secret=client_secret, 
    token=resp["access_token"], 
    refresh_token=resp["refresh_token"], 
)
```

### 6. 扫码登录

当你什么都不传时，就会要求你扫码登录

```python
client = P123Client()
```

### 7. 用 token 来扫码新的 token

你可以用一个 token 去扫码获得另一个 token（仅当不是 oauth 登录时）

```python
client_new = client.login_another()
```

另外你也可以用 oauth 登录，虽然仅能访问 open 接口，但是 QPS 上放得更宽

下面我用 clouddrive 在 123 网盘上用 oauth 登录举例说明第三方挂载应用登录：

https://123yunpan.yuque.com/org-wiki-123yunpan-muaork/cr6ced/kf05anzt1r0qnudd

```python
import requests
from urllib.parse import parse_qsl, urlsplit

resp = client.login_oauth_authorize({
    "client_id": "7c278c60da9e43848c45ff8e6fa9da0a", 
    "redirect_uri": "https://redirect123pan.zhenyunpan.com/redirect_pan123", 
    "accessToken": client.token, 
    "state": "http://localhost:19798", 
})
with requests.get(resp["url"], allow_redirects=False, stream=True) as response:
    resp = dict(parse_qsl(urlsplit(response.headers["location"]).query))
client_new = P123Client(token=resp["access_token"], refresh_token=resp["refresh_token"])
```

### 8. 关于 token 的结构

<kbd>token</kbd> 中包含了一些信息，以 "." 进行分割，可以拆成 3 个部分：

- JWT 算法（经过 base64 加密）
- 用户信息（经过 base64 加密）
- 签名字符串

```python
from base64 import urlsafe_b64decode
from json import loads

token = client.token

method, user_info, sign = token.split(".", 2)
print("JWT 算法:", loads(urlsafe_b64decode(method)))
print("用户信息:", loads(urlsafe_b64decode(user_info+"==")))
print("签名:", sign)
```

## 2. 接口调用

所有需要直接或间接执行 HTTP 请求的接口，都有同步和异步的调用方式，且默认是采用 POST 发送 JSON 请求数据

```python
# 同步调用
client.method(payload)
client.method(payload, async_=False)

# 异步调用
await client.method(payload, async_=True)
```

从根本上讲，除了几个 `staticmethod`，它们都会调用 `P123Client.request`

```python
url = "https://www.123pan.com/api/someapi"
response = client.request(url=url, json={...})
```

当你需要构建自己的扩展模块，以增加一些新的 123 web 接口时，就需要用到此方法了

```python
from collections.abc import Coroutine
from typing import overload, Any, Literal

from p123client import P123Client

class MyCustom123Client(P123Client):

    @overload
    def foo(
        self, 
        payload: dict, 
        /, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def foo(
        self, 
        payload: dict, 
        /, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def foo(
        self, 
        payload: dict, 
        /, 
        async_: bool = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        api = "https://www.123pan.com/api/foo"
        return self.request(
            api, 
            method="GET", 
            params=payload, 
            async_=async_, 
            **request_kwargs, 
        )

    @overload
    def bar(
        self, 
        payload: dict, 
        /, 
        async_: Literal[False] = False, 
        **request_kwargs, 
    ) -> dict:
        ...
    @overload
    def bar(
        self, 
        payload: dict, 
        /, 
        async_: Literal[True], 
        **request_kwargs, 
    ) -> Coroutine[Any, Any, dict]:
        ...
    def bar(
        self, 
        payload: dict, 
        /, 
        async_: bool = False, 
        **request_kwargs, 
    ) -> dict | Coroutine[Any, Any, dict]:
        api = "https://www.123pan.com/api/bar"
        return self.request(
            api, 
            method="POST", 
            json=payload, 
            async_=async_, 
            **request_kwargs, 
        )
```

## 3. 检查响应

接口被调用后，如果返回的是 dict 类型的数据（说明原本是 JSON），则可以用 `p123client.check_response` 执行检查。首先会查看其中名为 "code" 的键的对应值，如果为 0 或 200 或者不存在，则原样返回被检查的数据；否则，抛出一个 `p123client.P123OSError` 的实例。

```python
from p123client import check_response

# 检查同步调用
data = check_response(client.method(payload))
# 检查异步调用
data = check_response(await client.method(payload, async_=True))
```

## 4. 辅助工具

一些简单的封装工具可能是必要的，特别是那种实现起来代码量比较少，可以封装成单个函数的。我把平常使用过程中，积累的一些经验具体化为一组工具函数。这些工具函数分别有着不同的功能，如果组合起来使用，或许能解决很多问题。

```python
from p123client import tool
```

## 5. 学习案例

### 1. 创建自定义 uri

```python
from p123client import P123Client
from p123client.tool import make_uri

# TODO: 改成你自己的账户和密码
client = P123Client(passport="手机号或邮箱", password="登录密码")

# TODO: 请改成你要处理的文件 id
file_id = 15688945
print(make_uri(client, file_id))
```

### 2. 由自定义 uri 转存文件到你的网盘

```python
from p123client import P123Client
from p123client.tool import upload_uri

# TODO: 改成你自己的账户和密码
client = P123Client(passport="手机号或邮箱", password="登录密码")

uri = "123://torrentgalaxy.db|1976025090|582aa8bfb0ad8e6f512d9661f6243bdd"
print(upload_uri(client, uri, duplicate=1))
```

### 3. 由自定义 uri 获取下载直链

```python
from p123client import P123Client
from p123client.tool import get_downurl

# TODO: 改成你自己的账户和密码
client = P123Client(passport="手机号或邮箱", password="登录密码")

# 带 s3_key_flag
print(get_downurl(client, "123://torrentgalaxy.db|1976025090|582aa8bfb0ad8e6f512d9661f6243bdd?1812602326-0"))
# 不带 s3_key_flag（会转存）
print(get_downurl(client, "123://torrentgalaxy.db|1976025090|582aa8bfb0ad8e6f512d9661f6243bdd"))
```

### 4. 直链服务

需要先安装 [blacksheep](https://www.neoteroi.dev/blacksheep/)

```console
pip install 'blacksheep[uvicorn]'
```

然后启动如下服务，就可以访问以获取直链了

**带 s3_key_flag**

http://localhost:8123/torrentgalaxy.db|1976025090|582aa8bfb0ad8e6f512d9661f6243bdd?1812602326-0

**不带 s3_key_flag（会转存）**

http://localhost:8123/torrentgalaxy.db|1976025090|582aa8bfb0ad8e6f512d9661f6243bdd

```python
from blacksheep import json, redirect, Application, Request
from p123client import P123Client
from p123client.tool import get_downurl

# TODO: 改成你自己的账户和密码
client = P123Client(passport="", password="")

app = Application(show_error_details=__debug__)

@app.router.route("/{path:uri}", methods=["GET", "HEAD"])
async def index(request: Request, uri: str):
    try:
        payload = int(uri)
    except ValueError:
        if uri.count("|") < 2:
            return json({"state": False, "message": f"bad uri: {uri!r}"}, 500)
        payload = uri
        if s3_key_flag := request.url.query:
            payload += "?" + s3_key_flag.decode("ascii")
    url = await get_downurl(client, payload, quoted=False, async_=True)
    return redirect(url)

if __name__ == "__main__":
    from uvicorn import run

    run(app, host="0.0.0.0", port=8123)
```

### 5. 遍历文件列表

导出的文件信息中，有个 `"uri"`，表示文件的自定义链接，前面以 `123://` 开头，你可以替换成 302 服务的地址，例如 `http://localhost:8123/`

#### 1. 遍历网盘中的文件列表

```python
from p123client import P123Client
from p123client.tool import iterdir

# TODO: 改成你自己的账户和密码
client = P123Client(passport="手机号或邮箱", password="登录密码")

for info in iterdir(client, parent_id=0, max_depth=-1):
    print(info)
```

#### 2. 遍历分享中的文件列表，不含目录

```python
from p123client.tool import share_iterdir

# NOTE: 无需登录
for info in share_iterdir(
    "https://www.123684.com/s/oec7Vv-CIYWh?提取码:ZY4K", 
    max_depth=-1, 
    predicate=lambda a: not a["is_dir"], 
):
    print(info)
```

#### 3. 导出分享中的文件列表到本地 .json 文件

```python
from orjson import dumps
from p123client.tool import share_iterdir

def export_share_files_json(
    link: str, 
    path: str = "", 
    cooldown: float = 0, 
):
    """把分享链接中的文件列表导出到 json 文件

    :param link: 分享链接，可以包含提取码
    :param path: 保存的路径，如果不提供则自动确定
    :param cooldown: 两次调用之间，冷却的时间（用两次调用开始时的时间差，而不是一次完成到下一次开始的时间差）
    """
    print("< 将拉取:", link)
    ls: list[dict] = []
    for i, a in enumerate(share_iterdir(link, max_depth=-1, cooldown=cooldown), 1):
        ls.append(a)
        print(i, a)
    if ls:
        info = ls[0]
        if not path:
            suffix = f"@{info['ShareKey']},{info['SharePwd']}.json"
            path = f"{info['name'][:255-len(suffix)]}{suffix}"
        open(path, "wb").write(dumps(ls))
        print()
        print("> 已拉取:", link)
        print("> 已保存:", path)

export_share_files_json("https://www.123684.com/s/oec7Vv-CIYWh?提取码:ZY4K")
```

### 6. 最新的操作记录

在网盘中，你可以按更新时间逆序查询，即可得到最新上传的文件列表

```python
client.fs_list_new({
    "orderBy": "update_time", 
    "orderDirection": "desc", 
    "SearchData": ".", 
})
```

更一般的，你可以在[同步空间](https://www.123pan.com/SynchronousSpace/main)中执行文件操作。

而在拉取文件列表时，需要指定

```python
client.fs_list_new({
    "operateType": "SyncSpacePage", 
    "event": "syncFileList", 
    "RequestSource": 1, 
})
```

同步空间中的增删改操作都有[操作记录](https://www.123pan.com/SynchronousSpace/record)，你可以用接口

```python
client.fs_sync_log()
```

## 其它资源

- 如果你需要更详细的文档，特别是关于各种接口的信息，可以阅读

    [https://p123client.readthedocs.io/en/latest/](https://p123client.readthedocs.io/en/latest/)
