# tron.rs

> [!WARNING]
> Work in progress, implementation incomplete.

Rust implementation of the [TRON](https://github.com/delaneyj/tron/tree/main) binary format, with Python bindings.

The goal is to implement a dict-like interface for TRON:

```python
import tron

data = Tron.from_json('{"name": "John Doe", "email": ["john@example.com", "jd@example.com"]}')
data["name"]
# "John Doe"
data["email"][0]
# "john@example.com"
data["age"] = 42
data["email"].append("john@doe.com")
```
