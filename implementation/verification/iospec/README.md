The files `initiator-operations.gobra` and `responder-operations.gobra` are generated from `operations.gobra.py` using the template `operations.gobra.jinja`.

Jinja has to be installed ([Instructions](https://jinja.palletsprojects.com/en/3.0.x/intro/#installation)).
The following command will execute the generation of IO and internal operations and permissions:
```
python3 operations.gobra.py
```
