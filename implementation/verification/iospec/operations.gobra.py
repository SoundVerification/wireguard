from jinja2 import Environment, FileSystemLoader, select_autoescape
from copy import deepcopy

env = Environment(
    loader=FileSystemLoader(""), # search in current directory
    autoescape=select_autoescape(),
    trim_blocks=True,
    lstrip_blocks=True # remove spaces and tabs from start of a line
)

template = env.get_template("operations.gobra.jinja")

commonContext = {
    "imports": [
        {
            "qualifier": ".",
            "path": "wireguard-gobra/wireguard/verification/claim"
        },
        {
            "qualifier": ".",
            "path": "wireguard-gobra/wireguard/verification/fact"
        },
        {
            "qualifier": ".",
            "path": "wireguard-gobra/wireguard/verification/place"
        },
        {
            "qualifier": ".",
            "path": "wireguard-gobra/wireguard/verification/term"
        },
        {
            "qualifier": ".",
            "path": "wireguard-gobra/wireguard/verification/theta"
        }
    ],
    "bios": [
        # external operations
        {
            "name": "sendBio",
            "operation_name": "e_out",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                },
                {
                    "name": "m",
                    "type": "Term"
                }
            ],
            "outputs": [],
            "generate_permission_only": True
        },
        {
            "name": "recvBio",
            "operation_name": "e_in",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "m",
                    "type": "Term"
                }
            ],
            "generate_permission_only": True
        },
        {
            "name": "createNonce",
            "operation_name": "e_fr",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "n",
                    "type": "Term"
                }
            ],
            "generate_permission_only": True
        },
        {
            "name": "getLtKBio",
            "operation_name": "e_LtK",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "m1",
                    "type": "Term"
                },
                {
                    "name": "m2",
                    "type": "Term"
                }
            ],
            "generate_permission_only": True
        },
        {
            "name": "getLtpKBio",
            "operation_name": "e_LtpK",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "m1",
                    "type": "Term"
                },
                {
                    "name": "m2",
                    "type": "Term"
                }
            ],
            "generate_permission_only": True
        },
        {
            "name": "getPsKBio",
            "operation_name": "e_PsK",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "m1",
                    "type": "Term"
                },
                {
                    "name": "m2",
                    "type": "Term"
                },
                {
                    "name": "m3",
                    "type": "Term"
                }
            ],
            "generate_permission_only": True
        },
        {
            "name": "getCounter",
            "operation_name": "e_Counter",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "n",
                    "type": "Term"
                }
            ],
            "generate_permission_only": True
        },
        {
            "name": "getMessage",
            "operation_name": "e_Message",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "m",
                    "type": "Term"
                }
            ],
            "generate_permission_only": True
        },
        {
            "name": "getTimestamp",
            "operation_name": "e_Timestamp",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "m",
                    "type": "Term"
                }
            ],
            "generate_permission_only": True
        },
        {
            "name": "getMAC",
            "operation_name": "e_MAC",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "m",
                    "type": "Term"
                }
            ],
            "generate_permission_only": True
        }
    ]
}

initiatorAndResponderContext = {
    "imports": [
        {
            "qualifier": ".",
            "path": "wireguard-gobra/wireguard/verification/claim"
        },
        {
            "qualifier": ".",
            "path": "wireguard-gobra/wireguard/verification/fact"
        },
        {
            "qualifier": ".",
            "path": "wireguard-gobra/wireguard/verification/place"
        },
        {
            "qualifier": ".",
            "path": "wireguard-gobra/wireguard/verification/term"
        },
        {
            "qualifier": ".",
            "path": "wireguard-gobra/wireguard/verification/theta"
        }
    ],
    "bios": [
        # (internal) operations 1-5
        {
            "name": "internalBio1",
            "operation_name": "e_1",
            "inputs": [
                {
                    "name": "theta",
                    "type": "Theta"
                },
                {
                    "name": "l",
                    "type": "mset[Fact]"
                },
                {
                    "name": "a",
                    "type": "mset[Claim]"
                },
                {
                    "name": "r",
                    "type": "mset[Fact]"
                }
            ],
            "outputs": [],
            "can_fail": False
        },
        {
            "name": "internalBio2",
            "operation_name": "e_2",
            "inputs": [
                {
                    "name": "theta",
                    "type": "Theta"
                },
                {
                    "name": "l",
                    "type": "mset[Fact]"
                },
                {
                    "name": "a",
                    "type": "mset[Claim]"
                },
                {
                    "name": "r",
                    "type": "mset[Fact]"
                }
            ],
            "outputs": [],
            "can_fail": False
        },
        {
            "name": "internalBio3",
            "operation_name": "e_3",
            "inputs": [
                {
                    "name": "theta",
                    "type": "Theta"
                },
                {
                    "name": "l",
                    "type": "mset[Fact]"
                },
                {
                    "name": "a",
                    "type": "mset[Claim]"
                },
                {
                    "name": "r",
                    "type": "mset[Fact]"
                }
            ],
            "outputs": [],
            "can_fail": False
        },
        {
            "name": "internalBio4",
            "operation_name": "e_4",
            "inputs": [
                {
                    "name": "theta",
                    "type": "Theta"
                },
                {
                    "name": "l",
                    "type": "mset[Fact]"
                },
                {
                    "name": "a",
                    "type": "mset[Claim]"
                },
                {
                    "name": "r",
                    "type": "mset[Fact]"
                }
            ],
            "outputs": [],
            "can_fail": False
        },
        {
            "name": "internalBio5",
            "operation_name": "e_5",
            "inputs": [
                {
                    "name": "theta",
                    "type": "Theta"
                },
                {
                    "name": "l",
                    "type": "mset[Fact]"
                },
                {
                    "name": "a",
                    "type": "mset[Claim]"
                },
                {
                    "name": "r",
                    "type": "mset[Fact]"
                }
            ],
            "outputs": [],
            "can_fail": False
        }
    ]
}

additionalInitiatorContext = {
    "bios": [
        {
            "name": "getInit0",
            "operation_name": "e_init0",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "m1",
                    "type": "Term"
                },
                {
                    "name": "m2",
                    "type": "Term"
                },
                {
                    "name": "m3",
                    "type": "Term"
                },
                {
                    "name": "m4",
                    "type": "Term"
                }
            ],
            "can_fail": True,
            "generate_permission_only": True
        }
    ]
}

additionalResponderContext = {
    "bios": [
        {
            "name": "getResp0",
            "operation_name": "e_resp0",
            "inputs": [
                {
                    "name": "rid",
                    "type": "Term"
                }
            ],
            "outputs": [
                {
                    "name": "m1",
                    "type": "Term"
                },
                {
                    "name": "m2",
                    "type": "Term"
                },
                {
                    "name": "m3",
                    "type": "Term"
                },
                {
                    "name": "m4",
                    "type": "Term"
                },
                {
                    "name": "m5",
                    "type": "Term"
                }
            ],
            "can_fail": True,
            "generate_permission_only": True
        }
    ]
}


def combine(dict1, dict2):
    res = deepcopy(dict1)
    dict2Copy = deepcopy(dict2)
    for k, v in dict2Copy.items():
        if k in res:
            res[k] = res[k] + v
        else:
            res[k] = v
    return res

initiatorContext = combine(initiatorAndResponderContext, additionalInitiatorContext)
responderContext = combine(initiatorAndResponderContext, additionalResponderContext)


# add suffix to each bio name and event name:
def addSuffix(dictionary, suffix):
    for k, v in dictionary.items():
        if k == "bios":
            for bio in v:
                bio["name"] = bio["name"] + suffix
                bio["operation_name"] = bio["operation_name"] + suffix

addSuffix(initiatorContext, "I")
addSuffix(responderContext, "R")


# render template and write to output files:
with open("common-operations.gobra", "w") as f:
    f.write(template.render(commonContext))

with open("initiator-operations.gobra", "w") as f:
    f.write(template.render(initiatorContext))

with open("responder-operations.gobra", "w") as f:
    f.write(template.render(responderContext))
