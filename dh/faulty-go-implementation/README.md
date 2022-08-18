# Faulty Go Diffie-Hellman Implementation
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL%202.0-brightgreen.svg)](../../LICENSE)

Verification of this implementation fails as expected because the implementation
tries to send the DH private key `x` instead of `g^x` in the first message.

## Building & Running the Initiator Role
Build:
```
go build
```

Run:
```
./dh-gobra --isInitiator --endpoint localhost:12345 --privateKey "ACvCw0fb1mqTQikmXOas+YEbJnC9O/N4H12k4w/ADVRVg6YAptHsQO57FNzeeS2BtGwHas51wRruj62+y4WpjQ==" --peerPublicKey "H4omvaajENeqxbRiOVCLZoGUrEWIVrVAtJPk5JgoEV8="
```

The command above configures the Initiator to use Keypair 1 for its own secret key and tries to communicate with the Responder by using Keypair 2's public key.

Note that the Responder has to be started first.


Keypair 1:
    - sk: "ACvCw0fb1mqTQikmXOas+YEbJnC9O/N4H12k4w/ADVRVg6YAptHsQO57FNzeeS2BtGwHas51wRruj62+y4WpjQ=="
    - pk: "VYOmAKbR7EDuexTc3nktgbRsB2rOdcEa7o+tvsuFqY0="

Keypair 2:
    - sk: "k2gUarJExuxjji+KlwD8NfclZ+ZCZ8xZk3NGzN3ypwgfiia9pqMQ16rFtGI5UItmgZSsRYhWtUC0k+TkmCgRXw=="
    - pk: "H4omvaajENeqxbRiOVCLZoGUrEWIVrVAtJPk5JgoEV8="

## Verifying the Initiator Role
Detailed explanations and Gobra's JAR file are given in WireGuard's implementation folder.
```
java -Xss128m -jar ../../wireguard/implementation/gobra.jar -I verification -I ./ --module dh-gobra --directory initiator
```
Note that verification of this implementation is expected to fail with the following error message:
```
ERROR viper.gobra.Gobra - Gobra has found 1 error(s) in package initiator - initiator
ERROR viper.gobra.Gobra -       <initiator/initiator.go:201:14> Precondition of call i.l.Send(msg1Data , t1, ridT, xT ) might not hold. 
Permission to e_OutFact(t, rid, m) might not suffice.
```
