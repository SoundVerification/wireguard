# Wireguard
[![Code Verification](https://github.com/soundverification/wireguard/actions/workflows/workflow.yml/badge.svg?branch=main)](https://github.com/soundverification/wireguard/actions/workflows/workflow.yml?query=branch%3Amain)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL%202.0-brightgreen.svg)](./LICENSE)

## Verifying & Running in Docker
The sources of this verified implementation together with the code verifier Gobra and its dependencies are provided as a Docker image.
The image can be pulled and started in interactive mode as follows (assuming that Docker has been installed):
```
docker run -it ghcr.io/soundverification/wireguard-gobra:latest bash
```
An interactive shell at the working directory `/gobra` is started.
In this directory, you find the source code of our WireGuard case study.
Furthermore, several scripts provide easy access to the common operations:
- `./compile.sh` compiles the source code and creates a binary called `wireguard-gobra`
- `./verify.sh` verifies the initiator and responder roles. Due to the virtualized environment and differing hardware, verification of both roles might take a while. We have observed ~11min (compared to 7.8min when verifying them in a non-virtualized environment, as reported in the paper).
- `./test.sh` runs the initiator and responder as two separate processes. The script pipes two messages via standard input to each role that are then sent via VPN to the other role.

### Limitations of the Docker Image
We recommend using the ready-to-use Docker image over a local installation.
Note however that the Docker image only provides a limited environment for executing the implementation.
In particular, executing the initiator and responder in an interactive way would require two processes each accepting input.
Also, routing traffic from the OS (such as ping packets) requires additional setup for the network interfaces that we do not support in the Docker image.
Therefore, the remainder of this document provides detailed steps for verifying and executing the verified WireGuard implementation in a non-virtualized environment.


## Verifying Initiator & Responder Non-Virtualized
Change into the directory `case_studies/wireguard/src`. All subsequent commands are assumed to be executed in this directory.
To verify the initiator's implementation, run:
```
java -Xss128m -jar <PATH TO GOBRA JAR> -I initiator -I verification -I ./ --module wireguard-gobra/wireguard -i initiator
```
This command assumes that a JAR of the Gobra code verifier has been obtained and that the Z3 SMT solver (version 4.8.7) is installed.
The version of Z3 can be checked by running `z3 -version`.

Similarly, to verify the responder's implementation, run:
```
java -Xss128m -jar <PATH TO GOBRA JAR> -I responder -I verification -I ./ --module wireguard-gobra/wireguard -i responder
```

Description of the flags:
- `-Xss128m` increases the stack size used to run the verifier. The default argument does not suffice and will cause a runtime exception.
- `-I initiator -I verification -I ./` instructs Gobra to consider the current directory and the `initiator` and `verification` subfolders when performing lookups of imported packages. Note that `initiator` takes precende over `verification` and `verification over the current directory meaning that packages found in these subfolders will be selected over those found in the current directory.
- `--module wireguard-gobra/wireguard` informs Gobra that we are currently in this module. This impacts the package resolution as it basically means that Gobra will ignore this prefix. For example, the import statement `import lib "wireguard-gobra/wireguard/library"` results in Gobra looking for the folder `library` in the specified include directories (`-I` option).
- `-i initiator` specifies the package that is verified


## Building & Running this WireGuard Implementation Non-Virtualized
- `go build -v -o wireguard-gobra` for building the binary
- `./wireguard-gobra -h` will print the usage of all parameters.
- Note that the binary has to be executed with sudo rights if an interface should be created, i.e. `useStandardIO` is set to false.

### Running this WireGuard Implementation with STD I/O
1. `go build -v -o wireguard-gobra` for building the binary
2. Start responder:
  ```
  ./wireguard-gobra \
    --interfaceName utun8 \
    --privateKey oCxC44w/QKqastjiex7OTiKCfJphexquZ3MmJE5upU0= \
    --publicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
    --peerPublicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
    --endpoint 127.0.0.1:12345 \
    --port 12344 \
    --useStandardIO
  ```
3. Start initiator:
  ```
  ./wireguard-gobra \
    --interfaceName utun10 \
    --privateKey YIQ1ZXYUVs6OjE2GjDhJgAqoJDaPPdReVtSQ1zOy7n8= \
    --publicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
    --peerPublicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
    --endpoint 127.0.0.1:12344 \
    --port 12345 \
    --isInitiator \
    --useStandardIO
  ```
4. Messages can now be entered via standard input. Note however that the initiator is expected to send the first message, then the responder replies with the second message, etc. For the initiator and the responder, messages can be entered at any point, but the entered messages will be forwarded in the aforementioned pattern.


## Running official WireGuard Implementation
### Requirements
1. Clone repo: `git clone https://git.zx2c4.com/wireguard-go`
2. Get Go >= 1.6 (e.g. `brew install go`)
3. Build it: `make`
4. Get Wireguard-Tools (e.g. `brew install wireguard-tools`)

### Demo
The following commands demonstrate how two clients (running on the same machine) can be configured such that a handshake is established and the clients can ping each other via the established tunnel.
Note that the commands have been tested on macOS. The commands for Linux seem to be slightly different and can be found in [WireGuard's Quick Start](https://www.wireguard.com/quickstart/).

### Run Client 1
1. `sudo ./wireguard-go -f utun6`
2. `wg genkey > client1.private`
3. `sudo ifconfig utun6 inet 192.168.2.1 192.168.2.2`
4. `sudo wg set utun6 private-key ./client1.private`
5. `sudo ifconfig utun6 up`
6. If the first 5 steps for client 2 have been executed, `sudo wg` will display the public keys of each each client
7. `sudo wg set utun6 peer poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= allowed-ips 192.168.2.2/32 endpoint 127.0.0.1:57950` Note that the public key and port have to be adapted based on `sudo wg`'s output
8. `ping 192.168.2.2` pings client 2 which includes performing a handshake
9. `sudo wg` will display the time of the last handshake

### Run Client 2
1. `sudo ./wireguard-go -f utun7`
2. `wg genkey > client2.private`
3. `sudo ifconfig utun7 inet 192.168.2.2 192.168.2.1`
4. `sudo wg set utun7 private-key ./client2.private`
5. `sudo ifconfig utun7 up`
6. If the first 5 steps for client 1 have been executed, `sudo wg` will display the public keys of each each client
7. `sudo wg set utun7 peer Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= allowed-ips 192.168.2.1/32 endpoint 127.0.0.1:50759` Note that the public key and port have to be adapted based on `sudo wg`'s output
8. `ping 192.168.2.1` pings client 1


## Running this WireGuard Implementation against official WireGuard Implementation
### Run Client 1 (official)
1. `sudo ./wireguard-go -f utun6`
2. `wg genkey > client1.private`
3. `sudo ifconfig utun6 inet 192.168.2.1 192.168.2.2`
4. `sudo wg set utun6 private-key ./client1.private`
5. `sudo ifconfig utun6 up`
6. `sudo wg set utun6 peer poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= allowed-ips 192.168.2.2/32 endpoint 127.0.0.1:12344`

## Run Client 2 (this Implementation)
Use `sudo wg` to get the listening port of client 1 and use it as parameter `--endpoint
```
  sudo ./wireguard-gobra \
    --interfaceName utun8 \
    --privateKey oCxC44w/QKqastjiex7OTiKCfJphexquZ3MmJE5upU0= \
    --publicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
    --peerPublicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
    --endpoint 127.0.0.1:62751 \
    --port 12344 \
    --isInitiator
  ```
`sudo ifconfig utun8 inet 192.168.2.2 192.168.2.1`

`ping 192.168.2.1` can then be executed. To ping in the other direction, i.e. `ping 192.168.2.2`, `--isInitiator` has to be dropped from the command above.
