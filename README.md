## ⚠️ This repository has permanently moved to [`viperproject/protocol-verification-refinement`](https://github.com/viperproject/protocol-verification-refinement)

---

# Tamarin Model & Verified Go Implementation of the WireGuard VPN Key Exchange Protocol and Diffie-Hellman
[![DH & WireGuard Protocol Model Verification](https://github.com/soundverification/wireguard/actions/workflows/model.yml/badge.svg?branch=main)](https://github.com/soundverification/wireguard/actions/workflows/model.yml?query=branch%3Amain)
[![DH Code Verification](https://github.com/soundverification/wireguard/actions/workflows/dh-code.yml/badge.svg?branch=main)](https://github.com/soundverification/wireguard/actions/workflows/dh-code.yml?query=branch%3Amain)
[![WireGuard Code Verification](https://github.com/soundverification/wireguard/actions/workflows/wireguard-code.yml/badge.svg?branch=main)](https://github.com/soundverification/wireguard/actions/workflows/wireguard-code.yml?query=branch%3Amain)
[![License: MPL 2.0](https://img.shields.io/badge/License-MPL%202.0-brightgreen.svg)](./LICENSE)

This repository provides the following content:
- Subdirectory `wireguard/model` contains the Tamarin model together with instructions how to verify it
- Subdirectory `wireguard/implementation` contains the verified Go implementation together with instructions how to verify and execute it.
- The subdirectory `dh` contains the verified DH protocol model together with a verified Go and Java implementations. Additionally, `dh/faulty-go-implementation` contains a Go implementation that tries to send the DH private key in plaintext for which verification fails because the IO specification does not permit such a send operation.
- The subdirectory `specification-generator` contains the sources of our tool to generate I/O specifications for Gobra & VeriFast from a Tamarin model.
