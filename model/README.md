# Tamarin model for WireGuard key exchange


## Files

- The `wireguard.spthy` file contains the Tamarin model, including the security properties and the auxiliary lemmas.

- The `wireguard.oracle` file contains an oracle (an auxiliary python script providing a heuristic to guide Tamarin's proof search).


## Prerequisite

To verify our model of the WireGuard key exchange, you need **Tamarin**
which can be obtained from [its website](https://tamarin-prover.github.io).

**Python2** is also required to run the oracle.



## Instructions

To verify the model with Tamarin, use the following command:

`tamarin-prover --heuristic=O --oraclename="wireguard.oracle" --prove wireguard.spthy`
