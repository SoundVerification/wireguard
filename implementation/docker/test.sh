#!/bin/bash

source ./compile.sh

function initiator() {
    echo -e "Hello\nWorld!\n" | ./wireguard-gobra \
        --interfaceName utun10 \
        --privateKey YIQ1ZXYUVs6OjE2GjDhJgAqoJDaPPdReVtSQ1zOy7n8= \
        --publicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
        --peerPublicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
        --endpoint 127.0.0.1:12344 \
        --port 12345 \
        --isInitiator \
        --useStandardIO
}

function responder() {
    echo -e "Hello back\nI'm the responder\n" | ./wireguard-gobra \
        --interfaceName utun8 \
        --privateKey oCxC44w/QKqastjiex7OTiKCfJphexquZ3MmJE5upU0= \
        --publicKey poKDYnMyFZWkSwGlAXXb79nh0L8rEb+S8XWAtXQxsmc= \
        --peerPublicKey Y1842DzWWfqP42p9SJNoX1fEJdTOkuyi/fx+1Y7aFU4= \
        --endpoint 127.0.0.1:12345 \
        --port 12344 \
        --useStandardIO
}

# execute initiator and responder in parallel and wait until they are done:
RESPONDER_TEMP_FILE=$(mktemp)
responder > $RESPONDER_TEMP_FILE &
INITIATOR_TEMP_FILE=$(mktemp)
initiator > $INITIATOR_TEMP_FILE &
wait

# print initiator and responder output:
echo -e "\n\n======== Initiator Output ========"
cat $INITIATOR_TEMP_FILE

echo -e "\n\n======== Responder Output ========"
cat $RESPONDER_TEMP_FILE
