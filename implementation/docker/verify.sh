#!/bin/bash

# verify initiator
echo "Verifying the Initiator. This might take some time..."
java -Xss128m -jar gobra.jar \
    --module "wireguard-gobra/wireguard" \
    --include initiator --include verification --include . \
    -i initiator

echo "Verifying the Responder. This might take some time..."
java -Xss128m -jar gobra.jar \
    --module "wireguard-gobra/wireguard" \
    --include responder --include verification --include . \
    -i responder
