#!/bin/bash

mkdir -p .gobra

# verify initiator
echo "Verifying the Initiator. This might take some time..."
java -Xss128m -jar gobra.jar \
    --module "wireguard-gobra/wireguard" \
    --include verification --include . \
    --directory initiator

# verify responder
echo "Verifying the Responder. This might take some time..."
java -Xss128m -jar gobra.jar \
    --module "wireguard-gobra/wireguard" \
    --include verification --include . \
    --directory responder
