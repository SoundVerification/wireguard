package device

import (
	"encoding/base64"
	"fmt"

	"wireguard-gobra/wireguard/conn"
)

type Peer struct {
	device          *Device
	Endpoint        conn.Endpoint
	CookieGenerator CookieGenerator
	Handshake       Handshake
	// keypairs     Keypairs
	keypair *Keypair
}

func NewPeer(device *Device, endpoint conn.Endpoint, pk NoisePublicKey) *Peer {
	// create peer
	peer := new(Peer)

	peer.CookieGenerator.Init(pk)
	peer.device = device

	// pre-compute DH
	handshake := &peer.Handshake
	handshake.PrecomputedStaticStatic = device.StaticIdentity.PrivateKey.SharedSecret(pk)
	// handshake.precomputedStaticStatic == (g^k_R) ^ k_I == g^(k_R * k_I)
	handshake.RemoteStatic = pk

	// set endpoint
	peer.Endpoint = endpoint

	return peer
}

func (peer *Peer) String() string {
	base64Key := base64.StdEncoding.EncodeToString(peer.Handshake.RemoteStatic[:])
	abbreviatedKey := "invalid"
	if len(base64Key) == 44 {
		abbreviatedKey = base64Key[0:4] + "…" + base64Key[39:43]
	}
	return fmt.Sprintf("peer(%s)", abbreviatedKey)
}
