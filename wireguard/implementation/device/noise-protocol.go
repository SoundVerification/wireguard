package device

import (
	"errors"
	"fmt"
	"time"

	// "fmt"

	"golang.org/x/crypto/blake2s"
	"golang.org/x/crypto/chacha20poly1305"
	"golang.org/x/crypto/poly1305"

	"wireguard-gobra/wireguard/tai64n"
)

const (
	NoiseConstruction = "Noise_IKpsk2_25519_ChaChaPoly_BLAKE2s"
	WGIdentifier      = "WireGuard v1 zx2c4 Jason@zx2c4.com"
	WGLabelMAC1       = "mac1----"
	WGLabelCookie     = "cookie--"
)

const (
	MessageInitiationType  = 1
	MessageResponseType    = 2
	MessageCookieReplyType = 3
	MessageTransportType   = 4
)

const (
	MessageInitiationSize      = 148                                           // size of handshake initiation message
	MessageResponseSize        = 92                                            // size of response message
	MessageCookieReplySize     = 64                                            // size of cookie reply message
	MessageTransportHeaderSize = 16                                            // size of data preceding content in transport message
	MessageTransportSize       = MessageTransportHeaderSize + poly1305.TagSize // size of empty transport
	MessageKeepaliveSize       = MessageTransportSize                          // size of keepalive
	MessageHandshakeSize       = MessageInitiationSize                         // size of largest handshake related message
)

const (
	MessageTransportOffsetReceiver = 4
	MessageTransportOffsetCounter  = 8
	MessageTransportOffsetContent  = 16
)

type handshakeState int

const (
	handshakeZeroed = handshakeState(iota)
	handshakeInitiationCreated
	handshakeInitiationConsumed
	handshakeResponseCreated
	handshakeResponseConsumed
)

/* Type is an 8-bit field, followed by 3 nul bytes,
 * by marshalling the messages in little-endian byteorder
 * we can treat these as a 32-bit unsigned int (for now)
 *
 */

type MessageInitiation struct {
	Type      uint32
	Sender    uint32                                        // sid_I
	Ephemeral NoisePublicKey                                // epk_I
	Static    [NoisePublicKeySize + poly1305.TagSize]byte   // c_pk_I
	Timestamp [tai64n.TimestampSize + poly1305.TagSize]byte // c_ts
	MAC1      [blake2s.Size128]byte
	MAC2      [blake2s.Size128]byte
}

type MessageResponse struct {
	Type      uint32
	Sender    uint32                 // sid_R
	Receiver  uint32                 // sid_I
	Ephemeral NoisePublicKey         // epk_R
	Empty     [poly1305.TagSize]byte // c_empty
	MAC1      [blake2s.Size128]byte
	MAC2      [blake2s.Size128]byte
}

type MessageCookieReply struct {
	Type     uint32
	Receiver uint32
	Nonce    [chacha20poly1305.NonceSizeX]byte
	Cookie   [blake2s.Size128 + poly1305.TagSize]byte
}

type Handshake struct {
	state                   handshakeState
	hash                    [blake2s.Size]byte       // hash value
	chainKey                [blake2s.Size]byte       // chain key
	PresharedKey            NoisePresharedKey        // psk
	localEphemeral          NoisePrivateKey          // ephemeral secret key
	localIndex              uint32                   // used to clear hash-table
	remoteIndex             uint32                   // index for sending
	RemoteStatic            NoisePublicKey           // long term key
	remoteEphemeral         NoisePublicKey           // ephemeral public key
	PrecomputedStaticStatic [NoisePublicKeySize]byte // precomputed shared secret
}

var (
	InitialChainKey [blake2s.Size]byte
	InitialHash     [blake2s.Size]byte
	ZeroNonce       [chacha20poly1305.NonceSize]byte
)

// dst = kdf1(c, data)
func MixKey(dst *[blake2s.Size]byte, c *[blake2s.Size]byte, data []byte) {
	KDF1(dst, c[:], data)
}

// dst == hash(h, data)
func MixHash(dst *[blake2s.Size]byte, h *[blake2s.Size]byte, data []byte) {
	hash, _ := blake2s.New256(nil)
	hash.Write(h[:])
	hash.Write(data)
	hash.Sum(dst[:0])
	hash.Reset()
}

// h.hash == hash(<old(h.hash), data>)
func (h *Handshake) mixHash(data []byte) {
	MixHash(&h.hash, &h.hash, data)
}

// h.chainKey == kdf1(<old(h.chainKey), data>)
func (h *Handshake) mixKey(data []byte) {
	MixKey(&h.chainKey, &h.chainKey, data)
}

/* Do basic precomputations
 */
func init() {
	// NoiseConstruction == 'wireguard'
	// WGIdentifier == prologue
	InitialChainKey = blake2s.Sum256([]byte(NoiseConstruction))
	// InitialChainKey == c_0 == hash(NoiseConstruction)
	MixHash(&InitialHash, &InitialChainKey, []byte(WGIdentifier))
	// InitialHash == h_0 == hash(InitialChainKey, WGIdentifier)
}

func (device *Device) CreateMessageInitiation(peer *Peer) (*MessageInitiation, error) {
	var errZeroECDHResult = errors.New("ECDH returned all zeros")

	handshake := &peer.Handshake

	// create ephemeral key
	var err error
	handshake.hash = InitialHash
	// handshake.hash == c0
	handshake.chainKey = InitialChainKey
	// handshake.chainKey == h0
	// create ek_I:
	handshake.localEphemeral, err = NewPrivateKey()
	if err != nil {
		return nil, err
	}

	handshake.mixHash(handshake.RemoteStatic[:])
	// handshake.hash == h1

	msg := MessageInitiation{
		Type: MessageInitiationType,
		// set epk_I:
		Ephemeral: handshake.localEphemeral.PublicKey(),
	}

	handshake.mixKey(msg.Ephemeral[:])
	// handshakey.chainKey == c1
	handshake.mixHash(msg.Ephemeral[:])
	// handshake.hash == h2

	// encrypt static key
	// handshake.remoteStatic == g^k_R == pk_R
	ss := handshake.localEphemeral.SharedSecret(handshake.RemoteStatic)
	// ss == g^(k_R * ek_I) == (g^k_R)^ek_I
	if isZero(ss[:]) {
		return nil, errZeroECDHResult
	}
	var key [chacha20poly1305.KeySize]byte
	// handshake.chainKey == c1
	// ss == g^(k_R * ek_I) == (g^k_R)^ek_I
	KDF2(
		&handshake.chainKey,
		&key,
		handshake.chainKey[:],
		ss[:],
	)
	// handshake.chainKey == c2 == kdf1(<c1, g^(k_R * ek_I)>)
	// key == k_1 == kdf2(<c1, g^(k_R * ek_I)>)
	aead, _ := chacha20poly1305.New(key[:]) // k_1
	// encrypt pk_i with additional data h2 and key k_1 and store it as c_pk_I in msg
	aead.Seal(msg.Static[:0], ZeroNonce[:], device.StaticIdentity.PublicKey[:], handshake.hash[:])
	handshake.mixHash(msg.Static[:])
	// handshake.hash == h3

	// encrypt timestamp
	if isZero(handshake.PrecomputedStaticStatic[:]) {
		return nil, errZeroECDHResult
	}
	KDF2(
		&handshake.chainKey,
		&key,
		handshake.chainKey[:],
		handshake.PrecomputedStaticStatic[:],
	)
	// g^(k_R * k_I) == (g^k_R)^k_I == handshake.precomputedStaticStatic
	// key == kdf2(c2, g^(k_R * k_I))
	// c3 == handshake.chainKey == kdf1(old(handshake.chainKey), g^(k_R * k_I))
	timestamp := tai64n.Now()
	// key == k2
	aead, _ = chacha20poly1305.New(key[:])
	// handshake.hash == h3
	aead.Seal(msg.Timestamp[:0], ZeroNonce[:], timestamp[:], handshake.hash[:])
	// msg.Timestamp == c_ts

	// assign index
	// device.indexTable.Delete(handshake.localIndex)
	// msg.Sender, err = device.indexTable.NewIndexForHandshake(peer, handshake)
	// msg.Sender = 0
	msg.Sender, err = randUint32()
	if err != nil {
		return nil, err
	}
	handshake.localIndex = msg.Sender
	// handshake.localIndex == sid_I

	handshake.mixHash(msg.Timestamp[:])
	// handshake.hash == h4
	handshake.state = handshakeInitiationCreated
	return &msg, nil
}

func (device *Device) ConsumeMessageInitiation(msg *MessageInitiation) *Peer {
	var (
		hash     [blake2s.Size]byte
		chainKey [blake2s.Size]byte
	)

	if msg.Type != MessageInitiationType {
		device.Log.Verbosef("ConsumeMessageInitiation: invalid type")
		return nil
	}

	// InitialHash == h0
	// device.staticIdentity.publicKey == pk_R
	MixHash(&hash, &InitialHash, device.StaticIdentity.PublicKey[:])
	// hash == h1
	// msg.Ephemeral == epk_I
	MixHash(&hash, &hash, msg.Ephemeral[:])
	// hash == h2
	// c0 == InitialChainKey
	// epk_I == msg.Ephemeral
	MixKey(&chainKey, &InitialChainKey, msg.Ephemeral[:])
	// chainKey == c1 == kdf1(c0, epk_I)

	// decrypt static key
	var err error
	var peerPK NoisePublicKey
	var key [chacha20poly1305.KeySize]byte
	ss := device.StaticIdentity.PrivateKey.SharedSecret(msg.Ephemeral)
	// ss == epk_I^k_R
	if isZero(ss[:]) {
		device.Log.Verbosef("ConsumeMessageInitiation: shared secret is zero")
		return nil
	}
	KDF2(&chainKey, &key, chainKey[:], ss[:])
	// c2 == chainKey == kdf1(c1, epk_I^k_R)
	// k1 == key == kdf2(c1, epk_I^k_R)
	aead, _ := chacha20poly1305.New(key[:])
	_, err = aead.Open(peerPK[:0], ZeroNonce[:], msg.Static[:], hash[:])
	// peerPK == pk_I
	if err != nil {
		device.Log.Verbosef("ConsumeMessageInitiation: AEAD decrypt failed")
		return nil
	}
	MixHash(&hash, &hash, msg.Static[:])
	// hash == h3

	// lookup peer
	/* previsouly:
	peer := device.LookupPeer(peerPK)
	if peer == nil {
		device.log.Verbosef("ConsumeMessageInitiation: peer not found")
		return nil
	}
	*/
	if !device.Peer.Handshake.RemoteStatic.Equals(peerPK) {
		device.Log.Verbosef("ConsumeMessageInitiation: wrong peer public key")
		return nil
	}
	peer := device.Peer
	handshake := &peer.Handshake

	// verify identity

	var timestamp tai64n.Timestamp

	if isZero(handshake.PrecomputedStaticStatic[:]) {
		device.Log.Verbosef("ConsumeMessageInitiation: precomputed static is zero")
		return nil
	}
	KDF2(
		&chainKey,
		&key,
		chainKey[:],
		handshake.PrecomputedStaticStatic[:],
	)
	// c3 == chainKey == kdf1(c2, (g^k_I)^k_R)
	// k2 == key == kdf2(c2, (g^k_I)^k_R)
	aead, _ = chacha20poly1305.New(key[:])
	_, err = aead.Open(timestamp[:0], ZeroNonce[:], msg.Timestamp[:], hash[:])
	// timestamp corresponds to decrypted timestamp from c_ts
	if err != nil {
		device.Log.Verbosef("ConsumeMessageInitiation: 2nd aead decrypt failed")
		return nil
	}
	MixHash(&hash, &hash, msg.Timestamp[:])
	// hash == h4 == h(<h3, c_ts>)

	// protect against replay & flood
	/*
		replay := !timestamp.After(handshake.lastTimestamp)
		flood := time.Since(handshake.lastInitiationConsumption) <= HandshakeInitationRate
		if replay {
			device.log.Verbosef("%v - ConsumeMessageInitiation: handshake replay @ %v", peer, timestamp)
			return nil
		}
		if flood {
			device.log.Verbosef("%v - ConsumeMessageInitiation: handshake flood", peer)
			return nil
		}
	*/

	// update handshake state
	handshake.hash = hash                     // h4
	handshake.chainKey = chainKey             // c3
	handshake.remoteIndex = msg.Sender        // sid_I
	handshake.remoteEphemeral = msg.Ephemeral // epk_I
	/*
		if timestamp.After(handshake.lastTimestamp) {
			handshake.lastTimestamp = timestamp
		}
		now := time.Now()
		if now.After(handshake.lastInitiationConsumption) {
			handshake.lastInitiationConsumption = now
		}
	*/
	handshake.state = handshakeInitiationConsumed

	setZero(hash[:])
	setZero(chainKey[:])

	// it's fine to return device.peer as we have checked that the public key matches
	return device.Peer
}

func (device *Device) CreateMessageResponse(peer *Peer) (*MessageResponse, error) {
	handshake := &peer.Handshake

	if handshake.state != handshakeInitiationConsumed {
		return nil, errors.New("handshake initiation must be consumed first")
	}

	// assign index

	var err error
	// device.indexTable.Delete(handshake.localIndex)
	// handshake.localIndex, err = device.indexTable.NewIndexForHandshake(peer, handshake)
	handshake.localIndex, err = randUint32()
	if err != nil {
		return nil, err
	}

	var msg MessageResponse
	msg.Type = MessageResponseType
	msg.Sender = handshake.localIndex    // sid_R
	msg.Receiver = handshake.remoteIndex // sid_I

	// create ephemeral key

	handshake.localEphemeral, err = NewPrivateKey()
	if err != nil {
		return nil, err
	}
	// handshake.localEphemeral == ek_R
	msg.Ephemeral = handshake.localEphemeral.PublicKey()
	// msg.Ephemeral == epk_R
	// handshake.hash == h4
	// handshake.chainKey == c3
	handshake.mixHash(msg.Ephemeral[:])
	// handshake.hash == h5
	handshake.mixKey(msg.Ephemeral[:])
	// handshake.chainKey == c4

	func() {
		ss := handshake.localEphemeral.SharedSecret(handshake.remoteEphemeral)
		// ss == (g^ek_I)^ek_R
		handshake.mixKey(ss[:])
		// handshake.chainKey == c5
		ss = handshake.localEphemeral.SharedSecret(handshake.RemoteStatic)
		// ss == (g^k_I)^ek_R
		handshake.mixKey(ss[:])
		// handshake.chainKey == c6
	}()

	// add preshared key

	var tau [blake2s.Size]byte
	var key [chacha20poly1305.KeySize]byte

	KDF3(
		&handshake.chainKey,
		&tau,
		&key,
		handshake.chainKey[:],     // c6
		handshake.PresharedKey[:], // psk
	)
	// handshake.chainKey == c7
	// tau == pi
	// key == k3

	handshake.mixHash(tau[:])
	// handshake.hash == h6

	func() {
		aead, _ := chacha20poly1305.New(key[:])
		aead.Seal(msg.Empty[:0], ZeroNonce[:], nil, handshake.hash[:])
		// msg.Empty == c_empty
		handshake.mixHash(msg.Empty[:])
		// handshake.hash == hash(<h6, c_empty>)
		// note that there is no abbreviation defined for this result
	}()

	handshake.state = handshakeResponseCreated

	return &msg, nil
}

func (device *Device) ConsumeMessageResponse(msg *MessageResponse) *Peer {
	if msg.Type != MessageResponseType {
		return nil
	}

	// previously: lookup handshake by receiver
	/*
		lookup := device.indexTable.Lookup(msg.Receiver)
		handshake := lookup.handshake
		if handshake == nil {
			return nil
		}
	*/
	// simplified: check whether localIndex matches:
	handshake := &device.Peer.Handshake
	// handshake.localIndex == sid_I
	// handshake.hash == h4
	// handshake.chainKey == c3
	if handshake.localIndex != msg.Receiver {
		return nil
	}

	var (
		hash     [blake2s.Size]byte
		chainKey [blake2s.Size]byte
	)

	ok := func() bool {

		// finish 3-way DH

		MixHash(&hash, &handshake.hash, msg.Ephemeral[:])
		// hash == h5 == hash(<h4, epk_R>)
		MixKey(&chainKey, &handshake.chainKey, msg.Ephemeral[:])
		// chainKey == c4

		func() {
			ss := handshake.localEphemeral.SharedSecret(msg.Ephemeral)
			// ss == epk_R^k_I == (g^ek_R)^ek_I
			MixKey(&chainKey, &chainKey, ss[:])
			// chainKey == c5
			setZero(ss[:])
		}()

		func() {
			ss := device.StaticIdentity.PrivateKey.SharedSecret(msg.Ephemeral)
			// ss == (g^ek_R)^k_I
			MixKey(&chainKey, &chainKey, ss[:])
			// chainKey == c6
			setZero(ss[:])
		}()

		// add preshared key (psk)

		var tau [blake2s.Size]byte
		var key [chacha20poly1305.KeySize]byte
		KDF3(
			&chainKey,
			&tau,
			&key,
			chainKey[:],               // c6
			handshake.PresharedKey[:], // psk
		)
		// chainKey == c7
		// tau == pi
		// key == k3
		MixHash(&hash, &hash, tau[:])
		// hash == h6

		// authenticate transcript

		aead, _ := chacha20poly1305.New(key[:]) // k3
		_, err := aead.Open(nil, ZeroNonce[:], msg.Empty[:], hash[:])
		// only check whether c_empty can be decrypted
		if err != nil {
			device.Log.Verbosef("Cannot decrypt empty message")
			return false
		}
		MixHash(&hash, &hash, msg.Empty[:])
		// hash == hash(<h6, c_empty>)
		// note that there is no abbreviation defined for this result
		return true
	}()

	if !ok {
		return nil
	}

	// update handshake state
	handshake.hash = hash              // hash(<h6, c_empty>)
	handshake.chainKey = chainKey      // c7
	handshake.remoteIndex = msg.Sender // sid_R
	handshake.state = handshakeResponseConsumed

	setZero(hash[:])
	setZero(chainKey[:])

	// it's fine to return device.peer as we have checked that local index matches
	return device.Peer
}

/* Derives a new keypair from the current handshake state
 *
 */
func (peer *Peer) BeginSymmetricSession() error {
	// device := peer.device
	handshake := &peer.Handshake

	// derive keys

	var isInitiator bool
	var sendKey [chacha20poly1305.KeySize]byte
	var recvKey [chacha20poly1305.KeySize]byte

	if handshake.state == handshakeResponseConsumed {
		// handshake.chainKey == c7
		KDF2(
			&sendKey,
			&recvKey,
			handshake.chainKey[:],
			nil,
		)
		// sendKey == kdf1(c7) == k_IR
		// recvKey == kdf2(c7) == k_RI
		isInitiator = true
	} else if handshake.state == handshakeResponseCreated {
		// handshake.chainKey == c7
		KDF2(
			&recvKey,
			&sendKey,
			handshake.chainKey[:],
			nil,
		)
		// recvKey == kdf1(c7) == k_IR
		// sendKey == kdf2(c7) == k_RI
		isInitiator = false
	} else {
		return fmt.Errorf("invalid state for keypair derivation: %v", handshake.state)
	}

	// zero handshake

	setZero(handshake.chainKey[:])
	setZero(handshake.hash[:]) // Doesn't necessarily need to be zeroed. Could be used for something interesting down the line.
	setZero(handshake.localEphemeral[:])
	peer.Handshake.state = handshakeZeroed

	// create AEAD instances

	keypair := new(Keypair)
	keypair.send, _ = chacha20poly1305.New(sendKey[:])    // k_IR or k_RI
	keypair.receive, _ = chacha20poly1305.New(recvKey[:]) // k_RI or k_IR

	setZero(sendKey[:])
	setZero(recvKey[:])

	keypair.created = time.Now()
	keypair.replayFilter.Reset()
	keypair.isInitiator = isInitiator
	keypair.localIndex = peer.Handshake.localIndex
	keypair.remoteIndex = peer.Handshake.remoteIndex

	// remap index

	// device.indexTable.SwapIndexForKeypair(handshake.localIndex, keypair)
	handshake.localIndex = 0

	// rotate key pairs
	// instead of using keypairs, we directly set the current keypair:
	peer.keypair = keypair
	/*
		keypairs := &peer.keypairs
		keypairs.Lock()
		defer keypairs.Unlock()

		previous := keypairs.previous
		next := keypairs.loadNext()
		current := keypairs.current

		if isInitiator {
			if next != nil {
				keypairs.storeNext(nil)
				keypairs.previous = next
				device.DeleteKeypair(current)
			} else {
				keypairs.previous = current
			}
			device.DeleteKeypair(previous)
			keypairs.current = keypair
		} else {
			keypairs.storeNext(keypair)
			device.DeleteKeypair(next)
			keypairs.previous = nil
			device.DeleteKeypair(previous)
		}
	*/
	return nil
}
