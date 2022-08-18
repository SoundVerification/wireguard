package main

import "encoding/base64"
import "errors"
import "flag"
import "fmt"
import "math/rand"
import "os"
import "dh-gobra/initiator"
import "dh-gobra/library"

type Config struct {
	IsInitiator            bool
	PrivateKey             string
	PeerEndpoint           string // <address>:<port>, e.g. "127.0.0.1:57654" (IPv4) or "[::1]:57950" (IPv6)
	PeerPublicKey          string
}

func parseArgs() Config {
	isInitiatorPtr := flag.Bool("isInitiator", false, "specifies whether this instance should act as an initiator")
	privateKeyPtr := flag.String("privateKey", "", "base64 encoded private key of this protocol participant")
	peerEndpointPtr := flag.String("endpoint", "", "<address>:<port> of the peer's endpoint")
	peerPublicKeyPtr := flag.String("peerPublicKey", "", "base64 encoded public key of the peer")

	flag.Parse()

	config := Config{
		IsInitiator:            *isInitiatorPtr,
		PrivateKey:             *privateKeyPtr,
		PeerEndpoint:           *peerEndpointPtr,
		PeerPublicKey:          *peerPublicKeyPtr,
	}
	return config
}

func main() {
	// parse args
	config := parseArgs()

	privateKey, peerPublicKey, err := parseKeys(config)
	if err != nil {
		os.Exit(-1)
		return
	}

	lib, err := library.NewLibState(config.PeerEndpoint, 0, 1, privateKey, peerPublicKey)
	if err != nil {
		os.Exit(-1)
		return
	}

	rid := rand.Uint32()
	if config.IsInitiator {
		err = initiator.RunInitiator(lib, rid)
	} else {
		err = errors.New("responder is currently not implemented")
	}
	lib.Close()
	if err == nil {
		os.Exit(0)
	} else {
		fmt.Println(err)
		os.Exit(1)
	}
}

func parseKeys(config Config) (privateKey [64]byte, peerPublicKey [32]byte, err error) {
	encoding := base64.StdEncoding
	privateKeySlice, err := encoding.DecodeString(config.PrivateKey)
	if err != nil {
		return privateKey, peerPublicKey, err
	}

	peerPublicKeySlice, err := encoding.DecodeString(config.PeerPublicKey)
	if err != nil {
		return privateKey, peerPublicKey, err
	}

	copy(privateKey[:], privateKeySlice)
	copy(peerPublicKey[:], peerPublicKeySlice)

	return privateKey, peerPublicKey, nil
}
