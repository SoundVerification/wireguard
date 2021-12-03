package main

import (
	"encoding/base64"
	"flag"
	"fmt"
	"math/rand"
	"os"
	"os/signal"
	"syscall"

	"golang.org/x/net/ipv4"
	"golang.org/x/net/ipv6"

	"wireguard-gobra/wireguard/conn"
	"wireguard-gobra/wireguard/device"
	"wireguard-gobra/wireguard/endpoint"
	"wireguard-gobra/wireguard/library"

	"wireguard-gobra/wireguard/initiator"
	"wireguard-gobra/wireguard/log"
	"wireguard-gobra/wireguard/responder"
)

const logLevel = log.LogLevelVerbose

const (
	ExitSetupSuccess = 0
	ExitSetupFailed  = 1
)

type Config struct {
	IsInitiator            bool
	UseOtherImplementation bool
	UseStandardIO          bool
	InterfaceName          string
	Port                   uint16
	IpVersion              int
	PrivateKey             string
	PublicKey              string
	PeerEndpoint           string // <address>:<port>, e.g. "127.0.0.1:57654" (IPv4) or "[::1]:57950" (IPv6)
	PeerPublicKey          string
}

func parseArgs() Config {
	isInitiatorPtr := flag.Bool("isInitiator", false, "specifies whether this instance should act as an initiator")
	useStandardIOPtr := flag.Bool("useStandardIO", false, "specifies whether input and output should be written to / taken from STDOUT and STDIN, respectively, or whether an interface should be created")
	interfaceNamePtr := flag.String("interfaceName", "", "interface name that should be used if 'useStandardIO' is set to false")
	portPtr := flag.Uint("port", 0, "port for local endpoint")
	ipVersionPtr := flag.Int("ipVersion", ipv4.Version, fmt.Sprintf("IP version, has to be either %v or %v", ipv4.Version, ipv6.Version))
	privateKeyPtr := flag.String("privateKey", "", "base64 encoded private key of this protocol participant")
	publicKeyPtr := flag.String("publicKey", "", "base64 encoded public key of this protocol participant")
	peerEndpointPtr := flag.String("endpoint", "", "<address>:<port> of the peer's endpoint")
	peerPublicKeyPtr := flag.String("peerPublicKey", "", "base64 encoded public key of the peer")
	useOtherImplementation := flag.Bool("useOtherImplementation", false, "specifies whether the second implementation should be run")

	flag.Parse()

	config := Config{
		IsInitiator:            *isInitiatorPtr,
		UseOtherImplementation: *useOtherImplementation,
		UseStandardIO:          *useStandardIOPtr,
		InterfaceName:          *interfaceNamePtr,
		Port:                   uint16(*portPtr),
		IpVersion:              *ipVersionPtr,
		PrivateKey:             *privateKeyPtr,
		PublicKey:              *publicKeyPtr,
		PeerEndpoint:           *peerEndpointPtr,
		PeerPublicKey:          *peerPublicKeyPtr,
	}
	return config
}

func main() {

	// parse args
	config := parseArgs()

	privateKey, publicKey, peerPublicKey, err := parseKeys(config)

	logger := log.NewLogger(
		logLevel,
		fmt.Sprintf("(%s) ", config.InterfaceName),
	)
	logger.Verbosef("Starting wireguard-gobra")

	/** inputChannel sends data from TUN device or STDIN to device which should forward it to peer */
	inputChannel := make(chan []byte)
	/** outputChannel sends data from device (which in turn received the data from the peer) to the TUN device or STDOUT */
	outputChannel := make(chan []byte)

	// create input/output
	var ep endpoint.Endpoint
	if config.UseStandardIO {
		ep = endpoint.NewStandardIO(inputChannel, outputChannel, logger)
	} else {
		ep, err = endpoint.NewTUN(inputChannel, outputChannel, config.InterfaceName, endpoint.DefaultMTU, logger)
	}

	if err != nil {
		logger.Errorf("Creating endpoint has failed: ", err)
		os.Exit(ExitSetupFailed)
		return
	}

	bind := conn.NewDefaultBind()
	peerEndpoint, err := bind.ParseEndpoint(config.PeerEndpoint)
	if err != nil {
		fmt.Println("error while parsing endpoint", err)
		return
	}

	// create device
	deviceInstance := device.NewDevice(inputChannel, outputChannel, config.IsInitiator, bind, config.IpVersion, config.Port, peerEndpoint, privateKey, publicKey, peerPublicKey, endpoint.DefaultMTU, logger, !config.UseStandardIO)

	var protocol func(*device.Device)
	var useOurImplementation = !config.UseOtherImplementation
	if useOurImplementation {
		protocol = func(d *device.Device) {

			libState, hsInfo, ok := library.NewLibraryState(d)
			if !ok {
				return
			}

			rid := rand.Uint32()
			if d.IsInitiator {
				w := &initiator.Initiator{
					LibState:      libState,
					HandshakeInfo: hsInfo,
				}
				_ = w
				w.RunInitiator(rid, 0, 1)
			} else {
				w := &responder.Responder{
					LibState:      libState,
					HandshakeInfo: hsInfo,
				}
				_ = w
				w.RunResponder(rid, 0, 1)
			}
		}
	} else {
		protocol = func(d *device.Device) {
			if d.IsInitiator {
				d.RunProtocolInitiator()
			} else {
				d.RunProtocolResponder()
			}
		}
	}

	// start listening
	deviceInstance.Start(protocol)
	ep.Listen()

	// wait for program to terminate
	term := make(chan os.Signal, 1)
	signal.Notify(term, syscall.SIGTERM)
	signal.Notify(term, os.Interrupt)

	select {
	case <-term:
	case <-ep.Wait():
	}

	deviceInstance.Close()
	<-deviceInstance.Wait()

	logger.Verbosef("Shutting down")
}

func parseKeys(config Config) (privateKey device.NoisePrivateKey, publicKey device.NoisePublicKey, peerPublicKey device.NoisePublicKey, err error) {
	// note that `wg genkey` encodes the key in base64
	encoding := base64.StdEncoding
	privateKeySlice, err := encoding.DecodeString(config.PrivateKey)
	if err != nil {
		return privateKey, publicKey, peerPublicKey, err
	}

	publicKeySlice, err := encoding.DecodeString(config.PublicKey)
	if err != nil {
		return privateKey, publicKey, peerPublicKey, err
	}

	peerPublicKeySlice, err := encoding.DecodeString(config.PeerPublicKey)
	if err != nil {
		return privateKey, publicKey, peerPublicKey, err
	}

	copy(privateKey[:], privateKeySlice)
	copy(publicKey[:], publicKeySlice)
	copy(peerPublicKey[:], peerPublicKeySlice)

	return privateKey, publicKey, peerPublicKey, nil
}
