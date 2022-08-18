package dhgobra.library;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Random;
import java.net.*;
import java.security.KeyFactory;
import java.security.NoSuchAlgorithmException;
import java.security.InvalidKeyException;
import java.security.PublicKey;
import java.security.PrivateKey;
import java.security.Signature;
import java.security.SignatureException;
import java.security.spec.EdECPoint;
import java.security.spec.EdECPublicKeySpec;
import java.security.spec.InvalidKeySpecException;
import java.security.spec.NamedParameterSpec;
import java.security.spec.EdECPrivateKeySpec;
import java.security.spec.PKCS8EncodedKeySpec;
import javax.crypto.spec.SecretKeySpec;
import java.security.spec.X509EncodedKeySpec;
import java.io.IOException;
// import org.bouncycastle.crypto.params.Ed25519PublicKeyParameters;
// import org.bouncycastle.crypto.Signer;
// import org.bouncycastle.crypto.signers.Ed25519Signer;

public final class Library {
    private final DatagramSocket socket;
    private boolean connClosed;
    private final byte[] pkA;
    private final byte[] skB;

    private final int MaxDataSize = 1024;
    private final byte[] recvBuffer = new byte[MaxDataSize];
    private final DatagramPacket recvPacket = new DatagramPacket(recvBuffer, recvBuffer.length);
    private final int NonceLength = 24;

    // based on RFC 3526
    private final int GroupGenerator = 2;
    private final String GroupSizeString = "FFFFFFFFFFFFFFFFC90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B139B22514A08798E3404DDEF9519B3CD3A431B302B0A6DF25F14374FE1356D6D51C245E485B576625E7EC6F44C42E9A637ED6B0BFF5CB6F406B7EDEE386BFB5A899FA5AE9F24117C4B1FE649286651ECE45B3DC2007CB8A163BF0598DA48361C55D39A69163FA8FD24CF5F83655D23DCA3AD961C62F356208552BB9ED529077096966D670C354E4ABC9804F1746C08CA18217C32905E462E36CE3BE39E772C180E86039B2783A2EC07A28FB5C55DF06F4C52C9DE2BCBF6955817183995497CEA956AE515D2261898FA051015728E5A8AACAA68FFFFFFFFFFFFFFFF";

    public final int DHHalfKeyLength = 256;
    private final int SignatureOverhead = 64;
    private final byte Msg2Tag = 0;
    private final byte Msg3Tag = 1;

    private InetAddress lastReceivedAddress;
    private int lastReceivedPort;

    public Library(int portNr, byte[] privateKey, byte[]peerPublicKey) throws SocketException {
        socket = new DatagramSocket(portNr);
        connClosed = false;
        pkA = peerPublicKey;
        skB = privateKey;
    }

    public boolean send(byte[] data) {
        DatagramPacket packet = new DatagramPacket(data, data.length, lastReceivedAddress, lastReceivedPort);
        try {
            socket.send(packet);
            return true;
        } catch (IOException e) {
            return false;
        }
    }

    public byte[] recv() {
        try {
            socket.receive(recvPacket);
            lastReceivedAddress = recvPacket.getAddress();
            lastReceivedPort = recvPacket.getPort();
            byte[] res = Arrays.copyOf(recvPacket.getData(), recvPacket.getLength());
            return res;
        } catch (IOException e) {
            return null;
        }
    }

    public void close() {
        connClosed = true;
        socket.close();
    }

    public Config GetConfig() {
        return new Config(0, 1, GetInitPublicKey(), GetRespSecretKey());
    }

    public byte[] GetInitPublicKey() {
        return pkA;
    }

    public byte[] GetRespSecretKey() {
        return skB;
    }

    public byte[] createNonce() {
        Random rand = new Random();
        byte[] res = new byte[NonceLength];
        rand.nextBytes(res);
        return res;
    }

    // arg is big-endian
    private byte[] expModWithBigIntBase(BigInteger base, byte[] exp) {
        // prepare mod argument:
        byte[] groupSizeBytes = convertFromHex(GroupSizeString);
        if (groupSizeBytes == null) {
            return null;
        }
        // "1" indicates that the byte array should be intepreted as an unsigned integer
        BigInteger mod = new BigInteger(1, groupSizeBytes);

        // prepare exp argument:
        // "1" indicates that the byte array should be intepreted as an unsigned integer
        BigInteger expInt = new BigInteger(1, exp);

        // perform calculation:
        BigInteger r = base.modPow(expInt, mod);

        // extract result:
        byte[] rBytes = r.toByteArray();
        if (rBytes.length < DHHalfKeyLength) {
            // prepend zeros:
            byte[] res = new byte[DHHalfKeyLength];
            System.arraycopy(rBytes, 0, res, DHHalfKeyLength - rBytes.length, rBytes.length);
            return res;
        } else if (rBytes.length > DHHalfKeyLength) {
            byte[] res = new byte[DHHalfKeyLength];
            System.arraycopy(rBytes, rBytes.length - DHHalfKeyLength, res, 0, DHHalfKeyLength);
            return res;
        } else {
            return rBytes;
        }
    }

    // args are big-endian
    private byte[] expMod(byte[] base, byte[] exp) {
        // "1" indicates that the byte array should be intepreted as an unsigned integer
        BigInteger baseInt = new BigInteger(1, base);
        return expModWithBigIntBase(baseInt, exp);
    }

    // arg is big-endian
    public byte[] dhExp(byte[] exp) {
        BigInteger g = BigInteger.valueOf(GroupGenerator);
        return expModWithBigIntBase(g, exp);
    }

    // args are big-endian
    public byte[] dhSharedSecret(byte[] dhSecret, byte[] dhHalfKey) {
        return expMod(dhHalfKey, dhSecret);
    }

    public byte[] sign(byte[] data, byte[] sk) {
        try {
            // prepare sk:
            // first 32 bytes of sk are the secret key and the following 32 bytes are the public key
            byte[] secretKeyPart = Arrays.copyOf(sk, 32);
            KeyFactory kf = KeyFactory.getInstance("Ed25519");
            final EdECPrivateKeySpec keySpec = new EdECPrivateKeySpec(new NamedParameterSpec("ED25519"), secretKeyPart);
            PrivateKey sKey = kf.generatePrivate(keySpec);

            Signature sig = Signature.getInstance("Ed25519");
            sig.initSign(sKey);
            sig.update(data);
            byte[] signature = sig.sign();
            byte[] res = new byte[signature.length + data.length];
            System.arraycopy(signature, 0, res, 0, signature.length);
            System.arraycopy(data, 0, res, signature.length, data.length);
            return res;
        } catch (NoSuchAlgorithmException e) {
            System.out.println(e.toString());
        } catch (InvalidKeySpecException e) {
            System.out.println(e.toString());
        } catch (InvalidKeyException e) {
            System.out.println(e.toString());
        } catch (SignatureException e) {
            System.out.println(e.toString());
        }
        return null;
    }

    public byte[] open(byte[] signedData, byte[] pk) {
        if (signedData.length < SignatureOverhead) {
            return null;
        }
        byte[] signature = Arrays.copyOf(signedData, SignatureOverhead);
        byte[] data = new byte[signedData.length - SignatureOverhead];
        System.arraycopy(signedData, SignatureOverhead, data, 0, signedData.length - SignatureOverhead);

        /* the following code also works but requires BouncyCastle (implementation group: 'org.bouncycastle', name: 'bcprov-jdk15on', version: '1.70')
        Ed25519PublicKeyParameters publicKey = new Ed25519PublicKeyParameters(pk);
        Signer signer = new Ed25519Signer();
        signer.init(false, publicKey);
        signer.update(signedData, SignatureOverhead, signedData.length - SignatureOverhead);
        boolean success = signer.verifySignature(signature);
        */
        try {
            // prepare pk (taken from https://stackoverflow.com/a/66442530/1990080):
            KeyFactory kf = KeyFactory.getInstance("Ed25519");
            // determine if x was odd.
            boolean xisodd = false;
            int lastbyteInt = pk[pk.length - 1];
            if ((lastbyteInt & 255) >> 7 == 1) {
                xisodd = true;
            }
            // make sure most significant bit will be 0 - after reversing.
            pk[pk.length - 1] &= 127;
            // apparently we must reverse the byte array...
            pk = reverseBytes(pk);
            BigInteger y = new BigInteger(1, pk);
            NamedParameterSpec paramSpec = new NamedParameterSpec("Ed25519");
            EdECPoint ep = new EdECPoint(xisodd, y);
            EdECPublicKeySpec pubSpec = new EdECPublicKeySpec(paramSpec, ep);
            PublicKey pKey = kf.generatePublic(pubSpec);

            Signature sig = Signature.getInstance("Ed25519");
            sig.initVerify(pKey);
            sig.update(data);
            boolean success = sig.verify(signature);
            if (!success) {
                return null;
            }
            return data;
        } catch (NoSuchAlgorithmException e) {
            System.out.println(e.toString());
        } catch (InvalidKeySpecException e) {
            System.out.println(e.toString());
        } catch (InvalidKeyException e) {
            System.out.println(e.toString());
        } catch (SignatureException e) {
            System.out.println(e.toString());
        }
        return null;
    }

    public String convertToHex(byte[] data) {
        StringBuilder sb = new StringBuilder();
        for (byte b : data) {
            sb.append(String.format("%02x", b));
        }
        return sb.toString();
    }

    public byte[] convertFromHex(String hexString) {
        byte[] arr = new byte[hexString.length() / 2];
        char[] chars = hexString.toCharArray();
        for(int i = 0; i < hexString.length() - 1; i += 2) {
            String curr = new String (chars, i, 2);
            arr[i / 2] = (byte) Integer.parseInt(curr, 16);
        }
        return arr;
    }

    public byte[] reverseBytes(byte[] input) {
        byte[] res = new byte[input.length];
        for (int i = 0; i < input.length; i++) {
            res[i] = input[input.length - 1 - i];
        }
        return res;
    }

    public Msg1 unmarshalMsg1(byte[] data) {
        if (data == null || data.length < DHHalfKeyLength) {
            System.out.println("Unmarshalling msg1 failed");
            return null;
        }
        return new Msg1(Arrays.copyOf(data, DHHalfKeyLength));
    }

    public byte[] marshalMsg2(Msg2 msg2) {
        if (msg2 == null || msg2.X == null || msg2.Y == null) {
            return null;
        }

        byte[] tagBytes = uint32ToBytes(Msg2Tag);
        byte[] idABytes = uint32ToBytes(msg2.idA);
        byte[] idBBytes = uint32ToBytes(msg2.idB);
        if (tagBytes == null || idABytes == null || idBBytes == null) {
            return null;
        }

        byte[] data = new byte[msg2.X.length + msg2.Y.length + 12];
        System.arraycopy(tagBytes, 0, data, 0, 4);
        // note that idB occurs before idA in the 2nd message:
        System.arraycopy(idBBytes, 0, data, 4, 4);
        System.arraycopy(idABytes, 0, data, 8, 4);
        System.arraycopy(msg2.X, 0, data, 12, msg2.X.length);
        System.arraycopy(msg2.Y, 0, data, msg2.X.length + 12, msg2.Y.length);
        return data;
    }

    public Msg3 unmarshalMsg3(byte[] data) {
        if (data == null || data.length < 2 * DHHalfKeyLength + 12) {
            return null;
        }

        byte[] tagBytes = new byte[4];
        byte[] idABytes = new byte[4];
        byte[] idBBytes = new byte[4];
        byte[] Y = new byte[DHHalfKeyLength];
        byte[] X = new byte[DHHalfKeyLength];
        System.arraycopy(data, 0, tagBytes, 0, 4);
        System.arraycopy(data, 4, idABytes, 0, 4);
        System.arraycopy(data, 8, idBBytes, 0, 4);
        // note that Y occurs before X in the 3rd message:
        System.arraycopy(data, 12, Y, 0, DHHalfKeyLength);
        System.arraycopy(data, DHHalfKeyLength + 12, X, 0, DHHalfKeyLength);

        long tag = bytesToUint32(tagBytes);
        long idA = bytesToUint32(idABytes);
        long idB = bytesToUint32(idBBytes);

        if (!longInRange(tag) || !longInRange(idA) || !longInRange(idB)) {
            return null;
        }
        if (tag != Msg3Tag) {
            // unexpected message tag in msg3
            return null;
        }

        return new Msg3((int) idA, (int) idB, X, Y);
    }

    private boolean longInRange(long value) {
        if (value < 0 || value > 0xFFFFFFFFL) {
            return false;
        }
        return true;
    }

    private byte[] uint32ToBytes(long value) {
        if (!longInRange(value)) {
            return null;
        }
        return new byte[] {
            (byte) ((value >> 24) & 0xff),
            (byte) ((value >> 16) & 0xff),
            (byte) ((value >> 8) & 0xff),
            (byte) ((value >> 0) & 0xff),
        };
    }

    private long bytesToUint32(byte[] data) {
        if (data == null || data.length != 4) {
            return -1;
        }
        return (data[0] << 24) + (data[1] << 16) + (data[2] << 8) + data[3];
    }

    public void notMatchX() {
        System.out.println("Received X does not match");
    }

    public void notMatchY() {
        System.out.println("Received Y does not match");
    }

    public void success(byte[] sharedSecret) {
        System.out.println("Initiator & responder agreed on shared secret " + convertToHex(sharedSecret));
    }
}
