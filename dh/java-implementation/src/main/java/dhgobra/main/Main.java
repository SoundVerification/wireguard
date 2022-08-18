package dhgobra.main;

import java.util.Base64;
import java.util.Random;
import java.net.SocketException;
import org.apache.commons.cli.*;
import dhgobra.library.Library;
import dhgobra.responder.Responder;

public class Main {
    public static void main(String[] args) {

        Options options = new Options();
        

        Option isInitiatorOpt = new Option("i", "isInitiator", false, "specifies whether this instance should act as an initiator");
        options.addOption(isInitiatorOpt);

        Option portOpt = new Option("p", "port", true, "port number for listening to UDP traffic");
        portOpt.setRequired(true);
        options.addOption(portOpt);

        Option privateKeyOpt = new Option("sk", "privateKey", true, "base64 encoded private key of this protocol participant");
        privateKeyOpt.setRequired(true);
        options.addOption(privateKeyOpt);

        Option peerPublicKeyOpt = new Option("pk", "peerPublicKey", true, "base64 encoded public key of the peer");
        peerPublicKeyOpt.setRequired(true);
        options.addOption(peerPublicKeyOpt);

        try {
            CommandLineParser parser = new DefaultParser();
            CommandLine cmd = parser.parse(options, args);
            byte[] privateKey = parseKey(cmd.getOptionValue("privateKey"));
            byte[] peerPublicKey = parseKey(cmd.getOptionValue("peerPublicKey"));

            Library lib = new Library(Integer.parseInt(cmd.getOptionValue("port")), privateKey, peerPublicKey);

            int rid = new Random().nextInt();
            boolean success = false;
            if (cmd.hasOption("isInitiator")) {
                // not implemented
                System.out.println("Initiator is currently not implemented");
            } else {
                success = new Responder(lib, rid).Run();
            }
            lib.close();
            if (success) {
                System.exit(0);
            } else {
                System.exit(1);
            }
        } catch (ParseException e) {
            System.out.println(e.getMessage());
            System.exit(-1);
        } catch (SocketException e) {
            System.out.println(e.getMessage());
            System.exit(-1);
        }
    }

    private static byte[] parseKey(String input) {
        return Base64.getDecoder().decode(input);
    }
}
