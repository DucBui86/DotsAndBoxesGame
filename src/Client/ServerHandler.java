package Client;

import Exceptions.ProtocolException;
import Protocol.Protocol;

import java.io.*;
import java.net.Socket;
import java.net.SocketException;

/**
 * The server handler class for the client side
 */
public class ServerHandler implements Runnable {
    private BufferedReader br;
    private Socket socket;
    private Client client;


    /**
     * Instantiates a server handler object
     * @param socket the socket
     * @param client the client connected to the handler
     */
    public ServerHandler(Socket socket, Client client) throws IOException {
        this.client = client;
        this.socket = socket;

    }

    /**
     * Handling the messages coming from the server.
     * @param input the message
     */
    public void handleProtocol(String input) throws IOException, ProtocolException {
        String[] split = input.split(Protocol.SEPARATOR);

        switch (split[0]) {
            case Protocol.HELLO:
                client.handlerHello();
                break;
            case Protocol.LOGIN:
            case Protocol.ALREADYLOGGEDIN:
                client.handleLOGIN(input);
                break;
            case Protocol.NEWGAME:
                client.handleNEWGAME(input);
                break;
            case Protocol.MOVE:
                client.handleMOVE(input);
                break;
            case Protocol.GAMEOVER:
                client.handleGAMEOVER(input);
                break;
            case Protocol.LIST:
                client.handleLIST(input);
                break;
            case Protocol.ERROR:
                client.handleERROR(input);
                break;
            default:
                System.out.println(input);
        }
    }

    /**
     * Running the server handler on a thread.
     */
    public void run() {
        while (true) {
            try {
                this.br = new BufferedReader(new InputStreamReader(socket.getInputStream()));
                String line;
                while ((line = br.readLine()) != null) {
                    handleProtocol(line);
                }
                br.close();
            } catch (IOException | ProtocolException e) {
                try {
                    client.close();
                } catch (SocketException | OutOfMemoryError error) {
                    throw new RuntimeException(error);
                }
            }
        }
    }
}
