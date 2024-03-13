package Server;

import Protocol.Protocol;

import java.io.IOException;
import java.net.Socket;


/**
 * The server connection class to connect the server side to the client side.
 */
public class ServerConnection extends SocketConnection {

    public ClientHandler chandler;


    /**
     * Instantiates a new Server connection.
     *
     * @param socket the socket
     */
    protected ServerConnection(Socket socket) throws IOException {
        super(socket);
    }

    /**
     * Send a chat message to the server.
     *
     * @param message the message
     */
    public void sendMsg(String message) {
        System.out.println(message);
        super.sendMessage(message);
    }

    /**
     * Handles a message received from the connection.
     *
     * @param msg the message received from the connection
     */
    @Override
    protected void handleMessage(String msg) {
        String message = msg.split(Protocol.SEPARATOR)[0];
        switch (message) {
            case Protocol.HELLO:
                if (msg.split(Protocol.SEPARATOR).length < 2) {
                    chandler.sendMessage("Wrong message length. Try again using the protocol.");
                    break;
                }
                if (chandler.loggedIn) {
                    chandler.sendMessage(Protocol.ERROR);
                    break;
                }
                chandler.receiveMessage(msg);
                break;
            case Protocol.LOGIN:
                if (msg.split(Protocol.SEPARATOR).length < 2) {
                    chandler.sendMessage("Wrong message length. Try again using the protocol.");
                    break;
                }
                if (!chandler.helloed) {
                    chandler.sendMessage(Protocol.ERROR);
                    break;
                }
                chandler.receiveMessage(msg);
                break;
            case Protocol.LIST:
            case Protocol.QUEUE:
                if (!chandler.helloed || !chandler.loggedIn) {
                    chandler.sendMessage(Protocol.ERROR);
                    break;
                }
                chandler.receiveMessage(msg);
                break;
            case Protocol.MOVE:
                if (msg.split(Protocol.SEPARATOR).length < 2) {
                    chandler.sendMessage("Wrong message length. Try again using the protocol.");
                    break;
                }
                if (!chandler.helloed || !chandler.loggedIn || !chandler.inGame) {
                    chandler.sendMessage(Protocol.ERROR);
                    break;
                }
                chandler.receiveMessage(msg);
                break;
            default:
                chandler.sendMessage("Wrong message format. Try again using the protocol.");
                break;
        }
    }

    /**
     * Handles a disconnect from the connection, i.e., when the connection is closed.
     */
    @Override
    protected void handleDisconnect() {
        this.chandler.handleDisconnect();
        super.close();
    }

    /**
     * Start the connection.
     */
    public void start() {
        super.start();
    }
}
