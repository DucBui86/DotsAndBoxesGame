package Server;

import Game.DotsAndBoxesGame;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.PrintWriter;
import java.net.Socket;

/**
 * The client handler class for the server side.
 */
public class ClientHandler implements Runnable {
    Socket s;
    Server server;
    BufferedReader reader;
    PrintWriter writer;
    String name;
    boolean helloed;
    boolean loggedIn;
    boolean inGame;
    boolean inQueue;
    ClientHandler opponent;
    DotsAndBoxesGame game;
    public ServerConnection connection;

    /**
     * Instantiates a new Client handler.
     *
     * @param s      the socket
     * @param server the server
     */
    public ClientHandler(Socket s, Server server) {
        this.s = s;
        this.server = server;
        this.name = "";
        this.helloed = false;
        this.loggedIn = false;
        this.inGame = false;
        this.inQueue = false;
    }

    /**
     * Running the client handler.
     */
    @Override
    public void run() {
        try {
            writer = new PrintWriter(s.getOutputStream(), true);
            reader = new BufferedReader(new InputStreamReader(s.getInputStream()));
            System.out.println("Connection established");
            name = reader.readLine();
            String line;
            while (!s.isClosed()) {
                while ((line = reader.readLine()) != null) {
                    server.handleMessage(this, line);
                }
            }
            close();
        } catch (IOException e) {
            e.printStackTrace();
            close();
        }
    }

    /**
     * Send chat message to the server connection class.
     *
     * @param message the message
     */
    public void sendMessage(String message) {
        this.connection.sendMsg(message);
    }

    /**
     * Closes the client handler.
     */
    public void close() {
        server.removeClient(this);
        try {
            System.out.println("Connection lost...");
            s.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    /**
     * Getter for the username.
     *
     * @return the username
     */
    public String getUsername() {
        return this.name;
    }

    /**
     * Receive the username.
     *
     * @param name the username
     */
    public void receiveUsername(String name) {
        this.name = name;
    }

    /**
     * Receive chat message.
     *
     * @param message the message
     */
    public void receiveMessage(String message) {
        server.handleMessage(this, message);
    }

    /**
     * Disconnect the client handler.
     */
    public void handleDisconnect() {
        close();
    }


}
