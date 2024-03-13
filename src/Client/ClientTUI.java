package Client;

import Exceptions.ClientUnavailableException;
import Protocol.Protocol;


import java.io.*;
import java.net.InetAddress;
import java.net.UnknownHostException;

/**
 * Client TUI class
 * The interface is used to communication between clients and server.
 */

public class ClientTUI {
    private final BufferedReader reader;
    private final PrintWriter writer;
    private Client client;


    /**
     * Constructor of the client TUI class
     * @param client the client
     */
    public ClientTUI(Client client) {
        reader = new BufferedReader(new InputStreamReader(System.in));
        writer = new PrintWriter(System.out, true);
        this.client = client;
    }

    /**
     * Print the message on console for client.
     * @param message input message
     */
    public void showMessage(String message) {
        writer.println(message);
    }

    /**
     * The menu show the different protocol that client could select.
     */
    public void menu() {
        final String Menu = String.format("WELCOME TO DOTS AND BOXES CLIENT \n") +
                String.format("ENTER A COMMAND, PLEASE! \n"
                        + "[QUEUE]....... JOIN A NEW GAME \n"
                        + "[LIST] ....... LIST OF ACTIVE PLAYERS \n"
                        + "[QUIT] ....... EXIT THE SERVER");

        showMessage(Menu);
    }

    /**
     * Return the IP address that client entered to connect to server.
     * @return IP address.
     */
    public InetAddress getIP() throws IOException {
        InetAddress address;
        showMessage("PLEASE, ENTER SERVER ADDRESS: ");

        try {
            String userInput = reader.readLine();
            address = InetAddress.getByName(userInput);
            return address;
        } catch (UnknownHostException | NullPointerException e) {
            showMessage("ERROR: Host is unknown!");
            getIP();

        }
        return null;
    }

    /**
     * Return the port number that client entered to connect to server
     * @return port number
     */
    public int getPort() throws IOException {
        showMessage("ENTER A PORT NUMBER : ");
        int portNumber = 0;
        try {
            portNumber = Integer.parseInt(reader.readLine());
            return portNumber;
        } catch (NumberFormatException | NullPointerException e) {
            showMessage("ENTER A \"NUMBER\" PLEASE ");
            getPort();
        }
        return 0;
    }

    /**
     * Return string message (answer) that is the result of the input string.
     * @param input The input string.
     * @return message (answer).
     */
    public String inputString(String input) throws IOException {
        showMessage(input);
        String mess = reader.readLine().toUpperCase();
        return mess;
    }

    /**
     * Handle the protocol from client
     */
    public void handleUserProtocol() throws IOException {
        menu();
        String input = reader.readLine().toUpperCase();
        boolean validProtocol = false;

         while (!validProtocol) {
             switch (input) {
                 case Protocol.QUEUE:
                     client.setupNEWGAME();
                     client.sendProtocol(Protocol.QUEUE);
                     validProtocol = true;
                     break;
                 case Protocol.LIST:
                     client.sendProtocol(Protocol.LIST);
                     validProtocol = true;
                     break;
                 case Protocol.QUIT:
                    client.handleQUIT();
                    validProtocol = true;
                     break;
                 default:
                     showMessage("[ERROR]" + " INVALID PROTOCOL. PLEASE TRY AGAIN! ");
                     menu();
                     input = reader.readLine().toUpperCase();
             }
         }

    }

    /**
     * Start the ClientTUI with asking for an IP and a Port number.
     */
    public void start() throws IOException {
        try {
            if (!client.connect(getIP(), getPort())) {
                showMessage("[ERROR] CONNECTION LOST. PLEASE TRY AGAIN! ");
                start();
            }
        } catch (UnknownHostException | ClientUnavailableException e) {
            showMessage("[ERROR] " + e.getMessage());
            start();
        }
    }

    /**
     * Main method for the TUI
     * @param args
     * @throws IOException
     */
    public static void main(String[] args) throws IOException {
        ClientTUI tui = new ClientTUI(new Client());
        tui.start();
    }
}
