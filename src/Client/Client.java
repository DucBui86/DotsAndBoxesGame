package Client;

import Exceptions.ClientUnavailableException;
import Game.*;
import Game.ai.ComputerPlayer;
import Game.ai.NativeStrategy;
import Game.ai.SmartStrategy;
import Protocol.Protocol;

import java.io.IOException;
import java.io.PrintWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.SocketException;

/**
 * Client class.
 */
public class Client implements Runnable {
    private static final String welcome = "WELCOME TO CLIENT - SERVER";
    public final ClientTUI TUI;
    private Socket socket;
    private PrintWriter writer;
    private AbstractPlayer player;
    private String username;
    private DotsAndBoxesGame game;
    private ClientStatus status;

    /**
     * Construction of the Client class.
     */
    public Client() {
        this.TUI = new ClientTUI(this);
        this.status = ClientStatus.CONNECT_AWAITING;
    }

    /**
     * Connects the client to a server.
     * @param Ip ip address
     * @param portNumber port number
     * @return true if the connection is successful
     */
    //@ ensures conn.client != null && this.conn != null;
    public boolean connect(InetAddress Ip, int portNumber) throws ClientUnavailableException, NullPointerException {
        try {
            socket = new Socket(Ip, portNumber);
            writer = new PrintWriter(socket.getOutputStream(), true);

            sendProtocol(Protocol.HELLO, welcome);
            setStatus(ClientStatus.HELLO_AWAITING);

            TUI.showMessage("CONNECTED SUCCESSFUL");
            new Thread(this).start();
            return true;

        } catch (IOException e) {
            TUI.showMessage("[ERROR] " + e.getMessage());
            return false;
        }
    }

    /**
     * Running the thread.
     */
    public void run() {
        ServerHandler serverHandler;
        try {
            serverHandler = new ServerHandler(socket, this);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
        new Thread(serverHandler).start();
    }

    /**
     * Closes the client.
     */
    //@ requires this.socket != null;
    public void close() throws SocketException {
        try {
            this.socket.close();
            writer.close();
        } catch (IOException e) {
            TUI.showMessage("[CLIENT] CLIENT DISCONNECT" + e);
        }
    }

    /**
     * Set the status of client.
     *
     * @param status status of client.
     */
    public void setStatus(ClientStatus status) {
        this.status = status;
    }

    /**
     * Send a message to server
     *
     * @param message the message
     */
    public void sendMessage(String message) {
        writer.println(message);
        writer.flush();
    }

    /**
     * Send protocol to server
     *
     * @param input the protocol
     */
    public void sendProtocol(String input) {
        sendMessage(input);
    }

    /**
     * Send message with Protocol to server
     *
     * @param protocol the protocol
     * @param input the message
     */
    public void sendProtocol(String protocol, String input) {
        sendMessage(protocol + Protocol.SEPARATOR + input);
    }

    /**
     * Handle the "HELLO" protocol from the server.
     */
    public void handlerHello() {
        if (status.equals(ClientStatus.HELLO_AWAITING)) {
            this.sendLogin();
        }
    }

    /**
     * Send "LOGIN" protocol request to the server.
     */
    public void sendLogin() {
        try {
            String username = TUI.inputString("What is your username? ");

            setStatus(ClientStatus.LOGIN_AWAITING);
            sendProtocol(Protocol.LOGIN, username);
            this.username = username;
        } catch (IOException e) {
            System.out.println("[ERROR] LOGIN " + e.getMessage());
        }
    }

    /**
     * Handle the "LOGIN" protocol from server.
     * Check the username of client, if it is already exist on the server, asking a new username.
     *
     * @param input The input protocol receives from the server
     */
    public void handleLOGIN(String input) throws IOException {
        String[] split = input.split(Protocol.SEPARATOR);
        if (split[0].equals(Protocol.LOGIN)) {

            TUI.showMessage("LOGIN SUCCESSFUL: " + username);

            if (status.equals(ClientStatus.LOGIN_AWAITING)) {
                setStatus(ClientStatus.DECISION);
                TUI.handleUserProtocol();
            }
        } else if (split[0].equals(Protocol.ALREADYLOGGEDIN)) {
            TUI.showMessage("USERNAME IS ALREADY CLAIMED. PLEASE TRY A DIFFERENT USERNAME! ");
            this.sendLogin();
        }

    }

    /**
     * Handle "LIST" protocol from the server after client send the "LIST" request.
     *
     * @param input The input protocol contains the list of active users.
     */
    public void handleLIST(String input) throws IOException {
        String[] split = input.split(Protocol.SEPARATOR);
        TUI.showMessage("ACTIVE PLAYER LIST: ");
        for (int i = 1; i < split.length; i++) {
            TUI.showMessage(split[i]);
        }
        TUI.handleUserProtocol();
    }

    /**
     * Asking the user whether they want to play as a human or as an AI and then joining the queue.
     */
    public void setupNEWGAME() throws IOException {
        String answer = TUI.inputString("DO YOU WANT TO PLAY GAME BY \"AI\"? TYPE \"YES\" OR \"NO\" ");
        boolean yes = answer.equals("YES");
        if (yes) {
            String choice = TUI.inputString("NATIVE (-N) || SMART (-S)");
            if (choice.equals("-N")) {
                player = new ComputerPlayer(new NativeStrategy(username));
            } else {
                player = new ComputerPlayer(new SmartStrategy(username));
            }
        } else {
            player = new HumanPlayer(username);
        }
    }

    /**
     * Create a new game on the client side.
     * @param input the protocol sent from the server
     */
    public void handleNEWGAME(String input) {
        String[] playerName = input.split(Protocol.SEPARATOR);
        boolean player1Check = playerName[1].equals(username);

        if (player1Check) {
            TUI.showMessage("Your opponent [Y] is: " + playerName[2]);
            TUI.showMessage("\n START GAME ");

            HumanPlayer player2 = new HumanPlayer(playerName[2]);
            this.game = new DotsAndBoxesGame(player, player2);
            game.update();


        } else {
            TUI.showMessage("Your opponent [Y] is: " + playerName[1]);
            TUI.showMessage("\n START GAME ");
            HumanPlayer player2 = new HumanPlayer(playerName[1]);
            this.game = new DotsAndBoxesGame(player2, player);
            game.update();
        }

        if (game.getTurn().equals(player)) {
            this.doMove();
        } else {
            TUI.showMessage("WAITING YOUR TURN! ");
            setStatus(ClientStatus.MOVE_AWAITING);
        }
    }

    /**
     * Ask a move from the user and sending it to the server if it is their turn.
     */
    public void doMove() {
        if (game.getTurn().equals(player)) {
            Move move = player.determineMove(this.game);
            int index = move.getIndex();
            sendProtocol(Protocol.MOVE, Integer.toString(index));
            setStatus(ClientStatus.MOVE_AWAITING);
        } else {
            TUI.showMessage("WAITING YOUR TURN! ");
        }
    }

    /**
     * Make the move on the client side whenever receiving a move from the server.
     * @param input the protocol received from the server.
     */
    public void handleMOVE(String input) {
        String[] split = input.split(Protocol.SEPARATOR);

        if (status.equals(ClientStatus.MOVE_AWAITING)) {
            int index = Integer.parseInt(split[1]);
            DotsAndBoxesMove move = new DotsAndBoxesMove(index);
            this.game.doMove(move);
            game.update();

            if (this.game.isGameOver()) {
                TUI.showMessage("GAME OVER");
            } else {

                if (game.getTurn().equals(player)) {
                    this.doMove();

                } else {
                    TUI.showMessage("WAITING ");
                }
            }
        }
    }

    /**
     * Print the game over message for the client and remove it from the game.
     * @param input the game over message coming from the server
     */
    public void handleGAMEOVER(String input) throws IOException {
        String[] split = input.split(Protocol.SEPARATOR);

        switch (split[1]) {
            case Protocol.VICTORY:
                if (split[2].equals(username)) {
                    TUI.showMessage("CONGRATULATION! " + split[2] + " is winner ");
                } else {
                    TUI.showMessage("Ha ha ha");
                }
                break;
            case Protocol.DISCONNECT:
                TUI.showMessage("CONGRATULATION! " + split[2] + " is winner");
                break;
            case Protocol.DRAW:
                TUI.showMessage("DRAW! NO WINNER");
                break;
        }
        setStatus(ClientStatus.DECISION);
        TUI.handleUserProtocol();
    }

    /**
     * Disconnecting the client.
     */
    public void handleQUIT() {
        try {
            TUI.showMessage("[QUIT] QUIT SERVER");
            this.close();
        } catch (SocketException e) {
            throw new RuntimeException(e.getMessage());
        }
    }

    /**
     * Handling an error message from the server.
     * @param input the message
     */
    public void handleERROR(String input) {
        String[] split = input.split(Protocol.SEPARATOR);
        if (split[1].equals(Protocol.MOVE)) {
            doMove();
        } else {
            throw new IllegalStateException("Unexpected value: " + split[1]);
        }
    }

}
