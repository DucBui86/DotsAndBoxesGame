package Server;

import Game.AbstractPlayer;
import Game.DotsAndBoxesGame;
import Game.DotsAndBoxesMove;
import Game.HumanPlayer;
import Protocol.Protocol;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.Socket;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

/**
 * The server class
 */
public class Server extends SocketServer {
    ArrayList<ClientHandler> clients = new ArrayList<>();

    Lock lock = new ReentrantLock();

    ArrayList<ClientHandler> queueList = new ArrayList<>();

    Map<DotsAndBoxesGame, ClientHandler[]> games = new HashMap<>();


    /**
     * Constructs a new Server
     *
     * @param port the port to listen on
     * @throws IOException if the server socket cannot be created, for example, because the port is already bound.
     */
    public Server(int port) throws IOException {
        super(port);
    }

    /**
     * Returns the port on which this server is listening for connections.
     *
     * @return the port on which this server is listening for connections
     */
    public int getPort() {
        return super.getPort();
    }

    /**
     * Accepts connections and starts a new thread for each connection.
     * This method will block until the server socket is closed, for example by invoking closeServerSocket.
     *
     * @throws IOException if an I/O error occurs when waiting for a connection
     */
    public void acceptConnections() throws IOException {
        super.acceptConnections();
    }

    /**
     * Closes the server socket. This will cause the server to stop accepting new connections.
     * If called from a different thread than the one running acceptConnections, then that thread will return from
     * acceptConnections.
     */
    public synchronized void close() {
        super.close();
    }

    /**
     * Creates a new connection handler for the given socket.
     *
     * @param socket the socket for the connection
     */
    protected void handleConnection(Socket socket) {
        ServerConnection conn = null;
        try {
            conn = new ServerConnection(socket);
        } catch (IOException e){
            System.out.println(e);
        }
        ClientHandler ch = new ClientHandler(socket, this);
        conn.chandler = ch;
        ch.connection = conn;
        conn.start();
    }

    /**
     * Adds a client to the server.
     *
     * @param ch the client handler
     */
    public void addClient(ClientHandler ch) {
        try {
            lock.lock();
            clients.add(ch);
        } finally {
            lock.unlock();
        }
    }

    /**
     * Removes a client from the server.
     *
     * @param ch the client handler
     */
    public void removeClient(ClientHandler ch) {
        try {
            lock.lock();
            clients.remove(ch);
            if (ch.inGame) {
                games.remove(ch.game);
                gameOverDc(ch.opponent);
                ch.opponent.inGame = false;
            }
        } finally {
            lock.unlock();
        }
    }

    /**
     * Create a new game on the server side.
     * @param ch1 first client in the game
     * @param ch2 second client in the game
     */
    public void newGame(ClientHandler ch1, ClientHandler ch2) {
        try {
            lock.lock();
            AbstractPlayer player1 = new HumanPlayer(ch1.getUsername());
            AbstractPlayer player2 = new HumanPlayer(ch2.getUsername());
            DotsAndBoxesGame game = new DotsAndBoxesGame(player1, player2);
            games.put(game, new ClientHandler[]{ch1, ch2});
            ch2.inGame = true;
            ch1.inGame = true;
            ch2.inQueue = false;
            ch1.inQueue = false;
            ch1.game = game;
            ch2.game = game;
            ch1.opponent = ch2;
            ch2.opponent = ch1;
            ch2.sendMessage(Protocol.NEWGAME + Protocol.SEPARATOR + player1.getName() + Protocol.SEPARATOR + player2.getName());
            ch1.sendMessage(Protocol.NEWGAME + Protocol.SEPARATOR + player1.getName() + Protocol.SEPARATOR + player2.getName());
            queueList.remove(ch2);
        } finally {
            lock.unlock();
        }

    }


    /**
     * Make a move on the game on the server side.
     * @param ch the client making the move
     * @param move the move
     */
    public void move(ClientHandler ch, String move) {
        try {
            lock.lock();
            if (ch.game.isValidMove(new DotsAndBoxesMove(Integer.parseInt(move)))) {
                ch.game.doMove(new DotsAndBoxesMove(Integer.parseInt(move)));
            } else {
                ch.sendMessage(Protocol.ERROR + Protocol.SEPARATOR + "MoveNotValid");
            }
            ch.sendMessage(Protocol.MOVE + Protocol.SEPARATOR + move);
            ch.opponent.sendMessage(Protocol.MOVE + Protocol.SEPARATOR + move);
            gameOver(ch.game, ch, ch.opponent);
        } finally {
            lock.unlock();
        }
    }


    /**
     * Checks if the game is over or not. If it is, then remove the clients form the game and the game itself.
     * @param game the game
     * @param player1 the first client in the game
     * @param player2 the second client in the game
     */
    public void gameOver(DotsAndBoxesGame game, ClientHandler player1, ClientHandler player2) {
        if (game.isGameOver()) {
            if (!game.getBoard().hasWinner()) {
                player1.sendMessage(Protocol.GAMEOVER + Protocol.SEPARATOR + "DRAW");
                player2.sendMessage(Protocol.GAMEOVER + Protocol.SEPARATOR + "DRAW");
            } else {
                if (game.getBoard().isWinner("X")) {
                    player1.sendMessage(Protocol.GAMEOVER + Protocol.SEPARATOR + "VICTORY" + Protocol.SEPARATOR + player1.getUsername());
                    player2.sendMessage(Protocol.GAMEOVER + Protocol.SEPARATOR + "VICTORY" + Protocol.SEPARATOR + player1.getUsername());
                } else {
                    player1.sendMessage(Protocol.GAMEOVER + Protocol.SEPARATOR + "VICTORY" + Protocol.SEPARATOR + player2.getUsername());
                    player2.sendMessage(Protocol.GAMEOVER + Protocol.SEPARATOR + "VICTORY" + Protocol.SEPARATOR + player2.getUsername());
                }
            }
            games.remove(game);
            player1.inGame = false;
            player2.inGame = false;
        }
    }

    /**
     * Sending the game over by disconnect message to the client side.
     * @param ch the client
     */
    public void gameOverDc(ClientHandler ch) {
        ch.sendMessage(Protocol.GAMEOVER + Protocol.SEPARATOR + "DISCONNECT" + Protocol.SEPARATOR + ch.getUsername());
    }

    /**
     * Put a client in the queue. If there is already someone in the queue, make a game with the two clients.
     * @param ch the client queueing up
     */
    public void queue(ClientHandler ch) {
        try {
            lock.lock();
            if (queueList.size() > 0) {
                newGame(ch, queueList.get(0));
            } else {
                queueList.add(ch);
            }
        } finally {
            lock.unlock();
        }

    }

    /**
     * Remove the client from the queue.
     * @param ch the client to remove.
     */
    public void deQueue(ClientHandler ch) {
        try {
            lock.lock();
            ch.inQueue = false;
            queueList.remove(ch);
        } finally {
            lock.unlock();
        }

    }

    /**
     * Send the hello protocol to the client side.
     * @param ch the client to send the protocol to.
     */
    public void hello(ClientHandler ch) {
        ch.sendMessage(Protocol.HELLO + Protocol.SEPARATOR + "Server by Szabi and Cuong!");
        ch.helloed = true;
    }

    /**
     * Send the list of clients connected to the server to a client.
     * @param ch the client to send the protocol to.
     */
    public void list(ClientHandler ch) {
        StringBuilder chs = new StringBuilder();
        for (ClientHandler i : clients) {
            chs.append(Protocol.SEPARATOR).append(i.getUsername());
        }
        ch.sendMessage(Protocol.LIST + chs);
    }

    /**
     * Send the LOGIN protocol to the client if the username is available.
     * Send the ALRERADYLOGGEDIN protocol if it is not.
     * @param ch the client logging in
     * @param name the username chosen
     */
    public void login(ClientHandler ch, String name) {
        try {
            lock.lock();
            for (ClientHandler i : clients) {
                if (i.getUsername().equals(name)) {
                    ch.sendMessage(Protocol.ALREADYLOGGEDIN);
                    return;
                }
            }
            ch.receiveUsername(name);
            addClient(ch);
            ch.sendMessage(Protocol.LOGIN);
            ch.loggedIn = true;
        } finally {
            lock.unlock();
        }

    }

    /**
     * Handle a message coming from the client side.
     *
     * @param ch  the client
     * @param msg the message
     */
    public void handleMessage(ClientHandler ch, String msg) {
        try {
            lock.lock();
            String message = msg.split(Protocol.SEPARATOR)[0];
            System.out.println(ch.getUsername() + ": " + msg);
            switch (message) {
                case Protocol.HELLO:
                    hello(ch);
                    break;
                case Protocol.LOGIN:
                    login(ch, msg.split(Protocol.SEPARATOR)[1]);
                    break;
                case Protocol.LIST:
                    list(ch);
                    break;
                case Protocol.QUEUE:
                    if (ch.inQueue) {
                        deQueue(ch);
                    }
                    queue(ch);
                    break;
                case Protocol.MOVE:
                    move(ch, msg.split(Protocol.SEPARATOR)[1]);
                    break;
                default:
                    ch.sendMessage("Wrong message format. Try again using the Protocol.");
                    break;
            }
        } finally {
            lock.unlock();
        }
    }

    /**
     * Main method for the server.
     * @param args arguments
     */
    public static void main(String[] args) throws IOException {
        BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));
        Server server;
        String line;
        int port = -1;
        while (true) {
            try {
                while (port < 0 || port > 65536) { //while the port they put in is invalid
                    System.out.println("Please give a valid port number");
                    line = reader.readLine();
                    port = Integer.parseInt(line);
                }

                server = new Server(port);
                System.out.println("Port number:" + server.getPort());
                System.out.println("Server started...");
                server.acceptConnections(); //starting the server
                server.close(); //closing the server
                System.out.println("Server stopped...");
                break;
            } catch (NumberFormatException e) {
                System.out.println("Error: input was not an integer");
            }
        }
    }
}
