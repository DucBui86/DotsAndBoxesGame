package Game;

import Game.ai.ComputerPlayer;
import Game.ai.NativeStrategy;
import Game.ai.SmartStrategy;

import java.util.Objects;
import java.util.Scanner;


public class DotsAndBoxesTUI {
    static DotsAndBoxesGame game;
    Board board;

    public DotsAndBoxesTUI() {
        board = new Board();
    }

    /**
     * Determines the types of and names of players through user input
     */
    public static void main(String[] args) {
        String name1;
        String name2;

        System.out.println("\n\n -------------------- Welcome to Dots and Boxes! -------------------- ");
        System.out.println("Type '-n' for a Native AI, or '-s' for a Smart AI\n");
        Scanner scanner = new Scanner(System.in);
        if (args.length != 2) {
            System.out.println("Name of first player: ");
            name1 = scanner.nextLine();
            System.out.println("Name of second player: ");
            name2 = scanner.nextLine();
        } else {
            name1 = args[0];
            name2 = args[1];
        }
        AbstractPlayer player1;
        AbstractPlayer player2;


        if (name1.equalsIgnoreCase("-n")) {
            player1 = new ComputerPlayer(new NativeStrategy());
        } else if (name1.equalsIgnoreCase("-s")) {
            player1 = new ComputerPlayer(new SmartStrategy());
        } else {
            player1 = new HumanPlayer(name1);
        }
        if (name2.equalsIgnoreCase("-s")) {
            player2 = new ComputerPlayer(new SmartStrategy());
        } else if (name2.equalsIgnoreCase("-n")) {
            player2 = new ComputerPlayer(new NativeStrategy());
        } else {
            player2 = new HumanPlayer(name2);
        }


        game = new DotsAndBoxesGame(player1, player2);
        start();
    }


    /**
     * Starts the Dots and Boxes game.
     * Asks after each ended game if the user want to continue. Continues until
     * the user does not want to play anymore.
     */
    public static void start() {
        boolean continueGame = true;
        while (continueGame) {
            game.reset();
            play();
            System.out.println("\n> Play another time? (y/n)?");
            Scanner scanner = new Scanner(System.in);
            String input = scanner.nextLine();
            if (Objects.equals(input, "n")) {
                continueGame = false;
            }
        }
    }

    /**
     * Asks players for moves and updates the board until the game is over.
     */
    public static void play() {
        game.update();
        while (!game.getBoard().gameOver()) {
            game.doMove(game.players[game.turnPlayer].determineMove(game));
            game.update();
        }
        game.printResult();
    }

}
