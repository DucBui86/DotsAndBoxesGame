package Game;

import java.util.Scanner;

/**
 * The human player for the Dots and Boxes game.
 */
public class HumanPlayer extends AbstractPlayer{

    /**
     * Creates a new human player object.
     */
    public HumanPlayer(String name) {
        super(name);
    }

    /**
     * Asks the user to input the field where to place the next mark. This is
     * done using the standard input/output.
     *
     * @param game the game class
     * @return the player's chosen field
     */
    @Override
    public DotsAndBoxesMove determineMove(Game game) {
        if (game.getValidMoves().isEmpty()) {
            System.out.println("Don't have any valid move!");
        } else {
            while (true) {
                Scanner scanner = new Scanner(System.in);

                // Ask the user to input the row and column for the move
                System.out.println("it's your turn. Enter the index (0-59): ");
                while(!scanner.hasNextInt()) {
                    System.out.println("Wrong input type!");
                    System.out.println("it's your turn. Enter the index (0-59): ");
                    scanner.nextLine();
                }
                int index = scanner.nextInt();
                Move move = new DotsAndBoxesMove(index);

                if (!game.isValidMove(move)) {
                    System.out.println("Invalid Move! Please enter the index (0-59)");
                } else {
                    // Create and return the DotsAndBoxesMove
                    return new DotsAndBoxesMove(index);
                }
            }
        }
        return null;
    }
}
