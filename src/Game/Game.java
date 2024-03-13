package Game;

import java.util.List;

/**
 * Interface for the game.
 */
public interface Game {

    /**
     * Prints the result of the last game. <br>
     */
    //@ requires board.hasWinner() || board.isFull();
    void printResult();

    /**
     * Checks if the game is over or not.
     * @return true if the game is over.
     */
    boolean isGameOver();

    /**
     * Returns the valid moves.
     * @return the valid moves.
     */
    List<Integer> getValidMoves();

    /**
     * Checks if a move is valid or not.
     * @param move the move to check.
     * @return true if the move is valid.
     */
    boolean isValidMove(Move move);

    /**
     * Make a move in the game.
     * @param move the move being made.
     */
    void doMove(Move move);


}
