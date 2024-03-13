package Game.ai;

import Game.Move;
import Game.Game;

/**
 * The strategy interface for the Dots and Boxes game.
 */
public interface Strategy {
    /**
     * Returns the name of particular strategy.
     * @return String name of strategy
     */
    //@ensures \result!= null;
    String getName();

    /**
     * Determines which move will be played next in the current game.
     * @param game The instance of TicTacToeGame that is being played
     * @return Move which is played next
     */
    //@requires game != null;
    Move determineMove(Game game);
}
