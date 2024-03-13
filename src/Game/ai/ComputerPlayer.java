package Game.ai;

import Game.*;
import Game.AbstractPlayer;
import Game.DotsAndBoxesMove;

/**
 * The computer player for the Dots and Boxes game.
 */
public class ComputerPlayer extends AbstractPlayer {
    private Strategy strategy;

    /**
     * Constructs a new ComputerPlayer object with the specified strategy.
     *
     * @param strategy The strategy used by the computer player to determine its moves
     */
    public ComputerPlayer(Strategy strategy) {
        super(strategy.getName());
        this.strategy = strategy;
    }

    /**
     * Determines the field for the next move.
     *
     * @param game the current game
     * @return the player's choice
     */
    //@ requires game != null;
    //@ ensures \result instanceof Move;
    @Override
    public DotsAndBoxesMove determineMove(Game game) {
        return (DotsAndBoxesMove) strategy.determineMove(game);
    }
}
