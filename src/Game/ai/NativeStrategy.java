package Game.ai;

import Game.DotsAndBoxesMove;
import Game.Move;
import Game.Game;

import java.util.List;
import java.util.Random;

/**
 * The Native strategy for the Dots and Boxes game.
 */
public class NativeStrategy implements Strategy {

    private String name;

    // Constructor for default bot
    public NativeStrategy() {
        this.name = "Naive Strategy";
    }

    // Constructor for a bot with a given name;
    public NativeStrategy(String name) {
        this.name = name;
    }

    /**
     * Returns the name of particular strategy.
     *
     * @return String name of strategy
     */
    @Override
    public String getName() {
        return this.name;
    }

    /**
     * Determines which move will be played next in the current game.
     *
     * @param game The instance of TicTacToeGame that is being played
     * @return Move which is played next
     */
    @Override
    public Move determineMove(Game game) {
        List<Integer> validMoves = game.getValidMoves();

        if (!validMoves.isEmpty()) {
            Random rand = new Random();
            int value = rand.nextInt(game.getValidMoves().size());
            System.out.println(value);
            return new DotsAndBoxesMove(validMoves.get(value));
        } else {
            System.out.println("ERROR! NO VALID MOVE");
            return new DotsAndBoxesMove(66);
        }
    }
}
