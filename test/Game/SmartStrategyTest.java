package Game;

import Game.ai.SmartStrategy;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;


public class SmartStrategyTest {
    /**
     * Test the getName method
     */
    @Test
    public void testGetName() {
        SmartStrategy smartStrategy = new SmartStrategy("TestStrategy");
        Assertions.assertEquals("TestStrategy", smartStrategy.getName());
    }


    /**
     * Test the determineMove method with valid move
     */
    @Test
    public void testDetermineMoveWithValidMoves() {
        DotsAndBoxesGame game = new DotsAndBoxesGame(new HumanPlayer("Player1"), new HumanPlayer("Player2"));
        SmartStrategy smartStrategy = new SmartStrategy();

        // Set up a valid move
        game.doMove(new DotsAndBoxesMove(1));

        // The strategy should return a move
        Move move = smartStrategy.determineMove(game);
        Assertions.assertNotNull(move);
        Assertions.assertTrue(game.isValidMove(move));
    }
}
