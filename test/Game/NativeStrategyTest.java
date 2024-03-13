package Game;

import Game.ai.NativeStrategy;
import org.junit.Test;

import static org.junit.Assert.*;

/**
 * Game.NativeStrategyTest class
 */
public class NativeStrategyTest {
    /**
     * Test the getName method
     */
    @Test
    public void testGetName() {
        NativeStrategy nativeStrategy = new NativeStrategy("TestStrategy");
        assertEquals("TestStrategy", nativeStrategy.getName());
    }

    /**
     * Test the determineMove method with valid move
     */
    @Test
    public void testDetermineMoveWithValidMoves() {
        DotsAndBoxesGame game = new DotsAndBoxesGame(new HumanPlayer("Player1"), new HumanPlayer("Player2"));
        NativeStrategy nativeStrategy = new NativeStrategy();

        // Set up a valid move
        game.doMove(new DotsAndBoxesMove(1));

        // The strategy should return a move
        Move move = nativeStrategy.determineMove(game);
        assertNotNull(move);
        assertTrue(game.isValidMove(move));
    }

    /**
     * Test the determineMove with no valid move
     */
    @Test
    public void testDetermineMoveWithNoValidMoves() {
        DotsAndBoxesGame game = new DotsAndBoxesGame(new HumanPlayer("Player1"), new HumanPlayer("Player2"));
        NativeStrategy nativeStrategy = new NativeStrategy();

        // Play moves until there are no more valid moves
        while (!game.getValidMoves().isEmpty()) {
            Move move = nativeStrategy.determineMove(game);
            game.doMove(move);
        }

        // The strategy should return a move with index 66 as there are no valid moves
        Move move = nativeStrategy.determineMove(game);
        assertNotNull(move);
        assertEquals(66, move.getIndex());
    }
}

