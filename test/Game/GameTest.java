package Game;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test class for the game.
 */
public class GameTest {
    /**
     * The Game.
     */
    DotsAndBoxesGame game = new DotsAndBoxesGame(new HumanPlayer("X"),new HumanPlayer("Y"));

    /**
     * Setup before every test.
     */
    @BeforeEach
    public void setUp(){
        game.reset();
    }

    /**
     * Testing the validMoves() function in the DotsAndBoxesGame class.
     */
    @Test
    public void testValidMoves(){
        List<Integer> valids = new ArrayList<>();
        for (int i = 0; i >= 0 && i < 60; i++) {
            valids.add(i);
        }
        assertEquals(valids, game.getValidMoves());
        for (int i = 0; i >= 0 && i < 60; i++) {
            game.getBoard().setField(i);
        }
        valids.clear();
        assertEquals(valids, game.getValidMoves());
    }

    /**
     * Testing the doMove() function in the DotsAndBoxesGame class.
     */
    @Test
    public void testMove(){
        List<Integer> valids = game.getValidMoves();
        game.doMove(new DotsAndBoxesMove(15));
        assertNotEquals(valids, game.getValidMoves());
        assertFalse(game.isValidMove(new DotsAndBoxesMove(15)));
        assertTrue(game.isValidMove(new DotsAndBoxesMove(16)));
    }
}
