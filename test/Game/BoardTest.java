package Game;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


/**
 * Test class for the board.
 */
public class BoardTest {
    /**
     * The Board.
     */
    Board board = new Board();


    /**
     * Setup before every test.
     */
    @BeforeEach
    public void setUp() {
        board.reset();
    }

    /**
     * Testing the index() function of the board class.
     */
    @Test
    public void indexTest(){
        assertEquals(1, board.index(0, 1));
        assertEquals(6, board.index(1, 1));
        assertEquals(40, board.index(7, 2));
        assertEquals(58, board.index(10, 3));

    }

    /**
     * Testing the inBox() function in the board class.
     */
    @Test
    public void inBoxTest(){
        board.setField(0);
        board.setField(6);
        board.setField(11);
        board.point(new DotsAndBoxesMove(5), "X");
        assertEquals(1, board.teamPoints("X"));
        assertEquals(0, board.teamPoints("Y"));
    }

    /**
     * Testing the setField() function in the board class.
     */
    @Test
    public void setFieldTest(){
        for (int i = 0; i < board.fields.length; i++){
            assertEquals(Mark.EMPTY, board.getField(i));
            board.setField(i);
            assertNotEquals(Mark.EMPTY, board.getField(i));
        }
    }

    /**
     * Testing the gameOver() function in the board class.
     */
    @Test
    public void gameOverTest(){
        for (int i = 0; i < board.fields.length; i++){
            assertFalse(board.gameOver());
            assertFalse(board.isFull());
            board.setField(i);
        }
        assertTrue(board.gameOver());
    }

    /**
     * Testing the deepCopy() function in the board class.
     */
    @Test
    public void deepCopyTest(){
        Board copy = board.deepCopy();
        copy.setField(2);
        assertTrue(board.isEmptyField(2));
        assertFalse(copy.isEmptyField(2));
    }


}
