package Game;

/**
 * The move class for the Dots and Boxes game.
 */
public class DotsAndBoxesMove implements Move{
    private int index;

    /**
     * Constructor to initialize a DotsAndBoxesMove with specified row and column.
     *
     * @param index the index of the move
     */
    public DotsAndBoxesMove(int index) {
        this.index = index;

    }

    /**
     * Returns the index of the move
     * @return the index of the move
     */
    @Override
    public int getIndex() {
        return this.index;
    }
}
