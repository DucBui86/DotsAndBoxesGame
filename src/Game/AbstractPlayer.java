package Game;

/**
 * The player class for the Dots and Boxes game.
 */
public abstract class AbstractPlayer {

    private String name;

    /**
     * Creates a new Player object.
     */

    public AbstractPlayer(String name) {
        this.name = name;
    }

    /**
     * Returns the name of the player.
     */
    public String getName() {
        return name;
    }

    /**
     * Determines the field for the next move.
     *
     * @param game the current game
     * @return the player's choice
     */
    public abstract DotsAndBoxesMove determineMove(Game game);

}
