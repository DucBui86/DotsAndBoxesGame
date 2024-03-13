package Game;


import java.util.ArrayList;
import java.util.List;


/**
 * The game class for the Dots and Boxes game.
 */
public class DotsAndBoxesGame implements Game {
    private Board board;
    private AbstractPlayer player1;
    private AbstractPlayer player2;

    /*@ public invariant players.length == NUMBER_PLAYERS;
        public invariant (\forall int i; (i >= 0 && i < NUMBER_PLAYERS); players[i] != null);
    @*/
    /**
     * The 2 players of the game.
     */
    public AbstractPlayer[] players;

    public int turnPlayer;


    /**
     * Instantiates a DotsAndBoxes game object.
     *
     * @param player1 the first player of the game
     * @param player2 the second player of the game
     */
    public DotsAndBoxesGame(AbstractPlayer player1, AbstractPlayer player2) {
        board = new Board();
        this.player1 = player1;
        this.player2 = player2;
        players = new AbstractPlayer[]{player1, player2};
        turnPlayer = 0;
    }

    /**
     * Returns the board.
     *
     * @return the board.
     */
    public Board getBoard() {
        return board;
    }

    /**
     * Prints the game situation.
     */
    public void update() {
        System.out.println("\ncurrent game situation: \n\n" + board.tostring()
                + "\n");
        System.out.println("X: " + getScore("X") + "Y: " + getScore("Y"));
    }

    /**
     * Resets the game.
     */
    //@ ensures turnPlayer = 0;
    public void reset() {
        turnPlayer = 0;
        this.board.reset();
    }

    /**
     * Prints the result of the last game. <br>
     */
    //@ requires board.hasWinner() || board.isFull();
    @Override
    public void printResult() {
        System.out.println("Points: X(" + board.teamPoints("X") + "), Y(" + board.teamPoints("Y") + ")");
        if (board.hasWinner()) {
            if (board.isWinner("X")) {
                System.out.println("Player " + player1.getName() + " (X) has won!");
            } else {
                System.out.println("Player " + player2.getName() + " (Y) has won!");
            }
        } else {
            System.out.println("Draw. There is no winner!");
        }
    }

    /**
     * Checks if the game is over or not.
     *
     * @return true if the game is over.
     */
    @Override
    public boolean isGameOver() {
        return board.gameOver();
    }

    /**
     * Returns the valid moves.
     *
     * @return the valid moves.
     */
    @Override
    public List<Integer> getValidMoves() {
        List<Integer> validMoves = new ArrayList<>();
        // Iterate over all possible moves on the board
        for (int index = 0; index < 60; index++) {
            if (board.isEmptyField(index)) {
                validMoves.add(index);
            }
        }
        return validMoves;
    }

    /**
     * Make a move in the game.
     *
     * @param move the move being made.
     */
    @Override
    public void doMove(Move move) {
        DotsAndBoxesMove dotsAndBoxesMove = (DotsAndBoxesMove) move;
        int index = dotsAndBoxesMove.getIndex();

        if (isValidMove(move)) {
            board.setField(index);

            if (turnPlayer == 0) {
                if (!board.point(move, "X")) {
                    turnPlayer = (turnPlayer + 1) % 2;
                }
            } else {
                if (!board.point(move, "Y")) {
                    turnPlayer = (turnPlayer + 1) % 2;
                }
            }
        } else {
            System.out.println("This is not a valid move, please choose another one: ");
            doMove(players[turnPlayer].determineMove(this));
        }
    }

    /**
     * Checks if a move is valid or not.
     *
     * @param move the move to check.
     * @return true if the move is valid.
     */
    @Override
    public boolean isValidMove(Move move) {
        return getValidMoves().contains(move.getIndex());
    }

    /**
     * Checks who is on turn.
     *
     * @returnthe players name who is on turn.
     */
    public AbstractPlayer getTurn() {
        if (turnPlayer == 0) {
            return player1;
        } else {
            return player2;
        }
    }

    /**
     * Checks the score of a team.
     *
     * @param team the team
     * @return the score of the team
     */
    public int getScore(String team) {
        return board.teamPoints(team);
    }
}

