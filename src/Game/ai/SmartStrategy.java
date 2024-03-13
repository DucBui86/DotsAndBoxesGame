package Game.ai;

import Game.DotsAndBoxesGame;
import Game.DotsAndBoxesMove;
import Game.Move;
import Game.Game;
import Game.Board;

import java.util.List;

/**
 * The Smart strategy for the Dots and Boxes game.
 */
public class SmartStrategy implements Strategy {
    private final String name;

    // Constructor for default bot
    public SmartStrategy() {
        this.name = "Smart Strategy";
    }

    // Constructor for a bot with a given name;
    public SmartStrategy(String name){
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
        if (game instanceof DotsAndBoxesGame) {
            return findBestMove(((DotsAndBoxesGame) game).getBoard());
        } else {
            throw new IllegalArgumentException("Unsupported game type");
        }
    }

    /**
     * Finds the best move for the current state of the game.
     * @param board the board of the game
     * @return the best move
     */
    // Implementation of Minimax algorithm to find the best move for Dots and Boxes
    private Move findBestMove(Board board) {
        int bestScore = Integer.MIN_VALUE;
        int bestMoveIndex = -1;

        List<Integer> validMoves = board.validMoves();

        for (int moveIndex : validMoves) {

            Board boardCopy = board.deepCopy();
            boardCopy.setField(moveIndex);

            int score = minMax(boardCopy, 0, false);

            if (score > bestScore) {
                bestScore = score;
                bestMoveIndex = moveIndex;
            }
        }

        return new DotsAndBoxesMove(bestMoveIndex);
    }

    /**
     * The min max algorithm.
     * @param board the board of the game
     * @param depth the depth of the min max
     * @param maximizingPlayer if we want to maximize
     * @return the evaluation
     */
    private int minMax(Board board, int depth, boolean maximizingPlayer) {
        if (board.gameOver()) {
            return evaluateBoard(board);
        }

        List<Integer> validMoves = board.validMoves();

        if (maximizingPlayer) {
            int maxEval = Integer.MIN_VALUE;

            for (int moveIndex : validMoves) {
                board.setField(moveIndex);

                int eval = minMax(board, depth + 1, false);

                maxEval = Math.max(maxEval, eval);
            }

            return maxEval;
        } else {
            int minEval = Integer.MAX_VALUE;

            for (int moveIndex : validMoves) {
                board.setField(moveIndex);

                int eval = minMax(board, depth + 1, true);

                minEval = Math.min(minEval, eval);
            }

            return minEval;
        }
    }

    /**
     * Evaluating the points on the board.
     * @param board the board
     * @return the difference between the points of the two teams.
     */
    private int evaluateBoard(Board board) {
        // Replace this with your own heuristic evaluation function
        return board.teamPoints("X") - board.teamPoints("Y");
    }
}
