package Game;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * The board class for the Dots and Boxes game.
 */
public class Board {

    private static final String DELIM = "     ";

    ArrayList<Integer> horizontals = new ArrayList<>(Arrays.asList(0, 1, 2, 3, 4, 11, 12, 13, 14, 15, 22, 23, 24, 25, 26, 33, 34, 35, 36, 37, 44, 45, 46, 47, 48, 55, 56, 57, 58, 59));

    int X;
    int Y;


    private static final String[] NUMBERING = {
            " * 0  * 1  * 2  * 3  * 4  *  ",
            " 5    6    7    8    9   10  ",
            " * 11 * 12 * 13 * 14 * 15 *  ",
            "16    17   18   19   20   21 ",
            " * 22 * 23 * 24 * 25 * 26 *  ",
            "27    28   29   30   31   32 ",
            " * 33 * 34 * 35 * 36 * 37 *  ",
            "38    39   40   41   42   43 ",
            " * 44 * 45 * 46 * 47 * 48 *  ",
            "49    50   51   52   53   54 ",
            " * 55 * 56 * 57 * 58 * 59 *  "};

    /**
     * The  fields of the Dots and Boxes board. See NUMBERING for the
     * coding of the fields.
     */
    public Mark[] fields;


    /**
     * Creates an empty board.
     */
    //@ ensures (\forall int i; (i >= 0 && i < 60); fields[i] == Mark.EMPTY);
    public Board() {
        int i;
        this.fields = new Mark[60];
        for (i = 0; i >= 0 && i < 60; i++) {
            this.fields[i] = Mark.EMPTY;
        }
        this.X = 0;
        this.Y = 0;
    }

    /**
     * Creates a deep copy of the board.
     *
     * @return the board
     */
    /*@ ensures \result != this;
        ensures (\forall int i; (i >= 0 && i < 60); \result.fields[i] == this.fields[i]);
     @*/
    public Board deepCopy() {
        Board boardcopy = new Board();
        for (int i = 0; i >= 0 && i < 60; i++) {
            final Mark fieldsElement;
            fieldsElement = this.getField(i);
            boardcopy.fields[i] = fieldsElement;
        }
        return boardcopy;
    }


    /**
     * Calculates the index in the linear array of fields from a (row, col) pair.
     *
     * @param row the row
     * @param col the col
     * @return the index belonging to the (row,col)-field
     */
    /*@ requires row >= 0 && row < 11;
        requires col >= 0 && row < 11;
     @*/
    public int index(int row, int col) {
        if ((row % 2) == 1) {
            return (row / 2) * 6 + (row - row / 2) * 5 + col;
        } else {
            return (row / 2) * 6 + (row / 2) * 5 + col;
        }
    }


    /**
     * Returns true if index is a valid index of a field on the board.
     *
     * @param index the index
     * @return true if 0 <= index < 60
     */
    //@ ensures index >= 0 && index < 60 ==> \result == true;
    public boolean isField(int index) {
        return index >= 0 && index < 60;
    }

    /**
     * Returns the content of the field i.
     *
     * @param i the index of the field (see NUMBERING)
     * @return the mark on the field
     */
    /*@ requires isField(i);
        ensures \result == Mark.EMPTY || \result == Mark.HORIZ || \result == Mark.VERT;
     @*/
    public Mark getField(int i) {
        return this.fields[i];
    }

    /**
     * Returns true if the field is empty.
     *
     * @param i the index of the field (see NUMBERING)
     * @return true if the field is empty
     */
    /*@ requires isField(i);
        ensures isEmptyField(i) ==> \result == true;
     @*/
    public boolean isEmptyField(int i) {
        return this.getField(i).equals(Mark.EMPTY);
    }


    /**
     * Returns true if the whole board is full.
     *
     * @return true if all fields are full
     */
    //@ ensures (\forall int i; (i >= 0 && i < 60); !isEmptyField(fields[i]));
    public boolean isFull() {
        int i;
        for (i = 0; i >= 0 && i < 60; i++) {
            if (fields[i] == Mark.EMPTY) {
                return false;
            }
        }
        return true;
    }

    /**
     * Returns true if the game is over. The game is over when there is a winner
     * or the whole board is full.
     *
     * @return true if the game is over
     */
    //@ ensures isFull() || hasWinner() ==> \result == true;
    public boolean gameOver() {
        return this.isFull() || this.hasWinner();
    }

    /**
     * Checks and adds a point to a team if they finished a box.
     *
     * @param move the move
     * @param team the team
     * @return true if the team finished a box
     */
    //@ requires isEmptyField(fields[move.getIndex()]);
    //@ ensures inBox(move) ==> \old(X) == X + 1 || \old(Y) == Y + 1;
    public boolean point(Move move, String team) {
        int points = inBox(move);
        if (points > 0) {
            if (team.equals("X")) {
                this.X = this.X + points;
                System.out.println("X has scored " + points + " points. Total points: " + X);
            } else {
                this.Y = this.Y + points;
                System.out.println("Y has scored " + points +" points. Total points: " + Y);
            }
            return true;
        }
        return false;
    }

    /**
     * Checks which are the valid moves on the board.
     * @return the indexes of the valid moves.
     */
    public List<Integer> validMoves(){
        List<Integer> validMoves = new ArrayList<>();
        // Iterate over all possible moves on the board
        for (int index = 0; index < 60; index++) {
            if (isEmptyField(index)) {
                validMoves.add(index);
            }
        }
        return validMoves;
    }

    /**
     * Checks if the move completes a box. The box is completed if this move is
     * the exactly fourth line around it.
     *
     * @param move the move
     * @return true if the move completes a box.
     */
    //@ requires isEmptyField(fields[move.getIndex()]);
    public int inBox(Move move) {
        boolean up = false;
        boolean down = false;
        boolean right = false;
        boolean left = false;
        int point = 0;

        if (move.getIndex() >= 0 && move.getIndex() < 5) {
            down = !isEmptyField(move.getIndex() + 11) && !isEmptyField(move.getIndex() + 5) &&
                    !isEmptyField(move.getIndex() + 6);
            if (down) {
                point = 1;
            }
        } else if (move.getIndex() >= 55) {
            up = !isEmptyField(move.getIndex() - 11) && !isEmptyField(move.getIndex() - 6) &&
                    !isEmptyField(move.getIndex() - 5);
            if (up){
                point = 1;
            }
        } else if (!horizontals.contains(move.getIndex())) {
            if (move.getIndex() == 5 || move.getIndex() == 16 || move.getIndex() == 27 || move.getIndex() == 38 || move.getIndex() == 49) {
                right = !isEmptyField(move.getIndex() + 6) && !isEmptyField(move.getIndex() - 5) &&
                        !isEmptyField(move.getIndex() + 1);
                if (right){
                    point = 1;
                }
            } else if (move.getIndex() == 10 || move.getIndex() == 21 || move.getIndex() == 32 || move.getIndex() == 43 || move.getIndex() == 54) {
                left = !isEmptyField(move.getIndex() - 1) && !isEmptyField(move.getIndex() - 6) &&
                        !isEmptyField(move.getIndex() + 5);
                if (left){
                    point = 1;
                }
            }else {
                right = !isEmptyField(move.getIndex() + 6) && !isEmptyField(move.getIndex() - 5) &&
                        !isEmptyField(move.getIndex() + 1);
                left = !isEmptyField(move.getIndex() - 1) && !isEmptyField(move.getIndex() - 6) &&
                        !isEmptyField(move.getIndex() + 5);
                if(right){
                    point++;
                }
                if (left){
                    point++;
                }
            }
        }else{
            down = !isEmptyField(move.getIndex() + 11) && !isEmptyField(move.getIndex() + 5) &&
                    !isEmptyField(move.getIndex() + 6);
            up = !isEmptyField(move.getIndex() - 11) && !isEmptyField(move.getIndex() - 6) &&
                    !isEmptyField(move.getIndex() - 5);
            if(down){
                point++;
            }
            if (up){
                point++;
            }
        }
        return point;
    }


    /**
     * Checks if the team is the winner.
     *
     * @param team the team
     * @return true if the team has more points than the other team.
     */
    /*@
        requires team.equals("X") || team.equals("Y");
     @*/
    public boolean isWinner(String team) {
        if (!this.isFull()) {
            return false;
        }
        return teamPoints(team) > otherTeamPoints(team);
    }

    /**
     * Checks the points of a team.
     *
     * @param team the team
     * @return the points
     */
    public int teamPoints(String team) {
        if (team.equals("X")) {
            return this.X;
        } else if (team.equals("Y")) {
            return this.Y;
        }
        return 0;
    }

    /**
     * Checks the other team's points.
     *
     * @param team the team whose opponent's points we want to get.
     * @return the points
     */
    public int otherTeamPoints(String team) {
        if (team.equals("X")) {
            return this.Y;
        } else if (team.equals("Y")) {
            return this.X;
        }
        return 0;
    }

    /**
     * Checks if the game has a winner.
     *
     * @return true if the student has a winner.
     */
    //@ ensures isWinner(Mark.XX) || isWinner(Mark.OO) ==> \result == true;
    public boolean hasWinner() {
        return isWinner("X") || isWinner("Y");
    }

    /**
     * Returns a String representation of the board. In addition to the current
     * situation, the String also shows the numbering of the fields.
     *
     * @return the game situation as String
     */
    public String tostring() {
        String s = "";
        for (int i = 0; i <= 10; i++) {
            String row = getString(i);
            if (i % 2 == 0) {
                s = s + row + DELIM + NUMBERING[i] + "\n";
            } else {
                s = s + row + DELIM + NUMBERING[i] + "\n";
            }
        }
        return s;
    }

    /**
     * Representation of a row.
     * @param i the row number
     * @return the representation of the row.
     */
    private String getString(int i) {
        String row = "";
        if (i % 2 == 0) {
            row = row + "+";
            for (int j = 0; j < 5; j++) {
                if (!isEmptyField(index(i, j))) {
                    row = row + "---+";
                } else {
                    row = row + "   +";
                }
            }
        } else {
            for (int j = 0; j < 6; j++) {
                if (j == 5){
                    if (!isEmptyField(index(i, j))) {
                        row = row + "|";
                    } else {
                        row = row + " ";
                    }
                } else {
                    if (!isEmptyField(index(i, j))) {
                        row = row + "|   ";
                    } else {
                        row = row + "    ";
                    }
                }
            }
        }
        return row;
    }

    /**
     * Empties all fields of this board.
     */
    //@ ensures (\forall int i; (i >= 0 && i < 60); fields[i] == Mark.EMPTY);
    public void reset() {
        for (int i = 0; i >= 0 && i < 60; i++) {
            fields[i] = Mark.EMPTY;
        }
        this.X = 0;
        this.Y = 0;
    }

    /**
     * Sets the content of a field.
     *
     * @param i the field number (see NUMBERING)
     */
    /*@ requires isField(i);
        ensures !isEmptyField(getField(i));
     @*/
    public void setField(int i) {
        if (isField(i)) {
            if (horizontals.contains(i)) {
                fields[i] = Mark.HORIZ;
            } else {
                fields[i] = Mark.VERT;
            }
        }
    }
}
