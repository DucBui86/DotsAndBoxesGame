package Exceptions;

/**
 * Exception when the protocol is not right
 */
public class ProtocolException extends Exception {
    public ProtocolException(String string) {
        super("ERROR! PROTOCOL UNAVAILABLE" + string );
    }
}
