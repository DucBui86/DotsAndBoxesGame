package Exceptions;

/**
 * Exception when the client is not available
 */
public class ClientUnavailableException extends Exception {
    public ClientUnavailableException() {
        super("ERROR! CLIENT UNAVAILABLE");
    }
}
