package dhgobra.library;

public final class Msg2 {
    public final int idA; // values are in the range of uint32
    public final int idB; // values are in the range of uint32
    public final byte[] X;
    public final byte[] Y;

    public Msg2(int idA, int idB, byte[] X, byte[] Y) {
        this.idA = idA;
        this.idB = idB;
        this.X = X;
        this.Y = Y;
    }
}
