package dhgobra.library;

public final class Config {
  public final int idA;
  public final int idB;
  public final byte[] pkA;
  public final byte[] skB;

  public Config(int idA, int idB, byte[] pkA, byte[] skB) {
    this.idA = idA;
    this.idB = idB;
    this.pkA = pkA;
    this.skB = skB;
  }
  
}
