package cora.smt;

public final class QVar extends QExpression {
  private int _index;
  private String _name;

  /** The constructors are hidden, since IntegerExpressions should be made through an SmtProblem. */
  public QVar(int i) {
    _index = i;
    _name = "i" + _index;
  }

  /** The constructors are hidden, since IntegerExpressions should be made through an SmtProblem. */
  QVar(int i, String name) {
    _index = i;
    _name = "[" + name + "]";
  }

  public int queryIndex() {
    return _index;
  }

  public String queryName() {
    return _name;
  }

  public QExpression simplify() {
    return this;
  }

  public int compareTo(QExpression other) {
    throw new UnsupportedOperationException("TODO: Not yet implemented");
  }

}