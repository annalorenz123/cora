package cora.smt;
import charlie.exceptions.SmtEvaluationException;

import java.math.BigInteger;

public final class QVar extends QExpression {
  private int _index;
  private String _name;

  /** The constructors are hidden, since IntegerExpressions should be made through an SmtProblem. */
  public QVar(int i) {
    _index = i;
    _name = "i" + _index;
    _simplified = true;
  }

  /** The constructors are hidden, since IntegerExpressions should be made through an SmtProblem. */
  QVar(int i, String name) {
    _index = i;
    _name = "[" + name + "]";
    _simplified = true;
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

  public QValue evaluate(QValuation val) {
    if (val == null) throw new SmtEvaluationException("i" + _index + " (" + _name + ")");
    else return val.queryQValueAssignment(_index);
  }

  public int compareTo(QExpression other) {
    return switch (other) {
      case QValue v -> 1;
      case QVar x -> _index  - x.queryIndex();
      case QMult cm -> compareTo(cm.queryChild()) <= 0 ? -1 : 1;
      case QAddition a -> -1;
    };
  }

}