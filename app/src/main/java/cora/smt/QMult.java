package cora.smt;
public final class QMult extends QExpression {
  private QValue _constant;
  private QExpression _main;

  /** The constructor is hidden, since IntegerExpressions should be made through the SmtFactory. */
  public QMult(QValue k, QExpression e) {
    _constant = k;
    _main = e;
    // if (_main.isSimplified() && !(_main instanceof QValue) &&
    //     !(_main instanceof QMult) && !(_main instanceof QAddition) &&
    //     _constant != 0 && _constant != 1) _simplified = true;
  }

  public QValue queryConstant() {
    return _constant;
  }

  public QExpression queryChild() {
    return _main;
  }

  public QValue evaluate(QValuation val) {
    return _constant.multiply(_main.evaluate(val));
  }


  public QExpression simplify() {
    //if (_simplified) return this;
    if (_constant.queryNumerator() == 0) return new QValue(0,1);
    if (_constant.queryNumerator() == _constant.queryDenominator()) return _main.simplify();
    return _main.simplify().multiply(_constant);
  }

  public QExpression multiply(QValue constant) {
    QValue newconstant = _constant.multiply(constant);
    if (newconstant.queryNumerator() == 0) return new QValue(0,1);
    if (newconstant.queryNumerator() == newconstant.queryDenominator()) return _main;
    if (constant.queryNumerator() == constant.queryDenominator()) return this;
    return new QMult(newconstant, _main);
  }

  public int compareTo(QExpression other) {
    return switch (other) {
      case QValue v -> 1;
      case QMult cm -> {
        int c = _main.compareTo(cm.queryChild());
        if (c != 0) yield c;
        else yield _constant.compareTo(cm.queryConstant());
      }
      default -> _main.compareTo(other) >= 0 ? 1 : -1;
    };
  }

}