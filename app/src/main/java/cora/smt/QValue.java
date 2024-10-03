
package cora.smt;

public final class QValue extends QExpression {
  private int _numerator;
  private int _denominator;



  public QValue(int n, int d) {
    if (d == 0) {
      throw new IllegalArgumentException("Denominator cannot be zero.");
    }
    // Handle negative denominator to keep denominator positive
    if (d < 0) {
      n = -n;
      d = -d;
    }
    _numerator = n;
    _denominator = d;
  }

  public int queryNumerator() {
    return _numerator;
  }
  public int queryDenominator() {
    return _denominator;
  }

  public QValue simplify() {
    //todo implement
    return this;
  }

  public QExpression add(int value) {
    //return new QValue(value + _k);
    throw new UnsupportedOperationException("TODO: Not yet implemented");
  }

  //cannot be Qexpression???
  public QValue multiply(QValue value) {
    return new QValue(value.queryNumerator() * _numerator, value.queryDenominator()*_denominator);
  }

  public int compareTo(QExpression other) {
    if (other instanceof QValue){
      QValue q = (QValue) other;
      long leftSide = (long) this._numerator * q.queryDenominator();
      long rightSide = (long) this._denominator * q.queryNumerator();
      if (leftSide < rightSide) {
          return -1; // this < other
      } else if (leftSide > rightSide) {
          return 1;  // this > other
      }
      return 0;
    }
    return -1;
  }




} 