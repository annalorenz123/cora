
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


  public QValue simplify (QValue numerator , QValue denominator){
    return new QValue (numerator.queryNumerator()*denominator.queryDenominator(), numerator.queryDenominator()*denominator.queryNumerator());
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


  public QValue add(QValue q) {
    return new QValue ((_numerator * q.queryDenominator()) + (_denominator* q.queryNumerator()), _denominator * q.queryDenominator());
  }

  //cannot be Qexpression???
  public QValue multiply(QValue value) {
    return new QValue(value.queryNumerator() * _numerator, value.queryDenominator()*_denominator);
  }
  public int compareTo(QExpression other) {
    if (other instanceof QValue q ){
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