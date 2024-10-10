
package cora.smt;

public final class QValue extends QExpression {
  private int _numerator;
  private int _denominator;


  //write simplify function
  public QValue(int n, int d) {
    if (d == 0) {
      throw new IllegalArgumentException("Denominator cannot be zero.");
    }
    _numerator = n/gcd(n,d);
    _denominator = d/gcd(n,d);
    // Handle negative denominator to keep denominator positive
    if (_denominator < 0) {
      _numerator = -_numerator;
      _denominator = -_denominator;
    }
  }

  public static int gcd(int a, int b) {
    if (b == 0) {
        return a;
    }
    return gcd(b, a % b);
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