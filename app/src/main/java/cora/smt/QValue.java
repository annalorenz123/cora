
package cora.smt;

public final class QValue extends QExpression {
  private long _numerator;
  private long _denominator;


  //write simplify function
  public QValue(long n, long d) {
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

  public static long gcd(long a, long b) {
    if (b == 0) {
        return a;
    }
    return gcd(b, a % b);
  }


  public QValue simplify (QValue numerator , QValue denominator){
    return new QValue (numerator.queryNumerator()*denominator.queryDenominator(), numerator.queryDenominator()*denominator.queryNumerator());
  }

  public long queryNumerator() {
    return _numerator;
  }
  public long queryDenominator() {
    return _denominator;
  }

  public QValue simplify() {
    //todo implement
    this._numerator = _numerator/gcd(this._numerator,this._denominator);
    this._denominator = _denominator/gcd(this._numerator,this._denominator);
    return this;
  }

  public QValue evaluate(QValuation val) {
    return this;
  }


  public QValue add(QValue q) {
    //System.out.println ("adding " + this + " and " +q );
    //System.out.println ("result is " + (_numerator * q.queryDenominator() + (_denominator* q.queryNumerator()) +"/"+_denominator * q.queryDenominator()));
    return new QValue ((_numerator * q.queryDenominator()) + (_denominator* q.queryNumerator()), _denominator * q.queryDenominator());
  }

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