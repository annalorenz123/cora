package cora.smt;
import java.math.BigInteger;

public final class QValue extends QExpression {
  private BigInteger _numerator;
  private BigInteger _denominator;

  // Constructor
  public QValue(BigInteger n, BigInteger d) {
    if (d.equals(BigInteger.ZERO)) {
      throw new IllegalArgumentException("Denominator cannot be zero.");
    }
    
    // Simplify numerator and denominator by their GCD
    BigInteger gcd = n.gcd(d);
    _numerator = n.divide(gcd);
    _denominator = d.divide(gcd);

    // Handle negative denominator to keep it positive
    if (_denominator.compareTo(BigInteger.ZERO) < 0) {
      _numerator = _numerator.negate();
      _denominator = _denominator.negate();
    }
  }

  // Overload constructor for long values
  public QValue(long n, long d) {
    this(BigInteger.valueOf(n), BigInteger.valueOf(d));
  }

  // Query methods
  public BigInteger queryNumerator() {
    return _numerator;
  }
  
  public BigInteger queryDenominator() {
    return _denominator;
  }

  // Simplify method
  public QValue simplify() {
    BigInteger gcd = _numerator.gcd(_denominator);
    _numerator = _numerator.divide(gcd);
    _denominator = _denominator.divide(gcd);
    return this;
  }

  // Adding two QValues
  public QValue add(QValue q) {
    //System.out.println("adding " + this + " and " + q);
    
    BigInteger numerator = _numerator.multiply(q.queryDenominator())
                         .add(_denominator.multiply(q.queryNumerator()));
    BigInteger denominator = _denominator.multiply(q.queryDenominator());
    
    QValue result = new QValue(numerator, denominator);
    //System.out.println("result is " + result);
    return result;
  }

  public QValue simplify (QValue numerator , QValue denominator){
    return new QValue (numerator.queryNumerator().multiply(denominator.queryDenominator()), numerator.queryDenominator().multiply(denominator.queryNumerator()));
  }

  // Multiply two QValues
  public QValue multiply(QValue value) {
    //System.out.println("multiplying " + this + " and " + value);
    
    BigInteger numerator = _numerator.multiply(value.queryNumerator());
    BigInteger denominator = _denominator.multiply(value.queryDenominator());
    
    QValue result = new QValue(numerator, denominator);
    //System.out.println("result is " + result);
    return result;
  }

  // Compare two QValues
  public int compareTo(QExpression other) {
    if (other instanceof QValue q) {
      BigInteger leftSide = _numerator.multiply(q.queryDenominator());
      BigInteger rightSide = _denominator.multiply(q.queryNumerator());
      
      return leftSide.compareTo(rightSide); // Returns -1, 0, or 1
    }
    return -1;
  }

  public QValue evaluate(QValuation val) {
    return this;
  }

  // // Optional: Implement a negate function if needed
  // public QValue negate() {
  //   return new QValue(_numerator.negate(), _denominator);
  // }

  // public String toString() {
  //   return _numerator + "/" + _denominator;
  // }
}
