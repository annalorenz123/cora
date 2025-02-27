

package cora.smt;
import charlie.smt.IExpPrinter;
import java.math.BigInteger;
public sealed abstract class QExpression implements Comparable<QExpression> permits QVar, QValue, QAddition, QMult {

        /**
     * This variable should be set to true in the constructor if the IntegerExpression is simplified.
     * Note that being simplified means that all sub-expressions must also be simplified.
     */
    protected boolean _simplified;

    /**
     * The _simplified variable is set to false by default, but inheriting classes should all set it
     * to true if the class is in fact simplified.
     */
    protected QExpression() {
        _simplified = false;
    }

    public abstract QExpression simplify();


    public final QExpression negate() {
        return this.multiply(new QValue(BigInteger.valueOf(-1),BigInteger.valueOf(1)));
    }

    public abstract QValue evaluate(QValuation val);

    /** This returns whether the IntegerExpression is currently in simplified form.  */
    public final boolean isSimplified() {
        return _simplified;
    }


    public QExpression multiply(QValue constant) {
        if (constant.queryNumerator() == BigInteger.valueOf(0)) return new QValue(BigInteger.valueOf(0),BigInteger.valueOf(0));
        if (constant.queryNumerator() == constant.queryDenominator()) return this;
        return new QMult(constant, this);
    }


    public final String toString() {
        QExpPrinter printer = new QExpPrinter();
        return printer.print(this);
    }

    public final boolean equals(Object other) {
        return (other instanceof QExpression) && compareTo((QExpression)other) == 0;
    }
}    