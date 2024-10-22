

package cora.smt;
import charlie.smt.IExpPrinter;
public sealed abstract class QExpression implements Comparable<QExpression> permits QVar, QValue, QAddition, QMult {


    public abstract QExpression simplify();


    public final QExpression negate() {
        return multiply(new QValue(-1,1));
    }

    public abstract QValue evaluate(QValuation val);


    public QExpression multiply(QValue constant) {
        if (constant.queryNumerator() == 0) return new QValue(0,0);
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