package cora.smt;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.ArrayList;
import charlie.exceptions.IndexingException;
import charlie.util.Pair;




public final class QAddition extends QExpression {
  private ArrayList<QExpression> _children;

  private void addChild(QExpression child) {
    if (child instanceof QAddition a) {
      for (QExpression c : a._children) _children.add(c);
    }
    else _children.add(child);
  }

  /** Constructors are hidden, since IntegerExpressions should be made through the SmtFactory. */
  public QAddition(QExpression a, QExpression b) {
    _children = new ArrayList<QExpression>();
    addChild(a);
    addChild(b);
  }

  /** Constructors are hidden, since IntegerExpressions should be made through the SmtFactory. */
  public QAddition(List<QExpression> args) {
    _children = new ArrayList<QExpression>();
    for (QExpression arg : args) addChild(arg);
  }

  /** Private constructor when the array does not need to be copied and checked. */
  private QAddition(ArrayList<QExpression> args, boolean simpl) {
    _children = args;
  }

  /**
   * Adds a constant to the addition and returns the result.  If the Addition was simplified, then
   * so is the result.
   */
  public QExpression add(QValue constant) {
    return new QAddition (this, constant).simplify();
    // if (constant.queryNominator() == 0) return this;
    // if (_children.size() == 0) return constant;
    // if (_children.get(0) instanceof QValue k) {
    //   return new Addition ()
    //   if (k.queryValue() == -constant) {
    //     if (_children.size() == 2) return _children.get(1);
    //     else return new Addition(_children.subList(1, _children.size()));
    //   }
    //   if (_simplified) {
    //     ArrayList<IntegerExpression> ret = new ArrayList<IntegerExpression>(_children);
    //     ret.set(0, new IValue(k.queryValue() + constant));
    //     return new Addition(ret, true);
    //   }
    //   else {
    //     _children.set(0, new IValue(k.queryValue() + constant));
    //     Addition ret = new Addition(_children);
    //     _children.set(0, k);
    //     return ret;
    //   }
    // }
    // ArrayList<IntegerExpression> parts = new ArrayList<IntegerExpression>();
    // parts.add(new IValue(constant));
    // parts.addAll(_children);
    // return new Addition(parts, _simplified);
  }

  /** Returns the number of children this Addition has */
  public int numChildren() {
    return _children.size();
  }

  /** For 1 ≤ index ≤ numChildren(), returns the corresponding child. */
  public QExpression queryChild(int index) {
    if (index <= 0 || index > _children.size()) {
      throw new IndexingException("Addition", "queryChild", index, 1, _children.size());
    }
    return _children.get(index-1);
  }


  /** Returns a simplified representation of the addition */
  public QExpression simplify() {
    return this;
    //throw new UnsupportedOperationException("TODO: Not yet implemented");
  }

  public QExpression multiply(QValue constant) {
    if (constant.queryNumerator() == 0) return new QValue(0,0);
    if (constant.queryNumerator()  == constant.queryDenominator()) return this;
    ArrayList<QExpression> cs = new ArrayList<QExpression>();
    for (int i = 0; i < _children.size(); i++) cs.add(_children.get(i).multiply(constant));
    return new QAddition(cs);
  }

  public int compareTo(QExpression other) {
    return -1;
    //throw new UnsupportedOperationException("TODO: Not yet implemented");
  }
}