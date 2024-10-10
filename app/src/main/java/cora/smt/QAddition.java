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
    //if (_simplified) return this;
    // acquire all children in simplified form
    ArrayList<QExpression> todo = new ArrayList<QExpression>();
    for (QExpression c : _children) {
      c = c.simplify();
      if (c instanceof QAddition a) todo.addAll(a._children);
      else todo.add(c);
    }
    // store the children into a treemap so we can count duplicates, but merge the contants directly
    TreeMap<QExpression,QValue> counts = new TreeMap<QExpression,QValue>();
    QValue constant = new QValue(0,1);
    for (QExpression c : todo) {
      QExpression main;
      QValue num;
      if (c instanceof QValue k) {constant = constant.add(k); continue; }
      else if (c instanceof QMult cm) { main = cm.queryChild(); num = cm.queryConstant();}
      else { main = c; num = new QValue(1,1); }
      QValue current = counts.get(main);
      if (current == null) counts.put(main, num);
      else counts.put(main, num.add(current));
    }
    // read them out
    ArrayList<QExpression> ret = new ArrayList<QExpression>();
    if (constant.queryNumerator() != 0){
      ret.add(constant);
    } 
    for (Map.Entry<QExpression,QValue> entry : counts.entrySet()) {
      QValue k = entry.getValue();
      if (k.queryDenominator()==k.queryNumerator()) ret.add(entry.getKey());
      else if (k.queryNumerator() != 0) ret.add(new QMult(k, entry.getKey()));
    }
    // return the result
    if (ret.size() == 0) return new QValue(0,1);
    if (ret.size() == 1) return ret.get(0);
    return new QAddition(ret);
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