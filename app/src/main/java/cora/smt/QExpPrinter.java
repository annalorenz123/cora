/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.smt;

/**
 * IExpPrinters are used in the overall output process of the tool.  This class provides a default
 * implementation, but is meant to be inherited.  You can for instance instantiate the IExpPrinter
 * to use unicode symbols, ascii-art, html, print smt-style or whatever is needed.
 */
public class QExpPrinter {
  /**
   * Returns a string representation of the given IntegerExpression (using the other print method).
   * This is only supplied as a public access function, and is not meant to be overridden.
   */
  public final String print(QExpression e) {
    StringBuilder builder = new StringBuilder();
    print(e, builder);
    return builder.toString();
  }

  /**
   * This is the main public access function.  Call this to ensure that the given integer
   * expression is printed to the given string builder.
   * 
   * To define your own IExpPrinter, you can either override this method directly -- in which
   * case there is no need to override any of the other methods in the class -- or override (some
   * of) the functions it calls, which are printVar, printValue, printDivision, printModulo,
   * printMultiplication, printAddition, printCMult, directly.
   */
  public void print(QExpression e, StringBuilder builder) {
    switch (e) {
      case QVar x: printVar(x, builder); break;
      case QValue k: printValue(k, builder); break;
      case QMult c: printQMult(c, builder); break;
      case QAddition a: printQAddition(a, builder); break;
    }
  }

  /**
   * Helper function: this prints the given expression with brackets around it, unless it is basic
   * (so a variable or variable) in which case it is printed unmodified.
   */
  protected final void printBracketed(QExpression e, StringBuilder builder) {
    switch (e) {
      case QVar x: printVar(x, builder); break;
      case QValue k: printValue(k, builder); break;
      default:
        builder.append("(");
        print(e, builder);
        builder.append(")");
    }
  }

  /**
   * Override this function to change how integer variables are printed (if print is left unmasked).
   * The default functionality is just to add the name to the string builder unmodified.
   */
  protected void printVar(QVar x, StringBuilder builder) {
    builder.append(x.queryName());
  }

  /**
   * Override this function to change how integer values are printed (if print is left unmasked).
   * The default functionality is just to add the value to the string builder.
   */
  protected void printValue(QValue k, StringBuilder builder) {
    if (k.queryDenominator() == 1){
        builder.append("" + k.queryNumerator());
    }
    else{
        builder.append("" + k.queryNumerator() + "/" + k.queryDenominator());
    }
    
  }



  /**
   * Override this function to change how multiplications with a constant are printed (if print is
   * left unmasked).
   * The default functionality is to print constant * main, with brackets around main if main is
   * neither basic nor a multiplication.
   */
  protected void printQMult(QMult c, StringBuilder builder) {
    if (c.queryConstant().queryNumerator() == -c.queryConstant().queryDenominator()){
        builder.append("-");    
    }
    else if (c.queryConstant().queryNumerator() != c.queryConstant().queryDenominator()){
        builder.append("" + c.queryConstant());
        builder.append(" * ");
    }
    printBracketed(c.queryChild(), builder);
  }

  /**
   * Override this function to change how additions are printed (if print is left unmasked).
   * The default functionality is to print elem1 + ... + elemn, with none of the elements bracketed.
   */
  protected void printQAddition(QAddition a, StringBuilder builder) {
    if (a.numChildren() == 0) { builder.append("(0)"); return; }
    print(a.queryChild(1), builder);
    for (int i = 2; i <= a.numChildren(); i++) {
      builder.append(" + ");
      print(a.queryChild(i), builder);
    }
  }
}

