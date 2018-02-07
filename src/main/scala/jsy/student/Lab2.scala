package jsy.student

import jsy.lab2.Lab2Like

object Lab2 extends jsy.util.JsyApplication with Lab2Like {
  import jsy.lab2.Parser
  import jsy.lab2.ast._

  /*
   * CSCI 3155: Lab 2
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with  your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something  that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   *
   */

  /* We represent a variable environment as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */



  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   *
   * You can catch an exception in Scala using:
   * try ... catch { case ... => ... }
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n
      case B(b) => if(b) 1 else 0
      case S(str) => {
        try{
          str.toDouble
        }
        catch {
          case e:NumberFormatException=> Double.NaN
        }
      }
      case Undefined => Double.NaN
    }
  }

  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => if (n == 0 || n.isNaN) false else true
      case B(b) => b
      case S(str) => if (str == "") false else true
      case Undefined => false
    }
  }

  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n match {
        //case negative if n < 0 => "-" + toStr(N(-n)) // saves us a few cases
        // case zero if n==0 => "0"
        //case infinity if n.isInfinity => "Infinity"
        case isWhole if n.isWhole() => isWhole.toInt.toString
        case notWhole => notWhole.toString
        case _ => "NaN"
      }
      case B(b) => if (b) "true" else "false"
      case S(s) => s
      case Undefined => "undefined"
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case Var(x) => lookup(env, x) // Get value associated in env map with our string
      case N(n) => N(n)
      case B(b) => B(b)
      case S(str) => S(str)
      case Undefined => Undefined
      /* Inductive Cases */
      case Unary(uop, e1) => {
        uop match {
          case Neg => {
            val v1 = eval(env,e1)
            val np = -toNumber(v1)
            N(np)
          }
          case Not => {
            val v1 = eval(env,e1)
            val bp = !toBoolean(v1)
            B(bp)
          }
        }
      }
      case Binary(bop, e1, e2) => {
        bop match {
          case Plus => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            (v1,v2) match {
              case (S(x), _) => {
                val str = toStr(v2)
                S(x.concat(str))
              }
              case (_, S(y)) =>{
                val str = toStr(v1)
                S(str.concat(y))
              }
              case (_,_) => N(toNumber(v1)+toNumber(v2))
            }
          }
          case Minus => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            val np = toNumber(v1)-toNumber(v2)
            N(np)
          }
          case Times => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            val np = toNumber(v1)*toNumber(v2)
            N(np)
          }
          case Div => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            val np = toNumber(v1)/toNumber(v2)
            N(np)
          }
          case Eq => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            if(v1 == v2){
              B(true)
            }
            else{
              B(false)
            }

          }
          case Ne => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)

            if(v1 != v2) {
              B(true)
            }else { B(false)}

          }
          case Lt => {
            val v1:Expr = eval(env, e1)
            val v2:Expr = eval(env, e2)
            (v1,v2) match {
              case (S(s1), S(s2)) =>
                val comparison:Int = s1.compareTo(s2)
                if (comparison < 0) {
                  B(true)
                } else {
                  B(false)
                }
              case (_,_) =>
                B(toNumber(v1) < toNumber(v2))
            }
          }
          case Le => {
            val v1:Expr = eval(env, e1)
            val v2:Expr = eval(env, e2)
            (v1,v2) match {
              case (S(s1), S(s2)) =>
                val comparison:Int = s1.compareTo(s2)
                if (comparison <= 0) {
                  B(true)
                } else {
                  B(false)
                }
              case (_,_) =>
                B(toNumber(v1) <= toNumber(v2))
            }
          }
          case Gt => {
            val v1:Expr = eval(env, e1)
            val v2:Expr = eval(env, e2)
            (v1,v2) match {
              case (S(s1), S(s2)) =>
                val comparison:Int = s1.compareTo(s2)
                if (comparison > 0) {
                  B(true)
                } else {
                  B(false)
                }
              case (_,_) =>
                B(toNumber(v1) > toNumber(v2))
            }
          }
          case Ge => {
            val v1:Expr = eval(env, e1)
            val v2:Expr = eval(env, e2)
            (v1,v2) match {
              case (S(s1), S(s2)) =>
                val comparison:Int = s1.compareTo(s2)
                if (comparison >= 0) {
                  B(true)
                } else {
                  B(false)
                }
              case (_,_) =>
                B(toNumber(v1) >= toNumber(v2))
            }
          }

          case And => {
            val v1 = eval(env, e1)
            if (toBoolean(v1)) eval(env, e2) else v1
          }
          case Or => {
            val v1 = eval(env, e1)
            if (toBoolean(v1)) v1 else eval(env, e2)
          }
          case Seq => {
            val v1 = eval(env,e1)
            val v2 = eval(env,e2)
            v2
          }
        }
      }
      case If(e1, e2, e3) => if (toBoolean(eval(env, e1))) eval(env, e2) else eval(env, e3)
      case ConstDecl(x, e1, e2) => {
        val v:Expr = eval(env, e1) // Evaluate down to guarantee we are at a value, otherwise extend fails a require()
        val newEnv = extend(env, x, v) // Add the value to the env map, a running list of variables
        eval(newEnv, e2) // Evaluate following expressions with the scoped variable
      }
      case Print(e1) => println(pretty(eval(env, e1))); Undefined
      case _ => ???
    }
  }



  /* Interface to run your interpreter from the command-line.  You can ignore what's below. */
  def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }

    val expr = Parser.parseFile(file)

    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }

    if (debug) { println("Evaluating ...") }

    val v = eval(expr)

     println(pretty(v))
  }

}
