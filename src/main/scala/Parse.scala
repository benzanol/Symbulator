package sympany.parse

import scala.util.chaining._

import scala.scalajs.js.annotation.JSExportTopLevel

import sympany.symbolics._
import sympany.simplification.Simplify.simplify

object Parse {
	
	// Parse a complete latex string into a symbolic object
	@JSExportTopLevel("parseLatex")
	def parseLatex(raw: String): Option[Sym] = try {
		println(f"parseLatex $raw")
		var str = raw
			.replaceAll("\\\\right", "")
			.replaceAll("\\\\left", "")
			.replaceAll("\\\\cdot", " ")
		
		var sum = List[Sym]()
		var prod = List[Sym]()
		
		while (str.nonEmpty)
			if (str(0) == '+') {
				if (prod.isEmpty) return None
				
				str = str.tail
				sum :+= SymProd(prod:_*)
				prod = List[Sym]()
				
			} else if (str(0) == '-') {
				if (prod.isEmpty && sum.nonEmpty) return None
				if (prod.nonEmpty) sum :+= SymProd(prod:_*)
				
				str = str.tail
				prod = List[Sym](SymInt(-1))
				
			} else if (str.head == ' ') {
				str = str.tail
			} else {
				readExprPower(str) match {
					case None => return None
					case Some((sym, newStr)) => {
						str = newStr
						prod :+= sym
					}
				}
			}
		
		if (prod.isEmpty) return None
		else sum :+= SymProd(prod:_*)
		
		val simplified = simplify(SymSum(sum:_*))
		println(f"s= $simplified")
		Some(simplified)
	} catch {
		case error: Throwable => None
	}
	
	/* Given a string, and a left and right delimiter, for instance ( and ),
	 * return a tuple with the first balanced expression based on the delimiters,
	 * and the remaining part of the string.
	 * For example, "(2 * (x + 3)) - (4 / 7)" will return "(2 * (x + 3))" and " - (4 / 7)"
	 * when called with parenthesis as delimiters
	 */
	def readBalanced(str: String, left: Char, right: Char): (String, String) = {
		if (str.head != left) return ("", str)
		
		var level = 0
		for (i <- 0 until str.length) {
			str(i) match {
				case c if c == left => level += 1
				case c if c == right => level -= 1
				case _ if level == 0 => return (str.substring(1, i-1), str.substring(i))
				case _ => ()
			}
		}
		return (str.substring(1, str.length - 1), "")
	}
	
	// Read the expr, then if its followed by an exponent, read that
	def readExprPower(str: String): Option[(Sym, String)] = readExpr(str) match {
		case None => None
		case a @ Some((expr, str1)) =>
			if (str1.headOption == Some('^')) {
				readExpr(str1.tail, true) match {
					case Some((pow, str2)) => Some((SymPow(expr, pow), str2))
					case None => a
				}
			} else a
	}
	
	/* Only read the smallest possible expression from the start of str
	 * For instance, "71x+4" will return Int(71) and "x+4", and
	 * "(2+x)^5 - 1" will return Sum(Int(2), Var(x)) and "^5 - 1"
	 */
	def readExpr(str: String, pow: Boolean = false): Option[(Sym, String)] = {
		str(0) match {
			case ' ' => readExpr(str.tail, pow)
			case '(' => readBalanced(str, '(', ')').pipe{
				case (e, rest) => parseLatex(e).flatMap{s => Some((s, rest))}
			}
			case '{' => readBalanced(str, '{', '}').pipe{
				case (e, rest) => parseLatex(e).flatMap{s => Some((s, rest))}
			}
			case '\\' => readLatexCommand(str)
			case n if '0' to '9' contains n =>
				if (pow) Some((SymInt(n.toString.toInt), str.tail))
				else Some(readNumber(str))
			case l if ('A' to 'Z') ++ ('a' to 'z') contains l =>
				Some((SymVar(Symbol(l.toString)), str.tail))
			case _ => None
		}
	}
	
	// If str starts with a number, parse it
	def readNumber(str: String): (Sym, String) = {
		// Whether the decimal point has already been reached
		var decimal = false
		
		// Set to false as soon as a non-number character is reached
		var continue = true
		
		// Keep adding characters until a non-number character is reached
		var i = 0
		while (i < str.length && continue) str(i) match {
			case '.' if !decimal => decimal = true ; i += 1
			case n if '0' to '9' contains n => i += 1
			case _ => continue = false
		}
		
		val sym = str.substring(0, i).split("\\.") match {
			// An integer number (no decimal point)
			case Array(int: String) if int.nonEmpty => SymInt(int.toInt)
			// A number with a decimal point
			case Array(int, dec) => SymFrac((int + dec).toInt, BigInt(10).pow(dec.length))
			// An invalid number
			case _ => throw new Exception(f"Not a number: $str") ; SymInt(0)
		}
		(sym, str.substring(i))
	}
	
	// If str starts with a latex command, parse it
	def readLatexCommand(str: String): Option[(Sym, String)] = {
		val segments = readLatexSegments(str)
		if (segments._1.isEmpty) return None
		
		val rest = segments._2
		val cmd :: argStrings = segments._1
		
		// Quit if any of the arguments are invalid expressions
		val args = argStrings.flatMap(parseLatex)
		if (args.length < argStrings.length) return None
		
		// Create a symbolic expression based on the command
		cmd match {
			case "frac" => Some(SymProd(args(0), SymPow(args(1), SymInt(-1))) -> rest)
			case "ln" => readExpr(rest).map{
				case (e, rest2) => (SymLog(e) -> rest2)
			}
			case "log" => readExpr(rest).map{
				case (e, rest2) => (SymLog(e, SymInt(10)) -> rest2)
			}
			case "log_" => readExpr(rest, pow=true).flatMap{
				case (base, rest2) => readExpr(rest2).map{
					case (e, rest3) => (SymLog(e, base) -> rest3)
				}
			}
			case _ => None
		}
	}
	
	// Given that str starts with a latex command, return the segments of the command
	// (a list of the command and arguments), and the remainder of the string
	def readLatexSegments(str: String): (List[String], String) = {
		// Characters that should not appear in the name of the command,
		// but can of couse appear in the command arguments
		val badChars = " \\(){}0123456789"
		
		var parts = List[String]()
		var start = 1 // The first character should be the backslash
		var level = 0
		
		for (i <- 1 until str.length) str(i) match {
			case '{' if level == 0 => {
				parts :+= str.substring(start, i)
				start = i
				level = 1
			}
			case '{' => level += 1
			case '}' => level -= 1
			case c if parts.isEmpty && !(badChars contains c) => ()
				
			// If the level is 0 and the character isn't "{", it must be the end of the command
			case _ if level == 0 => {
				parts :+= str.substring(start, i)
				return (parts, str.substring(i))
			}
				
			case _ => ()
		}
		
		parts :+= str.substring(start)
		
		// Remove angle brackets from the arguments
		parts = parts.head :: parts.tail.map{s => s.substring(1, s.length - 1)}
		
		return (parts, "")
	}
}
