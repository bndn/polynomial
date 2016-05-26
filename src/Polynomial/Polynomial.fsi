module Polynomial

open Expression

type Atom = ANum of float | AExponent of string * int | ARoot of string * int| AAdd | ASub | AMul | ADiv

type AtomGroup = Atom list

type SimpleExpr = AtomGroup list

type Poly = P of Map<int, SimpleExpr>

/// <summary>
/// Given an expression, substitue all occurences of a variable with a different expression.
/// </summary>
/// <param name=e>The expression to substitute in.</param>
/// <param name=x>The variable to subtitute in the expression.</param>
/// <param name=ex>The expression to subtitute the variable with.</param>
/// <returns>The expression with all occurences of x substituted with ex.</returns>
val subst: Expr -> (string * Expr) -> Expr

/// <summary>
/// Convert an expression to a polynomial with respect to a variable.
/// </summary>
/// <param name=v>The variable to isolate.</param>
/// <param name=e>The expression to convert.</param>
/// <returns>The resulting polynomial.</returns>
val parse : string -> Expr -> Poly

/// <summary>
/// Evaluate the sum of an atom list list and substitute values from given map.
/// </summary>
/// <param name=m>The Map<string, float> with substitude variables in expression.</param>
/// <param name=all>The atom list list.</param>
/// <returns>The resulting float value from the evaluated expression.</returns>
val evaluateAtomGroup : Map<string, float> -> Atom list list -> float

/// <summary>
/// Evaluate the sum of an abstract syntax tree and substitute values from given map.
/// </summary>
/// <param name=m>The Map<string, float> with substitude variables in expression.</param>
/// <param name=e>The abstract syntax trees.</param>
/// <returns>The resulting float value from the evaluated expression.</returns>
val evaluateExpr : Map<string, float> -> Expr -> float

/// <summary>
/// Find the derivative of an abstract syntax tree with respect to a variable.
/// </summary>
/// <see cref="https://www.mathsisfun.com/calculus/derivatives-rules.html">Derivative Rules</see>
/// <see cref="https://proofwiki.org/wiki/Derivative_of_Nth_Root">Derivative of Nth Root</see>
/// <param name=k>The variable to find the derivative of.</param>
/// <param name=e>The abstract syntax tree.</param>
/// <returns>The resulting abstract syntax tree.</returns>
val derivative : string -> Expr -> Expr

/// <summary>
/// Find and estimation of each root in the interval of a polynomial.
/// </summary>
/// <param name=maxInterval>The max root value which can be found. Can NOT be infinite.</param>
/// <param name=minInterval>The min root value which can be found. Can NOT be infinite.</param>
/// <param name=error>The error of the root estimate.</param>
/// <param name=poly>The list of first polynomials float values.</param>
/// <returns>A list of floats, representing the distance to each root.</returns>
val findRoots : float -> float -> float -> List<float> -> List<float>