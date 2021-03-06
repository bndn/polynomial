﻿/// Copyright (C) 2016 The Authors.
module Polynomial.Test

open Expression
open Xunit;
open FsUnit.Xunit;

[<Literal>]
let EPSILON = 1.0e-6

// Pseudo code for chmutov
let factorial x =
    if x = 0 then 1 else
    let rec fac_aux a acc =
      if a >= x then
        a * acc
      else
        fac_aux (a + 1) (a * acc)
    fac_aux 1 x
let comb a b =
    let x = float (factorial a) in
    let y = float (factorial b) in
    let z = float (factorial (a - b)) in
        x / (y * z)
let rec strSum n f : string =
    if n = 0 then
        f 0
    else
        f n + " + " + (strSum (n - 1) f)
let chmutov degree =
    let T x = strSum (degree / 2) (fun (k : int) -> (string (comb degree (2 * k))) + " * (" + x + "^2 + -1.0)^" + (string k) + " * " + x + "^" + (string (degree - (2 * k))))
    (T "x" + " + " + T "y" + " + " + T "z")

let ex' = Expression.parse ("ox + t * dx")
let ey' = Expression.parse ("oy + t * dy")
let ez' = Expression.parse ("oz + t * dz")

[<Fact>]
let ``Degree of polynomials 1st`` () =
    let m11 = match (Polynomial.parse "t" (List.fold subst (Expression.parse "x") [("x",ex');("y",ey');("z",ez')])) with P(m) -> m
    let m12 = match (Polynomial.parse "t" (List.fold subst (Expression.parse "y") [("x",ex');("y",ey');("z",ez')])) with P(m) -> m
    let m13 = match (Polynomial.parse "t" (List.fold subst (Expression.parse "z") [("x",ex');("y",ey');("z",ez')])) with P(m) -> m

    // Find highest degree in polynomial
    m11 |> Map.toList |> List.maxBy fst |> fst |> should equal 1
    m12 |> Map.toList |> List.maxBy fst |> fst |> should equal 1
    m13 |> Map.toList |> List.maxBy fst |> fst |> should equal 1

[<Fact>]
let ``Degree of polynomials 2nd`` () =
    let m21 = match (Polynomial.parse "t" (List.fold subst (Expression.parse "x^2+y^2+z^2 - 0.5^2") [("x",ex');("y",ey');("z",ez')])) with P(m) -> m
    let m22 = match (Polynomial.parse "t" (List.fold subst (Expression.parse "(x^2+y^2+z^2)_2 + -0.5") [("x",ex');("y",ey');("z",ez')])) with P(m) -> m
    let m23 = match (Polynomial.parse "t" (List.fold subst (Expression.parse (chmutov 2)) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m

    m21 |> Map.toList |> List.maxBy fst |> fst |> should equal 2
    m22 |> Map.toList |> List.maxBy fst |> fst |> should equal 2
    m23 |> Map.toList |> List.maxBy fst |> fst |> should equal 2

[<Fact>]
let ``Degree of polynomials 3rd`` () =
    let m31 = match (Polynomial.parse "t" (List.fold subst (Expression.parse (chmutov 3)) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m

    m31 |> Map.toList |> List.maxBy fst |> fst |> should equal 3

[<Fact>]
let ``Degree of polynomials 4th`` () =
    let r = 0.5
    let R = 1.5
    let eq = let rs1 = "(" + (string R) + "^2" + " + " + (string r) + "^2)"
             let rs2 = "(" + (string R) + "^2" + " - " + (string r) + "^2)"
             let sx = "x^4 + 2x^2*y^2 + 2x^2*z^2 - 2*" + rs1 + "*x^2"
             let sy = "y^4 + 2y^2*z^2 + 2*" + rs2 + "*y^2"
             let sz = "z^4 - 2*" + rs1 + "*z^2"
             let sc = rs2 + "^2"
             sx + " + " + sy + " + " + sz + " + " + sc

    let m41 = match (Polynomial.parse "t" (List.fold subst (Expression.parse "(((x^2 + y^2)_2 + -1.5)^2 + z^2)_2 + -0.5") [("x",ex');("y",ey');("z",ez')])) with P(m) -> m
    let m42 = match (Polynomial.parse "t" (List.fold subst (Expression.parse eq) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m
    let m43 = match (Polynomial.parse "t" (List.fold subst (Expression.parse ("(((x^2 + y^2)_2 + -" + (string R) + ")^2 + z^2)_2 + -" + (string r))) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m
    let m44 = match (Polynomial.parse "t" (List.fold subst (Expression.parse (chmutov 4)) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m
    let m45 = match (Polynomial.parse "t" (List.fold subst (Expression.parse "(x - 2)^2(x+2)^2 + (y - 2)^2(y+2)^2 + (z - 2)^2(z+2)^2 + 3(x^2*y^2 + x^2z^2 + y^2z^2) + 6x y z - 10(x^2 + y^2 + z^2) + 22") [("x",ex');("y",ey');("z",ez')])) with P(m) -> m

    m41 |> Map.toList |> List.maxBy fst |> fst |> should equal 4
    m42 |> Map.toList |> List.maxBy fst |> fst |> should equal 4
    m43 |> Map.toList |> List.maxBy fst |> fst |> should equal 4
    m44 |> Map.toList |> List.maxBy fst |> fst |> should equal 4
    m45 |> Map.toList |> List.maxBy fst |> fst |> should equal 4

[<Fact>]
let ``Degree of polynomials 5th`` () =
    let m51 = match (Polynomial.parse "t" (List.fold subst (Expression.parse (chmutov 5)) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m

    m51 |> Map.toList |> List.maxBy fst |> fst |> should equal 5

[<Fact>]
let ``Degree of polynomials 6th`` () =
    let m61 = match (Polynomial.parse "t" (List.fold subst (Expression.parse (chmutov 6)) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m
    let m62 = match (Polynomial.parse "t" (List.fold subst (Expression.parse "(x^2 + (4.0/9.0)*y^2 + z^2 - 1)^3 - x^2 * z^3 - (9.0/80.0)*y^2*z^3") [("x",ex');("y",ey');("z",ez')])) with P(m) -> m

    m61 |> Map.toList |> List.maxBy fst |> fst |> should equal 6
    m62 |> Map.toList |> List.maxBy fst |> fst |> should equal 6

[<Fact>]
let ``Degree of polynomials 7th`` () =
    let m71 = match (Polynomial.parse "t" (List.fold subst (Expression.parse (chmutov 7)) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m

    m71 |> Map.toList |> List.maxBy fst |> fst |> should equal 7

[<Fact>]
let ``Degree of polynomials 8th`` () =
    let m81 = match (Polynomial.parse "t" (List.fold subst (Expression.parse (chmutov 8)) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m

    m81 |> Map.toList |> List.maxBy fst |> fst |> should equal 8

[<Fact>]
let ``Degree of polynomials 9th`` () =
    let m91 = match (Polynomial.parse "t" (List.fold subst (Expression.parse (chmutov 9)) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m

    m91 |> Map.toList |> List.maxBy fst |> fst |> should equal 9

[<Fact>]
let ``Degree of polynomials 10th`` () =
    let m101 = match (Polynomial.parse "t" (List.fold subst (Expression.parse (chmutov 10)) [("x",ex');("y",ey');("z",ez')])) with P(m) -> m

    m101 |> Map.toList |> List.maxBy fst |> fst |> should equal 10

[<Fact>]
let ``Evaluate atom group`` () =
    evaluateAtomGroup Map.empty [[ANum 2.0]]                                             |> should equal 2.0
    evaluateAtomGroup Map.empty [[ANum 2.0; ANum 3.0];[ANum 4.0]]                        |> should equal 10.0
    evaluateAtomGroup Map.empty [[ANum 2.0; ANum 3.0; ANum 4.0];[ANum 4.0];[ANum 5.0]]   |> should equal 33.0

[<Fact>]
let ``Evaluate atom group with variables`` () =
    let valueMap = Map.ofList [("x", 4.0); ("y", 5.0); ("z", 6.0)]

    evaluateAtomGroup valueMap [[ANum 2.0; AExponent("x", 2)]]                           |> should equal 32.0
    evaluateAtomGroup valueMap [[ANum 3.0; AExponent("x", 3)];[AExponent("y", 2); AExponent("x", 2); AExponent("y", 1)]] |> should equal 2192.0

[<Fact>]
let ``Invalid atom group evaluation`` () =
    (fun () -> evaluateAtomGroup Map.empty [[ANum 2.0; AExponent("x", 2)]]    |> ignore) |> shouldFail
    (fun () -> evaluateAtomGroup Map.empty [[AExponent("x", 1)]]              |> ignore) |> shouldFail

[<Fact>]
let ``Evaluate expressions`` () =
    evaluateExpr Map.empty (Expression.parse "2")                             |> should equal 2.0
    evaluateExpr Map.empty (Expression.parse "2 + 5.3")                       |> should equal 7.3
    evaluateExpr Map.empty (Expression.parse "2 - 5.3")                       |> should equal -3.3
    evaluateExpr Map.empty (Expression.parse "2 * 5.3")                       |> should equal 10.6
    evaluateExpr Map.empty (Expression.parse "(27 / 3)_2 * (5 + 4)")          |> should equal 27.0

    evaluateExpr Map.empty (Expression.parse "((27 / 3)_2 * (1 + 2)^2)_3")    |> should equal 3.0

[<Fact>]
let ``Evaluate expressions with variables`` () =
    let valueMap = Map.ofList [("x", 4.0); ("y", 5.0); ("z", 6.0)]

    evaluateExpr valueMap (Expression.parse "2 * x")                          |> should equal 8.0
    evaluateExpr valueMap (Expression.parse "y * x^3")                        |> should equal 320.0
    evaluateExpr valueMap (Expression.parse "(y + x^2) * (z / 2)")            |> should equal 63.0

[<Fact>]
let ``Invalid expressions evaluation`` () =
    (fun () -> evaluateExpr Map.empty (Expression.parse "x")      |> ignore)  |> shouldFail
    (fun () -> evaluateExpr Map.empty (Expression.parse "8+9+x")  |> ignore)  |> shouldFail

///<remark>
/// All the derivatives are put up against an online derivative calculated and the results when evaluating the expressions are compared.
///</remark>
///<see cref="http://www.derivative-calculator.net/">Derivative Calculator</see>
[<Fact>]
let ``Simple derivative`` () =
    let d1 = (Expression.parse >> derivative "x") "x"
    let d2 = (Expression.parse >> derivative "y") "y"

    // Online calc: x -> 1
    Polynomial.evaluateExpr Map.empty d1 |> should equal 1.0
    Polynomial.evaluateExpr Map.empty d2 |> should equal 1.0

[<Fact>]
let ``Derivative with addition and subtraction`` () =
    let d1 = (Expression.parse >> derivative "x") "x + 3"
    let d2 = (Expression.parse >> derivative "x") "x + x"
    let d3 = (Expression.parse >> derivative "x") "x + y"
    let d4 = (Expression.parse >> derivative "x") "x - x"
    let d5 = (Expression.parse >> derivative "x") "x - 3"

    // Online calc: x + 3 -> 1
    Polynomial.evaluateExpr Map.empty d1 |> should equal 1.0
    // Online calc: x + x -> 2
    Polynomial.evaluateExpr Map.empty d2 |> should equal 2.0
    // Online calc: x + y -> 2
    Polynomial.evaluateExpr Map.empty d3 |> should equal 1.0
    // Online calc: x - x -> 0
    Polynomial.evaluateExpr Map.empty d4 |> should equal 0.0
    // Online calc: x - 3 -> 1
    Polynomial.evaluateExpr Map.empty d5 |> should equal 1.0

[<Fact>]
let ``Derivative with multiplication`` () =
    let d1 = (Expression.parse >> derivative "x") "x * 2"
    let d2 = (Expression.parse >> derivative "x") "9 * x"
    let d3 = (Expression.parse >> derivative "x") "x * x"

    let valueMap = Map.ofList [("x", 3.0)]

    // Online calc: x * 2 -> 2
    Polynomial.evaluateExpr valueMap d1 |> should equal 2.0
    // Online calc: 9 * x -> 9
    Polynomial.evaluateExpr valueMap d2 |> should equal 9.0
    // Online calc: x * x -> 2x
    Polynomial.evaluateExpr valueMap d3 |> should equal 6.0

[<Fact>]
let ``Derivative with division`` () =
    let d1 = (Expression.parse >> derivative "x") "x / 4"
    let d2 = (Expression.parse >> derivative "x") "(x + 5) / (x * 3)"
    let d3 = (Expression.parse >> derivative "x") "5 / x"

    let valueMap = Map.ofList [("x", 4.0)]

    // Online calc: x / 4 -> 1 / 4
    Polynomial.evaluateExpr valueMap d1 |> should equal 0.25
    // Online calc: (x + 5) / (x * 3) -> -(5 / (3 (x^2)))
    Polynomial.evaluateExpr valueMap d2 |> should equal (Polynomial.evaluateExpr valueMap (Expression.parse "-(5 / (3 (x^2)))"))
    // Online calc: 5 / x -> - (5 / x^2)
    Polynomial.evaluateExpr valueMap d3 |> should equal (Polynomial.evaluateExpr valueMap (Expression.parse "- (5 / x^2)"))

[<Fact>]
let ``Derivative with exponents`` () =
    let d1 = (Expression.parse >> derivative "x") "x^2"
    let d2 = (Expression.parse >> derivative "x") "x^3"
    let d3 = (Expression.parse >> derivative "x") "(x + 3)^2"

    let valueMap = Map.ofList [("x", 4.0)]

    // Online calc: x^2 -> 2x
    Polynomial.evaluateExpr valueMap d1 |> should equal 8.0
    // Online calc: x^3 -> 3x^2
    Polynomial.evaluateExpr valueMap d2 |> should equal 48.0
    // Online calc: (x + 3)^2 -> 2 (x + 3)
    Polynomial.evaluateExpr valueMap d3 |> should equal 14.0

[<Fact>]
let ``Derivative with root`` () =
    let d1 = (Expression.parse >> derivative "x") "x_2"
    let d2 = (Expression.parse >> derivative "x") "x_3"
    let d3 = (Expression.parse >> derivative "x") "(x + 5)_2"

    let valueMap = Map.ofList [("x", 4.0)]

    // Online calc: x^(1/2) -> 1 / (2 (x)^(1/2))
    Polynomial.evaluateExpr valueMap d1 |> should equal 0.25
    // Online calc: x^(1/3) -> 1 / (3 (x)^(2/3))
    let expected = 0.13228342099
    (((Polynomial.evaluateExpr valueMap d2) - expected) > -EPSILON && ((Polynomial.evaluateExpr valueMap d2) - expected) < EPSILON) |> should equal true
    // Online calc: (x + 5)^(1/2) -> 1 / (2 (x + 5)^(1/2))
    let expected = 0.16666666666
    (((Polynomial.evaluateExpr valueMap d3) - expected) > -EPSILON && ((Polynomial.evaluateExpr valueMap d3) - expected) < EPSILON) |> should equal true

[<Fact>]
let ``Multiple variables and combination of rules`` () =
    let d1 = (Expression.parse >> derivative "x") "x^2 + y^2 + z^2 - 5^2"
    let d2 = (Expression.parse >> derivative "x") "(x^2 + y^2 + z^2)_2 + -5"
    let d3 = (Expression.parse >> derivative "x") "(((x^2 + y^2)_2 + -1.5)^2 + z^2)_2 + -0.5"

    let valueMap = Map.ofList [("x", 4.0); ("y", 5.0); ("z", 6.0)]

    // Online calc: x^2 + y^2 + z^2 - 5^2 -> 2x
    Polynomial.evaluateExpr valueMap d1 |> should equal 8.0

    // Online calc: (x^2 + y^2 + z^2)^(1/2) + -5 -> x / (x^2 + y^2 + z^2)^(1/2)
    Polynomial.evaluateExpr valueMap d2 |> should equal (Polynomial.evaluateExpr valueMap (Expression.parse "x / (x^2 + y^2 + z^2)_2"))

    // Online calc: (((x^2 + y^2)^(1/2) + -1.5)^2 + z^2)^(1/2) + -0.5 -> x*(sqrt(x^2+y^2)-3/2)/(sqrt(x^2+y^2)*sqrt((sqrt(x^2+y^2)-3/2)^2+z^2))
    let expected = 0.39529229591
    (((Polynomial.evaluateExpr valueMap d3) - expected) > -EPSILON && ((Polynomial.evaluateExpr valueMap d3) - expected) < EPSILON) |> should equal true

// Check for a zero value close within the accuracy that sturm sequence uses
let closeToError f =
    if (f > -0.0001 && f < 0.0001) then true else false

[<Fact>]
let ``Sturm sequence finding roots`` () =
    // Results from 1728.org
    // Our sturm implementation only finds the closest positive root to increase performance

    // Expected: 1.487583110336781
    let expected1 = 1.487583110336781
    let r1 = findRoots 10. 0. 0.0001 [-20.; 5.; 17.; -29.; 87.]
    closeToError(r1.[0] - expected1)    |> should equal true
    List.length r1                      |> should equal 1

    // Expected: 5, 3
    let expected2 = 3.
    let r2 = findRoots 10. 0. 0.0001 [3.; 6.; -123.; -126.; 1080.]
    closeToError(r2.[0] - expected2)    |> should equal true
    List.length r2                      |> should equal 1

    // Expected: 3.732050807568877, 1.7320508075688772, 0.2679491924311228
    let expected3 = 0.2679491924311228
    let r3 = findRoots 10. 0. 0.0001 [1.; -4.; -2.; 12.; -3.]
    closeToError(r3.[0] - expected3)    |> should equal true
    List.length r3                      |> should equal 1

    // Expected: 4, 1
    let expected4 = 1.
    let r4 = findRoots 10. 0. 0.0001 [2.; -4.; -22.; 24.]
    closeToError(r4.[0] - expected4)    |> should equal true
    List.length r4                      |> should equal 1

    // Expected: no real positive roots
    let r5 = findRoots 10. 0. 0.0001 [3.; -10.; 14.; 27.]
    List.isEmpty r5                      |> should equal true

    // Expected: no real positive roots
    let r6 = findRoots 10. 0. 0.0001 [1.; 6.; 12.; 8.]
    List.isEmpty r6                      |> should equal true
