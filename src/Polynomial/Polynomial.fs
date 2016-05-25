module Polynomial

open Expression

type Atom = ANum of float | AExponent of string * int | ARoot of string * int| AAdd | ASub | AMul | ADiv

type AtomGroup = Atom list

type SimpleExpr = AtomGroup list

type Poly = P of Map<int, SimpleExpr>

/// <summary>
/// Check if abstract syntax tree contains a root expression.
/// </summary>
/// <param name=e>The abstract syntax tree.</param>
/// <returns>True if tree contains root expression, false otherwise.</returns>
let hasRoot e =
    let rec hr et c =
        match et with
        | FNum x                  -> c ([])
        | FVar x                  -> c ([])
        | FAdd(e1, e2)            -> hr e1 (fun ex1 -> hr e2 (fun ex2 -> c (ex1 @ ex2)))
        | FSub(e1, e2)            -> hr e1 (fun ex1 -> hr e2 (fun ex2 -> c (ex1 @ ex2)))
        | FMult(e1, e2)           -> hr e1 (fun ex1 -> hr e2 (fun ex2 -> c (ex1 @ ex2)))
        | FDiv(e1, e2)            -> hr e1 (fun ex1 -> hr e2 (fun ex2 -> c (ex1 @ ex2)))
        | FExponent(e1, n)        -> hr e1 c
        | FRoot(e1, n) when n > 1 -> c ([1])
        | _                       -> []
    not (List.isEmpty (hr e id))

/// <summary>
/// Isolate the first expression in an atom group that doesn't contain addition
/// or subtraction starting from an operator.
/// </summary>
/// <param name=e>The atom group to find expression on.</param>
/// <returns>
/// The tuple of an atom group containing the elements before and after the
/// first encounter that doesn't satisfy the match.
/// </returns>
let findMul al =
    let rec fm a1 a2 =
        match a2 with
        | ((AAdd | ASub) as op) :: alt -> (a1, a2)
        | op :: alt -> fm (a1 @ [op]) alt
        | [] -> (a1, a2)
    fm [] al

/// <summary>
/// Check is atom group contains any AAdd or ASub atoms.
/// </summary>
/// <param name=>The atom group to check.</param>
/// <returns>
/// The boolean of whether the atom group contains (addition or substraction)
/// or if it doesn't contain it.
/// </returns>
let rec hasSum al =
    match al with
    | (AAdd | ASub) :: alt -> true
    | _ :: alt -> hasSum alt
    | []                   -> false

/// <summary>
/// Split an atom group on the first encounter with AAdd or ASub character.
/// </summary>
/// <remark>The AAdd and ASub atoms are removed in this process.</remark>
/// <param name=e>The atom group to split.</param>
/// <returns>A tuple of an atom group containing the elements before and after
/// the first encountered AAdd or ASub.</returns>
let findGroup al =
    let rec fg al1 al2 =
        match al2 with
        | ((AAdd | ASub) as op) :: alt -> (al1, alt)
        | op :: alt -> fg (al1 @ [op]) alt
        | [] -> (al1, [])
    fg [] al

/// <summary>
/// Flip replace AMul with ADiv and replace ADiv with AMul in an atom group.
/// </summary>
/// <param name=>The atom group to replace atoms.</param>
/// <returns>The atom group with flipped division and multiplication.</returns>
let flipMul al =
    let rec fm al1 c =
        match al1 with
        | AMul :: alt -> fm alt (fun alt1 -> c (ADiv :: alt1))
        | ADiv :: alt -> fm alt (fun alt1 -> c (AMul :: alt1))
        | ah :: alt -> fm alt (fun alt1 -> c (ah :: alt1))
        | [] -> c ([])
    fm al id

/// <summary>
/// Checks if abstact syntax tree contains specific variable.
/// </summary>
/// <param name=e>The abstract syntax tree.</param>
/// <param name=k>The variable to find.</param>
/// <returns>
/// True if variable exists in abstract syntax tree, false otherwise.
/// </returns>
let hasVar e k =
    let rec hv et c =
        match et with
        | FAdd(e1, e2)      -> hv e1 (fun ex1 -> hv e2 (fun ex2 -> c(ex1 @ ex2)))
        | FMult(e1, e2)     -> hv e1 (fun ex1 -> hv e2 (fun ex2 -> c(ex1 @ ex2)))
        | FSub(e1, e2)      -> hv e1 (fun ex1 -> hv e2 (fun ex2 -> c(ex1 @ ex2)))
        | FDiv(e1, e2)      -> hv e1 (fun ex1 -> hv e2 (fun ex2 -> c(ex1 @ ex2)))
        | FExponent(e1, n)  -> hv e1 c
        | FRoot(e1, n)      -> hv e1 c
        | FVar x            -> if x = k then c ([1]) else c ([])
        | FNum x            -> c ([])
    not (List.isEmpty (hv e id))

/// <summary>
/// Return all expressions seperated by an addition or subtraction on top of an
/// abstract syntax tree.
/// </summary>
/// <param name=e>The abstract syntax tree.</param>
/// <returns>The resulting list of expressions.</returns>
let getFirstLevelExpr e =
    let rec gfle et sub c =
        match et with
        | FAdd(e1, e2)          -> if sub then gfle e1 true (fun ex1 ->
                                       gfle e2 true (fun ex2 -> c (ex1 @ ex2)))
                                   else gfle e1 false (fun ex1 ->
                                       gfle e2 false (fun ex2 -> c (ex1 @ ex2)))
        | FSub(e1, e2)          -> if sub then gfle e1 true (fun ex1 ->
                                       gfle e2 false (fun ex2 -> c (ex1 @ ex2)))
                                   else gfle e1 false (fun ex1 ->
                                       gfle e2 true (fun ex2 -> c (ex1 @ ex2)))
        | FMult(_, _) as e1     -> if sub then c ([FMult(FNum -1.0, e1)]) else c ([e1])
        | FDiv(_, _) as e1      -> if sub then c ([FMult(FNum -1.0, e1)]) else c ([e1])
        | FRoot(e1, 1)          -> if sub then c ([FMult(FNum -1.0, e1)]) else c ([e1])
        | FRoot(_, n) as e1     -> if sub then c ([FMult(FNum -1.0, e1)]) else c ([e1])
        | FExponent(_, 0)       -> if sub then c ([FNum -1.0]) else c ([FNum 1.0])
        | FExponent(e1, 1)      -> if sub then c ([FMult(FNum -1.0, e1)]) else c ([e1])
        | FExponent(_, n) as e1 -> if sub then c ([FMult(FNum -1.0, e1)]) else c ([e1])
        | FNum x as e1          -> if sub then c ([FNum (-1.0 * x)]) else c ([e1])
        | FVar _ as e1          -> if sub then c ([FMult(FNum -1.0, e1)]) else c ([e1])
    gfle e false id

/// <summary>
/// Simplify expression list by multiplying identical groups and removing extra
/// exponents.
/// </summary>
/// <param name=e>The list of expressions.</param>
/// <param name=n>Exponent of expression.</param>
/// <returns>The resulting abstract syntax tree.</returns>
let simplifyExprList el n =
    let rec sel et c =
        match et with
        | FAdd(e1, e2) ->
            sel e1 (fun ex1 ->
                sel e2 (fun ex2 -> c (ex1 @ ex2)))
        | FMult(e1, e2) ->
            if e1 = e2 then c ([FMult(e1, e2)])
            elif e1 > e2 then c ([FMult(e1, e2)])
            else c ([FMult(e2, e1)])
    let exprList = List.fold (fun acc elem -> (sel elem id) @ acc) [] el
    let rec consMap etl m =
        match etl with
        | eh :: elt ->
            consMap elt (Map.add eh (if Map.containsKey eh m then m.[eh] + 1 else 1) m)
        | [] -> m

    let map = consMap exprList Map.empty

    let rec simplifyExpr k v =
        match k with
        | FMult(e1, e2) when e1 = e2 ->
            match e1 with
            | FRoot(ee1, nn) when nn = n -> ee1
            | _ when v > 1               -> FMult(k, FNum (float v))
            | _ when v = 1               -> k
        | _ when v > 1               -> FMult(k, FNum (float v))
        | _ when v = 1               -> k

    let addExpr el1 =
        let rec ae ((etl:Expr list), (e2:Expr)) =
            match etl with
            | eh :: elt -> ae (elt, FAdd(e2, eh))
            | [] -> e2
        if List.length el1 > 1 then ae (el1.Tail, el1.Head) else el1.Head
    let simpExpr = Map.fold (fun state key value -> (simplifyExpr key value) :: state) [] map
    addExpr simpExpr

/// <summary>
/// Combine expression lists in respect to exponents.
/// </summary>
/// <param name=e1>The list of expressions on left side.</param>
/// <param name=e2>The list of expressions on right side.</param>
/// <param name=n>The current exponent of the expression.</param>
/// <param name=nth>The nth root in the expression.</param>
/// <param name=nref>The original exponent of the expression.</param>
/// <returns>The list of combined expressions.</returns>
let rec combineExprList e1 e2 n nth nref =
    let rec combExprExpr (et1, et2) c =
        match et2 with
        | eh :: [] -> c (FMult(et1, eh))
        | eh :: elt ->
            combExprExpr (et1, [eh]) (fun ex1 ->
                combExprExpr (et1, elt) (fun ex2 ->
                    c (FAdd(ex1, ex2))
                )
            )
    if n > 2 then combineExprList (List.fold (fun acc elem -> (combExprExpr (elem, e2) id) :: acc) [] e1) e2 (n - 1) nth nref
             else List.fold (fun acc elem -> (combExprExpr (elem, e2) id) :: acc) [] e1

/// <summary>
/// Combine expression containing exponents.
/// </summary>
/// <param name=e>The abstract syntax tree.</param>
/// <param name=n>The exponent of the expression</param>
/// <returns>The resulting abstract syntax tree.</returns>
let combineExpr e n =
    let rootDetail e =
        let rec rd et (nth, count) =
            match et with
            | FRoot(e1, n) :: el -> rd el (n, count + 1)
            | [] -> (nth, count)
            | _ :: el -> rd el (nth, count)
        rd e (0, 0)

    let es = getFirstLevelExpr e
    let nth, count = rootDetail es
    if count > 1 then failwith "Multiple roots on separate branches is not supported"
    elif count = 0 then simplifyExprList (combineExprList es es n nth n) n
    elif n > 2 && List.length es > 1 then failwith "Exponent expression over 2 containing root followed by an other expression is not supported"
    elif (n % nth = 0) then simplifyExprList (combineExprList es es n nth n) n
    else failwith "Root inside exponent that is not multiples of each other, is not supported"

/// <summary>
/// Evaluate the sum of an atom list list and substitute values from given map.
/// </summary>
/// <param name=m>The Map<string, float> with substitude variables in expression.</param>
/// <param name=all>The atom list list.</param>
/// <returns>The resulting float value from the evaluated expression.</returns>
let evaluateAtomGroup m all =
    let eag al1 =
        let rec sum al2 s =
            match al2 with
            | ANum x :: alt -> sum alt (s * x)
            | AExponent (x, n) :: alt ->
                if Map.containsKey x m then sum alt (s * (Map.find x m) ** (float n))
                else failwith "Variable in group not defined"
            | [] -> s
            | _ -> failwith "Invalid atom group"
        if List.isEmpty al1 then 0.0 else sum al1 1.0
    List.fold (fun acc elem -> (eag elem) + acc) 0.0 all

/// <summary>
/// Evaluate the sum of an abstract syntax tree and substitute values from given map.
/// </summary>
/// <param name=m>The Map<string, float> with substitude variables in expression.</param>
/// <param name=e>The abstract syntax trees.</param>
/// <returns>The resulting float value from the evaluated expression.</returns>
let evaluateExpr m e =
    let rec ce et c =
        match et with
        | FMult(e1, e2)     -> ce e1 (fun ex1 -> ce e2 (fun ex2 -> c ((ex1) * (ex2))))
        | FAdd(e1, e2)      -> ce e1 (fun ex1 -> ce e2 (fun ex2 -> c ((ex1) + (ex2))))
        | FSub(e1, e2)      -> ce e1 (fun ex1 -> ce e2 (fun ex2 -> c ((ex1) - (ex2))))
        | FDiv(e1, e2)      -> ce e1 (fun ex1 -> ce e2 (fun ex2 -> c ((ex1) / (ex2))))
        | FExponent(e1, n)  -> ce e1 (fun ex1 -> c ((ex1)**(float n)))
        | FRoot(e1, n)      -> ce e1 (fun ex1 -> c ((ex1)**(1.0 / (float n))))
        | FNum x            -> c (x)
        | FVar x            -> if Map.containsKey x m then c (Map.find x m) else failwith "Variable in tree not defined"
    ce e id

/// <summary>
/// Evaluate atom group containing explicit atom operators and substitute values from given map.
/// </summary>
/// <param name=m>The Map<string, float> with substitude variables in expression.</param>
/// <param name=al>The atom list.</param>
/// <returns>The resulting float value from the evaluated expression.</returns>
let evaluateExplicitAtomGroup m al =
    let get m k = (if Map.containsKey k m then (Map.find k m) else failwith "Variable in tree not defined")
    let rec eeag l s =
        match l with
        | ANum x :: asl -> eeag asl x
        | AExponent(x, n) :: asl -> eeag asl ((get m x)**(float n))
        | AMul :: ANum x :: asl -> eeag asl (s * x)
        | AMul :: AExponent(x, n) :: asl -> eeag asl (s * (get m x)**(float n))
        | AAdd :: ANum x :: asl -> eeag asl (s + x)
        | AAdd :: AExponent(x, n) :: asl -> eeag asl (s + (get m x)**(float n))
        | ASub :: ANum x :: asl -> eeag asl (s - x)
        | ASub :: AExponent(x, n) :: asl -> eeag asl (s - (get m x)**(float n))
        | ADiv :: ANum x :: asl -> eeag asl (s / x)
        | ADiv :: AExponent(x, n) :: asl -> eeag asl (s / (get m x)**(float n))
        | [] -> s
        | _ -> failwith "Invalid atom group"
    eeag al 0.0

/// <summary>
/// Simplify abstract syntax tree by removing subtraction expressions.
/// </summary>
/// <param name=e>The abstract syntax tree.</param>
/// <returns>The resulting abstract syntax tree.</returns>
let removeSub e =
    let negNum et =
        match et with
        | FNum x    -> FNum (x * -1.0)
        | e         -> FMult (FNum -1.0, e)

    let rec rse et c =
        match et with
        | FNum x as e1              -> c (e1)
        | FVar x as e1              -> c (e1)
        | FAdd(e1, e2)              -> rse e1 (fun ex1 -> rse e2 (fun ex2 -> c (FAdd(ex1, ex2))))
        | FSub(e1, e2)              -> rse e1 (fun ex1 -> c (FAdd (ex1, negNum e2)))
        | FMult(e1, e2)             -> rse e1 (fun ex1 -> rse e2 (fun ex2 -> c (FMult(ex1, ex2))))
        | FDiv(e1, e2)              -> rse e1 (fun ex1 -> rse e2 (fun ex2 -> c (FDiv(ex1, ex2))))
        | FExponent(e1, 0)          -> c (FNum 1.0)
        | FExponent(e1, 1)          -> rse e1 c
        | FExponent(e1, n)          -> rse e1 (fun ex1 -> c (FExponent(ex1, n)))
        | FRoot(e1, 0)              -> failwith "0th root not allowed in expression"
        | FRoot(e1, 1)              -> rse e1 c
        | FRoot(e1, n) when n > 1   -> rse e1 (fun ex1 -> c (FRoot(ex1, n)))
    rse e id

/// <summary>
/// Remove root expressions from an abstract syntax tree.
/// </summary>
/// <param name=e>The abstract syntax tree.</param>
/// <returns>The resulting abstract syntax tree.</returns>
let removeRoot e =
    let rec rr (es, rs) =
        match es with
        | FAdd(e1, e2) ->
            match hasRoot e1, hasRoot e2 with
            | true, false -> rr (e1, FAdd(rs, (FMult(FNum -1.0, e2))))
            | false, true -> rr (e2, FAdd(rs, (FMult(FNum -1.0, e1))))
            | _           -> failwith "Multiple roots on separate branches is not supported"
        | FSub(e1, e2) ->
            match hasRoot e1, hasRoot e2 with
            | true, false -> rr (e1, FAdd(rs, e2))
            | false, true -> rr (FMult(FNum -1.0, e2), FAdd(rs, (FMult(FNum -1.0, e1))))
            | _           -> failwith "Multiple roots on separate branches is not supported"
        | FMult(e1, e2) ->
            match hasRoot e1, hasRoot e2 with
            | true, false -> rr(e1, FDiv(rs, e2))
            | false, true -> rr(e2, FDiv(rs, e1))
            | _           -> failwith "Multiple roots on separate branches is not supported"
        | FDiv(e1, e2) ->
            match hasRoot e1, hasRoot e2 with
            | true, false -> rr(e1, FMult(rs, e2))
            | false, true -> rr(e2, FDiv(e1, rs))
            | _           -> failwith "Multiple roots on separate branches is not supported"
        | FRoot(e1, 1) -> if hasRoot e1 then rr (e1, rs) else FAdd(e1, FMult(FNum -1.0, rs)) // Ignore 1st root
        | FRoot(e1, n) ->
            if hasRoot e1 then rr (e1, FExponent(rs, n))
            else FAdd(e1, FMult(FNum -1.0, FExponent(rs, n)))
        | FExponent(e1, 0) -> FAdd(FNum 1.0, (FMult(FNum -1.0, e1)))
        | FExponent(e1, 1) -> rr (e1, rs)
        | FExponent(e1, n) when n < 0 -> rr ((FDiv(FNum 1.0, FExponent(e1, n * -1))), rs)
        | FExponent(e1, 2) -> rr((combineExpr e1 2), rs)
        | FExponent(e1, n) -> failwith "Removing root contained in an exponent higher than 2 is not supported"
    if hasRoot e then rr (e, FNum 0.0) else e

/// <summary>
/// Given an expression, substitue all occurences of a variable with a different expression.
/// </summary>
/// <param name=e>The expression to substitute in.</param>
/// <param name=x>The variable to subtitute in the expression.</param>
/// <param name=ex>The expression to subtitute the variable with.</param>
/// <returns>The expression with all occurences of x substituted with ex.</returns>
let subst e (x, ex) =
    let rec su et c =
        match et with
        | FNum v            -> c (FNum v)
        | FVar v            -> if v = x then c (ex) else c (FVar v)
        | FAdd(e1, e2)      -> su e1 (fun ex1 -> su e2 (fun ex2 -> c (FAdd(ex1, ex2))))
        | FSub(e1, e2)      -> su e1 (fun ex1 -> su e2 (fun ex2 -> c (FSub(ex1, ex2))))
        | FMult(e1, e2)     -> su e1 (fun ex1 -> su e2 (fun ex2 -> c (FMult(ex1, ex2))))
        | FDiv(e1, e2)      -> su e1 (fun ex1 -> su e2 (fun ex2 -> c (FDiv(ex1, ex2))))
        | FExponent(e1, i)  -> su e1 (fun ex1 -> c (FExponent(ex1, i)))
        | FRoot(e1, i)      -> su e1 (fun ex1 -> c (FRoot(ex1, i)))
    su e id

/// <summary>
/// Combine two segregated atom groups.
/// </summary>
/// <param name=e1>First segregated atom group.</param>
/// <param name=e2>Second segregated atom group.</param>
/// <param name=com>The atom to combine the lists with.</param>
/// <returns>The combined right and left atom group.</returns>
let combine e1 e2 com =
    let rec comb et1 et2 c =
        match et1 with
        | ((ANum _ | AExponent _) as n1) :: ((AMul | ADiv) as op) :: ((ANum _ | AExponent _) as n2) :: al ->
            let alR, alL = findMul al
            comb alL et2 (fun al1 -> c ((n1 :: op :: n2 :: alR @ (com :: et2)) @ al1))
        | ((ANum _ | AExponent _) as n1) :: alt  -> comb alt et2 (fun al1 -> c (n1 :: com :: et2 @ al1))
        | AAdd as op :: alt                      -> comb alt et2 (fun al1 -> c (op :: al1))
        | [] -> c ([])
        | _ -> failwith "Invalid expression in for combining"
    comb e1 e2 id

/// <summary>
/// Segregate left side of expression and combine with right side.
/// </summary>
/// <param name=e1>The right side expression to combine on.</param>
/// <param name=e2>The left side to segregate.</param>
/// <param name=com>The atom to combine the lists with.</param>
/// <returns>The combined right and left atom group.</returns>
let segregateLeft e1 e2 com =
    let rec segLeft et1 et2 c =
        match et2 with
        | ((ANum _ | AExponent _) as n1) :: ((AAdd) as op) :: ((ANum _ | AExponent _) as n2) :: []                              ->
            c ((combine et1 [n1] com) @ [op] @ (combine et1 [n2] com))
        | ((ANum _ | AExponent _) as n1) :: ((AAdd) as op) :: ((ANum _ | AExponent _) as n2) :: ((AMul | ADiv ) as next) :: alt ->
            segLeft et1 (n2 :: next :: alt) (fun al2 -> c ((combine et1 ([n1]) com) @ [op] @ (al2)))
        | ((ANum _ | AExponent _) as n1) :: ((AAdd) as op) :: ((ANum _ | AExponent _) as n2) :: ((AAdd | ASub) as next) :: alt  ->
            segLeft et1 alt (fun al3 -> c ((combine et1 [n1] com) @ [op] @ (combine et1 [n2] com) @ [next] @ (al3)))
        | ((ANum _ | AExponent _) as n1) :: ((AMul | ADiv) as op) :: ((ANum _ | AExponent _) as n2) :: alt                      ->
            let alR, alL = findMul alt
            let head = if alL.IsEmpty then [] else [alL.Head]
            let tail = if alL.IsEmpty then [] else alL.Tail
            segLeft et1 tail (fun al2 -> c ((combine et1 (n1 :: op :: n2 :: alR) com) @ head @ al2))
        | ((ANum _ | AExponent _) as n1) :: [] -> c (combine et1 [n1] com)
        | [] -> c ([])
        | _  -> failwith "Invalid expression in left side of multiplication"
    segLeft e1 e2 id

/// <summary>
/// Segregate right side of expression and combine with left side.
/// </summary>
/// <param name=e1>The right side to segregate.</param>
/// <param name=e2>The left side.</param>
/// <param name=com>The atom to combine the lists with.</param>
/// <returns>The combined right and left atom group.</returns>
let segregateRight e1 e2 com =
    let rec segRight et1 et2 c =
        match et1 with
        | ((ANum _ | AExponent _) as n1) :: ((AAdd) as op) :: ((ANum _ | AExponent _) as n2) :: []                             ->
            c (segregateLeft (n1 :: op :: [n2]) et2 com)
        | ((ANum _ | AExponent _) as n1) :: ((AAdd) as op) :: ((ANum _ | AExponent _) as n2) :: ((AMul | ADiv) as next) :: alt ->
            segRight (n2 :: next :: alt) et2 (fun al2 -> c ((segregateLeft ([n1]) et2 com) @ [op] @ al2))
        | ((ANum _ | AExponent _) as n1) :: ((AAdd) as op) :: ((ANum _ | AExponent _) as n2) :: ((AAdd | ASub) as next) :: alt ->
            segRight alt et2 (fun al2 -> c ((segregateLeft (n1 :: op :: [n2]) et2 com) @ [next] @ (al2)))
        | ((ANum _ | AExponent _) as n1) :: ((AMul | ADiv) as op) :: ((ANum _ | AExponent _) as n2) :: alt                     ->
            let alR, alL = findMul alt
            let head = if alL.IsEmpty then [] else [alL.Head]
            let tail = if alL.IsEmpty then [] else alL.Tail
            segRight tail et2 (fun al2 -> c ((segregateLeft (n1 :: op :: n2 :: alR) et2 com) @ head @ al2))
        | ((ANum _ | AExponent _) as n1) :: [] -> c (segregateLeft ([n1]) et2 com)
        | [] -> c ([])
        | _  -> failwith "Invalid expression in right side of multiplication"
    segRight e1 e2 id

/// <summary>
/// Combine two atom groups with division and return a single atom group.
/// </summary>
/// <param name=e1>The atom list as numerator.</param>
/// <param name=e2>The atom list as denominator.</param>
/// <returns>The simplified atom group.</returns>
let combineDiv e1 e2 =
    if not (hasSum e2)
    then segregateRight e1 (flipMul e2) ADiv
    else
        // throws exception if division has variable and can't be simplified
        let s = evaluateExplicitAtomGroup Map.empty e2
        segregateRight e1 ([ANum s]) ADiv

/// <summary>
/// Simplify an expression to a list of atom groups that are implicitly added together, where each atom group consists
/// of atoms that are implicitly multiplied together.
/// </summary>
/// <param name=e>The expression to simplify.</param>
/// <returns>The simplified expression.</returns>
let simplify e =
    let rec sim et c =
        match et with
        | FNum x                      -> c ([ANum x])
        | FVar x                      -> c ([AExponent(x, 1)])
        | FExponent(_, 0)             -> c ([ANum 1.0])
        | FExponent(e1, 1)            -> sim e1 c
        | FExponent(e1, n) when n < 0 -> sim (FDiv(FNum 1.0, FExponent(e1, n * -1))) c
        | FExponent(e1, n)            -> sim (FMult(e1, FExponent(e1, n - 1))) c
        | FAdd(e1, e2)                -> sim e1 (fun al1 -> sim e2 (fun al2 -> c (al1 @ (AAdd :: al2))))
        | FSub(e1, e2)                -> failwith "Subtraction shouldn't be present"
        | FMult(e1, e2)               -> sim e1 (fun al1 -> sim e2 (fun al2 -> c (segregateRight al1 al2 AMul)))
        | FDiv(e1, e2)                -> sim e1 (fun al1 -> sim e2 (fun al2 -> c (combineDiv al1 al2)))
        | FRoot(e1, 0)                -> failwith "0th root is not allowed in expressions"
        | FRoot(e1, 1)                -> sim e1 c
        | FRoot(e1, n)                -> failwith "Roots shouldn't be present"
    sim e id

/// <summary>
/// Separate an Atom group into multiple groups on the AAdd atom.
/// </summary>
/// <param name=e>The atom list to separate.</param>
/// <returns>The simplified atom group.</returns>
let separateAtomGroup al =
    let rec sag al1 al2 =
        if List.isEmpty al2 then al1
        else
            let alR, alL = findGroup al2
            sag (al1 @ [alR]) alL
    sag [] al

/// <summary>
/// Simplify an atom group by summing constants and combining exponents.
/// </summary>
/// <param name=ag>The atom group to simplify.</param>
/// <returns>The simplified atom group.</returns>
let simplifyAtomGroup ag =
    let rec sag al s m =
        match al with
        | AMul :: ANum x :: alt when x = 0.  -> (0.0, Map.empty)
        | AMul :: ANum x :: alt              -> sag alt (s * x) m
        | ADiv :: ANum x :: alt              -> if not(x = 0.) then sag alt (s / x) m else failwith "Can't divide by 0"
        | ANum x :: alt when x = 0.          -> (0.0, Map.empty)
        | ANum x :: alt                      -> sag alt (s * x) m
        | AMul :: AExponent (x, n) :: alt    -> sag alt (s) (Map.add x (if Map.containsKey x m then m.[x] + n else n) m)
        | ADiv :: AExponent (x, n) :: alt    -> sag alt (s) (Map.add x (if Map.containsKey x m then m.[x] - n else -1 * n) m)
        | AExponent (x, n) :: alt            -> sag alt (s) (Map.add x (if Map.containsKey x m then m.[x] + n else n) m)
        | [] -> (s, m)
        | _ -> failwith "Invalid atom group can't be simplified"
    let (sum, map) = sag ag 1.0 Map.empty

    let u m = Map.fold (fun a x n -> a @ [AExponent(x, n)]) [] m

    match (sum, map) with
    | (0.0, m) -> [ANum 0.0]
    | (1.0, m) -> u m
    | (s,   m) -> ANum s :: u m

/// <summary>
/// Further simplify a simple expression by summing atom groups consiting only
/// of a constant and combining atom groups that are equal.
/// </summary>
/// <param name=ags>The simple expression to simplify.</param>
/// <returns>The simplified simple expression.</returns>
let simplifySimpleExpr ags =
    let ags' = List.map simplifyAtomGroup ags

    let f (s, m) = function
        | [ANum c] -> (s + c, m)
        | g        -> (s, Map.add g (if Map.containsKey g m then m.[g] + 1 else 1) m)

    let u m = Map.fold (fun a g n -> if ((n = 1 && not (List.isEmpty g))) then [g] @ a else [ANum (float n) :: g] @ a) [] m

    match List.fold f (0.0, Map.empty) ags' with
    | (0.0, m) -> u m
    | (s,   m) -> [ANum s] :: u m

/// <summary>
/// Split an atom group with respect to a variable.
/// </summary>
/// <param name=v>The variable to split on.</param>
/// <param name=m>The map to split the atom group into.</param>
/// <param name=ag>The atom group to split.</param>
/// <returns>A map containing the split atom group.</returns>
let splitAtomGroup v m = function
    | ag ->
        let isV = function AExponent(v', _) -> v = v' | _ -> false

        let addMap d ag m = Map.add d (if Map.containsKey d m then [ag] @ m.[d] else [ag]) m

        match List.tryFind isV ag with
        | Some (AExponent(_, d)) -> addMap d (List.filter (not << isV) ag) m
        | _                      -> addMap 0 ag m
    | [] -> m

/// <summary>
/// Convert an expression to a simplified simple expression.
/// </summary>
/// <param name=e>The expression to convert.</param>
/// <returns>The resulting simple expression.</returns>
let exprToSimpleExpr e = (removeSub >> removeRoot >> simplify >> separateAtomGroup >> simplifySimpleExpr) e

/// <summary>
/// Convert a simple expression to a polynomial with respect to a variable.
/// </summary>
/// <param name=ags>The simple expression to convert.</param>
/// <param name=v>The variable to isolate.</param>
/// <returns>The resulting polynomial.</returns>
let simpleExprToPoly ags v = P(List.fold (splitAtomGroup v) Map.empty ags)

/// <summary>
/// Convert an expression to a polynomial with respect to a variable.
/// </summary>
/// <param name=v>The variable to isolate.</param>
/// <param name=e>The expression to convert.</param>
/// <returns>The resulting polynomial.</returns>
let parse v e = (exprToSimpleExpr >> simpleExprToPoly) e v

/// <summary>
/// Find the derivative of an abstract syntax tree with respect to a variable.
/// </summary>
/// <see cref="https://www.mathsisfun.com/calculus/derivatives-rules.html">Derivative Rules</see>
/// <see cref="https://proofwiki.org/wiki/Derivative_of_Nth_Root">Derivative of Nth Root</see>
/// <param name=k>The variable to find the derivative of.</param>
/// <param name=e>The abstract syntax tree.</param>
/// <returns>The resulting abstract syntax tree.</returns>
let derivative k e =
    let rec de et dx c =
        match et with
        | FAdd(e1, e2)                  -> de e1 dx (fun ex1 -> de e2 dx (fun ex2 ->
            c (FAdd((if hasVar e1 k then ex1 else FNum 0.0), (if hasVar e2 k then ex2 else FNum 0.0)))))
        | FMult(e1, e2)                 ->
            match hasVar e1 k, hasVar e2 k with
            | true, false  -> de e1 dx (fun ex1 -> c (FMult(ex1, e2)))
            | false, true  -> de e2 dx (fun ex2 -> c (FMult(ex2, e1)))
            | true, true   -> de e1 dx (fun ex1 -> de e2 dx (fun ex2 -> c (FAdd(FMult(ex1, e2), FMult(e1, ex2)))))
            | false, false -> c (FNum 0.0)
        | FSub(e1, e2)                  -> de e1 dx (fun ex1 -> de e2 dx (fun ex2 ->
            c (FSub((if hasVar e1 k then ex1 else FNum 0.0), (if hasVar e2 k then ex2 else FNum 0.0)))))
        | FDiv(e1, e2)                  -> de e1 true (fun ex1 -> de e2 true (fun ex2 ->
            c (FDiv(FSub(FMult(ex1, e2), FMult(ex2, e1)), FExponent(e2, 2)))))
        | FExponent(e1, 0)              -> c (FNum 0.0)
        | FExponent(e1, 1)              -> de e1 dx c
        | FExponent(e1, n) when n < 0   -> de (FDiv(FNum 1.0, FExponent(e1, n * -1))) dx c
        | FExponent(e1, n)              -> if hasVar e1 k then de e1 true (fun ex1 ->
            c (FMult(FMult(FNum (float n), FExponent(e1, n - 1)), ex1))) else c (FNum 0.0)
        | FRoot(e1, 0)                  -> failwith "Derivative of 0th root not allowed"
        | FRoot(e1, n) when n < 0       -> failwith "Derivative of negative root is not supported"
        | FRoot(e1, 1)                  -> de e1 dx c
        | FRoot(e1, n) when n > 0       -> de e1 true (fun ex1 ->
            c (FMult(FDiv(FNum 1.0, FMult(FNum (float n), FExponent(FRoot(e1, n), n - 1))), ex1)))
        | FVar x                        -> if dx && x = k then c (FNum 1.0) elif x = k then c (FVar x) else c (FNum 0.0)
        | FNum x                        -> if dx then c (FNum 0.0) else c (FNum x)
    de e true id

/// <summary>
/// Perform polynomial long divison on polynomial and the derivative of the polynomial.
/// </summary>
/// <remark>
/// Largely inspired by Ocaml code see ref.
/// </remark>
/// <see cref="https://rosettacode.org/wiki/Polynomial_long_division">Polynomial long division</see>
/// <param name=f>The list of first polynomials float values.</param>
/// <param name=g>The list of derivative of first polynomial float values.</param>
/// <returns>The tuple pair of the quotient and remainder.</returns>
let longDivision f g =
    // Shifts a list by n, adding 0. floats to the back of the list
    let rec shift n l = if n <= 0 then l else shift (n - 1) (l @ [0.0])

    // Pads a list by n, adding 0 floats to the front of the list
    let rec pad n l = if n <= 0 then l else pad (n - 1) ( 0.0 :: l)

    // Norm removes zero values from a list of floats, normalizing it
    let rec norm l =
        match l with
        | 0.0 :: tl -> norm tl
        | _ -> l

    // Finds the degree of of l, after normalizing it
    let deg l = (List.length (norm l)) - 1

    // Acts a lot like the map2 funciton, except it pads the input list,
    // making sure they're the same length, before applying op
    let zip op p q =
        let d = (List.length p) - (List.length q)
        List.map2 op (pad (-d) p) (pad d q)

    let rec pdiv f s q =
        let ddif = (deg f) - (deg s) //Takes the difference in degrees between the two polynomials
        if ddif < 0  then (q, f) else
            let k = (List.head f) / (List.head s)
            let ks = List.map ((*) k) (shift ddif s)
            let q' = zip (+) q (shift ddif [k])
            let f' = norm (List.tail (zip (-) f ks))
            pdiv f' s q'
    pdiv (norm f) (norm g) []

/// <summary>
/// Find the number of roots in an interval of a polynomial.
/// </summary>
/// <param name=poly>The list of first polynomials float values.</param>
/// <param name=derivative>The list of derivative of first polynomial float values.</param>
/// <param name=maxInterval>The max root value which can be found. Can be infinity.</param>
/// <param name=minInterval>The min root value which can be found. Can be negative infinity.</param>
/// <returns>Int representing the number of roots.</returns>
let numberOfRoots poly derivative maxInterval minInterval =
    //Function for creating a sturmSequence, given a list of the format [polyList poly; polyList derivative]
    let rec sturmSequence pl =
        let length = List.length pl
        let remainder = snd (longDivision (List.item (length-2) pl) (List.item (length-1) pl))
        let remainder = List.map (fun x -> x*(-1.0)) remainder
        if List.length remainder <= 1
        then pl @ [remainder]
        else (pl @ [remainder]) |> sturmSequence

    //Function for counting the number of sign changes in the sturm sequence, given a constant c for the univariate polynomial.
    let countSignChange c ss =
        let summarize fl c =
            let fb = List.foldBack (fun elem (acc,n) -> (elem * c ** n + acc, n+1.)) fl (0.,0.)
            fst fb
        let rec recCSC c ss n pos =
            match ss with
            | fl :: ssl -> if (summarize fl c) > 0. = pos then recCSC c ssl (n) pos else recCSC c ssl (n+1) (not pos)
            | [] -> n
        recCSC c ss 0 (summarize (List.head ss) c > 0.)

    let pl = [poly;derivative]
    let ss = sturmSequence pl
    let scMaxInterval = countSignChange maxInterval ss
    let scMinInterval = countSignChange minInterval ss
    scMinInterval - scMaxInterval

/// <summary>
/// Find and estimation of each root in the interval of a polynomial.
/// </summary>
/// <param name=maxInterval>The max root value which can be found. Can NOT be infinite.</param>
/// <param name=minInterval>The min root value which can be found. Can NOT be infinite.</param>
/// <param name=error>The error of the root estimate.</param>
/// <param name=poly>The list of first polynomials float values.</param>
/// <returns>A list of floats, representing the distance to each root.</returns>
let findRoots maxInterval minInterval error poly =
    // Find derivative of simple float list with implicit exponents
    let quickDerivative (l:float list) =
        let exponents = [(float (l.Length-1))..(-1.)..0.]
        List.foldBack2 (fun n v acc -> if n = 0. then acc else n * v :: acc) exponents l []
    let derivative = quickDerivative poly
    let rec fr p d maxI minI err =
        let diff = abs(maxI - minI)
        let newMax = maxI-diff/2.
        let newMin = minI+diff/2.
        let closeRoots = numberOfRoots p d newMax minI
        let closeDiff = abs(newMax - minI)
        match closeRoots with
        | 0                    ->
            let farRoots = numberOfRoots p d maxI newMin
            let farDiff = abs(maxI - newMin)
            match farRoots with
            | 0                   -> []
            | 1                   -> if farDiff < err then [minI + farDiff/2.] else fr poly derivative maxI newMin err
            | n when error > diff -> [minI + (farDiff/2.)]
            | _                   -> fr p d maxI newMin err
        | 1                   -> if closeDiff < err then [minI + closeDiff/2.] else fr poly derivative newMax minI err
        | n when error > diff -> [minI + (diff/2.)]
        | _                   -> fr p d newMax minI err
    fr poly derivative maxInterval minInterval error

