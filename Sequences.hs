module Sequences where 

import Language

p = [
    --(Statement "rIsRelation" (Atom "relation" [Var "R"]) Assumed),
    --(Statement "xIsElement" (Atom "element" [Var "X"]) Assumed),
    --(Statement "yIsElement" (Atom "element" [Var "Y"]) Assumed),
    --(Statement "zIsElement" (Atom "element" [Var "Z"]) Assumed),
    (Statement "defSymmetric" ((Atom "symmetric" [Var "r"] `Iff` Forall "X" (Forall "Y" (Atom "element" [Var "X"] `And` Atom "element" [Var "Y"] `Impl`  Atom "relapp" [Var "r", Var "X", Var "Y"] `Impl` Atom "relapp" [Var "r", Var "Y", Var "X"])))) Assumed),
    (Statement "defBound" (Atom "bound" [Var "r"] `Iff` Forall "X" (Atom "element" [Var "X"] `Impl` (Exists "Y" (Atom "element" [Var "Y"] `And` Atom "relapp" [Var "r", Var "X", Var "Y"])))) Assumed),
    (Statement "defTransitive" ((Atom "transitive" [Var "r"] `Iff` Forall "X" (Forall "Y" (Forall "Z" (Atom "element" [Var "X"] `And` Atom "element" [Var "Y"] `And` Atom "element" [Var "Y"] `Impl` (Atom "relapp" [Var "r", Var "X", Var "Y"] `And` Atom "relapp" [Var "r", Var "Y", Var "Z"]) `Impl` Atom "relapp" [Var "r", Var "X", Var "Z"]))))) Assumed),
    (Statement "defReflexive" ((Atom "reflexive" [Var "r"] `Iff` Forall "X" (Atom "element" [Var "X"]  `Impl` Atom "relapp" [Var "r", Var "X", Var "X"]))) Assumed),
    (Statement "lemma" (((Atom "transitive" [Var "r"]) `And` (Atom "symmetric" [Var "r"]) `And` (Atom "bound" [Var "r"])) `Impl` (Atom "reflexive" [Var "r"])) 
        (BySequence [
          (Statement "lemmaAntecedent" ((Atom "transitive" [Var "r"]) `And` (Atom "symmetric" [Var "r"]) `And` (Atom "bound" [Var "r"])) Assumed), 
          (Statement "assumeNotEmpty" (Atom "element" [Var "x"]) Assumed),
          (Statement "fixY" (Atom "element" [Var "y"] `And` Atom "relapp" [Var "r", Var "x", Var "y"]) (BySequence [ 
            (Statement "applyBound" (Exists "Y" (Atom "element" [Var "Y"] `And` Atom "relapp" [Var "r", Var "x", Var "Y"])) ByContext)
          ])),
          (Statement "applySymmetry" (Atom "relapp" [Var "r", Var "y", Var "x"]) ByContext),
          (Statement "applyTransitivity" (Atom "relapp" [Var "r", Var "x", Var "x"]) ByContext),
          (Statement "lemmaConsequent" (Atom "reflexive" [Var "r"]) ByContext)
        ])
    )
    ]

p2 = [
      (Statement "defRational" ((Atom "rational" [Var "X"]) `Iff` (Exists "A" (Exists "B" ((Atom "relprime" [Var "A", Var "B"]) `And` (Atom "equals" [Var "X", Cons "frac" [Var "A", Var "B"]]))))) Assumed),
      (Statement "defIrrational" ((Atom "irrational" [Var "X"]) `Iff` (Not (Atom "rational" [Var "X"]))) Assumed),
      (Statement "defDiv" ((Atom "div" [Var "2", Var "Y"]) `Iff` (Exists "X" (Atom "equals" [Cons "times" [Var "X", Var "2"], Var "Y"]))) Assumed),
      --(Statement "divPowClosure" ((Atom "div" [Var "X", Var "Y"]) `Impl` (Atom "div" [Var "X", Cons "pow" [Var "Y"]])) Assumed),
      (Statement "sqrtPow" (Atom "equals" [Var "X", Cons "pow" [Cons "sqrt" [Var "X"]]]) Assumed),
      (Statement "equalSymmetric" ((Atom "equals" [Var "X", Var "Y"]) `Impl` (Atom "equals" [Var "Y", Var "X"])) Assumed),
      (Statement "equalTransitive" (((Atom "equals" [Var "X", Var "Y"]) `And` (Atom "equals" [Var "Y", Var "Z"])) `Impl` (Atom "equals" [Var "X", Var "Z"])) Assumed),
      (Statement "equalReflexive" (Atom "equals" [Var "X", Var "X"]) Assumed),
      (Statement "timesComm" (Atom "equals" [Cons "times" [Var "X", Var "Y"], Cons "times" [Var "Y", Var "X"]]) Assumed),
      (Statement "powIntro" ((Atom "equals" [Var "X", Var "Y"]) `Impl` (Atom "equals" [Cons "pow" [Var "X"], Cons "pow" [Var "Y"]])) Assumed),
      --(Statement "powInFrac" (Atom "equals" [Cons "pow" [Cons "frac" [Var "X", Var "Y"]], Cons "frac" [Cons "pow" [Var "X"], Cons "pow" [Var "Y"]]]) Assumed),
      (Statement "fracSymm" ((Atom "equals" [Var "X", Cons "frac" [Var "Y", Var "Z"]]) `Impl` (Atom "equals" [Cons "times" [Var "X", Var "Z"], Var "Y"])) Assumed),
      (Statement "lemma" (Atom "irrational" [Cons "sqrt" [Var "2"]]) 
        (BySequence [
            (Statement "negLemma" (Atom "rational" [Cons "sqrt" [Var "2"]]) Assumed),
            (Statement "existsPrime" ((((Atom "relprime" [Var "A", Var "B"]) `And` (Atom "equals" [Cons "sqrt" [Var "2"], Cons "frac" [Var "A", Var "B"]])))) ByContext),
            (Statement "transform" (Atom "equals" [Var "2", Cons "frac" [Cons "pow" [Var "A"], Cons "pow" [Var "B"]]]) ByContext),
            (Statement "transform2" (Atom "equals" [Cons "times" [Var "2", Cons "pow" [Var "B"]], Cons "pow" [Var "A"]]) ByContext),
            (Statement "transform2" (Atom "div" [Var "2", Var "A"]) ByContext)
            --(Statement "bot" (Atom "test" [Var "X"]) ByContext)

        ]))
     ]


-- A = ( A \ B ) ∪ ( A ∩ B )
pCases = [
  (Statement "setsEqualProof" ((Atom "equals" [Var "A", Var "B"]) `Iff` (((Atom "elem" [Var "X", Var "A"]) `Impl` (Atom "elem" [Var "X", Var "B"])) `And` ((Atom "elem" [Var "X", Var "B"]) `Impl` (Atom "elem" [Var "X", Var "A"])))) Assumed),
  (Statement "lemma" (Atom "equals" [Var "A", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]]) 
    (BySplit [
      (Statement "leftImplRight" ((Atom "elem" [Var "X", Var "A"]) `Impl` (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]])) 
          (BySequence [
              (Statement "takeXInLeft" (Atom "elem" [Var "$fixedX", Var "A"]) Assumed),
              (Statement "xInRight" (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]])
                (BySplit [
                  (Statement "xInB" ((Atom "elem" [Var "X", Var "B"]) `Impl` (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]])) 
                     (BySequence [
                        (Statement "fixedXinB" (Atom "elem" [Var "X", Var "B"]) Assumed),
                        (Statement "xInAintsecB" (Atom "elem" [Var "X", Cons "intsec" [Var "A", Var "B"]]) ByContext),
                        (Statement "xInRight" (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]]) ByContext)
                      ])
                  ),
                  (Statement "xNotInB" (Not ((Atom "elem" [Var "X", Var "B"])) `Impl` (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]])) 
                     (BySequence [
                        (Statement "fixedXinB" (Not (Atom "elem" [Var "X", Var "B"])) Assumed),
                        (Statement "xInAdiffB" (Atom "elem" [Var "X", Cons "diff" [Var "A", Var "B"]]) ByContext),
                        (Statement "xInRight" (Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]]) ByContext)
                     ])
                  )
                ])
              )
          ])
        ),
      (Statement "rightImplLeft" ((Atom "elem" [Var "X", Cons "union" [Cons "diff" [Var "A", Var "B"], Cons "intsec" [Var "A", Var "B"]]]) `Impl` (Atom "elem" [Var "X", Var "A"])) Assumed)
    ])
  )
 ]

-- n! ≤ n for any integer n ≥ 1.
--IA For n=1 (1.3) is true, since 1! = 11
--IH Suppose (1.3) is true for some n = k ≥ 1, that is k! ≤ k
--IS Prove that (1.3) is true for n = k + 1, that is (k + 1)! ≤ (k + 1)^(k+1)
--(k + 1)! = k! · (k + 1) ≤ k^k (k+1) < (k + 1)^k * (k + 1) = (k + 1)^(k+1)

pInduction = [
    (Statement "lesseqWellfounded" (Atom "welldefined" [Var "lesseq"]) Assumed),
    --(Statement "inductionProof" ((Atom "welldefined" [Var "rel"]) `And` (Atom "rel" []) `Impl` Bot) Assumed),
    (Statement "lesseq" ((Atom "lesseq" [Var "X", Var "Y"]) `Iff` (Atom "equals" [Var "X", Var "Y"] `Or` Atom "less" [Var "X", Var "Y"]) ) Assumed),
    (Statement "facBase" (Atom "equals" [Cons "fac" [Var "1"], Var "1"]) Assumed),
    --(Statement "facRec" (Atom "equals" [Cons "fac" [Var "n"], Var "1"]) Assumed),
    (Statement "lemma" (Atom "lesseq" [Cons "fac" [Var "n"], Var "n"]) 
      (BySplit [
          (Statement "inductionStart" ((Atom "lesseq" [Cons "fac" [Var "1"], Var "1"])) ByContext),
          (Statement "inductionStep" ((Atom "lesseq" [Cons "fac" [Cons "plus" [Var "n", Var "1"]], Cons "plus" [Var "n", Var "1"]])) 
            (BySequence [
              (Statement "inductionHypothesis" (Atom "lesseq" [Cons "fac" [Var "n"], Var "n"]) Assumed),
              -- ...
              (Statement "inductionformula" (Atom "lesseq" [Cons "fac" [Cons "plus" [Var "n", Var "1"]], Cons "plus" [Var "n", Var "1"]]) ByContext)
            ]) )
      ])
    )
  ]