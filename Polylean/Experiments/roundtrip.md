Passing to indexed tree and back for `x + y + x - y` left the following goal.

```lean
AddTree.lean:203:48
Tactic state
α: Type u
inst✝²: AddCommGroup α
inst✝¹: Repr α
inst✝: DecidableEq α
xy: α
⊢ egIndMap x y = x + y + x - y
Messages (1)
AddTree.lean:203:45
unsolved goals
α : Type u
inst✝² : AddCommGroup α
inst✝¹ : Repr α
inst✝ : DecidableEq α
x y : α
⊢ Array.get
            (match
                Array.getIdx?
                  (match
                      Array.getIdx?
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd
                        x with
                    | some i =>
                      (AddTree.leaf i,
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd)
                    | none =>
                      (AddTree.leaf
                        (Array.size
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd),
                        Array.push
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x)).snd
                  y with
              | some i =>
                (AddTree.leaf i,
                  (match
                      Array.getIdx?
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd
                        x with
                    | some i =>
                      (AddTree.leaf i,
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd)
                    | none =>
                      (AddTree.leaf
                        (Array.size
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd),
                        Array.push
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x)).snd)
              | none =>
                (AddTree.leaf
                  (Array.size
                    (match
                        Array.getIdx?
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x with
                      | some i =>
                        (AddTree.leaf i,
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd)
                      | none =>
                        (AddTree.leaf
                          (Array.size
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd),
                          Array.push
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd
                            x)).snd),
                  Array.push
                    (match
                        Array.getIdx?
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x with
                      | some i =>
                        (AddTree.leaf i,
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd)
                      | none =>
                        (AddTree.leaf
                          (Array.size
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd),
                          Array.push
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd
                            x)).snd
                    y)).snd
            (Fin.ofNat' (Array.size #[]) (_ : Array.size (egInd x y).snd.val > 0)) +
          IndexAddTree.foldMap
            (match Array.getIdx? (Array.push #[] x) y with
              | some i => (AddTree.leaf i, Array.push #[] x)
              | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).fst
            (match
                Array.getIdx?
                  (match
                      Array.getIdx?
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd
                        x with
                    | some i =>
                      (AddTree.leaf i,
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd)
                    | none =>
                      (AddTree.leaf
                        (Array.size
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd),
                        Array.push
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x)).snd
                  y with
              | some i =>
                (AddTree.leaf i,
                  (match
                      Array.getIdx?
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd
                        x with
                    | some i =>
                      (AddTree.leaf i,
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd)
                    | none =>
                      (AddTree.leaf
                        (Array.size
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd),
                        Array.push
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x)).snd)
              | none =>
                (AddTree.leaf
                  (Array.size
                    (match
                        Array.getIdx?
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x with
                      | some i =>
                        (AddTree.leaf i,
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd)
                      | none =>
                        (AddTree.leaf
                          (Array.size
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd),
                          Array.push
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd
                            x)).snd),
                  Array.push
                    (match
                        Array.getIdx?
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x with
                      | some i =>
                        (AddTree.leaf i,
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd)
                      | none =>
                        (AddTree.leaf
                          (Array.size
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd),
                          Array.push
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd
                            x)).snd
                    y)).snd
            (_ :
              Array.size
                  (match
                      Array.getIdx?
                        (match
                            Array.getIdx?
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd
                              x with
                          | some i =>
                            (AddTree.leaf i,
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd),
                              Array.push
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd
                                x)).snd
                        y with
                    | some i =>
                      (AddTree.leaf i,
                        (match
                            Array.getIdx?
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd
                              x with
                          | some i =>
                            (AddTree.leaf i,
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd),
                              Array.push
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd
                                x)).snd)
                    | none =>
                      (AddTree.leaf
                        (Array.size
                          (match
                              Array.getIdx?
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd
                                x with
                            | some i =>
                              (AddTree.leaf i,
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match
                                      Array.getIdx?
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y with
                                    | some i =>
                                      (AddTree.leaf i,
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                    | none =>
                                      (AddTree.leaf
                                        (Array.size
                                          (match Array.getIdx? #[] x with
                                            | some i => (AddTree.leaf i, #[])
                                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                        Array.push
                                          (match Array.getIdx? #[] x with
                                            | some i => (AddTree.leaf i, #[])
                                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                          y)).snd),
                                Array.push
                                  (match
                                      Array.getIdx?
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y with
                                    | some i =>
                                      (AddTree.leaf i,
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                    | none =>
                                      (AddTree.leaf
                                        (Array.size
                                          (match Array.getIdx? #[] x with
                                            | some i => (AddTree.leaf i, #[])
                                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                        Array.push
                                          (match Array.getIdx? #[] x with
                                            | some i => (AddTree.leaf i, #[])
                                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                          y)).snd
                                  x)).snd),
                        Array.push
                          (match
                              Array.getIdx?
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd
                                x with
                            | some i =>
                              (AddTree.leaf i,
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match
                                      Array.getIdx?
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y with
                                    | some i =>
                                      (AddTree.leaf i,
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                    | none =>
                                      (AddTree.leaf
                                        (Array.size
                                          (match Array.getIdx? #[] x with
                                            | some i => (AddTree.leaf i, #[])
                                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                        Array.push
                                          (match Array.getIdx? #[] x with
                                            | some i => (AddTree.leaf i, #[])
                                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                          y)).snd),
                                Array.push
                                  (match
                                      Array.getIdx?
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y with
                                    | some i =>
                                      (AddTree.leaf i,
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                    | none =>
                                      (AddTree.leaf
                                        (Array.size
                                          (match Array.getIdx? #[] x with
                                            | some i => (AddTree.leaf i, #[])
                                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                        Array.push
                                          (match Array.getIdx? #[] x with
                                            | some i => (AddTree.leaf i, #[])
                                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                          y)).snd
                                  x)).snd
                          y)).snd >
                0) +
        IndexAddTree.foldMap
          (match
              Array.getIdx?
                (match Array.getIdx? (Array.push #[] x) y with
                  | some i => (AddTree.leaf i, Array.push #[] x)
                  | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd
                x with
            | some i =>
              (AddTree.leaf i,
                (match Array.getIdx? (Array.push #[] x) y with
                  | some i => (AddTree.leaf i, Array.push #[] x)
                  | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd)
            | none =>
              (AddTree.leaf
                (Array.size
                  (match Array.getIdx? (Array.push #[] x) y with
                    | some i => (AddTree.leaf i, Array.push #[] x)
                    | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd),
                Array.push
                  (match Array.getIdx? (Array.push #[] x) y with
                    | some i => (AddTree.leaf i, Array.push #[] x)
                    | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd
                  x)).fst
          (match
              Array.getIdx?
                (match
                    Array.getIdx?
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd
                      x with
                  | some i =>
                    (AddTree.leaf i,
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd)
                  | none =>
                    (AddTree.leaf
                      (Array.size
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd),
                      Array.push
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd
                        x)).snd
                y with
            | some i =>
              (AddTree.leaf i,
                (match
                    Array.getIdx?
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd
                      x with
                  | some i =>
                    (AddTree.leaf i,
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd)
                  | none =>
                    (AddTree.leaf
                      (Array.size
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd),
                      Array.push
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd
                        x)).snd)
            | none =>
              (AddTree.leaf
                (Array.size
                  (match
                      Array.getIdx?
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd
                        x with
                    | some i =>
                      (AddTree.leaf i,
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd)
                    | none =>
                      (AddTree.leaf
                        (Array.size
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd),
                        Array.push
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x)).snd),
                Array.push
                  (match
                      Array.getIdx?
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd
                        x with
                    | some i =>
                      (AddTree.leaf i,
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd)
                    | none =>
                      (AddTree.leaf
                        (Array.size
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd),
                        Array.push
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x)).snd
                  y)).snd
          (_ :
            Array.size
                (match
                    Array.getIdx?
                      (match
                          Array.getIdx?
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd
                            x with
                        | some i =>
                          (AddTree.leaf i,
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd),
                            Array.push
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd
                              x)).snd
                      y with
                  | some i =>
                    (AddTree.leaf i,
                      (match
                          Array.getIdx?
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd
                            x with
                        | some i =>
                          (AddTree.leaf i,
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd),
                            Array.push
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd
                              x)).snd)
                  | none =>
                    (AddTree.leaf
                      (Array.size
                        (match
                            Array.getIdx?
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd
                              x with
                          | some i =>
                            (AddTree.leaf i,
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd),
                              Array.push
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd
                                x)).snd),
                      Array.push
                        (match
                            Array.getIdx?
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd
                              x with
                          | some i =>
                            (AddTree.leaf i,
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd),
                              Array.push
                                (match
                                    Array.getIdx?
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y with
                                  | some i =>
                                    (AddTree.leaf i,
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                  | none =>
                                    (AddTree.leaf
                                      (Array.size
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                      Array.push
                                        (match Array.getIdx? #[] x with
                                          | some i => (AddTree.leaf i, #[])
                                          | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                        y)).snd
                                x)).snd
                        y)).snd >
              0) -
      IndexAddTree.foldMap
        (match
            Array.getIdx?
              (match
                  Array.getIdx?
                    (match Array.getIdx? (Array.push #[] x) y with
                      | some i => (AddTree.leaf i, Array.push #[] x)
                      | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd
                    x with
                | some i =>
                  (AddTree.leaf i,
                    (match Array.getIdx? (Array.push #[] x) y with
                      | some i => (AddTree.leaf i, Array.push #[] x)
                      | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd)
                | none =>
                  (AddTree.leaf
                    (Array.size
                      (match Array.getIdx? (Array.push #[] x) y with
                        | some i => (AddTree.leaf i, Array.push #[] x)
                        | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd),
                    Array.push
                      (match Array.getIdx? (Array.push #[] x) y with
                        | some i => (AddTree.leaf i, Array.push #[] x)
                        | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd
                      x)).snd
              y with
          | some i =>
            (AddTree.leaf i,
              (match
                  Array.getIdx?
                    (match Array.getIdx? (Array.push #[] x) y with
                      | some i => (AddTree.leaf i, Array.push #[] x)
                      | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd
                    x with
                | some i =>
                  (AddTree.leaf i,
                    (match Array.getIdx? (Array.push #[] x) y with
                      | some i => (AddTree.leaf i, Array.push #[] x)
                      | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd)
                | none =>
                  (AddTree.leaf
                    (Array.size
                      (match Array.getIdx? (Array.push #[] x) y with
                        | some i => (AddTree.leaf i, Array.push #[] x)
                        | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd),
                    Array.push
                      (match Array.getIdx? (Array.push #[] x) y with
                        | some i => (AddTree.leaf i, Array.push #[] x)
                        | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd
                      x)).snd)
          | none =>
            (AddTree.leaf
              (Array.size
                (match
                    Array.getIdx?
                      (match Array.getIdx? (Array.push #[] x) y with
                        | some i => (AddTree.leaf i, Array.push #[] x)
                        | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd
                      x with
                  | some i =>
                    (AddTree.leaf i,
                      (match Array.getIdx? (Array.push #[] x) y with
                        | some i => (AddTree.leaf i, Array.push #[] x)
                        | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd)
                  | none =>
                    (AddTree.leaf
                      (Array.size
                        (match Array.getIdx? (Array.push #[] x) y with
                          | some i => (AddTree.leaf i, Array.push #[] x)
                          | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd),
                      Array.push
                        (match Array.getIdx? (Array.push #[] x) y with
                          | some i => (AddTree.leaf i, Array.push #[] x)
                          | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd
                        x)).snd),
              Array.push
                (match
                    Array.getIdx?
                      (match Array.getIdx? (Array.push #[] x) y with
                        | some i => (AddTree.leaf i, Array.push #[] x)
                        | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd
                      x with
                  | some i =>
                    (AddTree.leaf i,
                      (match Array.getIdx? (Array.push #[] x) y with
                        | some i => (AddTree.leaf i, Array.push #[] x)
                        | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd)
                  | none =>
                    (AddTree.leaf
                      (Array.size
                        (match Array.getIdx? (Array.push #[] x) y with
                          | some i => (AddTree.leaf i, Array.push #[] x)
                          | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd),
                      Array.push
                        (match Array.getIdx? (Array.push #[] x) y with
                          | some i => (AddTree.leaf i, Array.push #[] x)
                          | none => (AddTree.leaf (Array.size #[] + 1), Array.push (Array.push #[] x) y)).snd
                        x)).snd
                y)).fst
        (match
            Array.getIdx?
              (match
                  Array.getIdx?
                    (match
                        Array.getIdx?
                          (match Array.getIdx? #[] x with
                            | some i => (AddTree.leaf i, #[])
                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                          y with
                      | some i =>
                        (AddTree.leaf i,
                          (match Array.getIdx? #[] x with
                            | some i => (AddTree.leaf i, #[])
                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                      | none =>
                        (AddTree.leaf
                          (Array.size
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                          Array.push
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y)).snd
                    x with
                | some i =>
                  (AddTree.leaf i,
                    (match
                        Array.getIdx?
                          (match Array.getIdx? #[] x with
                            | some i => (AddTree.leaf i, #[])
                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                          y with
                      | some i =>
                        (AddTree.leaf i,
                          (match Array.getIdx? #[] x with
                            | some i => (AddTree.leaf i, #[])
                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                      | none =>
                        (AddTree.leaf
                          (Array.size
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                          Array.push
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y)).snd)
                | none =>
                  (AddTree.leaf
                    (Array.size
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd),
                    Array.push
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd
                      x)).snd
              y with
          | some i =>
            (AddTree.leaf i,
              (match
                  Array.getIdx?
                    (match
                        Array.getIdx?
                          (match Array.getIdx? #[] x with
                            | some i => (AddTree.leaf i, #[])
                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                          y with
                      | some i =>
                        (AddTree.leaf i,
                          (match Array.getIdx? #[] x with
                            | some i => (AddTree.leaf i, #[])
                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                      | none =>
                        (AddTree.leaf
                          (Array.size
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                          Array.push
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y)).snd
                    x with
                | some i =>
                  (AddTree.leaf i,
                    (match
                        Array.getIdx?
                          (match Array.getIdx? #[] x with
                            | some i => (AddTree.leaf i, #[])
                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                          y with
                      | some i =>
                        (AddTree.leaf i,
                          (match Array.getIdx? #[] x with
                            | some i => (AddTree.leaf i, #[])
                            | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                      | none =>
                        (AddTree.leaf
                          (Array.size
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                          Array.push
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y)).snd)
                | none =>
                  (AddTree.leaf
                    (Array.size
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd),
                    Array.push
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd
                      x)).snd)
          | none =>
            (AddTree.leaf
              (Array.size
                (match
                    Array.getIdx?
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd
                      x with
                  | some i =>
                    (AddTree.leaf i,
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd)
                  | none =>
                    (AddTree.leaf
                      (Array.size
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd),
                      Array.push
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd
                        x)).snd),
              Array.push
                (match
                    Array.getIdx?
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd
                      x with
                  | some i =>
                    (AddTree.leaf i,
                      (match
                          Array.getIdx?
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                            y with
                        | some i =>
                          (AddTree.leaf i,
                            (match Array.getIdx? #[] x with
                              | some i => (AddTree.leaf i, #[])
                              | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                            Array.push
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y)).snd)
                  | none =>
                    (AddTree.leaf
                      (Array.size
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd),
                      Array.push
                        (match
                            Array.getIdx?
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                              y with
                          | some i =>
                            (AddTree.leaf i,
                              (match Array.getIdx? #[] x with
                                | some i => (AddTree.leaf i, #[])
                                | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                          | none =>
                            (AddTree.leaf
                              (Array.size
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                              Array.push
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y)).snd
                        x)).snd
                y)).snd
        (_ :
          Array.size
              (match
                  Array.getIdx?
                    (match
                        Array.getIdx?
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x with
                      | some i =>
                        (AddTree.leaf i,
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd)
                      | none =>
                        (AddTree.leaf
                          (Array.size
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd),
                          Array.push
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd
                            x)).snd
                    y with
                | some i =>
                  (AddTree.leaf i,
                    (match
                        Array.getIdx?
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd
                          x with
                      | some i =>
                        (AddTree.leaf i,
                          (match
                              Array.getIdx?
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                y with
                            | some i =>
                              (AddTree.leaf i,
                                (match Array.getIdx? #[] x with
                                  | some i => (AddTree.leaf i, #[])
                                  | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                            | none =>
                              (AddTree.leaf
                                (Array.size
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                Array.push
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y)).snd)
                      | none =>
                        (AddTree.leaf
                          (Array.size
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd),
                          Array.push
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd
                            x)).snd)
                | none =>
                  (AddTree.leaf
                    (Array.size
                      (match
                          Array.getIdx?
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd
                            x with
                        | some i =>
                          (AddTree.leaf i,
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd),
                            Array.push
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd
                              x)).snd),
                    Array.push
                      (match
                          Array.getIdx?
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd
                            x with
                        | some i =>
                          (AddTree.leaf i,
                            (match
                                Array.getIdx?
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                  y with
                              | some i =>
                                (AddTree.leaf i,
                                  (match Array.getIdx? #[] x with
                                    | some i => (AddTree.leaf i, #[])
                                    | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                              | none =>
                                (AddTree.leaf
                                  (Array.size
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                  Array.push
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y)).snd)
                        | none =>
                          (AddTree.leaf
                            (Array.size
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd),
                            Array.push
                              (match
                                  Array.getIdx?
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                    y with
                                | some i =>
                                  (AddTree.leaf i,
                                    (match Array.getIdx? #[] x with
                                      | some i => (AddTree.leaf i, #[])
                                      | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd)
                                | none =>
                                  (AddTree.leaf
                                    (Array.size
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd),
                                    Array.push
                                      (match Array.getIdx? #[] x with
                                        | some i => (AddTree.leaf i, #[])
                                        | none => (AddTree.leaf (Array.size #[]), Array.push #[] x)).snd
                                      y)).snd
                              x)).snd
                      y)).snd >
            0) =
    x + y + x - y
All Messages (0)
```