import Mathlib.Combinatorics.SimpleGraph.Clique

attribute [local instance] Classical.propDecidable

universe u_1

open Lean Elab Command

private def comparatorNameWithNumericComponents (s : String) : Name :=
  s.splitOn "." |>.foldl (init := .anonymous) fun name component =>
    match component.toNat? with
    | some n => .num name n
    | none => .str name component

private def comparatorNumericName : Name → Name
  | .anonymous => .anonymous
  | .num parent n => .num (comparatorNumericName parent) n
  | .str parent component =>
      let parent := comparatorNumericName parent
      match component.toNat? with
      | some n => .num parent n
      | none => .str parent component

private def comparatorNumericExpr (e : Expr) : Expr :=
  e.replace fun
    | .const name levels => some <| .const (comparatorNumericName name) levels
    | _ => none

elab "comparator_copy_declaration " source:ident " as " target:str : command => do
  let sourceName := source.getId
  let some info := (← getEnv).find? sourceName
    | throwError "unknown source declaration {sourceName}"
  let targetName := comparatorNameWithNumericComponents target.getString
  let declaration ← match info with
    | .axiomInfo value =>
        pure <| Declaration.axiomDecl
          { value with name := targetName, type := comparatorNumericExpr value.type }
    | .defnInfo value =>
        pure <| Declaration.defnDecl
          { value with
            name := targetName
            type := comparatorNumericExpr value.type
            value := comparatorNumericExpr value.value }
    | .thmInfo value =>
        pure <| Declaration.thmDecl
          { value with
            name := targetName
            type := comparatorNumericExpr value.type
            value := comparatorNumericExpr value.value }
    | _ => throwError "unsupported declaration kind for {sourceName}"
  liftCoreM <| addAndCompile declaration

noncomputable def _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Bool) →
      Rat
  := by
  sorry

comparator_copy_declaration _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum as "_private.ErdosProblems.Erdos24.0.Erdos24.totalFlagContribPermSum"

noncomputable def Erdos24.totalFlagContrib :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Bool) →
      Rat
  := by
  sorry

noncomputable def Erdos24.mkAdj5 :
    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) → Bool) →
      Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
        Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) → Bool
  := by
  sorry

noncomputable def _private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits :
    Bool →
      Bool →
        Bool →
          Bool →
            Bool →
              Bool →
                Bool →
                  Bool →
                    Bool →
                      Bool → Fin (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) → Bool
  := by
  sorry

comparator_copy_declaration _private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits as "_private.ErdosProblems.Erdos24.0.Erdos24.edgeBits"

axiom _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContrib_mkAdj5_edgeBits_eq_permSum._native.native_decide.ax_1_1 :
    @Eq.{1} Bool
      (@Decidable.decide
        (∀ (b01 b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool),
          @Eq.{1} Rat
            (Erdos24.totalFlagContrib
              (Erdos24.mkAdj5
                (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits b01 b02 b03 b04 b12 b13 b14 b23 b24
                  b34)))
            (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
              (Erdos24.mkAdj5
                (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits b01 b02 b03 b04 b12 b13 b14 b23 b24
                  b34))))
        (@Bool.instDecidableForallOfDecidablePred
          (fun (b01 : Bool) ↦
            ∀ (b02 b03 b04 b12 b13 b14 b23 b24 b34 : Bool),
              @Eq.{1} Rat
                (Erdos24.totalFlagContrib
                  (Erdos24.mkAdj5
                    (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits b01 b02 b03 b04 b12 b13 b14 b23
                      b24 b34)))
                (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                  (Erdos24.mkAdj5
                    (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits b01 b02 b03 b04 b12 b13 b14 b23
                      b24 b34))))
          fun (a : Bool) ↦
          @Bool.instDecidableForallOfDecidablePred
            (fun (b02 : Bool) ↦
              ∀ (b03 b04 b12 b13 b14 b23 b24 b34 : Bool),
                @Eq.{1} Rat
                  (Erdos24.totalFlagContrib
                    (Erdos24.mkAdj5
                      (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a b02 b03 b04 b12 b13 b14 b23
                        b24 b34)))
                  (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                    (Erdos24.mkAdj5
                      (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a b02 b03 b04 b12 b13 b14 b23
                        b24 b34))))
            fun (a_1 : Bool) ↦
            @Bool.instDecidableForallOfDecidablePred
              (fun (b03 : Bool) ↦
                ∀ (b04 b12 b13 b14 b23 b24 b34 : Bool),
                  @Eq.{1} Rat
                    (Erdos24.totalFlagContrib
                      (Erdos24.mkAdj5
                        (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 b03 b04 b12 b13 b14 b23
                          b24 b34)))
                    (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                      (Erdos24.mkAdj5
                        (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 b03 b04 b12 b13 b14 b23
                          b24 b34))))
              fun (a_2 : Bool) ↦
              @Bool.instDecidableForallOfDecidablePred
                (fun (b04 : Bool) ↦
                  ∀ (b12 b13 b14 b23 b24 b34 : Bool),
                    @Eq.{1} Rat
                      (Erdos24.totalFlagContrib
                        (Erdos24.mkAdj5
                          (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 b04 b12 b13 b14
                            b23 b24 b34)))
                      (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                        (Erdos24.mkAdj5
                          (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 b04 b12 b13 b14
                            b23 b24 b34))))
                fun (a_3 : Bool) ↦
                @Bool.instDecidableForallOfDecidablePred
                  (fun (b12 : Bool) ↦
                    ∀ (b13 b14 b23 b24 b34 : Bool),
                      @Eq.{1} Rat
                        (Erdos24.totalFlagContrib
                          (Erdos24.mkAdj5
                            (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 b12 b13 b14
                              b23 b24 b34)))
                        (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                          (Erdos24.mkAdj5
                            (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 b12 b13 b14
                              b23 b24 b34))))
                  fun (a_4 : Bool) ↦
                  @Bool.instDecidableForallOfDecidablePred
                    (fun (b13 : Bool) ↦
                      ∀ (b14 b23 b24 b34 : Bool),
                        @Eq.{1} Rat
                          (Erdos24.totalFlagContrib
                            (Erdos24.mkAdj5
                              (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4 b13
                                b14 b23 b24 b34)))
                          (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                            (Erdos24.mkAdj5
                              (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4 b13
                                b14 b23 b24 b34))))
                    fun (a_5 : Bool) ↦
                    @Bool.instDecidableForallOfDecidablePred
                      (fun (b14 : Bool) ↦
                        ∀ (b23 b24 b34 : Bool),
                          @Eq.{1} Rat
                            (Erdos24.totalFlagContrib
                              (Erdos24.mkAdj5
                                (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4 a_5
                                  b14 b23 b24 b34)))
                            (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                              (Erdos24.mkAdj5
                                (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4 a_5
                                  b14 b23 b24 b34))))
                      fun (a_6 : Bool) ↦
                      @Bool.instDecidableForallOfDecidablePred
                        (fun (b23 : Bool) ↦
                          ∀ (b24 b34 : Bool),
                            @Eq.{1} Rat
                              (Erdos24.totalFlagContrib
                                (Erdos24.mkAdj5
                                  (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4
                                    a_5 a_6 b23 b24 b34)))
                              (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                                (Erdos24.mkAdj5
                                  (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4
                                    a_5 a_6 b23 b24 b34))))
                        fun (a_7 : Bool) ↦
                        @Bool.instDecidableForallOfDecidablePred
                          (fun (b24 : Bool) ↦
                            ∀ (b34 : Bool),
                              @Eq.{1} Rat
                                (Erdos24.totalFlagContrib
                                  (Erdos24.mkAdj5
                                    (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4
                                      a_5 a_6 a_7 b24 b34)))
                                (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                                  (Erdos24.mkAdj5
                                    (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4
                                      a_5 a_6 a_7 b24 b34))))
                          fun (a_8 : Bool) ↦
                          @Bool.instDecidableForallOfDecidablePred
                            (fun (b34 : Bool) ↦
                              @Eq.{1} Rat
                                (Erdos24.totalFlagContrib
                                  (Erdos24.mkAdj5
                                    (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4
                                      a_5 a_6 a_7 a_8 b34)))
                                (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                                  (Erdos24.mkAdj5
                                    (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4
                                      a_5 a_6 a_7 a_8 b34))))
                            fun (a_9 : Bool) ↦
                            instDecidableEqRat
                              (Erdos24.totalFlagContrib
                                (Erdos24.mkAdj5
                                  (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4
                                    a_5 a_6 a_7 a_8 a_9)))
                              (_private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContribPermSum
                                (Erdos24.mkAdj5
                                  (_private.ErdosProblems.Erdos24.«0».Erdos24.edgeBits a a_1 a_2 a_3 a_4
                                    a_5 a_6 a_7 a_8 a_9)))))
      Bool.true

comparator_copy_declaration _private.ErdosProblems.Erdos24.«0».Erdos24.totalFlagContrib_mkAdj5_edgeBits_eq_permSum._native.native_decide.ax_1_1 as "_private.ErdosProblems.Erdos24.0.Erdos24.totalFlagContrib_mkAdj5_edgeBits_eq_permSum._native.native_decide.ax_1_1"

noncomputable def SimpleGraph.numC5 :
    {V : Type u_1} → [Fintype.{u_1} V] → SimpleGraph.{u_1} V → Nat
  := by
  let _ := ULift.{u_1, 0} PUnit
  sorry

theorem Erdos24.erdos_pentagon_conjecture :
    ∀ (n : Nat)
      (G :
        SimpleGraph.{0}
          (Fin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n))),
      @SimpleGraph.CliqueFree.{0}
          (Fin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n))
          G (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
        @LE.le.{0} Nat instLENat
          (@SimpleGraph.numC5.{0}
            (Fin
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n))
            (Fin.fintype
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) n))
            G)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
  := by
  sorry
