import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient

attribute [local instance] Classical.propDecidable

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

noncomputable def Erdos418.m_BS :
    Nat
  := by
  sorry

axiom _private.ErdosProblems.Erdos418.«0».Erdos418.computation_lemma_check._native.native_decide.ax_1_1 :
    @Eq.{1} Bool
      (@Decidable.decide
        (∀ (m : Nat),
          @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
              (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Erdos418.m_BS
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Erdos418.m_BS))
              m →
            @Odd.{0} Nat Nat.instSemiring m →
              @Squarefree.{0} Nat Nat.instMonoid m →
                Not
                    (@Dvd.dvd.{0} Nat Nat.instDvd
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) m) →
                  @Ne.{1} Rat
                    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                        (@Nat.cast.{0} Rat Rat.instNatCast m))
                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                        (@Nat.cast.{0} Rat Rat.instNatCast m)
                        (@Finset.prod.{0, 0} Nat Rat Rat.commMonoid m.primeFactors fun (p : Nat) ↦
                          @HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                              (@Nat.cast.{0} Rat Rat.instNatCast p)))))
                    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                      (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                      (@Nat.cast.{0} Rat Rat.instNatCast Erdos418.m_BS)))
        (@Finset.decidableDforallFinset.{0} Nat
          (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Erdos418.m_BS
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Erdos418.m_BS))
          (fun (m : Nat)
              (a :
                @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                  (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                  (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Erdos418.m_BS
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Erdos418.m_BS))
                  m) ↦
            @Odd.{0} Nat Nat.instSemiring m →
              @Squarefree.{0} Nat Nat.instMonoid m →
                Not
                    (@Dvd.dvd.{0} Nat Nat.instDvd
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) m) →
                  @Ne.{1} Rat
                    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                        (@Nat.cast.{0} Rat Rat.instNatCast m))
                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                        (@Nat.cast.{0} Rat Rat.instNatCast m)
                        (@Finset.prod.{0, 0} Nat Rat Rat.commMonoid m.primeFactors fun (p : Nat) ↦
                          @HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                            (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                              (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                              (@Nat.cast.{0} Rat Rat.instNatCast p)))))
                    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                      (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                      (@Nat.cast.{0} Rat Rat.instNatCast Erdos418.m_BS)))
          fun (a : Nat)
            (h :
              @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
                (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
                (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Erdos418.m_BS
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) Erdos418.m_BS))
                a) ↦
          (fun (a : Nat) ↦
              @forall_prop_decidable (@Odd.{0} Nat Nat.instSemiring a)
                (fun (a_1 : @Odd.{0} Nat Nat.instSemiring a) ↦
                  @Squarefree.{0} Nat Nat.instMonoid a →
                    Not
                        (@Dvd.dvd.{0} Nat Nat.instDvd
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) a) →
                      @Ne.{1} Rat
                        (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                            (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                            (@Nat.cast.{0} Rat Rat.instNatCast a))
                          (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                            (@Nat.cast.{0} Rat Rat.instNatCast a)
                            (@Finset.prod.{0, 0} Nat Rat Rat.commMonoid a.primeFactors fun (p : Nat) ↦
                              @HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                                (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                  (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                  (@Nat.cast.{0} Rat Rat.instNatCast p)))))
                        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                          (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                          (@Nat.cast.{0} Rat Rat.instNatCast Erdos418.m_BS)))
                a.instDecidablePredOdd fun (h : @Odd.{0} Nat Nat.instSemiring a) ↦
                (fun (a : Nat) ↦
                    @forall_prop_decidable (@Squarefree.{0} Nat Nat.instMonoid a)
                      (fun (a_1 : @Squarefree.{0} Nat Nat.instMonoid a) ↦
                        Not
                            (@Dvd.dvd.{0} Nat Nat.instDvd
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) a) →
                          @Ne.{1} Rat
                            (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                              (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                (@Nat.cast.{0} Rat Rat.instNatCast a))
                              (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                (@Nat.cast.{0} Rat Rat.instNatCast a)
                                (@Finset.prod.{0, 0} Nat Rat Rat.commMonoid a.primeFactors
                                  fun (p : Nat) ↦
                                  @HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                                    (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                      (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                      (@Nat.cast.{0} Rat Rat.instNatCast p)))))
                            (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                              (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                              (@Nat.cast.{0} Rat Rat.instNatCast Erdos418.m_BS)))
                      a.instDecidablePredSquarefree fun (h : @Squarefree.{0} Nat Nat.instMonoid a) ↦
                      (fun (a : Nat) ↦
                          @forall_prop_decidable
                            (Not
                              (@Dvd.dvd.{0} Nat Nat.instDvd
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) a))
                            (fun
                                (a_1 :
                                  Not
                                    (@Dvd.dvd.{0} Nat Nat.instDvd
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      a)) ↦
                              @Ne.{1} Rat
                                (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                                  (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                    (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                    (@Nat.cast.{0} Rat Rat.instNatCast a))
                                  (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                    (@Nat.cast.{0} Rat Rat.instNatCast a)
                                    (@Finset.prod.{0, 0} Nat Rat Rat.commMonoid a.primeFactors
                                      fun (p : Nat) ↦
                                      @HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                                        (@OfNat.ofNat.{0} Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat
                                          (@instHDiv.{0} Rat Rat.instDiv)
                                          (@OfNat.ofNat.{0} Rat (nat_lit 1)
                                            (@Rat.instOfNat (nat_lit 1)))
                                          (@Nat.cast.{0} Rat Rat.instNatCast p)))))
                                (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                  (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                  (@Nat.cast.{0} Rat Rat.instNatCast Erdos418.m_BS)))
                            (@instDecidableNot
                              (@Dvd.dvd.{0} Nat Nat.instDvd
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) a)
                              (Nat.decidable_dvd
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) a))
                            fun
                              (h :
                                Not
                                  (@Dvd.dvd.{0} Nat Nat.instDvd
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) a)) ↦
                            (fun (a : Nat) ↦
                                @instDecidableNot
                                  (@Eq.{1} Rat
                                    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                        (@Nat.cast.{0} Rat Rat.instNatCast a))
                                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                        (@Nat.cast.{0} Rat Rat.instNatCast a)
                                        (@Finset.prod.{0, 0} Nat Rat Rat.commMonoid a.primeFactors
                                          fun (p : Nat) ↦
                                          @HSub.hSub.{0, 0, 0} Rat Rat Rat
                                            (@instHSub.{0} Rat Rat.instSub)
                                            (@OfNat.ofNat.{0} Rat (nat_lit 1)
                                              (@Rat.instOfNat (nat_lit 1)))
                                            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat
                                              (@instHDiv.{0} Rat Rat.instDiv)
                                              (@OfNat.ofNat.{0} Rat (nat_lit 1)
                                                (@Rat.instOfNat (nat_lit 1)))
                                              (@Nat.cast.{0} Rat Rat.instNatCast p)))))
                                    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                      (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                      (@Nat.cast.{0} Rat Rat.instNatCast Erdos418.m_BS)))
                                  (instDecidableEqRat
                                    (@HSub.hSub.{0, 0, 0} Rat Rat Rat (@instHSub.{0} Rat Rat.instSub)
                                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                        (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                        (@Nat.cast.{0} Rat Rat.instNatCast a))
                                      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                        (@Nat.cast.{0} Rat Rat.instNatCast a)
                                        (@Finset.prod.{0, 0} Nat Rat Rat.commMonoid a.primeFactors
                                          fun (p : Nat) ↦
                                          @HSub.hSub.{0, 0, 0} Rat Rat Rat
                                            (@instHSub.{0} Rat Rat.instSub)
                                            (@OfNat.ofNat.{0} Rat (nat_lit 1)
                                              (@Rat.instOfNat (nat_lit 1)))
                                            (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat
                                              (@instHDiv.{0} Rat Rat.instDiv)
                                              (@OfNat.ofNat.{0} Rat (nat_lit 1)
                                                (@Rat.instOfNat (nat_lit 1)))
                                              (@Nat.cast.{0} Rat Rat.instNatCast p)))))
                                    (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
                                      (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                      (@Nat.cast.{0} Rat Rat.instNatCast Erdos418.m_BS))))
                              a)
                        a)
                  a)
            a))
      Bool.true

comparator_copy_declaration _private.ErdosProblems.Erdos418.«0».Erdos418.computation_lemma_check._native.native_decide.ax_1_1 as "_private.ErdosProblems.Erdos418.0.Erdos418.computation_lemma_check._native.native_decide.ax_1_1"

theorem Erdos418.erdos_418 :
    @Set.Infinite.{0} Nat
      (@Compl.compl.{0} (Set.{0} Nat) (@Set.instCompl.{0} Nat)
        (@setOf.{0} Nat fun (x : Nat) ↦
          @Exists.{1} Nat fun (n : Nat) ↦
            @Eq.{1} Nat (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) n n.totient)
              x))
  := by
  sorry
