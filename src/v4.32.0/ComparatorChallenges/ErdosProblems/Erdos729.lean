import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false

namespace Erdos729

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

@[implicit_reducible] def main_theorem.match_1.{u} :
    (motive : ℕ × ℕ × ℕ → Sort u) →
      (T : ℕ × ℕ × ℕ) →
        ((a b n : ℕ) → motive (a, b, n)) → motive T :=
  fun motive T h ↦
    Prod.casesOn T fun a t ↦ Prod.casesOn t fun b n ↦ h a b n

end Erdos729

attribute [local instance] Classical.propDecidable

universe u_1

theorem Erdos729.main_theorem :
    ∀ (C : Real),
      @GT.gt.{0} Real Real.instLT C
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Exists.{1} Nat fun (K : Nat) ↦
          And (@GE.ge.{0} Nat instLENat K (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@Set.Infinite.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
              (@setOf.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat))
                fun (T : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) ↦
                Erdos729.main_theorem.match_1.{1}
                  (fun (T : Prod.{0, 0} Nat (Prod.{0, 0} Nat Nat)) ↦ Prop) T fun (a b n : Nat) ↦
                  And
                    (@GT.gt.{0} Nat instLTNat a
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (And
                      (@GT.gt.{0} Nat instLTNat b
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (And
                        (@GT.gt.{0} Nat instLTNat n
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (And
                          (@GT.gt.{0} Real Real.instLT
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast a)
                              (@Nat.cast.{0} Real Real.instNatCast b))
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast n)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                                (Real.log (@Nat.cast.{0} Real Real.instNatCast n)))))
                          (∀ (p : Nat),
                            Nat.Prime p →
                              @GT.gt.{0} Nat instLTNat p K →
                                @Eq.{1} Nat
                                  (padicValNat p
                                    (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
                                        (@Nat.cast.{0} Rat Rat.instNatCast n.factorial)
                                        (@HMul.hMul.{0, 0, 0} Rat Rat Rat
                                          (@instHMul.{0} Rat Rat.instMul)
                                          (@Nat.cast.{0} Rat Rat.instNatCast a.factorial)
                                          (@Nat.cast.{0} Rat Rat.instNatCast b.factorial))).den)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
  := by
  sorry
