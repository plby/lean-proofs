import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Defs

open Nat Finset Real Filter

namespace BinQuadForm

end BinQuadForm

def Theorem_2_2 : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ n₀ : ℕ,
    ∀ (V : Finset ℕ) (E : Finset (Finset ℕ)),
    V.card ≥ n₀ →
    (∀ e ∈ E, e.card = 3 ∧ e ⊆ V) →
    (∀ e ∈ E, ∃! K, K ⊆ V ∧ K.card ≥ 4 ∧
      (∀ t ⊆ K, t.card = 3 → t ∈ E) ∧ e ⊆ K) →
    (E.card : ℝ) < ε * (V.card : ℝ) ^ 3

axiom frankl_roedl_theorem : Theorem_2_2

namespace Erdos658

section
open Finset

def gridRange (N : ℕ) : Finset ℤ :=
  (Finset.range N).image (↑· : ℕ → ℤ)

def grid2 (N : ℕ) : Finset (ℤ × ℤ) :=
  gridRange N ×ˢ gridRange N

def grid3 (N : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  gridRange N ×ˢ (gridRange N ×ˢ gridRange N)

def ContainsSquare (S : Finset (ℤ × ℤ)) : Prop :=
  ∃ a b d : ℤ, d ≠ 0 ∧
    (a, b) ∈ S ∧ (a + d, b) ∈ S ∧
    (a, b + d) ∈ S ∧ (a + d, b + d) ∈ S

def ContainsQuadruple (S : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∃ a b c d : ℤ, d ≠ 0 ∧
    (a, b, c) ∈ S ∧ (a + d, b, c) ∈ S ∧
    (a, b + d, c) ∈ S ∧ (a + d, b + d, c + d) ∈ S
end

end Erdos658

attribute [local instance] Classical.propDecidable

theorem Erdos658.Theorem_1_2 :
    Theorem_2_2 →
      ∀ (δ : Real),
        @GT.gt.{0} Real Real.instLT δ
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Exists.{1} Nat fun (N₀ : Nat) ↦
            ∀ (N : Nat),
              @LT.lt.{0} Nat instLTNat N₀ N →
                ∀ (S : Finset.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int))),
                  @LE.le.{0} (Finset.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)))
                      (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)))
                        (@PartialOrder.toPreorder.{0}
                          (Finset.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)))
                          (@Finset.instPartialOrder.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)))))
                      S (Erdos658.grid3 N) →
                    @LE.le.{0} Real Real.instLE
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) δ
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat
                              (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@Nat.cast.{0} Real Real.instNatCast N)
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} (Prod.{0, 0} Int (Prod.{0, 0} Int Int)) S)) →
                      Erdos658.ContainsQuadruple S
  := by
  sorry
theorem Erdos658.Theorem_1_1 :
    Theorem_2_2 →
      ∀ (δ : Real),
        @GT.gt.{0} Real Real.instLT δ
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Exists.{1} Nat fun (N₀ : Nat) ↦
            ∀ (N : Nat),
              @LT.lt.{0} Nat instLTNat N₀ N →
                ∀ (S : Finset.{0} (Prod.{0, 0} Int Int)),
                  @LE.le.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                      (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                        (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                          (@Finset.instPartialOrder.{0} (Prod.{0, 0} Int Int))))
                      S (Erdos658.grid2 N) →
                    @LE.le.{0} Real Real.instLE
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) δ
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat
                              (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@Nat.cast.{0} Real Real.instNatCast N)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@Finset.card.{0} (Prod.{0, 0} Int Int) S)) →
                      Erdos658.ContainsSquare S
  := by
  sorry
theorem Erdos658.erdos658 :
    ∀ (δ : Real),
      @GT.gt.{0} Real Real.instLT δ
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Exists.{1} Nat fun (N₀ : Nat) ↦
          ∀ (N : Nat),
            @LT.lt.{0} Nat instLTNat N₀ N →
              ∀ (S : Finset.{0} (Prod.{0, 0} Int Int)),
                @LE.le.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                    (@Preorder.toLE.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                      (@PartialOrder.toPreorder.{0} (Finset.{0} (Prod.{0, 0} Int Int))
                        (@Finset.instPartialOrder.{0} (Prod.{0, 0} Int Int))))
                    S (Erdos658.grid2 N) →
                  @LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) δ
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat
                            (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@Nat.cast.{0} Real Real.instNatCast N)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Nat.cast.{0} Real Real.instNatCast (@Finset.card.{0} (Prod.{0, 0} Int Int) S)) →
                    Erdos658.ContainsSquare S
  := by
  sorry
