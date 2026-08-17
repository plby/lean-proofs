/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.AlmostBipartite
import ErdosProblems.Erdos622.BalancedCutWindow

/-!
# The uniform DKM window on an arbitrary balanced cut

This is the final adapter from the exact finite cut bijection to the
compact-uniform normal-window estimate proved in `AlmostBipartite`.

The cut in this file may in particular be the auxiliary balanced cut
`A₀ = A \ T`, `B₀ = B ∪ T`.  Nothing here replaces the original tailored
cut `(A,B)`, which remains the cut used by the graph-theoretic good-cut and
Hamiltonicity arguments.
-/

namespace Erdos622

open Set Filter

attribute [local instance] Classical.propDecidable

/-- Exact count of the DKM cardinal-difference window on an arbitrary
balanced cut. -/
theorem almostBipartiteCount_balancedWindow_eq
    {n : ℕ} {A B : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hA : A.card = n) (hB : B.card = n)
    (a b : ℝ) :
    almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
        (fun S ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
          ((S ∩ A).card + (n - (S ∩ B).card)) ∈ Icc a b) =
      BinomialCLT.fairBinomialWindowCount (2 * n) a b := by
  unfold almostBipartiteCount almostBipartiteEvent
  let P : ℕ → ℕ → Prop := fun x y ↦
    BinomialCLT.standardizedBinomialPoint (2 * n)
      (x + (n - y)) ∈ Icc a b
  have hsplit := cutPowerset_filter_card_eq_pairCount A B hcut
    (fun X Y ↦ P X.card Y.card)
  have htransport := pairCount_card_transport A B hA hB P
  calc
    _ = (((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun S ↦
          P (S ∩ A).card (S ∩ B).card).card) := by
      congr 1
      ext S
      simp only [Finset.mem_filter, P]
    _ = Counting.pairCount A B (fun X Y ↦ P X.card Y.card) := hsplit
    _ = Counting.pairCount (Finset.univ : Finset (Fin n))
        (Finset.univ : Finset (Fin n)) (fun X Y ↦ P X.card Y.card) := htransport
    _ = BinomialCLT.fairBinomialWindowCount (2 * n) a b := by
      have hbin := Counting.binomialDifference_count n n
        (fun k : ℕ ↦ BinomialCLT.standardizedBinomialPoint (2 * n) k ∈ Icc a b)
      refine Eq.trans ?_ (Eq.trans hbin ?_)
      · unfold Counting.pairCount
        congr 1
        ext p
        simp only [Finset.mem_filter, Function.uncurry_apply_pair, P]
      · rw [Counting.binomialCount_eq_sum]
        unfold BinomialCLT.fairBinomialWindowCount
        rw [← Nat.range_succ_eq_Iic]
        simp only [two_mul]

/-- Uniform strict lower bound for the DKM window count on every balanced
cut of a `2n`-element ambient type. -/
theorem eventually_uniform_balancedCut_dkm_difference_count
    {η M : ℝ} (hη : 0 < η) (hηM : η ≤ M) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ A B : Finset (Fin (2 * n)), IsCut A B →
          A.card = n → B.card = n →
          ∀ α ∈ Icc η M, ∀ β : ℝ,
            (1 / 2 : ℝ) + margin / 2 <
              (almostBipartiteCount
                (Finset.univ : Finset (Fin (2 * n)))
                (fun S ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
                  ((S ∩ A).card + (n - (S ∩ B).card)) ∈
                    Icc (-(dkmM1 α β * Real.sqrt 2))
                      (dkmM2 α β * Real.sqrt 2)) : ℝ) /
                (2 : ℝ) ^ (2 * n) := by
  obtain ⟨margin, hmargin, huniform⟩ :=
    eventually_uniform_dkm_difference_count hη hηM
  refine ⟨margin, hmargin, ?_⟩
  filter_upwards [huniform] with n hn
  intro A B hcut hA hB α hα β
  rw [almostBipartiteCount_balancedWindow_eq hcut hA hB]
  simpa only [binomialDifference_window_count] using hn α hα β

end Erdos622
