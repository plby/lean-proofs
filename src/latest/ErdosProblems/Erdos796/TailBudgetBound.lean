import ErdosProblems.Erdos796.SplitNormalCounting
import ErdosProblems.Erdos796.DyadicOverlapBound

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite Bonferroni bound for the split semiprime tail

The low-multiplier, large-first-prime split piece is charged to the single
semiprime-tail parameter space.  Its total fibre multiplicity is bounded by
the tail score plus the explicit dyadic pairwise-overlap budget.
-/

namespace Erdos796

namespace TailBudgetBound

open scoped BigOperators
open SplitNormalCounting SemiprimeTailBudget DyadicOverlapBound

theorem card_positiveIcc_pred_le (W : ℕ) :
    (positiveIcc (W - 1)).card ≤ W := by
  simp [positiveIcc]

/-- Exact finite tail bound used in the structural assembly. -/
theorem card_splitTailPiece_le_primeTailScore_add_overlap
    {n Y Z W : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (hWZ : W ≤ Z) :
    (splitTailPiece n Y Z W A).card ≤
      SmoothAugmentation.primeTailScore n Z +
        W ^ 2 * overlapDyadicBound n Z := by
  let M := positiveIcc (W - 1)
  let K := overlapDyadicBound n Z
  have hoverlap : ∀ s ∈ M, ∀ t ∈ M, s ≠ t →
      (multiplierOverlap n Z A s t).card ≤ K := by
    intro s hs t ht hst
    have hs' := mem_positiveIcc.mp hs
    have ht' := mem_positiveIcc.mp ht
    have hsW : s < W := by omega
    have htW : t < W := by omega
    exact card_multiplierOverlap_le_overlapDyadicBound_of_lt_of_le
      hA hs'.1 ht'.1 hst hsW htW hWZ
  have hsum := sum_card_multiplierFibres_le_primeTailScore_add hoverlap
  have hpiece := card_splitTailPiece_le_sum
    (n := n) (Y := Y) (Z := Z) (W := W) hA
  have hMcard : M.card ≤ W := by
    simpa [M] using! card_positiveIcc_pred_le W
  have hsq : M.card ^ 2 ≤ W ^ 2 := Nat.pow_le_pow_left hMcard 2
  calc
    (splitTailPiece n Y Z W A).card ≤
        ∑ s ∈ M, (multiplierFiberEdges n Z A s).card := by
      simpa [M] using! hpiece
    _ ≤ SmoothAugmentation.primeTailScore n Z + M.card ^ 2 * K := hsum
    _ ≤ SmoothAugmentation.primeTailScore n Z + W ^ 2 * K := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right K hsq) _
    _ = SmoothAugmentation.primeTailScore n Z +
        W ^ 2 * overlapDyadicBound n Z := rfl

end TailBudgetBound

end Erdos796
