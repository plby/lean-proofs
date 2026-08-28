import Wikipedia.HopfProblem.DegreeCollapseNegatedPresentation

/-!
# The original positive Morse ordering in negated coordinates

Native signed-chart negation complements the index in dimension seven.
Positive index ordering becomes index ordering below zero for the
negated function. The underlying critical points and state are unchanged.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem negated_native_index_add
    (p : criticalPoints (Vector 7) (fun x => -P.function x)) :
    nativeMorseIndex (Vector 7) (fun x => -P.function x) p +
      nativeMorseIndex (Vector 7) P.function p = 7 := by
  have hp : p.val ∈ criticalPoints (Vector 7) P.function :=
    criticalPoints_neg (E := Vector 7) P.function ▸ p.property
  obtain ⟨c⟩ := nonempty_signedMorseChart P.smooth P.morse p hp
  simpa only [GLOrthonormalization.Vector, finrank_euclideanSpace_fin] using
    nativeMorseIndex_neg_add c

theorem negated_index_order_below_zero
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (p q : criticalPoints (Vector 7) (fun x => -P.function x))
    (hq : -P.function q < 0) (hpq : -P.function p < -P.function q) :
    nativeMorseIndex (Vector 7) (fun x => -P.function x) p ≤
      nativeMorseIndex (Vector 7) (fun x => -P.function x) q := by
  let pP : criticalPoints (Vector 7) P.function :=
    ⟨p.val, criticalPoints_neg (E := Vector 7) P.function ▸ p.property⟩
  let qP : criticalPoints (Vector 7) P.function :=
    ⟨q.val, criticalPoints_neg (E := Vector 7) P.function ▸ q.property⟩
  have hh := horder qP pP (neg_neg_iff_pos.mp hq) (neg_lt_neg_iff.mp hpq)
  have hpidx := P.negated_native_index_add p
  have hqidx := P.negated_native_index_add q
  change nativeMorseIndex (Vector 7) P.function q ≤
    nativeMorseIndex (Vector 7) P.function p at hh
  omega

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
