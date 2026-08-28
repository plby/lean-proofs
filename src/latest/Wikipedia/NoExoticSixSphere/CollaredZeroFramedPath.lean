import Wikipedia.NoExoticSixSphere.CollaredZeroFramedComparison

/-!
# Finite native surgery paths retain a full endpoint framed comparison

Induction composes actual stabilized framed diffeomorphisms, not merely
unframed boundary maps. A path on the reversed state includes the constructed
signed reversal comparison before its surgery steps.
-/

noncomputable section

namespace NoExoticSixSphere.CollaredZero

open Wikipedia.HopfProblem.DegreeCollapse

variable {B : Type} [TopologicalSpace B]

theorem comparison_of_step {S U : LowCollaredSevenState B} (h : S.Step U) (b : B) :
    Nonempty (Comparison S U b) := by
  obtain ⟨d, _, _, f, A, hA, T, hT, rfl⟩ := h
  exact ⟨performComparison S b A hA T hT⟩

theorem comparison_of_reachable {S U : LowCollaredSevenState B} (h : S.Reachable U) (b : B) :
    Nonempty (Comparison S U b) := by
  induction h with
  | refl => exact ⟨comparisonRefl S b⟩
  | @tail U V hSU hUV ih =>
    obtain ⟨F⟩ := ih
    obtain ⟨G⟩ := comparison_of_step hUV b
    exact ⟨comparisonTrans F G⟩

theorem comparison_after_reversed_path {S U V : LowCollaredSevenState B}
    (hSU : S.Reachable U) (hUV : U.reverse.Reachable V) (b : B) :
    Nonempty (Comparison S V b) := by
  obtain ⟨F⟩ := comparison_of_reachable hSU b
  obtain ⟨G⟩ := comparison_of_reachable hUV b
  exact ⟨comparisonTrans F (comparisonTrans (reverseComparison U b) G)⟩

end NoExoticSixSphere.CollaredZero
