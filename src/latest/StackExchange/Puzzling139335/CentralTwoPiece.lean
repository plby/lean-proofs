import StackExchange.Puzzling139335.CentralNonRotation
import StackExchange.Puzzling139335.CentralRotation

/-!
# Two congruent pieces of a centrally symmetric Jordan region

For a proper Jordan crosscut, congruence of the two closed sides forces
the center of symmetry onto their common cut. The exhaustive plane-isometry
classification is discharged by the nonrotation and direct-rotation proofs.
No rectifiability, boundary-area, or prescribed-congruence hypothesis is used.
-/

open Set Schoenflies

namespace Puzzling139335.JordanCrosscut

/-- A centrally symmetric Jordan region cannot be cut into two congruent
closed Jordan sides with the center strictly inside one side. -/
theorem center_mem_of_congruent_sides
    {C Γ M N : Set Plane} {p q c : Plane}
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (hcongr : Congruent (closure (inside (M ∪ Γ))) (closure (inside (N ∪ Γ))))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) : c ∈ Γ := by
  obtain ⟨g, hg⟩ := hcongr
  rcases h.center_mem_or_other_rotation houter g hg hsym with hc | ⟨a, _, ha, hform⟩
  · exact hc
  · exact h.center_mem_of_direct_multiplier_ne_neg_one houter g a
      (PlaneIsometries.complexEquiv (g 0)) ha hform hg hsym

end Puzzling139335.JordanCrosscut
