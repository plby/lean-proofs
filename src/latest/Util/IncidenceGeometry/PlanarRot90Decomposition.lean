import Util.IncidenceGeometry.PlanarRot90

open Classical
noncomputable section

lemma PlanarRot90Decomposition (d v : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0) :
    v =
      (inner ℝ v d / (‖d‖ ^ 2)) • d +
        (inner ℝ v (PlanarRot90 d) / (‖d‖ ^ 2)) • PlanarRot90 d := by
  have hden : ‖d‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
  have hnormsq : ‖d‖ ^ 2 = d 0 ^ 2 + d 1 ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp
  apply PiLp.ext
  intro k
  fin_cases k <;>
    simp [PlanarRot90, PiLp.inner_apply] <;>
    field_simp [hden] <;>
    rw [hnormsq] <;>
    ring
