import Util.IncidenceGeometry.PlanarRot90

open Classical
noncomputable section

lemma PlanarRot90Decomposition (d v : EuclideanSpace ℝ (Fin 2)) (hd : d ≠ 0) :
    v =
      (inner ℝ v d / (‖d‖ ^ 2)) • d +
        (inner ℝ v (PlanarRot90 d) / (‖d‖ ^ 2)) • PlanarRot90 d := by
  have hnormsq : ‖d‖ ^ 2 = d 0 * d 0 + d 1 * d 1 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp
    ring
  apply PiLp.ext
  intro k
  fin_cases k
  · simp [PlanarRot90, PiLp.inner_apply, hnormsq]
    have hden : d.ofLp 0 ^ 2 + d.ofLp 1 ^ 2 ≠ 0 := by
      have hnormne : ‖d‖ ^ 2 ≠ 0 := by
        exact pow_ne_zero 2 (by simpa [norm_eq_zero] using hd)
      have hsquares :
          d.ofLp 0 ^ 2 + d.ofLp 1 ^ 2 =
            d.ofLp 0 * d.ofLp 0 + d.ofLp 1 * d.ofLp 1 := by
        ring
      simpa [hnormsq, hsquares] using hnormne
    field_simp [hden]
    ring
  · simp [PlanarRot90, PiLp.inner_apply, hnormsq]
    have hdenprod : d.ofLp 0 * d.ofLp 0 + d.ofLp 1 * d.ofLp 1 ≠ 0 := by
      have hnormne : ‖d‖ ^ 2 ≠ 0 := by
        exact pow_ne_zero 2 (by simpa [norm_eq_zero] using hd)
      simpa [hnormsq] using hnormne
    have hden : d.ofLp 1 ^ 2 + d.ofLp 0 ^ 2 ≠ 0 := by
      have hden' : d.ofLp 0 ^ 2 + d.ofLp 1 ^ 2 ≠ 0 := by
        have hnormne : ‖d‖ ^ 2 ≠ 0 := by
          exact pow_ne_zero 2 (by simpa [norm_eq_zero] using hd)
        have hsquares :
            d.ofLp 0 ^ 2 + d.ofLp 1 ^ 2 =
              d.ofLp 0 * d.ofLp 0 + d.ofLp 1 * d.ofLp 1 := by
          ring
        simpa [hnormsq, hsquares] using hnormne
      intro h
      apply hden'
      linarith
    field_simp [hdenprod]
    ring_nf
    symm
    calc
      d.ofLp 1 ^ 2 * v.ofLp 1 *
            (d.ofLp 1 ^ 2 + d.ofLp 0 ^ 2)⁻¹ +
          d.ofLp 0 ^ 2 * v.ofLp 1 *
            (d.ofLp 1 ^ 2 + d.ofLp 0 ^ 2)⁻¹ =
          v.ofLp 1 *
            ((d.ofLp 1 ^ 2 + d.ofLp 0 ^ 2) *
              (d.ofLp 1 ^ 2 + d.ofLp 0 ^ 2)⁻¹) := by
          ring
      _ = v.ofLp 1 * 1 := by
          rw [mul_inv_cancel₀ hden]
      _ = v.ofLp 1 := by ring
