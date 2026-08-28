import Wikipedia.NoExoticSixSphere.AnnulusDoublePointCompactness

/-!
# The interior and both boundary spheres of the original annulus

The original closed annulus is the closed radius-two ball minus the open
unit ball. Its interior is exactly the open annulus, and its frontier is
the union of the literal radius-one and radius-two spheres.
-/

open Set Metric

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization

theorem domain_eq_closedBall_sdiff_ball (p : ℕ) :
    domain p = closedBall (0 : Vector (p + 1)) 2 \ ball 0 1 := by
  ext x
  simp only [domain, mem_ofPred, mem_sdiff, mem_closedBall_zero_iff,
    mem_ball_zero_iff, not_lt, and_comm]

theorem interior_domain (p : ℕ) : interior (domain p) = openDomain p := by
  rw [domain_eq_closedBall_sdiff_ball, sdiff_eq, interior_inter,
    interior_closedBall _ (by norm_num : (2 : ℝ) ≠ 0), interior_compl,
    closure_ball _ one_ne_zero]
  ext x
  simp only [openDomain, mem_ofPred, mem_inter_iff, mem_compl_iff,
    mem_ball_zero_iff, mem_closedBall_zero_iff, not_le, and_comm]

theorem frontier_domain (p : ℕ) :
    frontier (domain p) = sphere (0 : Vector (p + 1)) 1 ∪ sphere 0 2 := by
  rw [(isClosed_domain p).frontier_eq, interior_domain]
  ext x
  simp only [mem_sdiff, mem_union, mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨hx, hnot⟩
    exact boundary_of_not_mem_openDomain hx hnot
  · rintro (hx | hx)
    · refine ⟨?_, ?_⟩
      · change 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2
        rw [hx]
        exact ⟨le_rfl, by norm_num⟩
      · intro h
        exact hx.not_gt h.1
    · refine ⟨?_, ?_⟩
      · change 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2
        rw [hx]
        exact ⟨by norm_num, le_rfl⟩
      · intro h
        exact hx.not_lt h.2

end NoExoticSixSphere.SphereAnnulus
