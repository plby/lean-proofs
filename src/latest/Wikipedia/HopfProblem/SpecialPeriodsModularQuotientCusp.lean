import Wikipedia.HopfProblem.SpecialPeriodsModularQuotientFibres
import Wikipedia.HopfProblem.SpecialPeriodsModularCusp

/-!
# One modular orbit above every sufficiently large j-value

The analytic cusp coordinate proves injectivity in a small q-disc. Equal
q-parameters differ by an integral translation, so high points with equal
`j` belong to the same modular orbit. Compactness of a truncated fundamental
domain then shows that every sufficiently large finite `j`-value has exactly
one orbit above it. This supplies an actual one-sheeted fibre, not an assumed
degree or a fundamental-domain classification by `j`.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped MatrixGroups Modular

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Equality of the actual q-parameters is an integral modular translation. -/
theorem modularOrbitProjection_eq_of_qParam_eq {z w : ℍ}
    (hq : Periodic.qParam 1 (z : ℂ) = Periodic.qParam 1 (w : ℂ)) :
    modularOrbitProjection z = modularOrbitProjection w := by
  obtain ⟨m, hm⟩ := Periodic.qParam_left_inv_mod_period (h := (1 : ℝ)) one_ne_zero (z : ℂ)
  obtain ⟨n, hn⟩ := Periodic.qParam_left_inv_mod_period (h := (1 : ℝ)) one_ne_zero (w : ℂ)
  have he : (z : ℂ) + (m : ℂ) = (w : ℂ) + (n : ℂ) := by
    simpa only [Complex.ofReal_one, mul_one] using
      hm.symm.trans ((congrArg (Periodic.invQParam 1) hq).trans hn)
  have htw : ModularGroup.T ^ (m - n) • z = w := by
    apply UpperHalfPlane.ext
    rw [ModularGroup.coe_T_zpow_smul_eq, Int.cast_sub]
    linear_combination he
  rw [← htw, modularOrbitProjection_smul]

/-- On a sufficiently high half-plane, equality of `j` forces equality of
modular orbits. -/
theorem modularJ_high_im_orbit_separation :
    ∃ A : ℝ, ∀ z w : ℍ, A ≤ z.im → A ≤ w.im → modularJ z = modularJ w →
      modularOrbitProjection z = modularOrbitProjection w := by
  obtain ⟨r, hr, hinj⟩ := modularJInQ_injOn_small_disc
  have hevent : {z : ℍ | Periodic.qParam 1 (z : ℂ) ∈ Metric.ball 0 r} ∈ atImInfty :=
    (qParam_tendsto_atImInfty zero_lt_one).eventually (Metric.ball_mem_nhds 0 hr)
  obtain ⟨A, hA⟩ := UpperHalfPlane.atImInfty_mem _ |>.mp hevent
  refine ⟨A, fun z w hz hw hj => modularOrbitProjection_eq_of_qParam_eq ?_⟩
  apply hinj (hA z hz) (hA w hw)
  simpa only [modularJInQ_qParam] using hj

/-- Proper control of the low part of the fundamental domain promotes
the cusp calculation to all orbits above sufficiently large values. -/
theorem modularQuotientJ_large_norm_injective :
    ∃ R : ℝ, ∀ x y : ModularOrbitSpace, R < ‖modularQuotientJ x‖ →
      modularQuotientJ x = modularQuotientJ y → x = y := by
  obtain ⟨A, hA⟩ := modularJ_high_im_orbit_separation
  have hcompact := ModularGroup.isCompact_truncatedFundamentalDomain A
  obtain ⟨R, hR⟩ := hcompact.exists_bound_of_continuousOn modularJ_continuous.continuousOn
  refine ⟨R, ?_⟩
  intro x y hx hxy
  obtain ⟨z, rfl⟩ := modularOrbitProjection_surjective x
  obtain ⟨w, rfl⟩ := modularOrbitProjection_surjective y
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  obtain ⟨δ, hδ⟩ := ModularGroup.exists_smul_mem_fd w
  have hzlarge : R < ‖modularJ (γ • z)‖ := by
    simpa only [modularJ_SL_invariant, modularQuotientJ_projection] using hx
  have hwlarge : R < ‖modularJ (δ • w)‖ := by
    simpa only [modularJ_SL_invariant, modularQuotientJ_projection, hxy] using hx
  have hzheight : A ≤ (γ • z).im := by
    by_contra h
    exact (not_lt_of_ge (hR (γ • z) ⟨hγ, (lt_of_not_ge h).le⟩)) hzlarge
  have hwheight : A ≤ (δ • w).im := by
    by_contra h
    exact (not_lt_of_ge (hR (δ • w) ⟨hδ, (lt_of_not_ge h).le⟩)) hwlarge
  have heq : modularJ (γ • z) = modularJ (δ • w) := by
    simpa only [modularJ_SL_invariant, modularQuotientJ_projection] using hxy
  simpa only [modularOrbitProjection_smul] using hA _ _ hzheight hwheight heq

/-- Every sufficiently large finite value has exactly one preimage in the
actual topological modular orbit space. -/
theorem modularQuotientJ_unique_fibre_at_large_values :
    ∃ R : ℝ, 0 < R ∧ ∀ c : ℂ, R < ‖c‖ → ∃! x : ModularOrbitSpace, modularQuotientJ x = c := by
  obtain ⟨R, hR⟩ := modularQuotientJ_large_norm_injective
  refine ⟨max R 0 + 1, by positivity, ?_⟩
  intro c hc
  obtain ⟨x, hx⟩ := modularQuotientJ_surjective c
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply hR y x
  · rw [hy]
    exact (lt_of_le_of_lt (le_max_left R 0)
      (lt_add_of_pos_right (max R 0) zero_lt_one)).trans hc
  · exact hy.trans hx.symm

end Wikipedia.HopfProblem.SpecialPeriods
