import Wikipedia.HopfProblem.DegreeCollapseNativeBeltArc

/-!
# The native belt arc has injective derivative

Its original negative coordinate has derivative rho times the prescribed
unit vector. This proves model immersion without any calculation of the
positive square-root derivative. The inverse native chart has a bijective
derivative, so immersion holds throughout the actual local arc.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

section Model

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem fderiv_beltPassage_upper_fst (ρ s w : ℝ) (u : N) (v : P) :
    (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s w).1 = (ρ * w) • u := by
  have hfirst : HasDerivAt (fun t : ℝ => (BeltPassage.upper ρ t u v).1) (ρ • u) s := by
    simpa only [BeltPassage.upper, id_eq, mul_one] using
      ((hasDerivAt_id s).const_mul ρ).smul_const u
  have hchain : fderiv ℝ (fun t => (BeltPassage.upper ρ t u v).1) s =
      (ContinuousLinearMap.fst ℝ N P).comp (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s) := by
    have hh := fderiv_comp s (ContinuousLinearMap.fst ℝ N P).differentiableAt
      ((BeltPassage.contDiff_upper ρ u v).differentiable (by simp) s)
    rw [(ContinuousLinearMap.fst ℝ N P).fderiv] at hh
    exact hh
  have hh := congrArg (fun L : ℝ →L[ℝ] N => L w) hchain
  rw [hfirst.hasFDerivAt.fderiv] at hh
  change w • (ρ • u) = (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s w).1 at hh
  rw [smul_smul, mul_comm w ρ] at hh
  exact hh.symm

theorem injective_fderiv_beltPassage_upper {ρ : ℝ} (hρ : ρ ≠ 0) (s : ℝ)
    {u : N} (hu : u ≠ 0) (v : P) :
    Injective (fderiv ℝ (fun t => BeltPassage.upper ρ t u v) s) := by
  intro a b hab
  have hh := congrArg Prod.fst hab
  rw [fderiv_beltPassage_upper_fst, fderiv_beltPassage_upper_fst] at hh
  exact mul_left_cancel₀ hρ (smul_left_injective ℝ hu hh)

end Model

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

open Classical in
theorem nativeBeltArc_derivative_injective
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) {s : ℝ} (hs : |s| ≤ 1) :
    Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (nativeBeltArc S q u v) s) := by
  have ht := nativeBeltArc_coordinates_mem_target S q u v hs
  have hu : u.val ≠ 0 := by
    intro h
    have hn := mem_sphere_zero_iff_norm.mp u.property
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  change Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
    ((S.data q).chart.splitChart.symm ∘ (fun t => BeltPassage.upper (S.data q).radius t u.val v.val)) s)
  rw [mfderiv_comp s ((S.data q).chart.splitChart.symm.mdifferentiableAt (by simp) ht)
    ((BeltPassage.contDiff_upper (S.data q).radius u.val v.val).contMDiff.mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv]
  exact (PartialChart.bijective_mfderiv (S.data q).chart.splitChart.symm ht).injective.comp
    (injective_fderiv_beltPassage_upper (S.data q).radius_pos.ne' s hu v.val)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
