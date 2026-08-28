import Wikipedia.SmoothSixDPoincare.SmallDerivativeGerm

/-!
# Linearizing a transverse coordinate germ without adding intersections

If the actual first derivative maps the first coordinate plane transversely
to the second, the projected block is invertible. Divide by that block:
the projected nonlinear germ is tangent to identity. Its error has an
arbitrarily small Lipschitz bound on a constructed ball. Consequently
every pointwise convex blend with the actual linear derivative still
meets the opposite coordinate plane only at zero on that ball.
-/

noncomputable section

open Set Function Filter Metric
open scoped Topology ContDiff NNReal
open Wikipedia.SmoothSixDPoincare.SmallPerturbation

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- A bounded scalar multiple of a flat displacement is still flat. The
scalar need not be differentiable or even continuous. -/
theorem hasFDerivAt_scalar_displacement {f g : A → A} (hfzero : f 0 = 0)
    (hf : HasFDerivAt f (ContinuousLinearMap.id ℝ A) 0)
    (hscalar : ∀ x, ∃ α ∈ Icc (0 : ℝ) 1, g x = x + α • (f x - x)) :
    HasFDerivAt g (ContinuousLinearMap.id ℝ A) 0 := by
  have hgzero : g 0 = 0 := by
    obtain ⟨α, -, he⟩ := hscalar 0
    simpa only [hfzero, sub_self, smul_zero, add_zero] using he
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  filter_upwards [hf.isLittleO.bound hε] with x hx
  simp only [hfzero, hgzero, sub_zero, ContinuousLinearMap.id_apply] at hx ⊢
  obtain ⟨α, hα, he⟩ := hscalar x
  rw [he, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα.1]
  exact (mul_le_of_le_one_left (norm_nonneg _) hα.2).trans hx

/-- Construct one open neighborhood on which all convex linearization
blends retain the unique transverse-plane intersection. -/
theorem exists_open_transverse_convex_blend {φ : (A × B) → (A × B)} {U : Set (A × B)}
    (hU : IsOpen U) (hzero : (0 : A × B) ∈ U) (hφ : ContDiffOn ℝ ∞ φ U)
    (hφzero : φ 0 = 0) (L : (A × B) →L[ℝ] (A × B)) (hder : fderiv ℝ φ 0 = L)
    (P : A ≃L[ℝ] A) (hP : ∀ x : A, (L (x, 0)).1 = P x) :
    ∃ W : Set (A × B), IsOpen W ∧ (0 : A × B) ∈ W ∧ W ⊆ U ∧
      ∀ x : A, (x, (0 : B)) ∈ W → ∀ α ∈ Icc (0 : ℝ) 1,
        (φ (x, 0) + α • (L (x, 0) - φ (x, 0))).1 = 0 ↔ x = 0 := by
  let ι := ContinuousLinearMap.inl ℝ A B
  let π := ContinuousLinearMap.fst ℝ A B
  let H : A → A := fun x => P.symm ((φ (x, 0)).1)
  let S : Set A := ι ⁻¹' U
  have hS : IsOpen S := hU.preimage ι.continuous
  have hSzero : (0 : A) ∈ S := hzero
  have hH : ContDiffOn ℝ ∞ H S := P.symm.contDiff.comp_contDiffOn
    (π.contDiff.comp_contDiffOn (hφ.comp ι.contDiff.contDiffOn (fun x hx => hx)))
  have hfd : HasFDerivAt φ L 0 := by
    rw [← hder]
    exact ((hφ.contDiffAt (hU.mem_nhds hzero)).differentiableAt (by simp)).hasFDerivAt
  have hHd : HasFDerivAt H (P.symm.toContinuousLinearMap.comp (π.comp (L.comp ι))) 0 :=
    P.symm.toContinuousLinearMap.hasFDerivAt.comp (0 : A)
      (π.hasFDerivAt.comp (0 : A) (hfd.comp (f := ι) (0 : A) ι.hasFDerivAt))
  have hlinear : P.symm.toContinuousLinearMap.comp (π.comp (L.comp ι)) =
      ContinuousLinearMap.id ℝ A := by
    apply ContinuousLinearMap.ext
    intro x
    change P.symm ((L (x, 0)).1) = x
    rw [hP, P.symm_apply_apply]
  rw [hlinear] at hHd
  let u : A → A := fun x => H x - x
  have hu : ContDiffOn ℝ ∞ u S := hH.sub contDiffOn_id
  have hu0 : u 0 = 0 := by
    change P.symm ((φ (0 : A × B)).1) - 0 = 0
    rw [hφzero]
    simp
  have hdu : fderiv ℝ u 0 = 0 := by
    have hh := hHd.sub (hasFDerivAt_id (0 : A))
    change fderiv ℝ (H - id) 0 = 0
    simpa only [sub_self] using hh.fderiv
  obtain ⟨ρ, hρ, -, hlip⟩ :=
    exists_closedBall_small_lipschitz_of_fderiv_zero
      hS hSzero hu hdu (show (0 : ℝ≥0) < 1 / 2 by norm_num)
  let W := U ∩ ball (0 : A × B) ρ
  refine ⟨W, hU.inter isOpen_ball, ⟨hzero, mem_ball_self hρ⟩, inter_subset_left, ?_⟩
  intro x hx α hα
  have hxρ : x ∈ closedBall (0 : A) ρ := by
    have hh := mem_ball_zero_iff.mp hx.2
    apply mem_closedBall_zero_iff.mpr
    simpa only [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg x)] using hh.le
  have h0ρ : (0 : A) ∈ closedBall (0 : A) ρ := mem_closedBall_self hρ.le
  have herr : ‖u x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := by
    have hh := hlip.dist_le_mul x hxρ 0 h0ρ
    simpa only [hu0, dist_zero_right, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh
  constructor
  · intro hz
    have he : x + (1 - α) • u x = 0 := by
      have hh := congrArg P.symm hz
      change P.symm ((φ (x, 0)).1 + α • ((L (x, 0)).1 - (φ (x, 0)).1)) = P.symm 0 at hh
      simp only [map_add, map_smul, map_sub, hP, P.symm_apply_apply, map_zero] at hh
      change H x + α • (x - H x) = 0 at hh
      calc
        x + (1 - α) • u x = H x + α • (x - H x) := by dsimp [u]; module
        _ = 0 := hh
    have he' : x = -((1 - α) • u x) := eq_neg_of_add_eq_zero_left he
    have hnorm : ‖x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := calc
      ‖x‖ = ‖-((1 - α) • u x)‖ := congrArg norm he'
      _ = ‖(1 - α) • u x‖ := norm_neg _
      _ = (1 - α) * ‖u x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hα.2])]
      _ ≤ ‖u x‖ := mul_le_of_le_one_left (norm_nonneg _) (by linarith [hα.1])
      _ ≤ (1 / 2 : ℝ) * ‖x‖ := herr
    exact norm_eq_zero.mp (le_antisymm (by linarith [norm_nonneg x]) (norm_nonneg x))
  · rintro rfl
    simp only [show ((0 : A), (0 : B)) = (0 : A × B) from rfl, hφzero, map_zero,
      sub_self, smul_zero, add_zero, Prod.fst_zero]

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
