import Wikipedia.HopfProblem.HolomorphicCousinAnnulus
import Wikipedia.HopfProblem.HolomorphicCousinDivision
import Wikipedia.HopfProblem.HolomorphicCousinGlobal
import Wikipedia.HopfProblem.HolomorphicCousinTransform
import Wikipedia.HopfProblem.HolomorphicCousinUniqueness

/-!
# Constructive additive Cousin solvers

The two boundary Cauchy integrals give a holomorphic splitting on the finite
disc and on the disc about infinity.  The latter summand vanishes at infinity,
so this normalized splitting is unique.  Dividing it by the coordinate at
infinity gives the corresponding existence and uniqueness result for the
transition function of `O(-1)`.

The imported global solver also starts from actual holomorphic local
cocycles on an arbitrary open cover of the finite plane with a distinguished
patch at infinity.  A relative smooth partition of unity and the proved
Cauchy--Green integral solve the global problem, without assuming a section
on a whole affine patch.  The global `O` solutions differ by one constant,
and the `O(-1)` solution is unique.

No vanishing of sheaf cohomology or existence of the special period functions
is assumed.  Applying these solvers to the source's particular period torsors
is a separate step.
-/

noncomputable section

open Complex Metric Set

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The finite-chart term is the Cauchy integral over the outer circle. -/
def interiorPart (h : ℂ → ℂ) (b : ℝ) : ℂ → ℂ := cauchyTransform h b

/-- The exterior term is minus the Cauchy integral over the inner circle. -/
def exteriorPart (h : ℂ → ℂ) (a : ℝ) (z : ℂ) : ℂ := -cauchyTransform h a z

/-- The exterior term in the holomorphic coordinate `u = 1/z` at infinity. -/
def exteriorAtInfinity (h : ℂ → ℂ) (a : ℝ) (u : ℂ) : ℂ := -infinityKernel h a u

@[simp] theorem exteriorAtInfinity_zero (h : ℂ → ℂ) (a : ℝ) :
    exteriorAtInfinity h a 0 = 0 := by simp [exteriorAtInfinity]

theorem exteriorAtInfinity_inv (h : ℂ → ℂ) (a : ℝ) {z : ℂ} (hz : z ≠ 0) :
    exteriorAtInfinity h a z⁻¹ = exteriorPart h a z := by
  simp only [exteriorAtInfinity, exteriorPart, infinityKernel_inv h a hz]

theorem interiorPart_analytic {h : ℂ → ℂ} {b : ℝ} (hb : 0 < b)
    (hh : ContinuousOn h (sphere 0 b)) :
    AnalyticOnNhd ℂ (interiorPart h b) (ball 0 b) :=
  cauchyTransform_analyticOnNhd_interior hb (hh.circleIntegrable hb.le)

theorem exteriorPart_analytic {h : ℂ → ℂ} {a : ℝ} (ha : 0 < a)
    (hh : ContinuousOn h (sphere 0 a)) :
    AnalyticOnNhd ℂ (exteriorPart h a) {z | a < ‖z‖} :=
  (cauchyTransform_analyticOnNhd_exterior ha hh).neg

theorem exteriorAtInfinity_analytic {h : ℂ → ℂ} {a : ℝ} (ha : 0 < a)
    (hh : ContinuousOn h (sphere 0 a)) :
    AnalyticOnNhd ℂ (exteriorAtInfinity h a) (ball 0 a⁻¹) :=
  (analyticOnNhd_infinityKernel ha hh).neg

/-- A normalized solution on the two actual coordinate discs. -/
structure NormalizedSplitting (h : ℂ → ℂ) (a b : ℝ) where
  /-- The finite-coordinate function. -/
  finitePart : ℂ → ℂ
  /-- The function in the reciprocal coordinate. -/
  infinityPart : ℂ → ℂ
  finite_analytic : AnalyticOnNhd ℂ finitePart (ball 0 b)
  infinity_analytic : AnalyticOnNhd ℂ infinityPart (ball 0 a⁻¹)
  infinity_zero : infinityPart 0 = 0
  equation : ∀ z ∈ annulus a b, finitePart z + infinityPart z⁻¹ = h z

private theorem sphere_outer_subset {a b : ℝ} (hab : a ≤ b) :
    sphere (0 : ℂ) b ⊆ closedBall 0 b \ ball 0 a := by
  intro z hz
  have hzn : ‖z‖ = b := by simpa only [mem_sphere, dist_zero_right] using hz
  simp only [Set.mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt]
  exact ⟨hzn.le, hzn.symm ▸ hab⟩

private theorem sphere_inner_subset {a b : ℝ} (hab : a ≤ b) :
    sphere (0 : ℂ) a ⊆ closedBall 0 b \ ball 0 a := by
  intro z hz
  have hzn : ‖z‖ = a := by simpa only [mem_sphere, dist_zero_right] using hz
  simp only [Set.mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt]
  exact ⟨hzn.trans_le hab, hzn.ge⟩

/-- The solution is constructed by the actual two Cauchy integrals. -/
def cauchySplitting {h : ℂ → ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hh : AnalyticOnNhd ℂ h (closedBall 0 b \ ball 0 a)) :
    NormalizedSplitting h a b where
  finitePart := interiorPart h b
  infinityPart := exteriorAtInfinity h a
  finite_analytic := interiorPart_analytic (ha.trans hab)
    (hh.continuousOn.mono (sphere_outer_subset hab.le))
  infinity_analytic := exteriorAtInfinity_analytic ha
    (hh.continuousOn.mono (sphere_inner_subset hab.le))
  infinity_zero := exteriorAtInfinity_zero h a
  equation := by
    intro z hz
    have hz₀ : z ≠ 0 := norm_pos_iff.mp (ha.trans hz.1)
    rw [exteriorAtInfinity_inv h a hz₀]
    exact normalized_circleIntegral_sub ha hab hh hz

/-- **Additive Cousin splitting on an annulus.** A holomorphic function on
the original annulus splits on any smaller annulus with positive inner radius;
the two summands extend respectively across zero and across infinity. -/
theorem exists_normalized_splitting {h : ℂ → ℂ} {r a b R : ℝ}
    (ha : 0 < a) (hra : r < a) (hab : a < b) (hbR : b < R)
    (hh : AnalyticOnNhd ℂ h (annulus r R)) :
    Nonempty (NormalizedSplitting h a b) :=
  ⟨cauchySplitting ha hab (hh.mono (closedAnnulus_subset_annulus hra hbR))⟩

/-- The normalized pair is unique on its coordinate domains; values assigned
outside those domains are deliberately irrelevant. -/
theorem NormalizedSplitting.unique {h : ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (s t : NormalizedSplitting h a b) :
    EqOn s.finitePart t.finitePart (ball 0 b) ∧
      EqOn s.infinityPart t.infinityPart (ball 0 a⁻¹) :=
  normalized_splitting_unique ha hab s.finite_analytic t.finite_analytic
    s.infinity_analytic t.infinity_analytic s.equation t.equation
    s.infinity_zero t.infinity_zero

/-- Without the normalization at infinity the set of solutions has exactly
one complex constant of freedom. -/
theorem NormalizedSplitting.classify {h : ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (s : NormalizedSplitting h a b)
    {f G : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 b))
    (hG : AnalyticOnNhd ℂ G (ball 0 a⁻¹))
    (heq : ∀ z ∈ annulus a b, f z + G z⁻¹ = h z) :
    EqOn f (fun z => s.finitePart z - G 0) (ball 0 b) ∧
      EqOn G (fun u => s.infinityPart u + G 0) (ball 0 a⁻¹) := by
  have he : ∀ z ∈ annulus a b,
      s.finitePart z - f z = G z⁻¹ - s.infinityPart z⁻¹ := by
    intro z hz
    exact sub_eq_sub_iff_add_eq_add.mpr
      (((s.equation z hz).trans (heq z hz).symm).trans (add_comm _ _))
  obtain ⟨hfinite, hinfty⟩ := eq_const_of_two_chart_agreement ha hab
    (s.finite_analytic.sub hf) (hG.sub s.infinity_analytic) he
  constructor
  · intro z hz
    have hz' : s.finitePart z - f z = G 0 := by
      simpa only [Pi.sub_apply, s.infinity_zero, sub_zero] using hfinite hz
    calc
      f z = s.finitePart z - (s.finitePart z - f z) := (sub_sub_cancel _ _).symm
      _ = s.finitePart z - G 0 := by rw [hz']
  · intro u hu
    have hu' : G u - s.infinityPart u = G 0 := by
      simpa only [Pi.sub_apply, s.infinity_zero, sub_zero] using hinfty hu
    exact (sub_eq_iff_eq_add.mp hu').trans (add_comm _ _)

/-- The same solution in the ordinary exterior coordinate. -/
theorem additive_cousin_split {h : ℂ → ℂ} {r a b R : ℝ}
    (ha : 0 < a) (hra : r < a) (hab : a < b) (hbR : b < R)
    (hh : AnalyticOnNhd ℂ h (annulus r R)) :
    AnalyticOnNhd ℂ (interiorPart h b) (ball 0 b) ∧
      AnalyticOnNhd ℂ (exteriorPart h a) {z | a < ‖z‖} ∧
      AnalyticOnNhd ℂ (exteriorAtInfinity h a) (ball 0 a⁻¹) ∧
      exteriorAtInfinity h a 0 = 0 ∧
      (∀ z, a < ‖z‖ → exteriorAtInfinity h a z⁻¹ = exteriorPart h a z) ∧
      ∀ z ∈ annulus a b, interiorPart h b z + exteriorPart h a z = h z := by
  have hhA := continuousOn_sphere_of_analyticOnNhd_annulus hh hra (hab.trans hbR)
  have hhB := continuousOn_sphere_of_analyticOnNhd_annulus hh (hra.trans hab) hbR
  refine ⟨interiorPart_analytic (ha.trans hab) hhB, exteriorPart_analytic ha hhA,
    exteriorAtInfinity_analytic ha hhA, exteriorAtInfinity_zero h a,
    fun z hz => exteriorAtInfinity_inv h a (norm_pos_iff.mp (ha.trans hz)), ?_⟩
  intro z hz
  exact normalized_circleIntegral_sub ha hab
    (hh.mono (closedAnnulus_subset_annulus hra hbR)) hz

/-- A solution for the `O(-1)` transition: the second summand acquires the
factor `z⁻¹`, and no normalization of its value at infinity is needed. -/
structure NegativeOneSplitting (h : ℂ → ℂ) (a b : ℝ) where
  finitePart : ℂ → ℂ
  infinityPart : ℂ → ℂ
  finite_analytic : AnalyticOnNhd ℂ finitePart (ball 0 b)
  infinity_analytic : AnalyticOnNhd ℂ infinityPart (ball 0 a⁻¹)
  equation : ∀ z ∈ annulus a b, finitePart z + z⁻¹ * infinityPart z⁻¹ = h z

/-- Factoring the vanishing exterior function gives the negative-one twist. -/
def NormalizedSplitting.negativeOne {h : ℂ → ℂ} {a b : ℝ} (ha : 0 < a)
    (s : NormalizedSplitting h a b) : NegativeOneSplitting h a b where
  finitePart := s.finitePart
  infinityPart := dslope s.infinityPart 0
  finite_analytic := s.finite_analytic
  infinity_analytic := analyticOnNhd_dslope_zero (inv_pos.mpr ha) s.infinity_analytic
  equation := by
    intro z hz
    rw [zero_mul_dslope s.infinity_zero]
    exact s.equation z hz

/-- The `O(-1)` additive Cousin problem has a solution on the two discs. -/
theorem exists_negativeOne_splitting {h : ℂ → ℂ} {r a b R : ℝ}
    (ha : 0 < a) (hra : r < a) (hab : a < b) (hbR : b < R)
    (hh : AnalyticOnNhd ℂ h (annulus r R)) :
    Nonempty (NegativeOneSplitting h a b) := by
  obtain ⟨s⟩ := exists_normalized_splitting ha hra hab hbR hh
  exact ⟨s.negativeOne ha⟩

/-- The `O(-1)` solution is unique, without a constant ambiguity. -/
theorem NegativeOneSplitting.unique {h : ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (s t : NegativeOneSplitting h a b) :
    EqOn s.finitePart t.finitePart (ball 0 b) ∧
      EqOn s.infinityPart t.infinityPart (ball 0 a⁻¹) := by
  have heq : ∀ z ∈ annulus a b,
      s.finitePart z - t.finitePart z = z⁻¹ ^ 1 * (t.infinityPart z⁻¹ - s.infinityPart z⁻¹) := by
    intro z hz
    have he := (s.equation z hz).trans (t.equation z hz).symm
    rw [pow_one, mul_sub]
    exact sub_eq_sub_iff_add_eq_add.mpr (he.trans (add_comm _ _))
  obtain ⟨hfinite, hinfty⟩ := negative_twist_eq_zero ha hab (by decide : 0 < 1)
    (s.finite_analytic.sub t.finite_analytic)
    (t.infinity_analytic.sub s.infinity_analytic) heq
  constructor
  · intro z hz
    exact sub_eq_zero.mp (hfinite hz)
  · intro z hz
    exact (sub_eq_zero.mp (hinfty hz)).symm

end Wikipedia.HopfProblem.HolomorphicCousin
