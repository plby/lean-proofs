import Wikipedia.HopfProblem.HolomorphicCousinCocyclePotential
import Wikipedia.HopfProblem.HolomorphicCousinCorrection
import Wikipedia.HopfProblem.HolomorphicCousinGlobalUniqueness

/-!
# Global additive Cousin solutions from local cocycles

An arbitrary open cover of the complex plane is allowed.  One distinguished
member contains a neighborhood of infinity.  A holomorphic additive cocycle
on this cover gives an actual smooth local cochain by a relative partition of
unity, a globally defined compactly supported forcing term, and its explicit
Cauchy--Green correction.  The result is a holomorphic local cochain with the
original transition functions, including a proved holomorphic extension at
infinity in the distinguished patch.

This is the chart-level global vanishing argument needed for `O` and `O(-1)`.
In particular, no holomorphic section over an entire affine chart is part of
the input.  For `O(-1)`, local functions are expressed in the finite-coordinate
frame; the factor `z⁻¹` is the change to the frame at infinity.
-/

noncomputable section

open Complex Metric Set
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCousin

variable {ι : Type*}

/-- A normalized holomorphic solution of an actual local additive cocycle. -/
structure NormalizedCocycleSolution (U : ι → Set ℂ) (h : ι → ι → ℂ → ℂ)
    (i₀ : ι) (R : ℝ) where
  localPart : ι → ℂ → ℂ
  infinityPart : ℂ → ℂ
  local_analytic : ∀ i, AnalyticOnNhd ℂ (localPart i) (U i)
  infinity_analytic : AnalyticOnNhd ℂ infinityPart (ball 0 R⁻¹)
  infinity_zero : infinityPart 0 = 0
  equation : ∀ i j z, z ∈ U i → z ∈ U j → localPart i z - localPart j z = h i j z
  atInfinity : ∀ z, R < ‖z‖ → localPart i₀ z = infinityPart z⁻¹

/-- **Global additive Cousin existence.** Holomorphic local cocycles admit
holomorphic local primitives; the primitive in the distinguished infinity
patch has an analytic extension with value zero at infinity. -/
theorem exists_normalized_holomorphic_cocycle_solution {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i)
    {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k →
      h i j z + h j k z = h i k z)
    (i₀ : ι) {R : ℝ} (hR : 0 < R) (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    Nonempty (NormalizedCocycleSolution U h i₀ R) := by
  obtain ⟨P, hPU, htrans, ⟨V, _, hRV, _, hs0, _⟩, hsupport, hcompact⟩ :=
    exists_normalized_cocycle_localPotential hU hcover hh hc i₀ R hRU
  have hbound : ∀ z ∈ Function.support P.forcing, ‖z‖ ≤ R := by
    intro z hz
    have hzR := hsupport (subset_tsupport P.forcing hz)
    exact (show ‖z‖ < R by simpa only [mem_ball, dist_zero_right] using hzR).le
  refine ⟨{
    localPart := P.correctedPart
    infinityPart := P.correctedInfinity
    local_analytic := ?_
    infinity_analytic := P.correctedInfinity_analytic hcompact hR hbound
    infinity_zero := P.correctedInfinity_zero
    equation := ?_
    atInfinity := ?_ }⟩
  · intro i
    simpa only [hPU] using P.correctedPart_analytic hcompact i
  · intro i j z hi hj
    exact (P.correctedPart_sub i j z).trans (htrans i j z hi hj)
  · intro z hz
    apply P.correctedPart_eq_infinity (norm_pos_iff.mp (hR.trans hz))
    apply hs0
    apply hRV
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hz.le

/-- A solution whose infinity coefficient uses the transition factor for
`O(-1)`.  The local coefficients are all in the finite-coordinate frame. -/
structure NegativeOneCocycleSolution (U : ι → Set ℂ) (h : ι → ι → ℂ → ℂ)
    (i₀ : ι) (R : ℝ) where
  localPart : ι → ℂ → ℂ
  infinityPart : ℂ → ℂ
  local_analytic : ∀ i, AnalyticOnNhd ℂ (localPart i) (U i)
  infinity_analytic : AnalyticOnNhd ℂ infinityPart (ball 0 R⁻¹)
  equation : ∀ i j z, z ∈ U i → z ∈ U j → localPart i z - localPart j z = h i j z
  atInfinity : ∀ z, R < ‖z‖ → localPart i₀ z = z⁻¹ * infinityPart z⁻¹

/-- The proved zero at infinity makes the coordinate division removable. -/
def NormalizedCocycleSolution.negativeOne {U : ι → Set ℂ} {h : ι → ι → ℂ → ℂ}
    {i₀ : ι} {R : ℝ} (hR : 0 < R) (s : NormalizedCocycleSolution U h i₀ R) :
    NegativeOneCocycleSolution U h i₀ R where
  localPart := s.localPart
  infinityPart := dslope s.infinityPart 0
  local_analytic := s.local_analytic
  infinity_analytic := analyticOnNhd_dslope_zero (inv_pos.mpr hR) s.infinity_analytic
  equation := s.equation
  atInfinity := by
    intro z hz
    rw [s.atInfinity z hz]
    exact (zero_mul_dslope s.infinity_zero z⁻¹).symm

/-- **Global `O(-1)` Cousin existence**, constructed from the original local
cocycle and without an affine-patch triviality assumption. -/
theorem exists_negativeOne_holomorphic_cocycle_solution {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i)
    {h : ι → ι → ℂ → ℂ}
    (hh : ∀ i j, AnalyticOnNhd ℂ (h i j) (U i ∩ U j))
    (hc : ∀ i j k z, z ∈ U i → z ∈ U j → z ∈ U k →
      h i j z + h j k z = h i k z)
    (i₀ : ι) {R : ℝ} (hR : 0 < R) (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀) :
    Nonempty (NegativeOneCocycleSolution U h i₀ R) := by
  obtain ⟨s⟩ := exists_normalized_holomorphic_cocycle_solution hU hcover hh hc i₀ hR hRU
  exact ⟨s.negativeOne hR⟩

/-- The normalized global solution is unique on every local chart and on the
actual inverse-coordinate disc. -/
theorem NormalizedCocycleSolution.unique {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i)
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ} (hR : 0 < R)
    (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀) (s t : NormalizedCocycleSolution U h i₀ R) :
    (∀ i, EqOn (s.localPart i) (t.localPart i) (U i)) ∧
      EqOn s.infinityPart t.infinityPart (ball 0 R⁻¹) := by
  have hcompat : ∀ i j, EqOn (fun z => s.localPart i z - t.localPart i z)
      (fun z => s.localPart j z - t.localPart j z) (U i ∩ U j) := by
    intro i j z hz
    linear_combination (s.equation i j z hz.1 hz.2) - (t.equation i j z hz.1 hz.2)
  have htail : ∀ z : ℂ, R < ‖z‖ → z ∈ U i₀ := by
    intro z hz
    apply hRU
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hz.le
  obtain ⟨hfinite, hinfty⟩ := eq_const_of_open_cover_agreement hU hcover
    (fun i => (s.local_analytic i).sub (t.local_analytic i)) hcompat hR htail
    (s.infinity_analytic.sub t.infinity_analytic)
    (fun z hz => congrArg₂ (· - ·) (s.atInfinity z hz) (t.atInfinity z hz))
  constructor
  · intro i z hz
    have he := hfinite i hz
    simpa only [Pi.sub_apply, s.infinity_zero, t.infinity_zero, sub_zero, sub_eq_zero] using he
  · intro u hu
    have he := hinfty hu
    simpa only [Pi.sub_apply, s.infinity_zero, t.infinity_zero, sub_zero, sub_eq_zero] using he

/-- Without normalization, the only ambiguity is addition of one common
complex constant to every local representative and to the infinity chart. -/
theorem NormalizedCocycleSolution.classify {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i)
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ} (hR : 0 < R)
    (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀) (s : NormalizedCocycleSolution U h i₀ R)
    {f : ι → ℂ → ℂ} {G : ℂ → ℂ}
    (hf : ∀ i, AnalyticOnNhd ℂ (f i) (U i))
    (hG : AnalyticOnNhd ℂ G (ball 0 R⁻¹))
    (heq : ∀ i j z, z ∈ U i → z ∈ U j → f i z - f j z = h i j z)
    (hinfty : ∀ z, R < ‖z‖ → f i₀ z = G z⁻¹) :
    (∀ i, EqOn (f i) (fun z => s.localPart i z + G 0) (U i)) ∧
      EqOn G (fun u => s.infinityPart u + G 0) (ball 0 R⁻¹) := by
  have hcompat : ∀ i j, EqOn (fun z => f i z - s.localPart i z)
      (fun z => f j z - s.localPart j z) (U i ∩ U j) := by
    intro i j z hz
    linear_combination (heq i j z hz.1 hz.2) - (s.equation i j z hz.1 hz.2)
  have htail : ∀ z : ℂ, R < ‖z‖ → z ∈ U i₀ := by
    intro z hz
    apply hRU
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hz.le
  obtain ⟨hfinite, hinfty⟩ := eq_const_of_open_cover_agreement hU hcover
    (fun i => (hf i).sub (s.local_analytic i)) hcompat hR htail
    (hG.sub s.infinity_analytic)
    (fun z hz => congrArg₂ (· - ·) (hinfty z hz) (s.atInfinity z hz))
  constructor
  · intro i z hz
    have he : f i z - s.localPart i z = G 0 := by
      simpa only [Pi.sub_apply, s.infinity_zero, sub_zero] using hfinite i hz
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  · intro u hu
    have he : G u - s.infinityPart u = G 0 := by
      simpa only [Pi.sub_apply, s.infinity_zero, sub_zero] using hinfty hu
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

/-- The negative-one transition has no constant ambiguity: its global
solution is unique without any prescribed value in the infinity frame. -/
theorem NegativeOneCocycleSolution.unique {U : ι → Set ℂ}
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ z, ∃ i, z ∈ U i)
    {h : ι → ι → ℂ → ℂ} {i₀ : ι} {R : ℝ} (hR : 0 < R)
    (hRU : (ball (0 : ℂ) R)ᶜ ⊆ U i₀) (s t : NegativeOneCocycleSolution U h i₀ R) :
    (∀ i, EqOn (s.localPart i) (t.localPart i) (U i)) ∧
      EqOn s.infinityPart t.infinityPart (ball 0 R⁻¹) := by
  have hcompat : ∀ i j, EqOn (fun z => s.localPart i z - t.localPart i z)
      (fun z => s.localPart j z - t.localPart j z) (U i ∩ U j) := by
    intro i j z hz
    linear_combination (s.equation i j z hz.1 hz.2) - (t.equation i j z hz.1 hz.2)
  have htail : ∀ z : ℂ, R < ‖z‖ → z ∈ U i₀ := by
    intro z hz
    apply hRU
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hz.le
  have hinfty : ∀ z : ℂ, R < ‖z‖ → s.localPart i₀ z - t.localPart i₀ z =
      z⁻¹ ^ 1 * (s.infinityPart z⁻¹ - t.infinityPart z⁻¹) := by
    intro z hz
    rw [s.atInfinity z hz, t.atInfinity z hz, pow_one, mul_sub]
  obtain ⟨hfinite, hinfty⟩ := negative_twist_eq_zero_of_open_cover hU hcover
    (fun i => (s.local_analytic i).sub (t.local_analytic i)) hcompat hR htail
    (by decide : 0 < 1) (s.infinity_analytic.sub t.infinity_analytic) hinfty
  exact ⟨fun i z hz => sub_eq_zero.mp (hfinite i hz),
    fun u hu => sub_eq_zero.mp (hinfty hu)⟩

end Wikipedia.HopfProblem.HolomorphicCousin
