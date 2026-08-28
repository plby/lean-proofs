import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Boundary values of a disc uniformization are distinct

A noncritical analytic boundary chart determines the limit of the inverse
uniformization.  Consequently two such boundary charts with the same disc
value have the same boundary point.  The ambient space is any Hausdorff
space, so the result applies both at finite triangle vertices and at the
ideal vertex in the one-point compactification.

The chart's correspondence with actual interior points is a hypothesis:
analytic extension alone is not treated as a boundary correspondence.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannBoundary

variable {X : Type*} [TopologicalSpace X] {D : Set X}

/-- An ambient representative of the inverse disc homeomorphism.  The
irrelevant values outside the disc are set to its actual center preimage. -/
def discHomeomorphInverse (e : D ≃ₜ ball (0 : ℂ) 1) (z : ℂ) : X := by
  classical
  exact if hz : z ∈ ball (0 : ℂ) 1 then (e.symm ⟨z, hz⟩ : X)
    else (e.symm ⟨0, by simp⟩ : X)

theorem discHomeomorphInverse_of_mem (e : D ≃ₜ ball (0 : ℂ) 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    discHomeomorphInverse e z = (e.symm ⟨z, hz⟩ : X) := by
  simp only [discHomeomorphInverse, dif_pos hz]

/-- A genuine noncritical boundary coordinate supplies the one-sided
limit of the inverse uniformization, without presupposing that inverse
has already been extended to the boundary. -/
theorem tendsto_discHomeomorphInverse_of_boundary_chart
    (e : D ≃ₜ ball (0 : ℂ) 1) {f : X → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) {φ : ℂ → X} {H : ℂ → ℂ} {d : ℂ}
    (hφ : ContinuousAt φ 0) (hH : HasStrictDerivAt H d 0) (hd : d ≠ 0)
    (hcoord : ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 → φ z ∈ D ∧ f (φ z) = H z) :
    Tendsto (discHomeomorphInverse e) (𝓝[ball (0 : ℂ) 1] (H 0)) (𝓝 (φ 0)) := by
  let k := hH.localInverse H d 0 hd
  have hk0 : k (H 0) = 0 := hH.eventually_left_inverse hd |>.self_of_nhds
  have hk : Tendsto k (𝓝 (H 0)) (𝓝 (0 : ℂ)) := by
    have ht : Tendsto k (𝓝 (H 0)) (𝓝 (k (H 0))) :=
      (hH.to_localInverse hd).hasDerivAt.continuousAt.tendsto
    rwa [hk0] at ht
  have ht : Tendsto (φ ∘ k) (𝓝[ball (0 : ℂ) 1] (H 0)) (𝓝 (φ 0)) :=
    (hφ.tendsto.comp hk).mono_left nhdsWithin_le_nhds
  have heq : discHomeomorphInverse e =ᶠ[𝓝[ball (0 : ℂ) 1] (H 0)] φ ∘ k := by
    have hright : ∀ᶠ y in 𝓝[ball (0 : ℂ) 1] (H 0), H (k y) = y :=
      (hH.eventually_right_inverse hd).filter_mono nhdsWithin_le_nhds
    have hparam : ∀ᶠ y in 𝓝[ball (0 : ℂ) 1] (H 0),
        ‖H (k y)‖ < 1 → φ (k y) ∈ D ∧ f (φ (k y)) = H (k y) :=
      (hk.eventually hcoord).filter_mono nhdsWithin_le_nhds
    filter_upwards [hright, hparam, self_mem_nhdsWithin] with y hy hcy hyD
    have hyn : ‖y‖ < 1 := by simpa using hyD
    obtain ⟨hmem, hval⟩ := hcy (by simpa only [hy] using hyn)
    have himage : e ⟨φ (k y), hmem⟩ = ⟨y, hyD⟩ := by
      apply Subtype.ext
      exact (he ⟨φ (k y), hmem⟩).symm.trans (hval.trans hy)
    rw [discHomeomorphInverse_of_mem e hyD]
    change (e.symm ⟨y, hyD⟩ : X) = φ (k y)
    have hinv : e.symm ⟨y, hyD⟩ = ⟨φ (k y), hmem⟩ := by
      rw [← himage, e.symm_apply_apply]
    exact congrArg Subtype.val hinv
  exact ht.congr' heq.symm

theorem unitCircle_mem_closure_unitBall {w : ℂ} (hw : ‖w‖ = 1) :
    w ∈ closure (ball (0 : ℂ) 1) := by
  rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
  simpa only [mem_closedBall, dist_zero_right, hw] using le_rfl (a := (1 : ℝ))

/-- Boundary values cannot be identified by a disc uniformization once
the actual noncritical one-sided boundary charts are established. -/
theorem boundary_points_eq_of_equal_disc_values [T2Space X]
    (e : D ≃ₜ ball (0 : ℂ) 1) {f : X → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ))
    {φ ψ : ℂ → X} {F G : ℂ → ℂ} {dF dG : ℂ}
    (hφ : ContinuousAt φ 0) (hψ : ContinuousAt ψ 0)
    (hF : HasStrictDerivAt F dF 0) (hdF : dF ≠ 0)
    (hG : HasStrictDerivAt G dG 0) (hdG : dG ≠ 0)
    (hcoordF : ∀ᶠ z in 𝓝 (0 : ℂ), ‖F z‖ < 1 → φ z ∈ D ∧ f (φ z) = F z)
    (hcoordG : ∀ᶠ z in 𝓝 (0 : ℂ), ‖G z‖ < 1 → ψ z ∈ D ∧ f (ψ z) = G z)
    (hcircle : ‖F 0‖ = 1) (hvalue : F 0 = G 0) :
    φ 0 = ψ 0 := by
  have : NeBot (𝓝[ball (0 : ℂ) 1] (F 0)) :=
    (mem_closure_iff_nhdsWithin_neBot).mp (unitCircle_mem_closure_unitBall hcircle)
  have htF := tendsto_discHomeomorphInverse_of_boundary_chart e he hφ hF hdF hcoordF
  have htG := tendsto_discHomeomorphInverse_of_boundary_chart e he hψ hG hdG hcoordG
  rw [← hvalue] at htG
  exact tendsto_nhds_unique htF htG

end Wikipedia.HopfProblem.RiemannBoundary
