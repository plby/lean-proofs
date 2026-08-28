import Wikipedia.SmoothSixDPoincare.LocalCurveEndpointGerms
import Wikipedia.SmoothSixDPoincare.CenteredParametrization

/-!
# Connecting arcs agreeing with native corner boundary arcs

The native centered charts and chosen nonzero sheet directions determine the
actual endpoint germs. The constructed arc agrees with those parametrizations
on neighborhoods of both endpoints, is embedded and immersive on the closed
unit interval, and avoids any finite set in its interior.
-/

noncomputable section

open Set Function Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.NativeParametrization

/-- Reverse real time smoothly, with the same map as inverse. -/
def reverseTime : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toEquiv := {
    toFun := fun t => 1 - t
    invFun := fun t => 1 - t
    left_inv := fun t => by ring
    right_inv := fun t => by ring }
  contMDiff_toFun := (contDiff_const.sub contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_const.sub contDiff_id).contMDiff

theorem reverseTime_one : reverseTime (1 : ℝ) = 0 := sub_self 1

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

def line (u : D) : ℝ →L[ℝ] D := (ContinuousLinearMap.id ℝ ℝ).smulRight u

theorem line_apply (u : D) (t : ℝ) : line u t = t • u := rfl

theorem injective_line {u : D} (hu : u ≠ 0) : Injective (line u) :=
  smul_left_injective ℝ hu

end Wikipedia.SmoothSixDPoincare.NativeParametrization

namespace Wikipedia.SmoothSixDPoincare

variable {D N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [T2Space N]

/-- Connect two native chart arcs while preserving their entire endpoint germs. -/
theorem exists_embedded_arc_with_native_endpoint_germs {x y : N} (γ : Path x y) (hxy : x ≠ y)
    (hdim : 3 ≤ Module.finrank ℝ D) {u v : D} (hu : u ≠ 0) (hv : v ≠ 0)
    {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f ∧ f 0 = x ∧ f 1 = y ∧
      (f =ᶠ[𝓝 (0 : ℝ)] fun t => NativeParametrization.centered (D := D) x (t • u)) ∧
      (f =ᶠ[𝓝 (1 : ℝ)] fun t => NativeParametrization.centered (D := D) y ((1 - t) • v)) ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ S) := by
  let c := NativeParametrization.centered (D := D) x
  let d := NativeParametrization.centered (D := D) y
  let L := NativeParametrization.line u
  let T := NativeParametrization.line v
  let R := NativeParametrization.reverseTime
  let a : ℝ → N := c ∘ L
  let b : ℝ → N := d ∘ (T ∘ R)
  have hL : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ L := L.contDiff.contMDiff
  have hT : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ T := T.contDiff.contMDiff
  have hR : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (R : ℝ → ℝ) := R.contMDiff_toFun
  have hTR : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ (T ∘ R) := hT.comp hR
  have hR1 : R (1 : ℝ) = 0 := NativeParametrization.reverseTime_one
  have hTR1 : (T ∘ R) (1 : ℝ) = 0 := by rw [Function.comp_apply, hR1, map_zero]
  have hc0 : L (0 : ℝ) ∈ c.source := by
    rw [map_zero]
    exact NativeParametrization.zero_mem_centered_source x
  have hd1 : (T ∘ R) (1 : ℝ) ∈ d.source := by
    rw [hTR1]
    exact NativeParametrization.zero_mem_centered_source y
  have ha : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ a (L ⁻¹' c.source) :=
    c.contMDiffOn_toFun.comp hL.contMDiffOn (fun _ ht => ht)
  have hb : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ b ((T ∘ R) ⁻¹' d.source) :=
    d.contMDiffOn_toFun.comp hTR.contMDiffOn (fun _ ht => ht)
  have ha0 : a 0 = x := by
    change c (L 0) = x
    rw [map_zero]
    exact NativeParametrization.centered_zero x
  have hb1 : b 1 = y := by
    change d ((T ∘ R) 1) = y
    rw [hTR1]
    exact NativeParametrization.centered_zero y
  have hia : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) a 0) := by
    rw [mfderiv_comp 0 (c.mdifferentiableAt (by simp) hc0)
      (hL.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, L.fderiv]
    exact (PartialChart.bijective_mfderiv c hc0).1.comp
      (NativeParametrization.injective_line (D := D) hu)
  have hiTR : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) (T ∘ R) 1) := by
    rw [mfderiv_comp 1 (hT.mdifferentiableAt (by simp))
      (hR.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, T.fderiv]
    exact (NativeParametrization.injective_line (D := D) hv).comp
      (PartialChart.bijective_mfderiv R.toPartialDiffeomorph (mem_univ (1 : ℝ))).1
  have hib : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) b 1) := by
    rw [mfderiv_comp 1 (d.mdifferentiableAt (by simp) hd1) (hTR.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv d hd1).1.comp hiTR
  have hne : a 0 ≠ b 1 := by rwa [ha0, hb1]
  obtain ⟨f, hf, hfa, hfb, hemb, hi, havoid⟩ :=
    exists_embedded_arc_with_local_endpoint_germs ha hb
      (c.open_source.preimage L.continuous) (d.open_source.preimage hTR.continuous)
      hc0 hd1 hia hib (γ.cast ha0 hb1) hne hdim hS
  exact ⟨f, hf, hfa.eq_of_nhds.trans ha0, hfb.eq_of_nhds.trans hb1,
    hfa, hfb, hemb, hi, havoid⟩

end Wikipedia.SmoothSixDPoincare
