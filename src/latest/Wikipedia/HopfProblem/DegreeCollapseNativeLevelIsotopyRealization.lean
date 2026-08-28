import Wikipedia.HopfProblem.DegreeCollapseNormalizedWholeLevelCylinder
import Wikipedia.HopfProblem.DegreeCollapseNativeWholeLevelTails

/-!
# Realizing a level isotopy in the original descending dynamics

Every actual smooth isotopy of a compact regular level is realized by a
supported holonomy change in an arbitrary positive regular gap. The whole
level supplies compact support; no coordinate support or prescribed
normalization is assumed. The original critical field germs are retained.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem exists_native_regular_level_isotopy_realization {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hdesc : ∀ y, y ∉ ManifoldMorse.criticalPoints E f →
      mvfderiv 𝓘(ℝ, E) f y (V y) < 0)
    (F : Flow ℝ M) (hF : ∀ y, IsMIntegralCurve (fun t => F t y) V)
    {a b c : ℝ} (ha : a < c) (hb : c < b)
    (hband : ∀ y, f y ∈ Icc a b → y ∉ ManifoldMorse.criticalPoints E f)
    (hreg : ∀ y, f y = c → y ∉ ManifoldMorse.criticalPoints E f)
    (z : {y : M // f y = c}) :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ D : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {y : M // f y = c} {y : M // f y = c} ∞,
      IsotopicToIdentity D →
      ∃ (r : ℝ) (C : Set M)
        (W V' : (y : M) → TangentSpace 𝓘(ℝ, E) y) (H G : Flow ℝ M),
        0 < r ∧ r < c - a ∧ IsCompact C ∧ C ⊆ f ⁻¹' Ioo a b ∧
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun y => (⟨y, W y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ y, IsMIntegralCurve (fun t => H t y) W) ∧
        (∀ y, range (fun t => H t y) = range (fun t => F t y) ∧
          (∀ p, Tendsto (fun t => H t y) atTop (𝓝 p) ↔ Tendsto (fun t => F t y) atTop (𝓝 p)) ∧
          ∀ p, Tendsto (fun t => H t y) atBot (𝓝 p) ↔ Tendsto (fun t => F t y) atBot (𝓝 p)) ∧
        ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
          (fun y => (⟨y, V' y⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
        (∀ y, IsMIntegralCurve (fun t => G t y) V') ∧
        (∀ y, V' y = 0 ↔ V y = 0) ∧
        (∀ y, y ∉ ManifoldMorse.criticalPoints E f → mvfderiv 𝓘(ℝ, E) f y (V' y) < 0) ∧
        (∀ y ∈ ManifoldMorse.criticalPoints E f, ∀ᶠ x in 𝓝 y, V' x = V x) ∧
        (∀ y ∉ C, ∀ᶠ x in 𝓝 y, V' x = W x) ∧
        (∀ x : {y : M // f y = c}, G 1 x = H 1 (D x)) ∧
        (∀ x : {y : M // f y = c}, f (H 1 x) = c - r) ∧
        (∀ x : {y : M // f y = c}, ∀ t : ℝ, t ≤ 0 → G t x = H t x) ∧
        ∀ x : {y : M // f y = c}, ∀ t : ℝ, 0 ≤ t → G t (H 1 x) = H t (H 1 x) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let L := {y : M // f y = c}
  let _ : CompactSpace L :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro D hD
  obtain ⟨B, hB, hBzero, hBone, hBslices⟩ := hD
  let I : SupportedRelativeIsotopy D univ ∅ := {
    family := B
    smooth := hB
    zero := hBzero
    one := hBone
    slices := fun t => by
      obtain ⟨d, hd⟩ := hBslices t
      exact ⟨d, fun x => (hd x).symm⟩
    fixedOutside := fun _ x hx => (hx (mem_univ x)).elim
    fixedOn := fun _ _ hx => hx.elim }
  obtain ⟨r, W, H, A, hr, hrbound, hW, hH, hWzero, hWneg, hWgerm,
      hgeometry, hsource, -, hformula, hheight, hmodel⟩ :=
    FlowTimeChange.exists_normalized_whole_level_cylinder hf hV hdesc F hF
      ha hb hband hreg z
  obtain ⟨C, V', G, Ψ, hC, hCsub, hV', hG, hzero, hneg, hgerm,
      -, -, hfull, hend, -, -, hleft, hright, -⟩ :=
    exists_native_whole_level_holonomy A hsource hf hr
      (fun p hp => hheight p ⟨hp.1.le, hp.2.le⟩) W hW hmodel H hH D isCompact_univ I
  have hCband : C ⊆ f ⁻¹' Ioo a b := by
    intro y hy
    have hh := (hCsub hy).2
    change f y ∈ Ioo (c - r) c at hh
    exact ⟨by linarith [hh.1], lt_trans hh.2 hb⟩
  have hcritical (y : M) (hy : y ∈ ManifoldMorse.criticalPoints E f) :
      ∀ᶠ x in 𝓝 y, V' x = V x := by
    have hout : y ∉ C := fun hc => hband y ⟨(hCband hc).1.le, (hCband hc).2.le⟩ hy
    filter_upwards [hgerm y hout, hWgerm y hy] with x hx hx'
    exact hx.trans hx'
  obtain ⟨htailLeft, htailRight⟩ :=
    native_whole_level_exterior_tails A Subtype.val H G hformula D Ψ hleft hright hfull
  have hA0 (x : L) : A (x, 0) = (x : M) := by
    rw [hformula, H.map_zero_apply]
  have hA1 (x : L) : A (x, 1) = H 1 x := hformula (x, 1)
  refine ⟨r, C, W, V', H, G, hr, hrbound, hC, hCband, hW, hH,
    hgeometry, hV', hG, fun y => (hzero y).trans (hWzero y),
    fun y hy => hneg y (hWneg y hy), hcritical, hgerm, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [← hA0 x, hend, hA1]
  · intro x
    have hh := hheight (x, 1) (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    rw [hA1, mul_one] at hh
    exact hh
  · intro x t ht
    simpa only [hA0] using htailLeft x t ht
  · intro x t ht
    simpa only [hA1] using htailRight x t ht

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
