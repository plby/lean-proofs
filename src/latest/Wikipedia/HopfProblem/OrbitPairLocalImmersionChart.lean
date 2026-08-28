import Wikipedia.HopfProblem.OrbitPairLocalImmersionRetraction
import Mathlib.Analysis.Normed.Module.ContinuousInverse

/-!
# Completing a native local immersion to a target chart

A complement of the actual derivative supplies the extra chart directions.
The inverse-function theorem applied after a native target chart gives a
partial diffeomorphism whose zero section is exactly the original local
immersion. The original target atlas is retained, and the chart can be
confined to any prescribed open target neighborhood.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeImmersion

open Wikipedia.SmoothSixDPoincare

variable {D G H N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

theorem exists_local_immersion_chart {f : D → N} {U : Set D}
    (hU : IsOpen U) (h0U : (0 : D) ∈ U)
    (hf : ContMDiffOn 𝓘(ℝ, D) J ∞ f U)
    (hinj : Injective (mfderiv 𝓘(ℝ, D) J f 0))
    {O : Set N} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ W : Submodule ℝ G, ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × W) J (D × W) N ∞,
        closedBall (0 : D) ε ×ˢ closedBall (0 : W) ε ⊆ Φ.source ∧
        Φ.source ⊆ U ×ˢ univ ∧ Φ.target ⊆ O ∧
        ∀ z, (z, 0) ∈ Φ.source → Φ (z, 0) = f z := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f 0)
  have hcf0 : f 0 ∈ c.source := mem_extChartAt_source (f 0)
  let U' : Set D := U ∩ f ⁻¹' c.source
  have hU' : IsOpen U' := hf.continuousOn.isOpen_inter_preimage hU c.open_source
  have h0U' : (0 : D) ∈ U' := ⟨h0U, hcf0⟩
  have hcf : ContDiffOn ℝ ∞ (c ∘ f) U' :=
    (c.contMDiffOn_toFun.comp (hf.mono inter_subset_left) (fun _ h => h.2)).contDiffOn
  have hdf : DifferentiableAt ℝ (c ∘ f) 0 :=
    (hcf.contDiffAt (hU'.mem_nhds h0U')).differentiableAt (by simp)
  let T : D →L[ℝ] G := fderiv ℝ (c ∘ f) 0
  have hT : Injective T := (ManifoldImmersion.injective_fderiv_chart_iff c
    ((hf.contMDiffAt (hU.mem_nhds h0U)).mdifferentiableAt (by simp)) hcf0).mpr hinj
  have hleft := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hT
  let W : Submodule ℝ G := hleft.complement
  let L : (D × W) ≃L[ℝ] G := T.coprodSubtypeLEquivOfIsCompl hleft.isCompl_complement
    (LinearMap.ker_eq_bot.mpr hT)
  let H : D × W → G := fun q => c (f q.1) + q.2.val
  have hH : ContDiffOn ℝ ∞ H (U' ×ˢ (univ : Set W)) :=
    (hcf.comp contDiffOn_fst (fun _ h => h.1)).add
      (W.subtypeL.contDiff.comp contDiff_snd).contDiffOn
  have hH0 : H (0, 0) = c (f 0) := add_zero _
  have hderiv : HasFDerivAt H (T.coprod W.subtypeL) (0, 0) := by
    have hfst : HasFDerivAt (Prod.fst : D × W → D)
        (ContinuousLinearMap.fst ℝ D W) (0, 0) := hasFDerivAt_fst
    have hsnd : HasFDerivAt (Prod.snd : D × W → W)
        (ContinuousLinearMap.snd ℝ D W) (0, 0) := hasFDerivAt_snd
    have h₁ := HasFDerivAt.comp (𝕜 := ℝ) (g := c ∘ f) (g' := T)
      (f := (Prod.fst : D × W → D)) (f' := ContinuousLinearMap.fst ℝ D W)
      ((0 : D), (0 : W)) hdf.hasFDerivAt hfst
    have h₂ := HasFDerivAt.comp (𝕜 := ℝ) (g := (W.subtypeL : W → G)) (g' := W.subtypeL)
      (f := (Prod.snd : D × W → W)) (f' := ContinuousLinearMap.snd ℝ D W)
      ((0 : D), (0 : W)) W.subtypeL.hasFDerivAt hsnd
    have hsum := h₁.add h₂
    have hlin : T.comp (ContinuousLinearMap.fst ℝ D W) +
        W.subtypeL.comp (ContinuousLinearMap.snd ℝ D W) = T.coprod W.subtypeL := by
      apply ContinuousLinearMap.ext
      intro q
      rfl
    rw [hlin] at hsum
    change HasFDerivAt H (T.coprod W.subtypeL) (0, 0) at hsum
    exact hsum
  let V : Set G := c.target ∩ c.symm ⁻¹' O
  have hV : IsOpen V := c.contMDiffOn_invFun.continuousOn.isOpen_inter_preimage c.open_target hO
  have hc0V : c (f 0) ∈ V := by
    refine ⟨c.map_source' hcf0, ?_⟩
    change c.symm (c (f 0)) ∈ O
    have hleft : c.symm (c (f 0)) = f 0 := c.left_inv' hcf0
    rw [hleft]
    exact h0O
  let Z : Set (D × W) := (U' ×ˢ univ) ∩ H ⁻¹' V
  have hZ : IsOpen Z := hH.continuousOn.isOpen_inter_preimage (hU'.prod isOpen_univ) hV
  have h0Z : (0, 0) ∈ Z := ⟨⟨h0U', mem_univ _⟩, by
    change H (0, 0) ∈ V
    rwa [hH0]⟩
  have hinv : (fderiv ℝ H (0, 0)).IsInvertible := by
    rw [hderiv.fderiv]
    exact ⟨L, rfl⟩
  obtain ⟨d, h0d, hdZ, hdH⟩ := NoExoticSixSphere.exists_partialDiffeomorph_of_contDiffOn
    hZ h0Z (hH.mono inter_subset_left) hinv
  let Φ := d.trans c.symm
  have h0Φ : (0, 0) ∈ Φ.source := by
    refine ⟨h0d, ?_⟩
    change d (0, 0) ∈ c.target
    rw [hdH, hH0]
    exact c.map_source' hcf0
  obtain ⟨ε, hε, hball⟩ := nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds h0Φ)
  refine ⟨W, ε, hε, Φ, ?_, ?_, ?_, ?_⟩
  · rw [closedBall_prod_same]
    exact hball
  · intro q hq
    exact ⟨(hdZ hq.1).1.1.1, mem_univ _⟩
  · intro z hz
    have hq := Φ.map_target' hz
    have hh := (hdZ hq.1).2.2
    change c.symm (H (Φ.invFun z)) ∈ O at hh
    have heq : Φ (Φ.invFun z) = c.symm (H (Φ.invFun z)) := by
      change c.symm (d (Φ.invFun z)) = c.symm (H (Φ.invFun z))
      rw [hdH]
    rw [← heq, Φ.right_inv' hz] at hh
    exact hh
  · intro z hz
    change c.symm (d (z, 0)) = f z
    rw [hdH]
    change c.symm (c (f z) + (0 : G)) = f z
    rw [add_zero]
    exact c.left_inv' (hdZ hz.1).1.1.2

end Wikipedia.HopfProblem.OrbitPair.NativeImmersion
