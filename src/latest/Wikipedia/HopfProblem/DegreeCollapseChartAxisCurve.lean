import Wikipedia.HopfProblem.DegreeCollapseCleanSheetAxisChart

/-!
# Native chart axes and the terminal sheet coordinate change

An axis of a native partial diffeomorphism is locally smooth and immersive.
The terminal coordinate change shifts its center to time one and exchanges
the two transverse factors, retaining a genuine native diffeomorphism.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

theorem chart_axis_curve_properties
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞)
    (p : ℝ) (hp : (p, (0 : V)) ∈ Φ.source) :
    ∃ U : Set ℝ, IsOpen U ∧ p ∈ U ∧
      (∀ t ∈ U, (t, (0 : V)) ∈ Φ.source) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) J ∞ (fun t => Φ (t, (0 : V))) U ∧
      Injective (mfderiv 𝓘(ℝ, ℝ) J (fun t => Φ (t, (0 : V))) p) := by
  let L := ContinuousLinearMap.inl ℝ ℝ V
  have hL : ContDiff ℝ ∞ L := L.contDiff
  let U : Set ℝ := L ⁻¹' Φ.source
  have hU : IsOpen U := Φ.open_source.preimage L.continuous
  have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ (Φ ∘ L) U :=
    Φ.contMDiffOn_toFun.comp hL.contMDiff.contMDiffOn (fun _ ht => ht)
  refine ⟨U, hU, hp, fun _ ht => ht, hcurve, ?_⟩
  change Injective (mfderiv 𝓘(ℝ, ℝ) J (Φ ∘ L) p)
  rw [mfderiv_comp p (Φ.mdifferentiableAt (by simp) hp)
    (hL.contMDiff.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, L.fderiv]
  exact (PartialChart.bijective_mfderiv Φ hp).injective.comp
    (fun _ _ h => congrArg Prod.fst h)

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

def terminalSheetCoordinates : Diffeomorph 𝓘(ℝ, ℝ × (D × D)) 𝓘(ℝ, ℝ × (D × D))
    (ℝ × (D × D)) (ℝ × (D × D)) ∞ where
  toEquiv := {
    toFun := fun z => (z.1 - 1, (z.2.2, z.2.1))
    invFun := fun z => (z.1 + 1, (z.2.2, z.2.1))
    left_inv := by intro z; ext <;> simp
    right_inv := by intro z; ext <;> simp }
  contMDiff_toFun := ((contDiff_fst.sub contDiff_const).prodMk
    (contDiff_snd.snd.prodMk contDiff_snd.fst)).contMDiff
  contMDiff_invFun := ((contDiff_fst.add contDiff_const).prodMk
    (contDiff_snd.snd.prodMk contDiff_snd.fst)).contMDiff

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
