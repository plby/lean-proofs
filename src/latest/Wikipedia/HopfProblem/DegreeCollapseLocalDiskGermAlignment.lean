import Wikipedia.HopfProblem.DegreeCollapseSupportedLocalGerm
import Wikipedia.HopfProblem.DegreeCollapseNormalDeterminantCorrection
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Exact alignment of a disk germ by a supported ambient isotopy

The unused normal direction corrects the determinant of the inverse chart
transition. The resulting nonlinear germ has a constructed supported
realization and sends the original disk plane pointwise to the standard one.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms

variable {A B ι κ : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Nontrivial κ]

theorem exists_supported_disk_germ_alignment (b : Module.Basis ι ℝ B) (i : ι)
    (basis : Module.Basis κ ℝ (A × B))
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (h0 : (0 : A × B) ∈ Φ.source) (hΦ0 : Φ 0 = 0)
    {U : Set (A × B)} (hU : IsOpen U) (h0U : (0 : A × B) ∈ U) :
    ∃ (d : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
      (K : Set (A × B)), IsCompact K ∧ K ⊆ U ∧
      Nonempty (SupportedRelativeIsotopy d K {0}) ∧
      (fun x : A => d (Φ (x, 0))) =ᶠ[𝓝 (0 : A)] (fun x => (x, (0 : B))) := by
  have ht0 : (0 : A × B) ∈ Φ.target := hΦ0 ▸ Φ.map_source' h0
  have hi0 : Φ.symm 0 = 0 := by
    have hh := Φ.left_inv' h0
    rwa [hΦ0] at hh
  have hi : ContDiffOn ℝ ∞ (Φ.symm : (A × B) → A × B) Φ.target :=
    Φ.contMDiffOn_invFun.contDiffOn
  have hib : Bijective (fderiv ℝ Φ.symm 0) := by
    have hh := PartialChart.bijective_mfderiv Φ.symm ht0
    change Bijective (mfderiv 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) Φ.symm 0 :
      (A × B) →L[ℝ] (A × B)) at hh
    rwa [mfderiv_eq_fderiv] at hh
  let C := (LinearEquiv.ofBijective (fderiv ℝ Φ.symm 0).toLinearMap hib).toContinuousLinearEquiv
  obtain ⟨R, hR⟩ := exists_normal_det_correction b i C
  let T := (ContinuousLinearEquiv.refl ℝ A).prodCongr R
  let f : (A × B) → A × B := T ∘ Φ.symm
  have hf : ContDiffOn ℝ ∞ f (U ∩ Φ.target) :=
    T.contDiff.comp_contDiffOn (hi.mono inter_subset_right)
  have hf0 : f 0 = 0 := by simp only [f, comp_apply, hi0, map_zero]
  have hfi := ((hi.contDiffAt (Φ.open_target.mem_nhds ht0)).differentiableAt (by simp)).hasFDerivAt
  have hdf : fderiv ℝ f 0 = T.toContinuousLinearMap.comp C.toContinuousLinearMap :=
    (T.toContinuousLinearMap.hasFDerivAt.comp 0 hfi).fderiv
  have hfb : Bijective (fderiv ℝ f 0) := by
    rw [hdf]
    exact T.bijective.comp C.bijective
  have hdet : (fderiv ℝ f 0).toLinearMap.det = 1 := by
    rw [hdf]
    exact hR
  obtain ⟨d, K, hK, hKU, hH, hgerm⟩ :=
    realizes_local_germ basis (hU.inter Φ.open_target) ⟨h0U, ht0⟩ hf hf0 hfb hdet
  refine ⟨d, K, hK, hKU.trans inter_subset_left, hH, ?_⟩
  have hΦt : Tendsto Φ (𝓝 (0 : A × B)) (𝓝 0) := by
    have hh := Φ.toOpenPartialHomeomorph.continuousAt h0
    change Tendsto Φ (𝓝 (0 : A × B)) (𝓝 (Φ 0)) at hh
    rwa [hΦ0] at hh
  have hcore : Tendsto (fun x : A => (x, (0 : B))) (𝓝 0) (𝓝 (0 : A × B)) :=
    (continuous_id.prodMk continuous_const).tendsto 0
  filter_upwards [(hgerm.comp_tendsto hΦt).comp_tendsto hcore,
    hcore (Φ.open_source.mem_nhds h0)] with x hx hxsource
  change d (Φ (x, 0)) = f (Φ (x, 0)) at hx
  rw [hx]
  change T (Φ.symm (Φ (x, 0))) = (x, 0)
  have hinv : Φ.symm (Φ (x, 0)) = (x, 0) := Φ.left_inv' hxsource
  rw [hinv]
  simp [T]

end Wikipedia.HopfProblem.DegreeCollapse.SupportedGerms
