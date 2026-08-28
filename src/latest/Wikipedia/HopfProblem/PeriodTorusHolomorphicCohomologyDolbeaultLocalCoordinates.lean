import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbarPlane
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultLocal

/-!
# Local Dolbeault primitives in the native period-cover coordinates

The actual product-coordinate germ solvers apply to arbitrary open
subsets of the native `ComplexPlane₂ = Fin 2 → ℂ`.  The transfer uses
the explicit complex continuous linear equivalence with `ℂ × ℂ` and
the proved literal coordinate-derivative identities.  Closedness is
required only on the given open set; no globally closed extension or
replacement of the native topology or atlas is used.
-/

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault

open PeriodTorusLineBundleClassification
open PeriodTorusLineBundleClassificationPolydiscAnalytic (complexPairEquiv)

/-- A smooth closed pair on a native open subset has an actual smooth
primitive near every point of that open subset. -/
theorem exists_native_closed_primitive_germ {U : Set ComplexPlane₂} (hU : IsOpen U)
    {f g : ComplexPlane₂ → ℂ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hclosed : ∀ w ∈ U, dbarCoordinate g 0 w = dbarCoordinate f 1 w)
    {z : ComplexPlane₂} (hz : z ∈ U) :
    ∃ u : ComplexPlane₂ → ℂ, ContDiff ℝ ∞ u ∧
      dbarCoordinate u 0 =ᶠ[𝓝 z] f ∧ dbarCoordinate u 1 =ᶠ[𝓝 z] g := by
  have he : ContDiff ℝ ∞ complexPairEquiv.symm :=
    complexPairEquiv.symm.contDiff.restrict_scalars ℝ
  have hclosed' : ∀ q ∈ complexPairEquiv.symm ⁻¹' U,
      dbarFirst (g ∘ complexPairEquiv.symm) q =
        dbarSecond (f ∘ complexPairEquiv.symm) q := by
    intro q hq
    have h := hclosed (complexPairEquiv.symm q) hq
    simpa only [dbarCoordinate_zero_eq_pair, dbarCoordinate_one_eq_pair,
      ContinuousLinearEquiv.apply_symm_apply] using h
  have hz' : complexPairEquiv z ∈ complexPairEquiv.symm ⁻¹' U := by
    simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz
  obtain ⟨u, hu, hfirst, hsecond⟩ :=
    HolomorphicSheafCohomology.DbarLocalOne.exists_smooth_primitive_germ
      (hU.preimage complexPairEquiv.symm.continuous)
      (hf.comp he.contDiffOn (fun _ h => h))
      (hg.comp he.contDiffOn (fun _ h => h)) hclosed' hz'
  have hez : Tendsto complexPairEquiv (𝓝 z) (𝓝 (complexPairEquiv z)) :=
    complexPairEquiv.continuous.continuousAt
  refine ⟨u ∘ complexPairEquiv,
    hu.comp (complexPairEquiv.contDiff.restrict_scalars ℝ), ?_, ?_⟩
  · filter_upwards [hfirst.comp_tendsto hez] with w hw
    simpa only [dbarCoordinate_pair_zero, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply] using hw
  · filter_upwards [hsecond.comp_tendsto hez] with w hw
    simpa only [dbarCoordinate_pair_one, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply] using hw

/-- The second native antiholomorphic coordinate derivative has a local
smooth primitive for every smooth coefficient, with no closedness hypothesis. -/
theorem exists_native_second_primitive_germ {U : Set ComplexPlane₂} (hU : IsOpen U)
    {g : ComplexPlane₂ → ℂ} (hg : ContDiffOn ℝ ∞ g U)
    {z : ComplexPlane₂} (hz : z ∈ U) :
    ∃ u : ComplexPlane₂ → ℂ, ContDiff ℝ ∞ u ∧ dbarCoordinate u 1 =ᶠ[𝓝 z] g := by
  have he : ContDiff ℝ ∞ complexPairEquiv.symm :=
    complexPairEquiv.symm.contDiff.restrict_scalars ℝ
  have hz' : complexPairEquiv z ∈ complexPairEquiv.symm ⁻¹' U := by
    simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hz
  obtain ⟨u, hu, hsecond⟩ :=
    HolomorphicSheafCohomology.AffineDolbeault.exists_smooth_second_primitive_germ
      (hU.preimage complexPairEquiv.symm.continuous)
      (hg.comp he.contDiffOn (fun _ h => h)) hz'
  have hez : Tendsto complexPairEquiv (𝓝 z) (𝓝 (complexPairEquiv z)) :=
    complexPairEquiv.continuous.continuousAt
  refine ⟨u ∘ complexPairEquiv,
    hu.comp (complexPairEquiv.contDiff.restrict_scalars ℝ), ?_⟩
  filter_upwards [hsecond.comp_tendsto hez] with w hw
  simpa only [dbarCoordinate_pair_one, Function.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply] using hw

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.Dolbeault
