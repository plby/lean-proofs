import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspQuotient
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The analytic structure of the actual cyclic cusp quotient

The exponential-induced homeomorphism supplies the complex quotient
structure on the cyclic cusp orbit space.  The actual quotient projection
is holomorphic, and the induced map to the punctured disc is a genuine
biholomorphism.  Adding the missing disc center gives the local cusp
filling; no full-triangle precise-invariance assertion is assumed here.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The complex exponential coordinate on the actual cyclic orbit space. -/
def cuspOrbitCoordinate (x : CuspOrbitSpace) : ℂ := cuspOrbitDiscHomeomorph x

theorem cuspOrbitCoordinate_isOpenEmbedding : IsOpenEmbedding cuspOrbitCoordinate :=
  puncturedDisc.isOpen.isOpenEmbedding_subtypeVal.comp cuspOrbitDiscHomeomorph.isOpenEmbedding

instance cuspOrbitChartedSpace : ChartedSpace ℂ CuspOrbitSpace :=
  cuspOrbitCoordinate_isOpenEmbedding.singletonChartedSpace

instance cuspOrbitIsManifold : IsManifold 𝓘(ℂ) ω CuspOrbitSpace :=
  cuspOrbitCoordinate_isOpenEmbedding.isManifold_singleton

theorem cuspOrbitCoordinate_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω cuspOrbitCoordinate :=
  contMDiff_isOpenEmbedding cuspOrbitCoordinate_isOpenEmbedding

@[simp] theorem cuspOrbitCoordinate_mk (z : ℍ) :
    cuspOrbitCoordinate (cuspOrbitMap z) = cuspQ z := rfl

/-- The quotient projection is holomorphic for the constructed quotient
complex structure, since its actual coordinate is the exponential. -/
theorem cuspOrbitMap_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω cuspOrbitMap := by
  apply ContMDiff.of_comp_isOpenEmbedding cuspOrbitCoordinate_isOpenEmbedding
  exact cuspQ_holomorphic

theorem cuspOrbitDiscHomeomorph_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω cuspOrbitDiscHomeomorph := by
  intro x
  have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y : CuspOrbitSpace => (cuspOrbitDiscHomeomorph y : ℂ)) x ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω cuspOrbitDiscHomeomorph x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (cuspOrbitCoordinate_holomorphic x)

theorem cuspOrbitDiscHomeomorph_symm_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω cuspOrbitDiscHomeomorph.symm := by
  apply ContMDiff.of_comp_isOpenEmbedding cuspOrbitCoordinate_isOpenEmbedding
  simpa only [Function.comp_def, cuspOrbitCoordinate, Homeomorph.apply_symm_apply] using
    (contMDiff_subtype_val : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun q : PuncturedDisc => (q : ℂ)))

/-- The actual cyclic quotient, with its verified quotient complex
structure, is biholomorphic to the punctured unit disc. -/
def cuspOrbitDiscBiholomorph : Diffeomorph 𝓘(ℂ) 𝓘(ℂ) CuspOrbitSpace PuncturedDisc ω where
  toEquiv := cuspOrbitDiscHomeomorph.toEquiv
  contMDiff_toFun := cuspOrbitDiscHomeomorph_holomorphic
  contMDiff_invFun := cuspOrbitDiscHomeomorph_symm_holomorphic

@[simp] theorem cuspOrbitDiscBiholomorph_mk (z : ℍ) :
    cuspOrbitDiscBiholomorph (cuspOrbitMap z) = cuspQMap z := rfl

/-- Inclusion of the actual punctured cusp into its filled unit disc. -/
def filledCuspInclusion (x : CuspOrbitSpace) : Disc :=
  ⟨cuspOrbitCoordinate x, by
    have hn : ‖cuspOrbitCoordinate x‖ < 1 := (cuspOrbitDiscHomeomorph x).property.2
    simpa [unitDisc] using hn⟩

@[simp] theorem filledCuspInclusion_val (x : CuspOrbitSpace) :
    (filledCuspInclusion x : ℂ) = cuspOrbitCoordinate x := rfl

theorem filledCuspInclusion_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω filledCuspInclusion := by
  intro x
  have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun y : CuspOrbitSpace => (filledCuspInclusion y : ℂ)) x ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω filledCuspInclusion x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (cuspOrbitCoordinate_holomorphic x)

theorem filledCuspInclusion_injective : Function.Injective filledCuspInclusion := by
  intro x y h
  apply cuspOrbitDiscHomeomorph.injective
  apply Subtype.ext
  exact congrArg (fun q : Disc => (q : ℂ)) h

theorem filledCuspInclusion_range : range filledCuspInclusion = {discZero}ᶜ := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩ h
    have he : cuspOrbitCoordinate x = 0 := congrArg (fun q : Disc => (q : ℂ)) h
    exact (cuspOrbitDiscHomeomorph x).property.1 he
  · intro hq
    have hzero : (q : ℂ) ≠ 0 := by
      intro he
      exact hq (Subtype.ext he)
    let q' : PuncturedDisc := ⟨q, hzero, disc_norm_lt_one q⟩
    refine ⟨cuspOrbitDiscHomeomorph.symm q', ?_⟩
    apply Subtype.ext
    simp [filledCuspInclusion, cuspOrbitCoordinate, q']

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
