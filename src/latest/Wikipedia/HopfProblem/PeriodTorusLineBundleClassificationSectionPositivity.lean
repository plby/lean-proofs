import Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
import Wikipedia.HopfProblem.PeriodTorusThetaPositivity

/-!
# Positivity from an arbitrary native holomorphic section

The proved native classification and section correspondence transfer the
actual theta positivity theorem to an independently given native line
bundle. Nonvanishing is checked in the actual quotient lift and native
fibre equivalence, rather than assumed for a separately chosen function.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative
open PeriodTorusLineBundleClassificationUniqueness

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The actual theta function recovers the original core section in the
preferred quotient lift. -/
theorem coreSectionEquivTheta_at_lift {p : PeriodDomain} (F : FactorOfAutomorphy p)
    (s : Core.HolomorphicSection F) (b : p.Torus) :
    (Core.sectionEquivTheta F s).val (Core.lift p b b) = id (α := ℂ) (s b) := by
  apply associatedMap_fibre_injective F (Core.lift p b b)
  have h := Section.associatedMap_pullback F (Core.quotientSection F s) (Core.lift p b b)
  rw [Core.lift_project p b (Core.mem_baseSet p b)] at h
  exact h

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

/-- In the original native fibre, the theta coefficient is precisely the
inverse of the constructed analytic fibre equivalence applied to the section. -/
theorem nativeSectionEquivTheta_at_lift (s : ContMDiffSection IC ℂ ω V) (b : p.Torus) :
    (nativeSectionEquivTheta p V s).val (Core.lift p b b) =
      id (α := ℂ) (((nativeAppellHumbertIso p V).fiberEquiv b).symm (s b)) :=
  coreSectionEquivTheta_at_lift (nativeUnitaryDatum p V).factor
    ((nativeAppellHumbertIso p V).symm.sectionEquiv s) b

theorem nativeSectionEquivTheta_at_lift_ne_zero_iff
    (s : ContMDiffSection IC ℂ ω V) (b : p.Torus) :
    (nativeSectionEquivTheta p V s).val (Core.lift p b b) ≠ 0 ↔ s b ≠ 0 := by
  rw [nativeSectionEquivTheta_at_lift]
  change (nativeAppellHumbertIso p V).symm.sectionEquiv s b ≠ 0 ↔ s b ≠ 0
  exact (nativeAppellHumbertIso p V).symm.sectionEquiv_value_ne_zero_iff s b

theorem nativeSectionEquivTheta_nonzero (s : ContMDiffSection IC ℂ ω V)
    (hs : ∃ b, s b ≠ 0) : ∃ z, (nativeSectionEquivTheta p V s).val z ≠ 0 := by
  obtain ⟨b, hb⟩ := hs
  exact ⟨Core.lift p b b, (nativeSectionEquivTheta_at_lift_ne_zero_iff p V s b).mpr hb⟩

/-- A scalar proportionality of the actual theta representatives is an
equality in every original native fibre. -/
theorem nativeSection_eq_smul_of_theta_eq_mul
    (s t : ContMDiffSection IC ℂ ω V) (c : ℂ)
    (h : ∀ z, (nativeSectionEquivTheta p V t).val z =
      c * (nativeSectionEquivTheta p V s).val z) : ∀ b, t b = c • s b := by
  intro b
  apply ((nativeAppellHumbertIso p V).fiberEquiv b).symm.injective
  rw [map_smul]
  change id (α := ℂ) (((nativeAppellHumbertIso p V).fiberEquiv b).symm (t b)) =
    c * id (α := ℂ) (((nativeAppellHumbertIso p V).fiberEquiv b).symm (s b))
  rw [← nativeSectionEquivTheta_at_lift, ← nativeSectionEquivTheta_at_lift]
  exact h (Core.lift p b b)

/-- The Hermitian datum of any original native bundle with a nonzero
holomorphic section is positive semidefinite. -/
theorem nativeUnitaryDatum_nonnegative_of_nonzero_section
    (s : ContMDiffSection IC ℂ ω V) (hs : ∃ b, s b ≠ 0) (v : ComplexPlane₂) :
    0 ≤ ((nativeUnitaryDatum p V).form v v).re := by
  let D := nativeUnitaryDatum p V
  let θ := nativeSectionEquivTheta p V s
  have hAuto : PeriodTorusTheta.AppellHumbertAutomorphy p D.form D.multiplier θ.val :=
    θ.property.2
  exact PeriodTorusTheta.hermitian_nonnegative_of_nonzero_theta p D.form D.hermitian
    D.multiplier D.norm_multiplier θ.val (θ.property.1.differentiable (by simp)) hAuto
    (nativeSectionEquivTheta_nonzero p V s hs) v

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
