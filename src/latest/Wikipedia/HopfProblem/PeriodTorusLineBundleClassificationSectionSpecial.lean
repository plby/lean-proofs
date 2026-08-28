import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationSectionPositivity
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationSectionSpecialData
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationSectionTrivialization

/-!
# Arbitrary native holomorphic sections on the special period tori

Away from the actual exceptional set, a nonzero section of an arbitrary
original native holomorphic line bundle forces its full unitary datum to
be trivial. The section is then nowhere zero, and every other section is
a constant scalar multiple in the original fibres.

These statements concern independently defined native sections. No polar
Cartier bundle or representation of arbitrary meromorphic functions by
such section pairs is assumed.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative
open PeriodTorusLineBundleClassificationUniqueness
open PeriodTorusTypeOneOne SpecialPeriods UpperHalfPlane

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable (z : ℍ) (V : (specialPeriodMap.point z).Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

/-- No factor presentation is supplied: the full datum is that constructed
for the original arbitrary native bundle by the proved classification. -/
theorem nativeUnitaryDatum_eq_trivial_of_nonzero_section
    (hz : z ∉ exceptionalTypeOneOneSet)
    (s : ContMDiffSection IC ℂ ω V) (hs : ∃ b, s b ≠ 0) :
    nativeUnitaryDatum (specialPeriodMap.point z) V =
      trivialUnitaryDatum (specialPeriodMap.point z) :=
  unitaryDatum_eq_trivial_of_nonzero_theta z hz
    (nativeUnitaryDatum (specialPeriodMap.point z) V)
    (nativeSectionEquivTheta (specialPeriodMap.point z) V s)
    (nativeSectionEquivTheta_nonzero (specialPeriodMap.point z) V s hs)

/-- A nonzero original holomorphic section has no zero at any point of
the actual special torus outside the exceptional set. -/
theorem nativeSection_nowhere_zero_of_not_exceptional
    (hz : z ∉ exceptionalTypeOneOneSet)
    (s : ContMDiffSection IC ℂ ω V) (hs : ∃ b, s b ≠ 0) : ∀ b, s b ≠ 0 := by
  obtain ⟨_, c, hc, hθ, _⟩ := unitaryDatum_theta_constant_of_not_exceptional z hz
    (nativeUnitaryDatum (specialPeriodMap.point z) V)
    (nativeSectionEquivTheta (specialPeriodMap.point z) V s)
    (nativeSectionEquivTheta_nonzero (specialPeriodMap.point z) V s hs)
  intro b
  apply (nativeSectionEquivTheta_at_lift_ne_zero_iff (specialPeriodMap.point z) V s b).mp
  simpa only [hθ] using hc

/-- Any two native sections with a nonzero first section are proportional
by one complex constant, with equality in every original native fibre. -/
theorem nativeSections_proportional_of_not_exceptional
    (hz : z ∉ exceptionalTypeOneOneSet)
    (s : ContMDiffSection IC ℂ ω V) (hs : ∃ b, s b ≠ 0)
    (t : ContMDiffSection IC ℂ ω V) : ∃ c : ℂ, ∀ b, t b = c • s b := by
  let p := specialPeriodMap.point z
  let D := nativeUnitaryDatum p V
  let θs := nativeSectionEquivTheta p V s
  let θt := nativeSectionEquivTheta p V t
  obtain ⟨hform, c, hc, hθs, _⟩ := unitaryDatum_theta_constant_of_not_exceptional z hz
    D θs (nativeSectionEquivTheta_nonzero p V s hs)
  have htAuto : PeriodTorusTheta.AppellHumbertAutomorphy p 0 D.multiplier θt.val := by
    simpa only [hform] using unitaryDatum_theta_automorphy D θt
  have ht := PeriodTorusTheta.theta_eq_at_zero_of_zero_form p D.multiplier
    D.norm_multiplier θt.val (θt.property.1.differentiable (by simp)) htAuto
  refine ⟨θt.val 0 / c, nativeSection_eq_smul_of_theta_eq_mul p V s t _ ?_⟩
  intro x
  change θt.val x = θt.val 0 / c * θs.val x
  rw [ht x, hθs]
  exact (div_mul_cancel₀ (θt.val 0) hc).symm

/-- The proportionality constant is unique whenever the first original
section is nonzero. -/
theorem nativeSections_unique_proportional_of_not_exceptional
    (hz : z ∉ exceptionalTypeOneOneSet)
    (s : ContMDiffSection IC ℂ ω V) (hs : ∃ b, s b ≠ 0)
    (t : ContMDiffSection IC ℂ ω V) : ∃! c : ℂ, ∀ b, t b = c • s b := by
  obtain ⟨c, hc⟩ := nativeSections_proportional_of_not_exceptional z V hz s hs t
  refine ⟨c, hc, ?_⟩
  intro d hd
  obtain ⟨b, hb⟩ := hs
  let e := ((nativeAppellHumbertIso (specialPeriodMap.point z) V).fiberEquiv b).symm
  have hne : id (α := ℂ) (e (s b)) ≠ 0 := by
    intro h
    apply hb
    exact e.injective (h.trans (map_zero e).symm)
  apply mul_right_cancel₀ hne
  have h := congrArg e ((hd b).symm.trans (hc b))
  rw [map_smul, map_smul] at h
  change d * id (α := ℂ) (e (s b)) = c * id (α := ℂ) (e (s b)) at h
  exact h

/-- An actual product diffeomorphism for the independently given native
bundle, obtained from any nonzero original holomorphic section. -/
def specialSectionProductDiffeomorph (hz : z ∉ exceptionalTypeOneOneSet)
    (s : ContMDiffSection IC ℂ ω V) (hs : ∃ b, s b ≠ 0) :
    Diffeomorph ((IC).prod I₁) ((IC).prod I₁)
      (TotalSpace ℂ V) ((specialPeriodMap.point z).Torus × ℂ) ω :=
  nonzeroSectionProductDiffeomorph (specialPeriodMap.point z) V s
    (nativeSection_nowhere_zero_of_not_exceptional z V hz s hs)

theorem specialSectionProductDiffeomorph_preserves_base
    (hz : z ∉ exceptionalTypeOneOneSet)
    (s : ContMDiffSection IC ℂ ω V) (hs : ∃ b, s b ≠ 0) (v : TotalSpace ℂ V) :
    (specialSectionProductDiffeomorph z V hz s hs v).1 = v.proj :=
  nonzeroSectionProductDiffeomorph_preserves_base (specialPeriodMap.point z) V s
    (nativeSection_nowhere_zero_of_not_exceptional z V hz s hs) v

theorem specialSectionProductDiffeomorph_map_add
    (hz : z ∉ exceptionalTypeOneOneSet)
    (s : ContMDiffSection IC ℂ ω V) (hs : ∃ b, s b ≠ 0)
    (b : (specialPeriodMap.point z).Torus) (v w : V b) :
    (specialSectionProductDiffeomorph z V hz s hs ⟨b, v + w⟩).2 =
      (specialSectionProductDiffeomorph z V hz s hs ⟨b, v⟩).2 +
        (specialSectionProductDiffeomorph z V hz s hs ⟨b, w⟩).2 :=
  nonzeroSectionProductDiffeomorph_map_add (specialPeriodMap.point z) V s
    (nativeSection_nowhere_zero_of_not_exceptional z V hz s hs) b v w

theorem specialSectionProductDiffeomorph_map_smul
    (hz : z ∉ exceptionalTypeOneOneSet)
    (s : ContMDiffSection IC ℂ ω V) (hs : ∃ b, s b ≠ 0)
    (b : (specialPeriodMap.point z).Torus) (c : ℂ) (v : V b) :
    (specialSectionProductDiffeomorph z V hz s hs ⟨b, c • v⟩).2 =
      c • (specialSectionProductDiffeomorph z V hz s hs ⟨b, v⟩).2 :=
  nonzeroSectionProductDiffeomorph_map_smul (specialPeriodMap.point z) V s
    (nativeSection_nowhere_zero_of_not_exceptional z V hz s hs) b c v

theorem specialSectionProductDiffeomorph_section
    (hz : z ∉ exceptionalTypeOneOneSet)
    (s : ContMDiffSection IC ℂ ω V) (hs : ∃ b, s b ≠ 0)
    (b : (specialPeriodMap.point z).Torus) :
    specialSectionProductDiffeomorph z V hz s hs ⟨b, s b⟩ = (b, 1) :=
  nonzeroSectionProductDiffeomorph_section (specialPeriodMap.point z) V s
    (nativeSection_nowhere_zero_of_not_exceptional z V hz s hs) b

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
