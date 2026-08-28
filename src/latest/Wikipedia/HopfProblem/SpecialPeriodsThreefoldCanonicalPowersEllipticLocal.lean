import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersEllipticNativeChart
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersEllipticSquare
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersBase
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalPrescribedDivisorOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsSectionDivisorLocal

/-!
# Actual local bundle comparisons for the quartic elliptic divisor

The chart domains below are the images of genuine native elliptic chart
sources under the original patch inclusion.  Their holomorphic units
are transported from the exact root-disc calculation.  Off the central
surface the actual tensor-square section has coefficient one in its
outside chart.  Together these give a local section comparison at every
point, including every central point, in the two independently built
native line bundles.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersElliptic

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  specialEllipticPieceChartedSpace

local instance powersLocalSmallManifold : IsManifold IF ω (SpecialEllipticPiece .four) :=
  specialEllipticPiece_isManifold .four

/-- The natural image of the entire original native chart source. -/
def chartDomain (a : SpecialEllipticPiece .four) : TopologicalSpace.Opens Threefold.Space :=
  ⟨EllipticGeometry.inclusion .four '' (chartAt Model a).source,
    (EllipticGeometry.inclusion_openEmbedding .four).isOpenMap _
      (chartAt Model a).open_source⟩

theorem chartDomain_subset_patch (a : SpecialEllipticPiece .four) :
    (chartDomain a : Set Threefold.Space) ⊆ GlobalEllipticDivisor.patch := by
  rintro _ ⟨x, _, rfl⟩
  exact (EllipticGeometry.nativePatchBiholomorph .four x).property

theorem chartDomain_cover (y : GlobalEllipticDivisor.patch) :
    y.val ∈ chartDomain ((EllipticGeometry.nativePatchBiholomorph .four).symm y) :=
  ⟨(EllipticGeometry.nativePatchBiholomorph .four).symm y, mem_chart_source Model _,
    congrArg Subtype.val ((EllipticGeometry.nativePatchBiholomorph .four).apply_symm_apply y)⟩

def chartPatchPoint (a : SpecialEllipticPiece .four) (x : chartDomain a) :
    GlobalEllipticDivisor.patch := ⟨x.val, chartDomain_subset_patch a x.property⟩

theorem chartPatchPoint_holomorphic (a : SpecialEllipticPiece .four) :
    ContMDiff IF IF ω (chartPatchPoint a) := by
  intro x
  have he : ContMDiffAt IF IF ω (Subtype.val ∘ chartPatchPoint a) x ↔
      ContMDiffAt IF IF ω (chartPatchPoint a) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (contMDiff_subtype_val x)

def chartNativePoint (a : SpecialEllipticPiece .four) (x : chartDomain a) :
    SpecialEllipticPiece .four :=
  (EllipticGeometry.nativePatchBiholomorph .four).symm (chartPatchPoint a x)

theorem chartNativePoint_inclusion (a : SpecialEllipticPiece .four) (x : chartDomain a) :
    EllipticGeometry.inclusion .four (chartNativePoint a x) = x.val :=
  congrArg Subtype.val ((EllipticGeometry.nativePatchBiholomorph .four).apply_symm_apply
    (chartPatchPoint a x))

theorem chartNativePoint_mem_source (a : SpecialEllipticPiece .four) (x : chartDomain a) :
    chartNativePoint a x ∈ (chartAt Model a).source := by
  obtain ⟨y, hy, he⟩ := x.property
  have h : chartNativePoint a x = y :=
    EllipticGeometry.inclusion_injective .four ((chartNativePoint_inclusion a x).trans he.symm)
  rw [h]
  exact hy

theorem chartNativePoint_holomorphic (a : SpecialEllipticPiece .four) :
    ContMDiff IF IF ω (chartNativePoint a) :=
  (EllipticGeometry.nativePatchBiholomorph .four).symm.contMDiff.comp
    (chartPatchPoint_holomorphic a)

def chartSmallPoint (a : SpecialEllipticPiece .four) (x : chartDomain a) : SmallChart a :=
  ⟨chartNativePoint a x, chartNativePoint_mem_source a x⟩

theorem chartSmallPoint_inclusion (a : SpecialEllipticPiece .four) (x : chartDomain a) :
    EllipticGeometry.inclusion .four (chartSmallPoint a x).val = x.val :=
  chartNativePoint_inclusion a x

theorem chartSmallPoint_holomorphic (a : SpecialEllipticPiece .four) :
    ContMDiff IF IF ω (chartSmallPoint a) := by
  intro x
  have he : ContMDiffAt IF IF ω (Subtype.val ∘ chartSmallPoint a) x ↔
      ContMDiffAt IF IF ω (chartSmallPoint a) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (chartNativePoint_holomorphic a x)

/-- A total extension of the actual chart unit, used only on its original
open domain when asserting regularity or the section comparison. -/
def chartCoefficient (a : SpecialEllipticPiece .four) (x : Threefold.Space) : ℂ := by
  classical
  exact if hx : x ∈ chartDomain a then
    nativeCoefficientUnit a (chartSmallPoint a ⟨x, hx⟩) else 1

theorem chartCoefficient_of_mem (a : SpecialEllipticPiece .four) {x : Threefold.Space}
    (hx : x ∈ chartDomain a) :
    chartCoefficient a x = nativeCoefficientUnit a (chartSmallPoint a ⟨x, hx⟩) := by
  simp only [chartCoefficient, dif_pos hx]

theorem chartCoefficient_holomorphicOn (a : SpecialEllipticPiece .four) :
    ContMDiffOn IF 𝓘(ℂ) ω (chartCoefficient a) (chartDomain a) := by
  have hh : ContMDiff IF 𝓘(ℂ) ω (fun x : chartDomain a => chartCoefficient a x.val) := by
    have he : (fun x : chartDomain a => chartCoefficient a x.val) =
        nativeCoefficientUnit a ∘ chartSmallPoint a := by
      funext x
      exact chartCoefficient_of_mem a x.property
    rw [he]
    exact (nativeCoefficientUnit_holomorphic a).comp (chartSmallPoint_holomorphic a)
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (hh ⟨x, hx⟩)).contMDiffWithinAt

theorem chartCoefficient_ne_zero (a : SpecialEllipticPiece .four) {x : Threefold.Space}
    (hx : x ∈ chartDomain a) : chartCoefficient a x ≠ 0 := by
  rw [chartCoefficient_of_mem a hx]
  exact nativeCoefficientUnit_ne_zero a _

theorem chartDomain_subset_pair (a : SpecialEllipticPiece .four) :
    (chartDomain a : Set Threefold.Space) ⊆
      squareData.baseSet (some (nativeChart a), some (nativeChart a)) ∩
        PowersBase.pullbackData.baseSet false := by
  rintro _ ⟨x, hx, rfl⟩
  have hp : EllipticGeometry.inclusion .four x ∈ GlobalEllipticDivisor.patch :=
    (EllipticGeometry.nativePatchBiholomorph .four x).property
  have hi : EllipticGeometry.inclusion .four x ∈ (nativeChart a).val.source :=
    Threefold.Canonical.inclusion_mem_patchChart_source (some (some .four)) a x hx
  exact ⟨⟨⟨hp, hi⟩, ⟨hp, hi⟩⟩,
    (mem_finiteChart _).mpr (GlobalPrescribedDivisor.fourPatch_projection_ne_infty hp)⟩

/-- The unit relates the actual tensor-square and pulled-back point
section coefficients on the entire genuine chart, including its zeros. -/
theorem chartCoefficient_equation (a : SpecialEllipticPiece .four) {x : Threefold.Space}
    (hx : x ∈ chartDomain a) :
    chartCoefficient a x *
        squareData.localCoefficient squareSection (some (nativeChart a), some (nativeChart a)) x =
      PowersBase.pullbackData.localCoefficient PowersBase.pullbackSection false x := by
  rw [chartCoefficient_of_mem a hx, squareSection_localCoefficient_self,
    PowersBase.pullbackSection_finite_coefficient (chartDomain_subset_pair a hx).2]
  have h := nativeCoefficientUnit_equation a (chartSmallPoint a ⟨x, hx⟩)
  rw [chartSmallPoint_inclusion] at h
  exact h

/-- A genuine local comparison at every point of an original elliptic chart. -/
def ellipticComparison (a : SpecialEllipticPiece .four) :
    LocalSectionComparison IF squareData PowersBase.pullbackData squareSection
      PowersBase.pullbackSection where
  sourceChart := (some (nativeChart a), some (nativeChart a))
  targetChart := false
  domain := chartDomain a
  domain_subset := chartDomain_subset_pair a
  coefficient := chartCoefficient a
  holomorphicOn := chartCoefficient_holomorphicOn a
  ne_zero _ hx := chartCoefficient_ne_zero a hx
  equation _ hx := chartCoefficient_equation a hx

/-- Off S2 the original outside frame makes the source section one,
so the target's actual nonzero local coefficient gives the comparison. -/
def outsideComparison (b : Bool) :
    LocalSectionComparison IF squareData PowersBase.pullbackData squareSection
      PowersBase.pullbackSection where
  sourceChart := (none, none)
  targetChart := b
  domain := GlobalEllipticDivisor.outside ⊓
    ⟨PowersBase.pullbackData.baseSet b, PowersBase.pullbackData.isOpen_baseSet b⟩
  domain_subset _ hx := ⟨⟨hx.1, hx.1⟩, hx.2⟩
  coefficient := PowersBase.pullbackCoefficient b
  holomorphicOn := (PowersBase.pullbackCoefficient_holomorphic b).mono inter_subset_right
  ne_zero x hx := by
    rw [← PowersBase.pullbackSection_localCoefficient b hx.2,
      HolomorphicCharacterBundle.TransitionData.localCoefficient_eq]
    exact mul_ne_zero (PowersBase.pullbackData.transition_ne_zero _ _ _)
      ((PowersBase.pullbackSection_ne_zero_iff x).mpr hx.1)
  equation x hx := by
    rw [squareSection_outside_coefficient hx.1, mul_one]
    exact (PowersBase.pullbackSection_localCoefficient b hx.2).symm

/-- Every global point has a proved native local unit comparison.
The central case uses the quartic equation, not division by a zero section. -/
theorem localComparison_exists (x : Threefold.Space) :
    ∃ Q : LocalSectionComparison IF squareData PowersBase.pullbackData squareSection
      PowersBase.pullbackSection, x ∈ Q.domain := by
  by_cases hx : x ∈ GlobalEllipticDivisor.outside
  · exact ⟨outsideComparison (PowersBase.pullbackData.indexAt x),
      hx, PowersBase.pullbackData.mem_baseSet_at x⟩
  · have hs : x ∈ GlobalEllipticDivisor.support := Classical.not_not.mp hx
    let y : GlobalEllipticDivisor.patch := ⟨x, GlobalEllipticDivisor.support_subset_patch hs⟩
    exact ⟨ellipticComparison ((EllipticGeometry.nativePatchBiholomorph .four).symm y),
      chartDomain_cover y⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersElliptic
