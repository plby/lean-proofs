import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsQuotientChartsForms
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsDescentAction

/-!
# Native-chart coefficients of genuinely descended canonical sections

Fibre compatibility identifies the actual globally descended section
with the inverse-differential pushforward along every native quotient
chart lift.  Thus its native coefficient is proved from the differential
and the original atlases, rather than supplied as descent data.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalQuotientCharts

open TrianglePeriodFamily.Canonical SpecialPeriods

local notation "I" => modelWithCornersSelf ℂ Model

variable {j : Kind} (D : Equivariant.Data j) (v : Lattice) (hv : AdmissibleTwist j v)

local instance descentFamilyChartedSpace : ChartedSpace Model D.TotalSpace :=
  D.periods.totalChartedSpace

local instance descentFamilyManifold : IsManifold I ω D.TotalSpace :=
  D.periods.totalSpace_isManifold

local instance descentQuotientChartedSpace : ChartedSpace Model (D.Space v hv) :=
  D.chartedSpace v hv

local instance descentQuotientManifold : IsManifold I ω (D.Space v hv) := D.isManifold v hv

/-- The actual canonical section produced by fibrewise descent through the
original finite quotient, not an assigned local coefficient function. -/
abbrev descendedWeightedSection (F : Disc → ℂ) : SectionsDescent.Section (D.Space v hv) :=
  SectionsDescent.descendedSection (quotient_isLocalDiffeomorph D v hv)
    (D.quotient_surjective v hv) (SectionsUpstairs.weightedSection D.periods F)

private theorem section_fiberTransport (s : SectionsDescent.Section (D.Space v hv))
    {x z : D.Space v hv} (h : x = z) : Pullback.fiberTransport h (s x) = s z := by
  subst z
  rfl

/-- Every native chart lift computes the same actual descended vector. -/
theorem descendedWeightedSection_eq_nativeChartSection (F : Disc → ℂ)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods F))
    (y x : D.Space v hv) (hx : x ∈ (chartAt Model y).source) :
    descendedWeightedSection D v hv F x = nativeChartSection D v hv F y x hx := by
  have he := SectionsDescent.descendedSection_at_image
    (quotient_isLocalDiffeomorph D v hv) (D.quotient_surjective v hv)
    (SectionsUpstairs.weightedSection D.periods F) hs (lift D v hv y x)
  calc
    _ = Pullback.fiberTransport (quotient_lift D v hv y x hx)
        (descendedWeightedSection D v hv F (D.quotient v hv (lift D v hv y x))) :=
      (section_fiberTransport D v hv (descendedWeightedSection D v hv F)
        (quotient_lift D v hv y x hx)).symm
    _ = nativeChartSection D v hv F y x hx :=
      congrArg (Pullback.fiberTransport (quotient_lift D v hv y x hx)) he

/-- The full top-covector formula for the genuine descended section on
the entire source of every native quotient chart. -/
theorem descendedWeightedSection_inCoordinates (F : Disc → ℂ)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods F))
    (y x : D.Space v hv) (hx : x ∈ (chartAt Model y).source) :
    Atlas.inCoordinates (D.Space v hv) (achart Model y) x
      (descendedWeightedSection D v hv F x) = F (chartBase D v hv y x hx) • volume := by
  rw [descendedWeightedSection_eq_nativeChartSection D v hv F hs y x hx]
  exact nativeChartSection_inCoordinates D v hv F y x hx

/-- The scalar coefficient is extracted from the actual native-chart top
covector, by evaluating it on the genuine base-first model basis. -/
def descendedChartCoefficient (F : Disc → ℂ) (y x : D.Space v hv) : ℂ :=
  coefficient (Atlas.inCoordinates (D.Space v hv) (achart Model y) x
    (descendedWeightedSection D v hv F x))

theorem descendedChartCoefficient_eq (F : Disc → ℂ)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods F))
    (y x : D.Space v hv) (hx : x ∈ (chartAt Model y).source) :
    descendedChartCoefficient D v hv F y x = F (chartBase D v hv y x hx) := by
  rw [descendedChartCoefficient, descendedWeightedSection_inCoordinates D v hv F hs y x hx]
  simp only [coefficient_smul, coefficient_volume, mul_one]

theorem descendedChartCoefficient_eq_lift (F : Disc → ℂ)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods F))
    (y x : D.Space v hv) (hx : x ∈ (chartAt Model y).source) :
    descendedChartCoefficient D v hv F y x = F (lift D v hv y x).1 := by
  rw [descendedChartCoefficient_eq D v hv F hs y x hx, chartBase_eq_lift_base]

/-- A native chart detects zeros of the actual descended canonical vector
by zeros of the coefficient on the actual base disc. -/
theorem descendedWeightedSection_eq_zero_iff (F : Disc → ℂ)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods F))
    (y x : D.Space v hv) (hx : x ∈ (chartAt Model y).source) :
    descendedWeightedSection D v hv F x = 0 ↔ F (chartBase D v hv y x hx) = 0 := by
  have he := (Atlas.coordinateEquiv (D.Space v hv) (achart Model y) hx).map_eq_zero_iff
    (x := descendedWeightedSection D v hv F x)
  change Atlas.inCoordinates (D.Space v hv) (achart Model y) x
    (descendedWeightedSection D v hv F x) = 0 ↔ descendedWeightedSection D v hv F x = 0 at he
  rw [descendedWeightedSection_inCoordinates D v hv F hs y x hx] at he
  simpa only [smul_eq_zero, volume_ne_zero, or_false] using he.symm

theorem descendedWeightedSection_ne_zero_iff (F : Disc → ℂ)
    (hs : SectionsDescent.Compatible (quotient_isLocalDiffeomorph D v hv)
      (SectionsUpstairs.weightedSection D.periods F))
    (y x : D.Space v hv) (hx : x ∈ (chartAt Model y).source) :
    descendedWeightedSection D v hv F x ≠ 0 ↔ F (chartBase D v hv y x hx) ≠ 0 :=
  (descendedWeightedSection_eq_zero_iff D v hv F hs y x hx).not

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalQuotientCharts
