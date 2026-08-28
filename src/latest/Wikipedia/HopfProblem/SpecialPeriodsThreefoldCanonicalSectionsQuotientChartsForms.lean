import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsQuotientCharts
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUpstairs
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackDiffeomorph

/-!
# Weighted canonical forms in the original quotient charts

The inverse pullback by the actual quotient differential takes the
upstairs weighted volume to a vector whose native downstairs-chart
coefficient is exactly the same function of the native first coordinate.
The statements concern actual canonical fibres, with explicit equality
transport where the quotient of a chosen local lift is identified with
the requested downstairs point.  No descent compatibility is assumed or
claimed here; these are the local formulas used in section descent.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalQuotientCharts

open TrianglePeriodFamily.Canonical SpecialPeriods

local notation "I" => modelWithCornersSelf ℂ Model

variable {j : Kind} (D : Equivariant.Data j) (v : Lattice) (hv : AdmissibleTwist j v)

local instance formsFamilyChartedSpace : ChartedSpace Model D.TotalSpace :=
  D.periods.totalChartedSpace

local instance formsFamilyManifold : IsManifold I ω D.TotalSpace :=
  D.periods.totalSpace_isManifold

local instance formsQuotientChartedSpace : ChartedSpace Model (D.Space v hv) :=
  D.chartedSpace v hv

local instance formsQuotientManifold : IsManifold I ω (D.Space v hv) := D.isManifold v hv

/-- The actual base of the local lift is the first native quotient coordinate. -/
theorem lift_base_coe (y x : D.Space v hv) (hx : x ∈ (chartAt Model y).source) :
    ((lift D v hv y x).1 : ℂ) = (chartAt Model y x).1 := by
  have h := familyChart_first_coordinate (fun s : Disc => (s : ℂ))
    SectionsUpstairs.disc_chart_apply D.periods (representative D v hv y)
      (lift D v hv y x) (lift_mem_familyChart D v hv y x hx)
  change (chartAt Model (representative D v hv y) (lift D v hv y x)).1 =
    ((lift D v hv y x).1 : ℂ) at h
  rw [chart_lift] at h
  exact h.symm

/-- The native first coordinate, proved to belong to the actual base disc. -/
def chartBase (y x : D.Space v hv) (hx : x ∈ (chartAt Model y).source) : Disc := by
  refine ⟨(chartAt Model y x).1, ?_⟩
  rw [← lift_base_coe D v hv y x hx]
  exact (lift D v hv y x).1.property

@[simp] theorem chartBase_coe (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    (chartBase D v hv y x hx : ℂ) = (chartAt Model y x).1 := rfl

theorem chartBase_eq_lift_base (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    chartBase D v hv y x hx = (lift D v hv y x).1 :=
  Subtype.ext (lift_base_coe D v hv y x hx).symm

/-- The inverse of the genuine differential pullback has unit coefficient
in the two matched original charts, on the entire downstairs chart source. -/
theorem inversePullback_inCoordinates (F : Disc → ℂ) (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    Atlas.inCoordinates (D.Space v hv) (achart Model y)
      (D.quotient v hv (lift D v hv y x))
      ((Pullback.pullbackEquiv (quotient_isLocalDiffeomorph D v hv)
        (lift D v hv y x)).symm
          (SectionsUpstairs.weightedSection D.periods F (lift D v hv y x))) =
      F (lift D v hv y x).1 • volume := by
  have hl := lift_mem_familyChart D v hv y x hx
  have hq : D.quotient v hv (lift D v hv y x) ∈ (chartAt Model y).source := by
    rw [quotient_lift D v hv y x hx]
    exact hx
  have h := Pullback.inCoordinates_pullbackEquiv (quotient_isLocalDiffeomorph D v hv)
    (achart Model (representative D v hv y)) (achart Model y) hl hq
      ((Pullback.pullbackEquiv (quotient_isLocalDiffeomorph D v hv)
        (lift D v hv y x)).symm
          (SectionsUpstairs.weightedSection D.periods F (lift D v hv y x)))
  rw [ContinuousLinearEquiv.apply_symm_apply, chartDerivative_eq_id D v hv y x hx] at h
  calc
    _ = Atlas.inCoordinates D.TotalSpace (achart Model (representative D v hv y))
        (lift D v hv y x)
        (SectionsUpstairs.weightedSection D.periods F (lift D v hv y x)) := h.symm
    _ = F (lift D v hv y x).1 • volume :=
      SectionsUpstairs.section_inCoordinates D.periods F (representative D v hv y)
        (lift D v hv y x) hl

/-- Native coordinates respect equality transport between the genuine
canonical fibres over equal base points. -/
theorem inCoordinates_fiberTransport {x z : D.Space v hv} (h : x = z)
    (i : atlas Model (D.Space v hv)) (w : (Atlas.core (D.Space v hv)).Fiber x) :
    Atlas.inCoordinates (D.Space v hv) i z (Pullback.fiberTransport h w) =
      Atlas.inCoordinates (D.Space v hv) i x w := by
  subst z
  rfl

/-- A local inverse-differential pushforward, in the literal fibre over `x`.
This is defined on the full source of the specified native quotient chart. -/
def nativeChartSection (F : Disc → ℂ) (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) : (Atlas.core (D.Space v hv)).Fiber x :=
  Pullback.fiberTransport (quotient_lift D v hv y x hx)
    ((Pullback.pullbackEquiv (quotient_isLocalDiffeomorph D v hv)
      (lift D v hv y x)).symm
        (SectionsUpstairs.weightedSection D.periods F (lift D v hv y x)))

theorem nativeChartSection_inCoordinates_lift (F : Disc → ℂ) (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    Atlas.inCoordinates (D.Space v hv) (achart Model y) x
      (nativeChartSection D v hv F y x hx) = F (lift D v hv y x).1 • volume := by
  rw [nativeChartSection, inCoordinates_fiberTransport]
  exact inversePullback_inCoordinates D v hv F y x hx

/-- Disc-valued coefficient functions are evaluated at the actual first
coordinate, retaining its proved membership in the original base disc. -/
theorem nativeChartSection_inCoordinates (F : Disc → ℂ) (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    Atlas.inCoordinates (D.Space v hv) (achart Model y) x
      (nativeChartSection D v hv F y x hx) = F (chartBase D v hv y x hx) • volume := by
  rw [nativeChartSection_inCoordinates_lift, chartBase_eq_lift_base]

/-- The corresponding formula for a coefficient supplied on the complex plane. -/
theorem nativeChartSection_inCoordinates_complex (F : ℂ → ℂ) (y x : D.Space v hv)
    (hx : x ∈ (chartAt Model y).source) :
    Atlas.inCoordinates (D.Space v hv) (achart Model y) x
      (nativeChartSection D v hv (fun s : Disc => F s) y x hx) =
      F (chartAt Model y x).1 • volume := by
  rw [nativeChartSection_inCoordinates, chartBase_coe]

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalQuotientCharts
