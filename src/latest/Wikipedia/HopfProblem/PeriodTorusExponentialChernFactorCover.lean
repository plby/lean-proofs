import Wikipedia.HopfProblem.PeriodTorusExponentialChernBasic
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernTransitions

/-!
# Original native factor-bundle logarithms as actual sheaf sections

The original factor core has its original quotient-chart cover and
preferred index equal to the base point.  Its native unit cocycle is
therefore the actual coordinate transition, whose existing holomorphic
logarithm is bundled here on the unchanged chart overlaps.
-/

noncomputable section

open Bundle TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open HolomorphicExponentialSheaf HolomorphicPicardNative
  HolomorphicFunctionSheaf.SphereH1 PeriodTorusLineBundleClassificationNative
  PeriodTorusAppellHumbert

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The original quotient-chart cover of the original torus. -/
def chartCover (p : PeriodDomain) (i : p.Torus) : Opens p.Torus :=
  ⟨Core.baseSet p i, Core.isOpen_baseSet p i⟩

theorem chartCover_covers (p : PeriodDomain) (x : p.Torus) :
    ∃ i, x ∈ chartCover p i := ⟨x, Core.mem_baseSet p x⟩

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The factor bundle's original preferred native cover is exactly this cover. -/
theorem factor_nativeCover (i : p.Torus) :
    nativeCover p.Torus (Core.data F).core.Fiber i = chartCover p i := rfl

/-- The original native unit cocycle, on its definitionally original cover. -/
abbrev factorNativeCocycle : CechOneCocycle (unitsSheaf IC p.Torus) (chartCover p) :=
  nativeCocycle IC p.Torus (Core.data F).core.Fiber

/-- Evaluating the original native unit cocycle recovers the original
holomorphic coordinate logarithm's ordinary exponential. -/
theorem factorNativeCocycle_eval (i j : p.Torus)
    (x : ↥(chartCover p i ⊓ chartCover p j)) :
    unitSectionEval ((factorNativeCocycle F).value i j) x =
      Complex.exp (PeriodTorusLineBundle.Chern.coordinateLog F i j x) := by
  rw [PeriodTorusLineBundle.Chern.coordinateLog_exp]
  change (scalarTransition (Core.data F).core.Fiber i j x : ℂ) = _
  rw [scalarTransition_coe]
  change ((Core.data F).core.localTriv i).coordChangeL ℂ
    ((Core.data F).core.localTriv j) x 1 = _
  rw [(Core.data F).core_localTriv_coordChange i j x.property]
  exact mul_one _

/-- The existing coordinate logarithm is an actual holomorphic section
on the original native overlap. -/
def coordinateLogSection (i j : p.Torus) :
    HolomorphicFunctionSheaf.Section IC p.Torus (chartCover p i ⊓ chartCover p j) :=
  ⟨fun x => PeriodTorusLineBundle.Chern.coordinateLog F i j x, by
    intro x
    have h := (PeriodTorusLineBundle.Chern.coordinateLog_holomorphic F i j).contMDiffAt
      (((Core.isOpen_baseSet p i).inter (Core.isOpen_baseSet p j)).mem_nhds x.property)
    exact (contMDiffAt_subtype_iff
      (f := PeriodTorusLineBundle.Chern.coordinateLog F i j) (x := x)).mpr h⟩

@[simp] theorem coordinateLogSection_apply (i j : p.Torus)
    (x : ↥(chartCover p i ⊓ chartCover p j)) :
    coordinateLogSection F i j x = PeriodTorusLineBundle.Chern.coordinateLog F i j x := rfl

/-- The literal original sheaf exponential of the actual logarithm is
the original native transition section, with no inverse convention. -/
theorem coordinateLogSection_exponential (i j : p.Torus) :
    (exponential IC p.Torus).hom.app (op (chartCover p i ⊓ chartCover p j))
      (coordinateLogSection F i j) = (factorNativeCocycle F).value i j := by
  apply unitSection_ext
  intro x
  exact (factorNativeCocycle_eval F i j x).symm

/-- The cocycle class here is literally the original native bundle class. -/
theorem factorNativeCocycle_class :
    HolomorphicPicard.CechExtension.classOf (factorNativeCocycle F) (chartCover_covers p) =
      HolomorphicPicard.nativeClass IC p.Torus (Core.data F).core.Fiber := rfl

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
