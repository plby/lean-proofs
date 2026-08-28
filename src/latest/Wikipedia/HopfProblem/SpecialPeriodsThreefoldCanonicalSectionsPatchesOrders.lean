import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsPatchesOrdersCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsSpecialOrders

/-!
# Exact canonical-section orders on the actual global elliptic patches

The transverse coefficient below is extracted from the genuine global
canonical section in a chart of the actual glued atlas.  Its transverse
points are the inverse of that very glued chart, codrestricted to the
actual patch.  Equality with the full-filling transverse germ follows
from the identity derivative in matching native and glued charts.
Consequently the order at every point of the two actual central sphere
fibres is respectively zero and two.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  Threefold.chartedSpace

local instance patchOrdersFullManifold (j : Kind) :
    IsManifold IF ω (SpecialFullFilling j) := (specialFullFilling_construction j).2.2.1

local instance patchOrdersSmallManifold (j : Kind) :
    IsManifold IF ω (SpecialEllipticPiece j) := specialEllipticPiece_isManifold j

local instance patchOrdersGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- The actual native elliptic point corresponding to a point of the full global patch. -/
def nativePatchPoint (j : Kind) (y : Threefold.liftedPatch (some (some j))) :
    SpecialEllipticPiece j := (EllipticGeometry.nativePatchBiholomorph j).symm y

@[simp] theorem nativePatchPoint_inclusion (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    EllipticGeometry.inclusion j (nativePatchPoint j y) = y.val :=
  congrArg Subtype.val ((EllipticGeometry.nativePatchBiholomorph j).apply_symm_apply y)

/-- The matching chart is an index of the actual global glued atlas. -/
def patchSectionChart (j : Kind) (y : Threefold.liftedPatch (some (some j))) :
    atlas Model Threefold.Space :=
  Threefold.Canonical.patchChart (some (some j)) (nativePatchPoint j y)

theorem patchSectionChart_center (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    (patchSectionChart j y).val y.val =
      chartAt Model (nativePatchPoint j y) (nativePatchPoint j y) := by
  calc
    _ = (patchSectionChart j y).val
        (EllipticGeometry.inclusion j (nativePatchPoint j y)) :=
      congrArg (patchSectionChart j y).val (nativePatchPoint_inclusion j y).symm
    _ = _ := Threefold.Canonical.patchChart_inclusion (some (some j)) _ _

/-- The actual inverse-chart transverse line, with values in the literal global patch. -/
def patchTransversePoint (j : Kind) (y : Threefold.liftedPatch (some (some j))) (z : ℂ) :
    Threefold.liftedPatch (some (some j)) :=
  EllipticGeometry.nativePatchBiholomorph j
    ((chartAt Model (nativePatchPoint j y)).symm
      (z, (chartAt Model (nativePatchPoint j y) (nativePatchPoint j y)).2))

/-- The point is literally the inverse of the specified global chart,
not merely a different transverse parameterization with the same order. -/
theorem patchTransversePoint_val (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) (z : ℂ) :
    (patchTransversePoint j y z).val = (patchSectionChart j y).val.symm
      (z, ((patchSectionChart j y).val y.val).2) := by
  rw [patchSectionChart_center]
  exact (patchChart_symm_native j (nativePatchPoint j y)
    (z, (chartAt Model (nativePatchPoint j y) (nativePatchPoint j y)).2)).symm

@[simp] theorem patchTransversePoint_center (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    patchTransversePoint j y ((patchSectionChart j y).val y.val).1 = y := by
  rw [patchSectionChart_center]
  change EllipticGeometry.nativePatchBiholomorph j
    ((chartAt Model (nativePatchPoint j y)).symm
      (chartAt Model (nativePatchPoint j y) (nativePatchPoint j y))) = y
  rw [(chartAt Model (nativePatchPoint j y)).left_inv
    (mem_chart_source Model (nativePatchPoint j y))]
  exact (EllipticGeometry.nativePatchBiholomorph j).apply_symm_apply y

/-- The scalar coefficient of the genuine global canonical section
in its actual glued chart along its actual transverse inverse-chart line. -/
def patchTransverseCoefficient (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) (z : ℂ) : ℂ :=
  coefficient (Threefold.Canonical.inCoordinates (patchSectionChart j y)
    (patchTransversePoint j y z).val (patchSection j (patchTransversePoint j y z)))

theorem native_transverse_mem_target_eventually (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    ∀ᶠ z in 𝓝 (chartAt Model (nativePatchPoint j y) (nativePatchPoint j y)).1,
      (z, (chartAt Model (nativePatchPoint j y) (nativePatchPoint j y)).2) ∈
        (chartAt Model (nativePatchPoint j y)).target := by
  let a := nativePatchPoint j y
  have ht : (chartAt Model a).target ∈ 𝓝 ((chartAt Model a a).1, (chartAt Model a a).2) :=
    (chartAt Model a).open_target.mem_nhds (mem_chart_target Model a)
  have hc : ContinuousAt (fun z : ℂ => (z, (chartAt Model a a).2))
      (chartAt Model a a).1 := continuousAt_id.prodMk continuousAt_const
  exact hc ht

/-- Near the centre, the actual curve lies in the source of its actual global chart. -/
theorem patchTransversePoint_mem_source_eventually (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    ∀ᶠ z in 𝓝 (chartAt Model (nativePatchPoint j y) (nativePatchPoint j y)).1,
      (patchTransversePoint j y z).val ∈ (patchSectionChart j y).val.source := by
  filter_upwards [native_transverse_mem_target_eventually j y] with z hz
  exact Threefold.Canonical.inclusion_mem_patchChart_source (some (some j))
    (nativePatchPoint j y) _ ((chartAt Model (nativePatchPoint j y)).map_target hz)

theorem patchTransversePoint_chart_eventuallyEq (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    (fun z : ℂ => (patchSectionChart j y).val (patchTransversePoint j y z).val) =ᶠ[
      𝓝 (chartAt Model (nativePatchPoint j y) (nativePatchPoint j y)).1]
        (fun z => (z, (chartAt Model (nativePatchPoint j y) (nativePatchPoint j y)).2)) := by
  filter_upwards [native_transverse_mem_target_eventually j y] with z hz
  exact (Threefold.Canonical.patchChart_inclusion (some (some j))
    (nativePatchPoint j y) _).trans ((chartAt Model (nativePatchPoint j y)).right_inv hz)

/-- Matching native and glued charts give equality of the actual
global-section coefficient and the actual full-filling coefficient as germs. -/
theorem patchTransverseCoefficient_eventuallyEq (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    patchTransverseCoefficient j y =ᶠ[
      𝓝 (chartAt Model (nativePatchPoint j y) (nativePatchPoint j y)).1]
        fullTransverseCoefficient j (nativePatchPoint j y).val := by
  let a := nativePatchPoint j y
  filter_upwards [native_transverse_mem_target_eventually j y] with z hz
  have hc := patchSection_inCoordinates j a
    ((chartAt Model a).symm (z, (chartAt Model a a).2))
    ((chartAt Model a).map_target hz)
  have he := congrArg coefficient hc
  rw [smallChart_symm_val j a hz] at he
  exact he

/-- The native point is central exactly when its actual global sphere
projection is the corresponding normalized elliptic value. -/
theorem nativePatchPoint_central_iff (j : Kind)
    (y : Threefold.liftedPatch (some (some j))) :
    specialFullFillingProjection j (nativePatchPoint j y).val =
        Wikipedia.HopfProblem.Elliptic.discZero ↔
      Threefold.projectionSphere y.val = EllipticGeometry.sphereValue j := by
  rw [← nativePatchPoint_inclusion j y,
    EllipticGeometry.projectionSphere_inclusion_eq_value_iff]
  constructor
  · exact congrArg (fun s : Disc => (s : ℂ))
  · exact fun h => Subtype.ext h

theorem nativePatchPoint_chart_first_eq_zero (j : Kind)
    (y : Threefold.liftedPatch (some (some j)))
    (hy : Threefold.projectionSphere y.val = EllipticGeometry.sphereValue j) :
    (chartAt Model (nativePatchPoint j y) (nativePatchPoint j y)).1 = 0 :=
  (specialFullFilling_central_chart j (nativePatchPoint j y).val (nativePatchPoint j y).val
    (mem_chart_source Model (nativePatchPoint j y).val)).mp
      ((nativePatchPoint_central_iff j y).mpr hy)

theorem patchTransverseCoefficient_eventuallyEq_zero (j : Kind)
    (y : Threefold.liftedPatch (some (some j)))
    (hy : Threefold.projectionSphere y.val = EllipticGeometry.sphereValue j) :
    patchTransverseCoefficient j y =ᶠ[𝓝 (0 : ℂ)]
      fullTransverseCoefficient j (nativePatchPoint j y).val := by
  simpa only [nativePatchPoint_chart_first_eq_zero j y hy] using
    patchTransverseCoefficient_eventuallyEq j y

/-- The true global transverse germ is analytic at every central point. -/
theorem patchTransverseCoefficient_analyticAt (j : Kind)
    (y : Threefold.liftedPatch (some (some j)))
    (hy : Threefold.projectionSphere y.val = EllipticGeometry.sphereValue j) :
    AnalyticAt ℂ (patchTransverseCoefficient j y) 0 :=
  (fullTransverseCoefficient_analyticAt j (nativePatchPoint j y).val
    ((nativePatchPoint_central_iff j y).mpr hy)).congr
      (patchTransverseCoefficient_eventuallyEq_zero j y hy).symm

theorem patchTransverseCoefficient_factorization (j : Kind)
    (y : Threefold.liftedPatch (some (some j)))
    (hy : Threefold.projectionSphere y.val = EllipticGeometry.sphereValue j) :
    patchTransverseCoefficient j y =ᶠ[𝓝 (0 : ℂ)]
      (fun z : ℂ => z ^ SectionsUnit.vanishingOrder j *
        SectionsUnit.discExtension (SectionsUnit.specialUnit j) z) :=
  (patchTransverseCoefficient_eventuallyEq_zero j y hy).trans
    (fullTransverseCoefficient_factorization j (nativePatchPoint j y).val
      ((nativePatchPoint_central_iff j y).mpr hy))

/-- Exact order of the actual section in the actual global glued chart,
at every point of the full central elliptic patch. -/
theorem patchTransverseCoefficient_analyticOrderAt (j : Kind)
    (y : Threefold.liftedPatch (some (some j)))
    (hy : Threefold.projectionSphere y.val = EllipticGeometry.sphereValue j) :
    analyticOrderAt (patchTransverseCoefficient j y) 0 =
      (SectionsUnit.vanishingOrder j : ℕ∞) :=
  (analyticOrderAt_congr (patchTransverseCoefficient_eventuallyEq_zero j y hy)).trans
    (fullTransverseCoefficient_analyticOrderAt j (nativePatchPoint j y).val
      ((nativePatchPoint_central_iff j y).mpr hy))

theorem patchTransverseCoefficient_three_order
    (y : Threefold.liftedPatch (some (some .three)))
    (hy : Threefold.projectionSphere y.val = ((0 : ℂ) : RiemannSphere)) :
    analyticOrderAt (patchTransverseCoefficient .three y) 0 = 0 :=
  patchTransverseCoefficient_analyticOrderAt .three y
    (hy.trans EllipticGeometry.sphereValue_three.symm)

theorem patchTransverseCoefficient_four_order
    (y : Threefold.liftedPatch (some (some .four)))
    (hy : Threefold.projectionSphere y.val = ((1 : ℂ) : RiemannSphere)) :
    analyticOrderAt (patchTransverseCoefficient .four y) 0 = 2 :=
  patchTransverseCoefficient_analyticOrderAt .four y
    (hy.trans EllipticGeometry.sphereValue_four.symm)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections
