import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicCoordinateFractions
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicDoubleFractions
import Wikipedia.HopfProblem.HolomorphicMeromorphicProductDescent
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Actual local base germs from equality on the double regular cover

Every genuine local fraction on the original cover is expressed in its
original coordinates and restricted to an actual small product of balls.
Equality of the native double-cover pullbacks gives all cross products
on that box. Native product descent then supplies a meromorphic base
germ, and functoriality of the actual stalk pullbacks identifies its
pullback with the original germ.
-/

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover

open HolomorphicForms.RegularCover HolomorphicMeromorphic

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] coverChartedSpace cover_isManifold
  doubleCoverChartedSpace doubleCover_isManifold

/-- The actual original complex coordinate of the free regular base. -/
noncomputable def baseCoordinateMap : ContMDiffMap IF I₁ Cover ℂ ω :=
  (ProductDescent.fstMap (E := ComplexPlane₂)).comp coordMap

@[simp] theorem baseCoordinateMap_apply (x : Cover) :
    baseCoordinateMap x = (x.1.val : ℂ) := rfl

theorem baseCoordinateMap_isOpenMap : IsOpenMap baseCoordinateMap :=
  (ProductDescent.fstMap_isOpenMap (E := ComplexPlane₂)).comp coordMap_isOpenMap

/-- Original image witnesses recover two native cover points with the
same free base point. The native double-cover identity therefore gives
the corresponding coordinate-section cross product. -/
theorem coordinate_local_fraction_cross_product
    (s : HolomorphicMeromorphic.Function IF Cover)
    (hs : leftPullback s = rightPullback s) (U : Opens Cover)
    (p q : HolomorphicFunctionSheaf.Section IF Cover U)
    (hq : ∀ x : U, holomorphicGerm IF Cover U x q ≠ 0)
    (hrep : ∀ x : U, s ⟨x.val, by trivial⟩ = fraction IF Cover U p q x)
    (a b : coordOpen U) (hbase : a.val.1 = b.val.1) :
    coordinateSection U p a * coordinateSection U q b =
      coordinateSection U p b * coordinateSection U q a := by
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  obtain ⟨⟨z, v⟩, hzv, rfl⟩ := ha
  obtain ⟨⟨z', w⟩, hzw, rfl⟩ := hb
  have hzz : z = z' := Subtype.ext (UpperHalfPlane.coe_injective hbase)
  subst z'
  change sectionCoordinates U p (coord (z, v)) * sectionCoordinates U q (coord (z, w)) =
    sectionCoordinates U p (coord (z, w)) * sectionCoordinates U q (coord (z, v))
  rw [sectionCoordinates_apply U p ⟨(z, v), hzv⟩,
    sectionCoordinates_apply U q ⟨(z, w), hzw⟩,
    sectionCoordinates_apply U p ⟨(z, w), hzw⟩,
    sectionCoordinates_apply U q ⟨(z, v), hzv⟩]
  exact local_fraction_cross_product s hs U p q hq hrep z v w hzv hzw

/-- Every native coordinate neighborhood contains an actual product of
positive-radius balls around the specified coordinate point. -/
theorem exists_coordinate_product_box (U : Opens Cover) (x : U) :
    ∃ (B : Opens ℂ) (V : Opens ComplexPlane₂),
      Nonempty B ∧ PreconnectedSpace B ∧ Nonempty V ∧
        ProductDescent.box B V ≤ coordOpen U ∧ coord x.val ∈ ProductDescent.box B V := by
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp (coordOpen U).isOpen)
    (coord x.val) (coordinatePoint U x).property
  let B : Opens ℂ := ⟨Metric.ball (coord x.val).1 r, Metric.isOpen_ball⟩
  let V : Opens ComplexPlane₂ := ⟨Metric.ball (coord x.val).2 r, Metric.isOpen_ball⟩
  have hbox : ProductDescent.box B V ≤ coordOpen U := by
    intro y hy
    apply hball
    change y ∈ Metric.ball (coord x.val).1 r ×ˢ Metric.ball (coord x.val).2 r at hy
    simpa only [ball_prod_same] using hy
  refine ⟨B, V, ⟨⟨(coord x.val).1, Metric.mem_ball_self hr⟩⟩, ?_,
    ⟨⟨(coord x.val).2, Metric.mem_ball_self hr⟩⟩, hbox, ?_⟩
  · exact isPreconnected_iff_preconnectedSpace.mp Metric.isPreconnected_ball
  · exact ⟨Metric.mem_ball_self hr, Metric.mem_ball_self hr⟩

/-- Equality of the actual double-cover pullbacks gives, at every native
cover point, a genuine meromorphic germ of the original complex base
whose actual pullback is the prescribed cover germ. -/
theorem exists_base_germ_of_double_cover_eq
    (s : HolomorphicMeromorphic.Function IF Cover)
    (hs : leftPullback s = rightPullback s) (x : Cover) :
    ∃ a : Germ I₁ ℂ (x.1.val : ℂ),
      germPullback IF I₁ baseCoordinateMap baseCoordinateMap_isOpenMap x a =
        s ⟨x, by trivial⟩ := by
  obtain ⟨U, _hUtop, hxU, p, q, hq, hrep⟩ :=
    local_representation IF Cover s ⟨x, by trivial⟩
  have hrep' : ∀ y : U, s ⟨y.val, by trivial⟩ = fraction IF Cover U p q y := hrep
  let xu : U := ⟨x, hxU⟩
  obtain ⟨B, V, hBne, hBconn, hVne, hW, hxW⟩ := exists_coordinate_product_box U xu
  let : Nonempty B := hBne
  let : PreconnectedSpace B := hBconn
  let : Nonempty V := hVne
  let pW : HolomorphicFunctionSheaf.Section IF Model (ProductDescent.box B V) :=
    HolomorphicFunctionSheaf.restrictionAlgHom IF Model hW (coordinateSection U p)
  let qW : HolomorphicFunctionSheaf.Section IF Model (ProductDescent.box B V) :=
    HolomorphicFunctionSheaf.restrictionAlgHom IF Model hW (coordinateSection U q)
  have hqW : ∀ y : ProductDescent.box B V,
      holomorphicGerm IF Model (ProductDescent.box B V) y qW ≠ 0 := by
    intro y hy
    apply coordinateSection_nonzero_germs U q hq (Set.inclusion hW y)
    exact (holomorphicGerm_restrict IF Model hW y (coordinateSection U q)).symm.trans hy
  have hcrossW : ∀ (z : B) (v w : V),
      pW (ProductDescent.boxPoint B V z v) * qW (ProductDescent.boxPoint B V z w) =
        pW (ProductDescent.boxPoint B V z w) * qW (ProductDescent.boxPoint B V z v) := by
    intro z v w
    exact coordinate_local_fraction_cross_product s hs U p q hq hrep'
      (Set.inclusion hW (ProductDescent.boxPoint B V z v))
      (Set.inclusion hW (ProductDescent.boxPoint B V z w)) rfl
  obtain ⟨g, hg⟩ := ProductDescent.exists_descended_section_germs B V pW qW hqW hcrossW
  let ξ : ProductDescent.box B V := ⟨coord x, hxW⟩
  let a : Germ I₁ ℂ (x.1.val : ℂ) := g (ProductDescent.basePoint B V ξ)
  have hlocal : germPullback IF IF coordMap coordMap_isOpenMap x
      (fraction IF Model (ProductDescent.box B V) pW qW ξ) = fraction IF Cover U p q xu := by
    have hrestr := fraction_restrict IF Model hW (coordinateSection U p) (coordinateSection U q) ξ
    exact (congrArg (germPullback IF IF coordMap coordMap_isOpenMap x) hrestr).trans
      (germPullback_coordinateFraction U p q hq xu)
  refine ⟨a, ?_⟩
  exact (germPullback_comp_apply IF IF I₁ coordMap coordMap_isOpenMap
    ProductDescent.fstMap ProductDescent.fstMap_isOpenMap x a).symm.trans
      ((congrArg (germPullback IF IF coordMap coordMap_isOpenMap x) (hg ξ)).trans
        (hlocal.trans (hrep' xu).symm))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicRegularCover
