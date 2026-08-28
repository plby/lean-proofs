import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Actual analytic maps of period tori induced by compatible linear maps

A complex continuous linear map carrying the source lattice into the target
lattice induces a map of the actual quotient tori.  Its analyticity is
proved in their existing quotient atlases by descent through the covering
projection.  Neither a torus map nor any map on cohomology is an input.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback

/-- A genuine complex linear map compatible with the two actual period lattices. -/
structure LatticeLinearMap (p q : PeriodDomain) where
  linear : ComplexPlane₂ →L[ℂ] ComplexPlane₂
  map_lattice : ∀ l : p.lattice, linear l ∈ q.lattice

namespace LatticeLinearMap

variable {p q : PeriodDomain} (L : LatticeLinearMap p q)

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

/-- The induced integral linear map of the actual lattices. -/
def latticeMap : p.lattice →ₗ[ℤ] q.lattice where
  toFun l := ⟨L.linear l, L.map_lattice l⟩
  map_add' l m := Subtype.ext (map_add L.linear (l : ComplexPlane₂) (m : ComplexPlane₂))
  map_smul' n l := by
    apply Subtype.ext
    change (L.linear.toLinearMap.restrictScalars ℤ) (n • (l : ComplexPlane₂)) =
      n • (L.linear.toLinearMap.restrictScalars ℤ) (l : ComplexPlane₂)
    exact map_smul _ _ _

@[simp] theorem latticeMap_coe (l : p.lattice) :
    (L.latticeMap l : ComplexPlane₂) = L.linear l := rfl

theorem linear_add_lattice (z : ComplexPlane₂) (l : p.lattice) :
    L.linear (z + l) = L.linear z + (L.latticeMap l : ComplexPlane₂) :=
  map_add L.linear z l

/-- The actual quotient linear map, constructed from the compatibility proof. -/
def torusLinearMap : p.Torus →ₗ[ℤ] q.Torus :=
  p.lattice.mapQ q.lattice (L.linear.toLinearMap.restrictScalars ℤ)
    (fun z hz => L.map_lattice ⟨z, hz⟩)

@[simp] theorem torusLinearMap_mkQ (z : ComplexPlane₂) :
    L.torusLinearMap (p.lattice.mkQ z) = q.lattice.mkQ (L.linear z) := rfl

/-- Analyticity follows from the actual analytic covering projections. -/
theorem torusLinearMap_holomorphic : ContMDiff IC IC ω L.torusLinearMap := by
  apply DiscreteQuotient.contMDiff_of_comp_mkQ p.lattice IC ω
  exact q.torus_projection_holomorphic.comp L.linear.contDiff.contMDiff

/-- The descended map with its proved holomorphicity. -/
def torusMap : ContMDiffMap IC IC p.Torus q.Torus ω :=
  ⟨L.torusLinearMap, L.torusLinearMap_holomorphic⟩

@[simp] theorem torusMap_apply (x : p.Torus) : L.torusMap x = L.torusLinearMap x := rfl

@[simp] theorem torusMap_mkQ (z : ComplexPlane₂) :
    L.torusMap (p.lattice.mkQ z) = q.lattice.mkQ (L.linear z) := rfl

@[simp] theorem torusMap_zero : L.torusMap 0 = 0 := map_zero L.torusLinearMap

theorem torusMap_add (x y : p.Torus) :
    L.torusMap (x + y) = L.torusMap x + L.torusMap y := map_add L.torusLinearMap x y

/-- The same actual map, bundled for native singular pullback. -/
def torusContinuousMap : C(p.Torus, q.Torus) :=
  ⟨L.torusLinearMap, L.torusLinearMap_holomorphic.continuous⟩

@[simp] theorem torusContinuousMap_apply (x : p.Torus) :
    L.torusContinuousMap x = L.torusMap x := rfl

@[simp] theorem torusContinuousMap_mkQ (z : ComplexPlane₂) :
    L.torusContinuousMap (p.lattice.mkQ z) = q.lattice.mkQ (L.linear z) := rfl

end LatticeLinearMap

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback
