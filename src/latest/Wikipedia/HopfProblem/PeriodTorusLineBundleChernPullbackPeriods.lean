import Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullbackBasic
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyPeriodDomain
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginNaturality
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# Actual positive-period transport under compatible linear torus maps

The coordinate lattice map is derived from the genuine linear map and
the original period markings.  The induced torus map carries each
literal positive period path to the path of its image period.  Therefore
its actual singular first-homology map, and its actual ordered two-loop
Pontryagin products, have these coordinates without an assumed homology
or cohomology action.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback.LatticeLinearMap

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyPontryagin

attribute [local instance] integerLinearMapModule integerTensorModule

variable {p q : PeriodDomain} (L : LatticeLinearMap p q)

/-- The actual lattice map in the two original ordered integral period markings. -/
def coordinateMap : Lattice →ₗ[ℤ] Lattice :=
  (q.latticeEquiv.toAddMonoidHom.comp
    (L.latticeMap.toAddMonoidHom.comp p.latticeEquiv.symm.toAddMonoidHom)).toIntLinearMap

@[simp] theorem coordinateMap_apply (x : Lattice) :
    L.coordinateMap x = q.latticeEquiv (L.latticeMap (p.latticeEquiv.symm x)) := rfl

/-- Returning to the true target lattice recovers the genuine lattice image. -/
theorem coordinateMap_symm (x : Lattice) :
    q.latticeEquiv.symm (L.coordinateMap x) = L.latticeMap (p.latticeEquiv.symm x) := by
  rw [coordinateMap_apply, AddEquiv.symm_apply_apply]

/-- The marked target period is the literal image in the covering vector space. -/
theorem periodVector_coordinateMap (x : Lattice) :
    q.periodVector (L.coordinateMap x) = L.linear (p.periodVector x) := by
  rw [coordinateMap_apply, q.periodVector_latticeEquiv, latticeMap_coe]
  rfl

/-- Pointwise equality of the actual projected straight period paths. -/
theorem torusContinuousMap_periodLoop_apply (x : Lattice) (t : unitInterval) :
    L.torusContinuousMap (p.periodLoop x t) = q.periodLoop (L.coordinateMap x) t := by
  rw [p.periodLoop_apply, torusContinuousMap_mkQ, q.periodLoop_apply,
    periodVector_coordinateMap]
  change q.lattice.mkQ ((L.linear.restrictScalars ℝ) ((t : ℝ) • p.periodVector x)) = _
  rw [map_smul]
  rfl

/-- The mapped genuine path, with only its equal zero endpoints cast. -/
theorem torusContinuousMap_periodLoop (x : Lattice) :
    (p.periodLoop x).map L.torusContinuousMap.continuous =
      (q.periodLoop (L.coordinateMap x)).cast L.torusMap_zero L.torusMap_zero := by
  apply Path.ext
  funext t
  exact L.torusContinuousMap_periodLoop_apply x t

/-- Naturality on actual singular first homology preserves the positive period convention. -/
theorem torusContinuousMap_periodLoop_homology (x : Lattice) :
    singularHomologyMap L.torusContinuousMap 1 (loopHomologyClass (p.periodLoop x)) =
      loopHomologyClass (q.periodLoop (L.coordinateMap x)) := by
  rw [singularHomologyMap_one, inducedHomology_loopHomologyClass,
    torusContinuousMap_periodLoop]
  rfl

/-- The same actual map in the canonical first-homology linear markings. -/
theorem torusContinuousMap_h1_marking (x : Lattice) :
    singularHomologyMap L.torusContinuousMap 1 (p.singularH1Equiv.symm x) =
      q.singularH1Equiv.symm (L.coordinateMap x) := by
  rw [p.singularH1Equiv_symm_apply, q.singularH1Equiv_symm_apply]
  exact L.torusContinuousMap_periodLoop_homology x

/-- The actual ordered two-period product maps to the product of the two actual image paths. -/
theorem torusContinuousMap_product11_periodLoops (x y : Lattice) :
    singularHomologyMap L.torusContinuousMap 2
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) =
      product11 q.Torus (loopHomologyClass (q.periodLoop (L.coordinateMap x)))
        (loopHomologyClass (q.periodLoop (L.coordinateMap y))) := by
  change singularHomologyMap L.torusContinuousMap (1 + 1)
    (product p.Torus 1 _ _) = product q.Torus 1 _ _
  rw [product_natural L.torusContinuousMap (fun a b => L.torusMap_add a b) 1,
    torusContinuousMap_periodLoop_homology, torusContinuousMap_periodLoop_homology]

end Wikipedia.HopfProblem.PeriodTorusLineBundleChernPullback.LatticeLinearMap
