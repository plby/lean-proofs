import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMatrixMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTranslations
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTopology

/-!
# Circle fibres of actual integral four-torus maps

Splitting off the first circle conjugates an integral four-torus map to
a map of a circle times a three-torus.  If its first row is the first
coordinate functional, the conjugated map preserves the circle.  On
each fixed-circle fibre its second component is the actual tail matrix
map followed by translation.  Translation invariance therefore identifies
its actual singular homology map with the tail matrix map in every degree.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomology.CircleTopology

/-- The literal three-by-three tail block of the integral four-torus matrix. -/
def topDegreeTailMatrix (A : Matrix (Fin 4) (Fin 4) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  A.submatrix Fin.succ Fin.succ

@[simp] theorem topDegreeTailMatrix_apply (A : Matrix (Fin 4) (Fin 4) ℤ) (i j : Fin 3) :
    topDegreeTailMatrix A i j = A i.succ j.succ := rfl

/-- The actual torus matrix map in the first-circle splitting homeomorphism. -/
def topDegreeCircleMap (A : Matrix (Fin 4) (Fin 4) ℤ) :
    C(Circle × ProductTorus 3, Circle × ProductTorus 3) :=
  (productTorusSuccHomeomorph 3 : C(_, _)).comp
    ((torusMatrixMap A).comp ((productTorusSuccHomeomorph 3).symm : C(_, _)))

@[simp] theorem topDegreeCircleMap_apply (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : Circle × ProductTorus 3) :
    topDegreeCircleMap A z = productTorusSuccHomeomorph 3
      (torusMatrixMap A ((productTorusSuccHomeomorph 3).symm z)) := rfl

@[simp] theorem topDegreeCircleMap_homeomorph (A : Matrix (Fin 4) (Fin 4) ℤ)
    (x : ProductTorus 4) :
    topDegreeCircleMap A (productTorusSuccHomeomorph 3 x) =
      productTorusSuccHomeomorph 3 (torusMatrixMap A x) := by
  rw [topDegreeCircleMap_apply, Homeomorph.symm_apply_apply]

/-- The conjugation identity as an equality of actual continuous maps. -/
theorem topDegreeCircleMap_comp_homeomorph (A : Matrix (Fin 4) (Fin 4) ℤ) :
    (topDegreeCircleMap A).comp (productTorusSuccHomeomorph 3 : C(_, _)) =
      (productTorusSuccHomeomorph 3 : C(_, _)).comp (torusMatrixMap A) := by
  apply ContinuousMap.ext
  intro x
  exact topDegreeCircleMap_homeomorph A x

/-- The first-row condition makes the actual first circle coordinate fixed. -/
theorem topDegreeCircleMap_fst (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0) (z : Circle × ProductTorus 3) :
    (topDegreeCircleMap A z).1 = z.1 := by
  change (∑ j : Fin 4, A 0 j • Fin.cons z.1 z.2 j) = z.1
  simp [hA]

/-- The second component is the tail matrix map plus the first-column translation. -/
theorem topDegreeCircleMap_snd (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : Circle × ProductTorus 3) (i : Fin 3) :
    (topDegreeCircleMap A z).2 i =
      torusMatrixMap (topDegreeTailMatrix A) z.2 i + A i.succ 0 • z.1 := by
  change (∑ j : Fin 4, A i.succ j • Fin.cons z.1 z.2 j) =
    (∑ j : Fin 3, A i.succ j.succ • z.2 j) + A i.succ 0 • z.1
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact add_comm _ _

/-- The literal section obtained by fixing the first circle coordinate. -/
def topDegreeCircleSection (z : Circle) : C(ProductTorus 3, Circle × ProductTorus 3) :=
  ⟨fun x => (z, x), continuous_const.prodMk continuous_id⟩

@[simp] theorem topDegreeCircleSection_apply (z : Circle) (x : ProductTorus 3) :
    topDegreeCircleSection z x = (z, x) := rfl

/-- The actual second component of the conjugated map on the specified circle fibre. -/
def topDegreeFibreMap (A : Matrix (Fin 4) (Fin 4) ℤ) (z : Circle) :
    C(ProductTorus 3, ProductTorus 3) :=
  ContinuousMap.snd.comp ((topDegreeCircleMap A).comp (topDegreeCircleSection z))

@[simp] theorem topDegreeFibreMap_apply (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : Circle) (x : ProductTorus 3) :
    topDegreeFibreMap A z x = (topDegreeCircleMap A (z, x)).2 := rfl

theorem topDegreeFibreMap_apply_coordinate (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : Circle) (x : ProductTorus 3) (i : Fin 3) :
    topDegreeFibreMap A z x i =
      torusMatrixMap (topDegreeTailMatrix A) x i + A i.succ 0 • z :=
  topDegreeCircleMap_snd A (z, x) i

/-- The constant fibre translation contributed by the first column. -/
def topDegreeFibreTranslation (A : Matrix (Fin 4) (Fin 4) ℤ) (z : Circle) :
    ProductTorus 3 := fun i => A i.succ 0 • z

@[simp] theorem topDegreeFibreTranslation_apply (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : Circle) (i : Fin 3) : topDegreeFibreTranslation A z i = A i.succ 0 • z := rfl

/-- The fibre decomposition is an identity of the actual continuous maps. -/
theorem topDegreeFibreMap_eq_translation (A : Matrix (Fin 4) (Fin 4) ℤ) (z : Circle) :
    topDegreeFibreMap A z = (rightTranslation (topDegreeFibreTranslation A z)).comp
      (torusMatrixMap (topDegreeTailMatrix A)) := by
  apply ContinuousMap.ext
  intro x
  ext i
  exact topDegreeFibreMap_apply_coordinate A z x i

/-- The actual homology action on any circle fibre is the tail matrix action in all degrees. -/
theorem topDegreeFibreMap_singularHomologyMap (A : Matrix (Fin 4) (Fin 4) ℤ)
    (z : Circle) (n : ℕ) :
    singularHomologyMap (topDegreeFibreMap A z) n =
      singularHomologyMap (torusMatrixMap (topDegreeTailMatrix A)) n := by
  rw [topDegreeFibreMap_eq_translation, singularHomologyMap_comp,
    rightTranslation_singularHomologyMap, LinearMap.id_comp]

/-- A head-preserving matrix carries each actual fixed-circle section into itself. -/
theorem topDegreeCircleMap_section (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0) (z : Circle) :
    (topDegreeCircleMap A).comp (topDegreeCircleSection z) =
      (topDegreeCircleSection z).comp (topDegreeFibreMap A z) := by
  apply ContinuousMap.ext
  intro x
  apply Prod.ext
  · exact topDegreeCircleMap_fst A hA (z, x)
  · rfl

/-- Expanding along the fixed first coordinate leaves exactly the tail determinant. -/
theorem topDegree_det_eq_tail (A : Matrix (Fin 4) (Fin 4) ℤ)
    (hA : ∀ j, A 0 j = if j = 0 then 1 else 0) :
    A.det = (topDegreeTailMatrix A).det := by
  rw [Matrix.det_succ_row_zero]
  simp [hA, topDegreeTailMatrix]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
