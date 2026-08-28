import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalPrism

/-!
# Separating the first face of the original formal boundary

The remaining signed faces retain the first vertex. This separation and
the common-vertex cone identity are in the original free ordered chain
modules, so shared faces can cancel before expanding any cross product.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open SingularMayerVietoris PeriodTorusHigherHomology
open scoped BigOperators

variable {V W : Type*}

/-- Delete the first vertex, without its boundary sign (which is positive). -/
def firstFace (q : ℕ) : FormalChains W (q + 2) →ₗ[ℤ] FormalChains W (q + 1) :=
  formalLift fun w => formalSimplex (Fin.tail w)

@[simp] theorem firstFace_simplex (q : ℕ) (w : Fin (q + 2) → W) :
    firstFace q (formalSimplex w) = formalSimplex (Fin.tail w) :=
  formalLift_simplex _ _

/-- The other signed faces, all of which retain the original first vertex. -/
def retainedFirstBoundary (q : ℕ) :
    FormalChains W (q + 2) →ₗ[ℤ] FormalChains W (q + 1) :=
  formalLift fun w => ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i.val + 1) •
    formalSimplex (w ∘ i.succ.succAbove)

@[simp] theorem retainedFirstBoundary_simplex (q : ℕ) (w : Fin (q + 2) → W) :
    retainedFirstBoundary q (formalSimplex w) =
      ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i.val + 1) •
        formalSimplex (w ∘ i.succ.succAbove) :=
  formalLift_simplex _ _

/-- Every simplex in the retained-face formula starts at the original vertex. -/
theorem retainedFace_first_vertex (q : ℕ) (w : Fin (q + 2) → W) (i : Fin (q + 1)) :
    (w ∘ i.succ.succAbove) 0 = w 0 := by
  simp only [Function.comp_apply, Fin.succ_succAbove_zero]

/-- The exact first-face separation of the original simplicial boundary. -/
theorem formalBoundary_firstFace_split_simplex (q : ℕ) (w : Fin (q + 2) → W) :
    formalBoundary (q + 1) (formalSimplex w) =
      formalSimplex (Fin.tail w) + retainedFirstBoundary q (formalSimplex w) := by
  rw [formalBoundary_simplex, Fin.sum_univ_succ, retainedFirstBoundary_simplex]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.succAbove_zero]
  rfl

/-- The separation holds on arbitrary formal chains, not only generators. -/
theorem formalBoundary_firstFace_split (q : ℕ) :
    (formalBoundary (V := W) (q + 1)) = firstFace q + retainedFirstBoundary q := by
  apply formalChains_ext
  intro w
  simpa only [LinearMap.add_apply, firstFace_simplex] using
    formalBoundary_firstFace_split_simplex q w

/-- With a common first right vertex, the frozen recursive edge product
has one common cone on the complete signed boundary. -/
theorem formalEdgeCrossProduct_sum_common_first {ι : Type*} (q : ℕ)
    (s : Finset ι) (c : ι → ℤ) (v : Fin 2 → V) (w : ι → Fin (q + 2) → W)
    (a : W) (hfirst : ∀ j ∈ s, w j 0 = a) :
    formalEdgeCrossProduct (q + 1) (formalSimplex v)
        (∑ j ∈ s, c j • formalSimplex (w j)) =
      formalCone (v 0, a) (q + 2)
        (formalMap (fun z => (v 1, z)) (q + 2) (∑ j ∈ s, c j • formalSimplex (w j)) -
          formalMap (fun z => (v 0, z)) (q + 2) (∑ j ∈ s, c j • formalSimplex (w j)) -
          formalEdgeCrossProduct q (formalSimplex v)
            (formalBoundary (q + 1) (∑ j ∈ s, c j • formalSimplex (w j)))) := by
  calc
    _ = ∑ j ∈ s, c j • formalEdgeCrossProduct (q + 1)
        (formalSimplex v) (formalSimplex (w j)) := by
      simp only [map_sum, map_smul]
    _ = ∑ j ∈ s, c j • formalCone (v 0, a) (q + 2)
        (formalMap (fun z => (v 1, z)) (q + 2) (formalSimplex (w j)) -
          formalMap (fun z => (v 0, z)) (q + 2) (formalSimplex (w j)) -
          formalEdgeCrossProduct q (formalSimplex v)
            (formalBoundary (q + 1) (formalSimplex (w j)))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [formalEdgeCrossProduct_simplex_succ, formalPointCrossProduct_edge_boundary,
        hfirst j hj]
    _ = _ := by
      simp only [map_sum, map_smul, map_sub, smul_sub, Finset.sum_sub_distrib]

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
