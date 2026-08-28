import Wikipedia.HopfProblem.SingularMayerVietorisAffineSimplex
import Wikipedia.HopfProblem.SingularMayerVietorisFormalChainsSubdivision
import Wikipedia.HopfProblem.FirstHurewiczChainNaturality

/-!
# Evaluating formal affine chains in the actual singular complex

The augmented formal degree `n+1` evaluates in genuine singular degree `n`.
Evaluation commutes with the actual singular differential and with affine
maps of standard simplices. Barycenters are preserved by those affine maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

/-- The actual barycenter selector on points of a standard simplex. -/
def simplexCenter (p : ℕ) : FormalCenter (Simplex p) := fun _ v => simplexBarycenter v

/-- Evaluate each ordered formal simplex as its actual affine singular simplex. -/
def affineChainMap (p n : ℕ) : FormalChains (Simplex p) (n + 1) →ₗ[ℤ] Chains (Simplex p) n :=
  formalLift fun v => simplexChain (Simplex p) n (affineSimplex v)

@[simp] theorem affineChainMap_simplex (p n : ℕ) (v : Fin (n + 1) → Simplex p) :
    affineChainMap p n (formalSimplex v) = simplexChain (Simplex p) n (affineSimplex v) :=
  formalLift_simplex _ _

/-- Formal face deletion evaluates to the actual singular differential. -/
theorem affineChainMap_boundary (p n : ℕ) (c : FormalChains (Simplex p) (n + 2)) :
    ((singularComplex (Simplex p)).d (n + 1) n).hom (affineChainMap p (n + 1) c) =
      affineChainMap p n (formalBoundary (n + 1) c) := by
  have h : (((singularComplex (Simplex p)).d (n + 1) n).hom).comp
      (affineChainMap p (n + 1)) = (affineChainMap p n).comp (formalBoundary (n + 1)) := by
    apply formalChains_ext
    intro v
    change ((singularComplex (Simplex p)).d (n + 1) n).hom
      (affineChainMap p (n + 1) (formalSimplex v)) = _
    rw [affineChainMap_simplex, boundary_simplex]
    change _ = affineChainMap p n (formalBoundary (n + 1) (formalSimplex v))
    rw [formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, affineChainMap_simplex, affineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

/-- Actual affine maps commute with evaluation of formal chains. -/
theorem inducedChain_affineChainMap {m n p : ℕ} (v : Fin (n + 1) → Simplex p)
    (c : FormalChains (Simplex n) (m + 1)) :
    inducedChain (affineSimplex v) m (affineChainMap n m c) =
      affineChainMap p m (formalMap (affineSimplex v) (m + 1) c) := by
  have h : (inducedChain (affineSimplex v) m).comp (affineChainMap n m) =
      (affineChainMap p m).comp (formalMap (affineSimplex v) (m + 1)) := by
    apply formalChains_ext
    intro w
    simp only [LinearMap.comp_apply, affineChainMap_simplex, inducedChain_simplex,
      formalMap_simplex, affineSimplex_comp]
    rfl
  exact LinearMap.congr_fun h c

/-- The actual identity simplex is the evaluation of its ordered standard vertices. -/
@[simp] theorem affineChainMap_stdVertices (n : ℕ) :
    affineChainMap n n (formalSimplex (stdVertices n)) =
      simplexChain (Simplex n) n (ContinuousMap.id (Simplex n)) := by
  rw [affineChainMap_simplex, affineSimplex_stdVertices]

/-- The ordered vertices of the actual `i`-th face. -/
def faceVertices (n : ℕ) (i : Fin (n + 2)) : Fin (n + 1) → Simplex (n + 1) :=
  fun j => stdVertices (n + 1) (i.succAbove j)

@[simp] theorem affineSimplex_faceVertices (n : ℕ) (i : Fin (n + 2)) :
    affineSimplex (faceVertices n i) = simplexFace n i := by
  have h := affineSimplex_face (stdVertices (n + 1)) i
  rw [affineSimplex_stdVertices, ContinuousMap.id_comp] at h
  exact h.symm

/-- Affine maps preserve the chosen actual barycenter selector. -/
theorem affineSimplex_preserves_center {n p : ℕ} (v : Fin (n + 1) → Simplex p)
    (m : ℕ) (w : Fin (m + 1) → Simplex n) :
    affineSimplex v (simplexCenter n m w) = simplexCenter p m (affineSimplex v ∘ w) :=
  affineSimplex_simplexBarycenter v w

/-- In particular, actual standard face maps preserve the chosen centers. -/
theorem simplexFace_preserves_center (n : ℕ) (i : Fin (n + 2))
    (m : ℕ) (v : Fin (m + 1) → Simplex n) :
    simplexFace n i (simplexCenter n m v) =
      simplexCenter (n + 1) m (simplexFace n i ∘ v) := by
  rw [← affineSimplex_faceVertices]
  exact affineSimplex_preserves_center (faceVertices n i) m v

theorem simplexFace_stdVertices (n : ℕ) (i : Fin (n + 2)) :
    simplexFace n i ∘ stdVertices n = faceVertices n i := by
  funext j
  simp only [Function.comp_apply, stdVertices, simplexFace_apply, stdSimplex.map_vertex,
    faceVertices]

/-- The boundary of the formal standard simplex is the alternating sum of
the actual face images of the lower-dimensional standard simplex. -/
theorem formalBoundary_stdVertices (n : ℕ) :
    formalBoundary (n + 1) (formalSimplex (stdVertices (n + 1))) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        formalMap (simplexFace n i) (n + 1) (formalSimplex (stdVertices n)) := by
  rw [formalBoundary_simplex]
  apply Finset.sum_congr rfl
  intro i hi
  rw [formalMap_simplex, simplexFace_stdVertices]
  rfl

/-- Subdivision is natural under an actual affine simplex map. -/
theorem formalSubdivision_affine_natural {n p : ℕ} (v : Fin (n + 1) → Simplex p)
    (m : ℕ) (c : FormalChains (Simplex n) m) :
    formalMap (affineSimplex v) m (formalSubdivision (simplexCenter n) m c) =
      formalSubdivision (simplexCenter p) m (formalMap (affineSimplex v) m c) :=
  formalMap_subdivision (simplexCenter n) (simplexCenter p) (affineSimplex v)
    (affineSimplex_preserves_center v) m c

end Wikipedia.HopfProblem.SingularMayerVietoris
