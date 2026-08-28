import Wikipedia.HopfProblem.FirstHurewiczSimplex
import Mathlib.Analysis.Convex.Combination
import Mathlib.Algebra.BigOperators.Fin

/-!
# Affine simplices for singular-chain subdivision

An ordered tuple of points in a standard simplex determines an actual
continuous affine singular simplex, by barycentric interpolation. Its
faces are exactly the affine simplices obtained by deleting vertices.
These identities connect formal subdivision chains to Mathlib's actual
singular-chain differential.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

/-- The actual affine simplex with the prescribed ordered vertices. -/
def affineSimplex {n p : ℕ} (v : Fin (n + 1) → Simplex p) : C(Simplex n, Simplex p) where
  toFun t := ⟨∑ i, t i • (v i : Fin (p + 1) → ℝ),
    (convex_stdSimplex ℝ (Fin (p + 1))).sum_mem
      (fun i _ => stdSimplex.zero_le t i) (stdSimplex.sum_eq_one t) (fun i _ => (v i).property)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)

@[simp] theorem affineSimplex_coe {n p : ℕ} (v : Fin (n + 1) → Simplex p) (t : Simplex n) :
    (affineSimplex v t : Fin (p + 1) → ℝ) = ∑ i, t i • (v i : Fin (p + 1) → ℝ) := rfl

@[simp] theorem affineSimplex_coordinate {n p : ℕ} (v : Fin (n + 1) → Simplex p)
    (t : Simplex n) (j : Fin (p + 1)) :
    affineSimplex v t j = ∑ i, t i * v i j := by
  change (∑ i, t i • (v i : Fin (p + 1) → ℝ)) j = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Evaluation at an actual standard vertex recovers the prescribed vertex. -/
@[simp] theorem affineSimplex_vertex {n p : ℕ} (v : Fin (n + 1) → Simplex p)
    (i : Fin (n + 1)) : affineSimplex v (stdSimplex.vertex (S := ℝ) i) = v i := by
  apply Subtype.ext
  change (∑ j : Fin (n + 1), ((Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) j) •
    (v j : Fin (p + 1) → ℝ)) = (v i : Fin (p + 1) → ℝ)
  simp [Pi.single_apply]

/-- The ordered standard vertices of the standard topological simplex. -/
def stdVertices (n : ℕ) : Fin (n + 1) → Simplex n := stdSimplex.vertex

@[simp] theorem affineSimplex_stdVertices (n : ℕ) :
    affineSimplex (stdVertices n) = ContinuousMap.id (Simplex n) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  funext j
  change (∑ i, t i • Pi.single i (1 : ℝ)) j = t j
  simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

/-- The actual cosimplicial face map deletes precisely its indexed vertex. -/
theorem affineSimplex_face {n p : ℕ} (v : Fin (n + 2) → Simplex p) (i : Fin (n + 2)) :
    (affineSimplex v).comp (simplexFace n i) = affineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (∑ j : Fin (n + 2), simplexFace n i t j • (v j : Fin (p + 1) → ℝ)) =
    ∑ j : Fin (n + 1), t j • (v (i.succAbove j) : Fin (p + 1) → ℝ)
  rw [Fin.sum_univ_succAbove _ i]
  simp only [simplexFace_apply_self, zero_smul, simplexFace_apply_succAbove, zero_add]

/-- Composing affine simplices is affine interpolation of the image vertices. -/
theorem affineSimplex_comp {m n p : ℕ} (v : Fin (n + 1) → Simplex p)
    (w : Fin (m + 1) → Simplex n) :
    (affineSimplex v).comp (affineSimplex w) = affineSimplex (fun j => affineSimplex v (w j)) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  funext k
  change affineSimplex v (affineSimplex w t) k = affineSimplex (fun j => affineSimplex v (w j)) t k
  simp only [affineSimplex_coordinate, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

/-- Every affine-simplex point belongs to the convex hull of its actual vertices. -/
theorem affineSimplex_mem_convexHull {n p : ℕ} (v : Fin (n + 1) → Simplex p)
    (t : Simplex n) :
    (affineSimplex v t : Fin (p + 1) → ℝ) ∈
      convexHull ℝ (range fun i => (v i : Fin (p + 1) → ℝ)) := by
  change (∑ i, t i • (v i : Fin (p + 1) → ℝ)) ∈ _
  apply (convex_convexHull ℝ _).sum_mem
  · intro i _
    exact stdSimplex.zero_le t i
  · exact stdSimplex.sum_eq_one t
  · intro i _
    exact subset_convexHull ℝ _ (mem_range_self i)

/-- A convex set containing the vertices contains the whole actual affine simplex. -/
theorem affineSimplex_mem_of_convex {n p : ℕ} (v : Fin (n + 1) → Simplex p)
    {s : Set (Fin (p + 1) → ℝ)} (hs : Convex ℝ s)
    (hv : ∀ i, (v i : Fin (p + 1) → ℝ) ∈ s) (t : Simplex n) :
    (affineSimplex v t : Fin (p + 1) → ℝ) ∈ s :=
  hs.sum_mem (fun i _ => stdSimplex.zero_le t i) (stdSimplex.sum_eq_one t) (fun i _ => hv i)

/-- The barycenter of the specified tuple, as an actual point of its target simplex. -/
def simplexBarycenter {n p : ℕ} (v : Fin (n + 1) → Simplex p) : Simplex p :=
  affineSimplex v (stdSimplex.barycenter : Simplex n)

theorem simplexBarycenter_coe {n p : ℕ} (v : Fin (n + 1) → Simplex p) :
    (simplexBarycenter v : Fin (p + 1) → ℝ) =
      ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i, (v i : Fin (p + 1) → ℝ) := by
  change (∑ i, (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ • (v i : Fin (p + 1) → ℝ)) = _
  simp only [Fintype.card_fin, Finset.smul_sum]

@[simp] theorem simplexBarycenter_singleton {p : ℕ} (v : Fin 1 → Simplex p) :
    simplexBarycenter v = v 0 := by
  change affineSimplex v (stdSimplex.barycenter : Simplex 0) = v 0
  have h : (stdSimplex.barycenter : Simplex 0) = stdSimplex.vertex (S := ℝ) (0 : Fin 1) :=
    simplexZero_eq_vertex _
  rw [h, affineSimplex_vertex]

/-- Affine interpolation preserves barycenters, as needed for subdivision naturality. -/
theorem affineSimplex_simplexBarycenter {m n p : ℕ} (v : Fin (n + 1) → Simplex p)
    (w : Fin (m + 1) → Simplex n) :
    affineSimplex v (simplexBarycenter w) = simplexBarycenter (fun j => affineSimplex v (w j)) :=
  ContinuousMap.congr_fun (affineSimplex_comp v w) (stdSimplex.barycenter : Simplex m)

theorem simplexBarycenter_mem_convexHull {n p : ℕ} (v : Fin (n + 1) → Simplex p) :
    (simplexBarycenter v : Fin (p + 1) → ℝ) ∈
      convexHull ℝ (range fun i => (v i : Fin (p + 1) → ℝ)) :=
  affineSimplex_mem_convexHull v _

end Wikipedia.HopfProblem.SingularMayerVietoris
