import Wikipedia.HopfProblem.FirstHurewiczSimplex
import Mathlib.Algebra.BigOperators.Fin

/-!
# Affine faces for the singular Alexander–Whitney product

All maps below are the actual affine maps of the standard topological
simplex, obtained by sending each vertex to its specified vertex.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularCohomologyCup

open FirstHurewicz

/-- The affine map induced by an ordered list of vertices. -/
def vertexMap {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1)) :
    C(Simplex m, Simplex n) :=
  ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩

@[simp] theorem vertexMap_apply {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (s : Simplex m) : vertexMap f s = stdSimplex.map f s := rfl

@[simp] theorem vertexMap_vertex {m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (i : Fin (m + 1)) :
    vertexMap f (stdSimplex.vertex (S := ℝ) i) = stdSimplex.vertex (f i) :=
  stdSimplex.map_vertex f i

theorem vertexMap_comp {l m n : ℕ} (f : Fin (m + 1) → Fin (n + 1))
    (g : Fin (l + 1) → Fin (m + 1)) :
    (vertexMap f).comp (vertexMap g) = vertexMap (f ∘ g) := by
  apply ContinuousMap.ext
  intro s
  exact stdSimplex.map_comp_apply g f s

@[simp] theorem vertexMap_id (n : ℕ) :
    vertexMap (id : Fin (n + 1) → Fin (n + 1)) = ContinuousMap.id (Simplex n) := by
  apply ContinuousMap.ext
  intro s
  exact stdSimplex.map_id_apply s

theorem simplexFace_eq_vertexMap (n : ℕ) (i : Fin (n + 2)) :
    simplexFace n i = vertexMap i.succAbove := rfl

/-- The vertex list of a consecutive face in a larger simplex. -/
abbrev windowIndex (a k n : ℕ) (h : a + k ≤ n) (i : Fin (k + 1)) : Fin (n + 1) :=
  ⟨a + i.val, by omega⟩

@[simp] theorem windowIndex_val (a k n : ℕ) (h : a + k ≤ n) (i : Fin (k + 1)) :
    (windowIndex a k n h i).val = a + i.val := rfl

/-- The face spanned by consecutive vertices `a, …, a + k`. -/
def windowFace (a k n : ℕ) (h : a + k ≤ n) : C(Simplex k, Simplex n) :=
  vertexMap (windowIndex a k n h)

/-- The first `p + 1` vertices of the `(p + q)`-simplex. -/
def frontFace (p q : ℕ) : C(Simplex p, Simplex (p + q)) :=
  windowFace 0 p (p + q) (by omega)

/-- The last `q + 1` vertices, starting at their common vertex `p`. -/
def backFace (p q : ℕ) : C(Simplex q, Simplex (p + q)) :=
  windowFace p q (p + q) (by omega)

@[simp] theorem frontFace_vertex (p q : ℕ) (i : Fin (p + 1)) :
    frontFace p q (stdSimplex.vertex (S := ℝ) i) =
      stdSimplex.vertex (⟨i.val, by omega⟩ : Fin (p + q + 1)) := by
  simpa only [frontFace, windowFace, windowIndex, Nat.zero_add] using
    vertexMap_vertex (windowIndex 0 p (p + q) (by omega)) i

@[simp] theorem backFace_vertex (p q : ℕ) (i : Fin (q + 1)) :
    backFace p q (stdSimplex.vertex (S := ℝ) i) =
      stdSimplex.vertex (⟨p + i.val, by omega⟩ : Fin (p + q + 1)) := by
  exact vertexMap_vertex _ i

end Wikipedia.HopfProblem.SingularCohomologyCup
