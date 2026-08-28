import Wikipedia.HopfProblem.FirstHurewiczTrianglePaths

/-!
# Singular simplices whose actual vertices have a fixed image

The predicate is stated on the barycentric vertices themselves. Its face
and converse lemmas use Mathlib's genuine cosimplicial face maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]

/-- Every actual vertex of the singular simplex is sent to the base point. -/
def VerticesBased (x : X) (n : ℕ) (smp : C(Simplex n, X)) : Prop :=
  ∀ i : Fin (n + 1), smp (stdSimplex.vertex (S := ℝ) i) = x

/-- Every face of a vertex-based simplex is vertex-based. -/
theorem VerticesBased.face {x : X} {n : ℕ} {smp : C(Simplex (n + 1), X)}
    (h : VerticesBased x (n + 1) smp) (i : Fin (n + 2)) :
    VerticesBased x n (smp.comp (simplexFace n i)) := by
  intro j
  change smp (simplexFace n i (stdSimplex.vertex (S := ℝ) j)) = x
  rw [simplexFace_vertex]
  exact h (i.succAbove j)

theorem verticesBased_face {x : X} {n : ℕ} {smp : C(Simplex (n + 1), X)}
    (h : VerticesBased x (n + 1) smp) (i : Fin (n + 2)) :
    VerticesBased x n (smp.comp (simplexFace n i)) := h.face i

@[simp] theorem verticesBased_const (x : X) (n : ℕ) :
    VerticesBased x n (ContinuousMap.const (Simplex n) x) := fun _ => rfl

/-- In degree zero, being vertex-based says that the entire map is constant. -/
theorem verticesBased_zero_iff {x : X} {smp : C(Simplex 0, X)} :
    VerticesBased x 0 smp ↔ smp = ContinuousMap.const (Simplex 0) x := by
  constructor
  · intro h
    apply ContinuousMap.ext
    intro s
    change smp s = x
    rw [simplexZero_eq_vertex s]
    exact h 0
  · rintro rfl
    exact verticesBased_const x 0

/-- Every vertex of a positive-dimensional simplex belongs to an actual face. -/
theorem simplexVertex_exists_face (n : ℕ) (k : Fin (n + 2)) :
    ∃ i : Fin (n + 2), ∃ j : Fin (n + 1),
      simplexFace n i (stdSimplex.vertex (S := ℝ) j) =
        stdSimplex.vertex (S := ℝ) k := by
  obtain ⟨i, hi⟩ := exists_ne k
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi.symm
  refine ⟨i, j, ?_⟩
  rw [simplexFace_vertex, hj]

/-- If every face is vertex-based, so is the original positive-dimensional simplex. -/
theorem verticesBased_of_faces {x : X} {n : ℕ} {smp : C(Simplex (n + 1), X)}
    (h : ∀ i : Fin (n + 2), VerticesBased x n (smp.comp (simplexFace n i))) :
    VerticesBased x (n + 1) smp := by
  intro k
  obtain ⟨i, j, hij⟩ := simplexVertex_exists_face n k
  rw [← hij]
  exact h i j

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
