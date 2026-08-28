import Wikipedia.HopfProblem.SingularCohomologyCupCochainsDifferential

/-!
# Original integral cochains on explicit affine faces

These identities retain the actual singular simplex and its ordered
vertex maps. The deletion formulas allow the degree-(4,3) cup-one
identity to be checked as a finite signed polynomial identity.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCupOne

open FirstHurewicz SingularCohomologyCup

variable {X : Type} [TopologicalSpace X]

theorem simplexFace_six (i : Fin 8) :
    simplexFace 6 i = vertexMap
      (![![1, 2, 3, 4, 5, 6, 7], ![0, 2, 3, 4, 5, 6, 7],
         ![0, 1, 3, 4, 5, 6, 7], ![0, 1, 2, 4, 5, 6, 7],
         ![0, 1, 2, 3, 5, 6, 7], ![0, 1, 2, 3, 4, 6, 7],
         ![0, 1, 2, 3, 4, 5, 7], ![0, 1, 2, 3, 4, 5, 6]] i) := by
  apply congrArg vertexMap
  fin_cases i <;> funext j <;> fin_cases j <;> rfl

def faceValue {p n : ℕ} (α : Cochain X p) (σ : SingularSimplex X n)
    (v : Fin (p + 1) → Fin (n + 1)) : ℤ :=
  α (simplexChain X p (σ.comp (vertexMap v)))

theorem faceValue_comp {p m n : ℕ} (α : Cochain X p) (σ : SingularSimplex X n)
    (v : Fin (m + 1) → Fin (n + 1)) (w : Fin (p + 1) → Fin (m + 1)) :
    faceValue α (σ.comp (vertexMap v)) w = faceValue α σ (v ∘ w) := by
  simp only [faceValue, ContinuousMap.comp_assoc, vertexMap_comp]

theorem comp_vecCons {A B : Type*} {k : ℕ} (f : A → B) (a : A) (v : Fin k → A) :
    f ∘ Matrix.vecCons a v = Matrix.vecCons (f a) (f ∘ v) := Fin.comp_cons f a v

theorem comp_vecEmpty {A B : Type*} (f : A → B) :
    f ∘ (Matrix.vecEmpty : Fin 0 → A) = Matrix.vecEmpty := by
  funext i
  exact Fin.elim0 i

def deleteVertices {A : Type*} {k : ℕ} (v : Fin (k + 1) → A) (i : Fin (k + 1)) :
    Fin k → A := v ∘ i.succAbove

@[simp] theorem deleteVertices_cons_zero {A : Type*} {k : ℕ} (a : A) (v : Fin k → A) :
    deleteVertices (Matrix.vecCons a v) 0 = v := by
  funext i
  simp [deleteVertices, Fin.succAbove_zero]

@[simp] theorem deleteVertices_cons_succ {A : Type*} {k : ℕ} (a : A)
    (v : Fin (k + 1) → A) (i : Fin (k + 1)) :
    deleteVertices (Matrix.vecCons a v) i.succ =
      Matrix.vecCons a (deleteVertices v i) := Fin.cons_comp_succ_succAbove a v i

theorem coboundary_faceValue {p n : ℕ} (α : Cochain X p) (σ : SingularSimplex X n)
    (v : Fin (p + 2) → Fin (n + 1)) :
    faceValue (coboundary α) σ v =
      ∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val * faceValue α σ (deleteVertices v i) := by
  simp only [faceValue, coboundary_simplex, simplexFace_eq_vertexMap,
    ContinuousMap.comp_assoc, vertexMap_comp, deleteVertices]

theorem coboundary_faceValue_three {n : ℕ} (α : Cochain X 3) (σ : SingularSimplex X n)
    (a b c d e : Fin (n + 1)) :
    faceValue (coboundary α) σ ![a, b, c, d, e] =
      faceValue α σ ![b, c, d, e] - faceValue α σ ![a, c, d, e] +
      faceValue α σ ![a, b, d, e] - faceValue α σ ![a, b, c, e] +
      faceValue α σ ![a, b, c, d] := by
  rw [coboundary_faceValue]
  simp only [Fin.sum_univ_succ, deleteVertices_cons_zero, deleteVertices_cons_succ,
    Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero]
  ring

theorem coboundary_faceValue_four {n : ℕ} (α : Cochain X 4) (σ : SingularSimplex X n)
    (a b c d e f : Fin (n + 1)) :
    faceValue (coboundary α) σ ![a, b, c, d, e, f] =
      faceValue α σ ![b, c, d, e, f] - faceValue α σ ![a, c, d, e, f] +
      faceValue α σ ![a, b, d, e, f] - faceValue α σ ![a, b, c, e, f] +
      faceValue α σ ![a, b, c, d, f] - faceValue α σ ![a, b, c, d, e] := by
  rw [coboundary_faceValue]
  simp only [Fin.sum_univ_succ, deleteVertices_cons_zero, deleteVertices_cons_succ,
    Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero]
  ring

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCupOne
