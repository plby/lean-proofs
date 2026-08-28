import Wikipedia.HopfProblem.FourthHurewiczFourSimplexQuotientBasic
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry

/-!
# Based singular simplices in the original native homotopy groups

These definitions retain the actual singular simplex and use the explicit
cube quotient.  Boundary-relative simplex homotopies give boundary-relative
native cube homotopies in every dimension.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open FirstHurewicz SecondHurewicz.SimplyConnected

/-- An actual singular simplex whose entire geometric boundary is based. -/
def BasedSimplex (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X) :=
  {τ : C(Simplex n, X) // ∀ s ∈ simplexBoundary n, τ s = x}

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

/-- The original singular simplex composed with the actual cube quotient. -/
def basedSimplexLoop {n : ℕ} (τ : BasedSimplex n x) : GenLoop (Fin n) X x :=
  ⟨τ.val.comp (simplexQuotient n),
    fun u hu => τ.property _ (simplexQuotient_boundary u hu)⟩

@[simp] theorem basedSimplexLoop_apply {n : ℕ} (τ : BasedSimplex n x) (u : Fin n → I) :
    basedSimplexLoop τ u = τ.val (simplexQuotient n u) := rfl

/-- The class in Mathlib's native homotopy quotient, with additive notation. -/
def basedSimplexClass {n : ℕ} (τ : BasedSimplex n x) : Additive (π_ n X x) :=
  Additive.ofMul (⟦basedSimplexLoop τ⟧ : π_ n X x)

theorem basedSimplex_face {n : ℕ} (τ : BasedSimplex (n + 1) x) (i : Fin (n + 2)) :
    τ.val.comp (simplexFace n i) = ContinuousMap.const (Simplex n) x := by
  apply ContinuousMap.ext
  intro s
  exact τ.property _ ⟨i, simplexFace_apply_self n i s⟩

def constantBasedSimplex (n : ℕ) (x : X) : BasedSimplex n x :=
  ⟨ContinuousMap.const (Simplex n) x, fun _ _ => rfl⟩

@[simp] theorem basedSimplexLoop_constant (n : ℕ) (x : X) :
    basedSimplexLoop (constantBasedSimplex n x) = GenLoop.const := rfl

@[simp] theorem basedSimplexClass_constant (n : ℕ) (x : X) :
    basedSimplexClass (constantBasedSimplex (n + 1) x) = 0 := rfl

def mapBasedSimplex {n : ℕ} (f : C(X, Y)) (τ : BasedSimplex n x) :
    BasedSimplex n (f x) :=
  ⟨f.comp τ.val, fun s hs => congrArg f (τ.property s hs)⟩

/-- Literal relative simplex homotopies induce literal relative cube homotopies. -/
def basedSimplexLoopHomotopy {n : ℕ} {τ υ : BasedSimplex n x}
    (H : τ.val.HomotopyRel υ.val (simplexBoundary n)) :
    (basedSimplexLoop τ).val.HomotopyRel (basedSimplexLoop υ).val
      (Cube.boundary (Fin n)) where
  toFun z := H (z.1, simplexQuotient n z.2)
  continuous_toFun := by fun_prop
  map_zero_left u := H.apply_zero _
  map_one_left u := H.apply_one _
  prop' t u hu := H.eq_fst t (simplexQuotient_boundary u hu)

theorem basedSimplexClass_homotopy {n : ℕ} {τ υ : BasedSimplex n x}
    (H : τ.val.HomotopyRel υ.val (simplexBoundary n)) :
    basedSimplexClass τ = basedSimplexClass υ :=
  congrArg Additive.ofMul (Quotient.sound ⟨basedSimplexLoopHomotopy H⟩)

/-- Actual equalities on all face maps give the whole-boundary condition. -/
def BasedSimplex.ofFaces {n : ℕ} (τ : C(Simplex (n + 1), X))
    (hτ : ∀ i : Fin (n + 2), τ.comp (simplexFace n i) = ContinuousMap.const (Simplex n) x) :
    BasedSimplex (n + 1) x :=
  ⟨τ, fun s ⟨i, hs⟩ => by
    simpa only [ContinuousMap.comp_apply, ContinuousMap.const_apply, simplexFace_inverse]
      using ContinuousMap.congr_fun (hτ i) (simplexFaceInverse n i ⟨s, hs⟩)⟩

@[simp] theorem BasedSimplex.ofFaces_val {n : ℕ} (τ : C(Simplex (n + 1), X))
    (hτ : ∀ i : Fin (n + 2), τ.comp (simplexFace n i) = ContinuousMap.const (Simplex n) x) :
    (BasedSimplex.ofFaces τ hτ).val = τ := rfl

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry
