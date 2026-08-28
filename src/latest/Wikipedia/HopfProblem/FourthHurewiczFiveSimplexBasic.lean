import Wikipedia.HopfProblem.FourthHurewiczFourSimplexBasic
import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexQuotientFacesSkeleton

/-!
# Singular simplex boundaries based on the codimension-two skeleton

The boundary data retain the original continuous singular simplex.  The
inverse of each literal simplex face map turns facewise based-boundary
data into the whole codimension-two skeleton condition, in every dimension.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

open FirstHurewicz SecondHurewicz.SimplyConnected

/-- An actual singular simplex based on every intersection of two distinct faces. -/
def BasedSimplexBoundary (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X) :=
  {τ : C(Simplex n, X) // ∀ s ∈ simplexTwoBoundary n, τ s = x}

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Each original face has its whole boundary based. -/
def basedSimplexBoundaryFace {n : ℕ} (τ : BasedSimplexBoundary (n + 1) x)
    (i : Fin (n + 2)) : BasedSimplex n x :=
  ⟨τ.val.comp (simplexFace n i),
    fun s hs => τ.property _ (simplexFace_simplexBoundary n i s hs)⟩

@[simp] theorem basedSimplexBoundaryFace_apply {n : ℕ}
    (τ : BasedSimplexBoundary (n + 1) x) (i : Fin (n + 2)) (s : Simplex n) :
    (basedSimplexBoundaryFace τ i).val s = τ.val (simplexFace n i s) := rfl

/-- Literal facewise data imply the actual codimension-two skeleton condition. -/
def BasedSimplexBoundary.ofFaces {n : ℕ} (τ : C(Simplex (n + 1), X))
    (h : ∀ i : Fin (n + 2), ∀ s ∈ simplexBoundary n,
      (τ.comp (simplexFace n i)) s = x) : BasedSimplexBoundary (n + 1) x :=
  ⟨τ, by
    intro s hs
    obtain ⟨i, j, hij, hi, hj⟩ := hs
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    let t := simplexFaceInverse n i ⟨s, hi⟩
    have ht : t ∈ simplexBoundary n := by
      refine ⟨k, ?_⟩
      change s (i.succAbove k) = 0
      rw [hk]
      exact hj
    have he := h i t ht
    change τ (simplexFace n i t) = x at he
    rw [show simplexFace n i t = s from simplexFace_inverse n i ⟨s, hi⟩] at he
    exact he⟩

@[simp] theorem BasedSimplexBoundary.ofFaces_val {n : ℕ}
    (τ : C(Simplex (n + 1), X))
    (h : ∀ i : Fin (n + 2), ∀ s ∈ simplexBoundary n,
      (τ.comp (simplexFace n i)) s = x) :
    (BasedSimplexBoundary.ofFaces τ h).val = τ := rfl

end Wikipedia.HopfProblem.HigherHurewicz.SimplexGeometry

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SecondHurewicz.SimplyConnected HigherHurewicz.SimplexGeometry

/-- The full geometric three-skeleton of the standard five-simplex. -/
abbrev fiveSimplexThreeSkeleton : Set (Simplex 5) := simplexTwoBoundary 5

/-- An actual singular five-simplex whose entire three-skeleton is based. -/
abbrev BasedFiveSimplex {X : Type*} [TopologicalSpace X] (x : X) :=
  BasedSimplexBoundary 5 x

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The actual four-dimensional face with its whole boundary based. -/
abbrev basedFiveSimplexFace (τ : BasedFiveSimplex x) (i : Fin 6) : BasedFourSimplex x :=
  basedSimplexBoundaryFace τ i

@[simp] theorem basedFiveSimplexFace_apply (τ : BasedFiveSimplex x)
    (i : Fin 6) (s : Simplex 4) :
    (basedFiveSimplexFace τ i).val s = τ.val (simplexFace 4 i s) := rfl

/-- Construct the based five-simplex from its six actual based face boundaries. -/
def BasedFiveSimplex.ofFaces (τ : C(Simplex 5, X))
    (h : ∀ i : Fin 6, ∀ s ∈ fourSimplexBoundary,
      (τ.comp (simplexFace 4 i)) s = x) : BasedFiveSimplex x :=
  BasedSimplexBoundary.ofFaces τ h

@[simp] theorem BasedFiveSimplex.ofFaces_val (τ : C(Simplex 5, X))
    (h : ∀ i : Fin 6, ∀ s ∈ fourSimplexBoundary,
      (τ.comp (simplexFace 4 i)) s = x) :
    (BasedFiveSimplex.ofFaces τ h).val = τ := rfl

@[simp] theorem basedFiveSimplexFace_ofFaces_val (τ : C(Simplex 5, X))
    (h : ∀ i : Fin 6, ∀ s ∈ fourSimplexBoundary,
      (τ.comp (simplexFace 4 i)) s = x) (i : Fin 6) :
    (basedFiveSimplexFace (BasedFiveSimplex.ofFaces τ h) i).val =
      τ.comp (simplexFace 4 i) := rfl

end Wikipedia.HopfProblem.FourthHurewicz
