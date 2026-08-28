import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexCubeFacets
import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeSymmetries
import Mathlib.GroupTheory.Perm.Fin

/-!
# Based codimension-two cubical boundaries

The input is an actual continuous cube, based on every intersection of two
distinct outer facets.  Each facet is therefore an original generalized
loop.  The evaluator interface records laws of actual relative homotopies
and concatenations; its native instance is supplied below, without any
homology or presentation assumption.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

open NativeSubdivision

/-- The endpoints of the closed unit interval. -/
def IsEndpoint (t : I) : Prop := t = 0 ∨ t = 1

/-- An actual cube which is based on its entire codimension-two boundary. -/
def BasedCubicalCell (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X) :=
  {F : C(Fin n → I, X) // ∀ u i j, i ≠ j →
    (u i = 0 ∨ u i = 1) → (u j = 0 ∨ u j = 1) → F u = x}

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Restriction to an actual cube facet, with its remaining coordinates in order. -/
def cubicalFace {n : ℕ} (F : BasedCubicalCell (n + 1) x)
    (i : Fin (n + 1)) (ε : I) (hε : ε = 0 ∨ ε = 1) : GenLoop (Fin n) X x :=
  ⟨F.val.comp (cubeFacet n i ε), fun u ⟨j, hj⟩ => by
    apply F.property _ i (i.succAbove j) (Fin.ne_succAbove i j)
    · simpa only [cubeFacet_apply_self] using hε
    · simpa only [cubeFacet_apply_succAbove] using hj⟩

@[simp] theorem cubicalFace_apply {n : ℕ} (F : BasedCubicalCell (n + 1) x)
    (i : Fin (n + 1)) (ε : I) (hε : ε = 0 ∨ ε = 1) (u : Fin n → I) :
    cubicalFace F i ε hε u = F.val (cubeFacet n i ε u) := rfl

/-- The lower facet in the original coordinate ordering. -/
abbrev cubicalLowerFace {n : ℕ} (F : BasedCubicalCell (n + 1) x)
    (i : Fin (n + 1)) : GenLoop (Fin n) X x :=
  cubicalFace F i 0 (Or.inl rfl)

/-- The upper facet in the original coordinate ordering. -/
abbrev cubicalUpperFace {n : ℕ} (F : BasedCubicalCell (n + 1) x)
    (i : Fin (n + 1)) : GenLoop (Fin n) X x :=
  cubicalFace F i 1 (Or.inr rfl)

variable (n : ℕ) (x : X) (A : Type*) [AddCommGroup A]

/-- Additive evaluation of actual native loops, invariant under actual homotopies. -/
structure CubicalEvaluator where
  evaluate : GenLoop (Fin n) X x → A
  map_const : evaluate GenLoop.const = 0
  map_homotopic : ∀ {p q}, GenLoop.Homotopic p q → evaluate p = evaluate q
  map_transAt : ∀ i p q, evaluate (GenLoop.transAt i p q) = evaluate p + evaluate q
  map_symmAt : ∀ i p, evaluate (GenLoop.symmAt i p) = -evaluate p
  map_swap : ∀ p i j, i ≠ j →
    evaluate (permuteCubeLoop p (Equiv.swap i j)) = -evaluate p

instance : CoeFun (CubicalEvaluator n x A) (fun _ => GenLoop (Fin n) X x → A) :=
  ⟨CubicalEvaluator.evaluate⟩

variable {n x A}

/-- All coordinate permutations have their genuine orientation sign. -/
theorem CubicalEvaluator.map_permutation (E : CubicalEvaluator n x A)
    (p : GenLoop (Fin n) X x) (e : Equiv.Perm (Fin n)) :
    E (permuteCubeLoop p e) = ((Equiv.Perm.sign e : ℤˣ) : ℤ) • E p := by
  induction e using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul e i j hij ih =>
    rw [permuteCubeLoop_mul, E.map_swap _ i j hij, ih]
    simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

/-- Moving the first coordinate to the end has the expected alternating sign. -/
theorem CubicalEvaluator.map_finRotate (E : CubicalEvaluator n x A)
    (p : GenLoop (Fin n) X x) :
    E (permuteCubeLoop p (finRotate n)) = (-1 : ℤ) ^ (n - 1) • E p := by
  rw [E.map_permutation, sign_finRotate]
  simp

/-- The alternating sum of the genuine based outer facets. -/
def cubicalBoundaryValue (E : CubicalEvaluator n x A)
    (F : BasedCubicalCell (n + 1) x) : A :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
    (E (cubicalUpperFace F i) - E (cubicalLowerFace F i))

/-- Native homotopy classes themselves satisfy every evaluator law. -/
def nativeCubicalEvaluator (n : ℕ) (x : X) :
    CubicalEvaluator (n + 2) x (Additive (π_ (n + 2) X x)) where
  evaluate := nativeClass
  map_const := nativeClass_const
  map_homotopic := nativeClass_homotopic
  map_transAt := nativeClass_transAt
  map_symmAt := nativeClass_symmAt
  map_swap := permuteCubeLoop_swap_additiveClass

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
