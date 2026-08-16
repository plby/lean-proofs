/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.ErdosStoneSimonovits
import Mathlib.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 755

The mathematical proof and the correspondence between its lemmas and the
formal development are documented in `tex/755.tex`.

The repository-local `answer` macro has the same identity expansion as the
metadata macro used by `google-deepmind/formal-conjectures`.
-/

syntax (name := answerSyntax755) "answer(" term ")" : term
macro_rules
  | `(answer($t)) => `($t)

open Filter Metric
open scoped BigOperators EuclideanGeometry Asymptotics RealInnerProductSpace SimpleGraph

namespace Erdos755

/-- A three-point set whose pairwise distances are all equal to `side`. -/
def IsEquilateralTriangle {d : ℕ} (side : ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  T.card = 3 ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = side

/-- A unit equilateral triangle in Euclidean `d`-space. -/
def IsUnitEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsEquilateralTriangle 1 T

/-- An equilateral triangle of any positive side length in Euclidean `d`-space. -/
def IsAnySizeEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ side : ℝ, 0 < side ∧ IsEquilateralTriangle side T

/-- Number of unit equilateral triangles spanned by a finite point set. -/
noncomputable def unitEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsUnitEquilateralTriangle T).card

/-- Number of equilateral triangles of any positive side length spanned by a finite point set. -/
noncomputable def anySizeEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsAnySizeEquilateralTriangle T).card

/-- Maximum number of unit equilateral triangles spanned by `n` points in Euclidean `d`-space. -/
noncomputable def TUnit (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ unitEquilateralTriangleCount d P = m}

/-- Maximum number of arbitrary-size equilateral triangles spanned by `n` points. -/
noncomputable def TAnySize (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ anySizeEquilateralTriangleCount d P = m}

/-! ## The unit-distance graph and the finite maximum -/

/-- The unit-distance graph on the subtype of a finite point set. -/
noncomputable def unitDistanceGraph {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) : SimpleGraph {x // x ∈ P} where
  Adj p q := dist (p : EuclideanSpace ℝ (Fin d)) q = 1
  symm.symm := by
    intro p q h
    rw [dist_comm]
    exact h
  loopless.irrefl := by
    intro p h
    simpa using h

noncomputable instance unitDistanceGraph.instDecidableRelAdj {d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin d))) : DecidableRel (unitDistanceGraph P).Adj :=
  Classical.decRel _

private def subtypeEmbedding { α : Type* } (P : Finset α) : {x // x ∈ P} ↪ α :=
  Function.Embedding.subtype _

private def liftEmbedding { α : Type* } [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) : {x // x ∈ T} ↪ {x // x ∈ P} where
  toFun x := ⟨x, hTP x.property⟩
  inj' x y h :=
    Subtype.ext (congrArg (fun z : {x // x ∈ P} ↦ (z : α)) h)

private def liftFinset { α : Type* } [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) : Finset {x // x ∈ P} :=
  T.attach.map (liftEmbedding P T hTP)

@[simp] private lemma map_liftFinset { α : Type* } [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) :
    (liftFinset P T hTP).map (subtypeEmbedding P) = T := by
  unfold liftFinset
  rw [Finset.map_map]
  exact Finset.attach_map_val

theorem erdos_755 :
    answer(True) ↔ ∃ o : ℕ → ℝ,
      o =o[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ∧
        ∀ᶠ n in atTop,
          (TUnit 6 n : ℝ) ≤ ((1 / 27 : ℝ) + o n) * (n : ℝ) ^ 3 := by
  sorry

