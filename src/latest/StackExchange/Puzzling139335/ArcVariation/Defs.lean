import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic

/-!
# Finite-resolution variation: concrete finite-chain definitions

The penalty `ε` is paid once for each chord.  We allow a chain to omit the
endpoints of its parameter interval: adjoining the endpoints only adds
nonnegative terms.  In particular this gives the usual partition supremum.
No finiteness, invariance, or concatenation property is postulated.
-/

open Set

namespace Puzzling139335.ArcVariation

noncomputable section

variable {α X : Type*} [PseudoMetricSpace X]

/-- A chord contributes only the part of its length exceeding the resolution. -/
def chord (ε : ℝ) (x y : X) : ℝ := max (dist x y - ε) 0

/-- The finite-resolution score of a finite ordered chain of parameter values. -/
def chainScore (ε : ℝ) (f : α → X) : List α → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: xs => chord ε (f a) (f b) + chainScore ε f (b :: xs)

/-- Weakly increasing finite chains lying in a parameter set. -/
def IsChainOn [LE α] (s : Set α) (xs : List α) : Prop :=
  xs.Pairwise (· ≤ ·) ∧ ∀ t ∈ xs, t ∈ s

/-- All scores of finite increasing chains in the parameter set. -/
def scoresOn [LE α] (ε : ℝ) (f : α → X) (s : Set α) : Set ℝ :=
  {r | ∃ xs, IsChainOn s xs ∧ r = chainScore ε f xs}

/-- Truncated variation, as an actual supremum of concrete finite-chain scores.
Its finiteness for continuous maps of compact real intervals is proved separately. -/
def variationOn [LE α] (ε : ℝ) (f : α → X) (s : Set α) : ℝ :=
  sSup (scoresOn ε f s)

theorem chord_nonneg (ε : ℝ) (x y : X) : 0 ≤ chord ε x y :=
  le_max_right _ _

theorem chord_symm (ε : ℝ) (x y : X) : chord ε x y = chord ε y x := by
  simp only [chord, dist_comm]

@[simp] theorem chord_self {ε : ℝ} (hε : 0 ≤ ε) (x : X) : chord ε x x = 0 := by
  simp [chord, max_eq_right (neg_nonpos.mpr hε)]

theorem chainScore_nonneg (ε : ℝ) (f : α → X) (xs : List α) :
    0 ≤ chainScore ε f xs := by
  induction xs using List.twoStepInduction with
  | nil => rfl
  | singleton a => rfl
  | cons_cons a b xs ih₁ ih₂ =>
      exact add_nonneg (chord_nonneg ε (f a) (f b)) (ih₂ b)

theorem zero_mem_scoresOn [LE α] (ε : ℝ) (f : α → X) (s : Set α) :
    0 ∈ scoresOn ε f s := by
  exact ⟨[], by simp [IsChainOn], rfl⟩

theorem scoresOn_nonempty [LE α] (ε : ℝ) (f : α → X) (s : Set α) :
    (scoresOn ε f s).Nonempty := ⟨0, zero_mem_scoresOn ε f s⟩

theorem chainScore_le_variationOn [LE α] {ε : ℝ} {f : α → X} {s : Set α}
    (hb : BddAbove (scoresOn ε f s)) {xs : List α} (hxs : IsChainOn s xs) :
    chainScore ε f xs ≤ variationOn ε f s :=
  le_csSup hb ⟨xs, hxs, rfl⟩

theorem variationOn_nonneg [LE α] {ε : ℝ} {f : α → X} {s : Set α}
    (hb : BddAbove (scoresOn ε f s)) : 0 ≤ variationOn ε f s :=
  le_csSup hb (zero_mem_scoresOn ε f s)

end

end Puzzling139335.ArcVariation
