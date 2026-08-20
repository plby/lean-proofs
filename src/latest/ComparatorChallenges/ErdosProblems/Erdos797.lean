import Mathlib

open scoped BigOperators
open Finset Function Set
open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos797

def IsAcyclicColoring {V C : Type*} (G : SimpleGraph V) (c : V → C) : Prop :=
  (∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) ∧
    ∀ ⦃v⦄ (w : G.Walk v v), w.IsCycle →
      ¬ ∃ a b : C, ∀ u ∈ w.support, c u = a ∨ c u = b

noncomputable def graphMaxDegree {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact G.maxDegree

def AcyclicBound (d k : ℕ) : Prop :=
  ∀ n : ℕ, ∀ G : SimpleGraph (Fin n), graphMaxDegree G ≤ d →
    ∃ c : Fin n → Fin k, IsAcyclicColoring G c

noncomputable def extremalAcyclicNumber (d : ℕ) : ℕ :=
  sInf {k : ℕ | AcyclicBound d k}

notation "f₇₉₇" => extremalAcyclicNumber

end Erdos797

namespace Erdos797.LowerBound

def lowerM (s : ℕ) := 2 ^ s

end Erdos797.LowerBound

namespace Erdos797.LowerBound

def lowerD (s : ℕ) := 32768 * s * lowerM s ^ 6

end Erdos797.LowerBound

namespace Erdos797

theorem erdos797_resolution :
    (∀ d : ℕ, 1 ≤ d → f₇₉₇ d ^ 3 ≤ 1024 ^ 3 * d ^ 4) ∧
    (∀ d : ℕ, LowerBound.lowerD 1 ≤ d →
      d ^ 4 ≤ 2 ^ 67 * Nat.log 2 d * f₇₉₇ d ^ 3) ∧
    ((fun d : ℕ ↦ (f₇₉₇ d : ℝ)) =o[Filter.atTop]
      (fun d : ℕ ↦ (d : ℝ) ^ 2)) := by
  sorry

end Erdos797

end
