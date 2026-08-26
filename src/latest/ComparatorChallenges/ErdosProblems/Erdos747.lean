import Mathlib

open Filter Real
open scoped Topology

namespace Erdos747

abbrev Vertex (n : ℕ) := Fin (3 * n)

abbrev Edge (n : ℕ) := Finset (Vertex n)

def allEdges (n : ℕ) : Finset (Edge n) :=
  (Finset.univ : Finset (Vertex n)).powersetCard 3

def IsMatching {n : ℕ} (F : Finset (Edge n)) : Prop :=
  ∀ ⦃A⦄, A ∈ F → ∀ ⦃B⦄, B ∈ F → A ≠ B → Disjoint A B

def HasPerfectMatching (n : ℕ) (H : Finset (Edge n)) : Prop :=
  ∃ F : Finset (Edge n), F ⊆ H ∧ F.card = n ∧ IsMatching F

def sample (n M : ℕ) : Finset (Finset (Edge n)) :=
  (allEdges n).powersetCard M

noncomputable def goodSample (n M : ℕ) : Finset (Finset (Edge n)) := by
  classical
  exact (sample n M).filter (HasPerfectMatching n)

noncomputable def pmProbability (n M : ℕ) : ℝ :=
  (goodSample n M).card / (sample n M).card

noncomputable def shamirScale (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (3 * n)

noncomputable def lowerEdgeCount (ε : ℝ) (n : ℕ) : ℕ :=
  ⌊(1 - ε) * shamirScale n⌋₊

noncomputable def upperEdgeCount (ε : ℝ) (n : ℕ) : ℕ :=
  ⌈(1 + ε) * shamirScale n⌉₊

noncomputable def ShamirThresholdResolution : Prop :=
  (∀ ε : ℝ, 0 < ε → ε < 1 →
      Tendsto (fun n ↦ pmProbability n (lowerEdgeCount ε n)) atTop (𝓝 0)) ∧
  (∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ pmProbability n (upperEdgeCount ε n)) atTop (𝓝 1))

/-- The exact two-sided fixed-edge perfect-matching threshold. -/
theorem erdos_747 : ShamirThresholdResolution := by
  sorry

end Erdos747
