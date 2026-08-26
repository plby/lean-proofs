/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

open Filter SimpleGraph

namespace Erdos1091

universe u

namespace Walk

/-- The finite set of chords of a walk in a finite ambient graph. -/
noncomputable def chordFinset {V : Type u} [Fintype V]
    {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Finset (Sym2 V) := by
  classical
  exact {e ∈ G.edgeFinset | p.IsChord e}

/-- The number of ambient-graph chords of a walk. -/
noncomputable def chordCount {V : Type u} [Fintype V]
    {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : ℕ :=
  (chordFinset p).card

end Walk

/-- The affirmative two-chord theorem and the negative quantitative answer. -/
theorem erdos_1091 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.chromaticNumber = (4 : ℕ∞) → G.CliqueFree 4 →
        ∃ (u : Fin n) (p : G.Walk u u),
          p.IsCycle ∧ Odd p.length ∧ 2 ≤ Walk.chordCount p) ∧
    (¬ ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∀ (r n : ℕ) (G : SimpleGraph (Fin n)),
        G.chromaticNumber = (4 : ℕ∞) →
        (∀ s : Finset (Fin n), s.card ≤ r →
          (G.induce (s : Set (Fin n))).chromaticNumber ≤ (3 : ℕ∞)) →
        ∃ (u : Fin n) (p : G.Walk u u),
          p.IsCycle ∧ Odd p.length ∧ f r ≤ Walk.chordCount p) := by
  sorry

/-- Explicit four-critical counterexamples with at most ten chords per cycle. -/
theorem erdos_1091_four_critical_counterexamples (m : ℕ) :
    ∃ G : SimpleGraph (Fin (20 * m + 31)),
      G.chromaticNumber = (4 : ℕ∞) ∧ G.CliqueFree 4 ∧
      (∀ H : G.Subgraph, H < ⊤ → H.coe.Colorable 3) ∧
      (∀ (u : Fin (20 * m + 31)) (p : G.Walk u u),
        p.IsCycle → Walk.chordCount p ≤ 10) := by
  sorry

end Erdos1091
