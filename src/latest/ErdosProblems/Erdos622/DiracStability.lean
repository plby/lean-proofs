/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos622.External.Erdos570.BondyChvatal
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# The stability interface for Dirac's theorem

Draganić--Keevash--Müyesser use the following stability alternative in the
bi-dense branch of their proof.  A graph whose minimum degree is within
`ε |V|` of the Dirac threshold is Hamiltonian, or it has an independent set
of size approximately `(1 / 2 - ε) |V|`, or it has two disjoint sets of that
size with at most `|V|` ordered crossing edges.

The source writes `(1 / 2 - ε) |V|` as an integer.  The definition below
makes the harmless rounding explicit by using the lower natural-number
integer part.  This file also records two elementary, reusable pieces of the
stability argument:

* sufficiently strong bi-density rules out both exceptional alternatives;
* a sub-unit real loss from the Dirac degree threshold disappears by
  integrality, so the already formalized Dirac theorem applies.

The latter is packaged with the explicit rational loss `1 / (4 |V|)` and in
uniform eventual form.  This is the exact boundary range of the stability
interface that follows from Dirac's theorem alone.
-/

open Filter Finset
open scoped SimpleGraph Topology

namespace Erdos622
namespace DiracStability

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rounded size of the exceptional sets in the KSS stability theorem. -/
def exceptionalSize (ε : ℝ) (N : ℕ) : ℕ :=
  ⌊(1 / 2 - ε) * (N : ℝ)⌋₊

/-- An independent set of the prescribed exact size. -/
def HasIndependentSetAt (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ A : Finset V, A.card = k ∧ G.IsIndepSet (A : Set V)

/-- Two disjoint prescribed-size sets joined by at most `b` ordered edges. -/
def HasSparsePairAt (G : SimpleGraph V) (k b : ℕ) : Prop :=
  ∃ A B : Finset V,
    Disjoint A B ∧ A.card = k ∧ B.card = k ∧
      (G.interedges A B).card ≤ b

/-- The three conclusions of the stability theorem, with all rounding and
edge-count conventions explicit. -/
def StabilityAlternative (G : SimpleGraph V) (k b : ℕ) : Prop :=
  G.IsHamiltonian ∨ HasIndependentSetAt G k ∨ HasSparsePairAt G k b

/-- A finite, cast-explicit formulation of the KSS stability statement.

The quantifier `N₀` represents "sufficiently large" and is uniform over the
finite vertex type and graph. -/
def StabilityStatement (ε : ℝ) (N₀ : ℕ) : Prop :=
  0 < ε ∧
    ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      N₀ ≤ Fintype.card W →
      (∀ v, (1 / 2 - ε) * (Fintype.card W : ℝ) ≤ G.degree v) →
      StabilityAlternative G (exceptionalSize ε (Fintype.card W))
        (Fintype.card W)

/-- Bi-density at scale `k`, in the strict form which directly excludes a
sparse pair with bound `b`.  The sets need not be disjoint, matching the
convention in the DKM bi-dense case. -/
def BiDenseAbove (G : SimpleGraph V) (k b : ℕ) : Prop :=
  ∀ A B : Finset V, k ≤ A.card → k ≤ B.card →
    b < (G.interedges A B).card

omit [Fintype V] [DecidableEq V] in
lemma interedges_self_eq_empty_of_isIndepSet (G : SimpleGraph V)
    {A : Finset V} (hA : G.IsIndepSet (A : Set V)) :
    G.interedges A A = ∅ := by
  ext e
  constructor
  · intro he
    have he' : (e.1 ∈ A ∧ e.2 ∈ A) ∧ G.Adj e.1 e.2 := by
      simpa [SimpleGraph.interedges_def] using he
    obtain ⟨⟨heA, heA'⟩, heAdj⟩ := he'
    exact (hA heA heA' heAdj.ne heAdj).elim
  · simp

omit [Fintype V] [DecidableEq V] in
/-- Strong bi-density excludes an independent set of size `k`. -/
lemma not_hasIndependentSetAt_of_biDenseAbove
    (G : SimpleGraph V) {k b : ℕ} (hDense : BiDenseAbove G k b) :
    ¬ HasIndependentSetAt G k := by
  rintro ⟨A, hAk, hAind⟩
  have hpos : b < (G.interedges A A).card :=
    hDense A A (by omega) (by omega)
  rw [interedges_self_eq_empty_of_isIndepSet G hAind] at hpos
  simp at hpos

omit [Fintype V] [DecidableEq V] in
/-- Strong bi-density excludes a sparse disjoint pair of size `k`. -/
lemma not_hasSparsePairAt_of_biDenseAbove
    (G : SimpleGraph V) {k b : ℕ} (hDense : BiDenseAbove G k b) :
    ¬ HasSparsePairAt G k b := by
  rintro ⟨A, B, _hAB, hAk, hBk, hsparse⟩
  have hdense : b < (G.interedges A B).card :=
    hDense A B (by omega) (by omega)
  omega

omit [Fintype V] [DecidableEq V] in
/-- A genuinely empty cut whose two sides are large enough supplies the
sparse-pair alternative.  This is the terminal step in the disconnected and
cut-vertex branches of the usual longest-cycle proof. -/
lemma hasSparsePairAt_of_emptyCut (G : SimpleGraph V) {A B : Finset V}
    {k b : ℕ} (hAB : Disjoint A B) (hkA : k ≤ A.card) (hkB : k ≤ B.card)
    (hEmpty : G.interedges A B = ∅) : HasSparsePairAt G k b := by
  obtain ⟨A', hA'A, hA'card⟩ := Finset.exists_subset_card_eq hkA
  obtain ⟨B', hB'B, hB'card⟩ := Finset.exists_subset_card_eq hkB
  refine ⟨A', B', hAB.mono hA'A hB'B, hA'card, hB'card, ?_⟩
  have hsub : G.interedges A' B' ⊆ G.interedges A B :=
    G.interedges_mono hA'A hB'B
  rw [hEmpty] at hsub
  have : G.interedges A' B' = ∅ := Finset.subset_empty.mp hsub
  simp [this]

/-- The preceding empty-cut certificate, injected into the full stability
alternative. -/
lemma stabilityAlternative_of_emptyCut (G : SimpleGraph V)
    {A B : Finset V} {k b : ℕ} (hAB : Disjoint A B)
    (hkA : k ≤ A.card) (hkB : k ≤ B.card)
    (hEmpty : G.interedges A B = ∅) : StabilityAlternative G k b := by
  exact Or.inr (Or.inr (hasSparsePairAt_of_emptyCut G hAB hkA hkB hEmpty))

/-- This is the logical step used after the stability theorem in the
bi-dense case: once the two exceptional outcomes are excluded, the graph is
Hamiltonian. -/
theorem StabilityAlternative.isHamiltonian_of_biDenseAbove
    {G : SimpleGraph V} {k b : ℕ} (h : StabilityAlternative G k b)
    (hDense : BiDenseAbove G k b) : G.IsHamiltonian := by
  rcases h with hHam | hInd | hSparse
  · exact hHam
  · exact (not_hasIndependentSetAt_of_biDenseAbove G hDense hInd).elim
  · exact (not_hasSparsePairAt_of_biDenseAbove G hDense hSparse).elim

omit [DecidableEq V] in
/-- An error of less than one in the doubled degree inequality disappears
because degrees and the graph order are natural numbers. -/
lemma dirac_degree_of_subunit_loss (G : SimpleGraph V) [DecidableRel G.Adj]
    {ρ : ℝ} (hLoss : 2 * ρ * (Fintype.card V : ℝ) < 1)
    (hDegree : ∀ v,
      (1 / 2 - ρ) * (Fintype.card V : ℝ) ≤ G.degree v) :
    ∀ v, Fintype.card V ≤ 2 * G.degree v := by
  intro v
  by_contra hnot
  have hNat : 2 * G.degree v + 1 ≤ Fintype.card V := by omega
  have hCast :
      2 * (G.degree v : ℝ) + 1 ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast hNat
  have hDegree' :
      (Fintype.card V : ℝ) - 2 * ρ * Fintype.card V ≤
        2 * (G.degree v : ℝ) := by
    nlinarith [hDegree v]
  nlinarith

/-- The integral-margin part of stability: if the loss in the doubled Dirac
inequality is strictly below one, Dirac's theorem gives the first stability
alternative. -/
theorem stability_of_subunit_loss (G : SimpleGraph V) [DecidableRel G.Adj]
    (k b : ℕ) {ρ : ℝ} (hCard : 3 ≤ Fintype.card V)
    (hLoss : 2 * ρ * (Fintype.card V : ℝ) < 1)
    (hDegree : ∀ v,
      (1 / 2 - ρ) * (Fintype.card V : ℝ) ≤ G.degree v) :
    StabilityAlternative G k b := by
  left
  exact SimpleGraph.dirac_theorem hCard
    (dirac_degree_of_subunit_loss G hLoss hDegree)

/-- Explicit rational specialization: a loss of one quarter of a vertex
from the minimum-degree threshold is too small to change the integral Dirac
inequality. -/
theorem stability_quarterVertexLoss (G : SimpleGraph V) [DecidableRel G.Adj]
    (k b : ℕ) (hCard : 3 ≤ Fintype.card V)
    (hDegree : ∀ v,
      (1 / 2 - 1 / (4 * (Fintype.card V : ℝ))) *
          (Fintype.card V : ℝ) ≤ G.degree v) :
    StabilityAlternative G k b := by
  apply stability_of_subunit_loss G k b hCard (ρ :=
    1 / (4 * (Fintype.card V : ℝ)))
  · have hCardPos : (0 : ℝ) < Fintype.card V := by positivity
    field_simp
    nlinarith
  · exact hDegree

/-- Uniform eventual form of the explicit rational stability result. -/
theorem eventually_stability_quarterVertexLoss :
    ∀ᶠ N : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (k b : ℕ),
        (∀ v,
          (1 / 2 - 1 / (4 * (N : ℝ))) * (N : ℝ) ≤ G.degree v) →
        StabilityAlternative G k b := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  intro G _ k b hDegree
  exact stability_quarterVertexLoss G k b (by simpa using hN) (by simpa using hDegree)

end

end DiracStability
end Erdos622
