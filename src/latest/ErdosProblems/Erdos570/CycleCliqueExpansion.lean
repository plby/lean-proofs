/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos79.Core

/-!
# The expansion core in the cycle--clique Ramsey bound

This file formalizes the deletion lemma at the start of the
Erdős--Faudree--Rousseau--Schelp proof of the subquadratic
cycle--clique estimate.  If a finite graph has no large independent set,
then it has a nonempty induced region in which every independent set has
many neighbours inside that region.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

/-- Neighbours of `X` which remain inside the ambient finite region `W`. -/
def relativeNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (W X : Finset V) : Finset V :=
  W.filter fun v ↦ ∃ x ∈ X, G.Adj x v

/-- Every independent set in `W` has at least `l` times as many neighbours
inside `W`.  This is property `H_l` in EFRS. -/
def ExpandsIndependentOn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (l : ℕ) (W : Finset V) : Prop :=
  ∀ X : Finset V, X ⊆ W → G.IsIndepSet (X : Set V) →
    l * X.card ≤ (relativeNeighborFinset G W X).card

@[simp] theorem mem_relativeNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {W X : Finset V} {v : V} :
    v ∈ relativeNeighborFinset G W X ↔
      v ∈ W ∧ ∃ x ∈ X, G.Adj x v := by
  simp [relativeNeighborFinset]

theorem disjoint_relativeNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {W X : Finset V} (hX : G.IsIndepSet (X : Set V)) :
    Disjoint X (relativeNeighborFinset G W X) := by
  rw [Finset.disjoint_left]
  intro x hxX hxN
  obtain ⟨-, y, hyX, hyx⟩ := mem_relativeNeighborFinset.mp hxN
  by_cases hxy : x = y
  · subst y
    exact G.loopless.irrefl x hyx
  · exact hX hxX hyX hxy hyx.symm

/-- A finite region either has a proportionally large independent set, or
contains a nonempty subregion satisfying `H_l`.  The proof repeatedly
removes a bad independent set together with all its relative neighbours.
The removed independent blocks have no edges to later blocks, so they can
all be united. -/
theorem independent_or_expanding_subregion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (l : ℕ) :
    ∀ W : Finset V,
      (∃ I : Finset V, I ⊆ W ∧ G.IsIndepSet (I : Set V) ∧
        (W.Nonempty → W.card < (l + 1) * I.card)) ∨
      (∃ U : Finset V, U ⊆ W ∧ U.Nonempty ∧
        ExpandsIndependentOn G l U) := by
  intro W
  induction W using Finset.strongInductionOn with
  | _ W ih =>
      by_cases hW : W.Nonempty
      · by_cases hexp : ExpandsIndependentOn G l W
        · exact Or.inr ⟨W, Finset.Subset.rfl, hW, hexp⟩
        · rw [ExpandsIndependentOn] at hexp
          push_neg at hexp
          obtain ⟨X, hXW, hXind, hXbad⟩ := hexp
          let N := relativeNeighborFinset G W X
          let R := W \ (X ∪ N)
          have hXnonempty : X.Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hXe
            subst X
            simp [N] at hXbad
          have hXR : Disjoint X R := by
            rw [Finset.disjoint_left]
            intro x hxX hxR
            exact (Finset.mem_sdiff.mp hxR).2 (by simp [hxX])
          have hRW : R ⊆ W := Finset.sdiff_subset
          have hproper : R ⊂ W := by
            have hx : X ⊆ X ∪ N := Finset.subset_union_left
            rw [Finset.ssubset_iff_of_subset hRW]
            obtain ⟨x, hxX⟩ := hXnonempty
            exact ⟨x, hXW hxX, by
              intro hxR
              exact (Finset.mem_sdiff.mp hxR).2 (hx hxX)⟩
          rcases ih R hproper with ⟨I, hIR, hIind, hIcard⟩ |
              ⟨U, hUR, hUne, hUexp⟩
          · left
            refine ⟨X ∪ I, ?_, ?_, ?_⟩
            · exact Finset.union_subset hXW (hIR.trans hRW)
            · rw [SimpleGraph.isIndepSet_iff, Finset.coe_union,
                Set.pairwise_union]
              rw [SimpleGraph.isIndepSet_iff] at hXind hIind
              refine ⟨hXind, hIind, ?_⟩
              intro a haX b hbI hab
              constructor
              · intro hadj
                have hbR : b ∈ R := hIR hbI
                have hbN : b ∈ N := by
                  apply mem_relativeNeighborFinset.mpr
                  exact ⟨hRW hbR, a, haX, hadj⟩
                exact (Finset.mem_sdiff.mp hbR).2 (by simp [hbN])
              · intro hadj
                have hbR : b ∈ R := hIR hbI
                have hbN : b ∈ N := by
                  apply mem_relativeNeighborFinset.mpr
                  exact ⟨hRW hbR, a, haX, hadj.symm⟩
                exact (Finset.mem_sdiff.mp hbR).2 (by simp [hbN])
            · intro _
              have hXN : Disjoint X N := by
                simpa [N] using disjoint_relativeNeighborFinset hXind
              have hXNW : X ∪ N ⊆ W := by
                apply Finset.union_subset hXW
                intro v hv
                exact (mem_relativeNeighborFinset.mp hv).1
              have hsplit : (X ∪ N).card + R.card = W.card := by
                have h := Finset.card_sdiff_add_card_eq_card hXNW
                simpa only [R, add_comm] using h
              have hremoved : (X ∪ N).card < (l + 1) * X.card := by
                rw [Finset.card_union_of_disjoint hXN]
                calc
                  X.card + N.card < X.card + l * X.card :=
                    Nat.add_lt_add_left hXbad X.card
                  _ = (l + 1) * X.card := by ring
              have hXIcard : (X ∪ I).card = X.card + I.card := by
                rw [Finset.card_union_of_disjoint (hXR.mono_right hIR)]
              have hRbound : R.card ≤ (l + 1) * I.card := by
                by_cases hR : R.Nonempty
                · exact (hIcard hR).le
                · have hRe : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
                  simp [hRe]
              rw [hXIcard]
              calc
                W.card = (X ∪ N).card + R.card := hsplit.symm
                _ < (l + 1) * X.card + (l + 1) * I.card :=
                  Nat.add_lt_add_of_lt_of_le hremoved hRbound
                _ = (l + 1) * (X.card + I.card) := by ring
          · exact Or.inr ⟨U, hUR.trans hRW, hUne, hUexp⟩
      · left
        have hWe : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
        subst W
        exact ⟨∅, by simp, by simp [SimpleGraph.isIndepSet_iff], by simp⟩

/-- EFRS expansion-core lemma in the form used for Ramsey bounds. -/
theorem exists_expanding_subregion_of_no_large_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {l n : ℕ} (W : Finset V) (hn : 2 ≤ n)
    (hcard : (l + 1) * (n - 1) ≤ W.card)
    (hfree : ∀ I : Finset V, I ⊆ W →
      G.IsIndepSet (I : Set V) → I.card < n) :
    ∃ U : Finset V, U ⊆ W ∧ U.Nonempty ∧
      ExpandsIndependentOn G l U := by
  rcases independent_or_expanding_subregion G l W with
      ⟨I, hIW, hIind, hlarge⟩ | h
  · have hIlt := hfree I hIW hIind
    have hpred : I.card ≤ n - 1 := by omega
    have hmul : (l + 1) * I.card ≤ (l + 1) * (n - 1) :=
      Nat.mul_le_mul_left (l + 1) hpred
    have hWne : W.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hWe
      subst W
      simp at hcard
      omega
    exact False.elim
      ((Nat.not_lt_of_ge hcard) ((hlarge hWne).trans_le hmul))
  · exact h

end Erdos570
