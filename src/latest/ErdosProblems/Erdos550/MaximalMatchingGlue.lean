import Mathlib
import ErdosProblems.Erdos550.ReducedMatching

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Maximal matching outside the two head clusters

This is the matching used in the paper's direct off-Turán route.  It is taken in
`Q - {X,Y}`, not in the common neighbourhood of the heads.  Maximality makes the
unmatched set independent, so an `α(Q)` bound immediately says that the matching
covers all but few clusters.  No lower bound on the density of a head-common
subgraph is involved.
-/

open Finset SimpleGraph

namespace Erdos550

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spanning subgraph obtained by deleting all edges incident with either
head. -/
def awayFromHeads (R : SimpleGraph ι) (X Y : ι) : SimpleGraph ι where
  Adj a b := R.Adj a b ∧ a ≠ X ∧ a ≠ Y ∧ b ≠ X ∧ b ≠ Y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.2.1, h.2.2.2.2, h.2.1, h.2.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

instance (R : SimpleGraph ι) [DecidableRel R.Adj] (X Y : ι) :
    DecidableRel (awayFromHeads R X Y).Adj := by
  intro a b
  change Decidable (R.Adj a b ∧ a ≠ X ∧ a ≠ Y ∧ b ≠ X ∧ b ≠ Y)
  infer_instance

/-- The clusters not covered by a matching and distinct from both heads. -/
def unmatchedAway (X Y : ι) (M : Finset (ι × ι)) : Finset ι :=
  Finset.univ \ (insert X (singleton Y) ∪ support M)

lemma mem_unmatchedAway_iff (X Y : ι) (M : Finset (ι × ι)) (a : ι) :
    a ∈ unmatchedAway X Y M ↔ a ≠ X ∧ a ≠ Y ∧ a ∉ support M := by
  simp [unmatchedAway]

/-- The unmatched vertices of a maximum matching outside the heads form an
independent set in the original reduced graph. -/
theorem maximum_matching_away_unmatched_independent
    (R : SimpleGraph ι) [DecidableRel R.Adj] (X Y : ι) :
    ∃ M : Finset (ι × ι),
      IsMatchingFamily (awayFromHeads R X Y) M ∧
      (∀ P, IsMatchingFamily (awayFromHeads R X Y) P → P.card ≤ M.card) ∧
      ∀ a ∈ unmatchedAway X Y M, ∀ b ∈ unmatchedAway X Y M,
        ¬ R.Adj a b := by
  obtain ⟨M, hM, hmax⟩ := exists_maximum_matchingFamily (awayFromHeads R X Y)
  refine ⟨M, hM, hmax, ?_⟩
  intro a ha b hb hab
  have ha' := (mem_unmatchedAway_iff X Y M a).mp ha
  have hb' := (mem_unmatchedAway_iff X Y M b).mp hb
  have haway : (awayFromHeads R X Y).Adj a b :=
    ⟨hab, ha'.1, ha'.2.1, hb'.1, hb'.2.1⟩
  rcases maximal_matchingFamily_covers hM hmax haway with h | h
  · exact ha'.2.2 h
  · exact hb'.2.2 h

/-- Abstract `α(Q)` consequence: if every set of at least `B` clusters spans an
edge, then a maximum matching outside the heads leaves fewer than `B` unmatched
clusters. -/
theorem exists_maximum_matching_away_with_small_unmatched
    (R : SimpleGraph ι) [DecidableRel R.Adj] (X Y : ι) (B : ℕ)
    (hα : ∀ A : Finset ι, B ≤ A.card →
      ∃ a ∈ A, ∃ b ∈ A, R.Adj a b) :
    ∃ M : Finset (ι × ι),
      IsMatchingFamily (awayFromHeads R X Y) M ∧
      (∀ P, IsMatchingFamily (awayFromHeads R X Y) P → P.card ≤ M.card) ∧
      (unmatchedAway X Y M).card < B := by
  obtain ⟨M, hM, hmax, hind⟩ :=
    maximum_matching_away_unmatched_independent R X Y
  refine ⟨M, hM, hmax, ?_⟩
  by_contra h
  obtain ⟨a, ha, b, hb, hab⟩ := hα (unmatchedAway X Y M) (by omega)
  exact hind a ha b hb hab

omit [Fintype ι] in
/-- Every edge of the chosen matching is an edge of the original reduced graph,
and all its endpoints avoid both heads. -/
lemma matching_away_edge_data
    (R : SimpleGraph ι) [DecidableRel R.Adj] (X Y : ι)
    (M : Finset (ι × ι)) (hM : IsMatchingFamily (awayFromHeads R X Y) M)
    (p : ι × ι) (hp : p ∈ M) :
    R.Adj p.1 p.2 ∧ p.1 ≠ X ∧ p.1 ≠ Y ∧ p.2 ≠ X ∧ p.2 ≠ Y :=
  hM.1 p hp

end Erdos550
