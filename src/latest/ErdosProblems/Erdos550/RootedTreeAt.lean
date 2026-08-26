import Mathlib
import ErdosProblems.Erdos550.RegularPairTree

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rooting a finite tree at a prescribed vertex

The block order in the off--Turán embedding starts at a chosen seed.  This
module records the standard distance-to-the-root orientation with that root
kept explicit.  In particular, the root is the unique vertex without a parent,
and every tree edge receives exactly one of its two possible orientations.
-/

open SimpleGraph

namespace Erdos550

open Classical

/-- Parent/rank data for a finite tree rooted at the prescribed vertex `r`. -/
lemma IsTree.exists_rooted_edge_structure_at
    {A : Type*} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) [DecidableRel T.Adj] (hT : T.IsTree) (r : A) :
    ∃ (parent : A → Option A) (rank : A → ℕ),
      parent r = none ∧
      (∀ a, parent a = none → a = r) ∧
      (∀ a b, parent a = some b → rank b < rank a) ∧
      (∀ a b, parent a = some b → T.Adj a b) ∧
      (∀ a b, T.Adj a b →
        parent a = some b ∨ parent b = some a) := by
  obtain ⟨par, hpar⟩ :
      ∃ par : A → A,
        (∀ a, a ≠ r →
          T.Adj a (par a) ∧ T.dist (par a) r < T.dist a r) ∧
        (∀ a, a ≠ r → ∀ b,
          T.Adj a b → T.dist b r < T.dist a r → b = par a) := by
    choose! par hpar using
      fun a ha => tree_closer_neighbor_exists_unique T hT r a ha
    exact ⟨par, fun a ha => (hpar a ha).1,
      fun a ha b hb hbr => (hpar a ha).2 b ⟨hb, hbr⟩⟩
  let parent : A → Option A :=
    fun a => if a = r then none else some (par a)
  let rank : A → ℕ := fun a => T.dist a r
  refine ⟨parent, rank, ?_, ?_, ?_, ?_, ?_⟩
  · simp [parent]
  · intro a ha
    by_contra har
    simp [parent, har] at ha
  · intro a b hab
    have har : a ≠ r := by
      intro h
      subst a
      simp [parent] at hab
    have hb : par a = b := by
      simpa [parent, har] using! hab
    subst b
    exact (hpar.1 a har).2
  · intro a b hab
    have har : a ≠ r := by
      intro h
      subst a
      simp [parent] at hab
    have hb : par a = b := by
      simpa [parent, har] using! hab
    subst b
    exact (hpar.1 a har).1
  · intro a b hab
    by_cases har : a = r
    · subst a
      right
      have hbr : b ≠ r := hab.ne.symm
      have hdist : T.dist r r < T.dist b r := by
        rw [SimpleGraph.dist_self]
        exact Nat.zero_lt_of_ne_zero fun hz =>
          (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hz).elim
            (fun h => hbr h) (fun h => h (hT.1 b r))
      have hba : r = par b :=
        hpar.2 b hbr r hab.symm hdist
      show parent b = some r
      rw [show parent b = some (par b) by simp [parent, hbr], ← hba]
    · by_cases hbr : b = r
      · subst b
        left
        have hdist : T.dist r r < T.dist a r := by
          rw [SimpleGraph.dist_self]
          exact Nat.zero_lt_of_ne_zero fun hz =>
            (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hz).elim
              (fun h => har h) (fun h => h (hT.1 a r))
        have hab' : r = par a :=
          hpar.2 a har r hab hdist
        show parent a = some r
        rw [show parent a = some (par a) by simp [parent, har], ← hab']
      · rcases lt_trichotomy (T.dist a r) (T.dist b r) with hlt | heq | hgt
        · right
          have hba : a = par b :=
            hpar.2 b hbr a hab.symm hlt
          simp [parent, hbr, hba]
        · exfalso
          apply hT.dist_ne_of_adj r hab
          simpa only [SimpleGraph.dist_comm] using! heq
        · left
          have hab' : b = par a :=
            hpar.2 a har b hab hgt
          simp [parent, har, hab']

end Erdos550
