import Mathlib
import ErdosProblems.Erdos550.HPLoadAccounting

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Geometry of matching parts in a finite partition

Injectivity of the two endpoint maps makes all matching parts pairwise
disjoint.  Heads chosen outside the endpoint images are disjoint from every
matching region as well.
-/

open Finset Finpartition

namespace Erdos550

open Classical

lemma partition_matching_left_right_disjoint
    {V κ : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V))
    (cL cR : κ → {C // C ∈ P.parts})
    (hinj : Function.Injective (Sum.elim cL cR))
    (k : κ) :
    Disjoint (cL k).1 (cR k).1 := by
  have hne : cL k ≠ cR k := by
    intro h
    have himpossible :
        (Sum.inl k : Sum κ κ) = Sum.inr k := hinj h
    cases himpossible
  exact P.disjoint (cL k).2 (cR k).2
    (fun h => hne (Subtype.ext h))

lemma partition_matching_edges_disjoint
    {V κ : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V))
    (cL cR : κ → {C // C ∈ P.parts})
    (hinj : Function.Injective (Sum.elim cL cR))
    (k j : κ) (hkj : k ≠ j) :
    Disjoint ((cL k).1 ∪ (cR k).1)
      ((cL j).1 ∪ (cR j).1) := by
  rw [Finset.disjoint_left]
  intro v hvk hvj
  rcases Finset.mem_union.mp hvk with hvkL | hvkR
  · rcases Finset.mem_union.mp hvj with hvjL | hvjR
    · exact Finset.disjoint_left.mp
        (P.disjoint (cL k).2 (cL j).2 (fun h =>
          hkj (Sum.inl.inj (hinj (Subtype.ext h))))) hvkL hvjL
    · have hcross : cL k ≠ cR j := by
        intro h
        have himpossible :
            (Sum.inl k : Sum κ κ) = Sum.inr j := hinj h
        cases himpossible
      exact Finset.disjoint_left.mp
        (P.disjoint (cL k).2 (cR j).2
          (fun h => hcross (Subtype.ext h))) hvkL hvjR
  · rcases Finset.mem_union.mp hvj with hvjL | hvjR
    · have hcross : cR k ≠ cL j := by
        intro h
        have himpossible :
            (Sum.inr k : Sum κ κ) = Sum.inl j := hinj h
        cases himpossible
      exact Finset.disjoint_left.mp
        (P.disjoint (cR k).2 (cL j).2
          (fun h => hcross (Subtype.ext h))) hvkR hvjL
    · exact Finset.disjoint_left.mp
        (P.disjoint (cR k).2 (cR j).2 (fun h =>
          hkj (Sum.inr.inj (hinj (Subtype.ext h))))) hvkR hvjR

lemma partition_head_matching_edge_disjoint
    {V κ : Type*} [Fintype V] [DecidableEq V]
    (P : Finpartition (Finset.univ : Finset V))
    (head : {C // C ∈ P.parts})
    (cL cR : κ → {C // C ∈ P.parts})
    (haway : ∀ k, cL k ≠ head ∧ cR k ≠ head)
    (k : κ) :
    Disjoint head.1 ((cL k).1 ∪ (cR k).1) := by
  rw [Finset.disjoint_left]
  intro v hvHead hvSide
  rcases Finset.mem_union.mp hvSide with hvL | hvR
  · exact Finset.disjoint_left.mp
      (P.disjoint head.2 (cL k).2
        (fun h => (haway k).1 (Subtype.ext h).symm)) hvHead hvL
  · exact Finset.disjoint_left.mp
      (P.disjoint head.2 (cR k).2
        (fun h => (haway k).2 (Subtype.ext h).symm)) hvHead hvR

end Erdos550
