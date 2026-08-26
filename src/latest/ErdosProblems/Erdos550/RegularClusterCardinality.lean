import Mathlib

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Cardinality facts for disjoint regularity clusters

These elementary lemmas expose the quantitative consequences of the nonempty,
pairwise-disjoint cluster family returned by the regularity lemma.  In particular,
the number of reduced vertices is at most the host order, and the cardinality of
a union of selected clusters is the sum of their cardinalities.
-/

open Finset

namespace Erdos550

/-
A nonempty pairwise-disjoint family of clusters has at most as many indices
as the ambient finite vertex type.
-/
lemma cluster_index_card_le
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (C : ι → Finset V)
    (hne : ∀ i, (C i).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j)) :
    Fintype.card ι ≤ Fintype.card V := by
  choose f hf using hne;
  exact Fintype.card_le_of_injective f fun i j hij => Classical.not_not.1 fun hi => Finset.disjoint_left.1 ( hdisj i j hi ) ( hf i ) ( hij ▸ hf j )

/-
The union of any selected pairwise-disjoint clusters has cardinality equal
to the sum of their cardinalities.
-/
lemma card_biUnion_clusters
    {V ι : Type*} [DecidableEq V]
    (C : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (S : Finset ι) :
    (S.biUnion C).card = ∑ i ∈ S, (C i).card := by
  exact Finset.card_biUnion fun i hi j hj hij => hdisj i j hij

/-
A uniform lower bound on cluster sizes yields the corresponding lower bound
on the union of any selected cluster set.
-/
lemma cluster_union_lower_bound
    {V ι : Type*} [DecidableEq V]
    (C : ι → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (smin : ℕ) (hmin : ∀ i, smin ≤ (C i).card)
    (S : Finset ι) :
    S.card * smin ≤ (S.biUnion C).card := by
  rw [ card_biUnion_clusters C hdisj S ] ; exact le_trans ( by simp +decide ) ( Finset.sum_le_sum fun i hi => hmin i ) ;

end Erdos550
