/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.MarkedTripleLoads

/-!
# Literal occupied-set accounting for a family of private groups

All sums count source mass or prescribed marks. Used vertices are the
actual union of previous images and the outside prefix; the outside prefix
is allowed to be arbitrarily large, but must avoid the group supports.
-/

open scoped BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoMarkedPrefixLoads

open Finset

variable {I J V : Type*} [DecidableEq I]
variable [Fintype J] [DecidableEq V]

def groupLoad (assign : J → I) (mass : J → ℕ) (i : I) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => assign j = i), mass j

theorem sum_groupLoad [Fintype I] (assign : J → I) (mass : J → ℕ) :
    ∑ i, groupLoad assign mass i = ∑ j, mass j := by
  simp only [groupLoad, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem groupLoad_le_total (assign : J → I) (mass : J → ℕ) (i : I) :
    groupLoad assign mass i ≤ ∑ j, mass j :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

def used (base : Finset V) (image : J → Finset V) := base ∪ Finset.univ.biUnion image

theorem used_inter_subset (base : Finset V) (image : J → Finset V)
    (support : I → Finset V) (assign : J → I)
    (hbase : ∀ i, Disjoint base (support i))
    (hsupport : ∀ i k, i ≠ k → Disjoint (support i) (support k))
    (himage : ∀ j, image j ⊆ support (assign j))
    (i : I) (target : Finset V) (htarget : target ⊆ support i) :
    used base image ∩ target ⊆
      (Finset.univ.filter (fun j => assign j = i)).biUnion (fun j => image j ∩ target) := by
  intro v hv
  have ht := (Finset.mem_inter.mp hv).2
  rcases Finset.mem_union.mp (Finset.mem_inter.mp hv).1 with hb | hu
  · exact (Finset.disjoint_left.mp (hbase i) hb (htarget ht)).elim
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hu
  have hji : assign j = i := by
    by_contra hn
    exact Finset.disjoint_left.mp (hsupport (assign j) i hn) (himage j hj) (htarget ht)
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩,
    Finset.mem_inter.mpr ⟨hj, ht⟩⟩

theorem used_inter_card_le (base : Finset V) (image : J → Finset V)
    (support : I → Finset V) (assign : J → I) (mass : J → ℕ)
    (hbase : ∀ i, Disjoint base (support i))
    (hsupport : ∀ i k, i ≠ k → Disjoint (support i) (support k))
    (himage : ∀ j, image j ⊆ support (assign j))
    (hmass : ∀ j, (image j).card ≤ mass j)
    (i : I) (target : Finset V) (htarget : target ⊆ support i) :
    (used base image ∩ target).card ≤ groupLoad assign mass i := by
  have hsub := used_inter_subset base image support assign hbase hsupport himage i target htarget
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  apply Finset.sum_le_sum
  intro j _
  exact (Finset.card_le_card Finset.inter_subset_left).trans (hmass j)

theorem used_center_bound (base : Finset V) (image : J → Finset V)
    (center pair : I → Finset V) (assign : J → I) (mass marks : J → ℕ)
    (hbase : ∀ i, Disjoint base (center i ∪ pair i))
    (hsupport : ∀ i k, i ≠ k → Disjoint (center i ∪ pair i) (center k ∪ pair k))
    (himage : ∀ j, image j ⊆ center (assign j) ∪ pair (assign j))
    (hlocal : ∀ j, 3 * ((image j) ∩ center (assign j)).card ≤ mass j + 3 * marks j)
    (i : I) :
    3 * (used base image ∩ center i).card ≤ groupLoad assign mass i + 3 * groupLoad assign marks i := by
  have hsub := used_inter_subset base image (fun i => center i ∪ pair i) assign
    hbase hsupport himage i (center i) Finset.subset_union_left
  have hcard := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hsum : (∑ j ∈ Finset.univ.filter (fun j => assign j = i),
      3 * ((image j) ∩ center i).card) ≤
      ∑ j ∈ Finset.univ.filter (fun j => assign j = i), (mass j + 3 * marks j) := by
    apply Finset.sum_le_sum
    intro j hj
    simpa only [(Finset.mem_filter.mp hj).2] using hlocal j
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  exact (Nat.mul_le_mul_left 3 hcard).trans hsum

end Erdos547b.ZhaoMarkedPrefixLoads

#print axioms Erdos547b.ZhaoMarkedPrefixLoads.sum_groupLoad
#print axioms Erdos547b.ZhaoMarkedPrefixLoads.used_inter_card_le
#print axioms Erdos547b.ZhaoMarkedPrefixLoads.used_center_bound
