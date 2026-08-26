import ErdosProblems.Erdos547.RectangularTransport

/-!
# Hall inequalities for mandatory and optional demand
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

open scoped Classical in
def graphNeighbours (G : SimpleGraph V) (S : Finset V) : Finset V :=
  Finset.univ.filter (fun v ↦ ∃ u ∈ S, G.Adj u v)

theorem independent_demand_hall (G : SimpleGraph V) (a b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ b u)
    (hI : ∀ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
      (∑ u ∈ I, a u) ≤ ∑ v ∈ graphNeighbours G I, b v)
    (U W : Finset V) :
    (∑ u ∈ U, a u) + (∑ u ∈ W, (b u - a u)) ≤
      ∑ v ∈ graphNeighbours G (U ∪ W) ∪ W, b v := by
  classical
  let K := U ∪ W
  let N := graphNeighbours G K
  let I := K \ (W ∪ N)
  let Z := W ∪ (K ∩ N)
  have hb (u : V) : 0 ≤ b u := (ha u).trans (hab u)
  have hpoint (u : V) : (if u ∈ U then a u else 0) +
      (if u ∈ W then b u - a u else 0) ≤
      (if u ∈ Z then b u else 0) + (if u ∈ I then a u else 0) := by
    by_cases hu : u ∈ U <;> by_cases hw : u ∈ W <;> by_cases hn : u ∈ N <;>
      simp only [I, Z, K, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
        hu, hw, hn, or_true, or_false, and_true,
        and_false, not_true_eq_false, not_false_eq_true, if_true, if_false,
        add_zero, zero_add]
    all_goals linarith [ha u, hab u, hb u]
  have hD : (∑ u ∈ U, a u) + (∑ u ∈ W, (b u - a u)) ≤
      (∑ u ∈ Z, b u) + ∑ u ∈ I, a u := by
    have hh := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset V)) ↦ hpoint u)
    simpa only [Finset.sum_add_distrib, Finset.sum_ite_mem_eq] using hh
  have hind : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
    intro u hu v hv huv
    have huK := (Finset.mem_sdiff.mp hu).1
    have hvN : v ∉ N := fun hh ↦ (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ hh)
    exact hvN (Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, huK, huv⟩)
  have hZK : Z ⊆ K := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Finset.mem_union_right _ hu
    · exact (Finset.mem_inter.mp hu).1
  have hNIN : graphNeighbours G I ⊆ N := by
    intro v hv
    obtain ⟨u, hu, huv⟩ := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, (Finset.mem_sdiff.mp hu).1, huv⟩
  have hdis : Disjoint Z (graphNeighbours G I) := Finset.disjoint_left.mpr fun v hv hvI ↦ by
    obtain ⟨u, hu, huv⟩ := (Finset.mem_filter.mp hvI).2
    have huN : u ∉ N := fun hh ↦ (Finset.mem_sdiff.mp hu).2 (Finset.mem_union_right _ hh)
    exact huN (Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hZK hv, huv.symm⟩)
  have hsub : Z ∪ graphNeighbours G I ⊆ N ∪ W := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · rcases Finset.mem_union.mp hu with hu | hu
      · exact Finset.mem_union_right _ hu
      · exact Finset.mem_union_left _ (Finset.mem_inter.mp hu).2
    · exact Finset.mem_union_left _ (hNIN hu)
  calc
    _ ≤ (∑ u ∈ Z, b u) + ∑ u ∈ I, a u := hD
    _ ≤ (∑ u ∈ Z, b u) + ∑ u ∈ graphNeighbours G I, b u := add_le_add le_rfl (hI I hind)
    _ = ∑ u ∈ Z ∪ graphNeighbours G I, b u := (Finset.sum_union hdis).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ ↦ hb u)

end Erdos547.DPRS

#print axioms Erdos547.DPRS.independent_demand_hall
