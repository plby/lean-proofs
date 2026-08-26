import ErdosProblems.Erdos547.TransportDeficiency

/-!
# Finite fractional Hall's theorem

Among maximum transports, choose one with the largest set of deficient rows.
A two-row redistribution makes that set closed under positive incoming flow.
Its neighbourhood is then a Hall obstruction unless all rows are full.
-/

noncomputable section

namespace Erdos547.DPRS.Transport

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V]

open scoped Classical in
theorem exists_full_rows_of_hall (P : V → V → Prop) (a b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u)
    (hHall : ∀ S : Finset V, (∑ u ∈ S, a u) ≤
      ∑ v ∈ Finset.univ.filter (fun v ↦ ∃ u ∈ S, P u v), b v) :
    ∃ f : Transport P a b, ∀ u, f.row u = a u := by
  classical
  obtain ⟨f, hmax, hdef⟩ := exists_maximum_with_deficiency P a b ha hb
  have hnone : ¬ f.deficientRows.Nonempty := by
    rintro ⟨x, hx⟩
    let R := f.deficientRows
    let C := Finset.univ.filter (fun v ↦ ∃ u ∈ R, P u v)
    have hfull (v : V) (hv : v ∈ C) : f.col v = b v := by
      obtain ⟨u, hu, huv⟩ := (Finset.mem_filter.mp hv).2
      exact maximum_saturates hmax huv (Finset.mem_filter.mp hu).2
    have hzero (u : V) (hu : u ∉ R) (v : V) (hv : v ∈ C) : f.weight u v = 0 := by
      apply le_antisymm _ (f.nonnegative u v)
      apply le_of_not_gt
      intro hp
      obtain ⟨z, hz, hzv⟩ := (Finset.mem_filter.mp hv).2
      exact hu (maximum_deficiency_closed hmax hdef hz hzv hp)
    have he : (∑ v ∈ C, b v) = ∑ u ∈ R, f.row u := by
      calc
        _ = ∑ v ∈ C, f.col v := Finset.sum_congr rfl fun v hv ↦ (hfull v hv).symm
        _ = ∑ u, ∑ v ∈ C, f.weight u v := Finset.sum_comm
        _ = ∑ u ∈ R, ∑ v ∈ C, f.weight u v := by
          symm
          exact Finset.sum_subset (Finset.subset_univ _)
            (fun u _ hu ↦ Finset.sum_eq_zero fun v hv ↦ hzero u hu v hv)
        _ = ∑ u ∈ R, f.row u := by
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_subset (Finset.subset_univ _)
          intro v _ hv
          exact f.supported u v (fun huv ↦ hv (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, u, hu, huv⟩))
    have hlt : (∑ u ∈ R, f.row u) < ∑ u ∈ R, a u := Finset.sum_lt_sum
      (fun u _ ↦ f.row_bound u) ⟨x, hx, (Finset.mem_filter.mp hx).2⟩
    have hh := hHall R
    change (∑ u ∈ R, a u) ≤ ∑ v ∈ C, b v at hh
    rw [he] at hh
    exact not_lt_of_ge hh hlt
  refine ⟨f, fun u ↦ le_antisymm (f.row_bound u) ?_⟩
  apply le_of_not_gt
  intro hu
  exact hnone ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩

end Erdos547.DPRS.Transport

#print axioms Erdos547.DPRS.Transport.exists_full_rows_of_hall
