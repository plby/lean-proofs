import ErdosProblems.Erdos73.PathCongestion

/-! A maximal disjoint family and incidence counting give bounded-congestion selection. -/

namespace Erdos73
noncomputable section
open scoped Classical

open Finset

theorem exists_disjoint_subfamily_of_bounded_congestion
    {I X : Type*} [DecidableEq I] [DecidableEq X]
    (s : Finset I) (R : I → Finset X) (q b k : ℕ)
    (hne : ∀ i ∈ s, (R i).Nonempty) (hrank : ∀ i ∈ s, (R i).card ≤ q)
    (hcong : ∀ x, (s.filter (fun i => x ∈ R i)).card ≤ b)
    (hsize : q * b * (k - 1) < s.card) :
    ∃ t : Finset I, t ⊆ s ∧ k ≤ t.card ∧ (t : Set I).PairwiseDisjoint R := by
  let C := s.powerset.filter (fun t : Finset I => (t : Set I).PairwiseDisjoint R)
  obtain ⟨t, htmax⟩ := C.exists_maximal (filter_nonempty_iff.mpr
    ⟨∅, empty_mem_powerset s, by simp⟩)
  simp only [C, mem_filter, mem_powerset] at htmax
  obtain ⟨hts, htdis⟩ := htmax.1
  let Z := t.biUnion R
  have hhit (i : I) (hi : i ∈ s) : ¬ Disjoint (R i) Z := by
    intro hn
    have hit : i ∉ t := by
      intro hit
      obtain ⟨x, hx⟩ := hne i hi
      exact Finset.disjoint_left.mp hn hx (mem_biUnion.mpr ⟨i, hit, hx⟩)
    apply htmax.not_gt _ (ssubset_insert hit)
    rw [insert_subset_iff, coe_insert]
    refine ⟨⟨hi, hts⟩, htdis.insert ?_⟩
    intro j hj _
    exact (disjoint_biUnion_right (R i) t R).mp hn j hj
  refine ⟨t, hts, ?_, htdis⟩
  by_contra hsmall
  have htcard : t.card ≤ k - 1 := by omega
  have hZ : Z.card ≤ t.card * q := card_biUnion_le_card_mul t R q
    (fun i hi => hrank i (hts hi))
  have hcount := card_le_mul_of_hits_with_congestion s R Z b
    (fun i hi => Finset.not_disjoint_iff.mp (hhit i hi)) (fun x _ => hcong x)
  have hh : s.card ≤ q * b * (k - 1) := by
    calc
      s.card ≤ Z.card * b := hcount
      _ ≤ (t.card * q) * b := Nat.mul_le_mul_right b hZ
      _ ≤ ((k - 1) * q) * b := Nat.mul_le_mul_right b (Nat.mul_le_mul_right q htcard)
      _ = q * b * (k - 1) := by ring
  omega

end
end Erdos73
