import ErdosProblems.Erdos1148.MaximalNatRuns
import Mathlib.Data.List.Sort

/-! # Ordering maximal runs by their starting times -/

namespace Erdos1148.DukeArithmetic

theorem exists_ordered_maximalNatRuns (V : Finset ℕ) :
    ∃ l : List (ℕ × ℕ), l.toFinset = maximalNatRuns V ∧ l.Nodup ∧
      l.Pairwise (fun p q => p.2 < q.1) := by
  classical
  let r : (ℕ × ℕ) → (ℕ × ℕ) → Prop := fun p q => p.1 ≤ q.1
  letI : Std.Total r := ⟨fun p q => Nat.le_total p.1 q.1⟩
  letI : IsTrans (ℕ × ℕ) r := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩
  let l := (maximalNatRuns V).toList.mergeSort (r · ·)
  have hperm : l.Perm (maximalNatRuns V).toList := List.mergeSort_perm _ _
  have hmem (p : ℕ × ℕ) : p ∈ l ↔ p ∈ maximalNatRuns V := by
    exact hperm.mem_iff.trans Finset.mem_toList
  have hnodup : l.Nodup := hperm.nodup_iff.mpr (maximalNatRuns V).nodup_toList
  have hpair : l.Pairwise r := List.pairwise_mergeSort' r _
  refine ⟨l, ?_, hnodup, ?_⟩
  · ext p
    exact List.mem_toFinset.trans (hmem p)
  · apply (hpair.and hnodup).imp_of_mem
    intro p q hp hq hpq
    have hp' := (hmem p).mp hp
    have hq' := (hmem q).mp hq
    apply maximalNatRuns_end_lt_start hp' hq'
    exact lt_of_le_of_ne hpq.1 (fun heq => hpq.2 (maximalNatRuns_fst_injOn V hp' hq' heq))

end Erdos1148.DukeArithmetic
