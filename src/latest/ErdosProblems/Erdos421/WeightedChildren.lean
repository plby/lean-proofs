import ErdosProblems.Erdos421.ChildEncoding
import ErdosProblems.Erdos421.WitnessLengths

/-! # Reciprocal gap lengths of actual children -/

namespace Erdos421

theorem shortChildren_reciprocal_sum_scale (i u : ℕ) :
    (∑ k ∈ shortChildren (2 ^ (60 * u)) i, (1 : ℝ) / gapLength k) ≤
      (60 * u : ℝ) ^ 2 * ((2 ^ (3 * u) : ℕ) : ℝ) ^ 2 := by
  classical
  let I := shortChildren (2 ^ (60 * u)) i
  have hmem : ∀ k : I, Rejected k ∧ ¬ Raw k ∧ ShortGap k ∧
      prime (k + 1) ≤ 2 ^ (60 * u) ∧ parent k = i := fun k ↦ mem_shortChildren.mp k.property
  let w : (k : I) → ParentData k :=
    fun k ↦ chosenParentData k ⟨(hmem k).1, (hmem k).2.1⟩
  have hparent : ∀ k : I, (w k).index = i := by
    intro k
    have h : Rejected k ∧ ¬ Raw k := ⟨(hmem k).1, (hmem k).2.1⟩
    have hp : parent k = (w k).index := by simp only [parent, dif_pos h, w]
    exact hp.symm.trans (hmem k).2.2.2.2
  have hg : ∀ k : I, gapLength k ≤ 2 ^ (3 * u) :=
    fun k ↦ (hmem k).2.2.1.length_le_scale (hmem k).2.2.2.1
  have hL : ∀ k : I, (w k).witness.E.card ≤ (60 * u) * 2 ^ (3 * u) := fun k ↦
    ((w k).witness.length_le_log_mul_gap (hmem k).2.2.2.1).trans
      (Nat.mul_le_mul_left _ (hg k))
  have hH : ∀ k : I, (w k).witness.n - (w k).witness.m + 1 ≤ 2 ^ (3 * u) := fun k ↦
    (w k).witness.laterLength_le_gap.trans (hg k)
  have h := parentData_reciprocal_sum_bound I i (60 * u) ((60 * u) * 2 ^ (3 * u))
    (2 ^ (3 * u)) w hparent hL hH
    (fun k ↦ (w k).witness.length_le_log_mul_gap (hmem k).2.2.2.1)
  rw [Finset.sum_coe_sort I (fun k : ℕ ↦ (1 : ℝ) / gapLength k)] at h
  have heq : ((60 * u : ℕ) : ℝ) * (((60 * u) * 2 ^ (3 * u) : ℕ) : ℝ) *
      ((2 ^ (3 * u) : ℕ) : ℝ) = (60 * u : ℝ) ^ 2 * ((2 ^ (3 * u) : ℕ) : ℝ) ^ 2 := by
    push_cast
    ring
  rwa [heq] at h

end Erdos421
