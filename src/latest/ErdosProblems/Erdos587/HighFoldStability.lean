import ErdosProblems.Erdos587.DyadicSumsets
import ErdosProblems.Erdos587.VolumeStability

/-!
Simultaneous stability of dyadic sumset cardinalities. The extra logarithmic
deletion loss is harmless for the target polylogarithmic upper bound and
permits direct comparison of high-fold sums after a bounded deletion.
-/

open scoped Pointwise

namespace Erdos587.CFP

def dyadicSumsetWithZero (A : Finset ℤ) (k : ℕ) : Finset ℤ :=
  (2 ^ k) • insert 0 A

theorem dyadicSumsetWithZero_nonempty (A : Finset ℤ) (k : ℕ) :
    (dyadicSumsetWithZero A k).Nonempty :=
  ⟨0, Finset.zero_mem_nsmul (Finset.mem_insert_self 0 A)⟩

theorem dyadicSumsetWithZero_mono {A B : Finset ℤ} (hAB : A ⊆ B) (k : ℕ) :
    dyadicSumsetWithZero A k ⊆ dyadicSumsetWithZero B k :=
  Finset.nsmul_subset_nsmul_left (Finset.insert_subset_insert 0 hAB)

theorem dyadicSumsetWithZero_card_le (A : Finset ℤ) (L k : ℕ)
    (hA : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ)) (hk : k ≤ L) :
    (dyadicSumsetWithZero A k).card ≤ 2 ^ (2 * L + 1) := by
  have hAZ : insert 0 A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ) := by
    apply Finset.insert_subset
    · simp
    · exact hA
  have hcard := card_nsmul_le_nat_interval (insert 0 A) (2 ^ L) hAZ (2 ^ k)
  have hpow : 2 ^ k ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hk
  have hp : 0 < (2 : ℕ) ^ (L + L) := by positivity
  have hprod : 2 ^ k * 2 ^ L ≤ 2 ^ (L + L) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hpow
  have htwice : 2 ^ (2 * L + 1) = 2 * 2 ^ (L + L) := by
    rw [show 2 * L = L + L by omega, pow_succ]
    ring
  change ((2 ^ k) • insert 0 A).card ≤ _
  rw [htwice]
  omega

/-- Simultaneously stabilize every dyadic sumset up to scale `2^L`, with
at most `(6*(L+1)^2+3)*r` deletions. Each further deletion of at most `r`
elements retains more than three quarters of each sumset cardinality. -/
theorem exists_subset_with_stable_dyadic_sumsets (A : Finset ℤ) (L r : ℕ)
    (hA : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ)) :
    ∃ B ⊆ A, A.card ≤ B.card + (6 * (L + 1) ^ 2 + 3) * r ∧
      ∀ D ⊆ B, B.card ≤ D.card + r → ∀ k ≤ L,
        3 * (dyadicSumsetWithZero B k).card <
          4 * (dyadicSumsetWithZero D k).card := by
  let V : Fin (L + 1) → Finset ℤ → ℕ := fun i B => (dyadicSumsetWithZero B i.val).card
  have hpos : ∀ B ⊆ A, ∀ i, 0 < V i B := by
    intro B hBA i
    exact Finset.card_pos.mpr (dyadicSumsetWithZero_nonempty B i.val)
  have hmono : ∀ B ⊆ A, ∀ D ⊆ B, ∀ i, V i D ≤ V i B := by
    intro B hBA D hDB i
    exact Finset.card_le_card (dyadicSumsetWithZero_mono hDB i.val)
  have hinitial : ∀ i, V i A ≤ 2 ^ (2 * L + 1) := by
    intro i
    exact dyadicSumsetWithZero_card_le A L i.val hA (by omega)
  obtain ⟨B, hBA, hcost, hstable⟩ := exists_subset_with_stable_volumes_log_bound
    V A r (2 ^ (2 * L + 1)) hpos hmono hinitial
  have hcost' : A.card ≤ B.card + (6 * (L + 1) ^ 2 + 3) * r := by
    simp only [Fintype.card_fin, Nat.log_pow Nat.one_lt_two] at hcost
    have heq : 3 * ((L + 1) * (2 * L + 1 + 1) + 1) = 6 * (L + 1) ^ 2 + 3 := by ring
    rwa [heq] at hcost
  refine ⟨B, hBA, hcost', ?_⟩
  intro D hDB hremove k hk
  exact hstable D hDB hremove ⟨k, by omega⟩

end Erdos587.CFP
