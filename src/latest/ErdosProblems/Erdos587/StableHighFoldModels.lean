import ErdosProblems.Erdos587.HighFoldModels
import ErdosProblems.Erdos587.HighFoldStability

/-!
Combine simultaneous dyadic-cardinality stability with scale selection.
The result is an actual large subset and one proper GAP model in which
every further bounded deletion has a uniform high-fold density bound.
-/

open scoped Pointwise

namespace Erdos587.CFP

theorem exists_stable_highFold_model (A : Finset ℤ) (L b t r : ℕ)
    (hA : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ)) (ht : 0 < t)
    (hwindow : t + t ≤ L) (hambient : L ≤ t * b)
    (hscale : 4 * freimanTSizeFactor (2 ^ (b + 3)) 2 ≤ 2 ^ t) :
    let F := freimanTSizeFactor (2 ^ (b + 3)) 2
    ∃ B ⊆ A, A.card ≤ B.card + (6 * (L + 1) ^ 2 + 3) * r ∧
      ∃ k, t ≤ k ∧ k < t + t ∧
        ∃ Q : GeneralizedAP, Q.rank ≤ b + 1 ∧
          (∀ i, 0 < Q.length i) ∧ Q.TProper (2 ^ k) ∧
          (0 : ℤ) ∈ Q.carrier ∧ insert 0 B ⊆ Q.carrier ∧
          (Q.dilate (2 ^ k)).boxCard ≤ F * (dyadicSumsetWithZero B k).card ∧
          (∀ i, 4 * F ≤ 2 ^ k * Q.length i + 1) ∧
          ∀ D ⊆ B, B.card ≤ D.card + r →
            2 * (Q.dilate (2 ^ k)).boxCard <
              (4 * F) * (dyadicSumsetWithZero D k).card := by
  let F := freimanTSizeFactor (2 ^ (b + 3)) 2
  obtain ⟨B, hBA, hcost, hstable⟩ := exists_subset_with_stable_dyadic_sumsets A L r hA
  have hBZ : insert 0 B ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ) := by
    apply Finset.insert_subset
    · simp
    · exact hBA.trans hA
  have hN : 2 ^ L ≤ (2 ^ t) ^ b := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) hambient
  obtain ⟨k, htk, hkt, Q, _hrank, hpos, hproper, hzero, hBQ, hbox⟩ :=
    exists_polynomial_window_highFold_model (insert 0 B) (2 ^ L) b t hBZ
      (Finset.mem_insert_self 0 B) ht hN
  have hboxpos : 0 < (Q.dilate (2 ^ k)).boxCard :=
    Finset.prod_pos (fun i _hi => Nat.succ_pos _)
  have hF : 0 < F := by
    by_contra hnot
    have hFzero : F = 0 := by omega
    change (Q.dilate (2 ^ k)).boxCard ≤ F * ((2 ^ k) • insert 0 B).card at hbox
    rw [hFzero, zero_mul] at hbox
    omega
  have hpow : 2 ^ t ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) htk
  have hscale' : 4 * F ≤ 2 ^ k := hscale.trans hpow
  have hrank : Q.rank ≤ b + 1 := by
    apply Q.rank_le_of_polynomial_dilate_bound hpos (2 ^ k) (2 ^ L) b F (by omega)
    · exact hN.trans (Nat.pow_le_pow_left hpow b)
    · exact hbox.trans (Nat.mul_le_mul_left F
        (card_nsmul_le_nat_interval (insert 0 B) (2 ^ L) hBZ (2 ^ k)))
  refine ⟨B, hBA, hcost, k, htk, hkt, Q, hrank, hpos, hproper, hzero, hBQ, hbox, ?_, ?_⟩
  · intro i
    have hm : 2 ^ k ≤ 2 ^ k * Q.length i := by
      calc
        2 ^ k = 2 ^ k * 1 := by simp
        _ ≤ 2 ^ k * Q.length i := Nat.mul_le_mul_left _ (by have hi := hpos i; omega)
    omega
  · intro D hDB hremove
    have hs := hstable D hDB hremove k (by omega)
    have hm := Nat.mul_lt_mul_of_pos_left hs hF
    change (Q.dilate (2 ^ k)).boxCard ≤ F * (dyadicSumsetWithZero B k).card at hbox
    calc
      2 * (Q.dilate (2 ^ k)).boxCard ≤ 3 * (F * (dyadicSumsetWithZero B k).card) := by
        nlinarith
      _ < (4 * F) * (dyadicSumsetWithZero D k).card := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hm

end Erdos587.CFP
