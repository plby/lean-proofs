import ErdosProblems.Erdos587.HooleyWeakStability
import ErdosProblems.Erdos587.HooleyFiniteIndexSpan
import ErdosProblems.Erdos587.UniformHighFold

/-! # Constant-deletion-loss robust coordinate models for interval sets -/

open scoped Pointwise
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem delta_exists_weak_highFold_model (b₀ : ℕ) :
    ∃ C K : ℕ, 0 < C ∧ 0 < K ∧ ∀ (b₁ : ℕ) (A : Finset ℤ) (L k t₀ t₁ : ℕ),
      A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ) → k ≤ L → 0 < t₀ → 0 < t₁ →
      L ≤ t₀ * b₀ → L ≤ t₁ * b₁ → C ≤ 2 ^ t₀ → C * 2 ^ (t₀ + t₀) ≤ 2 ^ k →
      4 * freimanTSizeFactor K 2 * 2 ^ t₁ ≤ 2 ^ k → 3 ^ (2 * b₁ + 2) * 4 ≤ A.card →
      ∃ B ⊆ A, A.card ≤ 3 ^ (2 * b₁ + 2) * B.card ∧ 4 ≤ B.card ∧
        ∃ P : GeneralizedAP, P.rank ≤ freimanRank K ∧
          (∀ i, 0 < P.length i) ∧ P.TProper (2 ^ k) ∧
          (0 : ℤ) ∈ P.carrier ∧ insert 0 B ⊆ P.carrier ∧
          (P.dilate (2 ^ k)).boxCard ≤ freimanTSizeFactor K 2 * (dyadicSumsetWithZero B k).card ∧
          ∀ D ⊆ B, B.card ≤ 3 * D.card →
            2 * (P.dilate (2 ^ k)).boxCard <
              (4 * freimanTSizeFactor K 2 * 2 ^ t₁) * (dyadicSumsetWithZero D k).card ∧
            (generatedSubgroup P.centeredCoordinates D).FiniteIndex ∧
            (generatedSubgroup P.centeredCoordinates D).index ≤
              (4 * freimanTSizeFactor K 2 * 2 ^ t₁) ^ P.rank ∧
            Submodule.span ℝ ((intCastVec ∘ P.centeredCoordinates) '' (D : Set ℤ)) = ⊤ := by
  classical
  obtain ⟨C, K, hC, hK, hdouble⟩ := exists_uniform_highFold_doubling b₀
  refine ⟨C, K, hC, hK, ?_⟩
  intro b₁ A L k t₀ t₁ hA hk ht₀ ht₁ hamb₀ hamb₁ hscale hH hwidth hcard
  obtain ⟨B, hBA, hcost, hstable⟩ :=
    delta_exists_relative_highFold_subset A L k t₁ b₁ hA hk ht₁ hamb₁
  have hBcard : 4 ≤ B.card := Nat.le_of_mul_le_mul_left (hcard.trans hcost) (by positivity)
  have hBbox : insert 0 B ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ) := by
    exact Finset.insert_subset (Finset.mem_Icc.mpr ⟨le_refl _, by positivity⟩) (hBA.trans hA)
  have hN : 2 ^ L ≤ (2 ^ t₀) ^ b₀ := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) hamb₀
  have hsmall := hdouble (insert 0 B) (2 ^ L) t₀ hBbox (Finset.mem_insert_self _ _)
    ((show 2 ≤ B.card by omega).trans
      (Finset.card_le_card (Finset.subset_insert 0 B))) ht₀ hN hscale (2 ^ k) hH
  obtain ⟨P, hrank, hpos, hproper, hzero, hBP, hbox⟩ :=
    exists_noncollapsed_highFold_model_of_small_doubling (insert 0 B)
      (Finset.mem_insert_self _ _) (2 ^ k) K (by positivity) hK hsmall
  have hF : 0 < freimanTSizeFactor K 2 := by
    have hboxpos : 0 < (P.dilate (2 ^ k)).boxCard :=
      Finset.prod_pos (fun _ _ => Nat.succ_pos _)
    by_contra hnot
    have hz : freimanTSizeFactor K 2 = 0 := by omega
    rw [hz, zero_mul] at hbox
    omega
  change (P.dilate (2 ^ k)).boxCard ≤
    freimanTSizeFactor K 2 * (dyadicSumsetWithZero B k).card at hbox
  refine ⟨B, hBA, hcost, hBcard, P, hrank, hpos, hproper, hzero, hBP, hbox, ?_⟩
  intro D hDB hremove
  have hs := hstable D hDB hremove
  have hmul := Nat.mul_lt_mul_of_pos_left hs hF
  have hfirst : (P.dilate (2 ^ k)).boxCard <
      (freimanTSizeFactor K 2 * 2 ^ t₁) * (dyadicSumsetWithZero D k).card := by
    exact hbox.trans_lt (by simpa only [mul_assoc] using hmul)
  have hdense : 2 * (P.dilate (2 ^ k)).boxCard <
      (4 * freimanTSizeFactor K 2 * 2 ^ t₁) * (dyadicSumsetWithZero D k).card := by
    nlinarith
  have hside (i : Fin P.rank) : 4 * freimanTSizeFactor K 2 * 2 ^ t₁ ≤
      2 ^ k * P.length i + 1 := by
    have hh := Nat.mul_le_mul_left (2 ^ k) (hpos i)
    omega
  obtain ⟨hfinite, hindex⟩ := P.finiteIndex_of_highFold_density D hzero
    ((hDB.trans (Finset.subset_insert 0 B)).trans hBP) (2 ^ k)
    (4 * freimanTSizeFactor K 2 * 2 ^ t₁) hdense hside
  exact ⟨hdense, hfinite, hindex,
    delta_real_span_of_finiteIndex_generated P.centeredCoordinates D hfinite⟩

end Erdos587.CFP
