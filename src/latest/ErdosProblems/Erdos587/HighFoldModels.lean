import ErdosProblems.Erdos587.DyadicSumsets
import ErdosProblems.Erdos587.GAPContraction
import ErdosProblems.Erdos587.GAPTrimVolumes

/-!
Bounded-rank GAP models at a selected high-fold scale, derived from interval
containment. Unlike the small-doubling interface, this scale-selection theorem
has no additive-combinatorial hypothesis on the input set.
-/

open scoped Pointwise

namespace Erdos587.CFP

theorem exists_noncollapsed_highFold_model_of_small_doubling
    (A : Finset ℤ) (hzero : 0 ∈ A) (h K : ℕ) (hh : 0 < h) (hK : 1 ≤ K)
    (hsmall : (h • A + h • A).card ≤ K * (h • A).card) :
    ∃ Q : GeneralizedAP, Q.rank ≤ freimanRank K ∧
      (∀ i, 0 < Q.length i) ∧ Q.TProper h ∧
      (0 : ℤ) ∈ Q.carrier ∧ A ⊆ Q.carrier ∧
      (Q.dilate h).boxCard ≤ freimanTSizeFactor K 2 * (h • A).card := by
  obtain ⟨P, hPrank, hPproper, hPzero, hAP, hPbox⟩ :=
    exists_highFold_GAP_model_of_small_doubling A hzero h K hh hK hsmall
  refine ⟨P.trimZeroSides, P.rank_trimZeroSides_le.trans hPrank,
    P.trimZeroSides_length_pos, P.tProper_trimZeroSides hPproper, ?_, ?_, ?_⟩
  · simpa only [P.carrier_trimZeroSides] using hPzero
  · simpa only [P.carrier_trimZeroSides] using hAP
  · simpa only [P.boxCard_dilate_trimZeroSides] using hPbox

/-- A polynomial-size interval supplies a proper high-fold model at some
scale in a prescribed dyadic window. -/
theorem exists_polynomial_window_highFold_model (A : Finset ℤ) (N b t : ℕ)
    (hA : A ⊆ Finset.Icc 0 (N : ℤ)) (hzero : 0 ∈ A)
    (ht : 0 < t) (hN : N ≤ (2 ^ t) ^ b) :
    ∃ k, t ≤ k ∧ k < t + t ∧
      ∃ Q : GeneralizedAP, Q.rank ≤ freimanRank (2 ^ (b + 3)) ∧
        (∀ i, 0 < Q.length i) ∧ Q.TProper (2 ^ k) ∧
        (0 : ℤ) ∈ Q.carrier ∧ A ⊆ Q.carrier ∧
        (Q.dilate (2 ^ k)).boxCard ≤
          freimanTSizeFactor (2 ^ (b + 3)) 2 * ((2 ^ k) • A).card := by
  obtain ⟨k, htk, hkt, hsmall⟩ :=
    exists_polynomial_window_small_doubling A N b t hA hzero ht hN
  refine ⟨k, htk, hkt, ?_⟩
  exact exists_noncollapsed_highFold_model_of_small_doubling A hzero
    (2 ^ k) (2 ^ (b + 3)) (by positivity) (Nat.one_le_pow (b + 3) 2 (by omega)) hsmall

/-- Once the lower end of the scale window exceeds the fixed Freiman loss,
the model has rank at most `b+1`, not just the coarse Freiman rank. -/
theorem exists_polynomial_window_lowRank_model (A : Finset ℤ) (N b t : ℕ)
    (hA : A ⊆ Finset.Icc 0 (N : ℤ)) (hzero : 0 ∈ A)
    (ht : 0 < t) (hN : N ≤ (2 ^ t) ^ b)
    (hlarge : 2 * freimanTSizeFactor (2 ^ (b + 3)) 2 < 2 ^ t) :
    ∃ k, t ≤ k ∧ k < t + t ∧
      ∃ Q : GeneralizedAP, Q.rank ≤ b + 1 ∧
        (∀ i, 0 < Q.length i) ∧ Q.TProper (2 ^ k) ∧
        (0 : ℤ) ∈ Q.carrier ∧ A ⊆ Q.carrier ∧
        (Q.dilate (2 ^ k)).boxCard ≤
          freimanTSizeFactor (2 ^ (b + 3)) 2 * ((2 ^ k) • A).card := by
  obtain ⟨k, htk, hkt, Q, _hQrank, hpos, hproper, hzeroQ, hAQ, hbox⟩ :=
    exists_polynomial_window_highFold_model A N b t hA hzero ht hN
  have hpow : 2 ^ t ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) htk
  have hrank : Q.rank ≤ b + 1 := by
    apply Q.rank_le_of_polynomial_dilate_bound hpos (2 ^ k) N b
      (freimanTSizeFactor (2 ^ (b + 3)) 2) (hlarge.trans_le hpow)
    · exact hN.trans (Nat.pow_le_pow_left hpow b)
    · exact hbox.trans (Nat.mul_le_mul_left _ (card_nsmul_le_nat_interval A N hA _))
  exact ⟨k, htk, hkt, Q, hrank, hpos, hproper, hzeroQ, hAQ, hbox⟩

end Erdos587.CFP
