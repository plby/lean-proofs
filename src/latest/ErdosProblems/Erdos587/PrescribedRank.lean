import ErdosProblems.Erdos587.HighFoldDoubling

/-!
Rank reduction by counting at a prescribed high-fold scale. Retaining the
original set cardinality in the dilation lower bound rules out dimension
three without changing coordinates or losing individual side lengths.
-/

open scoped Pointwise
open Erdos587.GeneralizedAP

namespace Erdos587.GeneralizedAP

theorem rank_le_two_of_dense_highFold
    (P : GeneralizedAP) (A : Finset ℤ) (N h F d : ℕ)
    (hh : 0 < h) (hpos : ∀ i, 0 < P.length i) (hrank : P.rank ≤ d)
    (hAP : A ⊆ P.carrier) (hA : A ⊆ Finset.Icc 0 (N : ℤ))
    (hdense : (P.dilate h).boxCard ≤ F * (h • A).card)
    (hlarge : 2 ^ d * F * (N + 1) < h ^ 2 * A.card) :
    P.rank ≤ 2 := by
  by_contra hnot
  have hdim : 3 ≤ P.rank := by omega
  have hcard : A.card ≤ P.boxCard :=
    (Finset.card_le_card hAP).trans P.card_carrier_le_box
  have hpow : h ^ 3 ≤ h ^ P.rank := Nat.pow_le_pow_right hh hdim
  have htwo : 2 ^ P.rank ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hrank
  have hambient : (h • A).card ≤ h * (N + 1) := by
    have hc := CFP.card_nsmul_le_nat_interval A N hA h
    nlinarith
  have hbound : h * (h ^ 2 * A.card) ≤ h * (2 ^ d * F * (N + 1)) := by
    calc
      h * (h ^ 2 * A.card) = h ^ 3 * A.card := by ring
      _ ≤ h ^ P.rank * P.boxCard := Nat.mul_le_mul hpow hcard
      _ ≤ 2 ^ P.rank * (P.dilate h).boxCard :=
        P.pow_mul_boxCard_le_two_pow_mul_dilate_boxCard hpos h
      _ ≤ 2 ^ d * (F * (h • A).card) := Nat.mul_le_mul htwo hdense
      _ ≤ 2 ^ d * (F * (h * (N + 1))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left F hambient)
      _ = h * (2 ^ d * F * (N + 1)) := by ring
  have hc := Nat.le_of_mul_le_mul_left hbound hh
  omega

end Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem exists_prescribed_scale_rank_two_model
    (A : Finset ℤ) (P : GeneralizedAP) (hzero : (0 : ℤ) ∈ A)
    (hAP : A ⊆ P.carrier) (hpos : ∀ i, 0 < P.length i) (hrank : 0 < P.rank)
    (N h D : ℕ) (hA : A ⊆ Finset.Icc 0 (N : ℤ))
    (hh : 0 < h) (hD : 0 < D) (hproper : P.TProper h)
    (hdense : (P.dilate h).boxCard ≤ D * (h • A).card)
    (hscale : nvDenseProperFactor D P.rank * (nvDenseCount D P.rank + 1) ^ P.rank ≤ h)
    (H : ℕ) (hH : nvDenseCount D P.rank * h ≤ H)
    (hlarge : 2 ^ freimanRank (highFoldDoublingConstant D P.rank) *
      freimanTSizeFactor (highFoldDoublingConstant D P.rank) 2 * (N + 1) < H ^ 2 * A.card) :
    ∃ Q : GeneralizedAP, Q.rank ≤ 2 ∧ (∀ i, 0 < Q.length i) ∧ Q.TProper H ∧
      (0 : ℤ) ∈ Q.carrier ∧ A ⊆ Q.carrier ∧ (Q.dilate H).boxCard ≤
        freimanTSizeFactor (highFoldDoublingConstant D P.rank) 2 * (H • A).card := by
  obtain ⟨Q, hQrank, hQpos, hQproper, hQzero, hAQ, hQdense⟩ :=
    exists_prescribed_scale_highFold_model A P hzero hAP hpos hrank h D hh hD
      hproper hdense hscale H hH
  have hq : 0 < nvDenseCount D P.rank := by rw [nvDenseCount_eq_mul]; positivity
  have hHpos := (Nat.mul_pos hq hh).trans_le hH
  exact ⟨Q, Q.rank_le_two_of_dense_highFold A N H _ _ hHpos hQpos hQrank hAQ hA
    hQdense hlarge, hQpos, hQproper, hQzero, hAQ, hQdense⟩

end Erdos587.CFP
