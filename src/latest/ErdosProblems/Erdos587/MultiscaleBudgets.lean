import ErdosProblems.Erdos587.StablePrescribedModel
import ErdosProblems.Erdos587.MultiscaleSubsetProgression

/-! Elementary numerical budgets for the interval-to-progression assembly. -/

open scoped BigOperators Pointwise
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

theorem freimanTSizeFactor_pos {K t : ℕ} (hK : 0 < K) (ht : 0 < t) :
    0 < freimanTSizeFactor K t := by
  have hrank := freimanRank_pos K
  unfold freimanTSizeFactor freimanSizeFactor
  positivity

theorem multiscale_initial_budget_of_interval
    (A : Finset ℤ) (L k n : ℕ) (hA : A ⊆ Finset.Icc 0 ((2 ^ L : ℕ) : ℤ))
    (hk : k ≤ L) (hgap : 4 * (L + 1) ≤ 2 ^ n) :
    (2 * 2 ^ k) * (Nat.log 2 (dyadicSumsetWithZero A k).card + 1) ≤ 2 ^ n * 2 ^ k := by
  have hlog := Nat.log_mono_right (dyadicSumsetWithZero_card_le A L k hA hk) (b := 2)
  rw [Nat.log_pow Nat.one_lt_two] at hlog
  calc
    (2 * 2 ^ k) * (Nat.log 2 (dyadicSumsetWithZero A k).card + 1) ≤
        (2 * 2 ^ k) * (2 * (L + 1)) := Nat.mul_le_mul_left _ (by omega)
    _ = (4 * (L + 1)) * 2 ^ k := by ring
    _ ≤ 2 ^ n * 2 ^ k := Nat.mul_le_mul_right _ hgap

theorem standardized_card_controls_dilate_box
    (P Q : GeneralizedAP) (H F : ℕ) (hF : 0 < F)
    (hcard : Q.carrier.card = ∏ i : Fin P.rank, (H * P.length i / F + 1)) :
    (P.dilate H).boxCard ≤ F ^ P.rank * Q.carrier.card := by
  rw [hcard]
  calc
    (P.dilate H).boxCard ≤ ∏ i : Fin P.rank, F * (H * P.length i / F + 1) := by
      apply Finset.prod_le_prod'
      intro i _
      change H * P.length i + 1 ≤ F * (H * P.length i / F + 1)
      have hh := Nat.lt_mul_div_succ (H * P.length i) hF
      omega
    _ = F ^ P.rank * ∏ i : Fin P.rank, (H * P.length i / F + 1) := by
      rw [Finset.prod_mul_distrib]
      simp

theorem standardized_card_lower_from_parent
    (P Q : GeneralizedAP) (A B : Finset ℤ) (H F : ℕ)
    (hrank : Q.rank = P.rank) (hF : 0 < F) (hpos : ∀ i, 0 < P.length i)
    (hBP : B ⊆ P.carrier) (hhalf : A.card ≤ 2 * B.card)
    (hcard : Q.carrier.card = ∏ i : Fin P.rank, (H * P.length i / F + 1)) :
    H ^ Q.rank * A.card ≤ 2 * (2 * F) ^ Q.rank * Q.carrier.card := by
  rw [hrank]
  have hBcard : B.card ≤ P.boxCard :=
    (Finset.card_le_card hBP).trans P.card_carrier_le_box
  have hbox := standardized_card_controls_dilate_box P Q H F hF hcard
  calc
    H ^ P.rank * A.card ≤ H ^ P.rank * (2 * P.boxCard) :=
      Nat.mul_le_mul_left _ (hhalf.trans (Nat.mul_le_mul_left 2 hBcard))
    _ = 2 * (H ^ P.rank * P.boxCard) := by ring
    _ ≤ 2 * (2 ^ P.rank * (P.dilate H).boxCard) :=
      Nat.mul_le_mul_left 2 (P.pow_mul_boxCard_le_two_pow_mul_dilate_boxCard hpos H)
    _ ≤ 2 * (2 ^ P.rank * (F ^ P.rank * Q.carrier.card)) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hbox)
    _ = 2 * (2 * F) ^ P.rank * Q.carrier.card := by rw [mul_pow]; ring

end Erdos587.CFP
