/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Two uniform probability bounds for a box after restricting coordinate values.
Informal source: the small-measure and geometric estimates in BBMST Lemma 3.6.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.GridRestriction
import ErdosProblems.Erdos1189.GeometricCutoff
import ErdosProblems.Erdos1189.IncidentLocalLemma

namespace Erdos1189

open Finset

lemma reciprocal_product_scale {ι : Type*} (J : Finset ι) (q r : ι → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hq : ∀ j ∈ J, 0 < q j) (hr : ∀ j ∈ J, ε * q j ≤ r j) :
    (∏ j ∈ J, 1 / r j) ≤ (1 / ε) ^ J.card * ∏ j ∈ J, 1 / q j := by
  calc
    _ ≤ ∏ j ∈ J, (1 / ε) * (1 / q j) := by
      apply prod_le_prod
      · intro j hj
        exact (one_div_pos.mpr ((mul_pos hε (hq j hj)).trans_le (hr j hj))).le
      · intro j hj
        have h := one_div_le_one_div_of_le (mul_pos hε (hq j hj)) (hr j hj)
        simpa only [one_div_mul_one_div] using h
    _ = _ := by rw [prod_mul_distrib, prod_const]

lemma ratio_le_inv_of_scaled_le {q r ε : ℝ} (hq : 0 < q) (hε : 0 < ε)
    (hr : ε * q ≤ r) : q / r ≤ 1 / ε := by
  have h := div_le_div_of_nonneg_left hq.le (mul_pos hε hq) hr
  apply h.trans_eq
  field_simp

namespace Grid

variable {ι : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]

lemma restricted_box_scaled_measure (R : (i : ι) → Finset (Fin (q i))) {H : Box q}
    (hH : RestrictionCompatible R H) (hR : ∀ i, 0 < (R i).card) {i : ι}
    (hi : i ∈ fixed H) :
    finiteProbability (boxEvent (restrictedBox R H)) * q i =
      ((q i : ℝ) / (R i).card) * ∏ j ∈ (fixed H).erase i, 1 / ((R j).card : ℝ) := by
  rw [finiteProbability_boxEvent_eq_fixed _ hR, fixed_restrictedBox R hH]
  have h := mul_prod_erase (fixed H) (fun j => 1 / ((R j).card : ℝ)) hi
  rw [← h]
  ring

lemma restricted_box_small_bound (R : (i : ι) → Finset (Fin (q i))) {H : Box q}
    (hH : RestrictionCompatible R H) (hq : ∀ j, 0 < q j) (hR : ∀ j, 0 < (R j).card)
    {ε : ℝ} (hε : 0 < ε) (hrel : ∀ j, ε * q j ≤ (R j).card) {i : ι}
    (hi : i ∈ fixed H) :
    finiteProbability (boxEvent (restrictedBox R H)) * q i ≤
      boxMeasureOn (univ.erase i) H / ε ^ (fixed H).card := by
  let J := (fixed H).erase i
  have hcard : J.card + 1 = (fixed H).card := card_erase_add_one hi
  have hprod := reciprocal_product_scale J (fun j => (q j : ℝ))
    (fun j => ((R j).card : ℝ)) hε (fun j _ => by exact_mod_cast hq j) (fun j _ => hrel j)
  have hratio := ratio_le_inv_of_scaled_le (by exact_mod_cast hq i) hε (hrel i)
  have hinter : univ.erase i ∩ fixed H = J := by
    ext j
    simp only [J, mem_inter, mem_erase, mem_univ, and_true]
  rw [restricted_box_scaled_measure R hH hR hi, boxMeasureOn_eq_fixed, hinter]
  calc
    _ ≤ (1 / ε) * ((1 / ε) ^ J.card * ∏ j ∈ J, 1 / (q j : ℝ)) :=
      mul_le_mul hratio hprod (prod_nonneg fun j _ => by positivity) (by positivity)
    _ = (∏ j ∈ J, 1 / (q j : ℝ)) / ε ^ (J.card + 1) := by
      rw [pow_succ, div_mul_eq_div_mul_one_div]
      simp only [one_div_pow]
      ring
    _ = _ := by rw [hcard]

lemma restricted_box_geometric_bound (R : (i : ι) → Finset (Fin (q i))) {H : Box q}
    (hH : RestrictionCompatible R H) (hq : ∀ j, 0 < q j) (hR : ∀ j, 2 ≤ (R j).card)
    {ε : ℝ} (hε : 0 < ε) (hrel : ∀ j, ε * q j ≤ (R j).card) {i : ι}
    (hi : i ∈ fixed H) :
    finiteProbability (boxEvent (restrictedBox R H)) * q i ≤
      (2 / ε) * (1 / 2 : ℝ) ^ (fixed H).card := by
  let J := (fixed H).erase i
  have hcard : J.card + 1 = (fixed H).card := card_erase_add_one hi
  have hprod : (∏ j ∈ J, 1 / ((R j).card : ℝ)) ≤ (1 / 2 : ℝ) ^ J.card := by
    calc
      _ ≤ ∏ j ∈ J, (1 / 2 : ℝ) := by
        apply prod_le_prod
        · intro j _
          positivity
        · intro j _
          exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hR j)
      _ = _ := prod_const _
  have hratio := ratio_le_inv_of_scaled_le (by exact_mod_cast hq i) hε (hrel i)
  rw [restricted_box_scaled_measure R hH (fun j => by have := hR j; omega) hi]
  calc
    _ ≤ (1 / ε) * (1 / 2 : ℝ) ^ J.card :=
      mul_le_mul hratio hprod (prod_nonneg fun j _ => by positivity) (by positivity)
    _ = (2 / ε) * (1 / 2 : ℝ) ^ (J.card + 1) := by rw [pow_succ]; ring
    _ = _ := by rw [hcard]

lemma restricted_weight_bound_of_cutoff {lam ε δ : ℝ} (hε : 0 < ε)
    (hcut : ∀ m : ℕ, ∀ z : ℝ, z ≤ δ / ε ^ m → z ≤ (2 / ε) * (1 / 2 : ℝ) ^ m →
      z ≤ (lam / 16) * (35 / 48 : ℝ) ^ m) :
    ∀ R : (i : ι) → Finset (Fin (q i)), ∀ H : Box q,
      RestrictionCompatible R H → (∀ j, 0 < q j) → (∀ j, 2 ≤ (R j).card) →
      (∀ j, ε * q j ≤ (R j).card) → ∀ i ∈ fixed H,
        boxMeasureOn (univ.erase i) H ≤ δ →
          localBoxWeight (restrictedBox R H) * q i ≤
            (lam / 16) * (5 / 6 : ℝ) ^ (fixed H).card := by
  intro R H hH hq hR hrel i hi hsmall
  have hfirst := restricted_box_small_bound R hH hq (fun j => by have := hR j; omega)
    hε hrel hi
  have hfirst' : finiteProbability (boxEvent (restrictedBox R H)) * q i ≤
      δ / ε ^ (fixed H).card :=
    hfirst.trans (div_le_div_of_nonneg_right hsmall (pow_pos hε _).le)
  have hsecond := restricted_box_geometric_bound R hH hq hR hε hrel hi
  have hbound := hcut (fixed H).card _ hfirst' hsecond
  have hmul := mul_le_mul_of_nonneg_left hbound
    (show (0 : ℝ) ≤ (8 / 7 : ℝ) ^ (fixed H).card by positivity)
  unfold localBoxWeight
  rw [fixed_restrictedBox R hH]
  calc
    _ = (8 / 7 : ℝ) ^ (fixed H).card *
        (finiteProbability (boxEvent (restrictedBox R H)) * q i) := mul_assoc _ _ _
    _ ≤ (8 / 7 : ℝ) ^ (fixed H).card * ((lam / 16) * (35 / 48 : ℝ) ^ (fixed H).card) := hmul
    _ = (lam / 16) * ((8 / 7 : ℝ) ^ (fixed H).card * (35 / 48 : ℝ) ^ (fixed H).card) := by ring
    _ = _ := by rw [← mul_pow]; norm_num

end Grid
end Erdos1189
