/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 884.
Informal proof: Daniel Larsen, building on Terence Tao's construction.
Formal proof: Claude Fable 5, with minor guidance from R. J. Honicky.
Source: https://www.erdosproblems.com/884#post-7362
https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258
Original Lean/Mathlib version: 4.31.0.
Original Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The port reuses the repository's existing PNT+ Selberg sieve by Arend Mellendijk.
-/
import ErdosProblems.Erdos884.DivisorsProd

set_option linter.mathlibStandardSet false

/-!
# Erdős 884 — Lemma F: polynomial gap bounds (Tao Lemma 2.2)

Real product functions `x ↦ ∏ (x - a)` over finsets, shifted elementary symmetric
sums, and the constant/non-constant difference dichotomy.
-/

namespace Erdos884

theorem F_prod_nonneg (s : Finset ℝ) (y : ℝ) (h : ∀ a ∈ s, a ≤ y) : 0 ≤ ∏ a ∈ s, (y - a) :=
  Finset.prod_nonneg fun a ha => sub_nonneg.2 (h a ha)

theorem F_prod_mono (s : Finset ℝ) {x y : ℝ} (h : ∀ a ∈ s, a ≤ y) (hxy : y ≤ x) :
    ∏ a ∈ s, (y - a) ≤ ∏ a ∈ s, (x - a) :=
  Finset.prod_le_prod (fun a ha => sub_nonneg.2 (h a ha)) (fun a ha => by
    have := h a ha; linarith)

theorem F_prod_sub_ge (s : Finset ℝ) {a₀ x y : ℝ} (ha₀ : a₀ ∈ s) (h : ∀ a ∈ s, a ≤ y)
    (hxy : y ≤ x) :
    (x - y) * ∏ a ∈ s.erase a₀, (y - a) ≤ (∏ a ∈ s, (x - a)) - ∏ a ∈ s, (y - a) := by
  have ht' : ∀ a ∈ s.erase a₀, a ≤ y := fun a ha => h a (Finset.mem_of_mem_erase ha)
  have hx : ∏ a ∈ s, (x - a) = (x - a₀) * ∏ a ∈ s.erase a₀, (x - a) := by
    rw [← Finset.prod_insert (Finset.notMem_erase a₀ s), Finset.insert_erase ha₀]
  have hy : ∏ a ∈ s, (y - a) = (y - a₀) * ∏ a ∈ s.erase a₀, (y - a) := by
    rw [← Finset.prod_insert (Finset.notMem_erase a₀ s), Finset.insert_erase ha₀]
  have h1 : ∏ a ∈ s.erase a₀, (y - a) ≤ ∏ a ∈ s.erase a₀, (x - a) := F_prod_mono _ ht' hxy
  have h2 : 0 ≤ ∏ a ∈ s.erase a₀, (y - a) := F_prod_nonneg _ y ht'
  have h3 : 0 ≤ y - a₀ := sub_nonneg.2 (h a₀ ha₀)
  have h4 : (x - y) * ∏ a ∈ s.erase a₀, (y - a) ≤ (x - y) * ∏ a ∈ s.erase a₀, (x - a) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have h5 : 0 ≤ (y - a₀) * (∏ a ∈ s.erase a₀, (x - a) - ∏ a ∈ s.erase a₀, (y - a)) :=
    mul_nonneg h3 (by linarith)
  rw [hx, hy]
  nlinarith [h4, h5]

theorem F_const_gap {s s' : Finset ℝ} (hne : s.Nonempty) (hne' : s'.Nonempty) {ℓ : ℝ}
    (hℓ : 0 < ℓ)
    (heq : ∀ x : ℝ, ∏ a ∈ s, (x - a) = (∏ a ∈ s', (x - a)) + ℓ) :
    s.max' hne < s'.max' hne' ∧
    (s'.max' hne' - s.max' hne) * ∏ a ∈ s.erase (s.max' hne), (s.max' hne - a) ≤ ℓ := by
  have hM : s.max' hne ∈ s := s.max'_mem hne
  have hM' : s'.max' hne' ∈ s' := s'.max'_mem hne'
  have hPs0 : ∏ a ∈ s, (s.max' hne - a) = 0 := Finset.prod_eq_zero hM (sub_self _)
  have hPs'0 : ∏ a ∈ s', (s'.max' hne' - a) = 0 := Finset.prod_eq_zero hM' (sub_self _)
  have hlt : s.max' hne < s'.max' hne' := by
    by_contra hcon
    push Not at hcon
    have h0 := heq (s.max' hne)
    rw [hPs0] at h0
    have hge : 0 ≤ ∏ a ∈ s', (s.max' hne - a) :=
      F_prod_nonneg s' _ fun a ha => le_trans (s'.le_max' a ha) hcon
    linarith
  refine ⟨hlt, ?_⟩
  have hPsM' : ∏ a ∈ s, (s'.max' hne' - a) = ℓ := by
    rw [heq (s'.max' hne'), hPs'0, zero_add]
  have hkey := F_prod_sub_ge s hM (fun a ha => s.le_max' a ha) hlt.le
  rw [hPsM', hPs0, sub_zero] at hkey
  exact hkey

/-- Shifted elementary symmetric sum: the `j`-th elementary symmetric polynomial of the
(truncated) shifts `p - x₀`, `p ∈ s`. -/
noncomputable def esymmShift (x₀ : ℕ) (s : Finset ℕ) (j : ℕ) : ℕ :=
  ∑ u ∈ s.powerset.filter (fun u => u.card = j), ∏ p ∈ u, (p - x₀)

theorem esymmShift_zero (x₀ : ℕ) (s : Finset ℕ) : esymmShift x₀ s 0 = 1 := by
  unfold esymmShift
  have h : s.powerset.filter (fun u => u.card = 0) = {∅} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ Finset.empty_subset s, h⟩⟩
  rw [h, Finset.sum_singleton, Finset.prod_empty]

theorem F_prod_expand {x₀ : ℕ} {s : Finset ℕ} (h : ∀ p ∈ s, x₀ ≤ p) (x : ℝ) :
    ∏ p ∈ s, (x + (p:ℝ)) =
      ∑ j ∈ Finset.range (s.card + 1), (esymmShift x₀ s j : ℝ) * (x + (x₀:ℝ)) ^ (s.card - j) := by
  classical
  have hsplit : ∀ p ∈ s, x + (p:ℝ) = ((p - x₀ : ℕ) : ℝ) + (x + (x₀:ℝ)) := by
    intro p hp
    rw [Nat.cast_sub (h p hp)]
    ring
  calc ∏ p ∈ s, (x + (p:ℝ))
      = ∏ p ∈ s, (((p - x₀ : ℕ):ℝ) + (x + (x₀:ℝ))) := Finset.prod_congr rfl hsplit
    _ = ∑ u ∈ s.powerset, (∏ p ∈ u, ((p - x₀:ℕ):ℝ)) * ∏ _p ∈ s \ u, (x + (x₀:ℝ)) :=
        Finset.prod_add _ _ s
    _ = ∑ u ∈ s.powerset, (∏ p ∈ u, ((p - x₀:ℕ):ℝ)) * (x + (x₀:ℝ)) ^ (s.card - u.card) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Finset.prod_const, Finset.card_sdiff,
          Finset.inter_eq_left.2 (Finset.mem_powerset.1 hu)]
    _ = ∑ j ∈ Finset.range (s.card + 1), ∑ u ∈ s.powerset.filter (fun u => u.card = j),
          (∏ p ∈ u, ((p - x₀:ℕ):ℝ)) * (x + (x₀:ℝ)) ^ (s.card - u.card) := by
        refine (Finset.sum_fiberwise_of_maps_to (fun u hu => ?_) _).symm
        rw [Finset.mem_range, Nat.lt_succ_iff]
        exact Finset.card_le_card (Finset.mem_powerset.1 hu)
    _ = ∑ j ∈ Finset.range (s.card + 1), (esymmShift x₀ s j : ℝ) * (x + (x₀:ℝ)) ^ (s.card - j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        simp only [esymmShift]
        rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [Nat.cast_prod, (Finset.mem_filter.1 hu).2]

theorem esymmShift_le {x₀ H : ℕ} {s : Finset ℕ} (h : ∀ p ∈ s, p ≤ x₀ + H) (j : ℕ) :
    esymmShift x₀ s j ≤ 2 ^ s.card * H ^ j := by
  classical
  unfold esymmShift
  calc ∑ u ∈ s.powerset.filter (fun u => u.card = j), ∏ p ∈ u, (p - x₀)
      ≤ ∑ _u ∈ s.powerset.filter (fun u => u.card = j), H ^ j := by
        refine Finset.sum_le_sum fun u hu => ?_
        obtain ⟨hus, huj⟩ := Finset.mem_filter.1 hu
        rw [Finset.mem_powerset] at hus
        calc ∏ p ∈ u, (p - x₀) ≤ ∏ _p ∈ u, H :=
              Finset.prod_le_prod' fun p hp => by have := h p (hus hp); omega
          _ = H ^ u.card := Finset.prod_const H
          _ = H ^ j := by rw [huj]
    _ = (s.powerset.filter (fun u => u.card = j)).card * H ^ j := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 ^ s.card * H ^ j :=
        Nat.mul_le_mul (le_trans (Finset.card_filter_le _ _)
          (le_of_eq (Finset.card_powerset s))) le_rfl

theorem F_const_of_esymm_eq {x₀ : ℕ} {s s' : Finset ℕ}
    (hs : ∀ p ∈ s, x₀ ≤ p) (hs' : ∀ p ∈ s', x₀ ≤ p) (hcard : s.card = s'.card)
    (heq : ∀ j, j < s.card → esymmShift x₀ s j = esymmShift x₀ s' j) (x : ℝ) :
    ∏ p ∈ s, (x + (p:ℝ)) = (∏ p ∈ s', (x + (p:ℝ))) + ((∏ p ∈ s, (p:ℝ)) - ∏ p ∈ s', (p:ℝ)) := by
  have key : ∀ y : ℝ, (∏ p ∈ s, (y + (p:ℝ))) - ∏ p ∈ s', (y + (p:ℝ)) =
      (esymmShift x₀ s s.card : ℝ) - (esymmShift x₀ s' s.card : ℝ) := by
    intro y
    rw [F_prod_expand hs y, F_prod_expand hs' y, ← hcard, ← Finset.sum_sub_distrib,
      Finset.sum_range_succ]
    have h0 : ∑ j ∈ Finset.range s.card,
        ((esymmShift x₀ s j : ℝ) * (y + (x₀:ℝ)) ^ (s.card - j)
          - (esymmShift x₀ s' j : ℝ) * (y + (x₀:ℝ)) ^ (s.card - j)) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [heq j (Finset.mem_range.1 hj)]; ring
    rw [h0, Nat.sub_self, pow_zero, zero_add]
    ring
  have h1 := key x
  have h2 := key 0
  simp only [zero_add] at h2
  linarith

/-- Internal helper: partial geometric-type sums with ratio ≤ 1/2 are at most twice the
leading term. -/
lemma geom_sum_aux {a b : ℝ} (ha : 0 ≤ a) (hab : 2 * a ≤ b) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), a ^ i * b ^ (m - i) ≤ 2 * b ^ m := by
  have hb : 0 ≤ b := by linarith
  induction m with
  | zero => norm_num [Finset.sum_range_one]
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have h1 : ∀ i ∈ Finset.range (n + 1),
        a ^ (i + 1) * b ^ (n + 1 - (i + 1)) = a * (a ^ i * b ^ (n - i)) := by
      intro i _
      have he : n + 1 - (i + 1) = n - i := by omega
      rw [he, pow_succ]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have h2 : a * ∑ i ∈ Finset.range (n + 1), a ^ i * b ^ (n - i) ≤ a * (2 * b ^ n) :=
      mul_le_mul_of_nonneg_left ih ha
    have hbn : 0 ≤ b ^ n := pow_nonneg hb n
    have h3 : a * (2 * b ^ n) ≤ b * b ^ n := by nlinarith
    have h4 : b * b ^ n = b ^ (n + 1) := by rw [pow_succ]; ring
    simp only [pow_zero, one_mul, Nat.sub_zero]
    linarith

/-- Internal helper: distinct naturals differ by at least 1 as reals. -/
lemma one_le_abs_natCast_sub {a b : ℕ} (h : a ≠ b) : (1:ℝ) ≤ |(a:ℝ) - (b:ℝ)| := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h1 : a + 1 ≤ b := hlt
    have h2 : (a:ℝ) + 1 ≤ (b:ℝ) := by exact_mod_cast h1
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 : b + 1 ≤ a := hlt
    have h2 : (b:ℝ) + 1 ≤ (a:ℝ) := by exact_mod_cast h1
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- Internal helper: if the coefficients of `∑ f j · x^(k-j)` vanish below `j₀`, the `j₀`-th has
absolute value ≥ 1, and the later ones are geometrically small compared to `x`, then the whole
sum has absolute value at least `x/2`. -/
lemma abs_expansion_ge {x C Hb : ℝ} {k j₀ : ℕ} (f : ℕ → ℝ)
    (hx1 : 1 ≤ x) (hHb : 0 ≤ Hb) (h2H : 2 * Hb ≤ x) (hC : 0 ≤ C)
    (hj₀k : j₀ < k)
    (hzero : ∀ i, i < j₀ → f i = 0)
    (hhead : 1 ≤ |f j₀|)
    (htail : ∀ j, j₀ < j → |f j| ≤ C * Hb ^ j)
    (hfinal : 4 * (C * Hb ^ (j₀ + 1)) ≤ x) :
    x / 2 ≤ |∑ j ∈ Finset.range (k + 1), f j * x ^ (k - j)| := by
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨m, rfl⟩ : ∃ m, k = j₀ + 1 + m := ⟨k - j₀ - 1, by omega⟩
  have he1 : j₀ + 1 + m - j₀ = m + 1 := by omega
  -- split off the head term; earlier terms vanish
  have hsplit : ∑ j ∈ Finset.range (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)
      = f j₀ * x ^ (m + 1)
        + ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun j => f j * x ^ (j₀ + 1 + m - j)) (Nat.zero_le j₀)
        (by omega : j₀ ≤ j₀ + 1 + m + 1)]
    have hzs : ∑ j ∈ Finset.Ico 0 j₀, f j * x ^ (j₀ + 1 + m - j) = 0 :=
      Finset.sum_eq_zero fun j hj => by rw [hzero j (Finset.mem_Ico.1 hj).2]; ring
    rw [hzs, zero_add,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : j₀ < j₀ + 1 + m + 1)
        (fun j => f j * x ^ (j₀ + 1 + m - j)), he1]
  -- the tail is small
  have htail_bound : |∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)|
      ≤ 2 * (C * Hb ^ (j₀ + 1)) * x ^ m := by
    have hstep1 : |∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)|
        ≤ ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), C * Hb ^ j * x ^ (j₀ + 1 + m - j) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j hj => ?_)
      obtain ⟨hj1, _hj2⟩ := Finset.mem_Ico.1 hj
      rw [abs_mul, abs_pow, abs_of_nonneg hx0]
      exact mul_le_mul_of_nonneg_right (htail j hj1) (pow_nonneg hx0 _)
    have hstep2 : ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), C * Hb ^ j * x ^ (j₀ + 1 + m - j)
        = (C * Hb ^ (j₀ + 1)) * ∑ i ∈ Finset.range (m + 1), Hb ^ i * x ^ (m - i) := by
      rw [Finset.sum_Ico_eq_sum_range]
      have he2 : j₀ + 1 + m + 1 - (j₀ + 1) = m + 1 := by omega
      rw [he2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have he3 : j₀ + 1 + m - (j₀ + 1 + i) = m - i := by omega
      rw [he3, pow_add]
      ring
    have hstep3 : (C * Hb ^ (j₀ + 1)) * ∑ i ∈ Finset.range (m + 1), Hb ^ i * x ^ (m - i)
        ≤ (C * Hb ^ (j₀ + 1)) * (2 * x ^ m) :=
      mul_le_mul_of_nonneg_left (geom_sum_aux hHb h2H m) (mul_nonneg hC (pow_nonneg hHb _))
    calc |∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)|
        ≤ ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), C * Hb ^ j * x ^ (j₀ + 1 + m - j) := hstep1
      _ = (C * Hb ^ (j₀ + 1)) * ∑ i ∈ Finset.range (m + 1), Hb ^ i * x ^ (m - i) := hstep2
      _ ≤ (C * Hb ^ (j₀ + 1)) * (2 * x ^ m) := hstep3
      _ = 2 * (C * Hb ^ (j₀ + 1)) * x ^ m := by ring
  -- the head is big
  have hhead_bound : x ^ (m + 1) ≤ |f j₀ * x ^ (m + 1)| := by
    rw [abs_mul, abs_pow, abs_of_nonneg hx0]
    exact le_mul_of_one_le_left (pow_nonneg hx0 _) hhead
  -- triangle inequality: |head + tail| ≥ |head| - |tail|
  have htri : |f j₀ * x ^ (m + 1)|
      - |∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)|
      ≤ |f j₀ * x ^ (m + 1)
          + ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)| := by
    have h := abs_sub_abs_le_abs_sub (f j₀ * x ^ (m + 1))
      (-(∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)))
    rw [abs_neg, sub_neg_eq_add] at h
    linarith
  -- assemble
  have hxm : 1 ≤ x ^ m := one_le_pow₀ hx1
  have hfin1 : 4 * (C * Hb ^ (j₀ + 1)) * x ^ m ≤ x * x ^ m :=
    mul_le_mul_of_nonneg_right hfinal (pow_nonneg hx0 m)
  have hpow : x ^ (m + 1) = x * x ^ m := by rw [pow_succ]; ring
  rw [hsplit]
  calc x / 2 ≤ x / 2 * x ^ m := le_mul_of_one_le_right (by linarith) hxm
    _ ≤ x ^ (m + 1) - 2 * (C * Hb ^ (j₀ + 1)) * x ^ m := by rw [hpow]; linarith
    _ ≤ |f j₀ * x ^ (m + 1)|
        - |∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)| := by
          linarith [hhead_bound, htail_bound]
    _ ≤ |f j₀ * x ^ (m + 1)
        + ∑ j ∈ Finset.Ico (j₀ + 1) (j₀ + 1 + m + 1), f j * x ^ (j₀ + 1 + m - j)| := htri

theorem F_nonconst_gap {x₀ H K : ℕ} {s s' : Finset ℕ}
    (hs : ∀ p ∈ s, x₀ < p ∧ p ≤ x₀ + H) (hs' : ∀ p ∈ s', x₀ < p ∧ p ≤ x₀ + H)
    (hcard : s.card = s'.card) (hK : s.card ≤ K) (hH : 1 ≤ H)
    (hbig : 8 * (2*H)^(K+1) ≤ x₀)
    (hne : ∃ j, j < s.card ∧ esymmShift x₀ s j ≠ esymmShift x₀ s' j) :
    (x₀ : ℝ) / 2 ≤ |(∏ p ∈ s, (p:ℝ)) - ∏ p ∈ s', (p:ℝ)| := by
  classical
  -- basic numeric facts
  have h2Hx : 2 * H ≤ x₀ := by
    have h1 : 2 * H ≤ (2 * H) ^ (K + 1) := Nat.le_self_pow (by omega) _
    have h2 : (2 * H) ^ (K + 1) ≤ 8 * (2 * H) ^ (K + 1) :=
      le_mul_of_one_le_left (Nat.zero_le _) (by norm_num)
    exact le_trans h1 (le_trans h2 hbig)
  have hx1 : 1 ≤ x₀ := by omega
  -- expansions at x = 0 give the difference of products as a sum
  have hs1 : ∀ p ∈ s, x₀ ≤ p := fun p hp => (hs p hp).1.le
  have hs1' : ∀ p ∈ s', x₀ ≤ p := fun p hp => (hs' p hp).1.le
  have hexp := F_prod_expand hs1 0
  have hexp' := F_prod_expand hs1' 0
  simp only [zero_add] at hexp hexp'
  have hD : (∏ p ∈ s, (p:ℝ)) - ∏ p ∈ s', (p:ℝ)
      = ∑ j ∈ Finset.range (s.card + 1),
          ((esymmShift x₀ s j : ℝ) - (esymmShift x₀ s' j : ℝ)) * (x₀:ℝ) ^ (s.card - j) := by
    rw [hexp, hexp', ← hcard, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- least index at which the shifted symmetric sums differ
  have hne2 : ∃ j, esymmShift x₀ s j ≠ esymmShift x₀ s' j := hne.imp fun j h => h.2
  have hj₀lt : Nat.find hne2 < s.card := by
    obtain ⟨j, hjlt, hj⟩ := hne
    exact lt_of_le_of_lt (Nat.find_le hj) hjlt
  -- coefficient bounds
  have habs : ∀ j, |(esymmShift x₀ s j : ℝ) - (esymmShift x₀ s' j : ℝ)|
      ≤ (2:ℝ) ^ (K + 1) * (H:ℝ) ^ j := by
    intro j
    have h1 : esymmShift x₀ s j ≤ 2 ^ K * H ^ j :=
      le_trans (esymmShift_le (fun p hp => (hs p hp).2) j)
        (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hK) le_rfl)
    have h2 : esymmShift x₀ s' j ≤ 2 ^ K * H ^ j := by
      have h3 := esymmShift_le (fun p hp => (hs' p hp).2) j
      rw [← hcard] at h3
      exact le_trans h3 (Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hK) le_rfl)
    have h1' : (esymmShift x₀ s j : ℝ) ≤ (2:ℝ) ^ K * (H:ℝ) ^ j := by exact_mod_cast h1
    have h2' : (esymmShift x₀ s' j : ℝ) ≤ (2:ℝ) ^ K * (H:ℝ) ^ j := by exact_mod_cast h2
    have hn1 : (0:ℝ) ≤ (esymmShift x₀ s j : ℝ) := Nat.cast_nonneg _
    have hn2 : (0:ℝ) ≤ (esymmShift x₀ s' j : ℝ) := Nat.cast_nonneg _
    have hpow2 : (2:ℝ) ^ (K + 1) * (H:ℝ) ^ j = 2 * ((2:ℝ) ^ K * (H:ℝ) ^ j) := by ring
    rw [hpow2, abs_le]
    constructor <;> linarith
  -- the size hypothesis, in the form the helper needs
  have hnat : 2 ^ (K + 3) * H ^ (Nat.find hne2 + 1) ≤ x₀ := by
    have h1 : H ^ (Nat.find hne2 + 1) ≤ H ^ (K + 1) :=
      Nat.pow_le_pow_right hH (by omega)
    have h2 : (2:ℕ) ^ (K + 3) ≤ 2 ^ (K + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 2 ^ (K + 3) * H ^ (Nat.find hne2 + 1) ≤ 2 ^ (K + 4) * H ^ (K + 1) :=
          Nat.mul_le_mul h2 h1
      _ = 8 * (2 * H) ^ (K + 1) := by rw [Nat.mul_pow]; ring
      _ ≤ x₀ := hbig
  rw [hD]
  refine abs_expansion_ge (x := (x₀:ℝ)) (C := (2:ℝ)^(K+1)) (Hb := (H:ℝ)) (k := s.card)
      (j₀ := Nat.find hne2)
      (fun j => (esymmShift x₀ s j : ℝ) - (esymmShift x₀ s' j : ℝ))
      ?_ (Nat.cast_nonneg H) ?_ (by positivity) hj₀lt ?_ ?_ ?_ ?_
  · exact_mod_cast hx1
  · exact_mod_cast h2Hx
  · intro i hi
    have heqi : esymmShift x₀ s i = esymmShift x₀ s' i := not_ne_iff.1 (Nat.find_min hne2 hi)
    simp [heqi]
  · exact one_le_abs_natCast_sub (Nat.find_spec hne2)
  · intro j _
    exact habs j
  · have hcast : ((2:ℝ) ^ (K + 3) * (H:ℝ) ^ (Nat.find hne2 + 1)) ≤ (x₀:ℝ) := by
      exact_mod_cast hnat
    calc 4 * ((2:ℝ) ^ (K + 1) * (H:ℝ) ^ (Nat.find hne2 + 1))
        = (2:ℝ) ^ (K + 3) * (H:ℝ) ^ (Nat.find hne2 + 1) := by ring
      _ ≤ (x₀:ℝ) := hcast

end Erdos884
