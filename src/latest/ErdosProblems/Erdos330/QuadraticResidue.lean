/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import ErdosProblems.Erdos330.PrimeSupply

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Quadratic-residue lemmas for Erdős Problem 330

This file contains the finite-field lemmas used by the selected coordinate of
the CRT gadget.
-/

namespace Erdos330

open Finset
open MulChar
open scoped Pointwise

/-- Nonzero quadratic residues in `ZMod p`. -/
noncomputable def QR (p : ℕ) [NeZero p] : Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun x => x ≠ 0 ∧ IsSquare x

theorem mem_QR {p : ℕ} [NeZero p] {x : ZMod p} :
    x ∈ QR p ↔ x ≠ 0 ∧ IsSquare x := by
  classical
  simp [QR]

theorem qr_neg_disjoint (p : ℕ) [Fact p.Prime] [NeZero p] (hp3 : p % 4 = 3) :
    ∀ x : ZMod p, x ∈ QR p → -x ∉ QR p := by
  classical
  intro x hx hxneg
  rw [mem_QR] at hx hxneg
  have hx0 : x ≠ 0 := hx.1
  have hxsq : IsSquare x := hx.2
  have hnegsq : IsSquare (-x) := hxneg.2
  have hdiv : IsSquare ((-x) / x) := hnegsq.div hxsq
  have hquot : (-x) / x = (-1 : ZMod p) := by
    field_simp [hx0]
  have hsqnegone : IsSquare (-1 : ZMod p) := by
    simpa [hquot] using hdiv
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hsqnegone) hp3

lemma QR_add_ne_zero {p : ℕ} [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) {u v : ZMod p} (hu : u ∈ QR p) (hv : v ∈ QR p) :
    u + v ≠ 0 := by
  intro huv
  have hvneg : v = -u := eq_neg_of_add_eq_zero_right huv
  have hneg : -u ∈ QR p := by simpa [hvneg] using hv
  exact (qr_neg_disjoint p hp3 u hu) hneg

lemma zmod_prime_odd_char_ne_two (p : ℕ) [Fact p.Prime] (hp23 : 23 ≤ p) :
    ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

lemma quadraticChar_neg_one_eq_neg_one_of_mod_four_eq_three (p : ℕ) [Fact p.Prime]
    (hp3 : p % 4 = 3) :
    (quadraticChar (ZMod p)) (-1) = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare]
  intro hsq
  exact (ZMod.exists_sq_eq_neg_one_iff.mp hsq) hp3

lemma jacobiSum_quadraticChar_self_eq_one (p : ℕ) [Fact p.Prime]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) :
    jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) = 1 := by
  let χ : MulChar (ZMod p) ℤ := quadraticChar (ZMod p)
  have hchar : ringChar (ZMod p) ≠ 2 := zmod_prime_odd_char_ne_two p hp23
  have hχne : χ ≠ 1 := quadraticChar_ne_one hchar
  have hχinv : χ⁻¹ = χ := MulChar.IsQuadratic.inv (quadraticChar_isQuadratic (ZMod p))
  have hneg : χ (-1) = -1 := quadraticChar_neg_one_eq_neg_one_of_mod_four_eq_three p hp3
  calc
    jacobiSum (quadraticChar (ZMod p)) (quadraticChar (ZMod p)) = jacobiSum χ χ := rfl
    _ = jacobiSum χ χ⁻¹ := by rw [hχinv]
    _ = -χ (-1) := jacobiSum_nontrivial_inv hχne
    _ = 1 := by rw [hneg]; norm_num

lemma quadraticChar_translate_sum_eq_one (p : ℕ) [Fact p.Prime]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) {t : ZMod p} (ht : t ≠ 0) :
    (∑ x : ZMod p, (quadraticChar (ZMod p)) x *
      (quadraticChar (ZMod p)) (t - x)) = 1 := by
  let χ : MulChar (ZMod p) ℤ := quadraticChar (ZMod p)
  have hχt_sq : χ t ^ 2 = 1 := quadraticChar_sq_one (F := ZMod p) ht
  calc
    (∑ x : ZMod p, (quadraticChar (ZMod p)) x *
      (quadraticChar (ZMod p)) (t - x))
        = ∑ x : ZMod p, χ x * χ (t - x) := rfl
    _ = ∑ u : ZMod p, χ (t * u) * χ (t - t * u) := by
      rw [← Equiv.sum_comp (Equiv.mulLeft₀ t ht)
        (fun x : ZMod p => χ x * χ (t - x))]
      rfl
    _ = ∑ u : ZMod p, χ u * χ (1 - u) := by
      apply Finset.sum_congr rfl
      intro u _hu
      have hsub : t - t * u = t * (1 - u) := by ring
      rw [hsub, map_mul, map_mul]
      ring_nf
      rw [hχt_sq]
      ring
    _ = jacobiSum χ χ := by rfl
    _ = 1 := by simpa [χ] using jacobiSum_quadraticChar_self_eq_one p hp3 hp23

lemma qr_indicator_twice (p : ℕ) [Fact p.Prime] [NeZero p] (x : ZMod p) :
    2 * (if x ∈ QR p then (1 : ℤ) else 0) =
      1 + (quadraticChar (ZMod p)) x - (if x = 0 then (1 : ℤ) else 0) := by
  by_cases hx0 : x = 0
  · simp [hx0, mem_QR]
  · by_cases hsq : IsSquare x
    · have hxQR : x ∈ QR p := (mem_QR).mpr ⟨hx0, hsq⟩
      have hχ : (quadraticChar (ZMod p)) x = 1 :=
        (quadraticChar_one_iff_isSquare hx0).mpr hsq
      simp [hx0, hxQR, hχ]
    · have hxQR : x ∉ QR p := by
        intro h
        exact hsq ((mem_QR).mp h).2
      have hχ : (quadraticChar (ZMod p)) x = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hsq
      simp [hx0, hxQR, hχ]

lemma qr_pair_indicator_four (p : ℕ) [Fact p.Prime] [NeZero p] (t x : ZMod p) :
    4 * (if x ∈ QR p ∧ t - x ∈ QR p then (1 : ℤ) else 0) =
      (1 + (quadraticChar (ZMod p)) x - (if x = 0 then (1 : ℤ) else 0)) *
        (1 + (quadraticChar (ZMod p)) (t - x) -
          (if t - x = 0 then (1 : ℤ) else 0)) := by
  calc
    4 * (if x ∈ QR p ∧ t - x ∈ QR p then (1 : ℤ) else 0)
        = (2 * (if x ∈ QR p then (1 : ℤ) else 0)) *
            (2 * (if t - x ∈ QR p then (1 : ℤ) else 0)) := by
          by_cases hx : x ∈ QR p <;> by_cases hy : t - x ∈ QR p <;> simp [hx, hy]
    _ = (1 + (quadraticChar (ZMod p)) x - (if x = 0 then (1 : ℤ) else 0)) *
        (1 + (quadraticChar (ZMod p)) (t - x) -
          (if t - x = 0 then (1 : ℤ) else 0)) := by
          rw [qr_indicator_twice p x, qr_indicator_twice p (t - x)]

lemma quadraticChar_sum_sub_left_zero (p : ℕ) [Fact p.Prime]
    (hp23 : 23 ≤ p) (t : ZMod p) :
    (∑ x : ZMod p, (quadraticChar (ZMod p)) (t - x)) = 0 := by
  change (∑ x : ZMod p, (quadraticChar (ZMod p)) ((Equiv.subLeft t) x)) = 0
  rw [Equiv.sum_comp (Equiv.subLeft t) (fun x : ZMod p => (quadraticChar (ZMod p)) x)]
  exact quadraticChar_sum_zero (zmod_prime_odd_char_ne_two p hp23)

lemma qr_pair_count_formula (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) {t : ZMod p} (ht : t ≠ 0) :
    (4 : ℤ) *
        (((Finset.univ.filter fun x : ZMod p => x ∈ QR p ∧ t - x ∈ QR p).card : ℕ) :
          ℤ) =
      (p : ℤ) - 1 - 2 * (quadraticChar (ZMod p)) t := by
  let χ : MulChar (ZMod p) ℤ := quadraticChar (ZMod p)
  have hsumχ : (Finset.univ.sum fun x : ZMod p => χ x) = 0 := by
    simpa [χ] using quadraticChar_sum_zero (zmod_prime_odd_char_ne_two p hp23)
  have hsumχsub : (Finset.univ.sum fun x : ZMod p => χ (t - x)) = 0 := by
    simpa [χ] using quadraticChar_sum_sub_left_zero p hp23 t
  have hsumprod : (Finset.univ.sum fun x : ZMod p => χ x * χ (t - x)) = 1 := by
    simpa [χ] using quadraticChar_translate_sum_eq_one p hp3 hp23 ht
  calc
    (4 : ℤ) *
        (((Finset.univ.filter fun x : ZMod p => x ∈ QR p ∧ t - x ∈ QR p).card :
          ℕ) : ℤ)
        = Finset.univ.sum (fun x : ZMod p =>
            4 * (if x ∈ QR p ∧ t - x ∈ QR p then (1 : ℤ) else 0)) := by
          rw [Finset.card_filter]
          rw [Nat.cast_sum]
          rw [Finset.mul_sum]
          simp
    _ = Finset.univ.sum (fun x : ZMod p =>
        (1 + χ x - (if x = 0 then (1 : ℤ) else 0)) *
          (1 + χ (t - x) - (if t - x = 0 then (1 : ℤ) else 0))) := by
          apply Finset.sum_congr rfl
          intro x _hx
          simpa [χ] using qr_pair_indicator_four p t x
    _ = (p : ℤ) - 1 - 2 * χ t := by
      conv_lhs =>
        enter [2, x]
        ring_nf
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp [sub_eq_zero, hsumχ, hsumχsub, hsumprod, ht]
      ring

lemma qr_pair_count_ge_five (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) {t : ZMod p} (ht : t ≠ 0) :
    5 ≤ (Finset.univ.filter fun x : ZMod p => x ∈ QR p ∧ t - x ∈ QR p).card := by
  let pairs := Finset.univ.filter fun x : ZMod p => x ∈ QR p ∧ t - x ∈ QR p
  have hformula : (4 : ℤ) * (pairs.card : ℤ) =
      (p : ℤ) - 1 - 2 * (quadraticChar (ZMod p)) t := by
    simpa [pairs] using qr_pair_count_formula p hp3 hp23 ht
  have hχle : (quadraticChar (ZMod p)) t ≤ 1 := by
    rcases quadraticChar_dichotomy (F := ZMod p) ht with h | h
    · rw [h]
    · rw [h]
      norm_num
  have h20 : (20 : ℤ) ≤ 4 * (pairs.card : ℤ) := by
    rw [hformula]
    have hpz : (23 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp23
    nlinarith
  have h5z : (5 : ℤ) ≤ (pairs.card : ℤ) := by nlinarith
  exact_mod_cast h5z

lemma QR_card_ge_five (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) :
    5 ≤ (QR p).card := by
  let pairs := Finset.univ.filter fun x : ZMod p => x ∈ QR p ∧ (1 : ZMod p) - x ∈ QR p
  have hpairs : 5 ≤ pairs.card := by
    simpa [pairs] using qr_pair_count_ge_five p hp3 hp23 (t := (1 : ZMod p)) one_ne_zero
  have hpairs_subset : pairs ⊆ QR p := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2.1
  exact hpairs.trans (Finset.card_le_card hpairs_subset)

lemma QR_sdiff_singleton_card_ge_two (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) (w : ZMod p) :
    2 ≤ (QR p \ {w}).card := by
  have hQR : 5 ≤ (QR p).card := QR_card_ge_five p hp3 hp23
  by_cases hw : w ∈ QR p
  · rw [Finset.card_sdiff_of_subset]
    · simp
      omega
    · intro x hx
      have hxw : x = w := by simpa using hx
      subst hxw
      exact hw
  · have hsdiff : QR p \ {w} = QR p := by
      ext x
      constructor
      · intro hx
        exact (Finset.mem_sdiff.mp hx).1
      · intro hx
        exact Finset.mem_sdiff.mpr ⟨hx, by
          intro hxwMem
          have hxw : x = w := by simpa using hxwMem
          exact hw (by simpa [hxw] using hx)⟩
    rw [hsdiff]
    omega

theorem exists_two_QR_avoiding (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) (w : ZMod p) :
    ∃ u v, u ∈ QR p ∧ v ∈ QR p ∧ u ≠ v ∧ u ≠ w ∧ v ≠ w := by
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq (s := QR p \ {w}) (n := 2)
      (QR_sdiff_singleton_card_ge_two p hp3 hp23 w)
  obtain ⟨u, v, huv, hSuv⟩ := Finset.card_eq_two.mp hScard
  have huS : u ∈ S := by simp [hSuv]
  have hvS : v ∈ S := by simp [hSuv]
  have hu : u ∈ QR p \ {w} := hSsub huS
  have hv : v ∈ QR p \ {w} := hSsub hvS
  exact ⟨u, v, (Finset.mem_sdiff.mp hu).1, (Finset.mem_sdiff.mp hv).1, huv,
    by simpa using (Finset.mem_sdiff.mp hu).2,
    by simpa using (Finset.mem_sdiff.mp hv).2⟩

lemma qr_bad_card_le_four {p : ℕ} [DecidableEq (ZMod p)] (t : ZMod p)
    (U : Finset (ZMod p)) (hUcard : U.card ≤ 2) :
    (U ∪ U.image (fun y : ZMod p => t - y)).card ≤ 4 := by
  calc
    (U ∪ U.image (fun y : ZMod p => t - y)).card ≤
        U.card + (U.image (fun y : ZMod p => t - y)).card :=
      Finset.card_union_le U (U.image (fun y : ZMod p => t - y))
    _ ≤ U.card + U.card := by
      exact Nat.add_le_add_left (Finset.card_image_le) U.card
    _ ≤ 4 := by omega

theorem qr_sum_after_delete_two
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p)
    (U : Finset (ZMod p))
    (_hUQ : U ⊆ QR p) (hUcard : U.card ≤ 2) :
    ∀ t : ZMod p, t ≠ 0 →
      ∃ x, x ∈ QR p ∧ x ∉ U ∧
      ∃ y, y ∈ QR p ∧ y ∉ U ∧ x + y = t := by
  intro t ht
  let pairs := Finset.univ.filter fun x : ZMod p => x ∈ QR p ∧ t - x ∈ QR p
  let bad := U ∪ U.image (fun y : ZMod p => t - y)
  have hpairs : 5 ≤ pairs.card := by
    simpa [pairs] using qr_pair_count_ge_five p hp3 hp23 ht
  have hbad : bad.card ≤ 4 := by
    simpa [bad] using qr_bad_card_le_four t U hUcard
  have hbad_lt_pairs : bad.card < pairs.card := by omega
  obtain ⟨x, hxpair, hxbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt_pairs
  have hxpair' : x ∈ QR p ∧ t - x ∈ QR p := by
    simpa [pairs] using hxpair
  have hxU : x ∉ U := by
    intro hxU
    exact hxbad (by simp [bad, hxU])
  have hxNotImage : x ∉ U.image (fun y : ZMod p => t - y) := by
    intro hximg
    exact hxbad (by simp [bad, hximg])
  refine ⟨x, hxpair'.1, hxU, t - x, hxpair'.2, ?_, ?_⟩
  · intro hyU
    exact hxNotImage (by
      refine Finset.mem_image.mpr ⟨t - x, hyU, ?_⟩
      ring)
  · ring

/-- A translate of the surviving quadratic residues after deleting `U`. -/
noncomputable def shiftedQRDelete (p : ℕ) [NeZero p] (h : ZMod p)
    (U : Finset (ZMod p)) : Finset (ZMod p) :=
  (QR p \ U).image fun q => h + q

lemma mem_shiftedQRDelete {p : ℕ} [NeZero p] {h q : ZMod p}
    {U : Finset (ZMod p)} :
    q ∈ shiftedQRDelete p h U ↔ ∃ r, r ∈ QR p ∧ r ∉ U ∧ h + r = q := by
  classical
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
    exact ⟨r, (Finset.mem_sdiff.mp hr).1, (Finset.mem_sdiff.mp hr).2, rfl⟩
  · rintro ⟨r, hrQR, hrU, rfl⟩
    exact Finset.mem_image.mpr ⟨r, Finset.mem_sdiff.mpr ⟨hrQR, hrU⟩, rfl⟩

lemma notMem_shiftedQRDelete_add_deleted {p : ℕ} [NeZero p]
    (h u : ZMod p) (U : Finset (ZMod p)) (huU : u ∈ U) :
    h + u ∉ shiftedQRDelete p h U := by
  intro hmem
  rw [mem_shiftedQRDelete] at hmem
  rcases hmem with ⟨r, _hrQR, hrU, hr⟩
  have hru : r = u := by
    linear_combination hr
  exact hrU (by simpa [hru] using huU)

lemma notMem_shiftedQRDelete_sub_QR {p : ℕ} [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (h u : ZMod p) (U : Finset (ZMod p)) (huQR : u ∈ QR p) :
    h - u ∉ shiftedQRDelete p h U := by
  intro hmem
  rw [mem_shiftedQRDelete] at hmem
  rcases hmem with ⟨r, hrQR, _hrU, hr⟩
  have hru : r = -u := by
    linear_combination hr
  have hneg : -u ∈ QR p := by simpa [hru] using hrQR
  exact (qr_neg_disjoint p hp3 u huQR) hneg

lemma mem_shiftedQRDelete_add_self_iff {p : ℕ} [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p)
    (h : ZMod p) (U : Finset (ZMod p)) (hUQ : U ⊆ QR p) (hUcard : U.card ≤ 2)
    {z : ZMod p} :
    z ∈ ((shiftedQRDelete p h U : Set (ZMod p)) +
        (shiftedQRDelete p h U : Set (ZMod p))) ↔
      z ≠ h + h := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩ hzh
    have hxfin : x ∈ shiftedQRDelete p h U := hx
    have hyfin : y ∈ shiftedQRDelete p h U := hy
    rw [mem_shiftedQRDelete] at hxfin hyfin
    rcases hxfin with ⟨r, hrQR, _hrU, hrx⟩
    rcases hyfin with ⟨s, hsQR, _hsU, hsy⟩
    have hsum : h + r + (h + s) = h + h := by
      calc
        h + r + (h + s) = x + y := by rw [hrx, hsy]
        _ = z := hxy
        _ = h + h := hzh
    have hrs0 : r + s = 0 := by
      calc
        r + s = (h + r + (h + s)) - (h + h) := by ring
        _ = (h + h) - (h + h) := by rw [hsum]
        _ = 0 := by ring
    have hs_neg : s = -r := eq_neg_of_add_eq_zero_right hrs0
    have hnegmem : -r ∈ QR p := by simpa [hs_neg] using hsQR
    exact (qr_neg_disjoint p hp3 r hrQR) hnegmem
  · intro hz
    have ht : z - (h + h) ≠ 0 := by
      intro hzero
      apply hz
      exact sub_eq_zero.mp hzero
    obtain ⟨r, hrQR, hrU, s, hsQR, hsU, hrs⟩ :=
      qr_sum_after_delete_two p hp3 hp23 U hUQ hUcard (z - (h + h)) ht
    refine ⟨h + r, ?_, h + s, ?_, ?_⟩
    · exact (mem_shiftedQRDelete.mpr ⟨r, hrQR, hrU, rfl⟩ :
        h + r ∈ (shiftedQRDelete p h U : Set (ZMod p)))
    · exact (mem_shiftedQRDelete.mpr ⟨s, hsQR, hsU, rfl⟩ :
        h + s ∈ (shiftedQRDelete p h U : Set (ZMod p)))
    · calc
        (fun x y => x + y) (h + r) (h + s) = (h + h) + (r + s) := by ring
        _ = (h + h) + (z - (h + h)) := by rw [hrs]
        _ = z := by ring

theorem shiftedQRDelete_add_self_eq_compl_singleton {p : ℕ} [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p)
    (h : ZMod p) (U : Finset (ZMod p)) (hUQ : U ⊆ QR p) (hUcard : U.card ≤ 2) :
    ((shiftedQRDelete p h U : Set (ZMod p)) +
        (shiftedQRDelete p h U : Set (ZMod p))) =
      Set.univ \ ({h + h} : Set (ZMod p)) := by
  ext z
  rw [mem_shiftedQRDelete_add_self_iff hp3 hp23 h U hUQ hUcard]
  simp

theorem allowed_add_shiftedQRDelete_eq_univ {p : ℕ} [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p)
    (h α : ZMod p) (U : Finset (ZMod p)) (hUcard : U.card ≤ 2) :
    ((Set.univ \ ({α} : Set (ZMod p))) + (shiftedQRDelete p h U : Set (ZMod p))) =
      Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro z
  let w : ZMod p := z - α - h
  let bad : Finset (ZMod p) := insert w U
  have hbad_card : bad.card ≤ 3 := by
    calc
      bad.card ≤ U.card + 1 := Finset.card_insert_le w U
      _ ≤ 3 := by omega
  have hQR_card : 5 ≤ (QR p).card := QR_card_ge_five p hp3 hp23
  have hbad_lt_QR : bad.card < (QR p).card := by omega
  obtain ⟨r, hrQR, hrbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_lt_QR
  have hrU : r ∉ U := by
    intro hrU
    exact hrbad (by simp [bad, hrU])
  have hrw : r ≠ w := by
    intro hrw
    exact hrbad (by simp [bad, hrw])
  refine ⟨z - (h + r), ?_, h + r, ?_, ?_⟩
  · refine ⟨Set.mem_univ _, ?_⟩
    intro hαmem
    have hαeq : z - (h + r) = α := by simpa using hαmem
    apply hrw
    dsimp [w]
    linear_combination -hαeq
  · exact (mem_shiftedQRDelete.mpr ⟨r, hrQR, hrU, rfl⟩ :
      h + r ∈ (shiftedQRDelete p h U : Set (ZMod p)))
  · ring

theorem exists_selected_coordinate_data (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) (α : ZMod p) :
    ∃ h : ZMod p, ∃ U : Finset (ZMod p),
      U ⊆ QR p ∧ U.card = 2 ∧ (∀ u ∈ U, u ≠ -(α - h)) ∧
      ((shiftedQRDelete p h U : Set (ZMod p)) +
          (shiftedQRDelete p h U : Set (ZMod p))) =
        Set.univ \ ({h + h} : Set (ZMod p)) ∧
      ∀ q ∈ shiftedQRDelete p h U, q ≠ α := by
  obtain ⟨v, hvnsq⟩ :=
    FiniteField.exists_nonsquare (zmod_prime_odd_char_ne_two p hp23 :
      ringChar (ZMod p) ≠ 2)
  obtain ⟨u1, u2, hu1QR, hu2QR, hu12, hu1v, hu2v⟩ :=
    exists_two_QR_avoiding p hp3 hp23 (-v)
  have hUQ : ({u1, u2} : Finset (ZMod p)) ⊆ QR p := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hu1QR
    · exact hu2QR
  have hUcard : ({u1, u2} : Finset (ZMod p)).card = 2 := Finset.card_pair hu12
  refine ⟨α - v, {u1, u2}, hUQ, hUcard, ?_, ?_, ?_⟩
  · intro u hu
    have huv : u ≠ -v := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hu1v
      · exact hu2v
    simpa using huv
  · exact shiftedQRDelete_add_self_eq_compl_singleton hp3 hp23 (α - v) {u1, u2} hUQ
      hUcard.le
  · intro q hq hqα
    rw [mem_shiftedQRDelete] at hq
    rcases hq with ⟨r, hrQR, _hrU, hrq⟩
    have hrv : r = v := by
      calc
        r = (α - v + r) - (α - v) := by ring
        _ = q - (α - v) := by rw [hrq]
        _ = α - (α - v) := by rw [hqα]
        _ = v := by ring
    have hvQR : v ∈ QR p := by simpa [hrv] using hrQR
    exact hvnsq ((mem_QR.mp hvQR).2)

theorem exists_selected_coordinate_full_data (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) (α : ZMod p) :
    ∃ h : ZMod p, ∃ U : Finset (ZMod p),
      U ⊆ QR p ∧ U.card = 2 ∧ (∀ u ∈ U, u ≠ -(α - h)) ∧
      ((shiftedQRDelete p h U : Set (ZMod p)) +
          (shiftedQRDelete p h U : Set (ZMod p))) =
        Set.univ \ ({h + h} : Set (ZMod p)) ∧
      ((Set.univ \ ({α} : Set (ZMod p))) +
          (shiftedQRDelete p h U : Set (ZMod p))) = Set.univ ∧
      ∀ q ∈ shiftedQRDelete p h U, q ≠ α := by
  obtain ⟨h, U, hUQ, hUcard, havoid, hself, hQavoid⟩ :=
    exists_selected_coordinate_data p hp3 hp23 α
  refine ⟨h, U, hUQ, hUcard, havoid, hself, ?_, hQavoid⟩
  exact allowed_add_shiftedQRDelete_eq_univ hp3 hp23 h α U hUcard.le

theorem exists_selected_coordinate_pair_data (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) (α : ZMod p) :
    ∃ h u1 u2 : ZMod p,
      u1 ∈ QR p ∧ u2 ∈ QR p ∧ u1 ≠ u2 ∧
      u1 ≠ -(α - h) ∧ u2 ≠ -(α - h) ∧
      ((shiftedQRDelete p h ({u1, u2} : Finset (ZMod p)) : Set (ZMod p)) +
          (shiftedQRDelete p h ({u1, u2} : Finset (ZMod p)) : Set (ZMod p))) =
        Set.univ \ ({h + h} : Set (ZMod p)) ∧
      ((Set.univ \ ({α} : Set (ZMod p))) +
          (shiftedQRDelete p h ({u1, u2} : Finset (ZMod p)) : Set (ZMod p))) = Set.univ ∧
      ∀ q ∈ shiftedQRDelete p h ({u1, u2} : Finset (ZMod p)), q ≠ α := by
  obtain ⟨h, U, hUQ, hUcard, havoid, hself, hfull, hQavoid⟩ :=
    exists_selected_coordinate_full_data p hp3 hp23 α
  obtain ⟨u1, u2, hu12, hUeq⟩ := Finset.card_eq_two.mp hUcard
  have hu1U : u1 ∈ U := by simp [hUeq]
  have hu2U : u2 ∈ U := by simp [hUeq]
  refine ⟨h, u1, u2, hUQ hu1U, hUQ hu2U, hu12, havoid u1 hu1U, havoid u2 hu2U,
    ?_, ?_, ?_⟩
  · simpa [hUeq] using hself
  · simpa [hUeq] using hfull
  · intro q hq
    exact hQavoid q (by simpa [hUeq] using hq)

theorem exists_selected_coordinate_strong_pair_data (p : ℕ) [Fact p.Prime] [NeZero p]
    (hp3 : p % 4 = 3) (hp23 : 23 ≤ p) (α : ZMod p) :
    ∃ h u1 u2 : ZMod p,
      u1 ∈ QR p ∧ u2 ∈ QR p ∧ u1 ≠ u2 ∧
      h + h ≠ α + α ∧
      u1 ≠ α - h ∧ u2 ≠ α - h ∧
      u1 ≠ -(α - h) ∧ u2 ≠ -(α - h) ∧
      ((shiftedQRDelete p h ({u1, u2} : Finset (ZMod p)) : Set (ZMod p)) +
          (shiftedQRDelete p h ({u1, u2} : Finset (ZMod p)) : Set (ZMod p))) =
        Set.univ \ ({h + h} : Set (ZMod p)) ∧
      ((Set.univ \ ({α} : Set (ZMod p))) +
          (shiftedQRDelete p h ({u1, u2} : Finset (ZMod p)) : Set (ZMod p))) = Set.univ ∧
      ∀ q ∈ shiftedQRDelete p h ({u1, u2} : Finset (ZMod p)), q ≠ α := by
  obtain ⟨v, hvnsq⟩ :=
    FiniteField.exists_nonsquare (zmod_prime_odd_char_ne_two p hp23 :
      ringChar (ZMod p) ≠ 2)
  obtain ⟨u1, u2, hu1QR, hu2QR, hu12, hu1negv, hu2negv⟩ :=
    exists_two_QR_avoiding p hp3 hp23 (-v)
  let h : ZMod p := α - v
  have hu1v : u1 ≠ v := by
    intro hu
    have hvQR : v ∈ QR p := by simpa [hu] using hu1QR
    exact hvnsq ((mem_QR.mp hvQR).2)
  have hu2v : u2 ≠ v := by
    intro hu
    have hvQR : v ∈ QR p := by simpa [hu] using hu2QR
    exact hvnsq ((mem_QR.mp hvQR).2)
  have hUQ : ({u1, u2} : Finset (ZMod p)) ⊆ QR p := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hu1QR
    · exact hu2QR
  have hUcard : ({u1, u2} : Finset (ZMod p)).card = 2 := Finset.card_pair hu12
  have hv0 : v ≠ 0 := by
    intro hv0
    apply hvnsq
    rw [hv0]
    exact IsSquare.zero
  have hτ_ne : h + h ≠ α + α := by
    intro hτ
    have hv2 : (2 : ZMod p) * v = 0 := by
      dsimp [h] at hτ
      linear_combination -hτ
    rcases mul_eq_zero.mp hv2 with htwo | hv
    · have htwo' : (2 : ZMod p) ≠ 0 := by
        intro hzero
        have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
        have hp2 : p ≤ 2 := Nat.le_of_dvd (by omega) hdiv
        omega
      exact htwo' htwo
    · exact hv0 hv
  refine ⟨h, u1, u2, hu1QR, hu2QR, hu12, hτ_ne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [h] using hu1v
  · simpa [h] using hu2v
  · simpa [h] using hu1negv
  · simpa [h] using hu2negv
  · exact shiftedQRDelete_add_self_eq_compl_singleton hp3 hp23 h {u1, u2} hUQ hUcard.le
  · exact allowed_add_shiftedQRDelete_eq_univ hp3 hp23 h α {u1, u2} hUcard.le
  · intro q hq hqα
    rw [mem_shiftedQRDelete] at hq
    rcases hq with ⟨r, hrQR, _hrU, hrq⟩
    have hrv : r = v := by
      calc
        r = (α - v + r) - (α - v) := by ring
        _ = q - (α - v) := by rw [hrq]
        _ = α - (α - v) := by rw [hqα]
        _ = v := by ring
    have hvQR : v ∈ QR p := by simpa [hrv] using hrQR
    exact hvnsq ((mem_QR.mp hvQR).2)

end Erdos330
