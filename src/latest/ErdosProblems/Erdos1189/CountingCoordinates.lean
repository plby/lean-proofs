/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The finite coordinate initial segments in the sharp counting construction.
Informal source: BBMST Definition 5.4, with zero-based digit indices.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameOrdering
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.PrimeCounting

namespace Erdos1189

open Finset

lemma coordinateScore_lower {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((p : ℝ) - 1) * ((e : ℝ) + 1) ≤ coordinateScore p e := by
  have hunit : logIncrement e * ((e : ℝ) + 1) ≤ 1 := by
    apply (le_div_iff₀ (by positivity)).mp
    simpa only [one_div] using logIncrement_le_inv e
  have hr : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have h : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
    linarith
  apply (le_div_iff₀ (logIncrement_pos e)).mpr
  have h := mul_le_mul_of_nonneg_left hunit hr
  nlinarith

lemma coordinateScore_ge_prime_weight {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (p : ℝ) - 1 ≤ coordinateScore p e := by
  have h := coordinateScore_lower hp e
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  nlinarith

lemma coordinateScore_ge_exponent {p : ℕ} (hp : p.Prime) (e : ℕ) :
    (e : ℝ) + 1 ≤ coordinateScore p e := by
  have h := coordinateScore_lower hp e
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have he : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  nlinarith

noncomputable def countingCoordinates (x : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((range (Nat.ceil x + 2)).product (range (Nat.ceil x))).filter
    fun c => c.1.Prime ∧ coordinateScore c.1 c.2 < x

lemma mem_countingCoordinates {x : ℝ} {p e : ℕ} :
    (p, e) ∈ countingCoordinates x ↔ p.Prime ∧ coordinateScore p e < x := by
  classical
  constructor
  · exact fun h => (mem_filter.mp h).2
  · rintro ⟨hp, hscore⟩
    have hceil := Nat.le_ceil x
    have hprime := coordinateScore_ge_prime_weight hp e
    have hexp := coordinateScore_ge_exponent hp e
    have hpbound : p < Nat.ceil x + 2 := by
      have h : (p : ℝ) < (Nat.ceil x : ℝ) + 2 := by linarith
      exact_mod_cast h
    have hebound : e < Nat.ceil x := by
      have h : (e : ℝ) < Nat.ceil x := by linarith
      exact_mod_cast h
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr hpbound, mem_range.mpr hebound⟩,
      hp, hscore⟩

lemma countingCoordinates_downward {x : ℝ} {p e f : ℕ}
    (h : (p, e) ∈ countingCoordinates x) (hfe : f ≤ e) :
    (p, f) ∈ countingCoordinates x := by
  obtain ⟨hp, hs⟩ := mem_countingCoordinates.mp h
  exact mem_countingCoordinates.mpr ⟨hp, ((coordinateScore_strictMono hp).monotone hfe).trans_lt hs⟩

lemma countingCoordinates_smaller_prime {x : ℝ} {p q e : ℕ}
    (h : (p, e) ∈ countingCoordinates x) (hq : q.Prime) (hqp : q < p) :
    (q, 0) ∈ countingCoordinates x := by
  obtain ⟨hp, hs⟩ := mem_countingCoordinates.mp h
  exact mem_countingCoordinates.mpr ⟨hq, (first_prime_score_lt hp hqp e).trans hs⟩

lemma countingCoordinates_mono : Monotone countingCoordinates := by
  intro x y hxy _ hc
  obtain ⟨hp, hs⟩ := mem_countingCoordinates.mp hc
  exact mem_countingCoordinates.mpr ⟨hp, hs.trans_le hxy⟩

noncomputable def countingInteger (x : ℝ) : ℕ := ∏ c ∈ countingCoordinates x, c.1

lemma countingInteger_ne_zero (x : ℝ) : countingInteger x ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ hc => (mem_countingCoordinates.mp hc).1.ne_zero

lemma countingInteger_factorization (x : ℝ) (p : ℕ) :
    (countingInteger x).factorization p =
      ((countingCoordinates x).filter (fun c => c.1 = p)).card := by
  classical
  rw [countingInteger, Nat.factorization_prod_apply
    (fun c hc => (mem_countingCoordinates.mp hc).1.ne_zero)]
  calc
    _ = ∑ c ∈ countingCoordinates x, if c.1 = p then 1 else 0 := by
      apply sum_congr rfl
      intro c hc
      simp only [(mem_countingCoordinates.mp hc).1.factorization, Finsupp.single_apply]
    _ = _ := by simp

lemma mem_primeFactors_countingInteger {x : ℝ} {p : ℕ} :
    p ∈ (countingInteger x).primeFactors ↔ (p, 0) ∈ countingCoordinates x := by
  classical
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  rw [countingInteger_factorization, card_ne_zero]
  constructor
  · rintro ⟨⟨q, e⟩, hc⟩
    obtain ⟨hc, hqp⟩ := mem_filter.mp hc
    dsimp at hqp
    subst q
    exact countingCoordinates_downward hc (Nat.zero_le e)
  · intro hp
    exact ⟨(p, 0), mem_filter.mpr ⟨hp, rfl⟩⟩

theorem countingInteger_primeFactors_initial {x : ℝ} (hx : coordinateScore 7 0 < x) :
    ∃ P : ℕ, P.Prime ∧ 7 ≤ P ∧ (countingInteger x).primeFactors = Nat.primesLE P := by
  have h7 : 7 ∈ (countingInteger x).primeFactors :=
    mem_primeFactors_countingInteger.mpr (mem_countingCoordinates.mpr ⟨by norm_num, hx⟩)
  have hne : (countingInteger x).primeFactors.Nonempty := ⟨7, h7⟩
  let P := (countingInteger x).primeFactors.max' hne
  have hPmem : P ∈ (countingInteger x).primeFactors := max'_mem _ _
  have hP := Nat.prime_of_mem_primeFactors hPmem
  refine ⟨P, hP, le_max' _ _ h7, ?_⟩
  ext q
  constructor
  · intro hq
    exact Nat.mem_primesLE.mpr ⟨le_max' _ _ hq, Nat.prime_of_mem_primeFactors hq⟩
  · intro hq
    obtain ⟨hqP, hqprime⟩ := Nat.mem_primesLE.mp hq
    rcases hqP.eq_or_lt with hqeq | hqlt
    · simpa only [hqeq] using hPmem
    · exact mem_primeFactors_countingInteger.mpr (countingCoordinates_smaller_prime
        (mem_primeFactors_countingInteger.mp hPmem) hqprime hqlt)

lemma countingInteger_one_lt {x : ℝ} (hx : coordinateScore 7 0 < x) :
    1 < countingInteger x := by
  have h7 : 7 ∈ (countingInteger x).primeFactors :=
    mem_primeFactors_countingInteger.mpr (mem_countingCoordinates.mpr ⟨by norm_num, hx⟩)
  exact (by norm_num : 1 < 7).trans_le (Nat.le_of_dvd
    (Nat.pos_of_ne_zero (countingInteger_ne_zero x)) (Nat.dvd_of_mem_primeFactors h7))

lemma mem_lower_finset_iff_lt_card {S : Finset ℕ}
    (hS : ∀ n ∈ S, ∀ m ≤ n, m ∈ S) (n : ℕ) : n ∈ S ↔ n < S.card := by
  constructor
  · intro hn
    have hsub : range (n + 1) ⊆ S := by
      intro m hm
      exact hS n hn m (by simpa using mem_range.mp hm)
    have hc := card_le_card hsub
    rw [card_range] at hc
    omega
  · intro hn
    by_contra hnot
    have hsub : S ⊆ range n := by
      intro m hm
      apply mem_range.mpr
      by_contra hmn
      exact hnot (hS m hm n (by omega))
    have hc := card_le_card hsub
    rw [card_range] at hc
    omega

theorem countingInteger_digit_iff {x : ℝ} {p e : ℕ} :
    e < (countingInteger x).factorization p ↔ (p, e) ∈ countingCoordinates x := by
  classical
  let S := (countingCoordinates x).filter (fun c => c.1 = p)
  let E := S.image Prod.snd
  have hmem : ∀ f, f ∈ E ↔ (p, f) ∈ countingCoordinates x := by
    intro f
    constructor
    · intro hf
      obtain ⟨⟨q, j⟩, hqj, hje⟩ := mem_image.mp hf
      obtain ⟨hqj, hqp⟩ := mem_filter.mp hqj
      dsimp at hqp hje
      subst q
      subst j
      exact hqj
    · intro hf
      exact mem_image.mpr ⟨(p, f), mem_filter.mpr ⟨hf, rfl⟩, rfl⟩
  have hE : ∀ n ∈ E, ∀ m ≤ n, m ∈ E := by
    intro n hn m hmn
    exact (hmem m).mpr (countingCoordinates_downward ((hmem n).mp hn) hmn)
  have hinj : Set.InjOn (fun c : ℕ × ℕ => c.2) S := by
    intro c hc d hd hcd
    apply Prod.ext
    · exact (mem_filter.mp hc).2.trans (mem_filter.mp hd).2.symm
    · exact hcd
  have hcard : E.card = (countingInteger x).factorization p := by
    rw [countingInteger_factorization]
    exact card_image_of_injOn hinj
  rw [← hcard, ← mem_lower_finset_iff_lt_card hE, hmem]

def coordinatePair {N : ℕ} (c : PrimeCoordinate N) : ℕ × ℕ := (c.1.val, c.2.val)

lemma coordinatePair_injective (N : ℕ) : Function.Injective (@coordinatePair N) := by
  rintro ⟨⟨p, hp⟩, ⟨e, he⟩⟩ ⟨⟨q, hq⟩, ⟨f, hf⟩⟩ h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  rfl

lemma image_counting_coordinates (x : ℝ) :
    (univ : Finset (PrimeCoordinate (countingInteger x))).image coordinatePair =
      countingCoordinates x := by
  classical
  ext c
  constructor
  · intro hc
    obtain ⟨i, _, rfl⟩ := mem_image.mp hc
    exact countingInteger_digit_iff.mp i.2.isLt
  · intro hc
    have hp := mem_primeFactors_countingInteger.mpr
      (countingCoordinates_downward hc (Nat.zero_le c.2))
    exact mem_image.mpr ⟨⟨⟨c.1, hp⟩, ⟨c.2, countingInteger_digit_iff.mpr hc⟩⟩,
      mem_univ _, rfl⟩

theorem countingInteger_weight (x : ℝ) :
    simpsonWeight (countingInteger x) = ∑ c ∈ countingCoordinates x, (c.1 - 1) := by
  classical
  rw [← image_counting_coordinates, sum_image
    (fun _ _ _ _ h => coordinatePair_injective (countingInteger x) h)]
  exact (sum_coordinateSize (countingInteger x)).symm

end Erdos1189
