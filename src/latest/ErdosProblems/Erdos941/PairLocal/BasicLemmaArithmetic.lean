/- Adapted from the checked repository proof in Erdos1148/BasicLemmaArithmetic.lean. -/
import Mathlib

/-!
# Arithmetic identities for the basic lemma

These lemmas formalize the coefficient calculations in the proof of the basic
lemma in Einsiedler–Lindenstrauss–Michel–Venkatesh, arXiv:1109.0413, §3. They do
not assume or prove the orbit-counting estimate or equidistribution theorem.
-/

namespace Erdos941.PairLocal

def discr {R : Type*} [CommRing R] (t : R × R × R) : R :=
  t.2.1 ^ 2 - 4 * t.1 * t.2.2

def pairing {R : Type*} [CommRing R] (t u : R × R × R) : R :=
  2 * t.2.1 * u.2.1 - 4 * t.1 * u.2.2 - 4 * u.1 * t.2.2

lemma discr_sub {R : Type*} [CommRing R] (t u : R × R × R) :
    discr (t - u) = discr t + discr u - pairing t u := by
  simp only [discr, pairing, Prod.fst_sub, Prod.snd_sub]
  ring

lemma discr_neg {R : Type*} [CommRing R] (t : R × R × R) :
    discr (-t) = discr t := by
  simp only [discr, Prod.fst_neg, Prod.snd_neg]
  ring

lemma pairing_neg_right {R : Type*} [CommRing R] (t u : R × R × R) :
    pairing t (-u) = -pairing t u := by
  simp only [pairing, Prod.fst_neg, Prod.snd_neg]
  ring

lemma eq_zero_of_nonsquare_mul_sq {d x y : ℤ} (hd : ¬ IsSquare d)
    (h : d * x ^ 2 = y ^ 2) : x = 0 := by
  by_contra hx
  apply hd
  apply Rat.isSquare_intCast_iff.mp
  refine ⟨(y : ℚ) / x, ?_⟩
  have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast hx
  have hq : (d : ℚ) * (x : ℚ) ^ 2 = (y : ℚ) ^ 2 := by exact_mod_cast h
  field_simp
  nlinarith [hq]

lemma fst_ne_zero_of_nonsquare_discr {d : ℤ} {t : ℤ × ℤ × ℤ}
    (hd : ¬ IsSquare d) (ht : discr t = d) : t.1 ≠ 0 := by
  intro ha
  apply hd
  refine ⟨t.2.1, ?_⟩
  simpa [discr, ha, pow_two] using ht.symm

/-- The degenerate positive pairing occurs only for identical forms. -/
lemma eq_of_pairing_eq_two_mul {d : ℤ} {t u : ℤ × ℤ × ℤ}
    (hd : ¬ IsSquare d) (ht : discr t = d) (hu : discr u = d)
    (hp : pairing t u = 2 * d) : t = u := by
  rcases t with ⟨a, b, c⟩
  rcases u with ⟨a', b', c'⟩
  have ha : a ≠ 0 := fst_ne_zero_of_nonsquare_discr hd ht
  dsimp [discr] at ht hu
  dsimp [pairing] at hp
  have hcross : d * (a' - a) ^ 2 = (a' * b - a * b') ^ 2 := by
    linear_combination -a' ^ 2 * ht - a ^ 2 * hu + a * a' * hp
  have haa : a' = a := by
    have := eq_zero_of_nonsquare_mul_sq hd hcross
    omega
  subst a'
  have hbb : b' = b := by
    nlinarith [sq_nonneg (b - b')]
  subst b'
  have hcc : c' = c := by
    have hmul : a * c' = a * c := by linarith
    exact mul_left_cancel₀ ha hmul
  subst c'
  rfl

/-- The degenerate negative pairing occurs only for opposite forms. -/
lemma eq_neg_of_pairing_eq_neg_two_mul {d : ℤ} {t u : ℤ × ℤ × ℤ}
    (hd : ¬ IsSquare d) (ht : discr t = d) (hu : discr u = d)
    (hp : pairing t u = -(2 * d)) : t = -u := by
  apply eq_of_pairing_eq_two_mul hd ht
  · simpa only [discr_neg] using hu
  · rw [pairing_neg_right, hp, neg_neg]

lemma pairing_sq_ne_four_mul_sq {d : ℤ} {t u : ℤ × ℤ × ℤ}
    (hd : ¬ IsSquare d) (ht : discr t = d) (hu : discr u = d)
    (hne : t ≠ u) (hneg : t ≠ -u) : (pairing t u) ^ 2 ≠ 4 * d ^ 2 := by
  intro h
  have heq : (pairing t u) ^ 2 = (2 * d) ^ 2 := by nlinarith [h]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp heq with hp | hp
  · exact hne (eq_of_pairing_eq_two_mul hd ht hu hp)
  · exact hneg (eq_neg_of_pairing_eq_neg_two_mul hd ht hu hp)

/-- Closeness excludes the negative degenerate value without a separate sign assumption. -/
lemma pairing_ne_degenerate_of_close {d L : ℤ} {t u : ℤ × ℤ × ℤ}
    (hd : ¬ IsSquare d) (ht : discr t = d) (hu : discr u = d) (hne : t ≠ u)
    (hL : L < 4 * d) (hclose : |2 * d - pairing t u| ≤ L) :
    pairing t u ≠ 2 * d ∧ pairing t u ≠ -(2 * d) := by
  constructor
  · intro hp
    exact hne (eq_of_pairing_eq_two_mul hd ht hu hp)
  · intro hp
    have habs := le_abs_self (2 * d - pairing t u)
    rw [hp] at habs hclose
    linarith

lemma abs_discr_le {t : ℝ × ℝ × ℝ} {B : ℝ}
    (ha : |t.1| ≤ B) (hb : |t.2.1| ≤ B) (hc : |t.2.2| ≤ B) :
    |discr t| ≤ 5 * B ^ 2 := by
  have hB : 0 ≤ B := (abs_nonneg _).trans ha
  have hb2 : t.2.1 ^ 2 ≤ B ^ 2 := by
    nlinarith [sq_abs t.2.1, mul_self_le_mul_self (abs_nonneg _) hb]
  have hac : |t.1| * |t.2.2| ≤ B ^ 2 := by
    simpa only [pow_two] using mul_le_mul ha hc (abs_nonneg _) hB
  calc
    |discr t| ≤ |t.2.1 ^ 2| + |4 * t.1 * t.2.2| := abs_sub _ _
    _ = t.2.1 ^ 2 + 4 * (|t.1| * |t.2.2|) := by
      rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_mul]
      norm_num
      ring
    _ ≤ 5 * B ^ 2 := by linarith

/-- The pairing lies in an interval quadratic in the coefficient distance. -/
lemma abs_two_mul_sub_pairing_le {d B : ℝ} {t u : ℝ × ℝ × ℝ}
    (ht : discr t = d) (hu : discr u = d)
    (ha : |t.1 - u.1| ≤ B) (hb : |t.2.1 - u.2.1| ≤ B)
    (hc : |t.2.2 - u.2.2| ≤ B) : |2 * d - pairing t u| ≤ 5 * B ^ 2 := by
  have h := abs_discr_le (t := t - u) ha hb hc
  rwa [discr_sub, ht, hu, ← two_mul] at h

/-- Multiples in a closed interval centered at a multiple, excluding the center. -/
noncomputable def noncentralMultiples (center L m : ℤ) : Finset ℤ :=
  (Finset.Icc (center - L) (center + L)).filter (fun ℓ => m ∣ ℓ ∧ ℓ ≠ center)

/-- There is no additive error term because the central multiple is excluded. -/
lemma card_noncentralMultiples {center L m : ℤ} (hL : 0 ≤ L) (hm : 0 < m)
    (hcenter : m ∣ center) :
    (noncentralMultiples center L m).card = 2 * (L / m).toNat := by
  have hr : 0 ≤ L / m := Int.ediv_nonneg hL hm.le
  have hrm : L / m * m ≤ L := Int.ediv_mul_le L hm.ne'
  have hcard : (noncentralMultiples center L m).card =
      ((Finset.Icc (-(L / m)) (L / m)).erase 0).card := by
    apply Finset.card_nbij' (fun ℓ => (ℓ - center) / m) (fun k => center + k * m)
    · intro ℓ hℓ
      simp only [Finset.mem_coe, noncentralMultiples, Finset.mem_filter, Finset.mem_Icc] at hℓ
      have hrec : (ℓ - center) / m * m = ℓ - center :=
        Int.ediv_mul_cancel (dvd_sub hℓ.2.1 hcenter)
      have hu : (ℓ - center) / m ≤ L / m :=
        (Int.le_ediv_iff_mul_le hm).2 (by linarith [hℓ.1.2])
      have hl : -((ℓ - center) / m) ≤ L / m :=
        (Int.le_ediv_iff_mul_le hm).2 (by nlinarith [hℓ.1.1])
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_Icc]
      constructor
      · intro hz
        rw [hz, zero_mul] at hrec
        exact hℓ.2.2 (by omega)
      · omega
    · intro k hk
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_Icc] at hk
      have hlu : k * m ≤ L / m * m := mul_le_mul_of_nonneg_right hk.2.2 hm.le
      have hll : -(L / m) * m ≤ k * m := mul_le_mul_of_nonneg_right hk.2.1 hm.le
      simp only [Finset.mem_coe, noncentralMultiples, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by nlinarith, by linarith⟩, dvd_add hcenter (dvd_mul_left m k), ?_⟩
      intro heq
      have : k * m = 0 := by linarith
      exact hk.1 ((mul_eq_zero.mp this).resolve_right hm.ne')
    · intro ℓ hℓ
      simp only [Finset.mem_coe, noncentralMultiples, Finset.mem_filter] at hℓ
      dsimp only
      rw [Int.ediv_mul_cancel (dvd_sub hℓ.2.1 hcenter)]
      ring
    · intro k _
      simp only [add_sub_cancel_left, Int.mul_ediv_cancel _ hm.ne']
  rw [hcard, Finset.card_erase_of_mem (by simp only [Finset.mem_Icc]; omega), Int.card_Icc]
  omega

lemma weighted_card_noncentralMultiples_le {center L : ℤ} {f : ℕ}
    (hL : 0 ≤ L) (hf : 0 < f) (hcenter : (f : ℤ) ^ 2 ∣ center) :
    (f : ℝ) * (noncentralMultiples center L ((f : ℤ) ^ 2)).card ≤
      2 * (L : ℝ) / f := by
  have hfZ : 0 < (f : ℤ) := by exact_mod_cast hf
  have hfR : 0 < (f : ℝ) := by exact_mod_cast hf
  have hm : 0 < (f : ℤ) ^ 2 := sq_pos_of_pos hfZ
  have hcard := card_noncentralMultiples hL hm hcenter
  have hcardZ : ((noncentralMultiples center L ((f : ℤ) ^ 2)).card : ℤ) =
      2 * (L / (f : ℤ) ^ 2) := by
    rw [hcard, Nat.cast_mul, Nat.cast_ofNat,
      Int.toNat_of_nonneg (Int.ediv_nonneg hL hm.le)]
  have hboundZ : ((noncentralMultiples center L ((f : ℤ) ^ 2)).card : ℤ) *
      (f : ℤ) ^ 2 ≤ 2 * L := by
    rw [hcardZ]
    nlinarith [Int.ediv_mul_le L hm.ne']
  have hboundR : ((noncentralMultiples center L ((f : ℤ) ^ 2)).card : ℝ) *
      (f : ℝ) ^ 2 ≤ 2 * (L : ℝ) := by exact_mod_cast hboundZ
  apply (le_div_iff₀ hfR).2
  nlinarith [hboundR]

noncomputable def squareDivisors (d : ℕ) : Finset ℕ :=
  d.divisors.filter (fun f => f ^ 2 ∣ d)

lemma mem_squareDivisors {d f : ℕ} (hd : d ≠ 0) :
    f ∈ squareDivisors d ↔ 0 < f ∧ f ^ 2 ∣ d := by
  simp only [squareDivisors, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hf, _⟩, hfsq⟩
    exact ⟨Nat.pos_of_dvd_of_pos hf (Nat.pos_of_ne_zero hd), hfsq⟩
  · rintro ⟨_, hfsq⟩
    exact ⟨⟨dvd_trans (dvd_pow_self f (by decide : 2 ≠ 0)) hfsq, hd⟩, hfsq⟩

/-- The weighted square-divisor sum has only logarithmic loss. -/
lemma sum_weighted_card_noncentralMultiples_le {d : ℕ} {L : ℤ}
    (hd : 0 < d) (hL : 0 ≤ L) :
    (∑ f ∈ squareDivisors d,
      (f : ℝ) * (noncentralMultiples (2 * d) L ((f : ℤ) ^ 2)).card) ≤
      2 * (L : ℝ) * (1 + Real.log d) := by
  have hLr : 0 ≤ (L : ℝ) := by exact_mod_cast hL
  have hsub : squareDivisors d ⊆ Finset.Icc 1 d := by
    intro f hf
    have hfd := (Finset.mem_filter.mp hf).1
    exact Finset.mem_Icc.mpr
      ⟨Nat.pos_of_mem_divisors hfd, Nat.le_of_dvd hd (Nat.dvd_of_mem_divisors hfd)⟩
  calc
    (∑ f ∈ squareDivisors d,
        (f : ℝ) * (noncentralMultiples (2 * d) L ((f : ℤ) ^ 2)).card) ≤
        ∑ f ∈ squareDivisors d, 2 * (L : ℝ) / f := by
      apply Finset.sum_le_sum
      intro f hf
      have hfs := (mem_squareDivisors hd.ne').mp hf
      apply weighted_card_noncentralMultiples_le hL hfs.1
      have hdiv : (f : ℤ) ^ 2 ∣ (d : ℤ) := by exact_mod_cast hfs.2
      exact dvd_mul_of_dvd_right hdiv 2
    _ ≤ ∑ f ∈ Finset.Icc 1 d, 2 * (L : ℝ) / f := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro f _ _
      positivity
    _ = 2 * (L : ℝ) * (harmonic d : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      simp only [Rat.cast_inv, Rat.cast_natCast, div_eq_mul_inv]
    _ ≤ 2 * (L : ℝ) * (1 + Real.log d) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log d) (by positivity)

lemma sum_weighted_card_noncentralMultiples_le_rpow {d : ℕ} {L : ℤ} {ε : ℝ}
    (hd : 0 < d) (hL : 0 ≤ L) (hε : 0 < ε) :
    (∑ f ∈ squareDivisors d,
      (f : ℝ) * (noncentralMultiples (2 * d) L ((f : ℤ) ^ 2)).card) ≤
      (2 * (1 + ε⁻¹)) * L * (d : ℝ) ^ ε := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hp : 1 ≤ (d : ℝ) ^ ε := Real.one_le_rpow hdR hε.le
  have hlog := Real.log_le_rpow_div (show 0 ≤ (d : ℝ) by positivity) hε
  have hbound : 1 + Real.log d ≤ (1 + ε⁻¹) * (d : ℝ) ^ ε := by
    rw [div_eq_mul_inv] at hlog
    nlinarith
  calc
    _ ≤ 2 * (L : ℝ) * (1 + Real.log d) :=
      sum_weighted_card_noncentralMultiples_le hd hL
    _ ≤ 2 * (L : ℝ) * ((1 + ε⁻¹) * (d : ℝ) ^ ε) :=
      mul_le_mul_of_nonneg_left hbound (by exact_mod_cast (show 0 ≤ 2 * L by omega))
    _ = _ := by ring

end Erdos941.PairLocal
