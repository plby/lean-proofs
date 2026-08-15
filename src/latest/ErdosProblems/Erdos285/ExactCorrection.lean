import Mathlib
import ErdosProblems.Erdos285.PrimePowers
import UnitFractions.Definitions

/-!
# Exact finite correction and cardinality padding

This file isolates the algebraic part of Martin's exact-correction argument for
Erdős Problem 285.  All reciprocal sums here are rational.  The analytic
construction converts its error into a rational number, so this loses no
information and makes divisibility arguments available.

The final quantitative bound on the largest denominator requires Martin's
prime-power elimination lemmas.  The results below provide the exact
telescoping identity, the odd-prime inverse-pair construction, and the
displayed-fraction cancellation identities used by those lemmas.
-/

namespace Erdos285.ExactCorrection

open Finset
open scoped BigOperators

noncomputable section

/-- The elementary two-term split used to increase the cardinality of an
Egyptian representation by one. -/
theorem unitFraction_split (n : ℕ) (hn : 0 < n) :
    (1 : ℚ) / n = 1 / (n + 1 : ℕ) + 1 / (n * (n + 1) : ℕ) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn10 : (n : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp

/-- A finite version of the telescoping split.

For `m = 1` this is `unitFraction_split`.  In Martin's padding step it replaces
one denominator `n` by `m + 1` unit fractions while preserving the sum.
-/
theorem unitFraction_telescoping (n m : ℕ) (hn : 0 < n) :
    (1 : ℚ) / n = 1 / (n + m : ℕ) +
      ∑ j ∈ range m, (1 : ℚ) / ((n + j) * (n + j + 1) : ℕ) := by
  have hterm : ∀ j : ℕ,
      (1 : ℚ) / ((n + j) * (n + j + 1) : ℕ) =
        1 / (n + j : ℕ) - 1 / (n + j + 1 : ℕ) := by
    intro j
    have hj : (0 : ℚ) < n + j := by exact_mod_cast Nat.add_pos_left hn j
    have hj1 : (0 : ℚ) < n + j + 1 := by positivity
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  have htel := sum_range_sub' (fun j : ℕ ↦ (1 : ℚ) / (n + j : ℕ)) m
  simpa [Nat.add_assoc] using congrArg (fun x : ℚ ↦ 1 / (n + m : ℕ) + x) htel.symm

/-! ## The inverse-pair core of the odd-prime case -/

/-- Over a prime field of cardinality at least five, every residue is a sum
of the inverses of two distinct units.

This is the finite-field core of Martin's odd prime-power inverse-pair lemma.
The three excluded inverse residues are `0`, `c`, and `c / 2`: avoiding them
ensures that both summands are nonzero and different. -/
theorem exists_distinct_inverse_pair_mod_prime (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (c : ZMod p) :
    ∃ x y : ZMod p,
      IsUnit x ∧ IsUnit y ∧ x ≠ y ∧ x⁻¹ + y⁻¹ = c := by
  let _ : Fact p.Prime := ⟨hp⟩
  let bad : Finset (ZMod p) := {0, c, c / 2}
  have hbadcard : bad.card ≤ 3 := by
    exact Finset.card_le_three
  have hbadne : bad ≠ univ := by
    intro hbad
    have hcard : bad.card = p := by
      rw [hbad]
      simp
    omega
  have hnotall : ¬ ∀ u : ZMod p, u ∈ bad := by
    intro hall
    exact hbadne (Finset.eq_univ_iff_forall.mpr hall)
  push Not at hnotall
  obtain ⟨u, hu⟩ := hnotall
  have hu0 : u ≠ 0 := by
    intro h
    apply hu
    simp [bad, h]
  have huc : u ≠ c := by
    intro h
    apply hu
    simp [bad, h]
  have huhalf : u ≠ c / 2 := by
    intro h
    apply hu
    simp [bad, h]
  let v : ZMod p := c - u
  have hv0 : v ≠ 0 := by
    intro h
    apply huc
    dsimp [v] at h
    exact sub_eq_zero.mp h |>.symm
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    intro h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hple : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega
  have huv : u ≠ v := by
    intro huv
    apply huhalf
    rw [eq_div_iff htwo]
    dsimp [v] at huv
    have hc : u + u = c := by
      calc
        u + u = (c - u) + u := congrArg (fun z : ZMod p ↦ z + u) huv
        _ = c := by ring
    calc
      u * 2 = u + u := by ring
      _ = c := hc
  refine ⟨u⁻¹, v⁻¹, (isUnit_iff_ne_zero.mpr ?_),
    (isUnit_iff_ne_zero.mpr ?_), ?_, ?_⟩
  · simpa using (inv_ne_zero hu0)
  · simpa using (inv_ne_zero hv0)
  · exact fun h ↦ huv (inv_inj.mp h)
  · simp [v]

/-- Source-faithful pigeonhole core of Martin's Lemma 14 for primes at least
five.  The numbers `s,t` are the small positive complements of the desired
integers near a prime power. -/
theorem exists_inverse_pair_complements (p : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) (a : ZMod p) :
    ∃ s t : ℕ,
      1 ≤ s ∧ s ≤ (p + 3) / 2 ∧
      1 ≤ t ∧ t ≤ (p + 3) / 2 ∧
      s ≠ t ∧
      (-((s : ℕ) : ZMod p))⁻¹ + (-((t : ℕ) : ZMod p))⁻¹ = a := by
  let _ : Fact p.Prime := ⟨hp⟩
  let h : ℕ := (p + 3) / 2
  let D : Finset ℕ := Icc 1 h
  let f : ℕ → ZMod p := fun s ↦ (-((s : ℕ) : ZMod p))⁻¹
  let A : Finset (ZMod p) := D.image f
  let B : Finset (ZMod p) := A.image fun x ↦ a - x
  have hpne2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hpne2
  have heven : Even (p + 3) := by
    rcases hpodd with ⟨w, hw⟩
    refine ⟨w + 2, ?_⟩
    omega
  have htwoh : 2 * h = p + 3 := by
    exact Nat.two_mul_div_two_of_even heven
  have hltp : h < p := by
    dsimp [h]
    omega
  have hDcard : D.card = h := by
    simp [D]
  have hfinj : Set.InjOn f D := by
    intro s hs t ht hst
    have hsD := Finset.mem_Icc.mp hs
    have htD := Finset.mem_Icc.mp ht
    have hcast : (s : ZMod p) = (t : ZMod p) := by
      apply neg_injective
      exact inv_inj.mp hst
    have hmod : s ≡ t [MOD p] :=
      (ZMod.natCast_eq_natCast_iff s t p).mp hcast
    exact hmod.eq_of_lt_of_lt (hsD.2.trans_lt hltp) (htD.2.trans_lt hltp)
  have hAcard : A.card = h := by
    change (D.image f).card = h
    rw [Finset.card_image_iff.mpr hfinj, hDcard]
  have hBcard : B.card = h := by
    change (A.image (fun x ↦ a - x)).card = h
    rw [Finset.card_image_iff.mpr, hAcard]
    intro x _ y _ hxy
    exact sub_right_injective hxy
  have hunion : (A ∪ B).card ≤ p := by
    simpa [ZMod.card] using Finset.card_le_univ (A ∪ B)
  have hinter : 3 ≤ (A ∩ B).card := by
    have hcount := Finset.card_inter_add_card_union A B
    rw [hAcard, hBcard] at hcount
    omega
  have hexists : ∃ r ∈ A ∩ B, r ≠ a / 2 := by
    by_contra hnone
    push Not at hnone
    have hsub : A ∩ B ⊆ {a / 2} := by
      intro r hr
      simpa using hnone r hr
    have hsmall := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hsmall
    omega
  obtain ⟨r, hr, hrhalf⟩ := hexists
  obtain ⟨s, hsD, hsr⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hr).1
  obtain ⟨x, hxA, hxr⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hr).2
  obtain ⟨t, htD, htx⟩ := Finset.mem_image.mp hxA
  have hsum : f s + f t = a := by
    rw [hsr, htx]
    exact ((sub_eq_iff_eq_add).mp hxr).symm
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    intro hz
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hple : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega
  have hst : s ≠ t := by
    intro hst
    subst t
    have hfxr : f s = r := hsr
    have hfx : f s = x := htx
    apply hrhalf
    rw [← hfxr, ← hfx] at hxr
    rw [← hfxr, eq_div_iff htwo, mul_two]
    exact ((sub_eq_iff_eq_add).mp hxr).symm
  rcases Finset.mem_Icc.mp hsD with ⟨hs1, hsh⟩
  rcases Finset.mem_Icc.mp htD with ⟨ht1, hth⟩
  exact ⟨s, t, hs1, hsh, ht1, hth, hst, hsum⟩

/-- Martin's Lemma 14 for prime powers whose underlying prime is at least
five.  The inverse congruence is modulo `p`, exactly as used to remove one
power of `p` from the reduced denominator. -/
theorem martin_lemma14_of_five_le {p ν : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hν : 0 < ν) (a : ZMod p) :
    ∃ m₁ m₂ : ℕ,
      (p ^ ν - 3) / 2 ≤ m₁ ∧
      m₁ < m₂ ∧ m₂ < p ^ ν ∧
      ¬ p ∣ m₁ * m₂ ∧
      ((m₁ : ZMod p)⁻¹ + (m₂ : ZMod p)⁻¹) = a := by
  obtain ⟨s, t, hs1, hsh, ht1, hth, hst, hsum⟩ :=
    exists_inverse_pair_complements p hp hp5 a
  let q : ℕ := p ^ ν
  let h : ℕ := (p + 3) / 2
  have hp0 : 0 < p := hp.pos
  have hpq : p ≤ q := by
    dsimp [q]
    exact Nat.le_pow hν
  have hq5 : 5 ≤ q := hp5.trans hpq
  have htwoh : 2 * h = p + 3 := by
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have heven : Even (p + 3) := by
      rcases hpodd with ⟨w, hw⟩
      exact ⟨w + 2, by omega⟩
    exact Nat.two_mul_div_two_of_even heven
  have hhp : h < p := by
    dsimp [h]
    omega
  have hsq : s ≤ q := hsh.trans (hhp.le.trans hpq)
  have htq : t ≤ q := hth.trans (hhp.le.trans hpq)
  have hqh : h ≤ q := hhp.le.trans hpq
  have hlower : (q - 3) / 2 ≤ q - h := by
    omega
  have hqdiv : p ∣ q := by
    dsimp [q]
    exact dvd_pow_self p (Nat.ne_zero_of_lt hν)
  have hnotdvd_s : ¬ p ∣ q - s := by
    intro hdiff
    have hps : p ∣ s := by
      rw [Nat.dvd_add_iff_left hdiff]
      rw [show s + (q - s) = q by omega]
      exact hqdiv
    have hple : p ≤ s := Nat.le_of_dvd (by omega) hps
    omega
  have hnotdvd_t : ¬ p ∣ q - t := by
    intro hdiff
    have hpt : p ∣ t := by
      rw [Nat.dvd_add_iff_left hdiff]
      rw [show t + (q - t) = q by omega]
      exact hqdiv
    have hple : p ≤ t := Nat.le_of_dvd (by omega) hpt
    omega
  have hqcast : (q : ZMod p) = 0 := by
    apply (ZMod.natCast_eq_zero_iff q p).mpr
    exact hqdiv
  have hinv_s : (((q - s : ℕ) : ZMod p)⁻¹) = (-((s : ℕ) : ZMod p))⁻¹ := by
    rw [Nat.cast_sub hsq, hqcast, zero_sub]
  have hinv_t : (((q - t : ℕ) : ZMod p)⁻¹) = (-((t : ℕ) : ZMod p))⁻¹ := by
    rw [Nat.cast_sub htq, hqcast, zero_sub]
  rcases lt_or_gt_of_ne hst with hstlt | htslt
  · refine ⟨q - t, q - s, ?_, ?_, ?_, ?_, ?_⟩
    · exact hlower.trans (Nat.sub_le_sub_left hth q)
    · omega
    · omega
    · intro hdvd
      rcases (hp.dvd_mul.mp hdvd) with hdvd | hdvd
      · exact hnotdvd_t hdvd
      · exact hnotdvd_s hdvd
    · rw [hinv_t, hinv_s, add_comm]
      exact hsum
  · refine ⟨q - s, q - t, ?_, ?_, ?_, ?_, ?_⟩
    · exact hlower.trans (Nat.sub_le_sub_left hsh q)
    · omega
    · omega
    · intro hdvd
      rcases (hp.dvd_mul.mp hdvd) with hdvd | hdvd
      · exact hnotdvd_s hdvd
      · exact hnotdvd_t hdvd
    · rw [hinv_s, hinv_t]
      exact hsum

/-! ## Displayed-fraction cancellation -/

/-- If a common natural factor divides both the displayed numerator and
denominator of a rational, then the reduced denominator divides the displayed
denominator after that factor is cancelled.

This is the bridge from the modular numerator congruence in Martin's Lemmas
15 and 16 to strict descent of the reduced denominator's prime-power part. -/
theorem rat_den_dvd_div_of_eq_divInt {r : ℚ} {a : ℤ} {b p : ℕ}
    (hb : b ≠ 0) (hp : p ≠ 0) (hpb : p ∣ b)
    (hpa : (p : ℤ) ∣ a) (hr : r = Rat.divInt a b) :
    r.den ∣ b / p := by
  obtain ⟨b', rfl⟩ := hpb
  obtain ⟨a', ha'⟩ := hpa
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  have hrepr : r = Rat.divInt a' b' := by
    rw [hr, ha']
    push_cast
    exact Rat.divInt_mul_left hpZ
  rw [hrepr]
  have hdenZ : (((Rat.divInt a' b').den : ℕ) : ℤ) ∣ (b' : ℤ) :=
    Rat.den_dvd a' b'
  have hden : (Rat.divInt a' b').den ∣ b' := by
    exact_mod_cast hdenZ
  simpa [hp] using hden

/-- Subtracting the two unit fractions used in the odd prime-power step,
written over the displayed denominator `r.den * m₁ * m₂`.

The hypothesis `q ∣ r.den` is exactly the branch in which Lemma 15 performs
a correction.  This form exposes the numerator on which its congruence
argument proves divisibility by the underlying prime. -/
theorem sub_two_unitFractions_eq_divInt (r : ℚ) (q m₁ m₂ : ℕ)
    (hq : q ≠ 0) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0)
    (hqd : q ∣ r.den) :
    r - (1 : ℚ) / (q * m₁ : ℕ) - (1 : ℚ) / (q * m₂ : ℕ) =
      Rat.divInt
        (r.num * (m₁ * m₂ : ℕ) -
          ((r.den / q) * (m₁ + m₂) : ℕ))
        (r.den * m₁ * m₂) := by
  let d : ℕ := r.den / q
  change r - (1 : ℚ) / (q * m₁ : ℕ) - (1 : ℚ) / (q * m₂ : ℕ) =
    Rat.divInt
      (r.num * (m₁ * m₂ : ℕ) - (d * (m₁ + m₂) : ℕ))
      (r.den * m₁ * m₂)
  have hden : q * d = r.den := Nat.mul_div_cancel' hqd
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hm₁Q : (m₁ : ℚ) ≠ 0 := by exact_mod_cast hm₁
  have hm₂Q : (m₂ : ℚ) ≠ 0 := by exact_mod_cast hm₂
  have hrdenQ : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hdenQ : (q : ℚ) * d = r.den := by
    exact_mod_cast hden
  rw [Rat.divInt_eq_div]
  nth_rewrite 1 [← Rat.num_div_den r]
  push_cast
  field_simp
  rw [← hdenQ]
  ring

/-- A representation whose denominators are above `A.sup id` is disjoint from
the finite set `A`. -/
theorem disjoint_of_sup_lt {A E : Finset ℕ}
    (hE : ∀ e ∈ E, A.sup id < e) : Disjoint A E := by
  rw [Finset.disjoint_left]
  intro a haA haE
  have hale : a ≤ A.sup id := Finset.le_sup (f := id) haA
  exact (not_lt_of_ge hale) (hE a haE)

/-- Joining an approximate representation to a disjoint exact correction adds
both reciprocal sums and cardinalities. -/
theorem union_correction {A E : Finset ℕ} (hdisj : Disjoint A E) :
    UnitFractions.rec_sum (A ∪ E) =
        UnitFractions.rec_sum A + UnitFractions.rec_sum E ∧
      (A ∪ E).card = A.card + E.card := by
  exact ⟨UnitFractions.rec_sum_disjoint hdisj, Finset.card_union_of_disjoint hdisj⟩

end

end Erdos285.ExactCorrection
