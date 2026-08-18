/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiUpper
import ErdosProblems.Erdos186.CFP.Bilu.MinkowskiSecondUpper
import ErdosProblems.Erdos186.CFP.Bilu.MahlerTheorem

/-!
# A coarse upper Minkowski--II inequality

For the application to the discrete John theorem one does not need the
sharp constant in Minkowski's second theorem.  This file follows the usual
packing proof with dyadic moduli.  The `i`-th modulus is four times the
largest dyadic integer below `m / lambda_i`.  If two lattice points of
`m K` have the same residues, divide their difference by the last nonzero
dyadic modulus; it is a lattice point strictly shorter than the relevant
successive minimum, contradicting the saturated-flag coordinate theorem.
-/

namespace Erdos186.CFP.Bilu.MinkowskiUpperCoarse

open scoped BigOperators Pointwise
open Filter MeasureTheory Module Set
open Erdos186.CFP.Bilu.Mahler
open Erdos186.CFP.Bilu.MinkowskiSecond
open Erdos186.CFP.Bilu.MinkowskiUpper


/-- The (integral) dyadic scale used in the packing argument.  We only use
it when `1 ≤ r`, so the integral logarithm is nonnegative. -/
noncomputable def dyadicNatFloor (r : ℝ) : ℕ :=
  2 ^ (Int.log 2 r).toNat

theorem intLog_nonneg_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    0 ≤ Int.log 2 r := by
  have h := Int.log_mono_right (b := 2) (show (0 : ℝ) < 1 by norm_num) hr
  norm_num at h
  exact h

theorem coe_dyadicNatFloor_eq_dyadicFloor {r : ℝ} (hr : 1 ≤ r) :
    (dyadicNatFloor r : ℝ) = dyadicFloor r := by
  rw [dyadicNatFloor, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
    Int.toNat_of_nonneg (intLog_nonneg_of_one_le hr)]
  rfl

theorem dyadicNatFloor_pos {r : ℝ} : 0 < dyadicNatFloor r := by
  exact pow_pos (by norm_num) _

theorem dyadicNatFloor_le {r : ℝ} (hr : 1 ≤ r) :
    (dyadicNatFloor r : ℝ) ≤ r := by
  rw [coe_dyadicNatFloor_eq_dyadicFloor hr]
  exact dyadicFloor_le (lt_of_lt_of_le zero_lt_one hr)

theorem two_mul_lt_dyadicNatFloor {r : ℝ} (hr : 1 ≤ r) :
    r < 2 * (dyadicNatFloor r : ℝ) := by
  rw [coe_dyadicNatFloor_eq_dyadicFloor hr]
  have h := half_lt_dyadicFloor (lt_of_lt_of_le zero_lt_one hr)
  linarith

theorem dyadicNatFloor_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    dyadicNatFloor a ≤ dyadicNatFloor b := by
  have hreal : (dyadicNatFloor a : ℝ) ≤ dyadicNatFloor b := by
    rw [coe_dyadicNatFloor_eq_dyadicFloor ha,
    coe_dyadicNatFloor_eq_dyadicFloor (ha.trans hab)]
    exact dyadicFloor_mono (lt_of_lt_of_le zero_lt_one ha) hab
  exact_mod_cast hreal

/-- Ordered integral dyadic floors divide in the expected direction. -/
theorem dyadicNatFloor_dvd {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    dyadicNatFloor a ∣ dyadicNatFloor b := by
  obtain ⟨q, _hq, hq⟩ :=
    exists_nat_mul_dyadicFloor_eq (a := a) (b := b)
      (lt_of_lt_of_le zero_lt_one ha) hab
  refine ⟨q, ?_⟩
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_mul, coe_dyadicNatFloor_eq_dyadicFloor ha,
    coe_dyadicNatFloor_eq_dyadicFloor (ha.trans hab)]
  simpa [mul_comm] using hq.symm

/-- The coordinate modulus for the `m`-th dilate of the unit ball. -/
noncomputable def dyadicModulus {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (m : ℕ) (i : Fin n) : ℕ :=
  4 * dyadicNatFloor ((m : ℝ) / successiveMinimum p i)

theorem dyadicModulus_pos {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ))
    (m : ℕ) (i : Fin n) : 0 < dyadicModulus p m i := by
  simp only [dyadicModulus]
  exact Nat.mul_pos (by norm_num) (dyadicNatFloor_pos)

theorem one_le_ratio_of_successiveMinimum_le {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) {m : ℕ}
    {i : Fin n} (hi : successiveMinimum p i ≤ m) :
    1 ≤ (m : ℝ) / successiveMinimum p i := by
  rw [le_div_iff₀ (successiveMinimum_pos p hp i)]
  simpa using hi

/-- Each dyadic modulus is large enough that dividing a difference of two
points of `m K` by that modulus is strictly below the corresponding
successive minimum. -/
theorem two_mul_cast_lt_dyadicModulus_mul_successiveMinimum {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) {m : ℕ}
    {i : Fin n} (hi : successiveMinimum p i ≤ m) :
    2 * (m : ℝ) <
      (dyadicModulus p m i : ℝ) * successiveMinimum p i := by
  have hr := two_mul_lt_dyadicNatFloor
    (one_le_ratio_of_successiveMinimum_le p hp hi)
  have hpos := successiveMinimum_pos p hp i
  have hr' := mul_lt_mul_of_pos_right hr hpos
  rw [dyadicModulus, Nat.cast_mul, Nat.cast_ofNat] at ⊢
  calc
    2 * (m : ℝ) = 2 * ((m : ℝ) / successiveMinimum p i * successiveMinimum p i) := by
      rw [div_mul_cancel₀ _ hpos.ne']
    _ < (4 * (dyadicNatFloor ((m : ℝ) / successiveMinimum p i) : ℝ)) *
          successiveMinimum p i := by
      nlinarith

theorem dyadicModulus_mul_successiveMinimum_le_four_mul {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) {m : ℕ} {i : Fin n}
    (hi : successiveMinimum p i ≤ m) :
    (dyadicModulus p m i : ℝ) * successiveMinimum p i ≤ 4 * m := by
  have hpos := successiveMinimum_pos p hp i
  rw [dyadicModulus, Nat.cast_mul, Nat.cast_ofNat]
  have h := dyadicNatFloor_le
    (one_le_ratio_of_successiveMinimum_le p hp hi)
  have h' := mul_le_mul_of_nonneg_right h hpos.le
  calc
    (4 * (dyadicNatFloor ((m : ℝ) / successiveMinimum p i) : ℝ)) *
          successiveMinimum p i ≤
        4 * ((m : ℝ) / successiveMinimum p i) * successiveMinimum p i := by
      nlinarith
    _ = 4 * (m : ℝ) := by
      rw [mul_assoc, div_mul_cancel₀ _ hpos.ne']

/-- Later coordinate moduli divide earlier ones.  This is precisely the
nesting which lets the last nonzero coordinate be divided out in the
residue-packing argument. -/
theorem dyadicModulus_dvd_of_le {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) {m : ℕ}
    {i j : Fin n} (hij : i ≤ j) (hj : successiveMinimum p j ≤ m) :
    dyadicModulus p m j ∣ dyadicModulus p m i := by
  have hmi : successiveMinimum p i ≤ m :=
    (successiveMinimum_mono p hij).trans hj
  apply Nat.mul_dvd_mul_left
  apply dyadicNatFloor_dvd
  · exact one_le_ratio_of_successiveMinimum_le p hp hj
  · apply div_le_div_of_nonneg_left (Nat.cast_nonneg m)
      (successiveMinimum_pos p hp i)
    exact successiveMinimum_mono p hij

/-- Integral points in a seminorm sublevel, used as the finite source of the
residue packing map. -/
def integralSublevel {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) (m : ℕ) : Type :=
  {c : IntegralPoint n // p (integralEmbed c) ≤ m}

/-- Coordinatewise reduction modulo the dyadic moduli. -/
noncomputable def residueMap {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (m : ℕ) :
    IntegralPoint n → ((i : Fin n) → ZMod (dyadicModulus p m i)) :=
  fun c i ↦ (c i : ZMod (dyadicModulus p m i))

theorem card_integralSublevel_le_of_residue_injective {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (m : ℕ)
    (hinj : Function.Injective
      (fun c : integralSublevel p m ↦ residueMap p m c.1)) :
    Nat.card (integralSublevel p m) ≤ ∏ i, dyadicModulus p m i := by
  letI : Fintype (integralSublevel p m) :=
    (finite_integralPoint_closedBall p hp m).fintype
  letI : ∀ i : Fin n, NeZero (dyadicModulus p m i) :=
    fun i ↦ ⟨Nat.ne_of_gt (dyadicModulus_pos p m i)⟩
  have hcard := Fintype.card_le_of_injective
    (f := fun c : integralSublevel p m ↦ residueMap p m c.1) hinj
  simpa [Nat.card_eq_fintype_card, residueMap, Fintype.card_pi, ZMod.card] using hcard

/-- The core packing assertion.  A collision modulo the nested dyadic
moduli gives, after division by its last nonzero coordinate modulus, a
strictly short nonzero integral point; the supplied flag condition rules
this out. -/
theorem residueMap_injective_of_strictShort {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (m : ℕ)
    (hm : ∀ i, successiveMinimum p i ≤ m)
    (hshort : ∀ (i : Fin n) (y : IntegralPoint n),
      p (integralEmbed y) < successiveMinimum p i →
        ∀ j, i ≤ j → y j = 0) :
    Function.Injective
      (fun c : integralSublevel p m ↦ residueMap p m c.1) := by
  intro c d hres
  apply Subtype.ext
  apply funext
  by_contra hne
  let s : Finset (Fin n) := Finset.univ.filter fun i ↦ c.1 i ≠ d.1 i
  have hs : s.Nonempty := by
    by_contra hs0
    apply hne
    intro i
    by_contra hi
    apply hs0
    exact ⟨i, by simp [s, hi]⟩
  let j : Fin n := s.max' hs
  have hjmem : j ∈ s := Finset.max'_mem s hs
  have hjne : c.1 j ≠ d.1 j := by simpa [s] using hjmem
  have hle : ∀ i, c.1 i ≠ d.1 i → i ≤ j := by
    intro i hi
    have himem : i ∈ s := by simp [s, hi]
    exact Finset.le_max' s i himem
  have hdiv : ∀ i, (dyadicModulus p m j : ℤ) ∣ d.1 i - c.1 i := by
    intro i
    by_cases hi : c.1 i = d.1 i
    · simp [hi]
    · have hij : i ≤ j := hle i hi
      have hres_i := congrFun hres i
      have hQi : (dyadicModulus p m i : ℤ) ∣ d.1 i - c.1 i := by
        apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp
        simpa [residueMap] using hres_i
      have hQ : dyadicModulus p m j ∣ dyadicModulus p m i :=
        dyadicModulus_dvd_of_le p hp hij (hm j)
      exact (Int.natCast_dvd_natCast.mpr hQ).trans hQi
  choose y hy using hdiv
  have hyj : y j ≠ 0 := by
    intro hy0
    have hzero : d.1 j - c.1 j = 0 := by simpa [hy j, hy0]
    exact hjne (sub_eq_zero.mp hzero).symm
  have heq : integralEmbed d.1 - integralEmbed c.1 =
      (dyadicModulus p m j : ℝ) • integralEmbed y := by
    ext i
    simp only [integralEmbed, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact_mod_cast hy i
  have hdiff : p (integralEmbed d.1 - integralEmbed c.1) ≤ 2 * m := by
    calc
      p (integralEmbed d.1 - integralEmbed c.1) ≤
          p (integralEmbed d.1) + p (integralEmbed c.1) :=
        map_sub_le_add p _ _
      _ ≤ 2 * m := by
        norm_num
        linarith [d.2, c.2]
  have hQpos : 0 < (dyadicModulus p m j : ℝ) := by
    exact_mod_cast dyadicModulus_pos p m j
  have hpy : p (integralEmbed y) < successiveMinimum p j := by
    rw [heq, map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hQpos.le] at hdiff
    have hlarge := two_mul_cast_lt_dyadicModulus_mul_successiveMinimum
      p hp (hm j)
    nlinarith
  have hz := hshort j y hpy j le_rfl
  exact hyj hz

/-- The dyadic packing count, already in the form that survives division by
`m^n` in the scaled-grid limit. -/
theorem cardinal_sublevel_mul_product_minima_le {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (m : ℕ)
    (hm : ∀ i, successiveMinimum p i ≤ m)
    (hshort : ∀ (i : Fin n) (y : IntegralPoint n),
      p (integralEmbed y) < successiveMinimum p i →
        ∀ j, i ≤ j → y j = 0) :
    (Nat.card (integralSublevel p m) : ℝ) * ∏ i, successiveMinimum p i ≤
      (4 : ℝ) ^ n * m ^ n := by
  have hinj := residueMap_injective_of_strictShort p hp m hm hshort
  have hcard := card_integralSublevel_le_of_residue_injective p hp m hinj
  have hcardR : (Nat.card (integralSublevel p m) : ℝ) ≤
      ∏ i, (dyadicModulus p m i : ℝ) := by
    exact_mod_cast hcard
  have hmins : 0 ≤ ∏ i, successiveMinimum p i :=
    Finset.prod_nonneg fun i _ ↦ (successiveMinimum_pos p hp i).le
  calc
    (Nat.card (integralSublevel p m) : ℝ) * ∏ i, successiveMinimum p i ≤
        (∏ i, (dyadicModulus p m i : ℝ)) * ∏ i, successiveMinimum p i :=
      mul_le_mul_of_nonneg_right hcardR hmins
    _ = ∏ i, ((dyadicModulus p m i : ℝ) * successiveMinimum p i) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ ∏ _ : Fin n, (4 : ℝ) * m := by
      apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg (by positivity)
          (successiveMinimum_pos p hp i).le
      · intro i _
        exact dyadicModulus_mul_successiveMinimum_le_four_mul p hp (hm i)
    _ = (4 : ℝ) ^ n * m ^ n := by
      rw [← mul_pow]
      simp

end Erdos186.CFP.Bilu.MinkowskiUpperCoarse
