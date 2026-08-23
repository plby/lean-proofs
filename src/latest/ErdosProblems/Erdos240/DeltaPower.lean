/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.Delta
import ErdosProblems.Erdos240.LcmBound
import Mathlib.RingTheory.Binomial

/-!
# Powered normalized binomial polynomials

This module packages the powered polynomial and normalized derivatives used
in van der Poorten--Loxton's Lemma 1.  The explicitly named nonsharp theorem
below is only a fallback denominator clearing; it is not the source's sharp
`lcmUpto h ^ m` normalization.
-/

noncomputable section

open scoped Polynomial

namespace Erdos240.DeltaPower

open Finset Polynomial
open Erdos240Delta

/-- The source polynomial `Delta(X;h)^lambda`. -/
def poweredDelta (h lambda : ℕ) : ℚ[X] :=
  delta h ^ lambda

/-- Its normalized `m`th derivative, i.e. its `m`th Hasse derivative. -/
def poweredDeltaHasse (h lambda m : ℕ) : ℚ[X] :=
  hasseDeriv m (poweredDelta h lambda)

/-- The integral numerator of `Delta(X;h)^lambda`. -/
def poweredNumeratorInt (h lambda : ℕ) : ℤ[X] :=
  deltaNumeratorInt h ^ lambda

/-- The normalized derivative of the integral numerator. -/
def poweredHasseNumeratorInt (h lambda m : ℕ) : ℤ[X] :=
  hasseDeriv m (poweredNumeratorInt h lambda)

/-- A polynomial over `ℚ` has coefficientwise nonnegative coefficients. -/
def CoeffNonneg (p : ℚ[X]) : Prop :=
  ∀ n, 0 ≤ p.coeff n

namespace CoeffNonneg

theorem one : CoeffNonneg (1 : ℚ[X]) := by
  intro n
  simp only [coeff_one]
  split_ifs <;> norm_num

theorem C {a : ℚ} (ha : 0 ≤ a) : CoeffNonneg (Polynomial.C a) := by
  intro n
  rw [coeff_C]
  split_ifs <;> positivity

theorem X_add_C {a : ℚ} (ha : 0 ≤ a) :
    CoeffNonneg (X + Polynomial.C a) := by
  intro n
  simp only [coeff_add, coeff_X, coeff_C]
  split_ifs <;> positivity

theorem mul {p q : ℚ[X]} (hp : CoeffNonneg p) (hq : CoeffNonneg q) :
    CoeffNonneg (p * q) := by
  intro n
  rw [coeff_mul]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i.1) (hq i.2)

theorem pow {p : ℚ[X]} (hp : CoeffNonneg p) (k : ℕ) :
    CoeffNonneg (p ^ k) := by
  induction k with
  | zero => simpa using one
  | succ k ih => simpa [pow_succ] using mul ih hp

theorem hasseDeriv {p : ℚ[X]} (hp : CoeffNonneg p) (m : ℕ) :
    CoeffNonneg (Polynomial.hasseDeriv m p) := by
  intro n
  rw [hasseDeriv_coeff]
  exact mul_nonneg (by positivity) (hp (n + m))

theorem eval_nonneg {p : ℚ[X]} (hp : CoeffNonneg p) {x : ℚ}
    (hx : 0 ≤ x) : 0 ≤ p.eval x := by
  rw [eval_eq_sum]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp i) (pow_nonneg hx i)

theorem eval_mono {p : ℚ[X]} (hp : CoeffNonneg p) {x y : ℚ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [eval_eq_sum, eval_eq_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxy i) (hp i)

theorem taylor {p : ℚ[X]} (hp : CoeffNonneg p) {x : ℚ}
    (hx : 0 ≤ x) : CoeffNonneg (Polynomial.taylor x p) := by
  intro n
  rw [taylor_coeff]
  exact (hp.hasseDeriv n).eval_nonneg hx

theorem coeff_le_eval_one {p : ℚ[X]} (hp : CoeffNonneg p) (m : ℕ) :
    p.coeff m ≤ p.eval 1 := by
  rw [eval_eq_sum]
  simp only [one_pow, mul_one]
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (fun i _ ↦ hp i) hm
  · simp only [mem_support_iff, ne_eq, not_not] at hm
    rw [hm]
    exact Finset.sum_nonneg fun i _ ↦ hp i

end CoeffNonneg

theorem coeffNonneg_deltaNumerator (h : ℕ) :
    CoeffNonneg (deltaNumerator h) := by
  induction h with
  | zero => simpa [deltaNumerator] using CoeffNonneg.one
  | succ h ih =>
      rw [show h + 1 = Nat.succ h by rfl, deltaNumerator_succ]
      exact ih.mul (CoeffNonneg.X_add_C (by positivity))

theorem coeffNonneg_delta (h : ℕ) : CoeffNonneg (delta h) := by
  rw [delta]
  exact (CoeffNonneg.C (by positivity)).mul (coeffNonneg_deltaNumerator h)

theorem coeffNonneg_poweredDelta (h lambda : ℕ) :
    CoeffNonneg (poweredDelta h lambda) := by
  exact (coeffNonneg_delta h).pow lambda

theorem poweredDelta_eq (h lambda : ℕ) :
    poweredDelta h lambda =
      C (((h.factorial : ℚ) ^ lambda)⁻¹) *
        (poweredNumeratorInt h lambda).map (Int.castRingHom ℚ) := by
  simp only [poweredDelta, delta, mul_pow,
    poweredNumeratorInt, deltaNumerator, Polynomial.map_pow]
  rw [← map_pow, inv_pow]

/-- Normalized differentiation agrees with ordinary iterated
differentiation divided by `m!`. -/
theorem factorial_smul_poweredDeltaHasse (h lambda m : ℕ) :
    m.factorial • poweredDeltaHasse h lambda m =
      (derivative^[m]) (poweredDelta h lambda) := by
  simpa [poweredDeltaHasse] using
    congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℚ) m)
      (poweredDelta h lambda)

theorem factorial_mul_eval_poweredDeltaHasse
    (h lambda m : ℕ) (x : ℚ) :
    (m.factorial : ℚ) * (poweredDeltaHasse h lambda m).eval x =
      ((derivative^[m]) (poweredDelta h lambda)).eval x := by
  have he := congrArg (fun p : ℚ[X] ↦ p.eval x)
    (factorial_smul_poweredDeltaHasse h lambda m)
  simpa [nsmul_eq_mul] using he

theorem poweredDeltaHasse_eq (h lambda m : ℕ) :
    poweredDeltaHasse h lambda m =
      C (((h.factorial : ℚ) ^ lambda)⁻¹) *
        (poweredHasseNumeratorInt h lambda m).map (Int.castRingHom ℚ) := by
  rw [poweredDeltaHasse, poweredDelta_eq]
  ext n
  simp [poweredHasseNumeratorInt, hasseDeriv_coeff]
  ring

/-- The integral numerator after normalized differentiation has the expected
degree. -/
theorem natDegree_poweredHasseNumeratorInt_le (h lambda m : ℕ) :
    (poweredHasseNumeratorInt h lambda m).natDegree ≤ h * lambda - m := by
  calc
    (poweredHasseNumeratorInt h lambda m).natDegree
        ≤ (poweredNumeratorInt h lambda).natDegree - m :=
      Polynomial.natDegree_hasseDeriv_le _ _
    _ ≤ h * lambda - m := by
      gcongr
      simp [poweredNumeratorInt, natDegree_pow,
        natDegree_deltaNumeratorInt, Nat.mul_comm]

/-- Clearing the visible denominator `(h!)^lambda` and the evaluation
denominator produces an integer. -/
theorem exists_int_cleared_poweredDeltaHasse_factorial
    (h lambda m q : ℕ) (z : ℤ) (hq : q ≠ 0) :
    ∃ w : ℤ,
      (q : ℚ) ^ (h * lambda - m) *
          ((h.factorial : ℚ) ^ lambda) *
          (poweredDeltaHasse h lambda m).eval ((z : ℚ) / q) = (w : ℚ) := by
  obtain ⟨w, hw⟩ := exists_int_pow_mul_eval_map
    (poweredHasseNumeratorInt h lambda m) (h * lambda - m) q z
    (natDegree_poweredHasseNumeratorInt_le h lambda m) hq
  refine ⟨w, ?_⟩
  rw [poweredDeltaHasse_eq, Polynomial.eval_mul, Polynomial.eval_C]
  calc
    (q : ℚ) ^ (h * lambda - m) * ((h.factorial : ℚ) ^ lambda) *
          (((h.factorial : ℚ) ^ lambda)⁻¹ *
            ((poweredHasseNumeratorInt h lambda m).map
              (Int.castRingHom ℚ)).eval ((z : ℚ) / q)) =
        (q : ℚ) ^ (h * lambda - m) *
          ((poweredHasseNumeratorInt h lambda m).map
            (Int.castRingHom ℚ)).eval ((z : ℚ) / q) := by
      have hf : ((h.factorial : ℚ) ^ lambda) ≠ 0 := by positivity
      field_simp
    _ = (w : ℚ) := hw

/-- `h!` divides `lcm(1,...,h)^h`. -/
theorem factorial_dvd_lcmUpto_pow (h : ℕ) :
    h.factorial ∣ Nat.lcmUpto h ^ h := by
  rw [Nat.factorial_eq_prod_range_add_one]
  have hprod :
      (∏ i ∈ Finset.range h, (i + 1)) ∣
        ∏ _i ∈ Finset.range h, Nat.lcmUpto h := by
    exact Finset.prod_dvd_prod_of_dvd (fun i ↦ i + 1)
      (fun _i ↦ Nat.lcmUpto h) (fun i hi ↦ by
        exact Finset.dvd_lcm (s := Finset.Icc 1 h) (f := id) (by
          simp only [Finset.mem_Icc]
          exact ⟨Nat.succ_pos i,
            Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)⟩))
  simpa using hprod

/-! ## Sharp lcm normalization -/

/-- The denominator assigned to the `i`th factor of the falling binomial
polynomial.  The zero factor receives denominator `k`; every other factor
receives denominator `i`. -/
def fallingDenom (k i : ℕ) : ℕ :=
  if i = 0 then k else i

theorem fallingDenom_pos {k i : ℕ} (hk : 0 < k) (_hi : i < k) :
    0 < fallingDenom k i := by
  simp only [fallingDenom]
  split_ifs with h
  · exact hk
  · exact Nat.pos_of_ne_zero h

theorem fallingDenom_le {k i : ℕ} (hi : i < k) :
    fallingDenom k i ≤ k := by
  simp only [fallingDenom]
  split_ifs
  · exact le_rfl
  · exact hi.le

theorem fallingDenom_dvd_index (k i : ℕ) : fallingDenom k i ∣ i := by
  simp only [fallingDenom]
  split_ifs with h
  · simp [h]
  · exact dvd_refl i

theorem prod_fallingDenom (k : ℕ) :
    ∏ i ∈ Finset.range k, fallingDenom k i = k.factorial := by
  obtain rfl | k := k
  · simp [fallingDenom]
  · calc
      ∏ i ∈ Finset.range (k + 1), fallingDenom (k + 1) i =
          (∏ i ∈ Finset.Ico 0 1, fallingDenom (k + 1) i) *
            ∏ i ∈ Finset.Ico 1 (k + 1), fallingDenom (k + 1) i := by
        rw [← Nat.Ico_zero_eq_range]
        exact (Finset.prod_Ico_consecutive
          (fun i ↦ fallingDenom (k + 1) i)
          (m := 0) (n := 1) (k := k + 1) (by omega) (by omega)).symm
      _ = (k + 1) * ∏ i ∈ Finset.Ico 1 (k + 1), i := by
        rw [show (∏ i ∈ Finset.Ico 0 1, fallingDenom (k + 1) i) =
            k + 1 by simp [fallingDenom]]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        simp only [Finset.mem_Ico] at hi
        simp [fallingDenom, Nat.ne_of_gt hi.1]
      _ = (k + 1).factorial := by
        rw [Finset.prod_Ico_id_eq_factorial]
        simp [Nat.factorial_succ, mul_comm]

/-- The falling binomial polynomial `X choose k`, viewed in `ℚ[X]`. -/
def fallingChoose (k : ℕ) : ℚ[X] :=
  Ring.choose (X : ℚ[X]) k

/-- An integral factorization of `fallingChoose k (L*X)` when every
denominator assigned above divides `L`. -/
def scaledFallingChooseInt (L k : ℕ) : ℤ[X] :=
  ∏ i ∈ Finset.range k,
    (C ((L / fallingDenom k i : ℕ) : ℤ) * X -
      C ((i / fallingDenom k i : ℕ) : ℤ))

theorem fallingDenom_dvd_lcmUpto {h k i : ℕ}
    (hk : k ≤ h) (hi : i < k) :
    fallingDenom k i ∣ Nat.lcmUpto h := by
  apply Finset.dvd_lcm (s := Finset.Icc 1 h) (f := id)
  simp only [Finset.mem_Icc]
  exact ⟨fallingDenom_pos (Nat.zero_lt_of_lt hi) hi,
    (fallingDenom_le hi).trans hk⟩

theorem map_scaledFallingChooseInt_factor
    {L k i : ℕ} (hk : 0 < k) (hi : i < k)
    (hd : fallingDenom k i ∣ L) :
    (C ((L / fallingDenom k i : ℕ) : ℤ) * X -
        C ((i / fallingDenom k i : ℕ) : ℤ)).map
        (Int.castRingHom ℚ) =
      C ((fallingDenom k i : ℚ)⁻¹) *
        (C (L : ℚ) * X - C (i : ℚ)) := by
  let d := fallingDenom k i
  have hdpos : 0 < d := fallingDenom_pos hk hi
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hdi : d ∣ i := fallingDenom_dvd_index k i
  have hLdiv : ((L / d : ℕ) : ℚ) = (L : ℚ) / d := by
    apply (eq_div_iff hd0).2
    exact_mod_cast Nat.div_mul_cancel hd
  have hidiv : ((i / d : ℕ) : ℚ) = (i : ℚ) / d := by
    apply (eq_div_iff hd0).2
    exact_mod_cast Nat.div_mul_cancel hdi
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X]
  change C (((L / d : ℕ) : ℚ)) * X - C (((i / d : ℕ) : ℚ)) =
    C ((d : ℚ)⁻¹) * (C (L : ℚ) * X - C (i : ℚ))
  rw [hLdiv, hidiv]
  rw [mul_sub, ← mul_assoc, ← C_mul, ← C_mul]
  congr 2 <;> field_simp

theorem descPochhammer_eq_prod_range (k : ℕ) :
    descPochhammer ℚ k = ∏ i ∈ Finset.range k, (X - C (i : ℚ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [descPochhammer_succ_right, ih, Finset.prod_range_succ]
      rfl

theorem fallingChoose_eq (k : ℕ) :
    fallingChoose k =
      C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k := by
  rw [fallingChoose]
  have h := Ring.descPochhammer_eq_factorial_smul_choose
    (r := (X : ℚ[X])) k
  have hdesc : (descPochhammer ℤ k).smeval (X : ℚ[X]) =
      descPochhammer ℚ k := by
    clear h
    induction k with
    | zero => simp
    | succ k ih =>
        rw [descPochhammer_succ_right, descPochhammer_succ_right,
          Polynomial.smeval_mul, ih]
        congr 1
        simp only [Polynomial.smeval_sub, Polynomial.smeval_X,
          Polynomial.smeval_natCast, pow_one, pow_zero]
        simp
  rw [hdesc] at h
  calc
    Ring.choose (X : ℚ[X]) k =
        C ((k.factorial : ℚ)⁻¹) *
          (k.factorial • Ring.choose (X : ℚ[X]) k) := by
      rw [nsmul_eq_mul, ← C_eq_natCast, ← mul_assoc, ← C_mul,
        inv_mul_cancel₀ (by positivity), C_1, one_mul]
    _ = C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k := by rw [← h]

theorem fallingChoose_comp_eq (L k : ℕ) :
    (fallingChoose k).comp (C (L : ℚ) * X) =
      C ((k.factorial : ℚ)⁻¹) *
        ∏ i ∈ Finset.range k,
          (C (L : ℚ) * X - C (i : ℚ)) := by
  rw [fallingChoose_eq, Polynomial.mul_comp, Polynomial.C_comp,
    descPochhammer_eq_prod_range, Polynomial.prod_comp]
  apply congrArg (fun p : ℚ[X] ↦ C ((k.factorial : ℚ)⁻¹) * p)
  apply Finset.prod_congr rfl
  intro i hi
  simp

theorem map_scaledFallingChooseInt (h k : ℕ) (hk : k ≤ h) :
    (scaledFallingChooseInt (Nat.lcmUpto h) k).map (Int.castRingHom ℚ) =
      (fallingChoose k).comp (C (Nat.lcmUpto h : ℚ) * X) := by
  obtain rfl | k := k
  · simp [scaledFallingChooseInt, fallingChoose]
  · have hkpos : 0 < k + 1 := Nat.succ_pos k
    simp only [scaledFallingChooseInt, Polynomial.map_prod]
    rw [Finset.prod_congr rfl (fun i hi ↦
      map_scaledFallingChooseInt_factor hkpos (Finset.mem_range.mp hi)
        (fallingDenom_dvd_lcmUpto hk (Finset.mem_range.mp hi)))]
    rw [Finset.prod_mul_distrib]
    calc
      (∏ i ∈ Finset.range (k + 1), C ((fallingDenom (k + 1) i : ℚ)⁻¹)) *
            ∏ i ∈ Finset.range (k + 1),
              (C (Nat.lcmUpto h : ℚ) * X - C (i : ℚ)) =
          C (∏ i ∈ Finset.range (k + 1),
              ((fallingDenom (k + 1) i : ℚ)⁻¹)) *
            ∏ i ∈ Finset.range (k + 1),
              (C (Nat.lcmUpto h : ℚ) * X - C (i : ℚ)) := by
        rw [map_prod]
      _ = C (((k + 1).factorial : ℚ)⁻¹) *
            ∏ i ∈ Finset.range (k + 1),
              (C (Nat.lcmUpto h : ℚ) * X - C (i : ℚ)) := by
        rw [Finset.prod_inv_distrib]
        congr 2
        rw [← Nat.cast_prod, prod_fallingDenom]
      _ = (fallingChoose (k + 1)).comp
            (C (Nat.lcmUpto h : ℚ) * X) :=
        (fallingChoose_comp_eq (Nat.lcmUpto h) (k + 1)).symm

/-- A nonsharp factorial-free fallback.  Its lcm exponent is the total degree
`h*lambda`, rather than the derivative order `m`, so this theorem must not be
used as the source's Lemma 1 normalization. -/
theorem exists_int_cleared_poweredDeltaHasse_lcm_nonsharp
    (h lambda m q : ℕ) (z : ℤ) (hq : q ≠ 0) :
    ∃ w : ℤ,
      (q : ℚ) ^ (2 * h * lambda) *
          (Nat.lcmUpto h : ℚ) ^ (h * lambda) *
          (poweredDeltaHasse h lambda m).eval ((z : ℚ) / q) = (w : ℚ) := by
  obtain ⟨w, hw⟩ :=
    exists_int_cleared_poweredDeltaHasse_factorial h lambda m q z hq
  obtain ⟨a, ha⟩ := pow_dvd_pow_of_dvd (factorial_dvd_lcmUpto_pow h) lambda
  have ha' : Nat.lcmUpto h ^ (h * lambda) = h.factorial ^ lambda * a := by
    simpa [pow_mul] using ha
  have hdeg : h * lambda - m ≤ 2 * h * lambda := by
    calc
      h * lambda - m ≤ h * lambda := Nat.sub_le _ _
      _ ≤ h * lambda + h * lambda := Nat.le_add_right _ _
      _ = 2 * h * lambda := by ring
  obtain ⟨b, hb⟩ := pow_dvd_pow_of_dvd_of_le (dvd_refl q) hdeg
  refine ⟨(b * a : ℕ) * w, ?_⟩
  have hb' : (q : ℚ) ^ (2 * h * lambda) =
      (q : ℚ) ^ (h * lambda - m) * b := by exact_mod_cast hb
  have ha'' : (Nat.lcmUpto h : ℚ) ^ (h * lambda) =
      (h.factorial : ℚ) ^ lambda * a := by exact_mod_cast ha'
  rw [hb', ha'']
  calc
    ((q : ℚ) ^ (h * lambda - m) * b) *
          (((h.factorial : ℚ) ^ lambda) * a) *
          (poweredDeltaHasse h lambda m).eval ((z : ℚ) / q) =
        (b : ℚ) * (a : ℚ) *
          ((q : ℚ) ^ (h * lambda - m) *
            ((h.factorial : ℚ) ^ lambda) *
            (poweredDeltaHasse h lambda m).eval ((z : ℚ) / q)) := by ring
    _ = (b : ℚ) * (a : ℚ) * (w : ℚ) := by rw [hw]
    _ = ((((b * a : ℕ) : ℤ) * w : ℤ) : ℚ) := by
      push_cast
      ring

/-- The lcm denominator used above has a fixed-base exponential bound. -/
theorem lcmUpto_pow_degree_le (h lambda : ℕ) :
    Nat.lcmUpto h ^ (h * lambda) ≤ 512 ^ (h * h * lambda) := by
  calc
    Nat.lcmUpto h ^ (h * lambda) ≤ (512 ^ h) ^ (h * lambda) :=
      Nat.pow_le_pow_left (Erdos240.LcmBound.lcmUpto_le h) _
    _ = 512 ^ (h * h * lambda) := by ring

/-- A normalized derivative at a nonnegative integral argument is
nonnegative. -/
theorem poweredDeltaHasse_eval_nat_nonneg (h lambda m n : ℕ) :
    0 ≤ (poweredDeltaHasse h lambda m).eval (n : ℚ) := by
  exact ((coeffNonneg_poweredDelta h lambda).hasseDeriv m).eval_nonneg
    (by positivity)

/-- For a polynomial with nonnegative coefficients, a Taylor coefficient at
`n` is at most the value at `n+1`.  Applied here, this bounds every normalized
derivative by the next value of the powered Delta polynomial. -/
theorem poweredDeltaHasse_eval_nat_le_next (h lambda m n : ℕ) :
    (poweredDeltaHasse h lambda m).eval (n : ℚ) ≤
      (poweredDelta h lambda).eval ((n + 1 : ℕ) : ℚ) := by
  let p := poweredDelta h lambda
  calc
    (poweredDeltaHasse h lambda m).eval (n : ℚ) =
        (Polynomial.taylor (n : ℚ) p).coeff m := by
      rw [taylor_coeff]
      rfl
    _ ≤ (Polynomial.taylor (n : ℚ) p).eval 1 :=
      ((coeffNonneg_poweredDelta h lambda).taylor (by positivity)).coeff_le_eval_one m
    _ = p.eval ((n + 1 : ℕ) : ℚ) := by
      rw [Polynomial.taylor_eval]
      congr 1
      norm_num [add_comm]

/-- A power-of-two form of the source's elementary size estimate. -/
theorem poweredDeltaHasse_eval_nat_le_two_pow (h lambda m n : ℕ) :
    (poweredDeltaHasse h lambda m).eval (n : ℚ) ≤
      (2 : ℚ) ^ ((n + 1 + h) * lambda) := by
  calc
    (poweredDeltaHasse h lambda m).eval (n : ℚ) ≤
        (poweredDelta h lambda).eval ((n + 1 : ℕ) : ℚ) :=
      poweredDeltaHasse_eval_nat_le_next h lambda m n
    _ = (((n + 1 + h).choose h : ℕ) : ℚ) ^ lambda := by
      simp only [poweredDelta, Polynomial.eval_pow, eval_delta_nat]
    _ ≤ ((2 ^ (n + 1 + h) : ℕ) : ℚ) ^ lambda := by
      gcongr
      exact_mod_cast Nat.choose_le_two_pow (n + 1 + h) h
    _ = (2 : ℚ) ^ ((n + 1 + h) * lambda) := by
      norm_num [pow_mul]

/-- The exact fixed-base size shape from Lemma 1 at nonnegative integral
arguments.  The harmless assumption `0 < h` absorbs the Taylor shift by one. -/
theorem poweredDeltaHasse_eval_nat_le_four_pow
    (h lambda m n : ℕ) (hh : 0 < h) :
    (poweredDeltaHasse h lambda m).eval (n : ℚ) ≤
      (4 : ℚ) ^ (lambda * (n + h)) := by
  have hbase : n + 1 + h ≤ 2 * (n + h) := by omega
  have hexp : (n + 1 + h) * lambda ≤ 2 * (lambda * (n + h)) := by
    calc
      (n + 1 + h) * lambda ≤ (2 * (n + h)) * lambda :=
        Nat.mul_le_mul_right lambda hbase
      _ = 2 * (lambda * (n + h)) := by ring
  calc
    (poweredDeltaHasse h lambda m).eval (n : ℚ) ≤
        (2 : ℚ) ^ ((n + 1 + h) * lambda) :=
      poweredDeltaHasse_eval_nat_le_two_pow h lambda m n
    _ ≤ (2 : ℚ) ^ (2 * (lambda * (n + h))) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hexp
    _ = (4 : ℚ) ^ (lambda * (n + h)) := by
      rw [show (4 : ℚ) = 2 ^ 2 by norm_num, pow_mul]

/-- A rational-argument form convenient for the auxiliary construction: an
explicit natural upper bound for the argument gives the same exponential
bound as at that integer. -/
theorem poweredDeltaHasse_eval_le_four_pow_of_le_nat
    (h lambda m n : ℕ) (x : ℚ) (hh : 0 < h)
    (hx : 0 ≤ x) (hxn : x ≤ n) :
    |(poweredDeltaHasse h lambda m).eval x| ≤
      (4 : ℚ) ^ (lambda * (n + h)) := by
  have hp := (coeffNonneg_poweredDelta h lambda).hasseDeriv m
  have hnonneg : 0 ≤ (poweredDeltaHasse h lambda m).eval x := by
    simpa [poweredDeltaHasse] using hp.eval_nonneg hx
  rw [abs_of_nonneg hnonneg]
  have hmono : (poweredDeltaHasse h lambda m).eval x ≤
      (poweredDeltaHasse h lambda m).eval (n : ℚ) := by
    simpa [poweredDeltaHasse] using hp.eval_mono hx hxn
  exact hmono.trans
    (poweredDeltaHasse_eval_nat_le_four_pow h lambda m n hh)

/-- The `lcmUpto` power occurring in the sharp derivative normalization has
fixed-base exponential size. -/
theorem lcmUpto_pow_le (h m : ℕ) :
    Nat.lcmUpto h ^ m ≤ 4 ^ (h * m) := by
  calc
    Nat.lcmUpto h ^ m ≤ (4 ^ h) ^ m :=
      Nat.pow_le_pow_left (Erdos240.LcmBound.lcmUpto_le_four_pow h) _
    _ = 4 ^ (h * m) := by rw [pow_mul]

/-- The exact combined size estimate used in Lemma 2: the sharp derivative
denominator and the normalized derivative together cost only the displayed
base-four exponent. -/
theorem lcmUpto_pow_mul_abs_poweredDeltaHasse_eval_nat_le_four_pow
    (h lambda m n : ℕ) (hh : 0 < h) :
    (Nat.lcmUpto h : ℚ) ^ m *
        |(poweredDeltaHasse h lambda m).eval (n : ℚ)| ≤
      (4 : ℚ) ^ (h * m + lambda * (n + h)) := by
  have hlcm : (Nat.lcmUpto h : ℚ) ^ m ≤ (4 : ℚ) ^ (h * m) := by
    exact_mod_cast lcmUpto_pow_le h m
  have hp := (coeffNonneg_poweredDelta h lambda).hasseDeriv m
  have heval_nonneg :
      0 ≤ (poweredDeltaHasse h lambda m).eval (n : ℚ) := by
    simpa [poweredDeltaHasse] using hp.eval_nonneg (by positivity : (0 : ℚ) ≤ n)
  have heval : |(poweredDeltaHasse h lambda m).eval (n : ℚ)| ≤
      (4 : ℚ) ^ (lambda * (n + h)) := by
    rw [abs_of_nonneg heval_nonneg]
    exact poweredDeltaHasse_eval_nat_le_four_pow h lambda m n hh
  calc
    (Nat.lcmUpto h : ℚ) ^ m *
          |(poweredDeltaHasse h lambda m).eval (n : ℚ)| ≤
        (4 : ℚ) ^ (h * m) * (4 : ℚ) ^ (lambda * (n + h)) :=
      mul_le_mul hlcm heval (abs_nonneg _) (by positivity)
    _ = (4 : ℚ) ^ (h * m + lambda * (n + h)) := by rw [pow_add]

/-- Rational-argument variant of the combined Lemma 2 estimate. -/
theorem lcmUpto_pow_mul_abs_poweredDeltaHasse_eval_le_four_pow_of_le_nat
    (h lambda m n : ℕ) (x : ℚ) (hh : 0 < h)
    (hx : 0 ≤ x) (hxn : x ≤ n) :
    (Nat.lcmUpto h : ℚ) ^ m * |(poweredDeltaHasse h lambda m).eval x| ≤
      (4 : ℚ) ^ (h * m + lambda * (n + h)) := by
  have hlcm : (Nat.lcmUpto h : ℚ) ^ m ≤ (4 : ℚ) ^ (h * m) := by
    exact_mod_cast lcmUpto_pow_le h m
  have heval := poweredDeltaHasse_eval_le_four_pow_of_le_nat
    h lambda m n x hh hx hxn
  calc
    (Nat.lcmUpto h : ℚ) ^ m * |(poweredDeltaHasse h lambda m).eval x| ≤
        (4 : ℚ) ^ (h * m) * (4 : ℚ) ^ (lambda * (n + h)) :=
      mul_le_mul hlcm heval (abs_nonneg _) (by positivity)
    _ = (4 : ℚ) ^ (h * m + lambda * (n + h)) := by rw [pow_add]

#print axioms Erdos240.DeltaPower.exists_int_cleared_poweredDeltaHasse_lcm_nonsharp
#print axioms Erdos240.DeltaPower.map_scaledFallingChooseInt
#print axioms Erdos240.DeltaPower.poweredDeltaHasse_eval_nat_le_four_pow
#print axioms Erdos240.DeltaPower.poweredDeltaHasse_eval_le_four_pow_of_le_nat
#print axioms Erdos240.DeltaPower.lcmUpto_pow_mul_abs_poweredDeltaHasse_eval_nat_le_four_pow
#print axioms Erdos240.DeltaPower.lcmUpto_pow_mul_abs_poweredDeltaHasse_eval_le_four_pow_of_le_nat

end Erdos240.DeltaPower
