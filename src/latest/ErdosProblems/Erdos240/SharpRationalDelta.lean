/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.IntegerValuedPolynomial
import ErdosProblems.Erdos240.DeltaPower
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Roots

/-!
# Sharp rational evaluation of powered Delta derivatives

This file supplies the rational-evaluation part of van der Poorten--Loxton's
sharp denominator lemma.  The integer-point derivative denominator is proved
in `IntegerValuedPolynomial`; the only new arithmetic input here is that

`k! | q^k * prod_{i < k} (z - i*q)`.

Prime by prime, a prime dividing `q` is supplied by `q^k`, while a prime
coprime to `q` turns the displayed arithmetic progression into a consecutive
product modulo the relevant prime power.
-/

noncomputable section

open scoped Polynomial

namespace Erdos240.SharpRationalDelta

open Finset Polynomial
open Erdos240Delta
open Erdos240.DeltaPower
open Erdos240.IntegerValuedPolynomial

private theorem prod_intModEq {s : Finset ℕ} {M : ℤ} {f g : ℕ → ℤ}
    (h : ∀ i ∈ s, f i ≡ g i [ZMOD M]) :
    (∏ i ∈ s, f i) ≡ ∏ i ∈ s, g i [ZMOD M] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [prod_insert ha, prod_insert ha]
      exact (h a (mem_insert_self _ _)).mul
        (ih fun i hi ↦ h i (mem_insert_of_mem hi))

/-- The elementary rational-binomial denominator lemma.  Notice that the
power of `q` is only `k`, after the `q^k` arising from evaluation of the
degree-`k` numerator has already been removed. -/
theorem factorial_dvd_q_pow_mul_descProgression
    (k q : ℕ) (z : ℤ) (_hq : q ≠ 0) :
    (k.factorial : ℤ) ∣
      (q : ℤ) ^ k * ∏ i ∈ Finset.range k, (z - (i : ℤ) * q) := by
  let T : ℕ :=
    ((q : ℤ) ^ k * ∏ i ∈ Finset.range k, (z - (i : ℤ) * q)).natAbs
  have hT : (k.factorial : ℤ) ∣
      (q : ℤ) ^ k * ∏ i ∈ Finset.range k, (z - (i : ℤ) * q) ↔
      k.factorial ∣ T := by
    simpa only [T, Int.natCast_dvd]
  rw [hT]
  by_cases hT0 : T = 0
  · simp [hT0]
  rw [← Nat.factorization_le_iff_dvd k.factorial_ne_zero hT0]
  intro p
  by_cases hp : p.Prime
  · let e := k.factorial.factorization p
    have he_le_k : e ≤ k := by
      exact (Nat.factorization_factorial_le_div_pred hp k).trans
        (Nat.div_le_self k (p - 1))
    apply (hp.pow_dvd_iff_le_factorization hT0).mp
    by_cases hpq : p ∣ q
    · have hpe_qk : p ^ e ∣ q ^ k :=
        (pow_dvd_pow p he_le_k).trans (pow_dvd_pow_of_dvd hpq k)
      have hqpow_abs : ((q : ℤ) ^ k).natAbs = q ^ k := by simp
      have hT_eq : T = q ^ k *
          (∏ i ∈ Finset.range k, (z - (i : ℤ) * q)).natAbs := by
        simp only [T, Int.natAbs_mul, hqpow_abs]
      rw [hT_eq]
      exact dvd_mul_of_dvd_left hpe_qk _
    · let M : ℕ := p ^ e
      have hcop : Nat.Coprime q M := by
        exact hp.coprime_pow_of_not_dvd hpq
      let a : ℤ := Nat.gcdA q M
      let b : ℤ := Nat.gcdB q M
      have hbezout : (1 : ℤ) = (q : ℤ) * a + (M : ℤ) * b := by
        have hg := Nat.gcd_eq_gcd_ab (x := q) (y := M)
        rw [hcop.gcd_eq_one] at hg
        norm_num only [Nat.cast_one] at hg
        simpa only [a, b] using hg
      have hqa : (q : ℤ) * a ≡ 1 [ZMOD (M : ℤ)] := by
        apply Int.modEq_iff_dvd.mpr
        refine ⟨b, ?_⟩
        rw [hbezout]
        ring
      have hfactor : ∀ i ∈ Finset.range k,
          z - (i : ℤ) * q ≡
            (q : ℤ) * (a * z - (i : ℤ)) [ZMOD (M : ℤ)] := by
        intro i _hi
        have hz := hqa.mul_right z
        have hiq : (i : ℤ) * q ≡ (i : ℤ) * q [ZMOD (M : ℤ)] :=
          Int.ModEq.rfl
        convert hz.symm.sub hiq using 1 <;> ring
      have hprod := prod_intModEq hfactor
      have hprod' :
          (∏ i ∈ Finset.range k, (z - (i : ℤ) * q)) ≡
            (q : ℤ) ^ k *
              ∏ i ∈ Finset.range k, (a * z - (i : ℤ)) [ZMOD (M : ℤ)] := by
        simpa only [Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_range] using hprod
      have hfac_dvd_asc : (k.factorial : ℤ) ∣
          ∏ i ∈ Finset.range k, (-a * z + (i : ℤ)) := by
        simpa using Nat.factorial_coe_dvd_prod k (-a * z)
      have hfac_dvd_desc : (k.factorial : ℤ) ∣
          ∏ i ∈ Finset.range k, (a * z - (i : ℤ)) := by
        obtain ⟨c, hc⟩ := hfac_dvd_asc
        refine ⟨(-1 : ℤ) ^ k * c, ?_⟩
        calc
          ∏ i ∈ Finset.range k, (a * z - (i : ℤ)) =
              ∏ i ∈ Finset.range k,
                ((-1 : ℤ) * (-a * z + (i : ℤ))) := by
            apply Finset.prod_congr rfl
            intro i _hi
            ring
          _ = (-1 : ℤ) ^ k *
                ∏ i ∈ Finset.range k, (-a * z + (i : ℤ)) := by
            rw [Finset.prod_mul_distrib]
            simp
          _ = (k.factorial : ℤ) * ((-1 : ℤ) ^ k * c) := by
            rw [hc]
            ring
      have hM_dvd_fac_nat : M ∣ k.factorial := by
        exact hp.pow_dvd_iff_le_factorization k.factorial_ne_zero |>.mpr le_rfl
      have hM_dvd_fac : (M : ℤ) ∣ (k.factorial : ℤ) := by exact_mod_cast hM_dvd_fac_nat
      have hM_dvd_rhs : (M : ℤ) ∣
          (q : ℤ) ^ k * ∏ i ∈ Finset.range k, (a * z - (i : ℤ)) :=
        dvd_mul_of_dvd_right (hM_dvd_fac.trans hfac_dvd_desc) _
      have hM_dvd_prod : (M : ℤ) ∣
          ∏ i ∈ Finset.range k, (z - (i : ℤ) * q) := by
        exact Int.modEq_zero_iff_dvd.mp
          (hprod'.trans hM_dvd_rhs.modEq_zero_int)
      have hM_dvd_T : M ∣ T := by
        have hM_dvd_prod_nat : M ∣
            (∏ i ∈ Finset.range k, (z - (i : ℤ) * q)).natAbs :=
          Int.natCast_dvd.mp hM_dvd_prod
        have hT_eq : T = q ^ k *
            (∏ i ∈ Finset.range k, (z - (i : ℤ) * q)).natAbs := by
          simp only [T, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
        rw [hT_eq]
        exact dvd_mul_of_dvd_right hM_dvd_prod_nat _
      exact hM_dvd_T
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- A falling-binomial polynomial of degree `k`, evaluated at `z/q`, has
denominator dividing `q^(2*k)`. -/
theorem exists_int_q_two_pow_mul_eval_fallingChoose
    (k q : ℕ) (z : ℤ) (hq : q ≠ 0) :
    ∃ w : ℤ,
      (q : ℚ) ^ (2 * k) *
          (IntegerValuedPolynomial.fallingChoose k).eval
            ((z : ℚ) / q) = (w : ℚ) := by
  obtain ⟨w, hw⟩ :=
    factorial_dvd_q_pow_mul_descProgression k q z hq
  refine ⟨w, ?_⟩
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hfacQ : (k.factorial : ℚ) ≠ 0 := by positivity
  have hwQ :
      (q : ℚ) ^ k *
          ∏ i ∈ Finset.range k, ((z : ℚ) - (i : ℚ) * q) =
        (k.factorial : ℚ) * (w : ℚ) := by
    exact_mod_cast hw
  rw [IntegerValuedPolynomial.fallingChoose_eq, Polynomial.eval_mul,
    Polynomial.eval_C,
    IntegerValuedPolynomial.descPochhammer_eq_prod_range,
    Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hprod :
      (∏ i ∈ Finset.range k, ((z : ℚ) / q - (i : ℚ))) =
        (∏ i ∈ Finset.range k, ((z : ℚ) - (i : ℚ) * q)) /
          (q : ℚ) ^ k := by
    calc
      (∏ i ∈ Finset.range k, ((z : ℚ) / q - (i : ℚ))) =
          ∏ i ∈ Finset.range k,
            (((z : ℚ) - (i : ℚ) * q) / q) := by
        apply Finset.prod_congr rfl
        intro i _hi
        field_simp
      _ = (∏ i ∈ Finset.range k, ((z : ℚ) - (i : ℚ) * q)) /
            (q : ℚ) ^ k := by
        rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
  rw [hprod]
  field_simp
  rw [show 2 * k = k + k by omega, pow_add]
  linear_combination (q : ℚ) ^ k * hwQ

theorem eval_fallingChoose_nat (n k : ℕ) :
    (IntegerValuedPolynomial.fallingChoose k).eval (n : ℚ) =
      (n.choose k : ℚ) := by
  rw [IntegerValuedPolynomial.fallingChoose]
  calc
    (Ring.choose (X : ℚ[X]) k).eval (n : ℚ) =
        Ring.choose (n : ℚ) k := by
      simpa using
        (Ring.map_choose (Polynomial.evalRingHom (n : ℚ))
          (X : ℚ[X]) k)
    _ = (n.choose k : ℚ) := Ring.choose_natCast n k

theorem natDegree_fallingChoose_le (k : ℕ) :
    (IntegerValuedPolynomial.fallingChoose k).natDegree ≤ k := by
  rw [IntegerValuedPolynomial.fallingChoose_eq,
    IntegerValuedPolynomial.descPochhammer_eq_prod_range]
  calc
    (C ((k.factorial : ℚ)⁻¹) *
        ∏ i ∈ Finset.range k, (X - C (i : ℚ))).natDegree ≤
        (C ((k.factorial : ℚ)⁻¹)).natDegree +
          (∏ i ∈ Finset.range k, (X - C (i : ℚ))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + ∑ i ∈ Finset.range k,
          (X - C (i : ℚ)).natDegree := by
      gcongr
      · simp
      · exact Polynomial.natDegree_prod_le _ _
    _ = k := by
      simp_rw [Polynomial.natDegree_X_sub_C]
      simp

/-- Newton expansion for an integer-valued rational polynomial.  The
coefficients are iterated forward differences of its integral values. -/
theorem exists_int_newtonExpansion {p : ℚ[X]} {d : ℕ}
    (hp : IsIntegerValued p) (hdeg : p.natDegree ≤ d) :
    ∃ c : ℕ → ℤ,
      p = ∑ k ∈ Finset.range (d + 1),
        C (c k : ℚ) * IntegerValuedPolynomial.fallingChoose k := by
  classical
  let a : ℕ → ℤ := fun n ↦ Classical.choose (hp (n : ℤ))
  have ha (n : ℕ) : p.eval (n : ℚ) = (a n : ℚ) := by
    exact Classical.choose_spec (hp (n : ℤ))
  let c : ℕ → ℤ := fun k ↦ (fwdDiff (1 : ℕ))^[k] a 0
  let N : ℚ[X] := ∑ k ∈ Finset.range (d + 1),
    C (c k : ℚ) * IntegerValuedPolynomial.fallingChoose k
  have hNdeg : N.natDegree ≤ d := by
    dsimp only [N]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    have hcdeg : (C (c k : ℚ)).natDegree ≤ 0 := by
      rw [Polynomial.natDegree_C]
    have hfdeg :
        (IntegerValuedPolynomial.fallingChoose k).natDegree ≤ d :=
      (natDegree_fallingChoose_le k).trans
        (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    exact Polynomial.natDegree_mul_le.trans (by
      simpa using Nat.add_le_add hcdeg hfdeg)
  have heval (n : Fin (d + 1)) :
      p.eval (n : ℚ) = N.eval (n : ℚ) := by
    rw [ha]
    have hn : (n : ℕ) ≤ d := by omega
    have hshift := shift_eq_sum_fwdDiff_iter (1 : ℕ) a (n : ℕ) 0
    simp only [zero_add, nsmul_eq_mul, Nat.mul_one] at hshift
    have hsum :
        (∑ k ∈ Finset.range ((n : ℕ) + 1),
            ((n : ℕ).choose k : ℚ) * (c k : ℚ)) =
          ∑ k ∈ Finset.range (d + 1),
            ((n : ℕ).choose k : ℚ) * (c k : ℚ) := by
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hn))
      intro k hkd hkn
      have hnk : (n : ℕ) < k := by
        exact Nat.lt_of_not_ge fun hle ↦ hkn (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      simp [Nat.choose_eq_zero_of_lt hnk]
    have hshiftQ :
        (a (n : ℕ) : ℚ) =
          ∑ k ∈ Finset.range ((n : ℕ) + 1),
            ((n : ℕ).choose k : ℚ) * (c k : ℚ) := by
      exact_mod_cast hshift
    rw [hshiftQ, hsum]
    dsimp only [N]
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [Polynomial.eval_mul, Polynomial.eval_C, eval_fallingChoose_nat]
    ring
  refine ⟨c, ?_⟩
  change p = N
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq p N
    (f := fun n : Fin (d + 1) ↦ (n : ℚ))
  · intro i j hij
    apply Fin.ext
    change (i.val : ℚ) = (j.val : ℚ) at hij
    exact_mod_cast hij
  · exact heval
  · simp only [Fintype.card_fin]
    omega

/-- Any integer-valued rational polynomial of degree at most `d` takes, at
`z/q`, a value whose denominator divides `q^(2*d)`. -/
theorem exists_int_q_two_pow_mul_eval_of_integerValued
    {p : ℚ[X]} {d q : ℕ} (z : ℤ)
    (hp : IsIntegerValued p) (hdeg : p.natDegree ≤ d) (hq : q ≠ 0) :
    ∃ w : ℤ,
      (q : ℚ) ^ (2 * d) * p.eval ((z : ℚ) / q) = (w : ℚ) := by
  classical
  obtain ⟨c, hc⟩ := exists_int_newtonExpansion hp hdeg
  choose w hw using fun k ↦
    exists_int_q_two_pow_mul_eval_fallingChoose k q z hq
  refine ⟨∑ k ∈ Finset.range (d + 1),
    c k * (q : ℤ) ^ (2 * (d - k)) * w k, ?_⟩
  rw [hc, Polynomial.eval_finsetSum, Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  have hkd : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hexp : 2 * d = 2 * (d - k) + 2 * k := by omega
  rw [hexp, pow_add]
  calc
    (q : ℚ) ^ (2 * (d - k)) * (q : ℚ) ^ (2 * k) *
          ((c k : ℚ) *
            (IntegerValuedPolynomial.fallingChoose k).eval
              ((z : ℚ) / q)) =
        (c k : ℚ) * (q : ℚ) ^ (2 * (d - k)) *
          ((q : ℚ) ^ (2 * k) *
            (IntegerValuedPolynomial.fallingChoose k).eval
              ((z : ℚ) / q)) := by ring
    _ = (c k : ℚ) * (q : ℚ) ^ (2 * (d - k)) * (w k : ℚ) := by
      rw [hw]

theorem natDegree_poweredDeltaHasse_le (h lambda m : ℕ) :
    (poweredDeltaHasse h lambda m).natDegree ≤ h * lambda := by
  rw [poweredDeltaHasse_eq]
  calc
    (C (((h.factorial : ℚ) ^ lambda)⁻¹) *
        (poweredHasseNumeratorInt h lambda m).map
          (Int.castRingHom ℚ)).natDegree ≤
        (C (((h.factorial : ℚ) ^ lambda)⁻¹)).natDegree +
          ((poweredHasseNumeratorInt h lambda m).map
            (Int.castRingHom ℚ)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ 0 + (h * lambda - m) := by
      gcongr
      · rw [Polynomial.natDegree_C]
      · exact Polynomial.natDegree_map_le.trans
          (natDegree_poweredHasseNumeratorInt_le h lambda m)
    _ ≤ h * lambda := by omega

/-- The sharp rational form of van der Poorten--Loxton's Lemma 1.  The lcm
exponent is the derivative order `m`, not the total degree `h*lambda`. -/
theorem exists_int_cleared_poweredDeltaHasse_lcm_int
    (h lambda m q : ℕ) (z : ℤ) (hq : q ≠ 0) :
    ∃ w : ℤ,
      (q : ℚ) ^ (2 * h * lambda) *
          (Nat.lcmUpto h : ℚ) ^ m *
          (poweredDeltaHasse h lambda m).eval ((z : ℚ) / q) = (w : ℚ) := by
  let p : ℚ[X] :=
    C ((Nat.lcmUpto h : ℚ) ^ m) * poweredDeltaHasse h lambda m
  have hp : IsIntegerValued p := by
    intro n
    obtain ⟨w, hw⟩ :=
      exists_int_lcmUpto_pow_mul_eval_delta_pow_hasse h lambda m n
    refine ⟨w, ?_⟩
    simpa only [p, Polynomial.eval_mul, Polynomial.eval_C,
      poweredDeltaHasse, poweredDelta] using hw
  have hpdeg : p.natDegree ≤ h * lambda := by
    dsimp only [p]
    exact Polynomial.natDegree_mul_le.trans (by
      have hc : (C ((Nat.lcmUpto h : ℚ) ^ m)).natDegree ≤ 0 := by
        rw [Polynomial.natDegree_C]
      simpa using Nat.add_le_add hc
        (natDegree_poweredDeltaHasse_le h lambda m))
  obtain ⟨w, hw⟩ :=
    exists_int_q_two_pow_mul_eval_of_integerValued z hp hpdeg hq
  refine ⟨w, ?_⟩
  simpa only [p, Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_assoc,
    mul_assoc] using hw

/-- Positive-natural-argument version, matching the source statement. -/
theorem exists_int_cleared_poweredDeltaHasse_lcm
    (h lambda m q N : ℕ) (hq : 0 < q) (_hN : 0 < N) :
    ∃ w : ℤ,
      (q : ℚ) ^ (2 * h * lambda) *
          (Nat.lcmUpto h : ℚ) ^ m *
          (poweredDeltaHasse h lambda m).eval ((N : ℚ) / q) = (w : ℚ) := by
  simpa using exists_int_cleared_poweredDeltaHasse_lcm_int
    h lambda m q (N : ℤ) hq.ne'

#print axioms Erdos240.SharpRationalDelta.exists_int_cleared_poweredDeltaHasse_lcm

end Erdos240.SharpRationalDelta
