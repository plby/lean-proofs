import ErdosProblems.Erdos135
import ErdosProblems.Erdos1081.Erdos1081Core

/-!
# An unconditional upper bound for values of `x² + 2y²`

Only the upper bound is needed for Erdős 659. We combine the elementary
inert-prime valuation obstruction, the Halberstam–Richert mean-value bound,
and the Euler product of the nonprincipal quadratic character modulo eight.
No Bernays asymptotic or class-group equidistribution is used.
-/

open Filter Finset Real
open scoped BigOperators Real

namespace Erdos659b.Counting

open Erdos135 (realZetaFactor complexZetaFactor complex_nat_cpow_neg_real
  norm_complexZetaFactor prime_rpow_neg_pos_le_half realZetaFactor_pos
  realZetaFactor_one_le realZetaFactor_le_two realZetaFactor_one_le_exp_mul
  norm_riemannZeta_real_le realZetaFactor_prod_le_zeta)

noncomputable def chi : DirichletCharacter ℂ 8 :=
  ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)

lemma chi_apply (n : ℕ) : chi n = (ZMod.χ₈' n : ℂ) := rfl

lemma chi_two : chi (2 : ℕ) = 0 := by
  rw [chi_apply, ZMod.χ₈'_nat_eq_if_mod_eight]
  norm_num

lemma chi_ne_one : chi ≠ 1 := by
  intro h
  have hh := congrArg (fun f : DirichletCharacter ℂ 8 => f (5 : ℕ)) h
  have hu : IsUnit ((5 : ℕ) : ZMod 8) := by decide
  rw [MulChar.one_apply hu, chi_apply, ZMod.χ₈'_nat_eq_if_mod_eight] at hh
  norm_num at hh

lemma exists_LSeries_bound : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ,
    1 < s → s ≤ 2 → ‖LSeries (fun n => chi n) (s : ℂ)‖ ≤ C := by
  have hcont : Continuous (fun s : ℝ => DirichletCharacter.LFunction chi (s : ℂ)) :=
    (DirichletCharacter.differentiable_LFunction chi_ne_one).continuous.comp
      Complex.continuous_ofReal
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro s hs hs2
  rw [← DirichletCharacter.LFunction_eq_LSeries chi (by simpa using hs)]
  exact (hC s ⟨hs.le, hs2⟩).trans (by linarith [le_abs_self C])

def Inert (p : ℕ) : Prop := p % 8 = 5 ∨ p % 8 = 7

instance (p : ℕ) : Decidable (Inert p) := inferInstanceAs (Decidable (_ ∨ _))

lemma prime_cases {p : ℕ} (hp : p.Prime) :
    p = 2 ∨ (p % 8 = 1 ∨ p % 8 = 3) ∨ Inert p := by
  by_cases h : p = 2
  · exact Or.inl h
  have ho := Nat.odd_iff.mp (hp.odd_of_ne_two h)
  have hr := Nat.mod_lt p (by decide : 0 < 8)
  unfold Inert
  omega

lemma chi_split {p : ℕ} (h : p % 8 = 1 ∨ p % 8 = 3) : chi p = 1 := by
  rw [chi_apply, ZMod.χ₈'_nat_eq_if_mod_eight]
  have ho : p % 2 ≠ 0 := by omega
  simp [ho, h]

lemma chi_inert {p : ℕ} (h : Inert p) : chi p = -1 := by
  rw [chi_apply, ZMod.χ₈'_nat_eq_if_mod_eight]
  unfold Inert at h
  have ho : p % 2 ≠ 0 := by omega
  have hs : ¬ (p % 8 = 1 ∨ p % 8 = 3) := by omega
  simp [ho, hs]

noncomputable def complexChiFactor (s : ℝ) (p : ℕ) : ℂ :=
  (1 - chi p * (p : ℂ) ^ (-(s : ℂ)))⁻¹

noncomputable def combinedFactor (s : ℝ) (p : ℕ) : ℝ :=
  ‖complexZetaFactor s p‖ * ‖complexChiFactor s p‖

lemma combinedFactor_split {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) (h : p % 8 = 1 ∨ p % 8 = 3) :
    combinedFactor s p = (realZetaFactor s p) ^ 2 := by
  rw [combinedFactor, complexChiFactor, chi_split h, one_mul]
  change ‖complexZetaFactor s p‖ * ‖complexZetaFactor s p‖ = _
  rw [norm_complexZetaFactor s hp, abs_of_pos (realZetaFactor_pos hs hp)]
  ring

lemma combinedFactor_two {s : ℝ} (hs : 1 ≤ s) :
    combinedFactor s 2 = realZetaFactor s 2 := by
  rw [combinedFactor, complexChiFactor, chi_two]
  simp only [zero_mul, sub_zero, inv_one, norm_one, mul_one]
  rw [norm_complexZetaFactor s Nat.prime_two,
    abs_of_pos (realZetaFactor_pos hs Nat.prime_two)]

lemma combinedFactor_inert {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) (h : Inert p) :
    combinedFactor s p = (1 - ((p : ℝ) ^ (-s)) ^ 2)⁻¹ := by
  let a : ℝ := (p : ℝ) ^ (-s)
  have ha := prime_rpow_neg_pos_le_half hs hp
  have hza : 0 < 1 - a := by dsimp [a]; linarith
  have hca : 0 < 1 + a := by dsimp [a]; linarith
  have hsq : 0 < 1 - a ^ 2 := by dsimp [a]; nlinarith
  rw [combinedFactor, complexChiFactor, chi_inert h,
    complex_nat_cpow_neg_real, norm_complexZetaFactor s hp]
  change |realZetaFactor s p| * ‖(1 - (-1 : ℂ) * (a : ℂ))⁻¹‖ = _
  rw [abs_of_pos (realZetaFactor_pos hs hp)]
  rw [neg_one_mul, sub_neg_eq_add, ← Complex.ofReal_one,
    ← Complex.ofReal_add, ← Complex.ofReal_inv, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr hca.le)]
  unfold realZetaFactor
  dsimp [a] at hza hca hsq ⊢
  field_simp [ne_of_gt hza, ne_of_gt hca, ne_of_gt hsq]
  ring

lemma combinedFactor_one_le {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) : 1 ≤ combinedFactor s p := by
  rcases prime_cases hp with rfl | h | h
  · rw [combinedFactor_two hs]
    exact realZetaFactor_one_le hs Nat.prime_two
  · rw [combinedFactor_split hs hp h]
    nlinarith [realZetaFactor_one_le hs hp]
  · rw [combinedFactor_inert hs hp h]
    have ha := prime_rpow_neg_pos_le_half hs hp
    exact (one_le_inv₀ (by nlinarith)).2 (by nlinarith)

lemma combinedFactor_prod_le {s : ℝ} (hs : 1 < s) (N : ℕ) :
    (∏ p ∈ N.primesBelow, combinedFactor s p) ≤
      ‖riemannZeta (s : ℂ) * LSeries (fun n => chi n) (s : ℂ)‖ := by
  let f : ℕ → NNReal := fun p =>
    ‖complexZetaFactor s p‖₊ * ‖complexChiFactor s p‖₊
  have hz := riemannZeta_eulerProduct_hasProd (s := (s : ℂ)) (by simpa using hs)
  have hL := DirichletCharacter.LSeries_eulerProduct_hasProd
    chi (s := (s : ℂ)) (by simpa using hs)
  have hmul := hz.mul hL
  have hnnPrime : HasProd (fun p : Nat.Primes => f p)
      ‖riemannZeta (s : ℂ) * LSeries (fun n => chi n) (s : ℂ)‖₊ := by
    have hcont : Continuous (nnnormHom.toMonoidHom : ℂ → NNReal) := by
      change Continuous fun z : ℂ => ‖z‖₊
      exact (continuous_nnnorm : Continuous fun z : ℂ => ‖z‖₊)
    have hmap := hmul.map nnnormHom.toMonoidHom hcont
    change HasProd (fun p : Nat.Primes =>
        ‖complexZetaFactor s p * complexChiFactor s p‖₊)
      ‖riemannZeta (s : ℂ) *
        LSeries (fun n => chi n) (s : ℂ)‖₊ at hmap
    simpa only [f, nnnorm_mul] using hmap
  have hnn : HasProd (fun n : ℕ => if n.Prime then f n else 1)
      ‖riemannZeta (s : ℂ) * LSeries (fun n => chi n) (s : ℂ)‖₊ :=
    (Nat.Primes.hasProd_iff_hasProd_ite f).mp hnnPrime
  have hle : (∏ p ∈ N.primesBelow, f p) ≤
      ‖riemannZeta (s : ℂ) * LSeries (fun n => chi n) (s : ℂ)‖₊ := by
    calc
      (∏ p ∈ N.primesBelow, f p) =
          ∏ p ∈ N.primesBelow, if p.Prime then f p else 1 := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [if_pos (Nat.prime_of_mem_primesBelow hp)]
      _ ≤ ‖riemannZeta (s : ℂ) *
          LSeries (fun n => chi n) (s : ℂ)‖₊ := by
        apply prod_le_hasProd _ _ hnn
        intro p _hp
        by_cases hp : p.Prime
        · rw [if_pos hp]
          change (1 : ℝ) ≤ combinedFactor s p
          exact combinedFactor_one_le (le_of_lt hs) hp
        · simp [hp]
  have hle' : ((↑(∏ p ∈ N.primesBelow, f p) : ℝ) ≤
      (↑‖riemannZeta (s : ℂ) *
        LSeries (fun n => chi n) (s : ℂ)‖₊ : ℝ)) :=
    NNReal.coe_le_coe.mpr hle
  simpa only [f, combinedFactor, NNReal.coe_prod, NNReal.coe_mul,
    coe_nnnorm] using hle'

noncomputable def goodFactor (s : ℝ) (p : ℕ) : ℝ :=
  if Inert p then 1 else realZetaFactor s p

lemma goodFactor_one_le {s : ℝ} (hs : 1 ≤ s) {p : ℕ} (hp : p.Prime) :
    1 ≤ goodFactor s p := by
  unfold goodFactor
  split_ifs
  · exact le_rfl
  · exact realZetaFactor_one_le hs hp

lemma goodFactor_two_le {s : ℝ} (hs : 1 ≤ s) :
    goodFactor s 2 ≤ 2 := by
  rw [goodFactor, if_neg (by norm_num [Inert])]
  exact realZetaFactor_le_two hs Nat.prime_two

lemma goodFactor_sq_le_combined {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    (goodFactor s p) ^ 2 ≤ combinedFactor s p := by
  rcases prime_cases hp with htwo | hmod | hmod
  · exact (hp2 htwo).elim
  · rw [goodFactor, if_neg (by unfold Inert; omega), combinedFactor_split hs hp hmod]
  · rw [goodFactor, if_pos hmod]
    simpa using combinedFactor_one_le hs hp

lemma goodFactor_prod_sq_le_four_combined {s : ℝ} (hs : 1 ≤ s) (N : ℕ) :
    (∏ p ∈ N.primesBelow, goodFactor s p) ^ 2 ≤
      4 * ∏ p ∈ N.primesBelow, combinedFactor s p := by
  classical
  let S := N.primesBelow
  let R := S.erase 2
  have hgood0 (p : ℕ) (hp : p ∈ S) : 0 ≤ goodFactor s p :=
    (goodFactor_one_le hs (Nat.prime_of_mem_primesBelow hp)).trans' zero_le_one
  have hrest0 : 0 ≤ ∏ p ∈ R, goodFactor s p := by
    exact Finset.prod_nonneg fun p hp => hgood0 p (by
      dsimp [R] at hp
      exact Finset.mem_of_mem_erase hp)
  have hfull_le : (∏ p ∈ S, goodFactor s p) ≤
      2 * ∏ p ∈ R, goodFactor s p := by
    by_cases h2 : 2 ∈ S
    · rw [← Finset.mul_prod_erase _ _ h2]
      exact mul_le_mul_of_nonneg_right (goodFactor_two_le hs) hrest0
    · have hRS : R = S := Finset.erase_eq_of_notMem h2
      rw [hRS]
      nlinarith [show 0 ≤ ∏ p ∈ S, goodFactor s p from
        Finset.prod_nonneg fun p hp => hgood0 p hp]
  have hrest_sq : (∏ p ∈ R, goodFactor s p) ^ 2 ≤
      ∏ p ∈ R, combinedFactor s p := by
    rw [← Finset.prod_pow]
    exact Finset.prod_le_prod
      (fun p hp => by positivity)
      (fun p hp => by
        have hp' : p ∈ S := by
          dsimp [R] at hp
          exact Finset.mem_of_mem_erase hp
        exact goodFactor_sq_le_combined hs
          (Nat.prime_of_mem_primesBelow hp')
          (by
            dsimp [R] at hp
            exact Finset.ne_of_mem_erase hp))
  have hcombined_sub : (∏ p ∈ R, combinedFactor s p) ≤
      ∏ p ∈ S, combinedFactor s p := by
    by_cases h2 : 2 ∈ S
    · rw [← Finset.mul_prod_erase _ _ h2]
      exact le_mul_of_one_le_left
        (Finset.prod_nonneg fun p hp => by
          exact (combinedFactor_one_le hs
            (Nat.prime_of_mem_primesBelow (by
              dsimp [R] at hp
              exact Finset.mem_of_mem_erase hp))).trans' zero_le_one)
        (combinedFactor_one_le hs Nat.prime_two)
    · rw [show R = S from Finset.erase_eq_of_notMem h2]
  calc
    (∏ p ∈ N.primesBelow, goodFactor s p) ^ 2 =
        (∏ p ∈ S, goodFactor s p) ^ 2 := by rfl
    _ ≤ (2 * ∏ p ∈ R, goodFactor s p) ^ 2 :=
      pow_le_pow_left₀ (Finset.prod_nonneg fun p hp => hgood0 p hp) hfull_le 2
    _ = 4 * (∏ p ∈ R, goodFactor s p) ^ 2 := by ring
    _ ≤ 4 * ∏ p ∈ R, combinedFactor s p := by gcongr
    _ ≤ 4 * ∏ p ∈ S, combinedFactor s p := by gcongr
    _ = 4 * ∏ p ∈ N.primesBelow, combinedFactor s p := by rfl

lemma goodFactor_one_le_exp_mul {s : ℝ} (hs : 1 ≤ s) {p : ℕ}
    (hp : p.Prime) :
    goodFactor 1 p ≤
      Real.exp ((s - 1) * Real.log p / (p - 1 : ℕ)) *
        goodFactor s p := by
  by_cases hmod : Inert p
  · rw [goodFactor, if_pos hmod, goodFactor, if_pos hmod, mul_one]
    apply Real.one_le_exp
    exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr hs)
        (Real.log_nonneg (by exact_mod_cast hp.one_le)))
      (by positivity)
  · rw [goodFactor, if_neg hmod, goodFactor, if_neg hmod]
    exact realZetaFactor_one_le_exp_mul hs hp

lemma goodFactor_one_prod_le_shift {s : ℝ} (hs : 1 ≤ s) (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow, goodFactor 1 p) ≤
      Real.exp ((s - 1) *
        BoundedGaps.Maynard.primeLogPredecessorSum N) *
        ∏ p ∈ (N + 1).primesBelow, goodFactor s p := by
  have hpoint (p : ℕ) (hp : p ∈ (N + 1).primesBelow) :=
    goodFactor_one_le_exp_mul hs (Nat.prime_of_mem_primesBelow hp)
  calc
    (∏ p ∈ (N + 1).primesBelow, goodFactor 1 p) ≤
        ∏ p ∈ (N + 1).primesBelow,
          (Real.exp ((s - 1) * Real.log p / (p - 1 : ℕ)) *
            goodFactor s p) := by
      exact Finset.prod_le_prod
        (fun p hp => by
          exact (goodFactor_one_le (by norm_num)
            (Nat.prime_of_mem_primesBelow hp)).trans' zero_le_one)
        hpoint
    _ = (∏ p ∈ (N + 1).primesBelow,
          Real.exp ((s - 1) * Real.log p / (p - 1 : ℕ))) *
        ∏ p ∈ (N + 1).primesBelow, goodFactor s p := by
      rw [Finset.prod_mul_distrib]
    _ = Real.exp (∑ p ∈ (N + 1).primesBelow,
          ((s - 1) * Real.log p / (p - 1 : ℕ))) *
        ∏ p ∈ (N + 1).primesBelow, goodFactor s p := by
      rw [Real.exp_sum]
    _ = Real.exp ((s - 1) *
          BoundedGaps.Maynard.primeLogPredecessorSum N) *
        ∏ p ∈ (N + 1).primesBelow, goodFactor s p := by
      congr 2
      rw [show (N + 1).primesBelow = Nat.primesLE N by rfl]
      unfold BoundedGaps.Maynard.primeLogPredecessorSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring


lemma exists_goodFactor_one_prod_le_sqrt_log :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (∏ p ∈ (N + 1).primesBelow, goodFactor 1 p) ≤
        C * Real.sqrt (Real.log (N : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ :=
    BoundedGaps.Maynard.exists_uniform_abs_primeLogPredecessorSum_sub_log
  obtain ⟨C, hCpos, hC⟩ := exists_LSeries_bound
  refine ⟨4 * Real.sqrt C * Real.exp (1 + |C₀|), by positivity, ?_⟩
  intro N hN
  let ell : ℝ := Real.log (N : ℝ)
  let s : ℝ := 1 + 1 / ell
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL1 : 1 ≤ ell := by
    dsimp [ell]
    rw [Real.le_log_iff_exp_le hNpos]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hN)
  have hLpos : 0 < ell := lt_of_lt_of_le zero_lt_one hL1
  have hs : 1 < s := by
    dsimp [s]
    have : 0 < 1 / ell := one_div_pos.mpr hLpos
    linarith
  have hmert :
      BoundedGaps.Maynard.primeLogPredecessorSum N ≤ ell + |C₀| := by
    have h := hC₀ N
    dsimp [ell]
    have hdiff := le_abs_self
      (BoundedGaps.Maynard.primeLogPredecessorSum N - Real.log (N : ℝ))
    have hCabs : C₀ ≤ |C₀| := le_abs_self C₀
    linarith
  have hexponent :
      (s - 1) * BoundedGaps.Maynard.primeLogPredecessorSum N ≤
        1 + |C₀| := by
    have habs : 0 ≤ |C₀| := abs_nonneg C₀
    dsimp [s]
    rw [add_sub_cancel_left]
    calc
      1 / ell * BoundedGaps.Maynard.primeLogPredecessorSum N =
          BoundedGaps.Maynard.primeLogPredecessorSum N / ell := by ring
      _ ≤ (1 + |C₀|) := by
        rw [div_le_iff₀ hLpos]
        nlinarith
  let P : ℝ := ∏ p ∈ (N + 1).primesBelow, goodFactor s p
  have hP0 : 0 ≤ P := by
    dsimp [P]
    exact Finset.prod_nonneg fun p hp =>
      (goodFactor_one_le (le_of_lt hs)
        (Nat.prime_of_mem_primesBelow hp)).trans' zero_le_one
  have hrecip : 1 / (s - 1) = ell := by
    dsimp [s]
    rw [add_sub_cancel_left]
    field_simp [ne_of_gt hLpos]
  have hs2 : s ≤ 2 := by
    dsimp [s]
    have : 1 / ell ≤ 1 := (div_le_one hLpos).2 hL1
    linarith
  have hcombined : (∏ p ∈ (N + 1).primesBelow, combinedFactor s p) ≤
      (1 + 1 / (s - 1)) * C := by
    calc
      _ ≤ ‖riemannZeta (s : ℂ) * LSeries (fun n => chi n) (s : ℂ)‖ :=
        combinedFactor_prod_le hs (N + 1)
      _ = ‖riemannZeta (s : ℂ)‖ * ‖LSeries (fun n => chi n) (s : ℂ)‖ := norm_mul _ _
      _ ≤ _ := mul_le_mul (norm_riemannZeta_real_le hs) (hC s hs hs2)
        (norm_nonneg _) (by positivity)
  have hPsq : P ^ 2 ≤ 4 * C * (1 + ell) := by
    calc
      P ^ 2 ≤ 4 * ∏ p ∈ (N + 1).primesBelow, combinedFactor s p := by
        simpa [P] using goodFactor_prod_sq_le_four_combined (le_of_lt hs) (N + 1)
      _ ≤ 4 * ((1 + 1 / (s - 1)) * C) :=
        mul_le_mul_of_nonneg_left hcombined (by norm_num)
      _ = 4 * C * (1 + ell) := by rw [hrecip]; ring
  have hP : P ≤ 4 * Real.sqrt C * Real.sqrt ell := by
    have hroot0 : 0 ≤ Real.sqrt ell := Real.sqrt_nonneg _
    have hrootSq : (Real.sqrt ell) ^ 2 = ell := Real.sq_sqrt hLpos.le
    have hCroot : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hCpos.le
    have hproduct : (Real.sqrt C * Real.sqrt ell) ^ 2 = C * ell := by
      rw [mul_pow, hCroot, hrootSq]
    have hCE : C ≤ C * ell := le_mul_of_one_le_right hCpos.le hL1
    have hR0 : 0 ≤ Real.sqrt C * Real.sqrt ell := by positivity
    have hbound : P ^ 2 ≤ (4 * (Real.sqrt C * Real.sqrt ell)) ^ 2 := by
      rw [mul_pow, hproduct]
      nlinarith only [hPsq, hCE]
    have := (sq_le_sq₀ hP0 (mul_nonneg (by norm_num) hR0)).mp hbound
    simpa only [mul_assoc] using this
  have hshift := goodFactor_one_prod_le_shift (le_of_lt hs) N
  calc
    (∏ p ∈ (N + 1).primesBelow, goodFactor 1 p) ≤
        Real.exp ((s - 1) *
          BoundedGaps.Maynard.primeLogPredecessorSum N) * P := by
      simpa [P] using hshift
    _ ≤ Real.exp (1 + |C₀|) * (4 * Real.sqrt C * Real.sqrt ell) := by
      exact mul_le_mul (Real.exp_le_exp.mpr hexponent) hP hP0
        (Real.exp_pos _).le
    _ = (4 * Real.sqrt C * Real.exp (1 + |C₀|)) *
        Real.sqrt (Real.log (N : ℝ)) := by
      dsimp [ell]
      ring

noncomputable def badFactor (p : ℕ) : ℝ :=
  if Inert p then (1 - ((p : ℝ)⁻¹) ^ 2)⁻¹ else 1

lemma badFactor_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ badFactor p := by
  unfold badFactor
  by_cases hmod : Inert p
  · rw [if_pos hmod]
    have ha := prime_rpow_neg_pos_le_half (s := 1) (by norm_num) hp
    have hprod : 0 ≤ (p : ℝ) ^ (-(1 : ℝ)) *
        (1 / 2 - (p : ℝ) ^ (-(1 : ℝ))) :=
      mul_nonneg ha.1.le (sub_nonneg.mpr ha.2)
    rw [show ((p : ℝ)⁻¹) = (p : ℝ) ^ (-(1 : ℝ)) by
      rw [Real.rpow_neg_one]]
    exact inv_nonneg.mpr (by nlinarith)
  · simp [hmod]

lemma badFactor_le_realZetaFactor_two {p : ℕ} (hp : p.Prime) :
    badFactor p ≤ realZetaFactor 2 p := by
  unfold badFactor
  by_cases hmod : Inert p
  · rw [if_pos hmod]
    unfold realZetaFactor
    rw [show ((p : ℝ) ^ (-(2 : ℝ))) = ((p : ℝ)⁻¹) ^ 2 by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]]
  · rw [if_neg hmod]
    exact realZetaFactor_one_le (by norm_num) hp

lemma badFactor_prod_le_two (N : ℕ) :
    (∏ p ∈ (N + 1).primesBelow, badFactor p) ≤ 2 := by
  calc
    (∏ p ∈ (N + 1).primesBelow, badFactor p) ≤
        ∏ p ∈ (N + 1).primesBelow, realZetaFactor 2 p := by
      exact Finset.prod_le_prod
        (fun _ hp => badFactor_nonneg (Nat.prime_of_mem_primesBelow hp))
        (fun p hp => badFactor_le_realZetaFactor_two
          (Nat.prime_of_mem_primesBelow hp))
    _ ≤ ‖riemannZeta ((2 : ℝ) : ℂ)‖ :=
      realZetaFactor_prod_le_zeta (by norm_num) (N + 1)
    _ ≤ 2 := by
      convert norm_riemannZeta_real_le (s := (2 : ℝ)) (by norm_num) using 1
      norm_num [div_eq_mul_inv]

noncomputable def obstructionPrimes (N : ℕ) : Finset ℕ :=
  (N + 1).primesBelow.filter Inert

lemma obstructionPrimes_prime {N p : ℕ} (hp : p ∈ obstructionPrimes N) : p.Prime :=
  Nat.prime_of_mem_primesBelow (Finset.mem_filter.mp hp).1

lemma parityEulerFactor {N p : ℕ} (hp : p ∈ (N + 1).primesBelow) :
    (∑' j : ℕ, Erdos1081.parityWeight (obstructionPrimes N) (p ^ j) /
      ((p ^ j : ℕ) : ℝ)) = badFactor p * goodFactor 1 p := by
  rw [Erdos1081.parityWeight_eulerFactor
    (fun _ h => obstructionPrimes_prime h) p (Nat.prime_of_mem_primesBelow hp)]
  by_cases h : Inert p <;>
    simp [obstructionPrimes, hp, h, badFactor, goodFactor, realZetaFactor, Real.rpow_neg_one]

lemma exists_parityEulerProduct_le : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
    (∏ p ∈ (N + 1).primesBelow,
      ∑' j : ℕ, Erdos1081.parityWeight (obstructionPrimes N) (p ^ j) /
        ((p ^ j : ℕ) : ℝ)) ≤ C * Real.sqrt (Real.log (N : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_goodFactor_one_prod_le_sqrt_log
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN
  calc
    _ = (∏ p ∈ (N + 1).primesBelow, badFactor p) *
        ∏ p ∈ (N + 1).primesBelow, goodFactor 1 p := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun _ hp => parityEulerFactor hp)
    _ ≤ 2 * (C * Real.sqrt (Real.log (N : ℝ))) := by
      apply mul_le_mul (badFactor_prod_le_two N) (hC N hN)
      · exact Finset.prod_nonneg fun p hp =>
          (goodFactor_one_le (by norm_num) (Nat.prime_of_mem_primesBelow hp)).trans' zero_le_one
      · norm_num
    _ = _ := by ring

lemma even_valuation_of_represented {p x y : ℕ}
    (hp : p.Prime) (hi : Inert p) (hpos : 0 < x ^ 2 + 2 * y ^ 2) :
    Even (padicValNat p (x ^ 2 + 2 * y ^ 2)) := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num [Inert] at hi
  have hns : Erdos1081.IsQuadraticObstruction 2 p := by
    change ¬ IsSquare (-2 : ZMod p)
    rw [ZMod.exists_sq_eq_neg_two_iff hp2]
    unfold Inert at hi
    omega
  exact Erdos1081.even_padicValNat_of_formAnisotropicAt hp
    (Erdos1081.formAnisotropicAt_of_not_isSquare_neg hp hns) hpos

noncomputable def values (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun n => ∃ x y : ℕ, n = x ^ 2 + 2 * y ^ 2)

open scoped Classical in
lemma values_subset_parity (N : ℕ) :
    values N ⊆ (Finset.Icc 1 N).filter (Erdos1081.ParityAdmissible (obstructionPrimes N)) := by
  classical
  intro n hn
  rcases Finset.mem_filter.mp hn with ⟨hn, x, y, rfl⟩
  refine Finset.mem_filter.mpr ⟨hn, ?_⟩
  intro p hp
  exact even_valuation_of_represented (obstructionPrimes_prime hp)
    (Finset.mem_filter.mp hp).2 (by have := (Finset.mem_Icc.mp hn).1; omega)

/-- The upper-bound half needed for the single quadratic form in Erdős 659. -/
theorem exists_count_le : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
    ((values N).card : ℝ) ≤ C * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_parityEulerProduct_le
  let H : ℝ := HalberstamScratch.explicitMassConstant 1 1 + 1
  have hH : 0 < H := by
    have := HalberstamScratch.explicitMassConstant_nonneg
      (lambda1 := (1 : ℝ)) (lambda2 := (1 : ℝ)) (by norm_num) (by norm_num)
    dsimp [H]
    linarith
  refine ⟨H * C, mul_pos hH hCpos, ?_⟩
  intro N hN
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsqrt : 0 < Real.sqrt (Real.log (N : ℝ)) := Real.sqrt_pos.mpr hlog
  have hsqrtSq := Real.sq_sqrt hlog.le
  calc
    ((values N).card : ℝ) ≤ (Erdos1081.parityAdmissibleCount (obstructionPrimes N) N : ℝ) := by
      exact_mod_cast Finset.card_le_card (values_subset_parity N)
    _ = ∑ n ∈ Finset.Icc 1 N, Erdos1081.parityWeight (obstructionPrimes N) n :=
      (Erdos1081.parityWeight_sum_eq_count _ _).symm
    _ ≤ H * (N : ℝ) / Real.log (N : ℝ) *
        ∏ p ∈ (N + 1).primesBelow,
          ∑' j : ℕ, Erdos1081.parityWeight (obstructionPrimes N) (p ^ j) /
            ((p ^ j : ℕ) : ℝ) :=
      Erdos1081.parityWeight_mean_le_euler _ (fun _ hp => obstructionPrimes_prime hp) N (by omega)
    _ ≤ H * (N : ℝ) / Real.log (N : ℝ) * (C * Real.sqrt (Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (hC N hN) (by positivity)
    _ = (H * C) * (N : ℝ) / Real.sqrt (Real.log (N : ℝ)) := by
      field_simp [ne_of_gt hlog, ne_of_gt hsqrt]
      rw [hsqrtSq]

#print axioms exists_count_le

end Erdos659b.Counting
