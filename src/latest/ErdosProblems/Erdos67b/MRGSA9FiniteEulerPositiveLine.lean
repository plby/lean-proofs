import ErdosProblems.Erdos67b.MRGSA9FiniteEuler

/-!
# Finite Euler products on the positive half-plane

The low factor in the Granville--Soundararajan A.10 contour is supported on
integers composed of a fixed finite set of primes.  Consequently its
Dirichlet series converges absolutely already on `re s > 0`, rather than only
on the generic half-plane `re s > 1`.  This file records that strengthened
summability and the corresponding finite Euler-product identity.
-/

open scoped BigOperators LSeries.notation
open Filter

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b.MRMultiplicativeEuler

/-- A prime-band coefficient supported on primes at most `y` has an
absolutely convergent L-series throughout the open positive half-plane. -/
theorem primeBandCoefficient_LSeriesSummable_of_pos_re
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] (y : ℕ)
    (hP : ∀ p, P p → p ≤ y)
    {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (primeBandCoefficient f P) s := by
  let a : ℕ → ℂ := primeBandCoefficient f P
  let b : ℕ → ℂ := multiplicativeLSeriesTerm a s
  have haMul : IsMultiplicativeOnPositiveNat a :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul P
  have haBound : ∀ n, 0 < n → ‖a n‖ ≤ 1 :=
    fun n hn ↦ norm_primeBandCoefficient_le_one hbound P hn
  have hbOne : b 1 = 1 := multiplicativeLSeriesTerm_one haMul s
  have hbMul : ∀ {m n : ℕ}, m.Coprime n → b (m * n) = b m * b n :=
    fun {m n} hmn ↦ multiplicativeLSeriesTerm_mul_of_coprime haMul s hmn
  have hlocal : ∀ {p : ℕ}, p.Prime →
      Summable (fun e : ℕ ↦ ‖b (p ^ e)‖) := by
    intro p hp
    let r : ℝ := (p : ℝ) ^ (-s.re)
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg p) _
    have hr1 : r < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
    have hgeom : Summable (fun e : ℕ ↦ r ^ e) := by
      apply summable_geometric_of_norm_lt_one
      simpa [Real.norm_eq_abs, abs_of_nonneg hr0]
    apply hgeom.of_nonneg_of_le (fun e ↦ norm_nonneg _)
    intro e
    dsimp only [b]
    rw [multiplicativeLSeriesTerm_prime_pow a s p e hp.pos,
      norm_mul, norm_pow]
    have hrEq : ‖(p : ℂ) ^ (-s)‖ = r := by
      rw [Complex.norm_natCast_cpow_of_pos hp.pos]
      rfl
    rw [hrEq]
    change ‖a (p ^ e)‖ * r ^ e ≤ r ^ e
    have hpowPos : 0 < p ^ e := pow_pos hp.pos e
    simpa using mul_le_mul_of_nonneg_right
      (haBound (p ^ e) hpowPos) (pow_nonneg hr0 e)
  have hsmooth : Summable
      (fun m : (y + 1).smoothNumbers ↦ ‖b m‖) :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hbOne hbMul hlocal (y + 1)).1
  have hindicator : Summable
      ((y + 1).smoothNumbers.indicator (fun n : ℕ ↦ ‖b n‖)) :=
    summable_subtype_iff_indicator.mp hsmooth
  have hsupport : ∀ n : ℕ,
      (y + 1).smoothNumbers.indicator (fun m : ℕ ↦ ‖b m‖) n = ‖b n‖ := by
    intro n
    by_cases hnSmooth : n ∈ (y + 1).smoothNumbers
    · simp [hnSmooth]
    · rw [Set.indicator_apply_eq_zero.mpr (fun hn ↦
        (hnSmooth hn).elim)]
      suffices a n = 0 by
        by_cases hn0 : n = 0
        · subst n
          simp [b, multiplicativeLSeriesTerm]
        · simp [b, multiplicativeLSeriesTerm, LSeries.term_of_ne_zero hn0,
            this]
      by_cases hn0 : n = 0
      · subst n
        simp [a, primeBandCoefficient, PrimeSupported]
      · by_contra ha0
        have hnSupp : PrimeSupported P n := by
          by_contra hnSupp
          apply ha0
          simp [a, primeBandCoefficient, hnSupp]
        apply hnSmooth
        rw [Nat.mem_smoothNumbers_iff_primeFactors_subset]
        refine ⟨hn0, ?_⟩
        intro p hpFactor
        rw [Nat.mem_primesBelow]
        exact ⟨Nat.lt_succ_of_le (hP p (hnSupp.2 p hpFactor)),
          Nat.prime_of_mem_primeFactors hpFactor⟩
  have hnorm : Summable (fun n : ℕ ↦ ‖b n‖) :=
    hindicator.congr hsupport
  exact hnorm.of_norm

/-- Exact finite Euler product on `re s > 0`. -/
theorem LSeries_primeBandCoefficient_eq_finiteEulerProduct_of_pos_re
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] (y : ℕ)
    (hP : ∀ p, P p → p ≤ y)
    {s : ℂ} (hs : 0 < s.re) :
    LSeries (primeBandCoefficient f P) s =
      ∏ p ∈ primesUpTo y with P p, gsA9LocalEulerFactor f s p := by
  let a : ℕ → ℂ := primeBandCoefficient f P
  let F : ℕ → ℂ := fun N ↦
    ∏ p ∈ N.primesBelow,
      ∑' e : ℕ, a (p ^ e) * ((p : ℂ) ^ (-s)) ^ e
  let E : ℂ := ∏ p ∈ primesUpTo y with P p,
    gsA9LocalEulerFactor f s p
  have haMul : IsMultiplicativeOnPositiveNat a :=
    primeBandCoefficient_isMultiplicativeOnPositiveNat hmul P
  have haSum : Summable
      (fun n ↦ ‖multiplicativeLSeriesTerm a s n‖) :=
    (primeBandCoefficient_LSeriesSummable_of_pos_re
      hmul hbound P y hP hs).norm
  have hlim : Tendsto F atTop (nhds (LSeries a s)) := by
    have hEuler := EulerProduct.eulerProduct
      (multiplicativeLSeriesTerm_one haMul s)
      (multiplicativeLSeriesTerm_mul_of_coprime haMul s)
      haSum (multiplicativeLSeriesTerm_zero a s)
    convert hEuler using 1
    · funext N
      apply Finset.prod_congr rfl
      intro p hp
      apply tsum_congr
      intro e
      exact (multiplicativeLSeriesTerm_prime_pow a s p e
        (Nat.Prime.pos (Nat.prime_of_mem_primesBelow hp))).symm
    · rfl
  have hevent : F =ᶠ[atTop] fun _ ↦ E := by
    filter_upwards [eventually_gt_atTop y] with N hyN
    have hset : N.primesBelow.filter P = (primesUpTo y).filter P := by
      ext p
      simp only [Finset.mem_filter, Nat.mem_primesBelow, mem_primesUpTo]
      constructor
      · rintro ⟨⟨hpN, hpprime⟩, hpP⟩
        exact ⟨⟨hpprime, hP p hpP⟩, hpP⟩
      · rintro ⟨⟨hpprime, hpy⟩, hpP⟩
        exact ⟨⟨hpy.trans_lt hyN, hpprime⟩, hpP⟩
    dsimp only [F, E, a]
    calc
      (∏ p ∈ N.primesBelow,
          ∑' e : ℕ, primeBandCoefficient f P (p ^ e) *
            ((p : ℂ) ^ (-s)) ^ e) =
        ∏ p ∈ N.primesBelow,
          if P p then gsA9LocalEulerFactor f s p else 1 := by
            apply Finset.prod_congr rfl
            intro p hpN
            exact localEulerFactor_primeBandCoefficient_eq_ite
              hmul P (Nat.prime_of_mem_primesBelow hpN) s
      _ = ∏ p ∈ N.primesBelow.filter P,
          gsA9LocalEulerFactor f s p := by
            rw [Finset.prod_filter]
      _ = ∏ p ∈ (primesUpTo y).filter P,
          gsA9LocalEulerFactor f s p := by rw [hset]
      _ = ∏ p ∈ primesUpTo y with P p,
          gsA9LocalEulerFactor f s p := rfl
  have hconst : Tendsto F atTop (nhds E) :=
    tendsto_const_nhds.congr' hevent.symm
  have := tendsto_nhds_unique hlim hconst
  simpa only [a, E] using this

/-- The undeleted low series on the positive half-plane. -/
theorem LSeries_gsA9Low_eq_finiteEulerProduct_of_pos_re
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA9Low f y) s =
      ∏ p ∈ primesUpTo y, gsA9LocalEulerFactor f s p := by
  have hbase := LSeries_primeBandCoefficient_eq_finiteEulerProduct_of_pos_re
    hmul hbound (fun p ↦ p ≤ y) y (fun _ h ↦ h) hs
  have hfilter :
      (primesUpTo y).filter (fun p ↦ p ≤ y) = primesUpTo y := by
    ext p
    simp only [Finset.mem_filter, mem_primesUpTo]
    tauto
  rw [hfilter] at hbase
  exact hbase

/-- The low-deletion series on the positive half-plane. -/
theorem LSeries_gsA9LowDeletion_eq_finiteEulerProduct_of_pos_re
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q] (y : ℕ)
    {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA9LowDeletion f Q y) s =
      ∏ p ∈ primesUpTo y with ¬ Q p, gsA9LocalEulerFactor f s p := by
  have hbase := LSeries_primeBandCoefficient_eq_finiteEulerProduct_of_pos_re
    hmul hbound (fun p ↦ p ≤ y ∧ ¬ Q p) y (fun _ h ↦ h.1) hs
  have hfilter :
      (primesUpTo y).filter (fun p ↦ p ≤ y ∧ ¬ Q p) =
        (primesUpTo y).filter (fun p ↦ ¬ Q p) := by
    ext p
    simp only [Finset.mem_filter, mem_primesUpTo]
    tauto
  rw [hfilter] at hbase
  exact hbase

end

end Erdos67b.MRHalaszBands
