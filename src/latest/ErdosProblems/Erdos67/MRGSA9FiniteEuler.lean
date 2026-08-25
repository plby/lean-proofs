import ErdosProblems.Erdos67.MRGSA9LowHigh
import ErdosProblems.Erdos67.MRMultiplicativeEuler

/-!
# Finite Euler products for the low factor in GS A.9

Because the small factor is supported on primes at most `y`, its complete
Dirichlet series is an exactly finite Euler product.  This is the rigorous
finite-product form needed for the inclusion--exclusion estimate (A.11).
-/

open scoped BigOperators LSeries.notation
open Filter

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67.MRMultiplicativeEuler

/-- The ordinary local Euler factor of `f` at `p`. -/
def gsA9LocalEulerFactor (f : ℕ → ℂ) (s : ℂ) (p : ℕ) : ℂ :=
  ∑' e : ℕ, f (p ^ e) * ((p : ℂ) ^ (-s)) ^ e

/-- A prime-band coefficient has the original local factor on primes in
the band and the constant local factor `1` off the band. -/
theorem localEulerFactor_primeBandCoefficient_eq_ite
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P : ℕ → Prop) [DecidablePred P]
    {p : ℕ} (hp : p.Prime) (s : ℂ) :
    (∑' e : ℕ, primeBandCoefficient f P (p ^ e) *
        ((p : ℂ) ^ (-s)) ^ e) =
      if P p then gsA9LocalEulerFactor f s p else 1 := by
  by_cases hpP : P p
  · rw [if_pos hpP]
    unfold gsA9LocalEulerFactor
    apply tsum_congr
    intro e
    by_cases he : e = 0
    · subst e
      simp [primeBandCoefficient, primeSupported_one P, hmul.1]
    · have hsupp : PrimeSupported P (p ^ e) := by
        refine ⟨pow_ne_zero e hp.ne_zero, ?_⟩
        intro q hq
        rw [Nat.primeFactors_prime_pow he hp] at hq
        have hqp : q = p := Finset.mem_singleton.mp hq
        simpa [hqp] using hpP
      rw [primeBandCoefficient_eq_of_supported f P hsupp]
  · rw [if_neg hpP]
    have hterm : ∀ e : ℕ,
        primeBandCoefficient f P (p ^ e) * ((p : ℂ) ^ (-s)) ^ e =
          if e = 0 then 1 else 0 := by
      intro e
      by_cases he : e = 0
      · subst e
        simp [primeBandCoefficient, primeSupported_one P, hmul.1]
      · have hnot : ¬ PrimeSupported P (p ^ e) := by
          intro hsupp
          apply hpP
          apply hsupp.2 p
          rw [Nat.primeFactors_prime_pow he hp]
          simp
        simp [primeBandCoefficient, hnot, he]
    simp_rw [hterm]
    rw [tsum_ite_eq 0]

/-- Exact finite Euler product for a multiplicative coefficient supported
on a predicate whose primes all lie below `y`. -/
theorem LSeries_primeBandCoefficient_eq_finiteEulerProduct
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] (y : ℕ)
    (hP : ∀ p, P p → p ≤ y)
    {s : ℂ} (hs : 1 < s.re) :
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
  have haBound : ∀ n, 0 < n → ‖a n‖ ≤ 1 :=
    fun n hn ↦ norm_primeBandCoefficient_le_one hbound P hn
  have hlim : Tendsto F atTop (nhds (LSeries a s)) :=
    tendsto_multiplicative_eulerProduct haMul haBound hs
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

/-- The undeleted low series is the product of all local factors through
`y`. -/
theorem LSeries_gsA9Low_eq_finiteEulerProduct
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (y : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (gsA9Low f y) s =
      ∏ p ∈ primesUpTo y, gsA9LocalEulerFactor f s p := by
  have hbase := LSeries_primeBandCoefficient_eq_finiteEulerProduct
    hmul hbound (fun p ↦ p ≤ y) y (fun _ h ↦ h) hs
  have hfilter :
      (primesUpTo y).filter (fun p ↦ p ≤ y) = primesUpTo y := by
    ext p
    simp only [Finset.mem_filter, mem_primesUpTo]
    tauto
  rw [hfilter] at hbase
  exact hbase

/-- The A.9 low deletion series is therefore the finite product over the
retained low primes. -/
theorem LSeries_gsA9LowDeletion_eq_finiteEulerProduct
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q] (y : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (gsA9LowDeletion f Q y) s =
      ∏ p ∈ primesUpTo y with ¬ Q p, gsA9LocalEulerFactor f s p := by
  have hbase := LSeries_primeBandCoefficient_eq_finiteEulerProduct
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

end Erdos67.MRHalaszBands
