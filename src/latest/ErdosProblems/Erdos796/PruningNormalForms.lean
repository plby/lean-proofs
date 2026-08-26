import ErdosProblems.Erdos796.PruningArithmetic
import Mathlib.Data.Finset.Max

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Canonical arithmetic normal forms for pruning

This file isolates the exact elementary-number-theoretic normal form used by
the pruning argument.  The largest prime factor is chosen canonically, and the
two cofactor branches are derived without any asymptotic input.
-/

namespace Erdos796

namespace PruningNormalForms

open PruningArithmetic

/-- The largest prime factor of `n`, with the harmless default value `1` when
`n` has no prime factor. -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 1

/-- For `n > 1`, the canonical largest prime factor is a prime. -/
theorem largestPrimeFactor_prime {n : ℕ} (hn : 1 < n) :
    (largestPrimeFactor n).Prime := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  rw [largestPrimeFactor, dif_pos hne]
  exact Nat.prime_of_mem_primeFactors (Finset.max'_mem _ _)

/-- For `n > 1`, the canonical largest prime factor divides `n`. -/
theorem largestPrimeFactor_dvd {n : ℕ} (hn : 1 < n) :
    largestPrimeFactor n ∣ n := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  rw [largestPrimeFactor, dif_pos hne]
  exact Nat.dvd_of_mem_primeFactors (Finset.max'_mem _ _)

/-- Every prime divisor is at most the canonical largest prime factor. -/
theorem prime_dvd_le_largestPrimeFactor {n p : ℕ} (hn : 1 < n)
    (hp : p.Prime) (hpn : p ∣ n) : p ≤ largestPrimeFactor n := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn
  have hmem : p ∈ n.primeFactors := hp.mem_primeFactors hpn (by omega)
  rw [largestPrimeFactor, dif_pos hne]
  exact Finset.le_max' _ _ hmem

/-- Multiplying an integer with three large factors by a positive integer
preserves such a factorization.  The multiplier is absorbed into the first
factor. -/
theorem hasThreeLargeFactors_mul_right {Y n k : ℕ}
    (h : HasThreeLargeFactors Y n) (hk : 0 < k) :
    HasThreeLargeFactors Y (n * k) := by
  obtain ⟨u, v, w, hYu, hYv, hYw, hn⟩ := h
  have huk : u ≤ u * k := by
    have h1k : 1 ≤ k := by omega
    simpa using! Nat.mul_le_mul_left u h1k
  refine ⟨u * k, v, w, hYu.trans_le huk, hYv, hYw, ?_⟩
  rw [hn]
  ring

/-- The first cofactor branch: `t` is `Z`-smooth and is smaller than `Y⁴`. -/
def SmoothCofactorForm (Y Z t : ℕ) : Prop :=
  ZSmooth Z t ∧ t < Y ^ 4

/-- The second cofactor branch, with canonical `r = P⁺(t)` and
`s = t / r`. -/
def SplitCofactorForm (Y Z t : ℕ) : Prop :=
  let r := largestPrimeFactor t
  let s := t / r
  ¬ZSmooth Z t ∧
    r.Prime ∧ r ∣ t ∧ Z < r ∧ t = r * s ∧ s < Y ^ 4

/-- If the first canonical prime factor `q` is already above `Y`, a smooth
cofactor cannot reach `Y⁴` without producing three factors above `Y`. -/
theorem smooth_cofactor_lt_pow_four
    {Y Z a q t : ℕ} (hZ : 2 ≤ Z) (hZY : Z ≤ Y)
    (hq : Y < q) (ha : a = q * t)
    (hno : ¬HasThreeLargeFactors Y a) (hsmooth : ZSmooth Z t) :
    t < Y ^ 4 := by
  by_contra h
  have ht : Y ^ 4 ≤ t := Nat.le_of_not_gt h
  have hlarge : HasThreeLargeFactors Y (q * t) :=
    three_large_factors_of_large_prime_and_zSmooth hZ hZY hq hsmooth ht
  apply hno
  rw [ha]
  exact hlarge

/-- Exact canonical arithmetic classification used by the pruning argument.

Set `q = P⁺(a)` and `t = a/q`.  If `t` is `Z`-smooth, then `t < Y⁴`.
Otherwise set `r = P⁺(t)` and `s = t/r`; then `r` is prime, divides `t`,
is larger than `Z`, and `s < Y⁴`.  The only hypotheses are the two scale
relations, positivity of `a`, the assumption `q > Y`, and exclusion of a
factorization of `a` into three factors above `Y`.
-/
theorem canonical_pruning_normal_form
    {Y Z a : ℕ} (hZ : 2 ≤ Z) (hZY : Z ≤ Y) (ha1 : 1 < a)
    (hqY : Y < largestPrimeFactor a)
    (hno : ¬HasThreeLargeFactors Y a) :
    let q := largestPrimeFactor a
    let t := a / q
    q.Prime ∧ q ∣ a ∧ a = q * t ∧
      (SmoothCofactorForm Y Z t ∨ SplitCofactorForm Y Z t) := by
  let q := largestPrimeFactor a
  let t := a / q
  have hqprime : q.Prime := by
    dsimp [q]
    exact largestPrimeFactor_prime ha1
  have hqa : q ∣ a := by
    dsimp [q]
    exact largestPrimeFactor_dvd ha1
  have ha : a = q * t := by
    dsimp [t]
    rw [Nat.mul_comm, Nat.div_mul_cancel hqa]
  refine ⟨hqprime, hqa, ha, ?_⟩
  by_cases hsmooth : ZSmooth Z t
  · left
    exact ⟨hsmooth,
      smooth_cofactor_lt_pow_four hZ hZY hqY ha hno hsmooth⟩
  · right
    have htpos : 0 < t := by
      by_contra h
      have htzero : t = 0 := Nat.eq_zero_of_not_pos h
      rw [htzero, Nat.mul_zero] at ha
      omega
    have hnotsmooth :
        ∃ p : ℕ, ∃ _ : p.Prime, ∃ _ : p ∣ t, Z < p := by
      simpa only [ZSmooth, not_forall, not_le] using! hsmooth
    obtain ⟨p, hpprime, hpt, hZp⟩ := hnotsmooth
    have ht1 : 1 < t := by
      have hple : p ≤ t := Nat.le_of_dvd htpos hpt
      exact hpprime.one_lt.trans_le hple
    let r := largestPrimeFactor t
    let s := t / r
    have hrprime : r.Prime := by
      dsimp [r]
      exact largestPrimeFactor_prime ht1
    have hrt : r ∣ t := by
      dsimp [r]
      exact largestPrimeFactor_dvd ht1
    have hZr : Z < r := by
      have hpr : p ≤ r := by
        dsimp [r]
        exact prime_dvd_le_largestPrimeFactor ht1 hpprime hpt
      exact hZp.trans_le hpr
    have ht : t = r * s := by
      dsimp [s]
      rw [Nat.mul_comm, Nat.div_mul_cancel hrt]
    have hsdvd : s ∣ t := by
      exact ⟨r, by simpa [Nat.mul_comm] using! ht⟩
    have hslt : s < Y ^ 4 := by
      by_contra h
      have hslarge : Y ^ 4 ≤ s := Nat.le_of_not_gt h
      by_cases hYr : Y < r
      · have hYs : Y < s := by
          have hY : 2 ≤ Y := hZ.trans hZY
          have hpow : Y < Y ^ 4 := by
            simpa only [pow_one] using!
              (Nat.pow_lt_pow_right (by omega : 1 < Y)
                (by norm_num : 1 < 4))
          exact hpow.trans_le hslarge
        apply hno
        refine ⟨q, r, s, hqY, hYr, hYs, ?_⟩
        calc
          a = q * t := ha
          _ = q * (r * s) := congrArg (fun x => q * x) ht
          _ = q * r * s := by ring
      · have hrY : r ≤ Y := Nat.le_of_not_gt hYr
        have hsmoothY : YSmooth Y s := by
          intro ℓ hℓprime hℓs
          have hℓt : ℓ ∣ t := hℓs.trans hsdvd
          exact (prime_dvd_le_largestPrimeFactor ht1 hℓprime hℓt).trans hrY
        have hlarge : HasThreeLargeFactors Y (q * s) :=
          three_large_factors_of_large_prime_and_zSmooth
            (hZ.trans hZY) (le_refl Y) hqY hsmoothY hslarge
        have hrpos : 0 < r := hrprime.pos
        have hlarge' : HasThreeLargeFactors Y ((q * s) * r) :=
          hasThreeLargeFactors_mul_right hlarge hrpos
        apply hno
        have heq : a = (q * s) * r := by
          calc
            a = q * t := ha
            _ = q * (r * s) := congrArg (fun x => q * x) ht
            _ = (q * s) * r := by ring
        rw [heq]
        exact hlarge'
    exact ⟨hsmooth, hrprime, hrt, hZr, ht, hslt⟩

end PruningNormalForms

end Erdos796
