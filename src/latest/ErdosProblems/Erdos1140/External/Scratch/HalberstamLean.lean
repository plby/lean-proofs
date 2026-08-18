import Mathlib

/-!
A fully proved finite Euler-product layer toward the Halberstam--Richert
mean-value estimate used by Erdős--Tenenbaum.  The theorem proved here is the
Rankin/Euler-product bound with exact constant `1`.  Its missing factor
`1 / log x` is precisely the genuinely sieve-theoretic part of the classical
Halberstam--Richert lemma.
-/

open scoped BigOperators
open Filter Finset

namespace HalberstamScratch

/-- Divide an arithmetic weight by its argument.  The value at zero is `0`. -/
private noncomputable def recipWeight (h : ℕ → ℝ) (n : ℕ) : ℝ :=
  h n / (n : ℝ)

/-- Exact local Euler-factor estimate implied by the prime-power hypothesis. -/
theorem prime_power_local_mass
    (h : ℕ → ℝ) (p : ℕ) (lambda1 lambda2 : ℝ)
    (hp : Nat.Prime p)
    (hh_nonneg : ∀ n, 0 ≤ h n)
    (hh_one : h 1 = 1)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ j : ℕ,
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j) :
    Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖) ∧
      (∑' j : ℕ, ‖recipWeight h (p ^ j)‖) ≤
        1 + lambda1 / ((p : ℝ) - lambda2) := by
  let r : ℝ := lambda2 / (p : ℝ)
  let c : ℝ := lambda1 / (p : ℝ)
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hr_nonneg : 0 ≤ r := div_nonneg hlambda2 hpReal.le
  have hr_lt : r < 1 := by
    dsimp [r]
    exact (div_lt_one hpReal).2 (hlambda2_lt.trans_le hpTwo)
  have hc_nonneg : 0 ≤ c := div_nonneg hlambda1 hpReal.le
  have hbound : ∀ j : ℕ,
      ‖recipWeight h (p ^ (j + 1))‖ ≤ c * r ^ j := by
    intro j
    have hdenom_nonneg : 0 ≤ (((p ^ (j + 1) : ℕ) : ℝ)) := by positivity
    calc
      ‖recipWeight h (p ^ (j + 1))‖
          = h (p ^ (j + 1)) / ((p ^ (j + 1) : ℕ) : ℝ) := by
              rw [recipWeight, Real.norm_eq_abs, abs_of_nonneg]
              exact div_nonneg (hh_nonneg _) hdenom_nonneg
      _ ≤ (lambda1 * lambda2 ^ j) /
            ((p ^ (j + 1) : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right (hpow j) hdenom_nonneg
      _ = c * r ^ j := by
          rw [Nat.cast_pow, pow_succ]
          dsimp [c, r]
          have hpNe : (p : ℝ) ≠ 0 := ne_of_gt hpReal
          rw [div_pow]
          field_simp [hpNe]
  have hgeom : Summable (fun j : ℕ => r ^ j) :=
    summable_geometric_of_lt_one hr_nonneg hr_lt
  have hmajor : Summable (fun j : ℕ => c * r ^ j) := hgeom.mul_left c
  have htail : Summable (fun j : ℕ => ‖recipWeight h (p ^ (j + 1))‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hbound hmajor
  have hseries : Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖) := by
    apply (summable_nat_add_iff 1).mp
    simpa [Nat.add_comm] using htail
  refine ⟨hseries, ?_⟩
  rw [hseries.tsum_eq_zero_add]
  have hzero : ‖recipWeight h (p ^ 0)‖ = 1 := by
    simp [recipWeight, hh_one]
  rw [hzero]
  have htail_le :
      (∑' j : ℕ, ‖recipWeight h (p ^ (j + 1))‖) ≤
        ∑' j : ℕ, c * r ^ j :=
    htail.tsum_le_tsum hbound hmajor
  have hmajor_sum : (∑' j : ℕ, c * r ^ j) = c * (1 - r)⁻¹ :=
    ((hasSum_geometric_of_lt_one hr_nonneg hr_lt).mul_left c).tsum_eq
  calc
    1 + ∑' j : ℕ, ‖recipWeight h (p ^ (j + 1))‖
        ≤ 1 + ∑' j : ℕ, c * r ^ j := by linarith
    _ = 1 + c * (1 - r)⁻¹ := by rw [hmajor_sum]
    _ = 1 + lambda1 / ((p : ℝ) - lambda2) := by
      dsimp [c, r]
      have hpNe : (p : ℝ) ≠ 0 := ne_of_gt hpReal
      have hdiffPos : 0 < (p : ℝ) - lambda2 :=
        sub_pos.mpr (hlambda2_lt.trans_le hpTwo)
      field_simp [hpNe, ne_of_gt hdiffPos]

/-- Explicit constant in the linear prime-power mass estimate, using the
indexing `h(p^(j+1)) ≤ lambda1 * lambda2^j`. -/
noncomputable def explicitMassConstant (lambda1 lambda2 : ℝ) : ℝ :=
  lambda1 *
    (Real.log 4 +
      8 * lambda2 * Real.log 2 / (1 - lambda2 / 2) ^ 2)

lemma explicitMassConstant_nonneg {lambda1 lambda2 : ℝ}
    (h1 : 0 ≤ lambda1) (h2 : 0 ≤ lambda2) :
    0 ≤ explicitMassConstant lambda1 lambda2 := by
  unfold explicitMassConstant
  positivity

private lemma recipWeight_one {h : ℕ → ℝ} (h1 : h 1 = 1) :
    recipWeight h 1 = 1 := by
  simp [recipWeight, h1]

private lemma recipWeight_mul {h : ℕ → ℝ} (h0 : h 0 = 0)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    {m n : ℕ} (hmn : m.Coprime n) :
    recipWeight h (m * n) = recipWeight h m * recipWeight h n := by
  by_cases hm : m = 0
  · subst m
    have hn : n = 1 := by simpa using hmn
    subst n
    simp [recipWeight, h0]
  by_cases hn : n = 0
  · subst n
    have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hmn
    subst m
    simp [recipWeight, h0]
  simp only [recipWeight, hmul hmn, Nat.cast_mul]
  field_simp [hm, hn]

private lemma nat_Icc_mem_smoothNumbers {x n : ℕ}
    (hn : n ∈ Finset.Icc 1 x) : n ∈ (x + 1).smoothNumbers := by
  rcases Finset.mem_Icc.mp hn with ⟨hn1, hnx⟩
  rw [Nat.mem_smoothNumbers]
  refine ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn1), ?_⟩
  intro p hp
  exact (Nat.le_of_mem_primeFactorsList hp).trans_lt (Nat.lt_succ_of_le hnx)

/--
Exact finite Euler-product majorant.  This is the part of the classical
Halberstam--Richert lemma obtained from positivity, multiplicativity, and
unique factorization alone:

`sum_{n ≤ x} h(n) ≤ x * product_{p ≤ x} sum_j h(p^j)/p^j`.

The classical lemma strengthens `x` to `C * x / log x`; that strengthening
does not follow from the Euler-product expansion and requires an upper-bound
sieve/mean-value argument.
-/
theorem euler_rankin_mean_bound
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hloc : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖))
    (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, h n) ≤
      (x : ℝ) *
        ∏ p ∈ (x + 1).primesBelow,
          ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  let f : ℕ → ℝ := recipWeight h
  have hf1 : f 1 = 1 := recipWeight_one h1
  have hfmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    exact recipWeight_mul h0 hmul hmn
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf1 hfmul hloc (x + 1)
  let e : {n // n ∈ Finset.Icc 1 x} ↪ (x + 1).smoothNumbers :=
    { toFun := fun n => ⟨n, nat_Icc_mem_smoothNumbers n.property⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : (x + 1).smoothNumbers => (z : ℕ)) hab }
  let s : Finset ((x + 1).smoothNumbers) := (Finset.Icc 1 x).attach.map e
  have hs_sum :
      (∑ n ∈ Finset.Icc 1 x, f n) = ∑ n ∈ s, f n := by
    calc
      (∑ n ∈ Finset.Icc 1 x, f n) =
          ∑ n ∈ (Finset.Icc 1 x).attach, f n :=
        (Finset.sum_attach (Finset.Icc 1 x) f).symm
      _ = ∑ n ∈ s, f n := by
        change (∑ n ∈ (Finset.Icc 1 x).attach, f n) =
          ∑ n ∈ (Finset.Icc 1 x).attach.map e, f n
        rw [Finset.sum_map]
        rfl
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (hnonneg n) (Nat.cast_nonneg n)
  have hs_le :
      (∑ n ∈ Finset.Icc 1 x, f n) ≤
        ∑' n : (x + 1).smoothNumbers, f n := by
    rw [hs_sum]
    exact hEuler.1.of_norm.sum_le_tsum s
      (fun n _ => hf_nonneg n)
  calc
    (∑ n ∈ Finset.Icc 1 x, h n)
        ≤ ∑ n ∈ Finset.Icc 1 x, (x : ℝ) * f n := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hnpos : 0 < (n : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1)
          have hnx : (n : ℝ) ≤ (x : ℝ) := by
            exact_mod_cast (Finset.mem_Icc.mp hn).2
          change h n ≤ (x : ℝ) * (h n / (n : ℝ))
          rw [← mul_div_assoc, le_div_iff₀ hnpos]
          nlinarith [hnonneg n]
    _ = (x : ℝ) * ∑ n ∈ Finset.Icc 1 x, f n := by
          rw [Finset.mul_sum]
    _ ≤ (x : ℝ) * ∑' n : (x + 1).smoothNumbers, f n := by
          exact mul_le_mul_of_nonneg_left hs_le (Nat.cast_nonneg x)
    _ = (x : ℝ) *
        ∏ p ∈ (x + 1).primesBelow,
          ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
          rw [hEuler.2.tsum_eq]
          rfl

/-- The reciprocal partial sum is bounded by its finite Euler product. -/
theorem reciprocal_sum_le_euler_product
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hloc : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖))
    (x : ℕ) :
    (∑ n ∈ Finset.Icc 1 x, h n / (n : ℝ)) ≤
      ∏ p ∈ (x + 1).primesBelow,
        ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  let f : ℕ → ℝ := recipWeight h
  have hf1 : f 1 = 1 := recipWeight_one h1
  have hfmul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    exact recipWeight_mul h0 hmul hmn
  have hEuler :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf1 hfmul hloc (x + 1)
  let e : {n // n ∈ Finset.Icc 1 x} ↪ (x + 1).smoothNumbers :=
    { toFun := fun n => ⟨n, nat_Icc_mem_smoothNumbers n.property⟩
      inj' := by
        intro a b hab
        apply Subtype.ext
        exact congrArg (fun z : (x + 1).smoothNumbers => (z : ℕ)) hab }
  let s : Finset ((x + 1).smoothNumbers) := (Finset.Icc 1 x).attach.map e
  have hs_sum :
      (∑ n ∈ Finset.Icc 1 x, f n) = ∑ n ∈ s, f n := by
    calc
      (∑ n ∈ Finset.Icc 1 x, f n) =
          ∑ n ∈ (Finset.Icc 1 x).attach, f n :=
        (Finset.sum_attach (Finset.Icc 1 x) f).symm
      _ = ∑ n ∈ s, f n := by
        change (∑ n ∈ (Finset.Icc 1 x).attach, f n) =
          ∑ n ∈ (Finset.Icc 1 x).attach.map e, f n
        rw [Finset.sum_map]
        rfl
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact div_nonneg (hnonneg n) (Nat.cast_nonneg n)
  calc
    (∑ n ∈ Finset.Icc 1 x, h n / (n : ℝ))
        = ∑ n ∈ Finset.Icc 1 x, f n := by rfl
    _ = ∑ n ∈ s, f n := hs_sum
    _ ≤ ∑' n : (x + 1).smoothNumbers, f n :=
      hEuler.1.of_norm.sum_le_tsum s (fun n _ => hf_nonneg n)
    _ = ∏ p ∈ (x + 1).primesBelow,
        ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
      rw [hEuler.2.tsum_eq]
      rfl

/-- The ordinary partial sum of a nonnegative arithmetic weight. -/
def partialSum (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, h n

/-- The reciprocal-weighted partial sum. -/
noncomputable def reciprocalPartialSum (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, h n / (n : ℝ)

/-- The logarithmically weighted partial sum. -/
noncomputable def logPartialSum (h : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, h n * Real.log (n : ℝ)

/--
The exact final summation step in the Halberstam--Richert proof.  A uniform
bound

`sum h(n) log n ≤ K N sum h(n)/n`

implies the crucial `N / log N` saving, with completely explicit constant
`K + 1`.  The extra `1` comes from bounding `log (N/n)` by `N/n`.
-/
theorem mean_le_of_log_moment
    (h : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ h n) (K : ℝ) (N : ℕ)
    (hN : 2 ≤ N)
    (hlog : logPartialSum h N ≤
      K * (N : ℝ) * reciprocalPartialSum h N) :
    partialSum h N ≤
      (K + 1) * (N : ℝ) / Real.log (N : ℝ) *
        reciprocalPartialSum h N := by
  have hNpos : 0 < (N : ℝ) := by positivity
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  have hrecip_nonneg : 0 ≤ reciprocalPartialSum h N := by
    unfold reciprocalPartialSum
    exact Finset.sum_nonneg fun n hn =>
      div_nonneg (hnonneg n) (Nat.cast_nonneg n)
  have hcomplement :
      (∑ n ∈ Finset.Icc 1 N,
          h n * (Real.log (N : ℝ) - Real.log (n : ℝ))) ≤
        (N : ℝ) * reciprocalPartialSum h N := by
    unfold reciprocalPartialSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro n hn
    have hnpos_nat : 0 < n :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
    have hratio_nonneg : 0 ≤ (N : ℝ) / (n : ℝ) :=
      div_nonneg hNpos.le hnpos.le
    have hlog_div :
        Real.log (N : ℝ) - Real.log (n : ℝ) =
          Real.log ((N : ℝ) / (n : ℝ)) := by
      rw [Real.log_div hNpos.ne' hnpos.ne']
    calc
      h n * (Real.log (N : ℝ) - Real.log (n : ℝ))
          = h n * Real.log ((N : ℝ) / (n : ℝ)) := by rw [hlog_div]
      _ ≤ h n * ((N : ℝ) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_self hratio_nonneg) (hnonneg n)
      _ = (N : ℝ) * (h n / (n : ℝ)) := by ring
  have hidentity :
      partialSum h N * Real.log (N : ℝ) =
        (∑ n ∈ Finset.Icc 1 N,
          h n * (Real.log (N : ℝ) - Real.log (n : ℝ))) +
          logPartialSum h N := by
    unfold partialSum logPartialSum
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hweighted :
      partialSum h N * Real.log (N : ℝ) ≤
        (K + 1) * (N : ℝ) * reciprocalPartialSum h N := by
    rw [hidentity]
    calc
      (∑ n ∈ Finset.Icc 1 N,
          h n * (Real.log (N : ℝ) - Real.log (n : ℝ))) +
          logPartialSum h N
          ≤ (N : ℝ) * reciprocalPartialSum h N +
              K * (N : ℝ) * reciprocalPartialSum h N :=
        add_le_add hcomplement hlog
      _ = (K + 1) * (N : ℝ) * reciprocalPartialSum h N := by ring
  rw [show
    (K + 1) * (N : ℝ) / Real.log (N : ℝ) * reciprocalPartialSum h N =
      ((K + 1) * (N : ℝ) * reciprocalPartialSum h N) /
        Real.log (N : ℝ) by ring]
  exact (le_div_iff₀ hlogNpos).2 hweighted

/--
The prime-power-mass-to-log-moment step, stated independently of the concrete
encoding of prime powers.  In the Halberstam--Richert proof, `W Q` is
`sum_{p^ν ≤ Q} h(p^ν) log(p^ν)`.  Unique factorization gives `hconv`, and the
Chebyshev/geometric calculation gives `hW`.  This lemma performs the remaining
finite summation with exact constant `K`.
-/
theorem log_moment_of_mass_convolution
    (h : ℕ → ℝ) (hnonneg : ∀ n, 0 ≤ h n)
    (W : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (N : ℕ)
    (hconv : logPartialSum h N ≤
      ∑ m ∈ Finset.Icc 1 N, h m * W (N / m))
    (hW : ∀ Q : ℕ, W Q ≤ K * (Q : ℝ)) :
    logPartialSum h N ≤
      K * (N : ℝ) * reciprocalPartialSum h N := by
  calc
    logPartialSum h N
        ≤ ∑ m ∈ Finset.Icc 1 N, h m * W (N / m) := hconv
    _ ≤ ∑ m ∈ Finset.Icc 1 N, h m * (K * ((N / m : ℕ) : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro m hm
      exact mul_le_mul_of_nonneg_left (hW (N / m)) (hnonneg m)
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
        K * (N : ℝ) * (h m / (m : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro m hm
      have hmpos_nat : 0 < m :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmpos_nat
      have hcastdiv : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) :=
        Nat.cast_div_le
      calc
        h m * (K * ((N / m : ℕ) : ℝ))
            ≤ h m * (K * ((N : ℝ) / (m : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hcastdiv hK) (hnonneg m)
        _ = K * (N : ℝ) * (h m / (m : ℝ)) := by ring
    _ = K * (N : ℝ) * reciprocalPartialSum h N := by
      unfold reciprocalPartialSum
      rw [Finset.mul_sum]

/--
Consumer-shaped explicit Halberstam--Richert theorem, reduced to the
logarithmic-moment estimate.  Once the standard prime-power mass calculation
provides `hlog`, the constant is exactly `K + 1` and the Euler product is the
one used in Erdős--Tenenbaum Lemma 1.
-/
theorem halberstam_richert_of_log_moment
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hloc : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖))
    (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : 2 ≤ N)
    (hlog : logPartialSum h N ≤
      K * (N : ℝ) * reciprocalPartialSum h N) :
    partialSum h N ≤
      (K + 1) * (N : ℝ) / Real.log (N : ℝ) *
        ∏ p ∈ (N + 1).primesBelow,
          ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  have hmean := mean_le_of_log_moment h hnonneg K N hN hlog
  have heuler : reciprocalPartialSum h N ≤
      ∏ p ∈ (N + 1).primesBelow,
        ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
    simpa [reciprocalPartialSum] using
      reciprocal_sum_le_euler_product h h0 h1 hmul hnonneg hloc N
  have hfactor_nonneg :
      0 ≤ (K + 1) * (N : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg
      (mul_nonneg (by linarith) (Nat.cast_nonneg N))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))
  exact hmean.trans (mul_le_mul_of_nonneg_left heuler hfactor_nonneg)

/--
Fully assembled explicit mean-value bound from the two concrete obligations
that remain in a prime-power implementation: the convolution inequality and
the linear prime-power mass bound.
-/
theorem halberstam_richert_of_mass_convolution
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (hloc : ∀ {p : ℕ}, p.Prime →
      Summable (fun j : ℕ => ‖recipWeight h (p ^ j)‖))
    (W : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K) (N : ℕ) (hN : 2 ≤ N)
    (hconv : logPartialSum h N ≤
      ∑ m ∈ Finset.Icc 1 N, h m * W (N / m))
    (hW : ∀ Q : ℕ, W Q ≤ K * (Q : ℝ)) :
    partialSum h N ≤
      (K + 1) * (N : ℝ) / Real.log (N : ℝ) *
        ∏ p ∈ (N + 1).primesBelow,
          ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply halberstam_richert_of_log_moment h h0 h1 hmul hnonneg hloc K hK N hN
  exact log_moment_of_mass_convolution h hnonneg W K hK N hconv hW

end HalberstamScratch

#print axioms HalberstamScratch.prime_power_local_mass
#print axioms HalberstamScratch.halberstam_richert_of_mass_convolution
