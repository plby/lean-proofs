/-
- https://www.erdosproblems.com/forum/thread/990#post-5312
- https://github.com/yuta0x89/ErdosProblems/blob/main/Erdos990.lean
-/

import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.Lagrange

/-!
## Erdős problem 990

This file formalizes the full argument for Erdős problem 990 from
`arXiv:2604.06609`, Section 5 (“A counterexample to sparse Erdős–Turán”).

The development is organized as follows:

1. a Vandermonde / Lagrange interpolation identity,
2. an exponential polynomial with a zero of order `N + 1`,
3. a logarithmic reparametrization producing a sparse polynomial,
4. an asymptotic estimate showing `M (sparsePoly N K) < 3` for large `K`,
5. the construction of an explicit counterexample family, and
6. the final contradiction to an absolute sparse Erdős--Turán type bound.

The statements are arranged to follow the paper closely while exposing
intermediate lemmas in a form convenient for Mathlib.
-/

set_option autoImplicit false

open scoped BigOperators Topology
open Polynomial

noncomputable section

namespace Erdos990

/-! ### Basic numerical invariants -/

/-- The number of nonzero coefficients of a polynomial. -/
def nu (f : ℂ[X]) : ℕ :=
  f.support.card

/-- The `ℓ¹`-sum of the coefficients. -/
def coeffL1 (f : ℂ[X]) : ℝ :=
  f.support.sum fun n => ‖f.coeff n‖

/-- The coefficient-growth parameter used in the paper. -/
def M (f : ℂ[X]) : ℝ :=
  coeffL1 f / Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

/-- Principal argument, normalized to the interval `[0, 2π)`. -/
def principalArg (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z

/-- Number of roots (counted with multiplicity) whose principal argument belongs to `I`. -/
def argRootCount (f : ℂ[X]) (I : Set ℝ) : ℕ :=
  by
    classical
    exact f.roots.countP (fun z : ℂ => principalArg z ∈ I)

/-- The uniform prediction for the number of roots of degree `d` inside `[α, β)`. -/
def expectedRootCount (d : ℕ) (α β : ℝ) : ℝ :=
  ((β - α) / (2 * Real.pi)) * (d : ℝ)

/-- The angular discrepancy appearing in the Erdős--Turán bound. -/
def angularDiscrepancy (f : ℂ[X]) (α β : ℝ) : ℝ :=
  |(argRootCount f (Set.Ico α β) : ℝ) - expectedRootCount f.natDegree α β|

/-- The sparse Erdős--Turán type statement disproved in the paper. -/
def SparseErdosTuranBound (C : ℝ) : Prop :=
  ∀ (f : ℂ[X]) {α β : ℝ},
    f.coeff 0 ≠ 0 →
    f.leadingCoeff ≠ 0 →
    0 ≤ α →
    α < β →
    β ≤ 2 * Real.pi →
    angularDiscrepancy f α β ≤ C * Real.sqrt ((nu f : ℝ) * Real.log (M f))

/-- On positive reals, the normalized principal argument is `0`. -/
theorem principalArg_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : principalArg (x : ℂ) = 0 := by
  unfold principalArg
  simp [Complex.arg_ofReal_of_nonneg hx]

/-- Abstract bridge from a positive real root of multiplicity `m` to an argument count. -/
theorem rootMultiplicity_le_argRootCount_of_positive_root
    {f : ℂ[X]} {x : ℝ} {I : Set ℝ}
    (hx : 0 < x) (hI : 0 ∈ I) :
    f.rootMultiplicity (x : ℂ) ≤ argRootCount f I := by
  classical
  rw [← Polynomial.count_roots (p := f) (a := (x : ℂ))]
  unfold argRootCount
  have h0I : principalArg (x : ℂ) ∈ I := by
    simpa [principalArg_ofReal_of_nonneg (le_of_lt hx)] using hI
  have hle :
      f.roots.filter ((x : ℂ) = ·) ≤
        f.roots.filter (fun z : ℂ => principalArg z ∈ I) := by
    exact Multiset.monotone_filter_right (s := f.roots) (fun z hz => by
      simpa [hz] using h0I)
  calc
    f.roots.count (x : ℂ) = (f.roots.filter ((x : ℂ) = ·)).card := by
      simpa using (Multiset.count_eq_card_filter_eq f.roots (x : ℂ))
    _ ≤ (f.roots.filter fun z : ℂ => principalArg z ∈ I).card := Multiset.card_le_card hle
    _ = f.roots.countP (fun z : ℂ => principalArg z ∈ I) := by
      symm
      exact Multiset.countP_eq_card_filter _ _

/-! ### Vandermonde identity -/

section Vandermonde

variable {K : Type*} [Field K] {r : ℕ}

/-- The signed Vandermonde denominator attached to the node `i`. -/
def vandermondeWeight (x : Fin r → K) (i : Fin r) : K :=
  (Finset.univ.erase i).prod fun j => (x i - x j)

/--
Paper lemma `p990:lem:vandermonde`.

The intended proof is to apply `Lagrange.coeff_eq_sum` to `P = X^n` on the node set
`Finset.univ`, and then simplify the coefficient of `X^(r-1)`.
-/
theorem vandermonde_identity
    (x : Fin r → K) (hx : Function.Injective x) {n : ℕ} (hn : n < r) :
    (∑ i : Fin r, x i ^ n / vandermondeWeight x i) =
      if n + 1 = r then (1 : K) else 0 := by
  have hvs : Set.InjOn x (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)) := by
    intro i _ j _ hij
    exact hx hij
  have hdeg : ((X : K[X]) ^ n).degree < ((Finset.univ : Finset (Fin r)).card : WithBot ℕ) := by
    simpa [Polynomial.degree_X_pow] using (show (n : WithBot ℕ) < (r : WithBot ℕ) from by
      exact_mod_cast hn)
  have hlag :
      ((X : K[X]) ^ n).coeff (r - 1) =
        ∑ i : Fin r, x i ^ n / vandermondeWeight x i := by
    simpa [vandermondeWeight] using
      (Lagrange.coeff_eq_sum (s := Finset.univ) (v := x) hvs
        (P := (X : K[X]) ^ n) hdeg)
  calc
    ∑ i : Fin r, x i ^ n / vandermondeWeight x i
        = ((X : K[X]) ^ n).coeff (r - 1) := by
            simpa using hlag.symm
    _ = if n + 1 = r then (1 : K) else 0 := by
      by_cases h : n + 1 = r
      · have : r - 1 = n := by omega
        simp [Polynomial.coeff_X_pow, this, h]
      · have : r - 1 ≠ n := by omega
        simp [Polynomial.coeff_X_pow, this, h]

/-- The vanishing range in the Vandermonde identity. -/
theorem vandermonde_identity_vanish
    (x : Fin r → K) (hx : Function.Injective x) {n : ℕ} (hn : n + 1 < r) :
    (∑ i : Fin r, x i ^ n / vandermondeWeight x i) = 0 := by
  have hn' : n < r := by omega
  rw [vandermonde_identity x hx hn']
  simp [Nat.ne_of_lt hn]

/-- The top derivative moment in the Vandermonde identity. -/
theorem vandermonde_identity_top
    (x : Fin r → K) (hx : Function.Injective x) (hr : 0 < r) :
    (∑ i : Fin r, x i ^ (r - 1) / vandermondeWeight x i) = (1 : K) := by
  have hn : r - 1 < r := by omega
  rw [vandermonde_identity (x := x) (hx := hx) (n := r - 1) hn]
  have htop : (r - 1) + 1 = r := Nat.sub_add_cancel (Nat.succ_le_of_lt hr)
  simp [htop]

end Vandermonde

/-! ### The explicit sparse family -/

/-- `s = N + 2` in the paper. -/
def s (N : ℕ) : ℕ :=
  N + 2

local instance instOfNatFinS (N : ℕ) : OfNat (Fin (s N)) 0 where
  ofNat := ⟨0, by simp [s]⟩

/-- `d = K^N` in the paper. -/
def d (N K : ℕ) : ℕ :=
  K ^ N

/-- The lacunary exponents `0, 1, K, K^2, ..., K^N`. -/
def exponent (N K : ℕ) (i : Fin (s N)) : ℕ :=
  if i.1 = 0 then 0
  else if i.1 = N + 1 then d N K
  else K ^ (i.1 - 1)

/-- The normalized frequencies `λ_j = m_j / d`. -/
def lambda (N K : ℕ) (i : Fin (s N)) : ℝ :=
  (exponent N K i : ℝ) / (d N K : ℝ)

/-- The unsigned Vandermonde factors `Δ_j`. -/
def Delta (N K : ℕ) (i : Fin (s N)) : ℝ :=
  (Finset.univ.erase i).prod fun j => |lambda N K i - lambda N K j|

/-- The signed Vandermonde product `∏_{ℓ ≠ j} (λ_j - λ_ℓ)`. -/
def signedWeight (N K : ℕ) (i : Fin (s N)) : ℝ :=
  (Finset.univ.erase i).prod fun j => (lambda N K i - lambda N K j)

/-- The paper's `A₁ = sqrt (Δ_s / Δ_1)`. -/
def A1 (N K : ℕ) : ℝ :=
  Real.sqrt (Delta N K (Fin.last (N + 1)) / Delta N K (0 : Fin (s N)))

/-- The paper's `T = (sqrt 2 * A₁)⁻¹`. -/
def T (N K : ℕ) : ℝ :=
  1 / (Real.sqrt 2 * A1 N K)

/-- The paper's `τ = 2 log T`. -/
def tau (N K : ℕ) : ℝ :=
  2 * Real.log (T N K)

/--
The coefficients `c_j`, written in the signed-weight form equivalent to equation `(def-cj)` in
the paper.

Here `signedWeight` absorbs the paper's factor `(-1)^(s-j) / Δ_j` into the denominator
`∏_{ℓ ≠ j} (λ_j - λ_ℓ)`.
-/
def cCoeff (N K : ℕ) (i : Fin (s N)) : ℂ :=
  Complex.exp ((-(lambda N K i * tau N K)) : ℂ) /
    (signedWeight N K i : ℂ)

/-- The lacunary polynomial `f_{N,K}(z)`. -/
def sparsePoly (N K : ℕ) : ℂ[X] :=
  ∑ i : Fin (s N), C (cCoeff N K i) * X ^ exponent N K i

/-- The exponential polynomial `F_{N,K}(u)`. -/
def expPoly (N K : ℕ) (u : ℂ) : ℂ :=
  ∑ i : Fin (s N), cCoeff N K i * Complex.exp ((lambda N K i : ℂ) * u)

/-- The positive real root `x₀ = exp (τ / d)`. -/
def x0 (N K : ℕ) : ℝ :=
  Real.exp (tau N K / (d N K : ℝ))

/-- The crowding interval `I_N = [0, π / d)`. -/
def crowdingInterval (N K : ℕ) : Set ℝ :=
  Set.Ico 0 (Real.pi / (d N K : ℝ))

@[simp] theorem s_eq (N : ℕ) : s N = N + 2 := rfl

@[simp] theorem d_eq (N K : ℕ) : d N K = K ^ N := rfl

theorem x0_pos (N K : ℕ) : 0 < x0 N K := by
  unfold x0
  exact Real.exp_pos _

theorem principalArg_x0 (N K : ℕ) : principalArg (x0 N K : ℂ) = 0 := by
  exact principalArg_ofReal_of_nonneg (le_of_lt (x0_pos N K))

private theorem x0_mem_slitPlane (N K : ℕ) : (x0 N K : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg]
  constructor
  · simpa [Complex.arg_ofReal_of_nonneg (le_of_lt (x0_pos N K))] using Real.pi_ne_zero.symm
  · exact_mod_cast (x0_pos N K).ne'

private theorem d_pos (N K : ℕ) (hK : 2 ≤ K) : 0 < d N K := by
  unfold d
  exact pow_pos (show 0 < K by omega) _

private theorem d_pos_real (N K : ℕ) (hK : 2 ≤ K) : 0 < (d N K : ℝ) := by
  exact_mod_cast d_pos N K hK

private theorem d_ne_zero_real (N K : ℕ) (hK : 2 ≤ K) : (d N K : ℝ) ≠ 0 :=
  (d_pos_real N K hK).ne'

private theorem d_ne_zero_complex (N K : ℕ) (hK : 2 ≤ K) : (d N K : ℂ) ≠ 0 := by
  exact_mod_cast (d_pos N K hK).ne'

private theorem d_one_le (N K : ℕ) (hK : 2 ≤ K) : 1 ≤ d N K :=
  Nat.succ_le_of_lt (d_pos N K hK)

private theorem d_one_le_real (N K : ℕ) (hK : 2 ≤ K) : (1 : ℝ) ≤ d N K := by
  exact_mod_cast (d_one_le N K hK : 1 ≤ d N K)

/-! ### Structural lemmas for the construction -/

/-- The support exponents are exactly the intended lacunary set. -/
theorem exponent_zero (N K : ℕ) : exponent N K 0 = 0 := by
  unfold exponent
  rw [if_pos]
  rfl

theorem exponent_last (N K : ℕ) : exponent N K (Fin.last (N + 1)) = d N K := by
  simp [exponent, d]

theorem exponent_middle (N K : ℕ) (i : Fin N) :
    exponent N K
      (Fin.castLT i.succ (by
        exact lt_trans i.succ.is_lt (Nat.lt_succ_self (N + 1)))) = K ^ (i : ℕ) := by
  change exponent N K
      ⟨i.1 + 1, by
        show i.1 + 1 < N + 2
        omega⟩ = K ^ (i : ℕ)
  have hi : (i : ℕ) ≠ N := Nat.ne_of_lt i.is_lt
  simp [exponent, hi]

private theorem exponent_eq_pow_of_ne_zero (N K : ℕ) {i : Fin (s N)} (hi0 : i.1 ≠ 0) :
    exponent N K i = K ^ (i.1 - 1) := by
  by_cases hs : i.1 = N + 1
  · simp [exponent, hs, d]
  · simp [exponent, hi0, hs]

private theorem exponent_strictMono (N K : ℕ) (hK : 2 ≤ K) :
    StrictMono (exponent N K) := by
  intro i j hij
  by_cases hi0 : i.1 = 0
  · have hzero : exponent N K i = 0 := by
      simp [exponent, hi0]
    have hj0 : j.1 ≠ 0 := by omega
    rw [hzero, exponent_eq_pow_of_ne_zero N K hj0]
    exact pow_pos (by omega : 0 < K) _
  · have hj0 : j.1 ≠ 0 := by omega
    rw [exponent_eq_pow_of_ne_zero N K hi0, exponent_eq_pow_of_ne_zero N K hj0]
    have hlt : i.1 - 1 < j.1 - 1 := by omega
    exact Nat.pow_lt_pow_right (by omega) hlt

/-- For `K ≥ 2`, the exponent map is injective. -/
theorem exponent_injective (N K : ℕ) (hK : 2 ≤ K) :
    Function.Injective (exponent N K) := by
  exact (exponent_strictMono N K hK).injective

/-- For `K ≥ 2`, the normalized frequencies are strictly increasing. -/
theorem lambda_strictMono (N K : ℕ) (hK : 2 ≤ K) :
    StrictMono (lambda N K) := by
  intro i j hij
  have hlt : exponent N K i < exponent N K j := exponent_strictMono N K hK hij
  unfold lambda
  exact div_lt_div_of_pos_right (by exact_mod_cast hlt) (d_pos_real N K hK)

/-- Distinct frequencies imply `Δ_j ≠ 0`. -/
theorem Delta_ne_zero (N K : ℕ) (hK : 2 ≤ K) (i : Fin (s N)) :
    Delta N K i ≠ 0 := by
  unfold Delta
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hij : j ≠ i := (Finset.mem_erase.mp hj).1
  apply abs_ne_zero.mpr
  exact sub_ne_zero.mpr fun h => hij (((lambda_strictMono N K hK).injective h).symm)

/-- Every coefficient in the sparse family is nonzero. -/
private theorem signedWeight_ne_zero (N K : ℕ) (hK : 2 ≤ K) (i : Fin (s N)) :
    signedWeight N K i ≠ 0 := by
  unfold signedWeight
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hij : j ≠ i := (Finset.mem_erase.mp hj).1
  exact sub_ne_zero.mpr fun h => hij (((lambda_strictMono N K hK).injective h).symm)

/-- Every coefficient in the sparse family is nonzero. -/
theorem cCoeff_ne_zero (N K : ℕ) (hK : 2 ≤ K) (i : Fin (s N)) :
    cCoeff N K i ≠ 0 := by
  unfold cCoeff
  refine div_ne_zero (Complex.exp_ne_zero _) ?_
  exact_mod_cast signedWeight_ne_zero N K hK i

/--
The sparse polynomial really has `N + 2` nonzero coefficients.

The intended proof is to combine `Polynomial.card_support_eq'` with the injectivity of the
exponent map and the nonvanishing of `cCoeff`.
-/
theorem nu_sparsePoly (N K : ℕ) (hK : 2 ≤ K) :
    nu (sparsePoly N K) = N + 2 := by
  unfold nu
  simpa [s] using
    (Polynomial.card_support_eq' (k := exponent N K) (x := cCoeff N K)
      (exponent_injective N K hK) (cCoeff_ne_zero N K hK))

/-! ### Moment cancellation and the multiple root -/

/-- The coefficient formula simplifies to the inverse signed Vandermonde weight. -/
theorem cCoeff_mul_exp_tau_eq_inv_signedWeight
    (N K : ℕ) (i : Fin (s N)) :
    cCoeff N K i * Complex.exp ((lambda N K i : ℂ) * (tau N K : ℂ)) =
      ((signedWeight N K i : ℂ)⁻¹) := by
  unfold cCoeff
  rw [div_eq_mul_inv]
  calc
    Complex.exp ((-(lambda N K i * tau N K)) : ℂ) * (signedWeight N K i : ℂ)⁻¹ *
        Complex.exp ((lambda N K i : ℂ) * (tau N K : ℂ))
      = (signedWeight N K i : ℂ)⁻¹ *
          (Complex.exp ((-(lambda N K i * tau N K)) : ℂ) *
            Complex.exp ((lambda N K i : ℂ) * (tau N K : ℂ))) := by
            ac_rfl
    _ = (signedWeight N K i : ℂ)⁻¹ * Complex.exp 0 := by
          congr 1
          rw [← Complex.exp_add]
          simp
    _ = ((signedWeight N K i : ℂ)⁻¹) := by simp

/-- The `n`-th iterated derivative of the exponential polynomial. -/
theorem expPoly_iteratedDeriv_formula (N K n : ℕ) (u : ℂ) :
    iteratedDeriv n (expPoly N K) u =
      ∑ i : Fin (s N),
        cCoeff N K i * (lambda N K i : ℂ) ^ n * Complex.exp ((lambda N K i : ℂ) * u) := by
  have hdiff : ∀ i : Fin (s N), i ∈ Finset.univ → ContDiffAt ℂ n
      (fun s : ℂ => cCoeff N K i * Complex.exp ((lambda N K i : ℂ) * s)) u := by
    intro i hi
    fun_prop
  unfold expPoly
  rw [iteratedDeriv_fun_sum hdiff]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_cexp_const_mul]
  simp [mul_left_comm, mul_comm]

/-- All derivatives up to order `N` vanish at `τ`. -/
theorem expPoly_moments_vanish
    (N K : ℕ) (hK : 2 ≤ K) {n : ℕ} (hn : n < s N - 1) :
    iteratedDeriv n (expPoly N K) (tau N K : ℂ) = 0 := by
  have hinj : Function.Injective (fun i : Fin (s N) => (lambda N K i : ℂ)) := by
    intro i j hij
    exact (lambda_strictMono N K hK).injective (Complex.ofReal_injective hij)
  have hs : n + 1 < s N := by omega
  have hsum :
      ∑ i : Fin (s N),
        cCoeff N K i * (lambda N K i : ℂ) ^ n *
          Complex.exp ((lambda N K i : ℂ) * (tau N K : ℂ))
      = ∑ i : Fin (s N),
          (lambda N K i : ℂ) ^ n /
            vandermondeWeight (fun i : Fin (s N) => (lambda N K i : ℂ)) i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    calc
      cCoeff N K i * (lambda N K i : ℂ) ^ n * Complex.exp ((lambda N K i : ℂ) * (tau N K : ℂ))
          = (lambda N K i : ℂ) ^ n *
              (cCoeff N K i * Complex.exp ((lambda N K i : ℂ) * (tau N K : ℂ))) := by
                ac_rfl
      _ = (lambda N K i : ℂ) ^ n * ((signedWeight N K i : ℂ)⁻¹) := by
            rw [cCoeff_mul_exp_tau_eq_inv_signedWeight N K i]
      _ = (lambda N K i : ℂ) ^ n /
            vandermondeWeight (fun i : Fin (s N) => (lambda N K i : ℂ)) i := by
            simp [vandermondeWeight, signedWeight, div_eq_mul_inv]
  rw [expPoly_iteratedDeriv_formula, hsum]
  simpa using
    (vandermonde_identity_vanish (x := fun i : Fin (s N) => (lambda N K i : ℂ)) hinj hs)

/-- The derivative of order `N + 1` at `τ` is exactly `1`. -/
theorem expPoly_top_derivative
    (N K : ℕ) (hK : 2 ≤ K) :
    iteratedDeriv (s N - 1) (expPoly N K) (tau N K : ℂ) = 1 := by
  have hinj : Function.Injective (fun i : Fin (s N) => (lambda N K i : ℂ)) := by
    intro i j hij
    exact (lambda_strictMono N K hK).injective (Complex.ofReal_injective hij)
  have hsum :
      ∑ i : Fin (s N),
        cCoeff N K i * (lambda N K i : ℂ) ^ (s N - 1) *
          Complex.exp ((lambda N K i : ℂ) * (tau N K : ℂ))
      = ∑ i : Fin (s N),
          (lambda N K i : ℂ) ^ (s N - 1) /
            vandermondeWeight (fun i : Fin (s N) => (lambda N K i : ℂ)) i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    calc
      cCoeff N K i * (lambda N K i : ℂ) ^ (s N - 1) *
          Complex.exp ((lambda N K i : ℂ) * (tau N K : ℂ))
          = (lambda N K i : ℂ) ^ (s N - 1) *
              (cCoeff N K i * Complex.exp ((lambda N K i : ℂ) * (tau N K : ℂ))) := by
                ac_rfl
      _ = (lambda N K i : ℂ) ^ (s N - 1) * ((signedWeight N K i : ℂ)⁻¹) := by
            rw [cCoeff_mul_exp_tau_eq_inv_signedWeight N K i]
      _ = (lambda N K i : ℂ) ^ (s N - 1) /
            vandermondeWeight (fun i : Fin (s N) => (lambda N K i : ℂ)) i := by
            simp [vandermondeWeight, signedWeight, div_eq_mul_inv]
  rw [expPoly_iteratedDeriv_formula, hsum]
  simpa using
    (vandermonde_identity_top
      (x := fun i : Fin (s N) => (lambda N K i : ℂ)) hinj (by simp [s]))

/-- `expPoly` has a zero of exact order `N + 1` at `τ`. -/
theorem expPoly_order_at_tau
    (N K : ℕ) (hK : 2 ≤ K) :
    analyticOrderAt (expPoly N K) (tau N K : ℂ) = N + 1 := by
  have ha : AnalyticAt ℂ (expPoly N K) (tau N K : ℂ) := by
    unfold expPoly
    fun_prop
  have hlow : ((N + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (expPoly N K) (tau N K : ℂ) := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]
    intro i hi
    exact expPoly_moments_vanish N K hK (by simpa [s] using hi)
  have hnot : ¬ (((N + 2 : ℕ) : ℕ∞) ≤ analyticOrderAt (expPoly N K) (tau N K : ℂ)) := by
    intro hge
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha] at hge
    have hz : iteratedDeriv (s N - 1) (expPoly N K) (tau N K : ℂ) = 0 := by
      exact hge (s N - 1) (by simp [s])
    rw [expPoly_top_derivative N K hK] at hz
    exact one_ne_zero hz
  have hfin : analyticOrderAt (expPoly N K) (tau N K : ℂ) ≠ ⊤ := by
    intro htop
    apply hnot
    rw [htop]
    simp
  rcases ENat.ne_top_iff_exists.mp hfin with ⟨m, hm⟩
  have hlow' : N + 1 ≤ m := by
    rw [← hm] at hlow
    exact_mod_cast hlow
  have hupp' : m < N + 2 := by
    by_contra hm'
    have hmle : N + 2 ≤ m := Nat.not_lt.mp hm'
    apply hnot
    rw [← hm]
    exact_mod_cast hmle
  have hm_eq : m = N + 1 := by
    omega
  calc
    analyticOrderAt (expPoly N K) (tau N K : ℂ) = m := by simpa using hm.symm
    _ = N + 1 := by exact_mod_cast hm_eq

/-- Near the positive point `x₀`, the sparse polynomial is obtained by the logarithmic substitution. -/
theorem sparsePoly_eq_expPoly_clog_eventually (N K : ℕ) (hK : 2 ≤ K) :
    ∀ᶠ z in 𝓝 (x0 N K : ℂ),
      (sparsePoly N K).eval z = expPoly N K ((d N K : ℂ) * Complex.log z) := by
  filter_upwards [Complex.isOpen_slitPlane.eventually_mem (x0_mem_slitPlane N K)] with z hz
  have hz0 : z ≠ 0 := Complex.slitPlane_ne_zero hz
  unfold sparsePoly expPoly
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Polynomial.eval_C_mul, Polynomial.eval_X_pow]
  congr 1
  have hlamR : lambda N K i * (d N K : ℝ) = exponent N K i := by
    unfold lambda
    field_simp [d_ne_zero_real N K hK]
  have hlam : ((lambda N K i : ℂ) * (d N K : ℂ)) = (exponent N K i : ℂ) := by
    exact_mod_cast hlamR
  calc
    z ^ exponent N K i = (Complex.exp (Complex.log z)) ^ exponent N K i := by
      rw [Complex.exp_log hz0]
    _ = Complex.exp ((exponent N K i) * Complex.log z) := by
      rw [← Complex.exp_nat_mul]
    _ = Complex.exp (((lambda N K i : ℂ) * (d N K : ℂ)) * Complex.log z) := by
      rw [hlam]
    _ = Complex.exp ((lambda N K i : ℂ) * ((d N K : ℂ) * Complex.log z)) := by
      simp [mul_assoc]

private theorem analyticOrderAt_eval_zero_eq_natTrailingDegree_of_ne_zero
    {q : ℂ[X]} (hq : q ≠ 0) :
    analyticOrderAt (fun z : ℂ => q.eval z) 0 = q.natTrailingDegree := by
  let n : ℕ := q.natTrailingDegree
  have ha : AnalyticAt ℂ (fun z : ℂ => q.eval z) 0 := by
    simpa using (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) q) 0 (by simp)
  have hdvd : X ^ n ∣ q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro m hm
    exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by simpa [n] using hm)
  rcases hdvd with ⟨r, hr⟩
  have hcoeffq : q.coeff n ≠ 0 := by
    exact mem_support_iff.mp (Polynomial.natTrailingDegree_mem_support_of_nonzero hq)
  have hcoeffr : r.coeff 0 ≠ 0 := by
    have hqeq : q.coeff n = r.coeff 0 := by
      rw [hr]
      simpa [n] using (Polynomial.coeff_X_pow_mul r n 0)
    exact hqeq.symm ▸ hcoeffq
  rw [ha.analyticOrderAt_eq_natCast]
  refine ⟨fun z : ℂ => r.eval z, ?_, ?_, ?_⟩
  · simpa using (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) r) 0 (by simp)
  · simpa [Polynomial.coeff_zero_eq_eval_zero] using hcoeffr
  · exact Filter.Eventually.of_forall fun z => by
      simp only [sub_zero]
      calc
        q.eval z = (X ^ n * r).eval z := by rw [hr]
        _ = z ^ n * r.eval z := by rw [Polynomial.eval_mul, Polynomial.eval_X_pow]
        _ = z ^ q.natTrailingDegree • r.eval z := by simp [n, smul_eq_mul]

private theorem analyticOrderAt_eval_eq_rootMultiplicity_of_ne_zero
    {p : ℂ[X]} (hp : p ≠ 0) (x : ℂ) :
    analyticOrderAt (fun z : ℂ => p.eval z) x = p.rootMultiplicity x := by
  let q : ℂ[X] := p.comp (X + C x)
  have hq : q ≠ 0 := by
    simpa [q] using (Polynomial.comp_X_add_C_ne_zero_iff (p := p) (t := x)).2 hp
  have hcongr :
      analyticOrderAt (fun z : ℂ => q.eval z) 0 =
        analyticOrderAt ((fun z : ℂ => p.eval z) ∘ fun z : ℂ => z + x) 0 := by
    apply analyticOrderAt_congr
    filter_upwards with z
    simp [q, Function.comp, Polynomial.eval_comp, add_comm]
  have hcomp :
      analyticOrderAt ((fun z : ℂ => p.eval z) ∘ fun z : ℂ => z + x) 0 =
        analyticOrderAt (fun z : ℂ => p.eval z) x := by
    simpa using
      (analyticOrderAt_comp_of_deriv_ne_zero
        (f := fun z : ℂ => p.eval z)
        (g := fun z : ℂ => z + x) (z₀ := 0)
        (by fun_prop) (by simp))
  calc
    analyticOrderAt (fun z : ℂ => p.eval z) x
        = analyticOrderAt ((fun z : ℂ => p.eval z) ∘ fun z : ℂ => z + x) 0 := by
            symm
            exact hcomp
    _ = analyticOrderAt (fun z : ℂ => q.eval z) 0 := by
          symm
          exact hcongr
    _ = q.natTrailingDegree := analyticOrderAt_eval_zero_eq_natTrailingDegree_of_ne_zero hq
    _ = p.rootMultiplicity x := by
          simpa [q] using
            (Polynomial.rootMultiplicity_eq_natTrailingDegree (p := p) (t := x)).symm

/--
The sparse polynomial has a positive real zero of multiplicity `N + 1`.

This is the main lemma `p990:lem:multiple-root` from the paper.
-/
theorem sparsePoly_rootMultiplicity_at_x0
    (N K : ℕ) (hK : 2 ≤ K) :
    (sparsePoly N K).rootMultiplicity (x0 N K : ℂ) = N + 1 := by
  have hsp : sparsePoly N K ≠ 0 := by
    have hcoeff0 : (sparsePoly N K).coeff 0 ≠ 0 := by
      rw [sparsePoly, finset_sum_coeff]
      rw [Finset.sum_eq_single_of_mem (0 : Fin (s N)) (Finset.mem_univ _)]
      · simpa [coeff_C_mul_X_pow, exponent_zero] using cCoeff_ne_zero N K hK (0 : Fin (s N))
      · intro j _ hj
        rw [coeff_C_mul_X_pow]
        split_ifs with h
        · exfalso
          exact hj ((exponent_injective N K hK) (by simpa [exponent_zero] using h.symm))
        · simp
    intro hs
    simpa [hs] using hcoeff0
  have hg : AnalyticAt ℂ (fun z : ℂ => (d N K : ℂ) * Complex.log z) (x0 N K : ℂ) := by
    have hlog : AnalyticAt ℂ Complex.log (x0 N K : ℂ) :=
      analyticAt_clog (x0_mem_slitPlane N K)
    simpa [mul_comm] using (analyticAt_const.mul hlog)
  have hg' : deriv (fun z : ℂ => (d N K : ℂ) * Complex.log z) (x0 N K : ℂ) ≠ 0 := by
    have hderiv :
        HasDerivAt (fun z : ℂ => (d N K : ℂ) * Complex.log z)
          ((d N K : ℂ) * (x0 N K : ℂ)⁻¹) (x0 N K : ℂ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (Complex.hasDerivAt_log (x0_mem_slitPlane N K)).const_mul (d N K : ℂ)
    rw [hderiv.deriv]
    exact mul_ne_zero (d_ne_zero_complex N K hK)
      (inv_ne_zero (by exact_mod_cast (x0_pos N K).ne'))
  have hcomp :
      analyticOrderAt (expPoly N K ∘ fun z : ℂ => (d N K : ℂ) * Complex.log z) (x0 N K : ℂ)
        = analyticOrderAt (expPoly N K) ((d N K : ℂ) * Complex.log (x0 N K : ℂ)) := by
    simpa using
      (analyticOrderAt_comp_of_deriv_ne_zero
        (f := expPoly N K)
        (g := fun z : ℂ => (d N K : ℂ) * Complex.log z)
        (z₀ := (x0 N K : ℂ)) hg hg')
  have hx0eval : ((d N K : ℂ) * Complex.log (x0 N K : ℂ)) = (tau N K : ℂ) := by
    have hreal : (d N K : ℝ) * Real.log (x0 N K) = tau N K := by
      unfold x0
      rw [Real.log_exp]
      field_simp [d_ne_zero_real N K hK]
    rw [← Complex.ofReal_log (le_of_lt (x0_pos N K))]
    exact_mod_cast hreal
  have hroot : (((sparsePoly N K).rootMultiplicity (x0 N K : ℂ) : ℕ∞)) = N + 1 := by
    calc
      (sparsePoly N K).rootMultiplicity (x0 N K : ℂ)
          = analyticOrderAt (fun z : ℂ => (sparsePoly N K).eval z) (x0 N K : ℂ) := by
              symm
              exact analyticOrderAt_eval_eq_rootMultiplicity_of_ne_zero hsp (x0 N K : ℂ)
      _ = analyticOrderAt (expPoly N K ∘ fun z : ℂ => (d N K : ℂ) * Complex.log z) (x0 N K : ℂ) := by
            exact analyticOrderAt_congr (sparsePoly_eq_expPoly_clog_eventually N K hK)
      _ = analyticOrderAt (expPoly N K) ((d N K : ℂ) * Complex.log (x0 N K : ℂ)) := hcomp
      _ = analyticOrderAt (expPoly N K) (tau N K : ℂ) := by rw [hx0eval]
      _ = N + 1 := expPoly_order_at_tau N K hK
  exact ENat.coe_inj.mp hroot

/-- All copies of the positive root lie in the crowding interval. -/
theorem overcrowded_small_interval
    (N K : ℕ) (hK : 2 ≤ K) :
    N + 1 ≤ argRootCount (sparsePoly N K) (crowdingInterval N K) := by
  have hI : 0 ∈ crowdingInterval N K := by
    unfold crowdingInterval
    constructor
    · simp
    · exact div_pos Real.pi_pos (d_pos_real N K hK)
  have hroot :
      (sparsePoly N K).rootMultiplicity (x0 N K : ℂ) ≤
        argRootCount (sparsePoly N K) (crowdingInterval N K) :=
    rootMultiplicity_le_argRootCount_of_positive_root (x0_pos N K) hI
  simpa [sparsePoly_rootMultiplicity_at_x0 N K hK] using hroot

/-- The uniform prediction for the crowding interval is exactly `1/2`. -/
theorem expectedRootCount_crowdingInterval (N K : ℕ) (hK : 2 ≤ K) :
    expectedRootCount (d N K) 0 (Real.pi / (d N K : ℝ)) = (1 / 2 : ℝ) := by
  unfold expectedRootCount
  field_simp [d_ne_zero_real N K hK, Real.pi_ne_zero]
  ring

/-! ### The growth parameter `M(f)` -/

/-- Middle indices `1, …, N` inside `Fin (N+2)`. -/
private def midIdx {N : ℕ} (i : Fin N) : Fin (s N) :=
  Fin.castLT i.succ (by
    simpa [s] using lt_trans i.succ.is_lt (Nat.lt_succ_self (N + 1)))

/-- The auxiliary coefficients `A_j = sqrt (Δ₁ Δ_s) / Δ_j` from the paper. -/
private def Acoeff (N K : ℕ) (i : Fin (s N)) : ℝ :=
  Real.sqrt (Delta N K 0 * Delta N K (Fin.last (N + 1))) / Delta N K i

/-- The middle ratios `R_i = Δ₁ / Δ_{i+1}` from the paper. -/
private def Rcoeff (N K : ℕ) (i : Fin N) : ℝ :=
  Delta N K 0 / Delta N K (midIdx i)

private theorem midIdx_eq_succ_castSucc {N : ℕ} (i : Fin N) :
    midIdx i = (i.castSucc).succ := by
  ext
  simp [midIdx]

/-- The support of the sparse polynomial is exactly the image of the exponent map. -/
private theorem sparsePoly_support_eq_image (N K : ℕ) (hK : 2 ≤ K) :
    (sparsePoly N K).support = Finset.image (exponent N K) Finset.univ := by
  classical
  ext n
  constructor
  · intro hn
    rw [mem_support_iff] at hn
    by_contra hnot
    have hcoeff : (sparsePoly N K).coeff n = 0 := by
      rw [sparsePoly, finset_sum_coeff]
      apply Finset.sum_eq_zero
      intro i hi
      rw [coeff_C_mul_X_pow]
      apply if_neg
      intro hin
      apply hnot
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hin.symm⟩
    exact hn hcoeff
  · intro hn
    rw [mem_support_iff]
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    rw [sparsePoly, finset_sum_coeff, Finset.sum_eq_single_of_mem i hi, coeff_C_mul_X_pow, if_pos rfl]
    · exact cCoeff_ne_zero N K hK i
    · intro j _ hij
      rw [coeff_C_mul_X_pow]
      apply if_neg
      intro h
      exact hij ((exponent_injective N K hK h).symm)

/-- The coefficient at one of the distinguished exponents is the corresponding `c_j`. -/
private theorem coeff_sparsePoly_exponent (N K : ℕ) (hK : 2 ≤ K) (i : Fin (s N)) :
    (sparsePoly N K).coeff (exponent N K i) = cCoeff N K i := by
  classical
  rw [sparsePoly, finset_sum_coeff]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp
  · intro j _ hij
    simp [if_neg (by intro h; exact hij.symm (exponent_injective N K hK h))]

/-- Exact `ℓ¹`-formula for the sparse family. -/
private theorem coeffL1_sparsePoly_eq_sum (N K : ℕ) (hK : 2 ≤ K) :
    coeffL1 (sparsePoly N K) = ∑ i : Fin (s N), ‖cCoeff N K i‖ := by
  classical
  unfold coeffL1
  rw [sparsePoly_support_eq_image N K hK, Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    simpa using congrArg norm (coeff_sparsePoly_exponent N K hK i)
  · intro i _ j _ hij
    exact exponent_injective N K hK hij

/-- The constant term of the sparse family. -/
private theorem coeff_zero_sparsePoly (N K : ℕ) (hK : 2 ≤ K) :
    (sparsePoly N K).coeff 0 = cCoeff N K 0 := by
  simpa [exponent_zero] using coeff_sparsePoly_exponent N K hK (0 : Fin (s N))

/-- The degree of the sparse family is the last lacunary exponent. -/
private theorem natDegree_sparsePoly (N K : ℕ) (hK : 2 ≤ K) :
    (sparsePoly N K).natDegree = d N K := by
  classical
  have hcoeff : (sparsePoly N K).coeff (d N K) = cCoeff N K (Fin.last (N + 1)) := by
    simpa [exponent_last] using
      coeff_sparsePoly_exponent N K hK (Fin.last (N + 1))
  have hcoeff_ne : (sparsePoly N K).coeff (d N K) ≠ 0 := by
    intro hz
    exact cCoeff_ne_zero N K hK (Fin.last (N + 1)) (hcoeff.symm.trans hz)
  have hdeg_le : (sparsePoly N K).natDegree ≤ d N K := by
    refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ)
      (f := fun i : Fin (s N) => C (cCoeff N K i) * X ^ exponent N K i) ?_
    intro i hi
    by_cases h0 : cCoeff N K i = 0
    · simp [h0]
    · by_cases hi0 : i.1 = 0
      · exact (Polynomial.natDegree_C_mul_X_pow_le (cCoeff N K i) (exponent N K i)).trans <| by
          simp [exponent, hi0, d]
      · by_cases hilast : i.1 = N + 1
        · exact (Polynomial.natDegree_C_mul_X_pow_le (cCoeff N K i) (exponent N K i)).trans <| by
            simp [exponent, hilast, d]
        · have hi_le : i.1 - 1 ≤ N := by
            have hi_lt : i.1 < N + 2 := by
              simpa [s] using i.is_lt
            have hi' : i.1 ≤ N := by
              omega
            omega
          exact (Polynomial.natDegree_C_mul_X_pow_le (cCoeff N K i) (exponent N K i)).trans <| by
            rw [exponent_eq_pow_of_ne_zero N K hi0, d]
            exact Nat.pow_le_pow_right (by omega) hi_le
  exact Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg_le hcoeff_ne

/-- The top coefficient of the sparse family. -/
private theorem leadingCoeff_sparsePoly (N K : ℕ) (hK : 2 ≤ K) :
    (sparsePoly N K).leadingCoeff = cCoeff N K (Fin.last (N + 1)) := by
  classical
  have hdeg : (sparsePoly N K).natDegree = d N K := natDegree_sparsePoly N K hK
  rw [← Polynomial.coeff_natDegree, hdeg]
  simpa [exponent_last] using coeff_sparsePoly_exponent N K hK (Fin.last (N + 1))

/-- Exact norm formula for `c_j`. -/
private theorem norm_cCoeff (N K : ℕ) (i : Fin (s N)) :
    ‖cCoeff N K i‖ = Real.exp (-(lambda N K i) * tau N K) / Delta N K i := by
  have hsw : ‖(signedWeight N K i : ℂ)‖ = Delta N K i := by
    simpa [signedWeight, Delta, Real.norm_eq_abs, Finset.abs_prod] using
      (Complex.norm_real (∏ j ∈ Finset.univ.erase i, (lambda N K i - lambda N K j)))
  have hexp : ‖Complex.exp ((-(lambda N K i * tau N K)) : ℂ)‖ =
      Real.exp (-(lambda N K i) * tau N K) := by
    simpa using Complex.norm_exp_ofReal (-(lambda N K i * tau N K))
  unfold cCoeff
  rw [norm_div, hexp, hsw]

/-- `λ_0 = 0`. -/
private theorem lambda_zero (N K : ℕ) : lambda N K 0 = 0 := by
  unfold lambda
  simp [exponent_zero]

/-- `λ_s = 1`. -/
private theorem lambda_last (N K : ℕ) (hK : 2 ≤ K) :
    lambda N K (Fin.last (N + 1)) = 1 := by
  unfold lambda
  rw [exponent_last]
  have hd : (d N K : ℝ) ≠ 0 := d_ne_zero_real N K hK
  field_simp [hd]

private theorem lambda_succ_eq_inv_pow (N K : ℕ) (hK : 2 ≤ K) (m : Fin (N + 1)) :
    lambda N K m.succ = ((K : ℝ)⁻¹) ^ (N - m.1) := by
  by_cases hm : m.1 = N
  · have hlast : m.succ = Fin.last (N + 1) := by
      ext
      simp [hm]
    rw [hlast, lambda_last N K hK, hm]
    simp
  · have hm' : m.1 < N := by omega
    have hne0 : (m.succ : Fin (s N)).1 ≠ 0 := by simp
    unfold lambda
    rw [exponent_eq_pow_of_ne_zero N K hne0, d]
    have hk0 : (K : ℝ) ≠ 0 := by
      exact_mod_cast (show K ≠ 0 by omega)
    have hmle : m.1 ≤ N := Nat.le_of_lt hm'
    calc
      ((K ^ m.1 : ℕ) : ℝ) / ((K ^ N : ℕ) : ℝ) = (K : ℝ) ^ m.1 / (K : ℝ) ^ N := by
        norm_num
      _ = (K : ℝ) ^ m.1 / ((K : ℝ) ^ m.1 * (K : ℝ) ^ (N - m.1)) := by
            rw [← pow_add, Nat.add_sub_of_le hmle]
      _ = ((K : ℝ) ^ (N - m.1))⁻¹ := by
            field_simp [pow_ne_zero _ hk0]
      _ = ((K : ℝ)⁻¹) ^ (N - m.1) := by
            rw [inv_pow]

/-- Positivity of the Vandermonde factors. -/
private theorem Delta_pos (N K : ℕ) (hK : 2 ≤ K) (i : Fin (s N)) :
    0 < Delta N K i := by
  have hnonneg : 0 ≤ Delta N K i := by
    unfold Delta
    positivity
  exact lt_of_le_of_ne hnonneg (Delta_ne_zero N K hK i).symm

/-- Exact endpoint identity `A₁ exp(τ/2) = 1/√2`. -/
private theorem Acoeff_zero_mul_exp_tau_half (N K : ℕ) (hK : 2 ≤ K) :
    Acoeff N K 0 * Real.exp (tau N K / 2) = 1 / Real.sqrt 2 := by
  have hΔ0 : 0 < Delta N K 0 := Delta_pos N K hK 0
  have hΔs : 0 < Delta N K (Fin.last (N + 1)) := Delta_pos N K hK (Fin.last (N + 1))
  have hA1 : 0 < A1 N K := by
    unfold A1
    positivity
  have hT : 0 < T N K := by
    unfold T
    positivity
  have hexp : Real.exp (tau N K / 2) = T N K := by
    unfold tau
    rw [show (2 * Real.log (T N K)) / 2 = Real.log (T N K) by ring]
    exact Real.exp_log hT
  have hAcoeff0 : Acoeff N K 0 = A1 N K := by
    unfold Acoeff A1
    rw [Real.sqrt_mul, Real.sqrt_div]
    · field_simp [hΔ0.ne', (Real.sqrt_ne_zero'.2 hΔ0).symm]
      rw [Real.sq_sqrt hΔ0.le]
    · positivity
    · positivity
  rw [hexp, hAcoeff0]
  unfold T
  field_simp [hA1.ne']

/-- Exact endpoint identity `A_s exp(-τ/2) = √2`. -/
private theorem Acoeff_last_mul_exp_neg_tau_half (N K : ℕ) (hK : 2 ≤ K) :
    Acoeff N K (Fin.last (N + 1)) * Real.exp (-(tau N K) / 2) = Real.sqrt 2 := by
  have hΔ0 : 0 < Delta N K 0 := Delta_pos N K hK 0
  have hΔs : 0 < Delta N K (Fin.last (N + 1)) := Delta_pos N K hK (Fin.last (N + 1))
  have hA1 : 0 < A1 N K := by
    unfold A1
    positivity
  have hT : 0 < T N K := by
    unfold T
    positivity
  have hexp : Real.exp (-(tau N K) / 2) = (T N K)⁻¹ := by
    unfold tau
    rw [show -(2 * Real.log (T N K)) / 2 = - Real.log (T N K) by ring]
    rw [Real.exp_neg, Real.exp_log hT]
  have hAcoeffLast : Acoeff N K (Fin.last (N + 1)) = (A1 N K)⁻¹ := by
    unfold Acoeff A1
    rw [Real.sqrt_mul, Real.sqrt_div]
    · field_simp [hΔs.ne', (Real.sqrt_ne_zero'.2 hΔ0).symm, (Real.sqrt_ne_zero'.2 hΔs).symm]
      rw [Real.sq_sqrt hΔs.le]
    · positivity
    · positivity
  rw [hexp, hAcoeffLast]
  unfold T
  field_simp [hA1.ne']

/-- The exact coefficient formula from Proposition `p990:prop:height`. -/
private theorem M_sparsePoly_exact (N K : ℕ) (hK : 2 ≤ K) :
    M (sparsePoly N K)
      = ∑ i : Fin (s N), Acoeff N K i * Real.exp ((1 / 2 - lambda N K i) * tau N K) := by
  classical
  have hcoeffL1 : coeffL1 (sparsePoly N K) = ∑ i : Fin (s N),
      Real.exp (-(lambda N K i) * tau N K) / Delta N K i := by
    rw [coeffL1_sparsePoly_eq_sum N K hK]
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [norm_cCoeff]
  have h0 : ‖(sparsePoly N K).coeff 0‖ = 1 / Delta N K 0 := by
    rw [coeff_zero_sparsePoly N K hK, norm_cCoeff, lambda_zero]
    simp
  have hs : ‖(sparsePoly N K).leadingCoeff‖ =
      Real.exp (-(tau N K)) / Delta N K (Fin.last (N + 1)) := by
    rw [leadingCoeff_sparsePoly N K hK, norm_cCoeff, lambda_last N K hK]
    simp
  have hΔ0 : 0 < Delta N K 0 := Delta_pos N K hK 0
  have hΔs : 0 < Delta N K (Fin.last (N + 1)) := Delta_pos N K hK (Fin.last (N + 1))
  have hden : Real.sqrt
      (‖(sparsePoly N K).coeff 0‖ * ‖(sparsePoly N K).leadingCoeff‖)
      = Real.exp (-(tau N K) / 2) / Real.sqrt (Delta N K 0 * Delta N K (Fin.last (N + 1))) := by
    rw [h0, hs]
    have hfrac :
        1 / Delta N K 0 * (Real.exp (-(tau N K)) / Delta N K (Fin.last (N + 1)))
          = Real.exp (-(tau N K)) / (Delta N K 0 * Delta N K (Fin.last (N + 1))) := by
      field_simp [hΔ0.ne', hΔs.ne']
    have hExp : Real.exp (-(tau N K)) = (Real.exp (-(tau N K) / 2)) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [hfrac, Real.sqrt_div (by positivity), hExp, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  unfold M
  rw [hcoeffL1, hden, div_eq_mul_inv, inv_div, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro i hi
  unfold Acoeff
  ring_nf
  have hhalf : (Real.exp (tau N K * (-1 / 2)))⁻¹ = Real.exp (tau N K * (1 / 2)) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hhalf]
  have hmul :
      Real.exp (-(lambda N K i * tau N K)) * (Delta N K i)⁻¹ *
          Real.sqrt (Delta N K 0 * Delta N K (Fin.last (N + 1))) * Real.exp (tau N K * (1 / 2)) =
        (Delta N K i)⁻¹ * Real.sqrt (Delta N K 0 * Delta N K (Fin.last (N + 1))) *
          (Real.exp (-(lambda N K i * tau N K)) * Real.exp (tau N K * (1 / 2))) := by
    ac_rfl
  rw [hmul, ← Real.exp_add]

/-- Exact finite-product formula for the last Vandermonde factor. -/
private theorem Delta_last_eq_prod (N K : ℕ) (hK : 2 ≤ K) :
    Delta N K (Fin.last (N + 1))
      = ∏ m ∈ Finset.range N, (1 - ((K : ℝ)⁻¹) ^ (m + 1)) := by
  classical
  -- This is the paper identity `Δ_s = ∏_{m=1}^N (1 - ε^m)` with `ε = K⁻¹`.
  -- We rewrite the erased product over `Fin (N + 2)` as a product over `Fin (N + 1)`,
  -- split off the `j = 0` term, and then reflect the remaining range product.
  unfold Delta
  have hcast :
      (∏ j ∈ (Finset.univ.erase (Fin.last (N + 1)) : Finset (Fin (N + 2))),
        |lambda N K (Fin.last (N + 1)) - lambda N K j|)
        = ∏ x : Fin (N + 1), |lambda N K (Fin.last (N + 1)) - lambda N K (Fin.castSucc x)| := by
    rw [show (Finset.univ.erase (Fin.last (N + 1)) : Finset (Fin (N + 2))) =
        Finset.univ.map Fin.castSuccEmb by simp [Fin.univ_castSuccEmb (N + 1)]]
    simp
  refine hcast.trans ?_
  rw [lambda_last N K hK, Fin.prod_univ_succ]
  rw [Finset.prod_fin_eq_prod_range]
  have hrange :
      (∏ i ∈ Finset.range N,
          if h : i < N then |1 - lambda N K ((⟨i, h⟩ : Fin N).castSucc.succ)| else 1)
        = ∏ m ∈ Finset.range N, (1 - ((K : ℝ)⁻¹) ^ (N - m)) := by
    refine Finset.prod_congr rfl ?_
    intro m hm
    have hm' : m < N := Finset.mem_range.mp hm
    simp [hm']
    have hpow :
        exponent N K ((⟨m, hm'⟩ : Fin N).castSucc.succ) = K ^ m := by
      simpa [midIdx, s] using exponent_middle N K (⟨m, hm'⟩ : Fin N)
    have hlam :
        lambda N K ((⟨m, hm'⟩ : Fin N).castSucc.succ) = ((K : ℝ)⁻¹) ^ (N - m) := by
      unfold lambda
      rw [hpow, d]
      have hk0 : (K : ℝ) ≠ 0 := by
        exact_mod_cast (show K ≠ 0 by omega)
      have hmle : m ≤ N := Nat.le_of_lt hm'
      calc
        ((K ^ m : ℕ) : ℝ) / ((K ^ N : ℕ) : ℝ)
            = (K : ℝ) ^ m / (K : ℝ) ^ N := by norm_num
        _ = (K : ℝ) ^ m / ((K : ℝ) ^ m * (K : ℝ) ^ (N - m)) := by
              rw [← pow_add, Nat.add_sub_of_le hmle]
        _ = ((K : ℝ) ^ (N - m))⁻¹ := by
              field_simp [pow_ne_zero _ hk0]
        _ = ((K : ℝ)⁻¹) ^ (N - m) := by rw [inv_pow]
    have hbase_nonneg : 0 ≤ ((K : ℝ)⁻¹) := by positivity
    have hbase_le_one : ((K : ℝ)⁻¹) ≤ 1 := by
      exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ K by omega))
    have hpow_le_one : ((K : ℝ)⁻¹) ^ (N - m) ≤ 1 :=
      pow_le_one₀ hbase_nonneg hbase_le_one
    calc
      |1 - lambda N K ((⟨m, hm'⟩ : Fin N).castSucc.succ)|
          = |1 - ((K : ℝ)⁻¹) ^ (N - m)| := by rw [hlam]
      _ = 1 - ((K : ℝ)⁻¹) ^ (N - m) := by
            rw [abs_of_nonneg (sub_nonneg.mpr hpow_le_one)]
      _ = 1 - (((K : ℝ) ^ (N - m))⁻¹) := by rw [inv_pow]
  have hpowRewrite :
      (∏ m ∈ Finset.range N, (1 - ((K : ℝ)⁻¹) ^ (N - m)))
        = ∏ x ∈ Finset.range N, (1 - (((K : ℝ) ^ (N - x))⁻¹)) := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    rw [inv_pow]
  calc
    |1 - lambda N K 0| *
        (∏ i ∈ Finset.range N,
          if h : i < N then |1 - lambda N K ((⟨i, h⟩ : Fin N).castSucc.succ)| else 1)
        = ∏ m ∈ Finset.range N, (1 - ((K : ℝ)⁻¹) ^ (N - m)) := by
            rw [lambda_zero]
            norm_num
            simpa using hrange
    _ = ∏ x ∈ Finset.range N, (1 - (((K : ℝ) ^ (N - x))⁻¹)) := hpowRewrite
    _ = ∏ x ∈ Finset.range N, (1 - (((K : ℝ) ^ (N - 1 - x + 1))⁻¹)) := by
            refine Finset.prod_congr rfl ?_
            intro x hx
            have hx' : x < N := Finset.mem_range.mp hx
            rw [show N - x = N - 1 - x + 1 by omega]
    _ = ∏ x ∈ Finset.range N, (1 - (((K : ℝ) ^ (x + 1))⁻¹)) := by
          simpa using
            (Finset.prod_range_reflect (fun m => 1 - (((K : ℝ) ^ (m + 1))⁻¹)) N)
    _ = ∏ x ∈ Finset.range N, (1 - ((K : ℝ)⁻¹) ^ (x + 1)) := by
          refine Finset.prod_congr rfl ?_
          intro x hx
          rw [inv_pow]

/-- Exact finite-product formula for the endpoint ratio `R_i`. -/
private theorem Rcoeff_eq_main_term (N K : ℕ) (hK : 2 ≤ K) (i : Fin N) :
    Rcoeff N K i
      = (((K : ℝ) ^ (i.1 * (i.1 + 1) / 2))⁻¹)
          / (((1 - (((K : ℝ) ^ (N - i.1))⁻¹))
              * ∏ m ∈ Finset.range i.1, (1 - (((K : ℝ) ^ (m + 1))⁻¹)))
              * ∏ m ∈ Finset.range (N - i.1 - 1), (1 - (((K : ℝ) ^ (m + 1))⁻¹))) := by
  classical
  set ε : ℝ := (K : ℝ)⁻¹
  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hε_le_one : ε ≤ 1 := by
    dsimp [ε]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast (show 1 ≤ K by omega))
  have hli : lambda N K i.castSucc.succ = ε ^ (N - i.1) := by
    simpa [ε] using lambda_succ_eq_inv_pow N K hK i.castSucc
  have hε_ne_zero : ε ≠ 0 := by
    dsimp [ε]
    exact inv_ne_zero (by exact_mod_cast (show K ≠ 0 by omega))
  unfold Rcoeff Delta
  rw [midIdx_eq_succ_castSucc]
  have h0 :
      (∏ j ∈ (Finset.univ.erase (0 : Fin (N + 2)) : Finset (Fin (N + 2))),
        |lambda N K 0 - lambda N K j|)
        = ∏ x : Fin (N + 1), lambda N K x.succ := by
    rw [show (Finset.univ.erase (0 : Fin (N + 2)) : Finset (Fin (N + 2))) =
        Finset.univ.map ⟨Fin.succ, Fin.succ_injective (n := N + 1)⟩ by
          simp [Fin.univ_succ (N + 1)]]
    simp [lambda_zero]
    refine Fintype.prod_congr (fun x : Fin (N + 1) => |lambda N K x.succ|)
      (fun x : Fin (N + 1) => lambda N K x.succ) ?_
    intro x
    change |lambda N K x.succ| = lambda N K x.succ
    rw [abs_of_nonneg]
    unfold lambda
    exact div_nonneg (by exact_mod_cast Nat.zero_le (exponent N K x.succ))
      (by exact_mod_cast Nat.zero_le (d N K))
  have hmid :
      (∏ j ∈ (Finset.univ.erase (i.castSucc.succ) : Finset (Fin (N + 2))),
        |lambda N K i.castSucc.succ - lambda N K j|)
        = ∏ x : Fin (N + 1), |lambda N K i.castSucc.succ - lambda N K (i.castSucc.succ.succAbove x)| := by
    rw [show (Finset.univ.erase (i.castSucc.succ) : Finset (Fin (N + 2))) =
        Finset.univ.map (Fin.succAboveEmb i.castSucc.succ) by
          simp [Fin.univ_succAbove (N + 1) i.castSucc.succ]]
    simp
  calc
    (∏ j ∈ (Finset.univ.erase (0 : Fin (N + 2)) : Finset (Fin (N + 2))),
        |lambda N K 0 - lambda N K j|) /
        ∏ j ∈ (Finset.univ.erase (i.castSucc.succ) : Finset (Fin (N + 2))),
          |lambda N K i.castSucc.succ - lambda N K j|
      = (∏ x : Fin (N + 1), lambda N K x.succ) /
          ∏ x : Fin (N + 1), |lambda N K i.castSucc.succ - lambda N K (i.castSucc.succ.succAbove x)| := by
            rw [h0, hmid]
    _ = (((K : ℝ) ^ (i.1 * (i.1 + 1) / 2))⁻¹) /
          (((1 - (((K : ℝ) ^ (N - i.1))⁻¹))
              * ∏ m ∈ Finset.range i.1, (1 - (((K : ℝ) ^ (m + 1))⁻¹)))
              * ∏ m ∈ Finset.range (N - i.1 - 1), (1 - (((K : ℝ) ^ (m + 1))⁻¹))) := by
            rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
            have hfirst : lambda N K (Fin.succ (0 : Fin (N + 1))) = ε ^ N := by
              simpa [ε] using lambda_succ_eq_inv_pow N K hK (0 : Fin (N + 1))
            have hzeroDen :
                |lambda N K i.castSucc.succ - lambda N K (i.castSucc.succ.succAbove 0)| = ε ^ (N - i.1) := by
              have hz : lambda N K (i.castSucc.succ.succAbove 0) = 0 := by
                rw [Fin.succ_succAbove_zero]
                exact lambda_zero N K
              rw [hz, hli]
              have hnonneg : 0 ≤ ε ^ (N - i.1) := by positivity
              simpa [abs_of_nonneg hnonneg]
            have hnumTail :
                (∏ x : Fin N, lambda N K x.succ.succ)
                  = (∏ m ∈ Finset.range N, ε ^ (N - (m + 1))) := by
              rw [Finset.prod_fin_eq_prod_range]
              refine Finset.prod_congr rfl ?_
              intro m hm
              have hm' : m < N := Finset.mem_range.mp hm
              simp [hm', ε]
              simpa [ε] using
                (lambda_succ_eq_inv_pow N K hK (Fin.succ ⟨m, hm'⟩))
            have hleftNum :
                (∏ m ∈ Finset.range i.1, ε ^ (N - (m + 1)))
                  = (ε ^ (N - i.1)) ^ i.1 * ∏ m ∈ Finset.range i.1, ε ^ m := by
              calc
                (∏ m ∈ Finset.range i.1, ε ^ (N - (m + 1)))
                    = ∏ m ∈ Finset.range i.1, (ε ^ (N - i.1)) * ε ^ (i.1 - (m + 1)) := by
                        refine Finset.prod_congr rfl ?_
                        intro m hm
                        have hm' : m < i.1 := Finset.mem_range.mp hm
                        rw [← pow_add]
                        congr
                        omega
                _ = (∏ _m ∈ Finset.range i.1, ε ^ (N - i.1)) *
                      ∏ m ∈ Finset.range i.1, ε ^ (i.1 - (m + 1)) := by
                        rw [Finset.prod_mul_distrib]
                _ = (ε ^ (N - i.1)) ^ i.1 *
                      ∏ m ∈ Finset.range i.1, ε ^ (i.1 - (m + 1)) := by
                        simp [Finset.prod_const]
                _ = (ε ^ (N - i.1)) ^ i.1 * ∏ m ∈ Finset.range i.1, ε ^ m := by
                      congr 1
                      calc
                        (∏ m ∈ Finset.range i.1, ε ^ (i.1 - (m + 1)))
                            = ∏ m ∈ Finset.range i.1, ε ^ (i.1 - 1 - m) := by
                                refine Finset.prod_congr rfl ?_
                                intro m hm
                                have hm' : m < i.1 := Finset.mem_range.mp hm
                                have hsub : i.1 - (m + 1) = i.1 - 1 - m := by
                                  omega
                                simpa [hsub]
                        _ = ∏ m ∈ Finset.range i.1, ε ^ m := by
                              simpa using
                                (Finset.prod_range_reflect (fun m => ε ^ m) i.1)
            have hrightNum :
                (∏ m ∈ Finset.range (N - i.1), ε ^ (N - i.1 - (m + 1)))
                  = ∏ m ∈ Finset.range (N - i.1), ε ^ (N - i.1 - (m + 1)) := rfl
            have hdenTail :
                (∏ x : Fin N,
                    |lambda N K i.castSucc.succ - lambda N K (i.castSucc.succ.succAbove x.succ)|)
                  = ((∏ m ∈ Finset.range i.1,
                        ε ^ (N - i.1) * (1 - ε ^ (i.1 - m))) *
                      ∏ m ∈ Finset.range (N - i.1),
                        ε ^ (N - i.1 - (m + 1)) * (1 - ε ^ (m + 1))) := by
              rw [Finset.prod_fin_eq_prod_range]
              have hsplit :
                  (∏ n ∈ Finset.range N,
                      if h : n < N then
                        |lambda N K i.castSucc.succ -
                            lambda N K (i.castSucc.succ.succAbove (Fin.succ ⟨n, h⟩))|
                      else 1)
                    = (∏ n ∈ Finset.range i.1,
                        if h : n < N then
                          |lambda N K i.castSucc.succ -
                              lambda N K (i.castSucc.succ.succAbove (Fin.succ ⟨n, h⟩))|
                        else 1) *
                      ∏ n ∈ Finset.range (N - i.1),
                        if h : i.1 + n < N then
                          |lambda N K i.castSucc.succ -
                              lambda N K (i.castSucc.succ.succAbove (Fin.succ ⟨i.1 + n, h⟩))|
                        else 1 := by
                simpa [show i.1 + (N - i.1) = N by omega] using
                  (Finset.prod_range_add
                    (f := fun n =>
                      if h : n < N then
                        |lambda N K i.castSucc.succ -
                            lambda N K (i.castSucc.succ.succAbove (Fin.succ ⟨n, h⟩))|
                      else 1)
                    i.1 (N - i.1))
              rw [hsplit]
              congr 1
              · refine Finset.prod_congr rfl ?_
                intro m hm
                have hm' : m < i.1 := Finset.mem_range.mp hm
                have hmN : m < N := by omega
                have hlt : (⟨m, hmN⟩ : Fin N) < i := by
                  change m < i.1
                  exact hm'
                simp [hmN]
                have hidx :
                    i.castSucc.succ.succAbove ((⟨m, hmN⟩ : Fin N).succ)
                      = (((⟨m, hmN⟩ : Fin N).castSucc).succ) := by
                  apply Fin.ext
                  simpa using
                    congrArg Fin.val <|
                      (Fin.succ_succAbove_succ i.castSucc ⟨m, hmN⟩).trans <|
                        by rw [Fin.succAbove_castSucc_of_lt i ⟨m, hmN⟩ hlt]
                have hleft_lambda :
                    lambda N K (((⟨m, hmN⟩ : Fin N).castSucc).succ)
                      = ε ^ (N - m) := by
                  simpa [ε] using
                    (lambda_succ_eq_inv_pow N K hK
                      ((⟨m, hmN⟩ : Fin N).castSucc))
                change
                  |lambda N K i.castSucc.succ -
                      lambda N K (i.castSucc.succ.succAbove ((⟨m, hmN⟩ : Fin N).succ))|
                    = ε ^ (N - i.1) * (1 - ε ^ (i.1 - m))
                rw [hidx, hli, hleft_lambda]
                have hmle : m ≤ i.1 := Nat.le_of_lt hm'
                have hsub : N - m = N - i.1 + (i.1 - m) := by
                  omega
                calc
                  |ε ^ (N - i.1) - ε ^ (N - m)| = |ε ^ (N - i.1) - ε ^ (N - i.1) * ε ^ (i.1 - m)| := by
                    rw [hsub, pow_add]
                  _ = |ε ^ (N - i.1) * (1 - ε ^ (i.1 - m))| := by ring_nf
                  _ = ε ^ (N - i.1) * (1 - ε ^ (i.1 - m)) := by
                    have hpow_le : ε ^ (i.1 - m) ≤ 1 := pow_le_one₀ hε_nonneg hε_le_one
                    have hnonneg : 0 ≤ ε ^ (N - i.1) * (1 - ε ^ (i.1 - m)) := by
                      exact mul_nonneg (pow_nonneg hε_nonneg _) (sub_nonneg.mpr hpow_le)
                    rw [abs_of_nonneg hnonneg]
              · refine Finset.prod_congr rfl ?_
                intro m hm
                have hm' : m < N - i.1 := Finset.mem_range.mp hm
                have hmN : i.1 + m < N := by omega
                have hle : i ≤ (⟨i.1 + m, hmN⟩ : Fin N) := by
                  change i.1 ≤ i.1 + m
                  omega
                simp [hmN]
                have hidx :
                    i.castSucc.succ.succAbove ((⟨i.1 + m, hmN⟩ : Fin N).succ)
                      = ((⟨i.1 + m, hmN⟩ : Fin N).succ).succ := by
                  apply Fin.ext
                  simpa using
                    congrArg Fin.val <|
                      (Fin.succ_succAbove_succ i.castSucc ⟨i.1 + m, hmN⟩).trans <|
                        by rw [Fin.succAbove_castSucc_of_le i ⟨i.1 + m, hmN⟩ hle]
                have hright_lambda :
                    lambda N K (((⟨i.1 + m, hmN⟩ : Fin N).succ).succ)
                      = ε ^ (N - i.1 - (m + 1)) := by
                  have hsubexp : N - (i.1 + m + 1) = N - i.1 - (m + 1) := by
                    omega
                  simpa [ε] using
                    (lambda_succ_eq_inv_pow N K hK
                      ((⟨i.1 + m, hmN⟩ : Fin N).succ)).trans (by simp [hsubexp])
                change
                  |lambda N K i.castSucc.succ -
                      lambda N K (i.castSucc.succ.succAbove ((⟨i.1 + m, hmN⟩ : Fin N).succ))|
                    = ε ^ (N - i.1 - (m + 1)) * (1 - ε ^ (m + 1))
                rw [hidx, hli, hright_lambda]
                have hmle : m + 1 ≤ N - i.1 := by omega
                have hsub : N - i.1 = N - i.1 - (m + 1) + (m + 1) := by
                  omega
                calc
                  |ε ^ (N - i.1) - ε ^ (N - i.1 - (m + 1))|
                      = |ε ^ (N - i.1 - (m + 1) + (m + 1))
                          - ε ^ (N - i.1 - (m + 1))| := by
                            congr
                  _ = |ε ^ (N - i.1 - (m + 1)) * ε ^ (m + 1)
                          - ε ^ (N - i.1 - (m + 1))| := by
                            rw [pow_add]
                  _ = |ε ^ (N - i.1 - (m + 1)) * (ε ^ (m + 1) - 1)| := by ring_nf
                  _ = ε ^ (N - i.1 - (m + 1)) * (1 - ε ^ (m + 1)) := by
                    have hpow_le : ε ^ (m + 1) ≤ 1 := pow_le_one₀ hε_nonneg hε_le_one
                    have hnonneg : 0 ≤ ε ^ (N - i.1 - (m + 1)) * (1 - ε ^ (m + 1)) := by
                      exact mul_nonneg (pow_nonneg hε_nonneg _) (sub_nonneg.mpr hpow_le)
                    have hnonpos :
                        ε ^ (N - i.1 - (m + 1)) * (ε ^ (m + 1) - 1) ≤ 0 := by
                      have hneg :
                          ε ^ (N - i.1 - (m + 1)) * (ε ^ (m + 1) - 1)
                            = -(ε ^ (N - i.1 - (m + 1)) * (1 - ε ^ (m + 1))) := by
                        ring
                      rw [hneg]
                      exact neg_nonpos.mpr hnonneg
                    rw [abs_of_nonpos hnonpos]
                    ring
            rw [hfirst, hzeroDen, hnumTail, hdenTail]
            have hsplitNum :
                (∏ m ∈ Finset.range N, ε ^ (N - (m + 1)))
                  = (∏ m ∈ Finset.range i.1, ε ^ (N - (m + 1))) *
                    ∏ m ∈ Finset.range (N - i.1), ε ^ (N - i.1 - (m + 1)) := by
              calc
                (∏ m ∈ Finset.range N, ε ^ (N - (m + 1)))
                    = (∏ m ∈ Finset.range i.1, ε ^ (N - (m + 1))) *
                        ∏ m ∈ Finset.range (N - i.1), ε ^ (N - (i.1 + (m + 1))) := by
                          simpa [show i.1 + (N - i.1) = N by omega, Nat.add_assoc] using
                            (Finset.prod_range_add (f := fun m => ε ^ (N - (m + 1))) i.1 (N - i.1))
                _ = (∏ m ∈ Finset.range i.1, ε ^ (N - (m + 1))) *
                        ∏ m ∈ Finset.range (N - i.1), ε ^ (N - i.1 - (m + 1)) := by
                      congr 1
                      refine Finset.prod_congr rfl ?_
                      intro m hm
                      have hsubexp : N - (i.1 + (m + 1)) = N - i.1 - (m + 1) := by
                        omega
                      simpa [hsubexp]
            rw [hsplitNum, hleftNum]
            have hrightProd :
                (∏ m ∈ Finset.range (N - i.1),
                    ε ^ (N - i.1 - (m + 1)) * (1 - ε ^ (m + 1)))
                  = (∏ m ∈ Finset.range (N - i.1), ε ^ (N - i.1 - (m + 1))) *
                      ∏ m ∈ Finset.range (N - i.1), (1 - ε ^ (m + 1)) := by
              rw [Finset.prod_mul_distrib]
            rw [hrightProd]
            have hleftProd :
                (∏ m ∈ Finset.range i.1, ε ^ (N - i.1) * (1 - ε ^ (i.1 - m)))
                  = (ε ^ (N - i.1)) ^ i.1 *
                      ∏ m ∈ Finset.range i.1, (1 - ε ^ (m + 1)) := by
              calc
                (∏ m ∈ Finset.range i.1, ε ^ (N - i.1) * (1 - ε ^ (i.1 - m)))
                    = (∏ _m ∈ Finset.range i.1, ε ^ (N - i.1)) *
                        ∏ m ∈ Finset.range i.1, (1 - ε ^ (i.1 - m)) := by
                          rw [Finset.prod_mul_distrib]
                _ = (ε ^ (N - i.1)) ^ i.1 *
                        ∏ m ∈ Finset.range i.1, (1 - ε ^ (i.1 - m)) := by
                          simp [Finset.prod_const]
                _ = (ε ^ (N - i.1)) ^ i.1 *
                        ∏ m ∈ Finset.range i.1, (1 - ε ^ (m + 1)) := by
                      congr 1
                      calc
                        (∏ m ∈ Finset.range i.1, (1 - ε ^ (i.1 - m)))
                            = ∏ m ∈ Finset.range i.1, (1 - ε ^ (i.1 - 1 - m + 1)) := by
                                refine Finset.prod_congr rfl ?_
                                intro m hm
                                have hm' : m < i.1 := Finset.mem_range.mp hm
                                have hsub : i.1 - m = i.1 - 1 - m + 1 := by
                                  omega
                                simpa [hsub]
                        _ = ∏ m ∈ Finset.range i.1, (1 - ε ^ (m + 1)) := by
                              simpa using
                                (Finset.prod_range_reflect (fun m => 1 - ε ^ (m + 1)) i.1)
            rw [hleftProd]
            have hrightTerms :
                (∏ m ∈ Finset.range (N - i.1), (1 - ε ^ (m + 1)))
                  = (∏ m ∈ Finset.range (N - i.1 - 1), (1 - ε ^ (m + 1))) *
                      (1 - ε ^ (N - i.1)) := by
              simpa [Nat.sub_add_cancel (show 1 ≤ N - i.1 by omega)] using
                (Finset.prod_range_succ (fun m => 1 - ε ^ (m + 1)) (N - i.1 - 1))
            rw [hrightTerms]
            have hrightPowNonzero :
                (∏ m ∈ Finset.range (N - i.1), ε ^ (N - i.1 - (m + 1))) ≠ 0 := by
              refine Finset.prod_ne_zero_iff.mpr ?_
              intro m hm
              exact pow_ne_zero _ hε_ne_zero
            have hleftPowNonzero : (ε ^ (N - i.1)) ^ i.1 ≠ 0 := by
              exact pow_ne_zero _ (pow_ne_zero _ hε_ne_zero)
            have hpowTail :
                (∏ m ∈ Finset.range i.1, ε ^ m) = ε ^ (i.1 * (i.1 - 1) / 2) := by
              simpa [Finset.sum_range_id] using
                (Finset.prod_pow_eq_pow_sum (Finset.range i.1) (fun m => m) ε)
            rw [hpowTail]
            set P : ℝ := ∏ m ∈ Finset.range i.1, (1 - ε ^ (m + 1))
            set Q : ℝ := ∏ m ∈ Finset.range (N - i.1 - 1), (1 - ε ^ (m + 1))
            set D : ℝ := (1 - ε ^ (N - i.1)) * P * Q
            have hk1 : (1 : ℝ) < K := by
              exact_mod_cast (show 1 < K by omega)
            have hε_lt_one : ε < 1 := by
              dsimp [ε]
              exact inv_lt_one_of_one_lt₀ hk1
            have hfactor_nonzero : ∀ n : ℕ, 1 ≤ n → 1 - ε ^ n ≠ 0 := by
              intro n hn
              have hpow_lt_one : ε ^ n < 1 := by
                exact pow_lt_one₀ hε_nonneg hε_lt_one (Nat.ne_of_gt hn)
              exact sub_ne_zero.mpr (ne_of_gt hpow_lt_one)
            have hleftTermsNonzero :
                (∏ m ∈ Finset.range i.1, (1 - ε ^ (m + 1))) ≠ 0 := by
              refine Finset.prod_ne_zero_iff.mpr ?_
              intro m hm
              exact hfactor_nonzero (m + 1) (Nat.succ_le_succ (Nat.zero_le _))
            have hrightTermsNonzero :
                Q ≠ 0 := by
              refine Finset.prod_ne_zero_iff.mpr ?_
              intro m hm
              exact hfactor_nonzero (m + 1) (Nat.succ_le_succ (Nat.zero_le _))
            have hendpointNonzero : 1 - ε ^ (N - i.1) ≠ 0 := by
              exact hfactor_nonzero (N - i.1) (Nat.succ_le_of_lt (Nat.sub_pos_of_lt i.is_lt))
            have hεpowNonzero : ε ^ (N - i.1) ≠ 0 := by
              exact pow_ne_zero _ hε_ne_zero
            have hD_nonzero : D ≠ 0 := by
              dsimp [D]
              exact mul_ne_zero (mul_ne_zero hendpointNonzero hleftTermsNonzero) hrightTermsNonzero
            have hcancel :
                ε ^ N *
                    ((ε ^ (N - i.1)) ^ i.1 *
                      (ε ^ (i.1 * (i.1 - 1) / 2) *
                        ∏ m ∈ Finset.range (N - i.1), ε ^ (N - i.1 - (m + 1)))) /
                    (ε ^ (N - i.1) *
                      ((ε ^ (N - i.1)) ^ i.1 *
                        (P *
                            ((∏ m ∈ Finset.range (N - i.1), ε ^ (N - i.1 - (m + 1))) *
                              (Q * (1 - ε ^ (N - i.1)))))))
                  = ε ^ N * ε ^ (i.1 * (i.1 - 1) / 2) / (ε ^ (N - i.1) * D) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              simp [D, mul_assoc, mul_left_comm, mul_comm, mul_inv_rev,
                hleftPowNonzero, hrightPowNonzero]
            have hpowMain :
                ε ^ N * ε ^ (i.1 * (i.1 - 1) / 2)
                  = ε ^ (N - i.1) * ε ^ (i.1 * (i.1 + 1) / 2) := by
              rw [← pow_add, ← pow_add]
              have htri :
                  i.1 * (i.1 + 1) / 2 = i.1 * (i.1 - 1) / 2 + i.1 := by
                simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
                  (Nat.triangle_succ i.1)
              have hexp :
                  N + i.1 * (i.1 - 1) / 2 = N - i.1 + i.1 * (i.1 + 1) / 2 := by
                rw [htri]
                omega
              simpa [hexp]
            calc
              ε ^ N *
                  ((ε ^ (N - i.1)) ^ i.1 * ε ^ (i.1 * (i.1 - 1) / 2) *
                    ∏ m ∈ Finset.range (N - i.1), ε ^ (N - i.1 - (m + 1))) /
                  (ε ^ (N - i.1) *
                    ((ε ^ (N - i.1)) ^ i.1 * P *
                      ((∏ m ∈ Finset.range (N - i.1), ε ^ (N - i.1 - (m + 1))) *
                        (Q * (1 - ε ^ (N - i.1))))))
                  = ε ^ N * ε ^ (i.1 * (i.1 - 1) / 2) / (ε ^ (N - i.1) * D) := by
                      simpa [mul_assoc, mul_left_comm, mul_comm] using hcancel
              _
                  = (ε ^ (N - i.1) * ε ^ (i.1 * (i.1 + 1) / 2)) / (ε ^ (N - i.1) * D) := by
                      rw [hpowMain]
              _ = ε ^ (i.1 * (i.1 + 1) / 2) / D := by
                    exact mul_div_mul_left _ _ hεpowNonzero
              _ = (((K : ℝ) ^ (i.1 * (i.1 + 1) / 2))⁻¹) /
                    (((1 - (((K : ℝ) ^ (N - i.1))⁻¹))
                        * ∏ m ∈ Finset.range i.1, (1 - (((K : ℝ) ^ (m + 1))⁻¹)))
                        * ∏ m ∈ Finset.range (N - i.1 - 1), (1 - (((K : ℝ) ^ (m + 1))⁻¹))) := by
                    simp [D, P, Q, ε, inv_pow, mul_left_comm, mul_comm]

/-- The product `Δ_s` tends to `1`. -/
private theorem Delta_last_tendsto_one (N : ℕ) :
    Filter.Tendsto (fun K : ℕ => Delta N K (Fin.last (N + 1))) Filter.atTop (𝓝 1) := by
  have hterm : ∀ m ∈ Finset.range N,
      Filter.Tendsto (fun K : ℕ => 1 - ((K : ℝ)⁻¹) ^ (m + 1)) Filter.atTop (𝓝 1) := by
    intro m hm
    simpa using Filter.Tendsto.const_sub 1
      ((tendsto_inv_atTop_nhds_zero_nat :
        Filter.Tendsto (fun K : ℕ => ((K : ℝ)⁻¹ : ℝ)) Filter.atTop (𝓝 0)).pow (m + 1))
  have hprod : Filter.Tendsto
      (fun K : ℕ => (∏ m ∈ Finset.range N, (1 - ((K : ℝ)⁻¹) ^ (m + 1))))
      Filter.atTop (𝓝 (∏ m ∈ Finset.range N, (1 : ℝ))) := by
    exact tendsto_finset_prod _ hterm
  have hK : ∀ᶠ K in Filter.atTop, 2 ≤ K := Filter.eventually_ge_atTop 2
  have hEq : ∀ᶠ K in Filter.atTop,
      Delta N K (Fin.last (N + 1))
        = ∏ m ∈ Finset.range N, (1 - ((K : ℝ)⁻¹) ^ (m + 1)) := by
    filter_upwards [hK] with K hK
    rw [Delta_last_eq_prod N K hK]
  exact (Filter.tendsto_congr' hEq).mpr <| by
    simpa [Finset.prod_const_one] using hprod

/-- Exact finite-product formula for the first Vandermonde factor. -/
private theorem Delta_zero_eq_inv_pow (N K : ℕ) (hK : 2 ≤ K) :
    Delta N K 0 = ((K : ℝ)⁻¹) ^ (N * (N + 1) / 2) := by
  let ε : ℝ := (K : ℝ)⁻¹
  unfold Delta
  change (∏ j ∈ (Finset.univ.erase (0 : Fin (N + 2)) : Finset (Fin (N + 2))),
      |lambda N K 0 - lambda N K j|)
    = ((K : ℝ)⁻¹) ^ (N * (N + 1) / 2)
  rw [show (Finset.univ.erase (0 : Fin (N + 2)) : Finset (Fin (N + 2))) =
      Finset.univ.map ⟨Fin.succ, Fin.succ_injective (n := N + 1)⟩ by
        simp [Fin.univ_succ (N + 1)]]
  simp [lambda_zero]
  have habs :
      (∏ x : Fin (N + 1), |lambda N K x.succ|) = ∏ x : Fin (N + 1), lambda N K x.succ := by
    refine Fintype.prod_congr (fun x : Fin (N + 1) => |lambda N K x.succ|)
      (fun x : Fin (N + 1) => lambda N K x.succ) ?_
    intro x
    change |lambda N K x.succ| = lambda N K x.succ
    rw [abs_of_nonneg]
    unfold lambda
    exact div_nonneg (by exact_mod_cast Nat.zero_le (exponent N K x.succ))
      (by exact_mod_cast Nat.zero_le (d N K))
  rw [habs]
  rw [Fin.prod_univ_succ]
  have hfirst : lambda N K (Fin.succ (0 : Fin (N + 1))) = ε ^ N := by
    simpa [ε] using lambda_succ_eq_inv_pow N K hK (0 : Fin (N + 1))
  have htail :
      (∏ x : Fin N, lambda N K x.succ.succ)
        = ∏ m ∈ Finset.range N, ε ^ (N - (m + 1)) := by
    rw [Finset.prod_fin_eq_prod_range]
    refine Finset.prod_congr rfl ?_
    intro m hm
    have hm' : m < N := Finset.mem_range.mp hm
    simp [hm']
    simpa [ε] using lambda_succ_eq_inv_pow N K hK (Fin.succ ⟨m, hm'⟩)
  have hreflect :
      (∏ m ∈ Finset.range N, ε ^ (N - (m + 1)))
        = ∏ m ∈ Finset.range N, ε ^ m := by
    calc
      (∏ m ∈ Finset.range N, ε ^ (N - (m + 1)))
          = ∏ m ∈ Finset.range N, ε ^ (N - 1 - m) := by
              refine Finset.prod_congr rfl ?_
              intro m hm
              have hm' : m < N := Finset.mem_range.mp hm
              have hsub : N - (m + 1) = N - 1 - m := by omega
              simpa [hsub]
      _ = ∏ m ∈ Finset.range N, ε ^ m := by
            simpa using (Finset.prod_range_reflect (fun m => ε ^ m) N)
  have hsum :
      (∏ m ∈ Finset.range N, ε ^ m) = ε ^ (N * (N - 1) / 2) := by
    simpa [Finset.sum_range_id] using
      (Finset.prod_pow_eq_pow_sum (Finset.range N) (fun m => m) ε)
  rw [hfirst, htail, hreflect, hsum, ← pow_add]
  have htri : N + N * (N - 1) / 2 = N * (N + 1) / 2 := by
    simpa [add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.triangle_succ N).symm
  rw [htri]
  simp [ε, inv_pow]

private theorem tau_eq_log_ratio (N K : ℕ) (hK : 2 ≤ K) :
    tau N K = Real.log (Delta N K 0 / (2 * Delta N K (Fin.last (N + 1)))) := by
  have hΔ0 : 0 < Delta N K 0 := Delta_pos N K hK 0
  have hΔs : 0 < Delta N K (Fin.last (N + 1)) := Delta_pos N K hK (Fin.last (N + 1))
  have hA1 : 0 < A1 N K := by
    unfold A1
    positivity
  calc
    tau N K = -2 * (Real.log (Real.sqrt 2) + Real.log (A1 N K)) := by
      unfold tau T
      rw [one_div, Real.log_inv, Real.log_mul (by positivity) hA1.ne']
      ring
    _ = -Real.log 2 - Real.log (Delta N K (Fin.last (N + 1)) / Delta N K 0) := by
      rw [show Real.log (Real.sqrt 2) = Real.log 2 / 2 by
        rw [Real.log_sqrt (by positivity)]]
      unfold A1
      rw [Real.log_sqrt (by positivity)]
      ring
    _ = -Real.log 2 - (Real.log (Delta N K (Fin.last (N + 1))) - Real.log (Delta N K 0)) := by
      rw [Real.log_div hΔs.ne' hΔ0.ne']
    _ = Real.log (Delta N K 0) - (Real.log 2 + Real.log (Delta N K (Fin.last (N + 1)))) := by
      ring
    _ = Real.log (Delta N K 0) - Real.log (2 * Delta N K (Fin.last (N + 1))) := by
      rw [Real.log_mul (by norm_num) hΔs.ne']
    _ = Real.log (Delta N K 0 / (2 * Delta N K (Fin.last (N + 1)))) := by
      rw [Real.log_div hΔ0.ne' (by positivity)]

/-- For the first middle term one has `R_1 → 1`. -/
private theorem Rcoeff_zero_tendsto_one (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto (fun K : ℕ => Rcoeff N K ⟨0, by omega⟩) Filter.atTop (𝓝 1) := by
  let i0 : Fin N := ⟨0, by omega⟩
  have hK : ∀ᶠ K in Filter.atTop, 2 ≤ K := Filter.eventually_ge_atTop 2
  have hEq : ∀ᶠ K in Filter.atTop, Rcoeff N K i0 = (Delta N K (Fin.last (N + 1)))⁻¹ := by
    filter_upwards [hK] with K hK
    rw [Rcoeff_eq_main_term N K hK i0, Delta_last_eq_prod N K hK]
    have hprod :
        (∏ m ∈ Finset.range N, (1 - ((K : ℝ)⁻¹ ^ (m + 1))))
          = (∏ m ∈ Finset.range (N - 1), (1 - ((K : ℝ)⁻¹ ^ (m + 1)))) *
              (1 - ((K : ℝ)⁻¹ ^ N)) := by
      rw [show N = (N - 1) + 1 by omega, Finset.prod_range_succ]
      simp
    rw [hprod]
    simp [i0, div_eq_mul_inv, inv_pow, mul_comm]
  have hΔ : Filter.Tendsto (fun K : ℕ => Delta N K (Fin.last (N + 1))) Filter.atTop (𝓝 1) :=
    Delta_last_tendsto_one N
  exact (Filter.tendsto_congr' hEq).mpr (by simpa using hΔ.inv₀ one_ne_zero)

/-- For higher middle terms one has `R_i → 0`. -/
private theorem Rcoeff_succ_tendsto_zero (N : ℕ) (i : Fin N) (hi : 1 ≤ i.1) :
    Filter.Tendsto (fun K : ℕ => Rcoeff N K i) Filter.atTop (𝓝 0) := by
  have hK : ∀ᶠ K in Filter.atTop, 2 ≤ K := Filter.eventually_ge_atTop 2
  have hEq : ∀ᶠ K in Filter.atTop,
      Rcoeff N K i
        = (((K : ℝ) ^ (i.1 * (i.1 + 1) / 2))⁻¹)
            / (((1 - (((K : ℝ) ^ (N - i.1))⁻¹))
                * ∏ m ∈ Finset.range i.1, (1 - (((K : ℝ) ^ (m + 1))⁻¹)))
                * ∏ m ∈ Finset.range (N - i.1 - 1), (1 - (((K : ℝ) ^ (m + 1))⁻¹))) := by
    filter_upwards [hK] with K hK
    rw [Rcoeff_eq_main_term N K hK i]
  have hpow : Filter.Tendsto
      (fun K : ℕ => ((K : ℝ)⁻¹) ^ (i.1 * (i.1 + 1) / 2)) Filter.atTop (𝓝 0) := by
    have hpos : 0 < i.1 * (i.1 + 1) / 2 := by
      have htwo : 2 ≤ i.1 * (i.1 + 1) := by
        nlinarith [hi]
      exact Nat.div_pos htwo (by decide)
    simpa [hpos.ne'] using
      ((tendsto_inv_atTop_nhds_zero_nat :
        Filter.Tendsto (fun K : ℕ => ((K : ℝ)⁻¹ : ℝ)) Filter.atTop (𝓝 0)).pow
        (i.1 * (i.1 + 1) / 2))
  have hden : Filter.Tendsto
    (fun K : ℕ => (((1 - ((K : ℝ)⁻¹) ^ (N - i.1))
        * ∏ m ∈ Finset.range i.1, (1 - ((K : ℝ)⁻¹) ^ (m + 1)))
        * ∏ m ∈ Finset.range (N - i.1 - 1), (1 - ((K : ℝ)⁻¹) ^ (m + 1))))
    Filter.atTop (𝓝 1) := by
    have hterm : ∀ m,
        Filter.Tendsto (fun K : ℕ => 1 - ((K : ℝ)⁻¹) ^ (m + 1)) Filter.atTop (𝓝 1) := by
      intro m
      simpa using Filter.Tendsto.const_sub 1
        ((tendsto_inv_atTop_nhds_zero_nat :
          Filter.Tendsto (fun K : ℕ => ((K : ℝ)⁻¹ : ℝ)) Filter.atTop (𝓝 0)).pow (m + 1))
    have hleft : Filter.Tendsto
        (fun K : ℕ => (1 - ((K : ℝ)⁻¹) ^ (N - i.1))) Filter.atTop (𝓝 1) := by
      have hsub : N - i.1 - 1 + 1 = N - i.1 := by
        omega
      simpa [hsub] using hterm (N - i.1 - 1)
    have hprod1 : Filter.Tendsto
        (fun K : ℕ => (∏ m ∈ Finset.range i.1, (1 - ((K : ℝ)⁻¹) ^ (m + 1))))
        Filter.atTop (𝓝 1) := by
      simpa [Finset.prod_const_one] using tendsto_finset_prod (s := Finset.range i.1)
        (fun m hm => hterm m)
    have hprod2 : Filter.Tendsto
        (fun K : ℕ => (∏ m ∈ Finset.range (N - i.1 - 1), (1 - ((K : ℝ)⁻¹) ^ (m + 1))))
        Filter.atTop (𝓝 1) := by
      simpa [Finset.prod_const_one] using tendsto_finset_prod (s := Finset.range (N - i.1 - 1))
        (fun m hm => hterm m)
    simpa [mul_assoc] using hleft.mul (hprod1.mul hprod2)
  exact (Filter.tendsto_congr' hEq).mpr <| by
    have hdiv : Filter.Tendsto
        (fun K : ℕ =>
          (((K : ℝ)⁻¹) ^ (i.1 * (i.1 + 1) / 2)) /
            (((1 - ((K : ℝ)⁻¹ ^ (N - i.1)))
                * ∏ m ∈ Finset.range i.1, (1 - ((K : ℝ)⁻¹ ^ (m + 1))))
                * ∏ m ∈ Finset.range (N - i.1 - 1), (1 - ((K : ℝ)⁻¹ ^ (m + 1)))))
        Filter.atTop (𝓝 0) := by
      simpa [Pi.div_apply] using Filter.Tendsto.div hpow hden one_ne_zero
    simpa [inv_pow] using hdiv

/-- The small correction factor `exp (- λ_i τ)` tends to `1` for every middle index. -/
private theorem small_power_tendsto_one (N : ℕ) (i : Fin N) :
    Filter.Tendsto (fun K : ℕ => Real.exp (-(lambda N K (midIdx i)) * tau N K))
      Filter.atTop (𝓝 1) := by
  have hp : 0 < N - i.1 := Nat.sub_pos_of_lt i.is_lt
  have hlogK' : Filter.Tendsto
      (fun K : ℕ => Real.log (K : ℝ) / (K : ℝ) ^ ((N - i.1 : ℕ) : ℝ))
      Filter.atTop (𝓝 0) := by
    have hpos : 0 < ((N - i.1 : ℕ) : ℝ) := by exact_mod_cast hp
    simpa [Function.comp] using
      (((isLittleO_log_rpow_atTop hpos).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop)
  have hlogK : Filter.Tendsto (fun K : ℕ => Real.log (K : ℝ) / (K : ℝ) ^ (N - i.1))
      Filter.atTop (𝓝 0) := by
    have hEq :
        (fun K : ℕ => Real.log (K : ℝ) / (K : ℝ) ^ ((N - i.1 : ℕ) : ℝ)) =ᶠ[Filter.atTop]
          (fun K : ℕ => Real.log (K : ℝ) / (K : ℝ) ^ (N - i.1)) := by
      filter_upwards with K
      rw [Real.rpow_natCast]
    exact (Filter.tendsto_congr' hEq).mp hlogK'
  have hlamPow : Filter.Tendsto
      (fun K : ℕ => ((K : ℝ)⁻¹) ^ (N - i.1)) Filter.atTop (𝓝 0) := by
    simpa [hp.ne'] using
      ((tendsto_inv_atTop_nhds_zero_nat :
        Filter.Tendsto (fun K : ℕ => ((K : ℝ)⁻¹ : ℝ)) Filter.atTop (𝓝 0)).pow (N - i.1))
  have hlam : Filter.Tendsto (fun K : ℕ => lambda N K (midIdx i)) Filter.atTop (𝓝 0) := by
    have hK : ∀ᶠ K in Filter.atTop, 2 ≤ K := Filter.eventually_ge_atTop 2
    have hEq : ∀ᶠ K in Filter.atTop,
        lambda N K (midIdx i) = ((K : ℝ)⁻¹) ^ (N - i.1) := by
      filter_upwards [hK] with K hK
      simpa [midIdx_eq_succ_castSucc] using lambda_succ_eq_inv_pow N K hK i.castSucc
    exact (Filter.tendsto_congr' hEq).mpr hlamPow
  have hlog2Delta : Filter.Tendsto
      (fun K : ℕ => Real.log (2 * Delta N K (Fin.last (N + 1)))) Filter.atTop (𝓝 (Real.log 2)) := by
    have h2Delta : Filter.Tendsto
        (fun K : ℕ => 2 * Delta N K (Fin.last (N + 1))) Filter.atTop (𝓝 (2 : ℝ)) := by
      simpa using (Delta_last_tendsto_one N).const_mul (2 : ℝ)
    simpa using (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp h2Delta
  have hτsmall : Filter.Tendsto
      (fun K : ℕ => (lambda N K (midIdx i)) * tau N K) Filter.atTop (𝓝 0) := by
    have hK : ∀ᶠ K in Filter.atTop, 2 ≤ K := Filter.eventually_ge_atTop 2
    have hEq : ∀ᶠ K in Filter.atTop,
        (lambda N K (midIdx i)) * tau N K
          = -(((N * (N + 1) / 2 : ℕ) : ℝ) * (Real.log (K : ℝ) / (K : ℝ) ^ (N - i.1)))
            - (lambda N K (midIdx i)) * Real.log (2 * Delta N K (Fin.last (N + 1))) := by
      filter_upwards [hK] with K hK
      rw [tau_eq_log_ratio N K hK, Delta_zero_eq_inv_pow N K hK,
        midIdx_eq_succ_castSucc, lambda_succ_eq_inv_pow N K hK i.castSucc]
      simp only [Fin.val_castSucc]
      have hnum_ne : ((K : ℝ)⁻¹) ^ (N * (N + 1) / 2) ≠ 0 := by
        exact pow_ne_zero _ (inv_ne_zero (by exact_mod_cast (show K ≠ 0 by omega)))
      have hden_ne : 2 * Delta N K (Fin.last (N + 1)) ≠ 0 := by
        exact mul_ne_zero (by norm_num) (Delta_pos N K hK (Fin.last (N + 1))).ne'
      rw [Real.log_div hnum_ne hden_ne]
      rw [show ((K : ℝ)⁻¹) ^ (N * (N + 1) / 2) =
          ((K : ℝ)⁻¹) ^ (((N * (N + 1) / 2 : ℕ) : ℝ)) by rw [Real.rpow_natCast]]
      rw [Real.log_rpow (by positivity : 0 < ((K : ℝ)⁻¹))
        (((N * (N + 1) / 2 : ℕ) : ℝ))]
      rw [Real.log_inv, div_eq_mul_inv, inv_pow]
      ring
    have hmain1 : Filter.Tendsto
        (fun K : ℕ =>
          -(((N * (N + 1) / 2 : ℕ) : ℝ) * (Real.log (K : ℝ) / (K : ℝ) ^ (N - i.1))))
        Filter.atTop (𝓝 0) := by
      simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using
        hlogK.const_mul (-(((N * (N + 1) / 2 : ℕ) : ℝ)))
    have hmain2 : Filter.Tendsto
        (fun K : ℕ => (lambda N K (midIdx i)) * Real.log (2 * Delta N K (Fin.last (N + 1))))
        Filter.atTop (𝓝 0) := by
      simpa using hlam.mul hlog2Delta
    exact (Filter.tendsto_congr' hEq).mpr (by simpa using hmain1.sub hmain2)
  have hN' : Filter.Tendsto
      (fun K : ℕ => -((lambda N K (midIdx i)) * tau N K)) Filter.atTop (𝓝 0) := by
    simpa using hτsmall.neg
  have hExpEq :
      (fun K : ℕ => Real.exp (-(lambda N K (midIdx i)) * tau N K)) =ᶠ[Filter.atTop]
        (fun K : ℕ => Real.exp (-((lambda N K (midIdx i)) * tau N K))) := by
    filter_upwards with K
    rw [neg_mul]
  have hexp : Filter.Tendsto (fun K : ℕ => Real.exp (-(lambda N K (midIdx i)) * tau N K))
      Filter.atTop (𝓝 (Real.exp 0)) := by
    exact (Filter.tendsto_congr' hExpEq).mpr
      (Real.continuous_exp.continuousAt.tendsto.comp hN')
  simpa using hexp

/--
Asymptotic proposition `p990:prop:height` from the paper.

**Important:** the paper assumes `1 ≤ N`. The statement without this hypothesis is false for
`N = 0`, so we include `hN : 1 ≤ N` explicitly.

The proof below formalizes exactly the decomposition in the paper:

* rewrite `M (sparsePoly N K)` using the exact coefficient formula,
* isolate the endpoint terms,
* write every middle term as `A₁ exp(τ/2) · R_i · exp(-λ_i τ)`,
* use `A₁ exp(τ/2) = 1 / sqrt 2`, `A_s exp(-τ/2) = sqrt 2`,
* show `R_1 → 1`, `R_i → 0` (`i ≥ 2`), and `exp(-λ_i τ) → 1`.
-/
theorem M_tendsto_two_sqrt_two (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto (fun K : ℕ => M (sparsePoly N K)) Filter.atTop (𝓝 (2 * Real.sqrt 2)) := by
  classical
  have hK : ∀ᶠ K in Filter.atTop, 2 ≤ K := Filter.eventually_ge_atTop 2
  have hmain :
      (fun K : ℕ => M (sparsePoly N K)) =ᶠ[Filter.atTop]
        (fun K : ℕ =>
          Acoeff N K 0 * Real.exp (tau N K / 2)
            + (∑ i : Fin N,
                Acoeff N K (midIdx i)
                  * Real.exp ((1 / 2 - lambda N K (midIdx i)) * tau N K))
            + Acoeff N K (Fin.last (N + 1)) * Real.exp (-(tau N K) / 2)) := by
    filter_upwards [hK] with K hK
    rw [M_sparsePoly_exact N K hK]
    let F : Fin (s N) → ℝ := fun j =>
      Acoeff N K j * Real.exp ((1 / 2 - lambda N K j) * tau N K)
    have hsplit :
        (∑ j : Fin (s N), F j)
          = F 0 + (∑ i : Fin N, F (midIdx i)) + F (Fin.last (N + 1)) := by
      have hsucc :
          (∑ j : Fin (s N), F j) = F 0 + ∑ i : Fin (N + 1), F i.succ := by
        simpa [F, s] using (Fin.sum_univ_succ (f := F))
      have htail :
          (∑ i : Fin (N + 1), F i.succ)
            = (∑ i : Fin N, F (midIdx i)) + F (Fin.last (N + 1)) := by
        simpa [midIdx, F] using (Fin.sum_univ_castSucc (f := fun j : Fin (N + 1) => F j.succ))
      calc
        (∑ j : Fin (s N), F j) = F 0 + ∑ i : Fin (N + 1), F i.succ := hsucc
        _ = F 0 + ((∑ i : Fin N, F (midIdx i)) + F (Fin.last (N + 1))) := by rw [htail]
        _ = F 0 + (∑ i : Fin N, F (midIdx i)) + F (Fin.last (N + 1)) := by ring
    dsimp [F] at hsplit
    rw [lambda_zero, lambda_last N K hK] at hsplit
    convert hsplit using 1 <;> ring
  exact (Filter.tendsto_congr' hmain).mpr <| by
    have hfirst :
      Filter.Tendsto (fun K : ℕ => Acoeff N K 0 * Real.exp (tau N K / 2))
        Filter.atTop (𝓝 (1 / Real.sqrt 2)) := by
      have hEq :
          (fun K : ℕ => Acoeff N K 0 * Real.exp (tau N K / 2)) =ᶠ[Filter.atTop]
            (fun _ : ℕ => (1 / Real.sqrt 2 : ℝ)) := by
        filter_upwards [hK] with K hK
        simpa using Acoeff_zero_mul_exp_tau_half N K hK
      exact (Filter.tendsto_congr' hEq).mpr tendsto_const_nhds
    have hlast :
      Filter.Tendsto (fun K : ℕ => Acoeff N K (Fin.last (N + 1)) * Real.exp (-(tau N K) / 2))
        Filter.atTop (𝓝 (Real.sqrt 2)) := by
      have hEq :
          (fun K : ℕ =>
            Acoeff N K (Fin.last (N + 1)) * Real.exp (-(tau N K) / 2)) =ᶠ[Filter.atTop]
            (fun _ : ℕ => Real.sqrt 2) := by
        filter_upwards [hK] with K hK
        simpa using Acoeff_last_mul_exp_neg_tau_half N K hK
      exact (Filter.tendsto_congr' hEq).mpr tendsto_const_nhds
    have hmidterm : ∀ i : Fin N,
        Filter.Tendsto
          (fun K : ℕ => Acoeff N K (midIdx i)
            * Real.exp ((1 / 2 - lambda N K (midIdx i)) * tau N K))
          Filter.atTop
          (𝓝 (if i.1 = 0 then (1 / Real.sqrt 2 : ℝ) else 0)) := by
      intro i
      have hEq :
          (fun K : ℕ =>
            Acoeff N K (midIdx i) * Real.exp ((1 / 2 - lambda N K (midIdx i)) * tau N K))
            =ᶠ[Filter.atTop]
              (fun K : ℕ =>
                (Acoeff N K 0 * Real.exp (tau N K / 2))
                  * (Rcoeff N K i * Real.exp (-(lambda N K (midIdx i)) * tau N K))) := by
        filter_upwards [hK] with K hK
        have hA :
            Acoeff N K (midIdx i) = Acoeff N K 0 * Rcoeff N K i := by
          have hΔ0 : Delta N K 0 ≠ 0 := (Delta_pos N K hK 0).ne'
          have hΔi : Delta N K (midIdx i) ≠ 0 := (Delta_pos N K hK (midIdx i)).ne'
          unfold Acoeff Rcoeff
          field_simp [hΔ0, hΔi]
        calc
          Acoeff N K (midIdx i) * Real.exp ((1 / 2 - lambda N K (midIdx i)) * tau N K)
              = Acoeff N K (midIdx i)
                  * (Real.exp (tau N K / 2) * Real.exp (-(lambda N K (midIdx i)) * tau N K)) := by
                    rw [show ((1 / 2 - lambda N K (midIdx i)) * tau N K)
                        = tau N K / 2 + (-(lambda N K (midIdx i)) * tau N K) by ring]
                    rw [Real.exp_add]
          _ = (Acoeff N K 0 * Rcoeff N K i)
                * (Real.exp (tau N K / 2) * Real.exp (-(lambda N K (midIdx i)) * tau N K)) := by
                  rw [hA]
          _ = (Acoeff N K 0 * Real.exp (tau N K / 2))
                * (Rcoeff N K i * Real.exp (-(lambda N K (midIdx i)) * tau N K)) := by
                  ring
      by_cases hi : i.1 = 0
      · let i0 : Fin N := ⟨0, by simpa using hN⟩
        have hi0 : i = i0 := Fin.ext hi
        subst i
        have hR : Filter.Tendsto (fun K : ℕ => Rcoeff N K i0) Filter.atTop (𝓝 1) :=
          Rcoeff_zero_tendsto_one N hN
        have hsmall : Filter.Tendsto
            (fun K : ℕ => Real.exp (-(lambda N K (midIdx i0)) * tau N K)) Filter.atTop (𝓝 1) :=
          small_power_tendsto_one N i0
        refine (Filter.tendsto_congr' hEq).mpr ?_
        simpa using hfirst.mul (hR.mul hsmall)
      · have hi' : 1 ≤ i.1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi)
        have hR : Filter.Tendsto (fun K : ℕ => Rcoeff N K i) Filter.atTop (𝓝 0) :=
          Rcoeff_succ_tendsto_zero N i hi'
        have hsmall : Filter.Tendsto
            (fun K : ℕ => Real.exp (-(lambda N K (midIdx i)) * tau N K)) Filter.atTop (𝓝 1) :=
          small_power_tendsto_one N i
        refine (Filter.tendsto_congr' hEq).mpr ?_
        simpa [hi] using hfirst.mul (hR.mul hsmall)
    have hmid : Filter.Tendsto
        (fun K : ℕ => ∑ i : Fin N,
          Acoeff N K (midIdx i) * Real.exp ((1 / 2 - lambda N K (midIdx i)) * tau N K))
        Filter.atTop
        (𝓝 (∑ i : Fin N, if i.1 = 0 then (1 / Real.sqrt 2 : ℝ) else 0)) := by
      exact tendsto_finset_sum _ (fun i _ => hmidterm i)
    have hmid' : Filter.Tendsto
        (fun K : ℕ => ∑ i : Fin N,
          Acoeff N K (midIdx i) * Real.exp ((1 / 2 - lambda N K (midIdx i)) * tau N K))
        Filter.atTop (𝓝 (1 / Real.sqrt 2)) := by
      have : (∑ i : Fin N, if i.1 = 0 then (1 / Real.sqrt 2 : ℝ) else 0) = 1 / Real.sqrt 2 := by
        classical
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN)
        simp
      rw [this] at hmid
      exact hmid
    have hsum := (hfirst.add hmid').add hlast
    have hconst : (1 / Real.sqrt 2 : ℝ) + (1 / Real.sqrt 2) + Real.sqrt 2 = 2 * Real.sqrt 2 := by
      have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
      have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
      field_simp [hsqrt]
      nlinarith [hsqrt_sq]
    rw [hconst] at hsum
    exact hsum

/-- A convenient existential corollary of the asymptotic height estimate. -/
theorem M_lt_three_of_largeK (N : ℕ) (hN : 1 ≤ N) :
    ∃ K0 : ℕ, ∀ K ≥ K0, M (sparsePoly N K) < 3 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  have hsqrt_lt : 2 * Real.sqrt 2 < 3 := by
    nlinarith
  have h_eventually : ∀ᶠ K in Filter.atTop, M (sparsePoly N K) < 3 := by
    have h_nhds : Set.Iio 3 ∈ 𝓝 (2 * Real.sqrt 2) := Iio_mem_nhds hsqrt_lt
    exact M_tendsto_two_sqrt_two N hN h_nhds
  rw [Filter.eventually_atTop] at h_eventually
  rcases h_eventually with ⟨K0, hK0⟩
  exact ⟨K0, hK0⟩

/-! ### Final assembly -/

/--
For every `N ≥ 1`, one gets an explicit sparse polynomial with bounded `M` and a positive root of
multiplicity `N + 1`.
-/
theorem explicit_counterexample_family (N : ℕ) (hN : 1 ≤ N) :
    ∃ K : ℕ, 2 ≤ K ∧
      nu (sparsePoly N K) = N + 2 ∧
      M (sparsePoly N K) < 3 ∧
      (sparsePoly N K).rootMultiplicity (x0 N K : ℂ) = N + 1 := by
  rcases M_lt_three_of_largeK N hN with ⟨K0, hK0⟩
  let K := max 2 K0
  refine ⟨K, le_max_left _ _, ?_, ?_, ?_⟩
  · exact nu_sparsePoly N K (le_max_left _ _)
  · exact hK0 K (le_max_right _ _)
  · exact sparsePoly_rootMultiplicity_at_x0 N K (le_max_left _ _)

/-- Main theorem `p990:thm:main`: there is no absolute sparse Erdős--Turán bound. -/
theorem erdos990_no_absolute_constant_sparseErdosTuran :
    ¬ ∃ C : ℝ, 0 < C ∧ SparseErdosTuranBound C := by
  rintro ⟨C, hC, hET⟩
  have hCnonneg : 0 ≤ C := le_of_lt hC
  let L : ℝ := Real.log 3
  have hL : 0 < L := by
    unfold L
    exact Real.log_pos (by norm_num)
  obtain ⟨N, hNgt⟩ := exists_nat_gt (max (2 : ℝ) (8 * C ^ 2 * L))
  have hNtwo : (2 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hNgt
  have hNlarge : 8 * C ^ 2 * L < N := lt_of_le_of_lt (le_max_right _ _) hNgt
  have hN : 1 ≤ N := by
    have hN2 : (2 : ℕ) < N := by exact_mod_cast hNtwo
    omega
  have htarget : C * Real.sqrt ((N + 2 : ℝ) * L) < (N : ℝ) + 1 / 2 := by
    have hNge2 : (2 : ℝ) ≤ N := le_of_lt hNtwo
    have hinside_le : ((N : ℝ) + 2) * L ≤ 2 * (N : ℝ) * L := by
      nlinarith [hL, hNge2]
    have hsqrt_le : Real.sqrt (((N : ℝ) + 2) * L) ≤ Real.sqrt (2 * (N : ℝ) * L) :=
      Real.sqrt_le_sqrt hinside_le
    have hsq :
        (C * Real.sqrt (2 * (N : ℝ) * L)) ^ 2 < ((N : ℝ) / 2) ^ 2 := by
      have hnonneg : 0 ≤ 2 * (N : ℝ) * L := by positivity
      nlinarith [hNlarge, Real.sq_sqrt hnonneg]
    have hhalf : C * Real.sqrt (2 * (N : ℝ) * L) < (N : ℝ) / 2 := by
      have hleft_nonneg : 0 ≤ C * Real.sqrt (2 * (N : ℝ) * L) := by positivity
      have hright_nonneg : 0 ≤ (N : ℝ) / 2 := by positivity
      exact (sq_lt_sq₀ hleft_nonneg hright_nonneg).mp hsq
    have hmain : C * Real.sqrt (((N : ℝ) + 2) * L) < (N : ℝ) / 2 := by
      have hle : C * Real.sqrt (((N : ℝ) + 2) * L) ≤ C * Real.sqrt (2 * (N : ℝ) * L) := by
        gcongr
      exact lt_of_le_of_lt hle hhalf
    linarith
  rcases explicit_counterexample_family N hN with ⟨K, hK, hnu, hMlt3, hmult⟩
  have hcoeff0 : (sparsePoly N K).coeff 0 ≠ 0 := by
    rw [coeff_zero_sparsePoly N K hK]
    exact cCoeff_ne_zero N K hK (0 : Fin (s N))
  have hlead : (sparsePoly N K).leadingCoeff ≠ 0 := by
    rw [leadingCoeff_sparsePoly N K hK]
    exact cCoeff_ne_zero N K hK (Fin.last (N + 1))
  have hβpos : 0 < Real.pi / (d N K : ℝ) := by
    exact div_pos Real.pi_pos (d_pos_real N K hK)
  have hβle : Real.pi / (d N K : ℝ) ≤ 2 * Real.pi := by
    have hβleπ : Real.pi / (d N K : ℝ) ≤ Real.pi := by
      rw [div_le_iff₀ (d_pos_real N K hK)]
      nlinarith [Real.pi_pos, d_one_le_real N K hK]
    linarith [Real.pi_pos, hβleπ]
  have hub :
      angularDiscrepancy (sparsePoly N K) 0 (Real.pi / (d N K : ℝ))
        ≤ C * Real.sqrt ((nu (sparsePoly N K) : ℝ) * Real.log (M (sparsePoly N K))) := by
    exact hET (f := sparsePoly N K) (α := 0) (β := Real.pi / (d N K : ℝ))
      hcoeff0 hlead (by simp) hβpos hβle
  have hMpos : 0 < M (sparsePoly N K) := by
    classical
    rw [M_sparsePoly_exact N K hK]
    have hnonneg :
        ∀ i : Fin (s N), 0 ≤ Acoeff N K i * Real.exp ((1 / 2 - lambda N K i) * tau N K) := by
      intro i
      have hΔ0 : 0 < Delta N K 0 := Delta_pos N K hK 0
      have hΔs : 0 < Delta N K (Fin.last (N + 1)) := Delta_pos N K hK (Fin.last (N + 1))
      have hΔi : 0 < Delta N K i := Delta_pos N K hK i
      unfold Acoeff
      positivity
    have hterm0eq :
        Acoeff N K 0 * Real.exp ((1 / 2 - lambda N K 0) * tau N K) = 1 / Real.sqrt 2 := by
      rw [lambda_zero]
      convert Acoeff_zero_mul_exp_tau_half N K hK using 1 <;> ring
    have hterm0pos : 0 < Acoeff N K 0 * Real.exp ((1 / 2 - lambda N K 0) * tau N K) := by
      rw [hterm0eq]
      positivity
    have hle :
        Acoeff N K 0 * Real.exp ((1 / 2 - lambda N K 0) * tau N K)
          ≤ ∑ i : Fin (s N), Acoeff N K i * Real.exp ((1 / 2 - lambda N K i) * tau N K) := by
      exact Finset.single_le_sum (fun i hi => hnonneg i) (Finset.mem_univ _)
    linarith
  have hlogM_le : Real.log (M (sparsePoly N K)) ≤ L := by
    unfold L
    exact le_of_lt (Real.log_lt_log hMpos hMlt3)
  have hsqrt_le :
      Real.sqrt ((nu (sparsePoly N K) : ℝ) * Real.log (M (sparsePoly N K)))
        ≤ Real.sqrt ((N + 2 : ℝ) * L) := by
    rw [hnu]
    apply Real.sqrt_le_sqrt
    norm_num
    exact mul_le_mul_of_nonneg_left hlogM_le (by positivity : 0 ≤ (N : ℝ) + 2)
  have hub' :
      angularDiscrepancy (sparsePoly N K) 0 (Real.pi / (d N K : ℝ))
        ≤ C * Real.sqrt ((N + 2 : ℝ) * L) := by
    have hmul : C * Real.sqrt ((nu (sparsePoly N K) : ℝ) * Real.log (M (sparsePoly N K)))
        ≤ C * Real.sqrt ((N + 2 : ℝ) * L) := by
      gcongr
    exact le_trans hub hmul
  have hcrowd : N + 1 ≤ argRootCount (sparsePoly N K) (crowdingInterval N K) :=
    overcrowded_small_interval N K hK
  have hdisc_lower :
      (N : ℝ) + 1 / 2 ≤ angularDiscrepancy (sparsePoly N K) 0 (Real.pi / (d N K : ℝ)) := by
    have hcount : (N + 1 : ℝ) ≤ argRootCount (sparsePoly N K) (crowdingInterval N K) := by
      exact_mod_cast hcrowd
    have hnonneg :
        0 ≤ (argRootCount (sparsePoly N K) (crowdingInterval N K) : ℝ) - (1 / 2 : ℝ) := by
      linarith
    unfold angularDiscrepancy
    rw [show Set.Ico 0 (Real.pi / (d N K : ℝ)) = crowdingInterval N K by rfl]
    rw [natDegree_sparsePoly N K hK, expectedRootCount_crowdingInterval N K hK,
      abs_of_nonneg hnonneg]
    linarith
  nlinarith [hdisc_lower, hub', htarget]

#print axioms erdos990_no_absolute_constant_sparseErdosTuran
-- 'erdos990_no_absolute_constant_sparseErdosTuran' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos990
