import ErdosProblems.Erdos980.ElliottTail.CumulativeMediumApplication
import ErdosProblems.Erdos980.External.Erdos387.BinomialEulerProduct
import ErdosProblems.Erdos851.ConcreteBetaCardinality

/-!
# Asymptotic parameters for the odd-prime medium sieve

This file records the numerical part of the odd-prime Rosser argument.  A
rank-`r` generator lattice has boundary error `x^(1-1/r)`.  If the Rosser
level is at most `x^eta`, with `eta < 1/r`, and its finite Euler factor has
dimension `k`, then the entire endpoint error is `o(x / log x)`.

It also packages two elementary finite estimates used to choose auxiliary
prime ideals: logarithmically many independent symbols already give an
inverse-square tensor density, while their product is bounded by the
displayed auxiliary modulus.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace Erdos980.ElliottTail.OddMediumParameters

noncomputable section

/-- Four times the upper binary logarithm gives enough tensor depth for an
inverse-fourth saving at numerical cutoff `t`.  Two powers are retained for
the public inverse-square tail bound, while the other two absorb the
logarithmic cost of the moving ray modulus. -/
def oddTensorDepth (t : ℕ) : ℕ := 4 * Nat.clog 2 (t + 1)

/-- A coarse upper bound for the product of `oddTensorDepth t` auxiliary
ordinary primes, each at most `t`. -/
def oddAuxiliaryModulusBound (t : ℕ) : ℕ := t ^ oddTensorDepth t

theorem prod_auxiliaryPrimes_le_modulusBound
    {t : ℕ} (Q : Finset ℕ) (hcard : Q.card ≤ oddTensorDepth t)
    (hle : ∀ q ∈ Q, q ≤ t) :
    Q.prod id ≤ oddAuxiliaryModulusBound t := by
  calc
    Q.prod id ≤ Q.prod (fun _ ↦ t) :=
      Finset.prod_le_prod' fun q hq ↦ hle q hq
    _ = t ^ Q.card := by simp
    _ ≤ t ^ oddTensorDepth t := by
      by_cases ht : t = 0
      · subst t
        simp [oddTensorDepth] at hcard
        simp [hcard, oddTensorDepth]
      · exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero ht) hcard

/-- The strengthened tensor depth gives an inverse-fourth geometric saving. -/
theorem oddTensorDepth_geometric_le_inverseFourth
    {ell : ℕ} (hell : 2 ≤ ell) (t : ℕ) :
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t ≤
      1 / ((t + 1 : ℕ) : ℝ) ^ 4 := by
  have hnpos : (0 : ℝ) < (t + 1 : ℕ) := by positivity
  have hpowNat : t + 1 ≤ 2 ^ Nat.clog 2 (t + 1) :=
    Nat.le_pow_clog (by norm_num) _
  have hpowReal : ((t + 1 : ℕ) : ℝ) ^ 4 ≤
      ((2 : ℕ) ^ Nat.clog 2 (t + 1) : ℕ) ^ 4 := by
    exact_mod_cast Nat.pow_le_pow_left hpowNat 4
  have hellR : (2 : ℝ) ≤ ell := by exact_mod_cast hell
  have hinv : (ell : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := by
    exact inv_anti₀ (by norm_num) hellR
  calc
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t ≤
        ((2 : ℝ)⁻¹) ^ oddTensorDepth t := by
      exact pow_le_pow_left₀ (by positivity) hinv _
    _ = ((((2 : ℕ) ^ Nat.clog 2 (t + 1) : ℕ) : ℝ) ^ 4)⁻¹ := by
      simp only [oddTensorDepth, Nat.cast_pow, Nat.cast_ofNat, inv_pow, pow_mul]
      congr 1
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ (((t + 1 : ℕ) : ℝ) ^ 4)⁻¹ := by
      exact inv_anti₀ (by positivity) hpowReal
    _ = 1 / ((t + 1 : ℕ) : ℝ) ^ 4 := by rw [one_div]

/-- The public inverse-square majorant used by the cumulative layer-cake
argument is retained after strengthening the tensor depth. -/
theorem oddTensorDepth_geometric_le_inverseSquare
    {ell : ℕ} (hell : 2 ≤ ell) (t : ℕ) :
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t ≤
      1 / ((t + 1 : ℕ) : ℝ) ^ 2 := by
  refine (oddTensorDepth_geometric_le_inverseFourth hell t).trans ?_
  have hnone : (1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ t + 1 by omega)
  have hpowTwo : (1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((t + 1 : ℕ) : ℝ) - 1)]
  have hpow : ((t + 1 : ℕ) : ℝ) ^ 2 ≤ ((t + 1 : ℕ) : ℝ) ^ 4 := by
    calc
      ((t + 1 : ℕ) : ℝ) ^ 2 = ((t + 1 : ℕ) : ℝ) ^ 2 * 1 := by ring
      _ ≤ ((t + 1 : ℕ) : ℝ) ^ 2 * ((t + 1 : ℕ) : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hpowTwo (sq_nonneg _)
      _ = ((t + 1 : ℕ) : ℝ) ^ 4 := by ring
  simpa only [one_div] using inv_anti₀ (by positivity) hpow

/-- The upper binary logarithm of a positive natural is bounded by the
natural itself. -/
theorem clog_two_le_self (n : ℕ) : Nat.clog 2 n ≤ n := by
  apply Nat.clog_le_of_le_pow
  exact Nat.le_of_lt n.lt_two_pow_self

/-- The strengthened depth absorbs its own logarithmic endpoint cost.  This
is the numerical estimate used after bounding the moving ray modulus by a
product of `oddTensorDepth t` auxiliary primes. -/
theorem oddTensorDepth_geometric_mul_depth_log_le_inverseSquare
    {ell : ℕ} (hell : 2 ≤ ell) (t : ℕ) :
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
        ((oddTensorDepth t : ℕ) : ℝ) * Real.log ((t + 1 : ℕ) : ℝ) ≤
      4 / ((t + 1 : ℕ) : ℝ) ^ 2 := by
  let n : ℕ := t + 1
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hnone : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n by simp [n])
  have hdepthNat : oddTensorDepth t ≤ 4 * n := by
    dsimp [oddTensorDepth, n]
    exact Nat.mul_le_mul_left 4 (clog_two_le_self (t + 1))
  have hdepth : (oddTensorDepth t : ℝ) ≤ 4 * (n : ℝ) := by
    exact_mod_cast hdepthNat
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) := Real.log_le_self hnpos.le
  have hcost : (oddTensorDepth t : ℝ) * Real.log (n : ℝ) ≤
      4 * (n : ℝ) ^ 2 := by
    calc
      (oddTensorDepth t : ℝ) * Real.log (n : ℝ) ≤
          (4 * (n : ℝ)) * Real.log (n : ℝ) := by gcongr
      _ ≤ (4 * (n : ℝ)) * (n : ℝ) := by gcongr
      _ = 4 * (n : ℝ) ^ 2 := by ring
  have hgeom := oddTensorDepth_geometric_le_inverseFourth hell t
  have hgeom' : ((ell : ℝ)⁻¹) ^ oddTensorDepth t ≤ 1 / (n : ℝ) ^ 4 := by
    simpa [n] using hgeom
  calc
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
          (oddTensorDepth t : ℝ) * Real.log ((t + 1 : ℕ) : ℝ) =
        ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
          ((oddTensorDepth t : ℝ) * Real.log (n : ℝ)) := by
      simp only [n]
      ring
    _ ≤ (1 / (n : ℝ) ^ 4) *
          ((oddTensorDepth t : ℝ) * Real.log (n : ℝ)) := by
      gcongr
    _ ≤ (1 / (n : ℝ) ^ 4) * (4 * (n : ℝ) ^ 2) := by
      gcongr
    _ = 4 / (n : ℝ) ^ 2 := by field_simp
    _ = 4 / ((t + 1 : ℕ) : ℝ) ^ 2 := by simp [n]

/-- Consequently the geometric tensor density absorbs the logarithm of any
positive modulus bounded by the auxiliary-prime product. -/
theorem oddTensorDepth_geometric_mul_log_modulus_le_inverseSquare
    {ell t f : ℕ} (hell : 2 ≤ ell) (hf0 : f ≠ 0)
    (hf : f ≤ (t + 1) ^ oddTensorDepth t) :
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t * Real.log (f : ℝ) ≤
      4 / ((t + 1 : ℕ) : ℝ) ^ 2 := by
  have hfpos : (0 : ℝ) < (f : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hf0
  have hlogf : Real.log (f : ℝ) ≤
      (oddTensorDepth t : ℝ) * Real.log ((t + 1 : ℕ) : ℝ) := by
    calc
      Real.log (f : ℝ) ≤
          Real.log ((((t + 1) ^ oddTensorDepth t : ℕ) : ℝ)) := by
        apply Real.log_le_log hfpos
        exact_mod_cast hf
      _ = Real.log (((t + 1 : ℕ) : ℝ) ^ oddTensorDepth t) := by
        norm_num
      _ = (oddTensorDepth t : ℝ) *
          Real.log ((t + 1 : ℕ) : ℝ) := by
        rw [Real.log_pow]
  have hgeomnonneg : 0 ≤ ((ell : ℝ)⁻¹) ^ oddTensorDepth t := by positivity
  calc
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t * Real.log (f : ℝ) ≤
        ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
          ((oddTensorDepth t : ℝ) * Real.log ((t + 1 : ℕ) : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hlogf hgeomnonneg
    _ = ((ell : ℝ)⁻¹) ^ oddTensorDepth t *
          (oddTensorDepth t : ℝ) * Real.log ((t + 1 : ℕ) : ℝ) := by ring
    _ ≤ 4 / ((t + 1 : ℕ) : ℝ) ^ 2 :=
      oddTensorDepth_geometric_mul_depth_log_le_inverseSquare hell t

/-- The two spare powers also absorb any fixed additional polylogarithmic
factor.  This pointwise form isolates the only eventual input: a fixed power
of `log (t+1)` is eventually at most `t+1`. -/
theorem oddTensorDepth_geometric_mul_log_modulus_mul_logPow_le_inverseSquare
    {ell t f q : ℕ} (hell : 2 ≤ ell) (hf0 : f ≠ 0)
    (hf : f ≤ (t + 1) ^ oddTensorDepth t)
    (hlogPow : Real.log ((t + 1 : ℕ) : ℝ) ^ (q + 1) ≤
      ((t + 1 : ℕ) : ℝ)) :
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t * Real.log (f : ℝ) *
        Real.log ((t + 1 : ℕ) : ℝ) ^ q ≤
      4 / ((t + 1 : ℕ) : ℝ) ^ 2 := by
  let n : ℕ := t + 1
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hnone : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show 1 ≤ n by simp [n])
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hfpos : (0 : ℝ) < (f : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hf0
  have hfone : (1 : ℝ) ≤ (f : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hf0
  have hlogfnonneg : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hfone
  have hdepthNat : oddTensorDepth t ≤ 4 * n := by
    dsimp [oddTensorDepth, n]
    exact Nat.mul_le_mul_left 4 (clog_two_le_self (t + 1))
  have hdepth : (oddTensorDepth t : ℝ) ≤ 4 * (n : ℝ) := by
    exact_mod_cast hdepthNat
  have hlogf : Real.log (f : ℝ) ≤
      (oddTensorDepth t : ℝ) * Real.log (n : ℝ) := by
    calc
      Real.log (f : ℝ) ≤
          Real.log ((((t + 1) ^ oddTensorDepth t : ℕ) : ℝ)) := by
        apply Real.log_le_log hfpos
        exact_mod_cast hf
      _ = Real.log ((n : ℝ) ^ oddTensorDepth t) := by simp [n]
      _ = (oddTensorDepth t : ℝ) * Real.log (n : ℝ) := by
        rw [Real.log_pow]
  have hgeom : ((ell : ℝ)⁻¹) ^ oddTensorDepth t ≤
      1 / (n : ℝ) ^ 4 := by
    simpa [n] using oddTensorDepth_geometric_le_inverseFourth hell t
  calc
    ((ell : ℝ)⁻¹) ^ oddTensorDepth t * Real.log (f : ℝ) *
          Real.log ((t + 1 : ℕ) : ℝ) ^ q =
        ((ell : ℝ)⁻¹) ^ oddTensorDepth t * Real.log (f : ℝ) *
          Real.log (n : ℝ) ^ q := by simp [n]
    _ ≤ (1 / (n : ℝ) ^ 4) * Real.log (f : ℝ) *
          Real.log (n : ℝ) ^ q := by gcongr
    _ ≤ (1 / (n : ℝ) ^ 4) *
          ((oddTensorDepth t : ℝ) * Real.log (n : ℝ)) *
            Real.log (n : ℝ) ^ q := by gcongr
    _ ≤ (1 / (n : ℝ) ^ 4) *
          ((4 * (n : ℝ)) * Real.log (n : ℝ)) *
            Real.log (n : ℝ) ^ q := by gcongr
    _ = (4 / (n : ℝ) ^ 4) * (n : ℝ) *
          Real.log (n : ℝ) ^ (q + 1) := by
      rw [pow_succ]
      ring
    _ ≤ (4 / (n : ℝ) ^ 4) * (n : ℝ) * (n : ℝ) := by
      gcongr
    _ = 4 / (n : ℝ) ^ 2 := by field_simp
    _ = 4 / ((t + 1 : ℕ) : ℝ) ^ 2 := by simp [n]

/-- Eventual form of the fixed-polylogarithm absorption estimate. -/
theorem eventually_oddTensorDepth_geometric_mul_log_modulus_mul_logPow_le_inverseSquare
    {ell : ℕ} (hell : 2 ≤ ell) (q : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ f : ℕ, f ≠ 0 →
      f ≤ (t + 1) ^ oddTensorDepth t →
      ((ell : ℝ)⁻¹) ^ oddTensorDepth t * Real.log (f : ℝ) *
          Real.log ((t + 1 : ℕ) : ℝ) ^ q ≤
        4 / ((t + 1 : ℕ) : ℝ) ^ 2 := by
  have hsmall :=
    ((Real.isLittleO_pow_log_id_atTop (n := q + 1)).comp_tendsto
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).bound one_pos
  filter_upwards [hsmall] with t ht
  intro f hf0 hf
  have ht' : ‖Real.log ((t + 1 : ℕ) : ℝ) ^ (q + 1)‖ ≤
      ‖((t + 1 : ℕ) : ℝ)‖ := by
    simpa only [Function.comp_apply, id_eq, one_mul] using ht
  have hnone : (1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ t + 1 by omega)
  have hlognonneg : 0 ≤ Real.log ((t + 1 : ℕ) : ℝ) :=
    Real.log_nonneg hnone
  rw [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlognonneg _),
    Real.norm_eq_abs, abs_of_nonneg (by positivity)] at ht'
  exact oddTensorDepth_geometric_mul_log_modulus_mul_logPow_le_inverseSquare
    hell hf0 hf ht'

/-- The finite Euler factor emitted by the Rosser remainder is dominated by
the inverse Euler product for the binomial density `k/p`. -/
theorem ascendingSievePrimes_endpointEuler_le_binomialInverseLocalEuler
    {k z y : ℕ} (hk : 1 ≤ k) (hz : 2 * k ≤ z) :
    ((Erdos851.ascendingSievePrimes z y).map
        (fun p : ℕ ↦ 1 + (k : ℝ) / p)).prod ≤
      Erdos851.inverseLocalEulerProduct
        (fun p ↦ Erdos387.binomialSieveNu k p) z y := by
  classical
  rw [Erdos851.inverseLocalEulerProduct]
  rw [← List.prod_toFinset _ (Erdos851.ascendingSievePrimes_nodup z y)]
  have hset : (Erdos851.ascendingSievePrimes z y).toFinset =
      Erdos851.sievePrimes z y := by
    ext p
    simp only [List.mem_toFinset, Erdos851.mem_ascendingSievePrimes]
  rw [hset]
  apply Finset.prod_le_prod
  · intro p hp
    exact add_nonneg zero_le_one (div_nonneg (by positivity) (by positivity))
  · intro p hp
    have hp' : p ∈ Erdos851.ascendingSievePrimes z y :=
      Erdos851.mem_ascendingSievePrimes.mpr hp
    have hpPrime := Erdos851.ascendingSievePrimes_prime p hp'
    have hzp : z < p := (Erdos851.mem_sievePrimes.mp hp).1
    have hklt : k < p := by
      calc
        k ≤ 2 * k := by omega
        _ ≤ z := hz
        _ < p := hzp
    rw [Erdos387.binomialSieveNu_prime hpPrime]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hfrac : (k : ℝ) / p < 1 := by
      rw [div_lt_one hp0]
      exact_mod_cast hklt
    have hden : 0 < 1 - (k : ℝ) / p := sub_pos.mpr hfrac
    rw [inv_eq_one_div, le_div_iff₀ hden]
    have hnonneg : 0 ≤ (k : ℝ) / p := div_nonneg (by positivity) hp0.le
    nlinarith [sq_nonneg ((k : ℝ) / p)]

/-- Endpoint-independent, dimension-`k` control of the exact Rosser finite
Euler factor. -/
theorem exists_endpointEuler_dimension_bound (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ z y : ℕ, 2 * k ≤ z → z ≤ y →
      ((Erdos851.ascendingSievePrimes z y).map
          (fun p : ℕ ↦ 1 + (k : ℝ) / p)).prod ≤
        A * (Real.log (y : ℝ) / Real.log (z : ℝ)) ^ k := by
  obtain ⟨A, hA, hdimension⟩ :=
    Erdos387.BinomialEulerProduct.exists_binomial_dimension_bound k hk
  refine ⟨A, hA, fun z y hz hzy ↦ ?_⟩
  exact (ascendingSievePrimes_endpointEuler_le_binomialInverseLocalEuler hk hz).trans
    (hdimension z y hz hzy)

/-- The real envelope for the cell-boundary contribution, a Rosser level
`x^eta`, and a dimension-`k` endpoint Euler factor. -/
def realRosserCellEnvelope (r k : ℕ) (eta C : ℝ) (x : ℝ) : ℝ :=
  C * x ^ (1 - (r : ℝ)⁻¹ + eta) * Real.log x ^ (k : ℝ)

/-- Once `eta < 1/r`, every fixed-dimensional Rosser cell remainder is
negligible on the prime-counting scale. -/
theorem realRosserCellEnvelope_isLittleO
    {r k : ℕ} {eta C : ℝ} (hr : 0 < r) (heta : eta < (r : ℝ)⁻¹) :
    (realRosserCellEnvelope r k eta C) =o[atTop]
      (fun x : ℝ ↦ x / Real.log x) := by
  let delta : ℝ := (r : ℝ)⁻¹ - eta
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hlog :
      (fun x : ℝ ↦ Real.log x ^ ((k : ℝ) + 1)) =o[atTop]
        (fun x : ℝ ↦ x ^ delta) :=
    isLittleO_log_rpow_rpow_atTop ((k : ℝ) + 1) hdelta
  have hpow :
      (fun x : ℝ ↦ x ^ (1 - delta)) =O[atTop]
        (fun x : ℝ ↦ x ^ (1 - delta)) :=
    isBigO_refl _ _
  have hcore := hpow.mul_isLittleO hlog
  have hcore' :
      (fun x : ℝ ↦ C * (x ^ (1 - delta) *
          Real.log x ^ ((k : ℝ) + 1))) =o[atTop]
        (fun x : ℝ ↦ x) := by
    refine (hcore.const_mul_left C).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]
    rw [show 1 - delta + delta = 1 by ring, Real.rpow_one]
  have hlogne : ∀ᶠ x : ℝ in atTop, Real.log x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
  apply (isLittleO_mul_iff_isLittleO_div hlogne).mp
  refine hcore'.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  dsimp [realRosserCellEnvelope, delta]
  rw [show 1 - ((r : ℝ)⁻¹ - eta) = 1 - (r : ℝ)⁻¹ + eta by ring]
  rw [show (k : ℝ) + 1 = 1 + (k : ℝ) by ring]
  rw [Real.rpow_add hlogpos, Real.rpow_one]
  ring

/-- The cell error beats the prime-counting scale by every fixed logarithmic
power.  This stronger form is what makes the estimate uniform all the way up
to the polylogarithmic cutoff `smoothParameterY`. -/
theorem realRosserCellEnvelope_isLittleO_logPow
    {r k : ℕ} {eta C : ℝ} (q : ℕ) (hr : 0 < r)
    (heta : eta < (r : ℝ)⁻¹) :
    (realRosserCellEnvelope r k eta C) =o[atTop]
      (fun x : ℝ ↦ x / Real.log x ^ q) := by
  let delta : ℝ := (r : ℝ)⁻¹ - eta
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hlog :
      (fun x : ℝ ↦ Real.log x ^ ((k : ℝ) + q)) =o[atTop]
        (fun x : ℝ ↦ x ^ delta) :=
    isLittleO_log_rpow_rpow_atTop ((k : ℝ) + q) hdelta
  have hcore :=
    (isBigO_refl (fun x : ℝ ↦ x ^ (1 - delta)) atTop).mul_isLittleO hlog
  have hcore' :
      (fun x : ℝ ↦ C * (x ^ (1 - delta) *
          Real.log x ^ ((k : ℝ) + q))) =o[atTop]
        (fun x : ℝ ↦ x) := by
    refine (hcore.const_mul_left C).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]
    rw [show 1 - delta + delta = 1 by ring, Real.rpow_one]
  have hlogne : ∀ᶠ x : ℝ in atTop, Real.log x ^ q ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact pow_ne_zero _
      (Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx))
  apply (isLittleO_mul_iff_isLittleO_div hlogne).mp
  refine hcore'.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  dsimp [realRosserCellEnvelope, delta]
  rw [show 1 - ((r : ℝ)⁻¹ - eta) = 1 - (r : ℝ)⁻¹ + eta by ring]
  rw [← Real.rpow_natCast]
  have hp : Real.log x ^ ((k : ℝ) + q) =
      Real.log x ^ (q : ℝ) * Real.log x ^ (k : ℝ) := by
    rw [Real.rpow_add hlogpos]
    ring
  rw [hp]
  ring

/-- Natural-endpoint form used by the finite Rosser sieve. -/
theorem rosserCellEnvelope_isLittleO
    {r k : ℕ} {eta C : ℝ} (hr : 0 < r) (heta : eta < (r : ℝ)⁻¹) :
    (fun x : ℕ ↦ realRosserCellEnvelope r k eta C (x : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) := by
  exact (realRosserCellEnvelope_isLittleO hr heta).natCast_atTop

/-- Natural-endpoint form with an arbitrary additional logarithmic saving. -/
theorem rosserCellEnvelope_isLittleO_logPow
    {r k : ℕ} {eta C : ℝ} (q : ℕ) (hr : 0 < r)
    (heta : eta < (r : ℝ)⁻¹) :
    (fun x : ℕ ↦ realRosserCellEnvelope r k eta C (x : ℝ)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ) ^ q) := by
  exact (realRosserCellEnvelope_isLittleO_logPow q hr heta).natCast_atTop

/-- The square of the largest numerical cutoff costs at most the expected
sixty-four powers of `log x`.  The harmless factor four absorbs the added
one in the inverse-square denominator. -/
theorem eventually_smoothParameterY_add_one_sq_le_log_pow :
    ∀ᶠ x : ℕ in atTop,
      (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2) ≤
        4 * Real.log (x : ℝ) ^ (64 : ℕ) := by
  filter_upwards [eventually_ge_atTop 8] with x hx
  have hxR : (8 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog : (1 : ℝ) < Real.log (x : ℝ) := by
    rw [Real.lt_log_iff_exp_lt (by
      exact_mod_cast (show 0 < x by omega))]
    calc
      Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < 8 := by norm_num
      _ ≤ (x : ℝ) := hxR
  have hlog0 : 0 ≤ Real.log (x : ℝ) := (zero_lt_one.trans hlog).le
  have hpow0 : 0 ≤ Real.log (x : ℝ) ^ (32 : ℝ) :=
    Real.rpow_nonneg hlog0 _
  have hy : (smoothParameterY x : ℝ) ≤
      Real.log (x : ℝ) ^ (32 : ℕ) := by
    have hfloor : (logarithmicCutoff (Real.log (x : ℝ)) : ℝ) ≤
        Real.log (x : ℝ) ^ (32 : ℝ) := by
      simpa only [logarithmicCutoff] using Nat.floor_le hpow0
    calc
      (smoothParameterY x : ℝ) ≤
          Real.log (x : ℝ) ^ (32 : ℝ) := by
        simpa only [smoothParameterY] using hfloor
      _ = Real.log (x : ℝ) ^ (32 : ℕ) :=
        Real.rpow_natCast _ _
  have hone : (1 : ℝ) ≤ Real.log (x : ℝ) ^ (32 : ℕ) :=
    one_le_pow₀ hlog.le
  have hsum : (smoothParameterY x : ℝ) + 1 ≤
      2 * Real.log (x : ℝ) ^ (32 : ℕ) := by
    linarith
  calc
    (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2) =
        ((smoothParameterY x : ℝ) + 1) ^ 2 := by push_cast; rfl
    _ ≤ (2 * Real.log (x : ℝ) ^ (32 : ℕ)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hsum _
    _ = 4 * Real.log (x : ℝ) ^ (64 : ℕ) := by ring

/-- Consequently the full Rosser boundary error, even after paying the
worst inverse-square uniformity cost at `smoothParameterY x`, is still
negligible on the prime-counting scale. -/
theorem rosserCellEnvelope_mul_smoothCutoff_sq_isLittleO
    {r k : ℕ} {eta C : ℝ} (hr : 0 < r)
    (heta : eta < (r : ℝ)⁻¹) :
    (fun x : ℕ ↦ realRosserCellEnvelope r k eta C (x : ℝ) *
        (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2)) =o[atTop]
      (fun x : ℕ ↦ (x : ℝ) / Real.log (x : ℝ)) := by
  have henv := rosserCellEnvelope_isLittleO_logPow
    (r := r) (k := k) (eta := eta) (C := C) 65 hr heta
  have hcut :
      (fun x : ℕ ↦ (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2)) =O[atTop]
        (fun x : ℕ ↦ Real.log (x : ℝ) ^ (64 : ℕ)) := by
    refine IsBigO.of_bound 4 ?_
    filter_upwards [eventually_smoothParameterY_add_one_sq_le_log_pow,
      eventually_ge_atTop 8] with x hxy hx
    have hlog0 : 0 ≤ Real.log (x : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ x by omega)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _), abs_of_nonneg (pow_nonneg hlog0 _)]
    exact hxy
  have hmul := henv.mul_isBigO hcut
  refine hmul.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop 8] with x hx
  have hlogne : Real.log (x : ℝ) ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one
    · exact_mod_cast (show 0 < x by omega)
    · exact_mod_cast (show x ≠ 1 by omega)
  field_simp

/-- Numerical reduction from the finite ray/Rosser estimate to the exact
cumulative inverse-square interface.  The finite arithmetic argument only
has to supply the displayed bound: its geometric tensor term has constant
`A`, while its boundary term is `realRosserCellEnvelope`. -/
theorem cumulativeExceptionalPrimeScaleBound_of_rosserCellEnvelope
    {ell r k : ℕ} {eta C A : ℝ} (hr : 0 < r)
    (heta : eta < (r : ℝ)⁻¹) (hC : 0 ≤ C)
    (hrosser : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        A * ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2) +
          realRosserCellEnvelope r k eta C (x : ℝ)) :
    CumulativeExceptionalPrimeScaleBound ell
      (inverseSquareMajorant (A + 1)) := by
  have herr := rosserCellEnvelope_mul_smoothCutoff_sq_isLittleO
    (r := r) (k := k) (eta := eta) (C := C) hr heta
  have herrBound := herr.bound (show (0 : ℝ) < 1 by norm_num)
  have hfinal : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        (x : ℝ) / Real.log (x : ℝ) *
          inverseSquareMajorant (A + 1) t := by
    filter_upwards [hrosser, herrBound, eventually_ge_atTop 2]
        with x hxrosser hxerr hx2
    intro t ht
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    have hscale : 0 ≤ (x : ℝ) / Real.log (x : ℝ) := by positivity
    have hE : 0 ≤ realRosserCellEnvelope r k eta C (x : ℝ) := by
      unfold realRosserCellEnvelope
      positivity
    have hYsq : 0 ≤ (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2) :=
      sq_nonneg _
    have hxerr' :
        realRosserCellEnvelope r k eta C (x : ℝ) *
            (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2) ≤
          (x : ℝ) / Real.log (x : ℝ) := by
      simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (mul_nonneg hE hYsq),
        abs_of_nonneg hscale] using hxerr
    have htcast : ((t + 1 : ℕ) : ℝ) ≤
        ((smoothParameterY x + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right ht 1
    have hsq : (((t + 1 : ℕ) : ℝ) ^ 2) ≤
        (((smoothParameterY x + 1 : ℕ) : ℝ) ^ 2) := by
      exact pow_le_pow_left₀ (by positivity) htcast _
    have hEscale : realRosserCellEnvelope r k eta C (x : ℝ) *
        (((t + 1 : ℕ) : ℝ) ^ 2) ≤
          (x : ℝ) / Real.log (x : ℝ) :=
      (mul_le_mul_of_nonneg_left hsq hE).trans hxerr'
    have hden : 0 < (((t + 1 : ℕ) : ℝ) ^ 2) := by positivity
    have hEdiv : realRosserCellEnvelope r k eta C (x : ℝ) ≤
        ((x : ℝ) / Real.log (x : ℝ)) /
          (((t + 1 : ℕ) : ℝ) ^ 2) :=
      (le_div_iff₀ hden).2 (by simpa [mul_comm] using hEscale)
    calc
      ((exceptionalPrimes ell t x).card : ℝ) ≤
          A * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            realRosserCellEnvelope r k eta C (x : ℝ) := hxrosser t ht
      _ ≤ A * ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) +
            ((x : ℝ) / Real.log (x : ℝ)) /
              (((t + 1 : ℕ) : ℝ) ^ 2) := by linarith
      _ = (x : ℝ) / Real.log (x : ℝ) *
            inverseSquareMajorant (A + 1) t := by
        unfold inverseSquareMajorant
        ring
  obtain ⟨X, hX⟩ := eventually_atTop.mp hfinal
  exact ⟨X, fun x hx t ht ↦ hX x hx t ht⟩

/-- Direct medium-estimate corollary of the numerical Rosser envelope
reduction. -/
theorem primeExponentMediumEstimate_of_rosserCellEnvelope
    {ell r k : ℕ} (hell : 2 ≤ ell) {eta C A : ℝ} (hr : 0 < r)
    (heta : eta < (r : ℝ)⁻¹) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hrosser : ∀ᶠ x : ℕ in atTop, ∀ t : ℕ, t ≤ smoothParameterY x →
      ((exceptionalPrimes ell t x).card : ℝ) ≤
        A * ((x : ℝ) / Real.log (x : ℝ)) /
            (((t + 1 : ℕ) : ℝ) ^ 2) +
          realRosserCellEnvelope r k eta C (x : ℝ)) :
    PrimeExponentMediumEstimate ell := by
  apply primeExponentMediumEstimate_of_inverseSquare_cumulative_bound
    ell hell (A + 1) (by linarith)
  exact cumulativeExceptionalPrimeScaleBound_of_rosserCellEnvelope
    hr heta hC hrosser

end

end Erdos980.ElliottTail.OddMediumParameters
