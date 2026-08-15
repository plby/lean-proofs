/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import PrimeNumberTheoremAnd.Consequences

/-!
# Analytic inputs for the BNPZ covering theorem

This module derives the fixed-modulus estimates needed by the public BNPZ
covering construction from the repository's proof of the prime number theorem
in arithmetic progressions.  No result in this file is postulated.
-/

open Filter Finset Asymptotics Real

namespace Erdos387

/-- The precise growing-parameter shifted Siegel--Walfisz lower bound used by
the public BNPZ wide-cover construction.  This is a named proposition, not an
assumption: downstream conditional interfaces take a proof of it explicitly.
-/
def ShiftedSiegelWalfiszLower : Prop :=
  ∀ C : ℕ, ∃ X₀ : ℕ, ∀ X Q a h : ℕ,
    X₀ ≤ X →
    2 ≤ Q →
    Q ≤ (Nat.log 2 X + 1) ^ C →
    h ≤ (Nat.log 2 X + 1) ^ C →
    a.Coprime Q →
    ((Finset.Ioc (X - h) (2 * X - h)).filter
      (fun p => p.Prime ∧ p % Q = a % Q)).card
      ≥ X / (8 * Q * (Nat.log 2 X + 1))

/-- Chebyshev's theta function restricted to a reduced residue class. -/
noncomputable def thetaAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
    if p % q = a then Real.log p else 0

/-- Primes in a real interval and in the residue class `a mod q`. -/
noncomputable def primeIntervalAP (q a : ℕ) (u v : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter (fun p => p.Prime ∧ p % q = a)

/-- Rewrite `thetaAP` as an unweighted finite-set restriction followed by a
logarithmic sum. -/
theorem thetaAP_eq_sum_filter (q a : ℕ) (x : ℝ) :
    thetaAP q a x =
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter (fun p => p.Prime ∧ p % q = a),
        Real.log p := by
  classical
  unfold thetaAP
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hprime : p.Prime <;> by_cases hres : p % q = a <;>
    simp [hprime, hres]

/-- The increment of `thetaAP` is exactly the logarithmic sum over the
corresponding interval. -/
theorem thetaAP_sub_eq_sum_interval (q a : ℕ) {u v : ℝ}
    (huv : u ≤ v) :
    thetaAP q a v - thetaAP q a u =
      ∑ p ∈ primeIntervalAP q a u v, Real.log p := by
  classical
  rw [thetaAP_eq_sum_filter, thetaAP_eq_sum_filter]
  let pred : ℕ → Prop := fun p => p.Prime ∧ p % q = a
  let left := (Finset.Iic ⌊u⌋₊).filter pred
  let block := (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter pred
  have hfloor : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono huv
  have hdis : Disjoint left block := by
    exact (Finset.Iic_disjoint_Ioc le_rfl).mono
      (Finset.filter_subset pred (Finset.Iic ⌊u⌋₊))
      (Finset.filter_subset pred (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊))
  have hunion : left ∪ block = (Finset.Iic ⌊v⌋₊).filter pred := by
    dsimp [left, block]
    rw [← Finset.filter_union, Finset.Iic_union_Ioc_eq_Iic hfloor]
  have hsum := Finset.sum_union hdis (f := fun p : ℕ => Real.log p)
  rw [hunion] at hsum
  dsimp [left, block, pred] at hsum
  rw [primeIntervalAP]
  linarith

/-- Removing logarithmic weights on a dyadic interval costs only replacing
`log p` by the endpoint bounds `log x` and `log (2*x)`. -/
theorem primeIntervalAP_log_bounds (q a : ℕ) {x u v : ℝ} (hx : 0 < x)
    (hxu : x ≤ u) (huv : u ≤ v) (hvx : v ≤ 2 * x) :
    (((primeIntervalAP q a u v).card : ℕ) : ℝ) * Real.log x ≤
        thetaAP q a v - thetaAP q a u ∧
      thetaAP q a v - thetaAP q a u ≤
        (((primeIntervalAP q a u v).card : ℕ) : ℝ) * Real.log (2 * x) := by
  classical
  rw [thetaAP_sub_eq_sum_interval q a huv]
  constructor
  · calc
      (((primeIntervalAP q a u v).card : ℕ) : ℝ) * Real.log x =
          ∑ p ∈ primeIntervalAP q a u v, Real.log x := by simp
      _ ≤ ∑ p ∈ primeIntervalAP q a u v, Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpI := (Finset.mem_filter.mp hp).1
        have hup : u < (p : ℝ) := Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hpI).1
        exact Real.log_le_log hx (hxu.trans_lt hup).le
  · calc
      (∑ p ∈ primeIntervalAP q a u v, Real.log p) ≤
          ∑ p ∈ primeIntervalAP q a u v, Real.log (2 * x) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpdata := Finset.mem_filter.mp hp
        have hpI := Finset.mem_Ioc.mp hpdata.1
        have hpprime : p.Prime := hpdata.2.1
        have hpv : (p : ℝ) ≤ v :=
          (Nat.cast_le.mpr hpI.2).trans
            (Nat.floor_le (hx.le.trans (hxu.trans huv)))
        exact Real.log_le_log (by exact_mod_cast hpprime.pos) (hpv.trans hvx)
      _ = (((primeIntervalAP q a u v).card : ℕ) : ℝ) * Real.log (2 * x) := by
        simp

/-- On large dyadic blocks, replacing `log x` by `log (2*x)` has arbitrarily
small relative cost. -/
theorem eventually_log_two_mul_le {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ x : ℝ in Filter.atTop,
      Real.log (2 * x) ≤ (1 + ρ) * Real.log x := by
  have hlarge : ∀ᶠ x : ℝ in Filter.atTop,
      Real.log 2 / ρ ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log 2 / ρ))
  filter_upwards [hlarge, eventually_gt_atTop (0 : ℝ)] with x hxlog hx
  rw [Real.log_mul (by norm_num) hx.ne']
  have hρlog : Real.log 2 ≤ ρ * Real.log x := by
    simpa [mul_comm] using (div_le_iff₀ hρ).mp hxlog
  nlinarith

/-- The elementary coefficient inequality used when logarithmic weights are
removed. -/
private theorem one_sub_two_mul_le_ratio {ρ : ℝ} (hρ : 0 ≤ ρ) (_hρlt : ρ < 1) :
    1 - 2 * ρ ≤ (1 - ρ) / (1 + ρ) := by
  apply (le_div_iff₀ (by linarith)).2
  nlinarith [sq_nonneg ρ]

/-- Removing logarithmic weights from an assumed family of uniform theta
estimates.  Separating this elementary implication keeps the analytic input
visible. -/
theorem primeIntervalAP_card_estimate_of_theta {q a : ℕ} (hq : 1 ≤ q)
    (δ ε : ℝ) (hε : 0 < ε)
    (hTheta : ∀ η : ℝ, 0 < η →
      ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
          |(thetaAP q a v - thetaAP q a u) -
              (v - u) / q.totient| ≤
            η * ((v - u) / q.totient)) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
        |(((primeIntervalAP q a u v).card : ℕ) : ℝ) -
            (v - u) / q.totient / Real.log x| ≤
          ε * ((v - u) / q.totient / Real.log x) := by
  let ρ : ℝ := min (ε / 8) (1 / 8)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by positivity) (by norm_num)
  have hρ_le_eps : ρ ≤ ε / 8 := by
    dsimp [ρ]
    exact min_le_left _ _
  have hρ_le_eighth : ρ ≤ 1 / 8 := by
    dsimp [ρ]
    exact min_le_right _ _
  have htwoρ_le_eps : 2 * ρ ≤ ε := by nlinarith
  have hρ_le_eps' : ρ ≤ ε := by nlinarith
  have hρlt : ρ < 1 := lt_of_le_of_lt hρ_le_eighth (by norm_num)
  obtain ⟨Xθ, hXθ3, hXθ⟩ := hTheta ρ hρ
  obtain ⟨Xlog, hXlog⟩ := eventually_atTop.mp (eventually_log_two_mul_le hρ)
  refine ⟨max Xθ Xlog, hXθ3.trans (le_max_left _ _), ?_⟩
  intro x hx u v hxu huv hvx hlen
  have hxθ : Xθ ≤ x := (le_max_left Xθ Xlog).trans hx
  have hxlog : Xlog ≤ x := (le_max_right Xθ Xlog).trans hx
  have hx3 : 3 ≤ x := hXθ3.trans hxθ
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx3
  have hlogpos : 0 < Real.log x := Real.log_pos (lt_of_lt_of_le (by norm_num) hx3)
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  let C : ℝ := (((primeIntervalAP q a u v).card : ℕ) : ℝ)
  let A : ℝ := (v - u) / (q.totient : ℝ)
  let L : ℝ := A / Real.log x
  let S : ℝ := thetaAP q a v - thetaAP q a u
  have hApos : 0 < A := by
    dsimp [A]
    exact div_pos (sub_pos.mpr huv) hφ
  have hLpos : 0 < L := by
    dsimp [L]
    exact div_pos hApos hlogpos
  have htheta := hXθ x hxθ u v hxu huv hvx hlen
  have htheta' : |S - A| ≤ ρ * A := by
    simpa only [S, A] using htheta
  have hthetaBounds : (1 - ρ) * A ≤ S ∧ S ≤ (1 + ρ) * A := by
    rw [abs_le] at htheta'
    constructor <;> linarith
  have hlogs := primeIntervalAP_log_bounds q a hxpos hxu huv.le hvx
  have hlogs' : C * Real.log x ≤ S ∧ S ≤ C * Real.log (2 * x) := by
    simpa only [C, S] using hlogs
  have hlogDist : Real.log (2 * x) ≤ (1 + ρ) * Real.log x := hXlog x hxlog
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hSupper : S ≤ C * ((1 + ρ) * Real.log x) :=
    hlogs'.2.trans (mul_le_mul_of_nonneg_left hlogDist hCnonneg)
  have hCupper : C ≤ (1 + ρ) * L := by
    rw [show (1 + ρ) * L = ((1 + ρ) * A) / Real.log x by
      dsimp [L]
      ring]
    exact (le_div_iff₀ hlogpos).2 (hlogs'.1.trans hthetaBounds.2)
  have hRatioLower : ((1 - ρ) / (1 + ρ)) * L ≤ C := by
    rw [show ((1 - ρ) / (1 + ρ)) * L =
        ((1 - ρ) * A) / ((1 + ρ) * Real.log x) by
      dsimp [L]
      field_simp]
    apply (div_le_iff₀ (mul_pos (by linarith) hlogpos)).2
    exact hthetaBounds.1.trans hSupper
  have hClower : (1 - 2 * ρ) * L ≤ C := by
    exact (mul_le_mul_of_nonneg_right
      (one_sub_two_mul_le_ratio hρ.le hρlt) hLpos.le).trans hRatioLower
  change |C - L| ≤ ε * L
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr htwoρ_le_eps) hLpos.le]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hρ_le_eps') hLpos.le]

/-- The axiom-free PNT in arithmetic progressions already available in this
repository, restated using `thetaAP`. -/
theorem thetaAP_isEquivalent {q a : ℕ} (hq : 1 ≤ q) (ha : a.Coprime q)
    (haq : a < q) :
    thetaAP q a ~[Filter.atTop] (fun x : ℝ => x / q.totient) := by
  change
    (fun x : ℝ => ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
      if p % q = a then Real.log p else 0) ~[Filter.atTop]
        (fun x : ℝ => x / q.totient)
  exact chebyshev_asymptotic_pnt hq ha haq

/-- Arbitrarily accurate relative control of `thetaAP` beyond a fixed
threshold. -/
theorem eventually_thetaAP_ratio_close {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in Filter.atTop,
      |thetaAP q a x / (x / q.totient) - 1| < η := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hden : ∀ᶠ x : ℝ in Filter.atTop, x / (q.totient : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_ne_zero hx.ne' hφ.ne'
  have hratio : Filter.Tendsto
      (fun x : ℝ => thetaAP q a x / (x / q.totient))
      Filter.atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hden).mp
      (thetaAP_isEquivalent hq ha haq)
  exact hratio.eventually (Metric.ball_mem_nhds 1 hη)

/-- Relative ratio control rewritten as an additive error estimate. -/
theorem eventually_thetaAP_abs_sub_le {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ x : ℝ in Filter.atTop,
      |thetaAP q a x - x / q.totient| ≤ η * (x / q.totient) := by
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  filter_upwards [eventually_thetaAP_ratio_close hq ha haq hη,
    eventually_gt_atTop (0 : ℝ)] with x hxclose hx
  have hmain : 0 < x / (q.totient : ℝ) := div_pos hx hφ
  have hid :
      thetaAP q a x - x / q.totient =
        (thetaAP q a x / (x / q.totient) - 1) * (x / q.totient) := by
    field_simp
  rw [hid, abs_mul, abs_of_pos hmain]
  exact mul_le_mul_of_nonneg_right hxclose.le hmain.le

/-- Uniform control of theta increments on every interval of relative length
at least `δ` inside a dyadic block.  This is the weighted fixed-modulus PNT
input used before removing logarithmic weights. -/
theorem thetaAP_dyadic_interval_estimate {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
        |(thetaAP q a v - thetaAP q a u) -
            (v - u) / q.totient| ≤
          ε * ((v - u) / q.totient) := by
  let η : ℝ := ε * δ / 8
  have hη : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (eventually_thetaAP_abs_sub_le hq ha haq hη)
  refine ⟨max 3 X, le_max_left _ _, ?_⟩
  intro x hx u v hxu huv hvx hlen
  have hXu : X ≤ u := le_trans (le_trans (le_max_right 3 X) hx) hxu
  have hXv : X ≤ v := hXu.trans huv.le
  have huerr := hX u hXu
  have hverr := hX v hXv
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left 3 X) hx)
  have hupos : 0 < u := hxpos.trans_le hxu
  have hvpos : 0 < v := hupos.trans huv
  have hrewrite :
      (thetaAP q a v - thetaAP q a u) - (v - u) / q.totient =
        (thetaAP q a v - v / q.totient) -
          (thetaAP q a u - u / q.totient) := by
    ring
  rw [hrewrite]
  calc
    |(thetaAP q a v - v / q.totient) -
        (thetaAP q a u - u / q.totient)|
        ≤ |thetaAP q a v - v / q.totient| +
            |thetaAP q a u - u / q.totient| := abs_sub _ _
    _ ≤ η * (v / q.totient) + η * (u / q.totient) :=
      add_le_add hverr huerr
    _ ≤ η * ((4 * x) / q.totient) := by
      have hu_le : u ≤ 2 * x := huv.le.trans hvx
      have huvsum : u + v ≤ 4 * x := by linarith
      rw [show η * (v / (q.totient : ℝ)) + η * (u / q.totient) =
        η * ((u + v) / q.totient) by ring]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right huvsum hφ.le) hη.le
    _ ≤ ε * ((v - u) / q.totient) := by
      rw [show η * ((4 * x) / (q.totient : ℝ)) =
        ε * ((δ * x / 2) / q.totient) by
          dsimp [η]
          ring]
      apply mul_le_mul_of_nonneg_left _ hε.le
      apply div_le_div_of_nonneg_right _ hφ.le
      nlinarith

/-- Fixed-modulus PNT on all relatively long subintervals of a dyadic block,
in the exact unweighted form needed by the covering argument. -/
theorem primeIntervalAP_card_estimate {q a : ℕ} (hq : 1 ≤ q)
    (ha : a.Coprime q) (haq : a < q) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
        |(((primeIntervalAP q a u v).card : ℕ) : ℝ) -
            (v - u) / q.totient / Real.log x| ≤
          ε * ((v - u) / q.totient / Real.log x) := by
  apply primeIntervalAP_card_estimate_of_theta hq δ ε hε
  intro η hη
  exact thetaAP_dyadic_interval_estimate hq ha haq δ η hδ hη

/-- The fixed-modulus analytic input used by the public covering
formalization, now proved from `WeakPNT_AP` rather than assumed. -/
theorem PNT_fixed_modulus (q a : ℕ) (hq : 1 ≤ q) (haq : a < q)
    (hcop : a.Coprime q) (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
        |(((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter
            (fun p => p.Prime ∧ p % q = a)).card : ℝ)
          - (v - u) / ((Nat.totient q : ℝ) * Real.log x)|
        ≤ ε * (v - u) / ((Nat.totient q : ℝ) * Real.log x) := by
  obtain ⟨x₀, hx₀, hmain⟩ :=
    primeIntervalAP_card_estimate hq hcop haq δ ε hδ hε
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx u v hxu huv hvx hlen
  have h := hmain x hx u v hxu huv hvx hlen
  simpa only [primeIntervalAP, div_div, mul_div_assoc] using h

/-- For every fixed modulus, reduced residue, and fixed shift, the shifted
dyadic interval `(X-h, 2X-h]` eventually contains at least a constant
multiple of the PNT main term.  The proof keeps the shorter unshifted block
`(X-h, 2(X-h)]` and applies `PNT_fixed_modulus` there.

This is the fixed-parameter precursor of the growing-modulus
Siegel--Walfisz estimate used in the BNPZ covering construction. -/
theorem eventually_fixed_shifted_dyadic_lower_real
    (Q a h : ℕ) (hQ : 2 ≤ Q) (hcop : a.Coprime Q) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.Ioc (X - h) (2 * X - h)).filter
          (fun p => p.Prime ∧ p % Q = a % Q)).card : ℝ) ≥
        ((X - h : ℕ) : ℝ) /
          (2 * ((Nat.totient Q : ℝ) *
            Real.log ((X - h : ℕ) : ℝ))) := by
  have hQpos : 0 < Q := by omega
  have hreslt : a % Q < Q := Nat.mod_lt _ hQpos
  have hrescop : (a % Q).Coprime Q :=
    (ZMod.coprime_mod_iff_coprime a Q).2 hcop
  obtain ⟨x₀, hx₀3, hmain⟩ :=
    PNT_fixed_modulus Q (a % Q) (by omega) hreslt hrescop
      1 (by norm_num) (1 / 2) (by norm_num)
  filter_upwards [eventually_ge_atTop (Nat.ceil x₀ + h)] with X hX
  let Y := X - h
  have hhX : h ≤ X := by omega
  have hYcast : x₀ ≤ (Y : ℝ) := by
    dsimp [Y]
    rw [Nat.cast_sub hhX]
    have hceil : x₀ ≤ (Nat.ceil x₀ : ℝ) := Nat.le_ceil x₀
    exact hceil.trans (by exact_mod_cast (Nat.le_sub_of_add_le hX))
  have hY3 : 3 ≤ Y := by
    exact_mod_cast hx₀3.trans hYcast
  have hYpos : 0 < Y := by omega
  have huvt : (Y : ℝ) < ((2 * Y : ℕ) : ℝ) := by
    exact_mod_cast (show Y < 2 * Y by omega)
  have hcast2 : ((2 * Y : ℕ) : ℝ) = 2 * (Y : ℝ) := by norm_num
  have hvx : ((2 * Y : ℕ) : ℝ) ≤ 2 * (Y : ℝ) := hcast2.le
  have hlen : (1 : ℝ) * Y ≤ ((2 * Y : ℕ) : ℝ) - Y := by
    rw [hcast2]
    linarith
  have hestimate := hmain (Y : ℝ) hYcast (Y : ℝ) ((2 * Y : ℕ) : ℝ)
    le_rfl huvt hvx hlen
  have hestimate' :
      |((((Finset.Ioc Y (2 * Y)).filter
          (fun p => p.Prime ∧ p % Q = a % Q)).card : ℕ) : ℝ) -
          (Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log Y)| ≤
        (1 / 2 : ℝ) *
          ((Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log Y)) := by
    simp only [Nat.floor_natCast] at hestimate
    rw [hcast2] at hestimate
    ring_nf at hestimate ⊢
    exact hestimate
  have hsmall :
      ((Y : ℝ) / (2 * ((Nat.totient Q : ℝ) * Real.log Y))) ≤
        ((((Finset.Ioc Y (2 * Y)).filter
          (fun p => p.Prime ∧ p % Q = a % Q)).card : ℕ) : ℝ) := by
    rw [abs_le] at hestimate'
    have hhalf :
        (1 / 2 : ℝ) *
            ((Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log Y)) ≤
          ((((Finset.Ioc Y (2 * Y)).filter
            (fun p => p.Prime ∧ p % Q = a % Q)).card : ℕ) : ℝ) := by
      linarith [hestimate'.1]
    rw [show (Y : ℝ) / (2 * ((Nat.totient Q : ℝ) * Real.log Y)) =
        (1 / 2 : ℝ) *
          ((Y : ℝ) / ((Nat.totient Q : ℝ) * Real.log Y)) by ring]
    exact hhalf
  have hupper : 2 * Y ≤ 2 * X - h := by
    dsimp [Y]
    omega
  have hsubset :
      (Finset.Ioc Y (2 * Y)).filter
          (fun p => p.Prime ∧ p % Q = a % Q) ⊆
        (Finset.Ioc (X - h) (2 * X - h)).filter
          (fun p => p.Prime ∧ p % Q = a % Q) := by
    dsimp [Y]
    exact Finset.filter_subset_filter _
      (Finset.Ioc_subset_Ioc le_rfl hupper)
  have hcard := Finset.card_le_card hsubset
  exact hsmall.trans (Nat.cast_le.mpr hcard)

/-- The real logarithm of a positive natural is bounded by its binary
integer logarithm plus one. -/
theorem real_log_nat_le_log_two_add_one (X : ℕ) (hX : 1 ≤ X) :
    Real.log (X : ℝ) ≤ (Nat.log 2 X + 1 : ℕ) := by
  have hpowNat : X < 2 ^ (Nat.log 2 X).succ :=
    Nat.lt_pow_succ_log_self Nat.one_lt_two X
  have hXpos : (0 : ℝ) < X := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (Nat.log 2 X).succ := by
    positivity
  have hloglt : Real.log (X : ℝ) <
      Real.log ((2 : ℝ) ^ (Nat.log 2 X).succ) :=
    Real.strictMonoOn_log hXpos hpowpos (by exact_mod_cast hpowNat)
  rw [Real.log_pow] at hloglt
  have hlogtwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  calc
    Real.log (X : ℝ) ≤ ((Nat.log 2 X).succ : ℝ) * Real.log 2 := hloglt.le
    _ ≤ ((Nat.log 2 X).succ : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hlogtwo (by positivity)
    _ = (Nat.log 2 X + 1 : ℕ) := by norm_num

/-- Exact fixed-parameter version of the shifted lower bound used by the
public cover formalization.  The conclusion now has the same natural-number
cardinality and binary-logarithm denominator as its Siegel--Walfisz input;
only uniformity as `Q` and `h` grow with `X` is absent. -/
theorem eventually_fixed_shifted_dyadic_lower
    (Q a h : ℕ) (hQ : 2 ≤ Q) (hcop : a.Coprime Q) :
    ∀ᶠ X : ℕ in Filter.atTop,
      ((Finset.Ioc (X - h) (2 * X - h)).filter
          (fun p => p.Prime ∧ p % Q = a % Q)).card
        ≥ X / (8 * Q * (Nat.log 2 X + 1)) := by
  filter_upwards [eventually_fixed_shifted_dyadic_lower_real Q a h hQ hcop,
    eventually_ge_atTop (2 * h + 4)] with X hreal hX
  let Y := X - h
  let L := Nat.log 2 X + 1
  have hXpos : 0 < X := by omega
  have hYtwo : 2 ≤ Y := by
    dsimp [Y]
    omega
  have hYpos : 0 < Y := by omega
  have hYX : Y ≤ X := Nat.sub_le _ _
  have hXtwoY : X ≤ 2 * Y := by
    dsimp [Y]
    omega
  have hLpos : 0 < L := by
    dsimp [L]
    omega
  have hphiNat : Q.totient ≤ Q := Nat.totient_le Q
  have hphiPos : 0 < Q.totient := Nat.totient_pos.mpr (by omega)
  have hlogYpos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hlogYX : Real.log (Y : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (by exact_mod_cast hYpos) (by exact_mod_cast hYX)
  have hlogXL : Real.log (X : ℝ) ≤ (L : ℝ) := by
    dsimp [L]
    exact real_log_nat_le_log_two_add_one X (by omega)
  have hlogYL : Real.log (Y : ℝ) ≤ (L : ℝ) := hlogYX.trans hlogXL
  have hdenNatPos : (0 : ℝ) < 8 * Q * L := by positivity
  have hdenRealPos : (0 : ℝ) <
      2 * ((Q.totient : ℝ) * Real.log (Y : ℝ)) := by positivity
  have hcastDen : ((8 * Q * L : ℕ) : ℝ) = 8 * Q * L := by norm_num
  have hratio :
      (X : ℝ) / ((8 * Q * L : ℕ) : ℝ) ≤
        (Y : ℝ) /
          (2 * ((Q.totient : ℝ) * Real.log (Y : ℝ))) := by
    rw [hcastDen]
    rw [div_le_div_iff₀ hdenNatPos hdenRealPos]
    calc
      (X : ℝ) * (2 * ((Q.totient : ℝ) * Real.log (Y : ℝ)))
          ≤ (2 * Y : ℝ) *
              (2 * ((Q.totient : ℝ) * Real.log (Y : ℝ))) := by
            gcongr
            exact_mod_cast hXtwoY
      _ = 4 * Y * Q.totient * Real.log (Y : ℝ) := by ring
      _ ≤ 4 * Y * Q * Real.log (Y : ℝ) := by gcongr
      _ ≤ 4 * Y * Q * L := by gcongr
      _ ≤ 8 * Y * Q * L := by
        gcongr
        norm_num
      _ = (Y : ℝ) * (8 * (Q : ℝ) * (L : ℝ)) := by ring
  have hcastDiv :
      ((X / (8 * Q * L) : ℕ) : ℝ) ≤
        (X : ℝ) / ((8 * Q * L : ℕ) : ℝ) := Nat.cast_div_le
  have hcastCard :
      ((X / (8 * Q * L) : ℕ) : ℝ) ≤
        (((Finset.Ioc (X - h) (2 * X - h)).filter
          (fun p => p.Prime ∧ p % Q = a % Q)).card : ℝ) := by
    exact hcastDiv.trans (hratio.trans (by simpa [Y] using hreal))
  exact_mod_cast hcastCard

/-- Finitely many fixed shifted residue classes have a single common
threshold.  Thus the remaining analytic gap is specifically uniformity for a
family whose moduli and shifts grow with `X`, not merely simultaneous control
of any prescribed finite family. -/
theorem eventually_finite_fixed_shifted_dyadic_lower_real
    {ι : Type*} [Finite ι] (Q a h : ι → ℕ)
    (hQ : ∀ i, 2 ≤ Q i) (hcop : ∀ i, (a i).Coprime (Q i)) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ i,
      (((Finset.Ioc (X - h i) (2 * X - h i)).filter
          (fun p => p.Prime ∧ p % Q i = a i % Q i)).card : ℝ) ≥
        ((X - h i : ℕ) : ℝ) /
          (2 * ((Nat.totient (Q i) : ℝ) *
            Real.log ((X - h i : ℕ) : ℝ))) := by
  exact Filter.eventually_all.2 fun i =>
    eventually_fixed_shifted_dyadic_lower_real
      (Q i) (a i) (h i) (hQ i) (hcop i)

/-- Exact natural-number version, simultaneously for any fixed finite
family. -/
theorem eventually_finite_fixed_shifted_dyadic_lower
    {ι : Type*} [Finite ι] (Q a h : ι → ℕ)
    (hQ : ∀ i, 2 ≤ Q i) (hcop : ∀ i, (a i).Coprime (Q i)) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ i,
      ((Finset.Ioc (X - h i) (2 * X - h i)).filter
          (fun p => p.Prime ∧ p % Q i = a i % Q i)).card
        ≥ X / (8 * Q i * (Nat.log 2 X + 1)) := by
  exact Filter.eventually_all.2 fun i =>
    eventually_fixed_shifted_dyadic_lower
      (Q i) (a i) (h i) (hQ i) (hcop i)

/-- One threshold works for every modulus, residue, and shift below a fixed
bound `M`.  This is the strongest consequence of finite uniformization alone;
the Siegel--Walfisz input needs the bound itself to grow with `X`. -/
theorem eventually_bounded_shifted_dyadic_lower (M : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ Q a h : ℕ,
      2 ≤ Q → Q ≤ M → h ≤ M → a.Coprime Q →
        ((Finset.Ioc (X - h) (2 * X - h)).filter
            (fun p => p.Prime ∧ p % Q = a % Q)).card
          ≥ X / (8 * Q * (Nat.log 2 X + 1)) := by
  have hall : ∀ᶠ X : ℕ in Filter.atTop,
      ∀ Q ∈ Finset.range (M + 1),
      ∀ r ∈ Finset.range (M + 1),
      ∀ h ∈ Finset.range (M + 1),
        2 ≤ Q → r.Coprime Q →
          ((Finset.Ioc (X - h) (2 * X - h)).filter
              (fun p => p.Prime ∧ p % Q = r % Q)).card
            ≥ X / (8 * Q * (Nat.log 2 X + 1)) := by
    rw [Finset.eventually_all]
    intro Q _hQM
    rw [Finset.eventually_all]
    intro r _hrM
    rw [Finset.eventually_all]
    intro h _hhM
    by_cases hQ : 2 ≤ Q
    · by_cases hcop : r.Coprime Q
      · filter_upwards [eventually_fixed_shifted_dyadic_lower Q r h hQ hcop]
          with X hX
        intro _ _
        exact hX
      · exact Filter.Eventually.of_forall fun _ _ hcop' => (hcop hcop').elim
    · exact Filter.Eventually.of_forall fun _ hQ' _ => (hQ hQ').elim
  filter_upwards [hall] with X hX
  intro Q a h hQ hQM hhM hcop
  have hQmem : Q ∈ Finset.range (M + 1) := Finset.mem_range.2 (by omega)
  have hrltQ : a % Q < Q := Nat.mod_lt _ (by omega)
  have hrmem : a % Q ∈ Finset.range (M + 1) :=
    Finset.mem_range.2 (by omega)
  have hhmem : h ∈ Finset.range (M + 1) := Finset.mem_range.2 (by omega)
  have hrcop : (a % Q).Coprime Q :=
    (ZMod.coprime_mod_iff_coprime a Q).2 hcop
  simpa using hX Q hQmem (a % Q) hrmem h hhmem hQ hrcop

/-- Threshold form of `eventually_bounded_shifted_dyadic_lower`, with the
same quantifier order as the public Siegel--Walfisz input except that its
parameter bound is the fixed number `M`. -/
theorem bounded_shifted_dyadic_lower (M : ℕ) :
    ∃ X₀ : ℕ, ∀ X Q a h : ℕ,
      X₀ ≤ X → 2 ≤ Q → Q ≤ M → h ≤ M → a.Coprime Q →
        ((Finset.Ioc (X - h) (2 * X - h)).filter
            (fun p => p.Prime ∧ p % Q = a % Q)).card
          ≥ X / (8 * Q * (Nat.log 2 X + 1)) := by
  obtain ⟨X₀, hX₀⟩ :=
    eventually_atTop.mp (eventually_bounded_shifted_dyadic_lower M)
  exact ⟨X₀, fun X Q a h hX hQ hQM hhM hcop =>
    hX₀ X hX Q a h hQ hQM hhM hcop⟩

/- Namespace-compatible adapter for the authors' public cover files. -/
namespace ANT

theorem PNT_fixed_modulus (q a : ℕ) (hq : 1 ≤ q) (haq : a < q)
    (hcop : a.Coprime q) (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ u v : ℝ, x ≤ u → u < v → v ≤ 2 * x → δ * x ≤ v - u →
        |(((Finset.Ioc ⌊u⌋₊ ⌊v⌋₊).filter
            (fun p => p.Prime ∧ p % q = a)).card : ℝ)
          - (v - u) / ((Nat.totient q : ℝ) * Real.log x)|
        ≤ ε * (v - u) / ((Nat.totient q : ℝ) * Real.log x) :=
  Erdos387.PNT_fixed_modulus q a hq haq hcop δ hδ ε hε

theorem eventually_fixed_shifted_dyadic_lower_real
    (Q a h : ℕ) (hQ : 2 ≤ Q) (hcop : a.Coprime Q) :
    ∀ᶠ X : ℕ in Filter.atTop,
      (((Finset.Ioc (X - h) (2 * X - h)).filter
          (fun p => p.Prime ∧ p % Q = a % Q)).card : ℝ) ≥
        ((X - h : ℕ) : ℝ) /
          (2 * ((Nat.totient Q : ℝ) *
            Real.log ((X - h : ℕ) : ℝ))) :=
  Erdos387.eventually_fixed_shifted_dyadic_lower_real Q a h hQ hcop

theorem eventually_finite_fixed_shifted_dyadic_lower_real
    {ι : Type*} [Finite ι] (Q a h : ι → ℕ)
    (hQ : ∀ i, 2 ≤ Q i) (hcop : ∀ i, (a i).Coprime (Q i)) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ i,
      (((Finset.Ioc (X - h i) (2 * X - h i)).filter
          (fun p => p.Prime ∧ p % Q i = a i % Q i)).card : ℝ) ≥
        ((X - h i : ℕ) : ℝ) /
          (2 * ((Nat.totient (Q i) : ℝ) *
            Real.log ((X - h i : ℕ) : ℝ))) :=
  Erdos387.eventually_finite_fixed_shifted_dyadic_lower_real Q a h hQ hcop

theorem eventually_fixed_shifted_dyadic_lower
    (Q a h : ℕ) (hQ : 2 ≤ Q) (hcop : a.Coprime Q) :
    ∀ᶠ X : ℕ in Filter.atTop,
      ((Finset.Ioc (X - h) (2 * X - h)).filter
          (fun p => p.Prime ∧ p % Q = a % Q)).card
        ≥ X / (8 * Q * (Nat.log 2 X + 1)) :=
  Erdos387.eventually_fixed_shifted_dyadic_lower Q a h hQ hcop

theorem eventually_finite_fixed_shifted_dyadic_lower
    {ι : Type*} [Finite ι] (Q a h : ι → ℕ)
    (hQ : ∀ i, 2 ≤ Q i) (hcop : ∀ i, (a i).Coprime (Q i)) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ i,
      ((Finset.Ioc (X - h i) (2 * X - h i)).filter
          (fun p => p.Prime ∧ p % Q i = a i % Q i)).card
        ≥ X / (8 * Q i * (Nat.log 2 X + 1)) :=
  Erdos387.eventually_finite_fixed_shifted_dyadic_lower Q a h hQ hcop

theorem eventually_bounded_shifted_dyadic_lower (M : ℕ) :
    ∀ᶠ X : ℕ in Filter.atTop, ∀ Q a h : ℕ,
      2 ≤ Q → Q ≤ M → h ≤ M → a.Coprime Q →
        ((Finset.Ioc (X - h) (2 * X - h)).filter
            (fun p => p.Prime ∧ p % Q = a % Q)).card
          ≥ X / (8 * Q * (Nat.log 2 X + 1)) :=
  Erdos387.eventually_bounded_shifted_dyadic_lower M

theorem bounded_shifted_dyadic_lower (M : ℕ) :
    ∃ X₀ : ℕ, ∀ X Q a h : ℕ,
      X₀ ≤ X → 2 ≤ Q → Q ≤ M → h ≤ M → a.Coprime Q →
        ((Finset.Ioc (X - h) (2 * X - h)).filter
            (fun p => p.Prime ∧ p % Q = a % Q)).card
          ≥ X / (8 * Q * (Nat.log 2 X + 1)) :=
  Erdos387.bounded_shifted_dyadic_lower M

end ANT

end Erdos387
