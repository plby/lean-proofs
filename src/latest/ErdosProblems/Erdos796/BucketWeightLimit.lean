import ErdosProblems.Erdos796.BaselineAsymptotic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A fixed large-prime bucket

For a fixed positive cofactor `j`, this file identifies the `j`-th bucket
exactly with a short interval of primes and derives its asymptotic weight from
the prime number theorem.
-/

namespace Erdos796

open Filter Topology
open scoped BigOperators Nat.Prime

/-- A quotient has value `j` precisely on its usual half-open interval. -/
theorem nat_div_eq_iff_cofactor_interval {n q j : ℕ}
    (hq : 0 < q) (hj : 0 < j) :
    n / q = j ↔ n / (j + 1) < q ∧ q ≤ n / j := by
  constructor
  · intro h
    have hjle : j ≤ n / q := h.ge
    have hjlt : n / q < j + 1 := by omega
    have hjmul : j * q ≤ n := (Nat.le_div_iff_mul_le hq).mp hjle
    have hnlt : n < (j + 1) * q := (Nat.div_lt_iff_lt_mul hq).mp hjlt
    constructor
    · exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mpr (by
        simpa [Nat.mul_comm] using! hnlt)
    · exact (Nat.le_div_iff_mul_le hj).mpr (by
        simpa [Nat.mul_comm] using! hjmul)
  · rintro ⟨hlower, hupper⟩
    have hnlt : n < q * (j + 1) :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos j)).mp hlower
    have hqmul : q * j ≤ n := (Nat.le_div_iff_mul_le hj).mp hupper
    have hjle : j ≤ n / q := (Nat.le_div_iff_mul_le hq).mpr (by
      simpa [Nat.mul_comm] using! hqmul)
    have hjlt : n / q < j + 1 := (Nat.div_lt_iff_lt_mul hq).mpr (by
      simpa [Nat.mul_comm] using! hnlt)
    omega

/-- Once `n ≥ (d+1)²`, the interval cut `n/d` lies strictly above `√n`. -/
theorem sqrt_lt_natDiv_of_sq_le {n d : ℕ} (hd : 0 < d)
    (hlarge : (d + 1) * (d + 1) ≤ n) :
    n.sqrt < n / d := by
  have hdsqrt : d + 1 ≤ n.sqrt := Nat.le_sqrt.mpr hlarge
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hd]
  nlinarith [Nat.sqrt_le n]

/-- Above the explicit square-root threshold, a fixed cofactor bucket is
exactly the interval of primes `(n/(j+1), n/j]`. -/
theorem bucketFinset_eq_newPrimes {n j : ℕ} (hj : 0 < j)
    (hlarge : (j + 2) * (j + 2) ≤ n) :
    ((Finset.Ioc n.sqrt n).filter fun q => q.Prime ∧ n / q = j) =
      newPrimes (n / (j + 1)) (n / j) := by
  have hsqrt : n.sqrt < n / (j + 1) := by
    apply sqrt_lt_natDiv_of_sq_le (d := j + 1) (by omega)
    simpa [Nat.add_assoc] using! hlarge
  ext q
  simp only [Finset.mem_filter, Finset.mem_Ioc, mem_newPrimes]
  constructor
  · rintro ⟨⟨hroot, hqn⟩, hprime, hdiv⟩
    have hinterval := (nat_div_eq_iff_cofactor_interval hprime.pos hj).mp hdiv
    exact ⟨hinterval.1, hinterval.2, hprime⟩
  · rintro ⟨hlower, hupper, hprime⟩
    refine ⟨⟨hsqrt.trans hlower, ?_⟩, hprime, ?_⟩
    · exact hupper.trans (Nat.div_le_self n j)
    · exact (nat_div_eq_iff_cofactor_interval hprime.pos hj).mpr
        ⟨hlower, hupper⟩

/-- Exact eventual prime-counting formula for a fixed bucket. -/
theorem bucketCount_eq_primeCounting_sub {n j : ℕ} (hj : 0 < j)
    (hlarge : (j + 2) * (j + 2) ≤ n) :
    bucketCount n j =
      Nat.primeCounting (n / j) - Nat.primeCounting (n / (j + 1)) := by
  rw [bucketCount, bucketFinset_eq_newPrimes hj hlarge]
  exact card_newPrimes (Nat.div_le_div_left (Nat.le_succ j) hj)

/-- A fixed natural floor quotient has the expected real-valued ratio. -/
theorem natDiv_cast_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => ((n / d : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 / (d : ℝ))) := by
  have hmod : Tendsto (fun n : ℕ => ((n % d : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := tendsto_mod_div_atTop_nhds_zero_nat hd
  have hmain : Tendsto
      (fun n : ℕ =>
        (1 - ((n % d : ℕ) : ℝ) / (n : ℝ)) / (d : ℝ))
      atTop (nhds ((1 - 0) / (d : ℝ))) :=
    (tendsto_const_nhds.sub hmod).div_const (d : ℝ)
  have heq : ∀ᶠ n : ℕ in atTop,
      ((n / d : ℕ) : ℝ) / (n : ℝ) =
        (1 - ((n % d : ℕ) : ℝ) / (n : ℝ)) / (d : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hdecomp :
        ((n % d : ℕ) : ℝ) + (d : ℝ) * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.mod_add_div n d
    field_simp
    linarith
  simpa using! hmain.congr' (heq.mono fun _ h => h.symm)

/-- Dividing a natural variable by a fixed positive integer preserves the
logarithmic scale. -/
theorem log_natDiv_div_log_tendsto_one (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun n : ℕ => Real.log ((n / d : ℕ) : ℝ) / Real.log (n : ℝ))
      atTop (nhds 1) := by
  have hratio := natDiv_cast_ratio_tendsto d hd
  have hdreal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlimit_ne : (1 / (d : ℝ)) ≠ 0 := by positivity
  have hlogratio : Tendsto
      (fun n : ℕ => Real.log (((n / d : ℕ) : ℝ) / (n : ℝ)))
      atTop (nhds (Real.log (1 / (d : ℝ)))) :=
    (Real.continuousAt_log hlimit_ne).tendsto.comp hratio
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto
      (fun n : ℕ =>
        Real.log (((n / d : ℕ) : ℝ) / (n : ℝ)) / Real.log (n : ℝ))
      atTop (nhds 0) := hlogratio.div_atTop hlogn
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsum : Tendsto
      (fun n : ℕ =>
        Real.log (((n / d : ℕ) : ℝ) / (n : ℝ)) / Real.log (n : ℝ) + 1)
      atTop (nhds (0 + 1)) := hsmall.add hone
  have heq : ∀ᶠ n : ℕ in atTop,
      Real.log ((n / d : ℕ) : ℝ) / Real.log (n : ℝ) =
        Real.log (((n / d : ℕ) : ℝ) / (n : ℝ)) / Real.log (n : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop (d + 1)] with n hn
    have hdn : d ≤ n := by omega
    have hnpos : 0 < n := hd.trans_le hdn
    have hquotpos : 0 < n / d := Nat.div_pos hdn hd
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hquot0 : ((n / d : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Real.log_div hquot0 hn0]
    have hlogn0 : Real.log (n : ℝ) ≠ 0 := by
      have : 1 < n := by omega
      exact (Real.log_pos (by exact_mod_cast this)).ne'
    field_simp
    ring
  simpa using! hsum.congr' (heq.mono fun _ h => h.symm)

/-- The second-order scale at `⌊n/d⌋`, when measured with the normalization
`log n / n`, has limiting mass `1/d`. -/
theorem secondOrderScale_natDiv_weight_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun n : ℕ =>
        secondOrderScale (n / d) * (Real.log (n : ℝ) / (n : ℝ)))
      atTop (nhds (1 / (d : ℝ))) := by
  have hratio := natDiv_cast_ratio_tendsto d hd
  have hlogratio := log_natDiv_div_log_tendsto_one d hd
  have hinv : Tendsto
      (fun n : ℕ =>
        (Real.log ((n / d : ℕ) : ℝ) / Real.log (n : ℝ))⁻¹)
      atTop (nhds (1 : ℝ)) := by
    simpa using! hlogratio.inv₀ one_ne_zero
  have hprod : Tendsto
      (fun n : ℕ =>
        (((n / d : ℕ) : ℝ) / (n : ℝ)) *
          (Real.log ((n / d : ℕ) : ℝ) / Real.log (n : ℝ))⁻¹)
      atTop (nhds ((1 / (d : ℝ)) * 1)) := hratio.mul hinv
  have heq : ∀ᶠ n : ℕ in atTop,
      secondOrderScale (n / d) * (Real.log (n : ℝ) / (n : ℝ)) =
        (((n / d : ℕ) : ℝ) / (n : ℝ)) *
          (Real.log ((n / d : ℕ) : ℝ) / Real.log (n : ℝ))⁻¹ := by
    filter_upwards [eventually_ge_atTop (2 * d)] with n hn
    have hm2 : 2 ≤ n / d := by
      rw [Nat.le_div_iff_mul_le hd]
      exact hn
    have hn2 : 2 ≤ n := by
      calc
        2 ≤ 2 * d := by omega
        _ ≤ n := hn
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hm0 : ((n / d : ℕ) : ℝ) ≠ 0 := by positivity
    have hlogn0 : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
    have hlogm0 : Real.log ((n / d : ℕ) : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < n / d by omega))).ne'
    simp only [secondOrderScale]
    field_simp
  simpa using! hprod.congr' (heq.mono fun _ h => h.symm)

/-- PNT on the dilated floor sequence `⌊n/d⌋`. -/
theorem primeCounting_natDiv_weight_tendsto
    (hPNT : PrimeNumberTheorem) (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (n : ℝ) / (n : ℝ)) *
          (Nat.primeCounting (n / d) : ℝ))
      atTop (nhds (1 / (d : ℝ))) := by
  have hquotTop : Tendsto (fun n : ℕ => n / d) atTop atTop :=
    Nat.tendsto_div_const_atTop hd.ne'
  have hpnt : Tendsto
      (fun n : ℕ =>
        (Nat.primeCounting (n / d) : ℝ) /
          secondOrderScale (n / d))
      atTop (nhds 1) := hPNT.comp hquotTop
  have hscale := secondOrderScale_natDiv_weight_tendsto d hd
  have hprod : Tendsto
      (fun n : ℕ =>
        ((Nat.primeCounting (n / d) : ℝ) /
            secondOrderScale (n / d)) *
          (secondOrderScale (n / d) *
            (Real.log (n : ℝ) / (n : ℝ))))
      atTop (nhds (1 * (1 / (d : ℝ)))) := hpnt.mul hscale
  have heq : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ) / (n : ℝ)) *
          (Nat.primeCounting (n / d) : ℝ) =
        ((Nat.primeCounting (n / d) : ℝ) /
            secondOrderScale (n / d)) *
          (secondOrderScale (n / d) *
            (Real.log (n : ℝ) / (n : ℝ))) := by
    filter_upwards [eventually_ge_atTop (2 * d)] with n hn
    have hm2 : 2 ≤ n / d := by
      rw [Nat.le_div_iff_mul_le hd]
      exact hn
    have hscale0 : secondOrderScale (n / d) ≠ 0 := by
      simp only [secondOrderScale]
      have hmpos : (0 : ℝ) < (n / d : ℕ) := by positivity
      have hlogmpos : 0 < Real.log ((n / d : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n / d by omega))
      positivity
    field_simp
  simpa using! hprod.congr' (heq.mono fun _ h => h.symm)

/-- Eventual form of the exact bucket formula, convenient for asymptotics. -/
theorem eventually_bucketCount_eq_primeCounting_sub (j : ℕ) (hj : 0 < j) :
    ∀ᶠ n : ℕ in atTop,
      bucketCount n j =
        Nat.primeCounting (n / j) -
          Nat.primeCounting (n / (j + 1)) := by
  filter_upwards [eventually_ge_atTop ((j + 2) * (j + 2))] with n hn
  exact bucketCount_eq_primeCounting_sub hj hn

/-- For each fixed positive cofactor, the normalized bucket count tends to
its cofactor weight.  The sole analytic input is the normalized PNT
proposition already isolated in `BaselineAsymptotic`. -/
theorem bucketCount_weight_tendsto
    (hPNT : PrimeNumberTheorem) (j : ℕ) (hj : 0 < j) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (n : ℝ) / (n : ℝ)) * (bucketCount n j : ℝ))
      atTop (nhds (cofactorWeight j)) := by
  have hjterm := primeCounting_natDiv_weight_tendsto hPNT j hj
  have hsucc : 0 < j + 1 := Nat.succ_pos j
  have hsuccTerm := primeCounting_natDiv_weight_tendsto hPNT (j + 1) hsucc
  have hdiff : Tendsto
      (fun n : ℕ =>
        (Real.log (n : ℝ) / (n : ℝ)) *
            (Nat.primeCounting (n / j) : ℝ) -
          (Real.log (n : ℝ) / (n : ℝ)) *
            (Nat.primeCounting (n / (j + 1)) : ℝ))
      atTop
      (nhds (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ))) :=
    hjterm.sub hsuccTerm
  have heq : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ) / (n : ℝ)) * (bucketCount n j : ℝ) =
        (Real.log (n : ℝ) / (n : ℝ)) *
            (Nat.primeCounting (n / j) : ℝ) -
          (Real.log (n : ℝ) / (n : ℝ)) *
            (Nat.primeCounting (n / (j + 1)) : ℝ) := by
    filter_upwards [eventually_bucketCount_eq_primeCounting_sub j hj] with n hn
    have hdiv : n / (j + 1) ≤ n / j :=
      Nat.div_le_div_left (Nat.le_succ j) hj
    have hpi : Nat.primeCounting (n / (j + 1)) ≤
        Nat.primeCounting (n / j) := Nat.monotone_primeCounting hdiv
    rw [hn, Nat.cast_sub hpi]
    ring
  have hweight :
      1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ) = cofactorWeight j := by
    unfold cofactorWeight
    norm_num only [Nat.cast_add, Nat.cast_one]
    have hj0 : (j : ℝ) ≠ 0 := by positivity
    have hsucc0 : (j : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  rw [← hweight]
  exact hdiff.congr' (heq.mono fun _ h => h.symm)

/-- An argument-order variant useful when `j` is implicit. -/
theorem bucketCount_fixed_tendsto_cofactorWeight
    {j : ℕ} (hj : 0 < j) (hPNT : PrimeNumberTheorem) :
    Tendsto
      (fun n : ℕ =>
        (Real.log (n : ℝ) / (n : ℝ)) * (bucketCount n j : ℝ))
      atTop (nhds (cofactorWeight j)) :=
  bucketCount_weight_tendsto hPNT j hj

end Erdos796
