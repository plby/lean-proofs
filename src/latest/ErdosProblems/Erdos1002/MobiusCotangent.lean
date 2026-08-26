import ErdosProblems.Erdos1002.RamanujanIdentities
import ErdosProblems.Erdos1002.DivisorSquareAverage
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Paired principal values and the cotangent kernel

This file starts the analytic identification used in the nearest-cell
window estimate.  The principal value is represented by its genuinely
convergent paired series, so no conditionally convergent all-integer `tsum`
is introduced.  Mathlib's proved Mittag--Leffler expansion of cotangent then
gives the exact value.
-/

open Filter
open scoped BigOperators ComplexConjugate Topology

namespace Erdos1002

noncomputable section

/-- Symmetrically paired principal-value series over all integer poles. -/
def pairedIntegerPrincipalValue (z : ℂ) : ℂ :=
  1 / z + ∑' n : ℕ+,
    (1 / (z - (n : ℕ)) + 1 / (z + (n : ℕ)))

/-- Exact cotangent identity for the paired principal value. -/
theorem pairedIntegerPrincipalValue_eq_cot
    {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    pairedIntegerPrincipalValue z =
      (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) := by
  exact (cot_series_rep hz).symm

/-- Paired principal value over the lattice `d * ℤ`. -/
def pairedMultiplePrincipalValue (d : ℕ+) (z : ℂ) : ℂ :=
  1 / z + ∑' n : ℕ+,
    (1 / (z - (d : ℕ) * (n : ℕ)) +
      1 / (z + (d : ℕ) * (n : ℕ)))

private theorem inv_scaled_sub_nat
    (d n : ℕ+) (z : ℂ) :
    1 / (z - (d : ℕ) * (n : ℕ)) =
      (1 / (d : ℂ)) * (1 / (z / (d : ℂ) - (n : ℕ))) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast d.ne_zero
  by_cases h : z - (d : ℕ) * (n : ℕ) = 0
  · have hz : z = (d : ℂ) * (n : ℂ) := by
      simpa only [Nat.cast_mul] using! sub_eq_zero.mp h
    simp [hz, hd]
  · have hscaled : z / (d : ℂ) - (n : ℕ) ≠ 0 := by
      intro hzero
      apply h
      have hzdiv : z / (d : ℂ) = (n : ℂ) := sub_eq_zero.mp hzero
      have hz : z = (n : ℂ) * (d : ℂ) := (div_eq_iff hd).mp hzdiv
      apply sub_eq_zero.mpr
      simpa only [Nat.cast_mul] using! hz.trans (mul_comm _ _)
    field_simp [hd, h, hscaled]

private theorem inv_scaled_add_nat
    (d n : ℕ+) (z : ℂ) :
    1 / (z + (d : ℕ) * (n : ℕ)) =
      (1 / (d : ℂ)) * (1 / (z / (d : ℂ) + (n : ℕ))) := by
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast d.ne_zero
  by_cases h : z + (d : ℕ) * (n : ℕ) = 0
  · have hz : z = -((d : ℂ) * (n : ℂ)) := by
      simpa only [Nat.cast_mul] using! eq_neg_of_add_eq_zero_left h
    rw [hz]
    field_simp [hd]
  · have hscaled : z / (d : ℂ) + (n : ℕ) ≠ 0 := by
      intro hzero
      apply h
      have hzdiv : z / (d : ℂ) = -(n : ℂ) :=
        eq_neg_of_add_eq_zero_left hzero
      have hz : z = -(n : ℂ) * (d : ℂ) := (div_eq_iff hd).mp hzdiv
      rw [hz]
      ring
    field_simp [hd, h, hscaled]

/-- Scaling the pole lattice is exactly scaling the unit-lattice paired
principal value. -/
theorem pairedMultiplePrincipalValue_eq_scaled
    (d : ℕ+) (z : ℂ) :
    pairedMultiplePrincipalValue d z =
      (1 / (d : ℂ)) * pairedIntegerPrincipalValue (z / (d : ℂ)) := by
  unfold pairedMultiplePrincipalValue pairedIntegerPrincipalValue
  calc
    1 / z + ∑' n : ℕ+,
        (1 / (z - (d : ℕ) * (n : ℕ)) +
          1 / (z + (d : ℕ) * (n : ℕ))) =
      (1 / (d : ℂ)) * (1 / (z / (d : ℂ))) +
        ∑' n : ℕ+,
          (1 / (d : ℂ)) *
            (1 / (z / (d : ℂ) - (n : ℕ)) +
              1 / (z / (d : ℂ) + (n : ℕ))) := by
        congr 1
        · have hd : (d : ℂ) ≠ 0 := by exact_mod_cast d.ne_zero
          by_cases hz : z = 0
          · simp [hz]
          · field_simp [hd, hz]
        · apply tsum_congr
          intro n
          rw [mul_add, inv_scaled_sub_nat d n z,
            inv_scaled_add_nat d n z]
    _ = (1 / (d : ℂ)) *
        (1 / (z / (d : ℂ)) +
          ∑' n : ℕ+,
            (1 / (z / (d : ℂ) - (n : ℕ)) +
              1 / (z / (d : ℂ) + (n : ℕ)))) := by
      rw [mul_add, tsum_mul_left]

/-- Scaled cotangent identity, with the lattice spacing explicit. -/
theorem pairedMultiplePrincipalValue_eq_cot
    (d : ℕ+) {z : ℂ}
    (hz : z / (d : ℂ) ∈ Complex.integerComplement) :
    pairedMultiplePrincipalValue d z =
      ((Real.pi : ℂ) / (d : ℂ)) *
        Complex.cot ((Real.pi : ℂ) * (z / (d : ℂ))) := by
  rw [pairedMultiplePrincipalValue_eq_scaled,
    pairedIntegerPrincipalValue_eq_cot hz]
  ring

/-! ## Finite Möbius inversion before the principal-value limit -/

/-- The symmetrically paired contribution of the two poles `n` and `-n`.
This is kept as a separate definition so that all Möbius manipulations below
are finite identities. -/
def pairedPoleTerm (z : ℂ) (n : ℕ) : ℂ :=
  1 / (z - (n : ℕ)) + 1 / (z + (n : ℕ))

/-- Möbius inversion detects coprimality, in the complex coefficient ring.
The nonzero hypothesis is essential because `Nat.divisors 0` is empty. -/
theorem sum_moebius_dvd_eq_coprime_complex
    (p n : ℕ) (hp : p ≠ 0) :
    (∑ d ∈ p.divisors,
      if d ∣ n then
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)
      else 0) =
      if Nat.Coprime n p then 1 else 0 := by
  have hgcd : Nat.gcd n p ≠ 0 :=
    (Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero hp)).ne'
  have hdivisors :
      (Nat.gcd n p).divisors = p.divisors.filter (fun d ↦ d ∣ n) := by
    ext d
    simp only [Nat.mem_divisors, hgcd, hp, ne_eq, not_false_eq_true,
      Finset.mem_filter]
    rw [Nat.dvd_gcd_iff]
    aesop
  calc
    (∑ d ∈ p.divisors,
        if d ∣ n then
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)
        else 0) =
        ∑ d ∈ p.divisors.filter (fun d ↦ d ∣ n),
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
      symm
      simp only [Finset.sum_filter]
    _ = ∑ d ∈ (Nat.gcd n p).divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) := by
      rw [hdivisors]
    _ = if Nat.Coprime n p then 1 else 0 := by
      exact_mod_cast sum_moebius_gcd n p

/-- The literal symmetric cutoff of the coprime-pole principal value.
The separate zero-pole coefficient is present only for modulus one. -/
def coprimePairedPartialSum (p : ℕ+) (R : ℕ) (z : ℂ) : ℂ :=
  (if (p : ℕ) = 1 then 1 / z else 0) +
    ∑ n ∈ Finset.Icc 1 R,
      if Nat.Coprime n (p : ℕ) then pairedPoleTerm z n else 0

/-- The same finite cutoff after expanding both the zero coefficient and
every positive coefficient by Möbius inversion.  No infinite sum has yet
been rearranged. -/
def mobiusExpandedPairedPartialSum (p : ℕ+) (R : ℕ) (z : ℂ) : ℂ :=
  ∑ d ∈ (p : ℕ).divisors,
    (((ArithmeticFunction.moebius d : ℤ) : ℂ) * (1 / z) +
      ∑ n ∈ Finset.Icc 1 R,
        if d ∣ n then
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) * pairedPoleTerm z n
        else 0)

/-- Exact finite Möbius expansion of the coprime symmetric cutoff.  This is
the rigorous algebraic step that must precede any principal-value limit. -/
theorem coprimePairedPartialSum_eq_mobiusExpanded
    (p : ℕ+) (R : ℕ) (z : ℂ) :
    coprimePairedPartialSum p R z =
      mobiusExpandedPairedPartialSum p R z := by
  have hp : (p : ℕ) ≠ 0 := p.ne_zero
  have hzero :
      (∑ d ∈ (p : ℕ).divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ)) =
        if (p : ℕ) = 1 then 1 else 0 := by
    exact_mod_cast sum_moebius_divisors (p : ℕ)
  unfold coprimePairedPartialSum mobiusExpandedPairedPartialSum
  rw [Finset.sum_add_distrib]
  calc
    (if (p : ℕ) = 1 then 1 / z else 0) +
        ∑ n ∈ Finset.Icc 1 R,
          (if Nat.Coprime n (p : ℕ) then pairedPoleTerm z n else 0) =
      ((∑ d ∈ (p : ℕ).divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℂ)) * (1 / z)) +
        ∑ n ∈ Finset.Icc 1 R,
          ((∑ d ∈ (p : ℕ).divisors,
              if d ∣ n then
                ((ArithmeticFunction.moebius d : ℤ) : ℂ)
              else 0) * pairedPoleTerm z n) := by
      congr 1
      · rw [hzero]
        split_ifs <;> simp
      · apply Finset.sum_congr rfl
        intro n _hn
        rw [sum_moebius_dvd_eq_coprime_complex (p : ℕ) n hp]
        split_ifs <;> simp
    _ = (∑ d ∈ (p : ℕ).divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (1 / z)) +
        ∑ n ∈ Finset.Icc 1 R,
          ∑ d ∈ (p : ℕ).divisors,
            if d ∣ n then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ) * pairedPoleTerm z n
            else 0 := by
      simp only [Finset.sum_mul, ite_mul, zero_mul]
    _ = (∑ d ∈ (p : ℕ).divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℂ) * (1 / z)) +
        ∑ d ∈ (p : ℕ).divisors,
          ∑ n ∈ Finset.Icc 1 R,
            if d ∣ n then
              ((ArithmeticFunction.moebius d : ℤ) : ℂ) * pairedPoleTerm z n
            else 0 := by
      rw [Finset.sum_comm]

/-! ## The resulting finite cotangent combination -/

/-- The Möbius-weighted principal value over all divisor lattices.  It is a
finite sum of independently defined paired principal values. -/
def mobiusCotangentPrincipalValue (p : ℕ+) (z : ℂ) : ℂ :=
  ∑ d ∈ (p : ℕ).divisors,
    ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
      pairedMultiplePrincipalValue (Nat.toPNat' d) z

/-- Dividing a noninteger complex number by a positive natural number cannot
produce an integer. -/
theorem integerComplement_div_nat
    {z : ℂ} (hz : z ∈ Complex.integerComplement)
    {d : ℕ} (hd : 0 < d) :
    z / (d : ℂ) ∈ Complex.integerComplement := by
  rw [Complex.integerComplement.mem_iff] at hz ⊢
  rintro ⟨k, hk⟩
  apply hz
  refine ⟨(d : ℤ) * k, ?_⟩
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hzdiv : z / (d : ℂ) = (k : ℂ) := hk.symm
  have hzEq : z = (k : ℂ) * (d : ℂ) := (div_eq_iff hdC).mp hzdiv
  push_cast
  simpa [mul_comm] using! hzEq.symm

/-- Reindex a finite sum over positive multiples of `d`.  This is the exact
finite change of variables `n = d k`; it is deliberately proved before any
passage to an infinite series. -/
theorem sum_Icc_dvd_eq_sum_Icc_mul
    {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (R d : ℕ) (hd : 0 < d) :
    (∑ n ∈ Finset.Icc 1 R, if d ∣ n then f n else 0) =
      ∑ k ∈ Finset.Icc 1 (R / d), f (d * k) := by
  let A : Finset ℕ := positiveMultiplesIcc R d
  let B : Finset ℕ := Finset.Icc 1 (R / d)
  let e : {n // n ∈ A} ≃ {k // k ∈ B} :=
    positiveMultiplesIccEquiv R d hd
  have hleft :
      (∑ n ∈ Finset.Icc 1 R, if d ∣ n then f n else 0) =
        ∑ n ∈ A, f n := by
    symm
    simpa only [A, positiveMultiplesIcc] using!
      Finset.sum_filter (s := Finset.Icc 1 R) (p := fun n ↦ d ∣ n) (f := f)
  rw [hleft]
  calc
    (∑ n ∈ A, f n) = ∑ n : {n // n ∈ A}, f (n : ℕ) := by
      exact (Finset.sum_attach A f).symm
    _ = ∑ n : {n // n ∈ A}, f (d * ((e n : {k // k ∈ B}) : ℕ)) := by
      apply Finset.sum_congr rfl
      intro n _hn
      congr 1
      have hdn : d ∣ (n : ℕ) :=
        (Finset.mem_filter.mp (show (n : ℕ) ∈ positiveMultiplesIcc R d by
          simpa only [A] using! n.property)).2
      exact (Nat.mul_div_cancel' hdn).symm
    _ = ∑ k : {k // k ∈ B}, f (d * (k : ℕ)) := by
      exact e.sum_comp (fun k : {k // k ∈ B} ↦ f (d * (k : ℕ)))
    _ = ∑ k ∈ B, f (d * k) := by
      exact Finset.sum_attach B (fun k ↦ f (d * k))
    _ = ∑ k ∈ Finset.Icc 1 (R / d), f (d * k) := by rfl

private theorem pairedPoleTerm_mul_succ_eq_scaled_cotTerm
    {z : ℂ} {d : ℕ} (hd : 0 < d) (n : ℕ) :
    pairedPoleTerm z (d * (n + 1)) =
      (1 / (d : ℂ)) * cotTerm (z / (d : ℂ)) n := by
  let dp : ℕ+ := Nat.toPNat' d
  let np : ℕ+ := Nat.succPNat n
  have hdp : (dp : ℕ) = d := by
    dsimp [dp]
    exact PNat.toPNat'_coe hd
  have hnp : (np : ℕ) = n + 1 := by
    exact Nat.succPNat_coe n
  unfold pairedPoleTerm
  change 1 / (z - (d * (n + 1) : ℕ)) +
      1 / (z + (d * (n + 1) : ℕ)) = _
  have hsub := inv_scaled_sub_nat dp np z
  have hadd := inv_scaled_add_nat dp np z
  rw [hdp, hnp] at hsub hadd
  simp only [Nat.cast_mul]
  rw [hsub, hadd]
  simp only [cotTerm, Nat.cast_add, Nat.cast_one]
  ring

theorem summable_pairedPoleTerm_mul_succ
    {z : ℂ} (hz : z ∈ Complex.integerComplement)
    {d : ℕ} (hd : 0 < d) :
    Summable (fun n : ℕ ↦ pairedPoleTerm z (d * (n + 1))) := by
  have hbase := Summable_cotTerm (integerComplement_div_nat hz hd)
  have hscaled :
      Summable (fun n : ℕ ↦
        (1 / (d : ℂ)) * cotTerm (z / (d : ℂ)) n) :=
    hbase.mul_left (1 / (d : ℂ))
  exact hscaled.congr (fun n ↦ (pairedPoleTerm_mul_succ_eq_scaled_cotTerm hd n).symm)

theorem sum_Icc_one_eq_sum_range
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, f k) =
      ∑ n ∈ Finset.range K, f (1 + n) := by
  have hIcc : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]

/-- The finite symmetric sum on one divisor lattice converges to the paired
principal value on that lattice.  The proof first performs the exact finite
change of variables and only then invokes the absolutely convergent paired
series. -/
theorem tendsto_divisorFilteredPairedPartialSum
    {z : ℂ} (hz : z ∈ Complex.integerComplement)
    {d : ℕ} (hd : 0 < d) :
    Tendsto
      (fun R : ℕ ↦
        1 / z + ∑ n ∈ Finset.Icc 1 R,
          if d ∣ n then pairedPoleTerm z n else 0)
      atTop
      (nhds (pairedMultiplePrincipalValue (Nat.toPNat' d) z)) := by
  let f : ℕ → ℂ := fun n ↦ pairedPoleTerm z (d * (n + 1))
  have hsum : Summable f := by
    exact summable_pairedPoleTerm_mul_succ hz hd
  have htail :
      Tendsto (fun K : ℕ ↦ ∑ n ∈ Finset.range K, f n) atTop
        (nhds (∑' n : ℕ, f n)) :=
    hsum.tendsto_sum_tsum_nat
  have hdiv : Tendsto (fun R : ℕ ↦ R / d) atTop atTop :=
    Nat.tendsto_div_const_atTop hd.ne'
  have htailDiv :
      Tendsto (fun R : ℕ ↦ ∑ n ∈ Finset.range (R / d), f n) atTop
        (nhds (∑' n : ℕ, f n)) :=
    htail.comp hdiv
  have hadd :
      Tendsto (fun R : ℕ ↦ 1 / z + ∑ n ∈ Finset.range (R / d), f n)
        atTop (nhds (1 / z + ∑' n : ℕ, f n)) :=
    tendsto_const_nhds.add htailDiv
  have hfinite (R : ℕ) :
      (∑ n ∈ Finset.Icc 1 R,
          if d ∣ n then pairedPoleTerm z n else 0) =
        ∑ n ∈ Finset.range (R / d), f n := by
    rw [sum_Icc_dvd_eq_sum_Icc_mul (pairedPoleTerm z) R d hd,
      sum_Icc_one_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n _hn
    simp only [f]
    congr 2
    omega
  have hvalue :
      pairedMultiplePrincipalValue (Nat.toPNat' d) z =
        1 / z + ∑' n : ℕ, f n := by
    unfold pairedMultiplePrincipalValue
    have hrewrite :
        (∑' n : ℕ+,
          (1 / (z - (Nat.toPNat' d : ℕ) * (n : ℕ)) +
            1 / (z + (Nat.toPNat' d : ℕ) * (n : ℕ)))) =
          ∑' n : ℕ+, pairedPoleTerm z (d * (n : ℕ)) := by
      apply tsum_congr
      intro n
      simp only [pairedPoleTerm, PNat.toPNat'_coe hd, Nat.cast_mul]
    rw [hrewrite]
    congr 1
    simpa only [f] using!
      (tsum_pnat_eq_tsum_succ
        (f := fun k : ℕ ↦ pairedPoleTerm z (d * k)))
  rw [hvalue]
  exact hadd.congr' (Eventually.of_forall fun R ↦
    congrArg (fun w : ℂ ↦ 1 / z + w) (hfinite R).symm)

theorem mobiusExpandedPairedPartialSum_eq_factored
    (p : ℕ+) (R : ℕ) (z : ℂ) :
    mobiusExpandedPairedPartialSum p R z =
      ∑ d ∈ (p : ℕ).divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          (1 / z + ∑ n ∈ Finset.Icc 1 R,
            if d ∣ n then pairedPoleTerm z n else 0) := by
  unfold mobiusExpandedPairedPartialSum
  apply Finset.sum_congr rfl
  intro d _hd
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro n _hn
  split_ifs <;> simp

/-- The finite Möbius expansion converges to the finite sum of divisor-lattice
principal values.  Finiteness of the divisor set is what licenses passing the
limit through the outer sum. -/
theorem tendsto_mobiusExpandedPairedPartialSum
    (p : ℕ+) {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Tendsto (fun R : ℕ ↦ mobiusExpandedPairedPartialSum p R z)
      atTop (nhds (mobiusCotangentPrincipalValue p z)) := by
  simp_rw [mobiusExpandedPairedPartialSum_eq_factored]
  unfold mobiusCotangentPrincipalValue
  apply tendsto_finset_sum
  intro d hdMem
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hdMem
  exact (tendsto_divisorFilteredPairedPartialSum hz hdPos).const_mul
    (((ArithmeticFunction.moebius d : ℤ) : ℂ))

/-- The literal coprime symmetric principal-value cutoffs converge, and their
limit is exactly the Möbius--cotangent combination.  This theorem contains
both the finite coefficient identity and the justified passage to the limit. -/
theorem tendsto_coprimePairedPartialSum
    (p : ℕ+) {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Tendsto (fun R : ℕ ↦ coprimePairedPartialSum p R z)
      atTop (nhds (mobiusCotangentPrincipalValue p z)) := by
  exact (tendsto_mobiusExpandedPairedPartialSum p hz).congr'
    (Eventually.of_forall fun R ↦
      (coprimePairedPartialSum_eq_mobiusExpanded p R z).symm)

/-- Every divisor lattice in `mobiusCotangentPrincipalValue` is identified
with its scaled cotangent kernel. -/
theorem mobiusCotangentPrincipalValue_eq_sum_cot
    (p : ℕ+) {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    mobiusCotangentPrincipalValue p z =
      ∑ d ∈ (p : ℕ).divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
          (((Real.pi : ℂ) / (d : ℂ)) *
            Complex.cot ((Real.pi : ℂ) * (z / (d : ℂ)))) := by
  unfold mobiusCotangentPrincipalValue
  apply Finset.sum_congr rfl
  intro d hdMem
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hdMem
  have hdCoe : ((Nat.toPNat' d : ℕ) : ℂ) = (d : ℂ) := by
    norm_cast
    exact PNat.toPNat'_coe hdPos
  rw [pairedMultiplePrincipalValue_eq_cot]
  · rw [hdCoe]
  · rw [hdCoe]
    exact integerComplement_div_nat hz hdPos

end

end Erdos1002
