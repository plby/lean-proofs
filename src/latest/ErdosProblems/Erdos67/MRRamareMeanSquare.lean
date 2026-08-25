import ErdosProblems.Erdos67.MRT
import ErdosProblems.Erdos67.MRMeanSquareProof

/-!
# A finite Ramaré mean-square reduction

This file combines the corrected Ramaré identity with the continuous
mean-value theorem for finite Dirichlet polynomials.  The result is an
explicit, unconditional estimate for a Dirichlet polynomial supported on
integers having a prime divisor in a selected block.  The corrected
Ramaré denominator remains visible in the coefficient square mass.
-/

open scoped BigOperators ComplexConjugate
open Finset MeasureTheory

namespace Erdos67

noncomputable section

/-! ## A finite Cauchy--Schwarz reduction under the integral -/

/-- The real square moment is the norm of the corresponding complex
`conj F * F` interval integral. -/
theorem intervalIntegral_norm_sq_eq_norm_conj_mul_self
    (F : ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖F t‖ ^ 2) =
      ‖∫ t in -T..T, conj (F t) * F t‖ := by
  have hnonneg : 0 ≤ ∫ t in -T..T, ‖F t‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    positivity
  calc
    (∫ t in -T..T, ‖F t‖ ^ 2) =
        ‖(((∫ t in -T..T, ‖F t‖ ^ 2) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∫ t in -T..T, (((‖F t‖ ^ 2 : ℝ) : ℂ))‖ := by
      rw [intervalIntegral.integral_ofReal]
    _ = ‖∫ t in -T..T, conj (F t) * F t‖ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      change ((‖F t‖ ^ 2 : ℝ) : ℂ) = conj (F t) * F t
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]

/-- A pointwise finite Cauchy--Schwarz inequality, integrated over a
symmetric segment.  This is the exact step which reduces the square moment
of a Ramaré prime-row sum to the sum of the square moments of its rows. -/
theorem norm_intervalIntegral_finsetSum_conj_mul_self_le
    {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℂ)
    {T : ℝ} (hT : 0 ≤ T) (hF : ∀ i ∈ S, Continuous (F i)) :
    ‖∫ t in -T..T, conj (∑ i ∈ S, F i t) * (∑ i ∈ S, F i t)‖ ≤
      (S.card : ℝ) *
        ∑ i ∈ S, ‖∫ t in -T..T, conj (F i t) * F i t‖ := by
  rw [← intervalIntegral_norm_sq_eq_norm_conj_mul_self
    (fun t ↦ ∑ i ∈ S, F i t) hT]
  have hle : -T ≤ T := by linarith
  have hsumContinuous : Continuous (fun t ↦ ∑ i ∈ S, F i t) := by
    fun_prop
  have hleft : IntervalIntegrable
      (fun t ↦ ‖∑ i ∈ S, F i t‖ ^ 2) volume (-T) T :=
    (hsumContinuous.norm.pow 2).intervalIntegrable _ _
  have hright : IntervalIntegrable
      (fun t ↦ (S.card : ℝ) * ∑ i ∈ S, ‖F i t‖ ^ 2)
      volume (-T) T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hpoint (t : ℝ) :
      ‖∑ i ∈ S, F i t‖ ^ 2 ≤
        (S.card : ℝ) * ∑ i ∈ S, ‖F i t‖ ^ 2 := by
    calc
      ‖∑ i ∈ S, F i t‖ ^ 2 ≤
          (∑ i ∈ S, ‖F i t‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ (∑ _i ∈ S, (1 : ℝ) ^ 2) *
          ∑ i ∈ S, ‖F i t‖ ^ 2 := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq S
          (fun _ ↦ (1 : ℝ)) (fun i ↦ ‖F i t‖)
      _ = (S.card : ℝ) * ∑ i ∈ S, ‖F i t‖ ^ 2 := by simp
  calc
    (∫ t in -T..T, ‖∑ i ∈ S, F i t‖ ^ 2) ≤
        ∫ t in -T..T, (S.card : ℝ) * ∑ i ∈ S, ‖F i t‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hle hleft hright
      intro t ht
      exact hpoint t
    _ = (S.card : ℝ) *
          ∑ i ∈ S, (∫ t in -T..T, ‖F i t‖ ^ 2) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_finsetSum]
      intro i hi
      exact (hF i hi).norm.pow 2 |>.intervalIntegrable _ _
    _ = (S.card : ℝ) *
          ∑ i ∈ S, ‖∫ t in -T..T, conj (F i t) * F i t‖ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact intervalIntegral_norm_sq_eq_norm_conj_mul_self (F i) hT

/-! ## Corrected Ramaré rows -/

/-- The coefficient of `n` in the row indexed by `p` in the corrected
Ramaré expansion. -/
def ramareRowCoefficient (P : Finset ℕ) (a : ℕ → ℂ)
    (p n : ℕ) : ℂ :=
  if p ∣ n then a n / (ramareDenominator P p (n / p) : ℂ) else 0

/-- A single prime row of the corrected Ramaré expansion, represented as
a finite logarithmic-frequency polynomial on the support subtype. -/
def ramareRowPolynomial (P S : Finset ℕ) (a : ℕ → ℂ)
    (p : ℕ) (t : ℝ) : ℂ :=
  finiteFrequencyPolynomial (fun n : ↑S ↦ Real.log (n : ℕ))
    (fun n : ↑S ↦ ramareRowCoefficient P a p n) (-t)

theorem continuous_ramareRowPolynomial
    (P S : Finset ℕ) (a : ℕ → ℂ) (p : ℕ) :
    Continuous (ramareRowPolynomial P S a p) := by
  unfold ramareRowPolynomial finiteFrequencyPolynomial
  fun_prop

/-- One corrected Ramaré row is the corresponding divisibility-restricted
sum in the original `cpow` notation. -/
theorem ramareRowPolynomial_eq
    {S : Finset ℕ} (hSpos : ∀ n ∈ S, 0 < n)
    (P : Finset ℕ) (a : ℕ → ℂ) (p : ℕ) (t : ℝ) :
    ramareRowPolynomial P S a p t =
      ∑ n ∈ S,
        if p ∣ n then
          (a n * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))) /
            (ramareDenominator P p (n / p) : ℂ)
        else 0 := by
  classical
  unfold ramareRowPolynomial finiteFrequencyPolynomial
  let G : ℕ → ℂ := fun n ↦
    ramareRowCoefficient P a p n *
      realExponentialPhase (-t * Real.log n)
  change (∑ r : ↑S, G r) = _
  rw [← Finset.sum_subtype S (fun n ↦ Iff.rfl) G]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only [G]
  by_cases hpn : p ∣ n
  · rw [ramareRowCoefficient, if_pos hpn, if_pos hpn,
      cpow_neg_I_mul_eq_logarithmicPhase_neg (hSpos n hn)]
    unfold logarithmicPhase realExponentialPhase
    ring
  · simp [ramareRowCoefficient, hpn]

/-- The corrected Ramaré identity decomposes the whole finite Dirichlet
polynomial as the sum of its prime rows. -/
theorem finiteDirichletPolynomial_eq_sum_ramareRows
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hSdiv : ∀ n ∈ S, ∃ p ∈ P, p ∣ n)
    (hSpos : ∀ n ∈ S, 0 < n) (a : ℕ → ℂ) (t : ℝ) :
    finiteDirichletPolynomial S a t =
      ∑ p ∈ P, ramareRowPolynomial P S a p t := by
  rw [finiteDirichletPolynomial_eq_ramare hP hSdiv]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ramareRowPolynomial_eq hSpos]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hpn : p ∣ n <;> simp [hpn]

/-- At a fixed supported integer, the square energy of the corrected
Ramaré coefficients over all active prime rows is at most the square energy
of the original coefficient.  This is where the corrected divisor-count
denominator is used quantitatively. -/
theorem sum_norm_sq_ramareRowCoefficient_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {n : ℕ} (hn : ∃ p ∈ P, p ∣ n) (a : ℕ → ℂ) :
    (∑ p ∈ P, ‖ramareRowCoefficient P a p n‖ ^ 2) ≤ ‖a n‖ ^ 2 := by
  let c := primeDivisorCount P n
  have hcpos : 0 < c := primeDivisorCount_pos hn
  have hrewrite (p : ℕ) (hp : p ∈ P) :
      ‖ramareRowCoefficient P a p n‖ ^ 2 =
        if p ∣ n then ‖a n‖ ^ 2 / (c : ℝ) ^ 2 else 0 := by
    by_cases hpn : p ∣ n
    · rw [ramareRowCoefficient, if_pos hpn, if_pos hpn,
        ramareDenominator_eq_primeDivisorCount hP hp hpn]
      dsimp only [c]
      rw [norm_div, Complex.norm_natCast, div_pow]
    · simp [ramareRowCoefficient, hpn]
  calc
    (∑ p ∈ P, ‖ramareRowCoefficient P a p n‖ ^ 2) =
        ∑ p ∈ P, if p ∣ n then ‖a n‖ ^ 2 / (c : ℝ) ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hrewrite p hp
    _ = (c : ℝ) * (‖a n‖ ^ 2 / (c : ℝ) ^ 2) := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
    _ = ‖a n‖ ^ 2 / (c : ℝ) := by
      field_simp [show (c : ℝ) ≠ 0 by exact_mod_cast hcpos.ne']
    _ ≤ ‖a n‖ ^ 2 := by
      apply div_le_self (sq_nonneg ‖a n‖)
      exact_mod_cast hcpos

/-- Summed over an arbitrary finite support, the corrected Ramaré rows do
not increase coefficient square mass. -/
theorem sum_ramareRowCoefficient_norm_sq_le
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hSdiv : ∀ n ∈ S, ∃ p ∈ P, p ∣ n) (a : ℕ → ℂ) :
    (∑ p ∈ P, ∑ n : ↑S, ‖ramareRowCoefficient P a p n‖ ^ 2) ≤
      ∑ n : ↑S, ‖a n‖ ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n hn
  exact sum_norm_sq_ramareRowCoefficient_le hP (hSdiv n n.property) a

/-- Continuous mean-square estimate for one Ramaré row.  The support
bound supplies the elementary `1/N` spacing of the logarithmic frequencies. -/
theorem norm_ramareRowPolynomial_intervalIntegral_le
    {S : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (hSpos : ∀ n ∈ S, 0 < n) (hSN : ∀ n ∈ S, n ≤ N)
    (P : Finset ℕ) (a : ℕ → ℂ) (p : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (ramareRowPolynomial P S a p t) *
          ramareRowPolynomial P S a p t‖ ≤
      (2 * T + 2 * Real.pi * (N : ℝ)) *
        ∑ n : ↑S, ‖ramareRowCoefficient P a p n‖ ^ 2 := by
  have hdelta : (0 : ℝ) < (N : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast hN)
  have hsep : ∀ r s : ↑S, r ≠ s →
      (N : ℝ)⁻¹ ≤ |Real.log (r : ℕ) - Real.log (s : ℕ)| := by
    intro r s hrs
    apply inv_nat_le_abs_log_sub_log
    · exact hSpos r r.property
    · exact hSpos s s.property
    · exact hSN r r.property
    · exact hSN s s.property
    · exact fun hrsval ↦ hrs (Subtype.ext hrsval)
  let Q : ℝ → ℂ := finiteFrequencyPolynomial
    (fun n : ↑S ↦ Real.log (n : ℕ))
    (fun n : ↑S ↦ ramareRowCoefficient P a p n)
  have hflip :
      (∫ t in -T..T, conj (Q (-t)) * Q (-t)) =
        ∫ t in -T..T, conj (Q t) * Q t := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg
        (a := -T) (b := T) (fun t ↦ conj (Q t) * Q t))
  change ‖∫ t in -T..T, conj (Q (-t)) * Q (-t)‖ ≤ _
  rw [hflip]
  simpa only [Q, inv_inv] using
    (norm_finiteFrequencyPolynomial_intervalIntegral_le
      (fun n : ↑S ↦ Real.log (n : ℕ))
      (fun n : ↑S ↦ ramareRowCoefficient P a p n)
      hT hdelta hsep)

/-- Explicit integrated Ramaré reduction.  It combines the corrected
identity, finite Cauchy--Schwarz in the prime index, and the logarithmic
Dirichlet-polynomial mean-value theorem. -/
theorem norm_finiteDirichletPolynomial_intervalIntegral_le_ramare
    {P S : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (hP : ∀ p ∈ P, p.Prime)
    (hSdiv : ∀ n ∈ S, ∃ p ∈ P, p ∣ n)
    (hSpos : ∀ n ∈ S, 0 < n) (hSN : ∀ n ∈ S, n ≤ N)
    (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (finiteDirichletPolynomial S a t) *
          finiteDirichletPolynomial S a t‖ ≤
      (P.card : ℝ) *
        ∑ p ∈ P,
          (2 * T + 2 * Real.pi * (N : ℝ)) *
            ∑ n : ↑S, ‖ramareRowCoefficient P a p n‖ ^ 2 := by
  have hdecomp : ∀ t : ℝ,
      finiteDirichletPolynomial S a t =
        ∑ p ∈ P, ramareRowPolynomial P S a p t :=
    finiteDirichletPolynomial_eq_sum_ramareRows hP hSdiv hSpos a
  simp_rw [hdecomp]
  refine (norm_intervalIntegral_finsetSum_conj_mul_self_le P
    (fun p t ↦ ramareRowPolynomial P S a p t) hT
    (fun p hp ↦ continuous_ramareRowPolynomial P S a p)).trans ?_
  gcongr with p hp
  exact norm_ramareRowPolynomial_intervalIntegral_le
    hN hSpos hSN P a p hT

/-- Coefficient-energy form of the integrated Ramaré reduction.  Relative
to the ordinary finite mean-value theorem, the only remaining loss is the
pointwise Cauchy--Schwarz factor `P.card`; the corrected denominator has
already removed all further row multiplicity from the square mass. -/
theorem norm_finiteDirichletPolynomial_intervalIntegral_le_ramare_energy
    {P S : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (hP : ∀ p ∈ P, p.Prime)
    (hSdiv : ∀ n ∈ S, ∃ p ∈ P, p ∣ n)
    (hSpos : ∀ n ∈ S, 0 < n) (hSN : ∀ n ∈ S, n ≤ N)
    (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (finiteDirichletPolynomial S a t) *
          finiteDirichletPolynomial S a t‖ ≤
      (P.card : ℝ) * (2 * T + 2 * Real.pi * (N : ℝ)) *
        ∑ n : ↑S, ‖a n‖ ^ 2 := by
  have hbase := norm_finiteDirichletPolynomial_intervalIntegral_le_ramare
    hN hP hSdiv hSpos hSN a hT
  have henergy := sum_ramareRowCoefficient_norm_sq_le hP hSdiv a
  calc
    ‖∫ t in -T..T,
        conj (finiteDirichletPolynomial S a t) *
          finiteDirichletPolynomial S a t‖ ≤
        (P.card : ℝ) *
          ∑ p ∈ P,
            (2 * T + 2 * Real.pi * (N : ℝ)) *
              ∑ n : ↑S, ‖ramareRowCoefficient P a p n‖ ^ 2 := hbase
    _ = (P.card : ℝ) * (2 * T + 2 * Real.pi * (N : ℝ)) *
          (∑ p ∈ P,
            ∑ n : ↑S, ‖ramareRowCoefficient P a p n‖ ^ 2) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (P.card : ℝ) * (2 * T + 2 * Real.pi * (N : ℝ)) *
          ∑ n : ↑S, ‖a n‖ ^ 2 := by
      gcongr

end

end Erdos67
