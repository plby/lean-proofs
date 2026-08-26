import ErdosProblems.Erdos67.StationaryRationalEnergy

/-!
# Exclusion of nonzero rational spectral atoms

A prime divisor of the denominator produces distinct frequencies approaching
zero. Their mass times squared denominator never decreases, so a positive
starting mass would give infinite spectral energy.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.StationaryModel

def denominatorTower (q d : ℕ+) (n : ℕ) : ℕ+ := d ^ n * q

theorem denominatorTower_zero (q d : ℕ+) : denominatorTower q d 0 = q := by
  simp [denominatorTower]

theorem denominatorTower_succ (q d : ℕ+) (n : ℕ) :
    denominatorTower q d (n + 1) = d * denominatorTower q d n := by
  simp only [denominatorTower, pow_succ]
  ac_rfl

theorem denominatorTower_ge (q d : ℕ+) (n : ℕ) : q.val ≤ (denominatorTower q d n).val := by
  have hp : 1 ≤ d.val ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ d.pos.ne')
  simpa only [denominatorTower, PNat.mul_coe, PNat.pow_coe, one_mul] using
    Nat.mul_le_mul_right q.val hp

theorem denominatorTower_frequency_injective (q d : ℕ+) (hd : 1 < d.val) :
    Function.Injective (fun n ↦ primitiveFrequency (denominatorTower q d n) 1) := by
  intro m n hmn
  have he : (denominatorTower q d m).val = (denominatorTower q d n).val :=
    (primitiveFrequency_order _ _).symm.trans
      ((congrArg addOrderOf hmn).trans (primitiveFrequency_order _ _))
  simp only [denominatorTower, PNat.mul_coe, PNat.pow_coe] at he
  exact (pow_right_strictMono₀ hd).injective (Nat.eq_of_mul_eq_mul_right q.pos he)

theorem normalized_rational_mass_le (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (q : ℕ+) (p : ℕ) (hp : p.Prime) (hpq : p ∣ q.val) (n : ℕ) :
    (q.val : ℝ) ^ 2 * rationalAtomMass σ q ≤
      ((denominatorTower q ⟨p, hp.pos⟩ n).val : ℝ) ^ 2 *
        rationalAtomMass σ (denominatorTower q ⟨p, hp.pos⟩ n) := by
  let d : ℕ+ := ⟨p, hp.pos⟩
  change (q.val : ℝ) ^ 2 * rationalAtomMass σ q ≤
    ((denominatorTower q d n).val : ℝ) ^ 2 * rationalAtomMass σ (denominatorTower q d n)
  induction n with
  | zero => simp only [denominatorTower_zero, le_refl]
  | succ n ih =>
    let t := denominatorTower q d n
    have hpt : p ∣ t.val := dvd_mul_of_dvd_right hpq _
    have hm := rational_atom_mass_le_prime_square Q hQ hCD σ hσ t p hp hpt
    change rationalAtomMass σ t ≤ (d.val : ℝ) ^ 2 * rationalAtomMass σ (d * t) at hm
    have hh := mul_le_mul_of_nonneg_left hm (sq_nonneg (t.val : ℝ))
    rw [denominatorTower_succ]
    apply ih.trans
    simpa only [t, PNat.mul_coe, Nat.cast_mul, mul_pow, mul_assoc,
      mul_left_comm] using hh

theorem no_positive_uniform_atomic_energy (σ : ProbabilityMeasure FrequencyCircle)
    (hE : Integrable spectralEnergy (σ : Measure FrequencyCircle))
    (θ : ℕ → FrequencyCircle) (hθ : Function.Injective θ) (K A : ℝ) (hK : 0 ≤ K)
    (hA : ∀ n, A ≤ K * (spectralEnergy (θ n) * (σ : Measure FrequencyCircle).real {θ n})) :
    A ≤ 0 := by
  classical
  by_contra hpos
  have hAp : 0 < A := lt_of_not_ge hpos
  have hb (N : ℕ) : (N : ℝ) * A ≤
      K * ∫ x, spectralEnergy x ∂(σ : Measure FrequencyCircle) := by
    have he := sum_atomic_energy_le_integral σ hE ((range N).image θ)
    rw [sum_image (fun a _ b _ hab ↦ hθ hab)] at he
    calc
      _ = ∑ n ∈ range N, A := by simp
      _ ≤ ∑ n ∈ range N, K * (spectralEnergy (θ n) *
          (σ : Measure FrequencyCircle).real {θ n}) := sum_le_sum (fun n _ ↦ hA n)
      _ = K * ∑ n ∈ range N, spectralEnergy (θ n) *
          (σ : Measure FrequencyCircle).real {θ n} := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left he hK
  obtain ⟨N, hN⟩ := exists_nat_gt ((K * ∫ x, spectralEnergy x ∂(σ : Measure FrequencyCircle)) / A)
  have hlt := (div_lt_iff₀ hAp).mp hN
  exact (not_lt_of_ge (hb N)) hlt

theorem rational_atom_mass_zero (Q : ProbabilityMeasure Configuration)
    (hQ : Measure.map (shift 1) (Q : Measure Configuration) = (Q : Measure Configuration))
    (hCD : ∀ (d : ℕ+) (F : C((ℤ → Bool), ℝ)),
      (∫ ω, F ω.1 ∂(Q : Measure Configuration)) =
        (d.val : ℝ) * ∫ ω, conditionalDilationTest d F ω ∂(Q : Measure Configuration))
    (σ : ProbabilityMeasure FrequencyCircle) (hσ : IsCorrelationSpectrum Q σ)
    (hE : Integrable spectralEnergy (σ : Measure FrequencyCircle))
    (q : ℕ+) (hq : 1 < q.val) : rationalAtomMass σ q = 0 := by
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (by omega : q.val ≠ 1)
  let θ : ℕ → FrequencyCircle := fun n ↦ primitiveFrequency (denominatorTower q ⟨p, hp.pos⟩ n) 1
  have hh : (q.val : ℝ) ^ 2 * rationalAtomMass σ q ≤ 0 := by
    apply no_positive_uniform_atomic_energy σ hE θ
      (denominatorTower_frequency_injective q ⟨p, hp.pos⟩ hp.one_lt)
      (2 * Real.pi ^ 2) _ (by positivity)
    intro n
    let t := denominatorTower q ⟨p, hp.pos⟩ n
    have ht : 1 < t.val := hq.trans_le (denominatorTower_ge q _ n)
    have he := mul_le_mul_of_nonneg_right (denominator_sq_le_energy t ht)
      (measureReal_nonneg (μ := (σ : Measure FrequencyCircle)) (s := {primitiveFrequency t 1}))
    calc
      _ ≤ (t.val : ℝ) ^ 2 * rationalAtomMass σ t :=
        normalized_rational_mass_le Q hQ hCD σ hσ q p hp hpq n
      _ ≤ _ := by simpa only [rationalAtomMass, mul_assoc] using he
  have hqR : (0 : ℝ) < (q.val : ℝ) ^ 2 := by positivity
  have hm : rationalAtomMass σ q ≤ 0 := by nlinarith
  exact le_antisymm hm measureReal_nonneg

end Erdos67.StationaryModel
