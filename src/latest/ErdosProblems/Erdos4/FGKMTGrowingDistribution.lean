import ErdosProblems.Erdos4.FGKMTWeightedDistribution
import ErdosProblems.Erdos4.FGKMTGrowingLogWeight

/-! An unconditional distribution estimate uniform in growing dimension. -/

open scoped BigOperators ArithmeticFunction.omega

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard

theorem weighted_sqrt_envelope {a C : ℝ} (hC : 0 ≤ C) {x d Q : ℕ} (hx : 1 ≤ x)
    (hweight : (1 + Real.log (Q : ℝ)) ^ (2 * d ^ 2) ≤
      Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ)))) :
    Real.sqrt (3 * ((x + 1 : ℕ) : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 * d ^ 2)) *
      Real.sqrt (C * ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ))))) ≤
        Real.sqrt (6 * C) * ((x : ℝ) * Real.exp (-(a / 8) * Real.sqrt (Real.log (x : ℝ)))) := by
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hsucc : ((x + 1 : ℕ) : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast (by omega : x + 1 ≤ 2 * x)
  have hfirst : 3 * ((x + 1 : ℕ) : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 * d ^ 2) ≤
      6 * (x : ℝ) * Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ))) := by
    calc
      _ ≤ 3 * ((x + 1 : ℕ) : ℝ) * Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hweight (by positivity)
      _ ≤ (3 * (2 * (x : ℝ))) * Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsucc (by norm_num)) (Real.exp_pos _).le
      _ = _ := by ring
  calc
    _ ≤ Real.sqrt (6 * (x : ℝ) * Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ)))) *
        Real.sqrt (C * ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ))))) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hfirst) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((6 * C) * ((x : ℝ) ^ 2) *
        Real.exp (-(a / 4) * Real.sqrt (Real.log (x : ℝ)))) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      calc
        _ = (6 * C) * ((x : ℝ) ^ 2) *
            (Real.exp ((a / 4) * Real.sqrt (Real.log (x : ℝ))) *
              Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ)))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hx0,
        ← Real.exp_half]
      have heq : (-(a / 4) * Real.sqrt (Real.log (x : ℝ))) / 2 =
          -(a / 8) * Real.sqrt (Real.log (x : ℝ)) := by ring
      rw [heq]
      ring

/-- One omitted prime works for every smaller endpoint, every squarefree
modulus subset, and every multiplicity parameter up to `log(x)^(1/8)`. -/
theorem exists_growing_dimension_distribution :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∃ B : ℕ,
        B ≤ exponentialConductorCutoff a x ∧ (B = 1 ∨ B.Prime) ∧
        ∀ d : ℕ, (d : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 8 : ℝ) →
        ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 (powerDistributionLevel x) →
          (∀ q ∈ S, q.Coprime B) → (∀ q ∈ S, Squarefree q) →
          (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * primeDiscrepancyUpTo x q) ≤
            C * ((x : ℝ) * Real.exp (-(a / 8) * Real.sqrt (Real.log (x : ℝ)))) := by
  obtain ⟨a, C, ha, ha1, hC, hdist⟩ := exists_exponential_weighted_distribution
  refine ⟨a, Real.sqrt (6 * C), ha, ha1, Real.sqrt_pos.mpr (by positivity), ?_⟩
  filter_upwards [hdist, eventually_distribution_cutoffs ha ha1, eventually_growing_log_weight ha]
    with x hdist hcut hweight
  obtain ⟨B, hBR, hB, hbound⟩ := hdist
  refine ⟨B, hBR, hB, ?_⟩
  intro d hd S hSQ hSB hsq
  have hQx : powerDistributionLevel x ≤ x := by
    exact_mod_cast hcut.2.2.2.2.2.2.2.trans (cubeRoot_le_self hcut.1)
  exact (hbound d S hSQ hSB hsq).trans (weighted_sqrt_envelope hC.le hcut.1
    (hweight d (powerDistributionLevel x) hQx hd))

end Erdos4.FGKMT
