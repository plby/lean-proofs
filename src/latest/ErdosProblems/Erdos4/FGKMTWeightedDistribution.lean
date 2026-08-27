import ErdosProblems.Erdos4.FGKMTPrimeDistribution
import BoundedGaps.Maynard.ImprovedGPY.S2TrivialDiscrepancy

/-! Finite divisor-multiplicity weights on the excised distribution estimate. -/

open scoped BigOperators ArithmeticFunction.omega

namespace Erdos4.FGKMT

open Filter BoundedGaps.Maynard

theorem primeDiscrepancyUpTo_nonneg (x q : ℕ) : 0 ≤ primeDiscrepancyUpTo x q := by
  by_cases hx : 2 ≤ x
  · exact (maxProgressionDiscrepancy_nonneg 2 q).trans
      (maxProgressionDiscrepancy_le_primeDiscrepancyUpTo (by norm_num) hx)
  · simp [primeDiscrepancyUpTo, hx]

theorem progressionDiscrepancy_uniform_trivial {x y q a : ℕ} (hyx : y ≤ x)
    (hq : 0 < q) (hqx : q ≤ x + 1) :
    progressionDiscrepancy y q a ≤ 3 * ((x + 1 : ℕ) : ℝ) / (q.totient : ℝ) := by
  have hφpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφx : (q.totient : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.totient_le q).trans hqx
  have hprogress := cast_primeCountUpTo_le_div_add_one y q a hq
  have hdiv : ((y + 1 : ℕ) : ℝ) / q ≤ ((x + 1 : ℕ) : ℝ) / (q.totient : ℝ) := by
    apply div_le_div₀ (by positivity) _ hφpos hφq
    exact_mod_cast Nat.add_le_add_right hyx 1
  have hone : (1 : ℝ) ≤ ((x + 1 : ℕ) : ℝ) / (q.totient : ℝ) :=
    (one_le_div₀ hφpos).mpr hφx
  have htotal : (primeCountTotal y : ℝ) / (q.totient : ℝ) ≤
      ((x + 1 : ℕ) : ℝ) / (q.totient : ℝ) := by
    apply div_le_div_of_nonneg_right _ hφpos.le
    exact_mod_cast (primeCountTotal_le_succ y).trans (Nat.add_le_add_right hyx 1)
  have hprogress0 : (0 : ℝ) ≤ primeCountUpTo y q a := Nat.cast_nonneg _
  have htotal0 : (0 : ℝ) ≤ (primeCountTotal y : ℝ) / (q.totient : ℝ) := by positivity
  unfold progressionDiscrepancy
  rw [mul_div_assoc, abs_le]
  constructor <;> linarith

theorem primeDiscrepancyUpTo_trivial {x q : ℕ} (hq : 0 < q) (hqx : q ≤ x + 1) :
    primeDiscrepancyUpTo x q ≤ 3 * ((x + 1 : ℕ) : ℝ) / (q.totient : ℝ) := by
  by_cases hx : 2 ≤ x
  · rw [primeDiscrepancyUpTo, dif_pos hx]
    apply Finset.sup'_le
    intro y hy
    rw [maxProgressionDiscrepancy, dif_pos hq]
    apply Finset.sup'_le
    intro a _ha
    exact progressionDiscrepancy_uniform_trivial (Finset.mem_Icc.mp hy).2 hq hqx
  · rw [primeDiscrepancyUpTo, dif_neg hx]
    positivity

theorem excisedPrimeSum_subset {x Q B : ℕ} (S : Finset ℕ)
    (hSQ : S ⊆ Finset.Icc 1 Q) (hB : ∀ q ∈ S, q.Coprime B) :
    (∑ q ∈ S, primeDiscrepancyUpTo x q) ≤ excisedPrimeSum x Q B := by
  unfold excisedPrimeSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    exact Finset.mem_filter.mpr ⟨hSQ hq, hB q hq⟩
  · intro q _ _
    exact primeDiscrepancyUpTo_nonneg x q

theorem excised_weighted_distribution_bound {x Q B : ℕ} (d : ℕ) (S : Finset ℕ)
    (hSQ : S ⊆ Finset.Icc 1 Q) (hB : ∀ q ∈ S, q.Coprime B)
    (hsq : ∀ q ∈ S, Squarefree q) (hQx : Q ≤ x + 1) :
    (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * primeDiscrepancyUpTo x q) ≤
      Real.sqrt (3 * ((x + 1 : ℕ) : ℝ) * (1 + Real.log (Q : ℝ)) ^ (2 * d ^ 2)) *
        Real.sqrt (excisedPrimeSum x Q B) := by
  have hCS := sum_weight_mul_le_sqrt_of_pointwise_div S
    (fun q => ((d ^ ω q : ℕ) : ℝ)) (primeDiscrepancyUpTo x)
    (fun q => (q.totient : ℝ)) (3 * ((x + 1 : ℕ) : ℝ))
    (fun q _ => primeDiscrepancyUpTo_nonneg x q)
    (fun q hq => primeDiscrepancyUpTo_trivial
      (by have hh := (Finset.mem_Icc.mp (hSQ hq)).1; omega)
      ((Finset.mem_Icc.mp (hSQ hq)).2.trans hQx))
  have hmean := sum_tauPow_sq_div_totient_le_one_add_log d Q S hSQ hsq
  apply hCS.trans
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hmean (by positivity))
  · exact Real.sqrt_le_sqrt (excisedPrimeSum_subset S hSQ hB)
  · exact Real.sqrt_nonneg _
  · exact Real.sqrt_nonneg _

theorem exists_exponential_weighted_distribution :
    ∃ a C : ℝ, 0 < a ∧ a ≤ 1 / 4 ∧ 0 < C ∧
      ∀ᶠ x : ℕ in atTop, ∃ B : ℕ,
        B ≤ exponentialConductorCutoff a x ∧ (B = 1 ∨ B.Prime) ∧
        ∀ d : ℕ, ∀ S : Finset ℕ,
          S ⊆ Finset.Icc 1 (powerDistributionLevel x) →
          (∀ q ∈ S, q.Coprime B) → (∀ q ∈ S, Squarefree q) →
          (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * primeDiscrepancyUpTo x q) ≤
            Real.sqrt (3 * ((x + 1 : ℕ) : ℝ) *
              (1 + Real.log (powerDistributionLevel x : ℝ)) ^ (2 * d ^ 2)) *
            Real.sqrt (C * ((x : ℝ) * Real.exp (-(a / 2) * Real.sqrt (Real.log (x : ℝ))))) := by
  obtain ⟨a, C, ha, ha1, hC, hdist⟩ := exists_exponential_prime_distribution
  refine ⟨a, C, ha, ha1, hC, ?_⟩
  filter_upwards [hdist, eventually_distribution_cutoffs ha ha1] with x hdist hcut
  obtain ⟨B, hBR, hB, hbound⟩ := hdist
  refine ⟨B, hBR, hB, ?_⟩
  intro d S hSQ hSB hsq
  have hQx : powerDistributionLevel x ≤ x + 1 := by
    have hh := hcut.2.2.2.2.2.2.2.trans (cubeRoot_le_self hcut.1)
    have hnat : powerDistributionLevel x ≤ x := by exact_mod_cast hh
    omega
  exact (excised_weighted_distribution_bound d S hSQ hSB hsq hQx).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbound) (Real.sqrt_nonneg _))

end Erdos4.FGKMT
