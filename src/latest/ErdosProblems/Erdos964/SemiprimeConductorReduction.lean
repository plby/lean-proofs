import ErdosProblems.Erdos964.ConductorWeights

/-!
# Semiprime progression errors after conductor reduction

This is an unconditional finite estimate for the actual progression counts.
The imprimitive errors are reduced to linear character maxima with both a
reciprocal-prime weight and a shorter conductor range. The remaining centered
primitive mass must still be bounded using large-sieve and small-conductor
estimates; no level-of-distribution conclusion is assumed or asserted here.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem finiteResidueCount_sum_discrepancy_le (S : Finset ℕ) (T : ℕ)
    (a : ℕ → ℕ) (ha : ∀ q, 0 < q → q ≤ T → (a q).Coprime q) :
    (∑ q ∈ Finset.Ioc 0 T,
      |(finiteResidueCount S q (a q) : ℝ) - (S.card : ℝ) / q.totient|) ≤
      ∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
        ((d * k).totient : ℝ)⁻¹ * ∑ ψ : primitiveCharacters d,
          (‖finiteCenteredCharacterSum S d ψ.1‖ +
            ‖∑ n ∈ S with ¬n.Coprime (d * k), ψ.1 n‖) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioc 0 T,
        (∑ d : q.divisors, ∑ ψ : primitiveCharacters d.1,
          (‖finiteCenteredCharacterSum S d.1 ψ.1‖ +
            ‖∑ n ∈ S with ¬n.Coprime q, ψ.1 n‖)) / q.totient := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := Finset.mem_Ioc.mp hq
      exact finiteResidueCount_discrepancy_conductors_le S hq'.1 (ha q hq'.1 hq'.2)
    _ = _ := sum_conductor_weights_eq T
      (fun q d ψ => ‖finiteCenteredCharacterSum S d ψ.1‖ +
        ‖∑ n ∈ S with ¬n.Coprime q, ψ.1 n‖)

/-- Mean progression discrepancy for a separated prime block. The first
term is the centered primitive mass. The last two terms control all
imprimitive corrections without replacing the inner character sums by
their cardinalities. -/
theorem semiprimeBlock_sum_discrepancy_le (P Q : Finset ℕ) (M N X T : ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hPinterval : P ⊆ Finset.Ioc 0 M) (hQinterval : Q ⊆ Finset.Ioc 0 N)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r)
    (hsize : ∀ p ∈ P, ∀ r ∈ Q, T < p * r)
    (a : ℕ → ℕ) (ha : ∀ q, 0 < q → q ≤ T → (a q).Coprime q) :
    (∑ q ∈ Finset.Ioc 0 T,
      |(finiteResidueCount (primeProductBlock P Q X) q (a q) : ℝ) -
        ((primeProductBlock P Q X).card : ℝ) / q.totient|) ≤
      (4 * (1 + Real.log (T : ℝ))) *
        (∑ d ∈ Finset.Ioc 0 T,
          (∑ ψ : primitiveCharacters d,
            ‖finiteCenteredCharacterSum (primeProductBlock P Q X) d ψ.1‖) / d.totient) +
      (∑ p ∈ P, ((p.totient : ℝ)⁻¹ * (4 * (1 + Real.log (T : ℝ)))) *
        ∑ d ∈ Finset.Ioc 0 (T / p),
          (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum Q N d ψ.1) / d.totient) +
      ∑ r ∈ Q, ((r.totient : ℝ)⁻¹ * (4 * (1 + Real.log (T : ℝ)))) *
        ∑ d ∈ Finset.Ioc 0 (T / r),
          (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum P M d ψ.1) / d.totient := by
  classical
  let S := primeProductBlock P Q X
  let U (d : ℕ) := ∑ ψ : primitiveCharacters d, ‖finiteCenteredCharacterSum S d ψ.1‖
  let VP (d : ℕ) := ∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum P M d ψ.1
  let VQ (d : ℕ) := ∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum Q N d ψ.1
  have hU (d : ℕ) : 0 ≤ U d := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hVP (d : ℕ) : 0 ≤ VP d :=
    Finset.sum_nonneg (fun ψ _ => finiteCharacterCutoffMaximum_nonneg P M d ψ.1)
  have hVQ (d : ℕ) : 0 ≤ VQ d :=
    Finset.sum_nonneg (fun ψ _ => finiteCharacterCutoffMaximum_nonneg Q N d ψ.1)
  have hcorr (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (hdk : d * k ≤ T) :
      (∑ ψ : primitiveCharacters d, ‖∑ n ∈ S with ¬n.Coprime (d * k), ψ.1 n‖) ≤
        (∑ p ∈ P with p ∣ d * k ∧ ¬p ∣ d, VQ d) +
        ∑ r ∈ Q with r ∣ d * k ∧ ¬r ∣ d, VP d := by
    calc
      _ ≤ ∑ ψ : primitiveCharacters d,
          ((∑ p ∈ P with p ∣ d * k ∧ ¬p ∣ d, finiteCharacterCutoffMaximum Q N d ψ.1) +
            ∑ r ∈ Q with r ∣ d * k ∧ ¬r ∣ d, finiteCharacterCutoffMaximum P M d ψ.1) := by
        apply Finset.sum_le_sum
        intro ψ hψ
        rw [← finiteCharacterSum_changeLevel_correction S (Nat.dvd_mul_right d k) ψ.1]
        simpa only [Finset.filter_filter] using
          semiprimeBlock_changeLevel_correction_le P Q M N X
            (Nat.mul_pos hd hk) (Nat.dvd_mul_right d k) ψ.1 hP hQ hPinterval hQinterval
            hsep (fun p hp r hr => hdk.trans_lt (hsize p hp r hr))
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1 <;> exact Finset.sum_comm
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
        ((d * k).totient : ℝ)⁻¹ *
          (U d + ∑ ψ : primitiveCharacters d,
            ‖∑ n ∈ S with ¬n.Coprime (d * k), ψ.1 n‖) := by
      simpa only [U, Finset.sum_add_distrib] using finiteResidueCount_sum_discrepancy_le S T a ha
    _ ≤ ∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
        ((d * k).totient : ℝ)⁻¹ *
          (U d + (∑ p ∈ P with p ∣ d * k ∧ ¬p ∣ d, VQ d) +
            ∑ r ∈ Q with r ∣ d * k ∧ ¬r ∣ d, VP d) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro k hk
      have hdpos := (Finset.mem_Ioc.mp hd).1
      have hk' := Finset.mem_Ioc.mp hk
      have hdk : d * k ≤ T := by
        simpa only [mul_comm] using (Nat.le_div_iff_mul_le hdpos).mp hk'.2
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [add_assoc]
      exact add_le_add le_rfl (hcorr d k hdpos hk'.1 hdk)
    _ = (∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
          ((d * k).totient : ℝ)⁻¹ * U d) +
        (∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
          ((d * k).totient : ℝ)⁻¹ * ∑ p ∈ P with p ∣ d * k ∧ ¬p ∣ d, VQ d) +
        (∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
          ((d * k).totient : ℝ)⁻¹ * ∑ r ∈ Q with r ∣ d * k ∧ ¬r ∣ d, VP d) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add
      (add_le_add (conductor_mass_le_log_prefix T U hU)
        (excludedPrime_conductor_mass_le P T hP VQ hVQ))
      (excludedPrime_conductor_mass_le Q T hQ VP hVP)

end Erdos964
