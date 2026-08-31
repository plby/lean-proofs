import ErdosProblems.Erdos964.SemiprimeConductorReduction

/-!
# Modulus-dependent semiprime endpoints

Bombieri--Vinogradov requires the sum of the separate endpoint maxima, not
just a bound for a common endpoint. Here every modulus may choose its own
endpoint. The primitive and correction bounds retain their existing maxima.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem finiteResidueCount_family_sum_discrepancy_le (S : ℕ → Finset ℕ) (T : ℕ)
    (a : ℕ → ℕ) (ha : ∀ q, 0 < q → q ≤ T → (a q).Coprime q) :
    (∑ q ∈ Finset.Ioc 0 T,
      |(finiteResidueCount (S q) q (a q) : ℝ) - ((S q).card : ℝ) / q.totient|) ≤
      ∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
        ((d * k).totient : ℝ)⁻¹ * ∑ ψ : primitiveCharacters d,
          (‖finiteCenteredCharacterSum (S (d * k)) d ψ.1‖ +
            ‖∑ n ∈ S (d * k) with ¬n.Coprime (d * k), ψ.1 n‖) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ioc 0 T,
        (∑ d : q.divisors, ∑ ψ : primitiveCharacters d.1,
          (‖finiteCenteredCharacterSum (S q) d.1 ψ.1‖ +
            ‖∑ n ∈ S q with ¬n.Coprime q, ψ.1 n‖)) / q.totient := by
      apply Finset.sum_le_sum
      intro q hq
      have hq' := Finset.mem_Ioc.mp hq
      exact finiteResidueCount_discrepancy_conductors_le (S q) hq'.1 (ha q hq'.1 hq'.2)
    _ = _ := sum_conductor_weights_eq T
      (fun q d ψ => ‖finiteCenteredCharacterSum (S q) d ψ.1‖ +
        ‖∑ n ∈ S q with ¬n.Coprime q, ψ.1 n‖)

theorem semiprimeBlock_family_sum_discrepancy_le (P Q : Finset ℕ) (M N K T : ℕ)
    (X : ℕ → ℕ) (hX : ∀ q, 0 < q → q ≤ T → X q ∈ Finset.Icc 1 K)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hPinterval : P ⊆ Finset.Ioc 0 M) (hQinterval : Q ⊆ Finset.Ioc 0 N)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r)
    (hsize : ∀ p ∈ P, ∀ r ∈ Q, T < p * r)
    (a : ℕ → ℕ) (ha : ∀ q, 0 < q → q ≤ T → (a q).Coprime q) :
    (∑ q ∈ Finset.Ioc 0 T,
      |(finiteResidueCount (primeProductBlock P Q (X q)) q (a q) : ℝ) -
        ((primeProductBlock P Q (X q)).card : ℝ) / q.totient|) ≤
      (4 * (1 + Real.log (T : ℝ))) *
        (∑ d ∈ Finset.Ioc 1 T,
          (∑ ψ : primitiveCharacters d, primeProductBlockMaximum P Q K d ψ.1) / d.totient) +
      (∑ p ∈ P, ((p.totient : ℝ)⁻¹ * (4 * (1 + Real.log (T : ℝ)))) *
        ∑ d ∈ Finset.Ioc 0 (T / p),
          (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum Q N d ψ.1) / d.totient) +
      ∑ r ∈ Q, ((r.totient : ℝ)⁻¹ * (4 * (1 + Real.log (T : ℝ)))) *
        ∑ d ∈ Finset.Ioc 0 (T / r),
          (∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum P M d ψ.1) / d.totient := by
  classical
  let S (q : ℕ) := primeProductBlock P Q (X q)
  let U (d : ℕ) := if d = 1 then 0 else
    ∑ ψ : primitiveCharacters d, primeProductBlockMaximum P Q K d ψ.1
  let VP (d : ℕ) := ∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum P M d ψ.1
  let VQ (d : ℕ) := ∑ ψ : primitiveCharacters d, finiteCharacterCutoffMaximum Q N d ψ.1
  have hU (d : ℕ) : 0 ≤ U d := by
    dsimp only [U]
    split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg (fun ψ _ => primeProductBlockMaximum_nonneg _ _ _ _ ψ.1)
  have hVP (d : ℕ) : 0 ≤ VP d :=
    Finset.sum_nonneg (fun ψ _ => finiteCharacterCutoffMaximum_nonneg P M d ψ.1)
  have hVQ (d : ℕ) : 0 ≤ VQ d :=
    Finset.sum_nonneg (fun ψ _ => finiteCharacterCutoffMaximum_nonneg Q N d ψ.1)
  have hcenter (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (hdk : d * k ≤ T) :
      (∑ ψ : primitiveCharacters d, ‖finiteCenteredCharacterSum (S (d * k)) d ψ.1‖) ≤ U d := by
    by_cases hd1 : d = 1
    · subst d
      simp only [U, if_pos rfl, finiteCenteredCharacterSum_level_one, norm_zero,
        Finset.sum_const_zero, le_refl]
    · rw [show U d = ∑ ψ : primitiveCharacters d, primeProductBlockMaximum P Q K d ψ.1
        from if_neg hd1]
      apply Finset.sum_le_sum
      intro ψ hψ
      rw [finiteCenteredCharacterSum_primitive_of_one_lt _ (by omega) ψ, finiteCharacterSum]
      exact norm_primeProductBlock_le_maximum P Q K d (X (d * k)) ψ.1
        (hX (d * k) (Nat.mul_pos hd hk) hdk)
  have hcorr (d k : ℕ) (hd : 0 < d) (hk : 0 < k) (hdk : d * k ≤ T) :
      (∑ ψ : primitiveCharacters d, ‖∑ n ∈ S (d * k) with ¬n.Coprime (d * k), ψ.1 n‖) ≤
        (∑ p ∈ P with p ∣ d * k ∧ ¬p ∣ d, VQ d) +
        ∑ r ∈ Q with r ∣ d * k ∧ ¬r ∣ d, VP d := by
    calc
      _ ≤ ∑ ψ : primitiveCharacters d,
          ((∑ p ∈ P with p ∣ d * k ∧ ¬p ∣ d, finiteCharacterCutoffMaximum Q N d ψ.1) +
            ∑ r ∈ Q with r ∣ d * k ∧ ¬r ∣ d, finiteCharacterCutoffMaximum P M d ψ.1) := by
        apply Finset.sum_le_sum
        intro ψ hψ
        rw [← finiteCharacterSum_changeLevel_correction (S (d * k)) (Nat.dvd_mul_right d k) ψ.1]
        simpa only [Finset.filter_filter] using
          semiprimeBlock_changeLevel_correction_le P Q M N (X (d * k))
            (Nat.mul_pos hd hk) (Nat.dvd_mul_right d k) ψ.1 hP hQ hPinterval hQinterval
            hsep (fun p hp r hr => hdk.trans_lt (hsize p hp r hr))
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1 <;> exact Finset.sum_comm
  have hUsum : (∑ d ∈ Finset.Ioc 0 T, U d / d.totient) =
      ∑ d ∈ Finset.Ioc 1 T,
        (∑ ψ : primitiveCharacters d, primeProductBlockMaximum P Q K d ψ.1) / d.totient := by
    have hfilter : (Finset.Ioc 0 T).filter (fun d => d ≠ 1) = Finset.Ioc 1 T := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      omega
    calc
      _ = ∑ d ∈ Finset.Ioc 0 T, if d ≠ 1 then
          (∑ ψ : primitiveCharacters d, primeProductBlockMaximum P Q K d ψ.1) / d.totient
          else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hd1 : d = 1 <;> simp [U, hd1]
      _ = _ := by rw [← Finset.sum_filter, hfilter]
  have hprimary := conductor_mass_le_log_prefix T U hU
  rw [hUsum] at hprimary
  calc
    _ ≤ ∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
        ((d * k).totient : ℝ)⁻¹ *
          ((∑ ψ : primitiveCharacters d, ‖finiteCenteredCharacterSum (S (d * k)) d ψ.1‖) +
            ∑ ψ : primitiveCharacters d, ‖∑ n ∈ S (d * k) with ¬n.Coprime (d * k), ψ.1 n‖) := by
      simpa only [Finset.sum_add_distrib] using
        finiteResidueCount_family_sum_discrepancy_le S T a ha
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
      exact add_le_add (hcenter d k hdpos hk'.1 hdk) (hcorr d k hdpos hk'.1 hdk)
    _ = (∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
          ((d * k).totient : ℝ)⁻¹ * U d) +
        (∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
          ((d * k).totient : ℝ)⁻¹ * ∑ p ∈ P with p ∣ d * k ∧ ¬p ∣ d, VQ d) +
        (∑ d ∈ Finset.Ioc 0 T, ∑ k ∈ Finset.Ioc 0 (T / d),
          ((d * k).totient : ℝ)⁻¹ * ∑ r ∈ Q with r ∣ d * k ∧ ¬r ∣ d, VP d) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ _ := add_le_add
      (add_le_add hprimary (excludedPrime_conductor_mass_le P T hP VQ hVQ))
      (excludedPrime_conductor_mass_le Q T hQ VP hVP)

end Erdos964
