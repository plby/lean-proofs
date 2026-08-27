import ErdosProblems.Erdos4.FGKMTFaceContribution

/-! A finite, quantitative lower bound for the actual ideal sieve quadratic form. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients RestrictedProductNorm Classical

variable {P : Type*} [Fintype P] [DecidableEq P] {k R : ℕ}

theorem rationalIdealForm_good_mass_lower {b : ℝ} (hb : 0 ≤ b) (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T : ℕ} (hR : 1 ≤ R) (hT : 1 ≤ T) (hTR : T ^ 2 ≤ R)
    (hcop : ∀ p, (ell p).Coprime W)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q) (j : Fin k) :
    sieveWindowDensity ell *
      (∑ a ∈ Finset.univ.filter (MixedDivisorGood (SieveCore j) W T
        (Real.log (R : ℝ) / 2) (R := R)), mixedDivisorNumerator (SieveCore j) W b T a) ≤
      rationalIdealForm b R ell j := by
  let S := (Finset.univ : Finset ((SieveCore j ⊕ Fin 2) → Fin (R + 1))).filter
    (MixedDivisorGood (SieveCore j) W T (Real.log (R : ℝ) / 2))
  let f : (P → Option (Fin k)) × (P → Option (Fin k)) → ℝ :=
    fun z => rationalIdealPair b R ell j z.1 z.2
  calc
    _ ≤ ∑ a ∈ S, f (faceLabelPair ell j a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a ha
      exact faceLabel_contribution_lower hb ell hprime hinj hR hT hTR hcop hcover j a
        (Finset.mem_filter.mp ha).2
    _ = ∑ z ∈ S.image (faceLabelPair ell j), f z := by
      rw [Finset.sum_image (faceLabelPair_injOn ell hprime hinj (Real.log (R : ℝ) / 2) hcover j)]
    _ ≤ ∑ z : (P → Option (Fin k)) × (P → Option (Fin k)), f z :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun z _ _ => rationalIdealPair_nonneg hb R ell (fun p => (hprime p).two_le) j z.1 z.2)
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

theorem rationalIdealForm_mixed_mass_lower {b : ℝ} (hb : 0 < b) (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T K : ℕ} (hR : 2 ≤ R) (hT : 1 ≤ T) (hTR : T ^ 2 ≤ R) (hK : 2 ≤ K)
    (hcop : ∀ p, (ell p).Coprime W)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) (j : Fin k)
    (hmean : (Fintype.card (SieveCore j) : ℝ) * rationalMass W b R ≤
      (1 / 4) * (b * rationalSquareMass W b R * (Real.log (R : ℝ) / 2)))
    (hcollision : 4 * (Fintype.card (SieveCore j) + 2) ^ 2 ≤ K - 1) :
    sieveWindowDensity ell * mixedDivisorMass (SieveCore j) W b R T / 2 ≤
      rationalIdealForm b R ell j := by
  have hR1 : 1 ≤ R := by omega
  have hTR1 : T ≤ R := by nlinarith
  have hlog : 0 < Real.log (R : ℝ) / 2 := by
    exact div_pos (Real.log_pos (by exact_mod_cast hR)) (by norm_num)
  have hm := mixedDivisor_good_mass_half (SieveCore j) W hb hR1 hT hTR1 hK hpre hlog hmean hcollision
  have hδ := sieveWindowDensity_nonneg ell (fun p => (hprime p).one_le)
  have hh := (mul_le_mul_of_nonneg_left hm hδ).trans
    (rationalIdealForm_good_mass_lower hb.le ell hprime hinj hR1 hT hTR hcop hcover j)
  simpa only [mul_div_assoc] using hh

theorem sieveCore_card (j : Fin k) : Fintype.card (SieveCore j) = k - 1 := by
  have hh := Fintype.card_congr (Equiv.optionSubtypeNe j)
  simp only [Fintype.card_option, Fintype.card_fin] at hh
  change Fintype.card (SieveCore j) + 1 = k at hh
  omega

theorem rationalIdealForm_energy_gain {b : ℝ} (hb : 0 < b) (ell : P → ℕ)
    (hprime : ∀ p, (ell p).Prime) (hinj : Function.Injective ell)
    {W T K : ℕ} (hR : 2 ≤ R) (hT : 1 ≤ T) (hTR : T ^ 2 ≤ R) (hK : 2 ≤ K)
    (hcop : ∀ p, (ell p).Coprime W)
    (hcover : ∀ u : ℕ, u ≤ R → Squarefree u → u.Coprime W →
      ∀ q ∈ u.primeFactors, ∃ p, ell p = q)
    (hpre : ∀ p : ℕ, p.Prime → p ≤ K → p ∣ W) (j : Fin k)
    (hmean : (k : ℝ) * rationalMass W b R ≤
      (1 / 4) * (b * rationalSquareMass W b R * (Real.log (R : ℝ) / 2)))
    (hcollision : 4 * (k + 1) ^ 2 ≤ K - 1) :
    (sieveWindowDensity ell * rationalMass W b T ^ 2 / (2 * rationalSquareMass W b R)) *
      energy (rationalCoefficient (k := k) b R ell) ≤ rationalIdealForm b R ell j := by
  have hk : 1 ≤ k := by have := j.isLt; omega
  have hmean' : (Fintype.card (SieveCore j) : ℝ) * rationalMass W b R ≤
      (1 / 4) * (b * rationalSquareMass W b R * (Real.log (R : ℝ) / 2)) := by
    apply le_trans _ hmean
    apply mul_le_mul_of_nonneg_right _ (rationalMass_nonneg hb.le W R)
    rw [sieveCore_card]
    exact_mod_cast Nat.sub_le k 1
  have hcollision' : 4 * (Fintype.card (SieveCore j) + 2) ^ 2 ≤ K - 1 := by
    rw [sieveCore_card, show k - 1 + 2 = k + 1 by omega]
    exact hcollision
  have hmain := rationalIdealForm_mixed_mass_lower hb ell hprime hinj hR hT hTR hK
    hcop hcover hpre j hmean' hcollision'
  have hM : 0 < rationalSquareMass W b R :=
    zero_lt_one.trans_le (one_le_rationalSquareMass W b (by omega))
  have hδ := sieveWindowDensity_nonneg ell (fun p => (hprime p).one_le)
  have hfactor : 0 ≤ sieveWindowDensity ell * rationalMass W b T ^ 2 /
      (2 * rationalSquareMass W b R) := by positivity
  calc
    _ ≤ (sieveWindowDensity ell * rationalMass W b T ^ 2 / (2 * rationalSquareMass W b R)) *
        rationalSquareMass W b R ^ k :=
      mul_le_mul_of_nonneg_left (rationalCoefficient_energy_upper b R ell hprime hinj hcop) hfactor
    _ = sieveWindowDensity ell * mixedDivisorMass (SieveCore j) W b R T / 2 := by
      have hpow : rationalSquareMass W b R ^ k =
          rationalSquareMass W b R ^ (k - 1) * rationalSquareMass W b R := by
        rw [← pow_succ, Nat.sub_add_cancel hk]
      unfold mixedDivisorMass
      rw [sieveCore_card, hpow]
      field_simp
    _ ≤ _ := hmain

end Erdos4.FGKMT
