import ErdosProblems.Erdos1148.ResidueIndexComparison
import ErdosProblems.Erdos1148.ResidueMaximalCount
import ErdosProblems.Erdos1148.DivisorBounds

/-! # A subpower loss in the residue-unit index -/

namespace Erdos1148.DukeArithmetic

open NumberField

theorem orderIndex_le_four_pow_primeFactors_mul_residueUnitIndex
    {d : ℤ} [Fact (¬IsSquare d)] {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    quadraticOrderIndex ht ≤ 4 ^ (quadraticOrderIndex ht).primeFactors.card *
      (orderResidueUnitSubgroup ht).index := by
  let R := 𝓞 (QuadraticDiscrAlgebra d) ⧸ quadraticOrderConductor d
  let := quadraticOrderConductor_quotient_finite ht
  have hnR : (quadraticOrderIndex ht : R) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr (quadraticOrderIndex_mem_conductor ht)
    simpa only [map_natCast] using h
  have hmax : Nat.card (MaximalSpectrum R) ≤ 2 * (quadraticOrderIndex ht).primeFactors.card := by
    have h := maximalSpectrum_card_le_degree_mul_primeFactors (QuadraticDiscrAlgebra d)
      (Ideal.Quotient.mk (quadraticOrderConductor d)) Ideal.Quotient.mk_surjective
      (quadraticOrderIndex ht) (quadraticOrderIndex_ne_zero ht) hnR
    simpa only [quadraticDiscrAlgebra_finrank] using h
  have hpow : 2 ^ Nat.card (MaximalSpectrum R) ≤
      4 ^ (quadraticOrderIndex ht).primeFactors.card := by
    calc
      _ ≤ 2 ^ (2 * (quadraticOrderIndex ht).primeFactors.card) :=
        pow_le_pow_right₀ (by decide) hmax
      _ = _ := by rw [pow_mul]; norm_num
  have hR : Nat.card R ≤ 4 ^ (quadraticOrderIndex ht).primeFactors.card * Nat.card Rˣ :=
    (finite_ring_card_le_pow_maximal_mul_units R).trans (Nat.mul_le_mul_right _ hpow)
  have hmul : quadraticOrderIndex ht * Nat.card Rˣ ≤
      (4 ^ (quadraticOrderIndex ht).primeFactors.card * (orderResidueUnitSubgroup ht).index) *
        Nat.card Rˣ := by
    calc
      _ ≤ Nat.card R * (orderResidueUnitSubgroup ht).index :=
        orderIndex_mul_residue_units_card_le ht
      _ ≤ (4 ^ (quadraticOrderIndex ht).primeFactors.card * Nat.card Rˣ) *
          (orderResidueUnitSubgroup ht).index := Nat.mul_le_mul_right _ hR
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hmul Nat.card_pos

lemma exists_four_pow_primeFactors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 →
      (4 : ℝ) ^ n.primeFactors.card ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := exists_prod_factorization_le_rpow (c := 4) (by norm_num) hε
  refine ⟨C, hC, ?_⟩
  intro n hn
  apply le_trans _ (hbound n hn)
  calc
    _ = ∏ _p ∈ n.primeFactors, (4 : ℝ) := by simp
    _ ≤ ∏ p ∈ n.primeFactors, (4 : ℝ) * ((n.factorization p : ℝ) + 1) ^ 2 := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p _
      have h : (1 : ℝ) ≤ ((n.factorization p : ℝ) + 1) ^ 2 :=
        one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg _))
      linarith

theorem exists_residueUnitIndex_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℤ) [Fact (¬IsSquare d)] (t : ℤ × ℤ × ℤ) (ht : discr t = d),
      c * (quadraticOrderIndex ht : ℝ) ^ (1 - ε) ≤ (orderResidueUnitSubgroup ht).index := by
  obtain ⟨C, hC, hbound⟩ := exists_four_pow_primeFactors_le_rpow hε
  refine ⟨C⁻¹, inv_pos.mpr hC, ?_⟩
  intro d hns t ht
  have hf : (0 : ℝ) < quadraticOrderIndex ht := by
    exact_mod_cast Nat.pos_of_ne_zero (quadraticOrderIndex_ne_zero ht)
  have hnat : (quadraticOrderIndex ht : ℝ) ≤
      (4 : ℝ) ^ (quadraticOrderIndex ht).primeFactors.card *
        ((orderResidueUnitSubgroup ht).index : ℝ) := by
    exact_mod_cast orderIndex_le_four_pow_primeFactors_mul_residueUnitIndex ht
  have hmul : (quadraticOrderIndex ht : ℝ) ≤
      (C * (quadraticOrderIndex ht : ℝ) ^ ε) * ((orderResidueUnitSubgroup ht).index : ℝ) :=
    hnat.trans (mul_le_mul_of_nonneg_right
      (hbound _ (quadraticOrderIndex_ne_zero ht)) (Nat.cast_nonneg _))
  have hdiv := (div_le_iff₀ (show 0 < C * (quadraticOrderIndex ht : ℝ) ^ ε by positivity)).mpr
    (by simpa only [mul_comm] using hmul)
  calc
    C⁻¹ * (quadraticOrderIndex ht : ℝ) ^ (1 - ε) =
        (quadraticOrderIndex ht : ℝ) / (C * (quadraticOrderIndex ht : ℝ) ^ ε) := by
      rw [Real.rpow_sub hf, Real.rpow_one]
      ring
    _ ≤ _ := hdiv

end Erdos1148.DukeArithmetic
