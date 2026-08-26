import ErdosProblems.Erdos380.ResidueProducts

/-!
# Changing the modulus of a prime character average

Only primes dividing the new modulus can change a character value. Counting
these primes supplies the explicit error when moving to primitive conductors,
and also controls the principal-character term in residue orthogonality.
-/

open scoped BigOperators

namespace Erdos380

noncomputable section

local instance transferCharacterDecidableEq (q : ℕ) : DecidableEq (DirichletCharacter ℂ q) :=
  Classical.decEq _

lemma primeCharacterMean_changeLevel_sub_le {d q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ d) (hd : d ∣ q) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    ‖primeCharacterMean s (DirichletCharacter.changeLevel hd χ) -
        primeCharacterMean s χ‖ ≤ (q.primeFactors.card : ℝ) / (s.card : ℝ) := by
  classical
  rw [primeCharacterMean, primeCharacterMean, ← sub_div, norm_div, Complex.norm_natCast,
    ← Finset.sum_sub_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ p ∈ s, ‖DirichletCharacter.changeLevel hd χ p - χ p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ s, if p ∈ q.primeFactors then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      by_cases hpf : p ∈ q.primeFactors
      · rw [if_pos hpf]
        have hnu : ¬ IsUnit (p : ZMod q) := by
          rw [ZMod.isUnit_prime_iff_not_dvd (hs p hp)]
          exact not_not.mpr (Nat.dvd_of_mem_primeFactors hpf)
        rw [MulChar.map_nonunit _ hnu, zero_sub, norm_neg]
        exact χ.norm_le_one p
      · rw [if_neg hpf]
        have hpd : ¬ p ∣ q := fun h => hpf ((hs p hp).mem_primeFactors h (NeZero.ne q))
        have hcop := (hs p hp).coprime_iff_not_dvd.mpr hpd
        have heq : DirichletCharacter.changeLevel hd χ p = χ p := by
          simpa using χ.changeLevel_eq_cast_of_dvd' hd hcop.isCoprime
        simp [heq]
    _ = ((s ∩ q.primeFactors).card : ℝ) := by
      simp only [Finset.sum_boole, Finset.filter_mem_eq_inter]
    _ ≤ (q.primeFactors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right

lemma primeCharacterMean_one_level_one (s : Finset ℕ) (hs : s.Nonempty) :
    primeCharacterMean s (1 : DirichletCharacter ℂ 1) = 1 := by
  have hf (p : ℕ) : (1 : DirichletCharacter ℂ 1) p = 1 := by
    rw [Subsingleton.elim (p : ZMod 1) 1]
    exact map_one _
  have hM : (s.card : ℂ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  simp [primeCharacterMean, hf, hM]

lemma primeCharacterMean_principal_sub_one_le {q : ℕ} [NeZero q]
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (hne : s.Nonempty) :
    ‖primeCharacterMean s (1 : DirichletCharacter ℂ q) - 1‖ ≤
      (q.primeFactors.card : ℝ) / (s.card : ℝ) := by
  have h := primeCharacterMean_changeLevel_sub_le
    (1 : DirichletCharacter ℂ 1) (one_dvd q) s hs
  simpa only [map_one, primeCharacterMean_one_level_one s hne] using h

lemma norm_prod_sub_one_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - 1‖ ≤ ∑ i ∈ s, ‖f i - 1‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self i s)
    have hfs : ∀ j ∈ s, ‖f j‖ ≤ 1 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      ‖f i * (∏ j ∈ s, f j) - 1‖ =
          ‖f i * ((∏ j ∈ s, f j) - 1) + (f i - 1)‖ := by congr 1; ring
      _ ≤ ‖f i * ((∏ j ∈ s, f j) - 1)‖ + ‖f i - 1‖ := norm_add_le _ _
      _ ≤ ‖(∏ j ∈ s, f j) - 1‖ + ‖f i - 1‖ := by
        rw [norm_mul]
        exact add_le_add
          (mul_le_of_le_one_left (norm_nonneg ((∏ j ∈ s, f j) - 1)) hfi) le_rfl
      _ ≤ _ := by linarith [ih hfs]

theorem principal_product_sub_one_le {ι : Type*} [Fintype ι] (s : ι → Finset ℕ)
    {q : ℕ} [NeZero q] (hs : ∀ i p, p ∈ s i → p.Prime)
    (hne : ∀ i, (s i).Nonempty) :
    ‖(∏ i, primeCharacterMean (s i) (1 : DirichletCharacter ℂ q)) - 1‖ ≤
      ∑ i, (q.primeFactors.card : ℝ) / ((s i).card : ℝ) := by
  refine (norm_prod_sub_one_le_sum Finset.univ
    (fun i => primeCharacterMean (s i) (1 : DirichletCharacter ℂ q))
    (fun i _ => primeCharacterMean_norm_le_one _ _)).trans ?_
  exact Finset.sum_le_sum fun i _ => primeCharacterMean_principal_sub_one_le
    (s i) (hs i) (hne i)

theorem ten_prime_residue_uniform_error_le (s : Fin 10 → Finset ℕ)
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a)
    (hs : ∀ i p, p ∈ s i → p.Prime) (hne : ∀ i, (s i).Nonempty) :
    ‖(tupleResidueProbability s q a : ℂ) - 1 / (q.totient : ℂ)‖ ≤
      ((∑ i, (q.primeFactors.card : ℝ) / ((s i).card : ℝ)) +
        ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ∑ i, ‖primeCharacterMean (s i) χ‖ ^ 10) / (q.totient : ℝ) := by
  classical
  let c : ℂ := ∏ i, primeCharacterMean (s i) (1 : DirichletCharacter ℂ q)
  have htri := norm_sub_le_norm_sub_add_norm_sub (tupleResidueProbability s q a : ℂ)
    (c / (q.totient : ℂ)) (1 / (q.totient : ℂ))
  have hp : ‖c / (q.totient : ℂ) - 1 / (q.totient : ℂ)‖ ≤
      (∑ i, (q.primeFactors.card : ℝ) / ((s i).card : ℝ)) / (q.totient : ℝ) := by
    rw [← sub_div, norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (principal_product_sub_one_le s hs hne)
      (Nat.cast_nonneg _)
  calc
    _ ≤ _ := htri
    _ ≤ _ := add_le_add (ten_prime_residue_discrepancy_le s ha) hp
    _ = _ := by rw [← add_div]; congr 1; exact add_comm _ _

end

end Erdos380
