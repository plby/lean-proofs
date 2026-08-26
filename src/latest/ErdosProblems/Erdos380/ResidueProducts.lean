import ErdosProblems.Erdos380.PrimeMoments
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Residues of products of independently selected primes

The finite orthogonality identity retains the principal character exactly;
thus primes dividing the modulus are not discarded without accounting for
their contribution.
-/

open scoped BigOperators

namespace Erdos380

noncomputable section

local instance characterDecidableEq (q : ℕ) : DecidableEq (DirichletCharacter ℂ q) :=
  Classical.decEq _

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Number of tuples from a family of finite sets with a prescribed product residue. -/
def tupleResidueCount (s : ι → Finset ℕ) (q : ℕ) (a : ZMod q) : ℕ := by
  classical
  exact (Finset.univ.filter fun f : ∀ i, s i =>
    ((∏ i, (f i).val : ℕ) : ZMod q) = a).card

lemma sum_character_tuple_product (s : ι → Finset ℕ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (∑ f : ∀ i, s i, χ (∏ i, (f i).val : ℕ)) =
      ∏ i, ∑ p ∈ s i, χ p := by
  classical
  simp only [Nat.cast_prod, map_prod]
  rw [← Fintype.prod_sum (fun i (p : s i) => χ p.val)]
  apply Finset.prod_congr rfl
  intro i _hi
  exact (Finset.sum_subtype (s i) (by simp) (fun p => χ p)).symm

/-- Character orthogonality for the unnormalized tuple count. -/
lemma totient_mul_tupleResidueCount (s : ι → Finset ℕ) {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : IsUnit a) :
    (q.totient : ℂ) * (tupleResidueCount s q a : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (∏ i, ∑ p ∈ s i, χ p) := by
  classical
  symm
  calc
    _ = ∑ χ : DirichletCharacter ℂ q,
        ∑ f : ∀ i, s i, χ a⁻¹ * χ (∏ i, (f i).val : ℕ) := by
      simp_rw [← sum_character_tuple_product, Finset.mul_sum]
    _ = ∑ f : ∀ i, s i,
        ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ (∏ i, (f i).val : ℕ) :=
      Finset.sum_comm
    _ = ∑ f : ∀ i, s i,
        if ((∏ i, (f i).val : ℕ) : ZMod q) = a then (q.totient : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro f _hf
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
      simp only [eq_comm]
    _ = _ := by simp [tupleResidueCount, mul_comm, Finset.sum_ite]

lemma primeCharacterMean_norm_le_one (s : Finset ℕ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) : ‖primeCharacterMean s χ‖ ≤ 1 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [primeCharacterMean]
  have hM : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  rw [primeCharacterMean, norm_div, Complex.norm_natCast, div_le_one hM]
  calc
    ‖∑ p ∈ s, χ p‖ ≤ ∑ p ∈ s, ‖χ p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ s, (1 : ℝ) := Finset.sum_le_sum fun p _hp => χ.norm_le_one p
    _ = _ := by simp

/-- Probability for independent uniform choices from the indicated finite sets. -/
def tupleResidueProbability (s : ι → Finset ℕ) (q : ℕ) (a : ZMod q) : ℝ :=
  (tupleResidueCount s q a : ℝ) / ∏ i, ((s i).card : ℝ)

lemma totient_mul_tupleResidueProbability (s : ι → Finset ℕ) {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : IsUnit a) :
    (q.totient : ℂ) * (tupleResidueProbability s q a : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (∏ i, primeCharacterMean (s i) χ) := by
  classical
  simp only [tupleResidueProbability, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_prod, primeCharacterMean, Finset.prod_div_distrib]
  simp_rw [← mul_div_assoc, ← Finset.sum_div]
  rw [totient_mul_tupleResidueCount s ha]

/-- Exact discrepancy from the principal-character term. -/
lemma tupleResidueProbability_sub_principal (s : ι → Finset ℕ) {q : ℕ} [NeZero q]
    {a : ZMod q} (ha : IsUnit a) :
    (tupleResidueProbability s q a : ℂ) -
        (∏ i, primeCharacterMean (s i) (1 : DirichletCharacter ℂ q)) / q.totient =
      (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        χ a⁻¹ * (∏ i, primeCharacterMean (s i) χ)) / q.totient := by
  classical
  have hφ : (q.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  have hia : IsUnit a⁻¹ := by
    rw [← ha.unit_spec, ZMod.inv_coe_unit]
    exact Units.isUnit _
  have h := totient_mul_tupleResidueProbability s ha
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    MulChar.one_apply hia, one_mul] at h
  apply (eq_div_iff hφ).mpr
  rw [sub_mul, div_mul_cancel₀ _ hφ]
  linear_combination h

/-- Triangle inequality for the nonprincipal Fourier modes. -/
theorem tupleResidueProbability_discrepancy_le (s : ι → Finset ℕ)
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ‖(tupleResidueProbability s q a : ℂ) -
        (∏ i, primeCharacterMean (s i) (1 : DirichletCharacter ℂ q)) / q.totient‖ ≤
      (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ∏ i, ‖primeCharacterMean (s i) χ‖) / (q.totient : ℝ) := by
  classical
  rw [tupleResidueProbability_sub_principal s ha, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro χ _hχ
  rw [norm_mul, norm_prod]
  exact mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (χ.norm_le_one a⁻¹)

/-- A deliberately coarse form of the equal-exponent product inequality. -/
lemma prod_nonneg_le_sum_pow_card (f : ι → ℝ) [Nonempty ι]
    (hf : ∀ i, 0 ≤ f i) :
    ∏ i, f i ≤ ∑ i, f i ^ Fintype.card ι := by
  classical
  obtain ⟨j, _hj, hj⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  calc
    ∏ i, f i ≤ ∏ _i : ι, f j :=
      Finset.prod_le_prod (fun i _ => hf i) (fun i hi => hj i hi)
    _ = f j ^ Fintype.card ι := by simp
    _ ≤ ∑ i, f i ^ Fintype.card ι :=
      Finset.single_le_sum (fun i _ => pow_nonneg (hf i) _) (Finset.mem_univ j)

/-- Ten independent factors reduce the residue error to tenth moments. -/
theorem ten_prime_residue_discrepancy_le (s : Fin 10 → Finset ℕ)
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ‖(tupleResidueProbability s q a : ℂ) -
        (∏ i, primeCharacterMean (s i) (1 : DirichletCharacter ℂ q)) / q.totient‖ ≤
      (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ∑ i, ‖primeCharacterMean (s i) χ‖ ^ 10) / (q.totient : ℝ) := by
  classical
  refine (tupleResidueProbability_discrepancy_le s ha).trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro χ _hχ
  simpa using prod_nonneg_le_sum_pow_card (fun i => ‖primeCharacterMean (s i) χ‖)
    (fun i => norm_nonneg _)

end

end Erdos380
