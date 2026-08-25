import ErdosProblems.Erdos964.SemiprimeLargeSieve
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveCharacterReduction

/-!
# Finite arithmetic-progression counts and character sums

The character reduction keeps the imprimitive correction as an exact sum.
For semiprimes, replacing this correction by its cardinality too early
would lose the cancellation needed when averaging over moduli.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

def finiteResidueCount (S : Finset ℕ) (q a : ℕ) : ℕ :=
  (S.filter (fun n => n ≡ a [MOD q])).card

noncomputable def finiteCharacterSum (S : Finset ℕ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) : ℂ := ∑ n ∈ S, χ n

noncomputable def finiteCenteredCharacterSum (S : Finset ℕ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) : ℂ := by
  classical
  exact finiteCharacterSum S q χ - if χ = 1 then (S.card : ℂ) else 0

theorem finiteCenteredCharacterSum_level_one (S : Finset ℕ)
    (χ : DirichletCharacter ℂ 1) : finiteCenteredCharacterSum S 1 χ = 0 := by
  classical
  rw [DirichletCharacter.level_one χ]
  have hone (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    apply MulChar.one_apply
    simpa only [ZMod.isUnit_iff_coprime] using Nat.coprime_one_right n
  simp [finiteCenteredCharacterSum, finiteCharacterSum, hone]

theorem finiteCenteredCharacterSum_primitive_of_one_lt (S : Finset ℕ) {d : ℕ}
    (hd : 1 < d) (ψ : primitiveCharacters d) :
    finiteCenteredCharacterSum S d ψ.1 = finiteCharacterSum S d ψ.1 := by
  have hne : ψ.1 ≠ 1 := by
    intro h
    let : NeZero d := ⟨by omega⟩
    have hprim := (DirichletCharacter.isPrimitive_def ψ.1).mp ψ.2
    rw [h, DirichletCharacter.conductor_one] at hprim
    omega
  simp only [finiteCenteredCharacterSum, if_neg hne, sub_zero]

theorem finiteResidueCount_character_average (S : Finset ℕ) {q a : ℕ}
    [NeZero q] (ha : a.Coprime q) :
    (finiteResidueCount S q a : ℂ) = (q.totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, χ (a : ZMod q)⁻¹ * finiteCharacterSum S q χ := by
  classical
  calc
    _ = ∑ n ∈ S, (if a % q = n % q then (1 : ℂ) else 0) := by
      simp only [finiteResidueCount, Finset.natCast_card_filter, Nat.ModEq, eq_comm]
    _ = ∑ n ∈ S, (q.totient : ℂ)⁻¹ * characterOrthogonalityKernel q a n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (inv_totient_mul_characterOrthogonalityKernel ha).symm
    _ = _ := by
      unfold characterOrthogonalityKernel finiteCharacterSum
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]

private theorem principal_at_inverse {q a : ℕ} (ha : a.Coprime q) :
    (1 : DirichletCharacter ℂ q) (a : ZMod q)⁻¹ = 1 := by
  have hunit : IsUnit (a : ZMod q) := by
    simpa only [ZMod.isUnit_iff_coprime] using ha
  obtain ⟨u, hu⟩ := hunit
  rw [← hu, ZMod.inv_coe_unit]
  exact MulChar.one_apply_coe _

theorem finiteResidueCount_centered_average (S : Finset ℕ) {q a : ℕ}
    [NeZero q] (ha : a.Coprime q) :
    (finiteResidueCount S q a : ℂ) - (S.card : ℂ) / q.totient =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
        χ (a : ZMod q)⁻¹ * finiteCenteredCharacterSum S q χ := by
  classical
  simp only [finiteCenteredCharacterSum, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    principal_at_inverse ha, one_mul]
  rw [← finiteResidueCount_character_average S ha]
  ring

/-- The progression discrepancy is bounded by the mean centered character
sum. This includes the exact principal-character correction. -/
theorem finiteResidueCount_discrepancy_le (S : Finset ℕ) {q a : ℕ}
    [NeZero q] (ha : a.Coprime q) :
    |(finiteResidueCount S q a : ℝ) - (S.card : ℝ) / q.totient| ≤
      (∑ χ : DirichletCharacter ℂ q, ‖finiteCenteredCharacterSum S q χ‖) / q.totient := by
  classical
  have hnorm :
      ‖∑ χ : DirichletCharacter ℂ q,
        χ (a : ZMod q)⁻¹ * finiteCenteredCharacterSum S q χ‖ ≤
      ∑ χ : DirichletCharacter ℂ q, ‖finiteCenteredCharacterSum S q χ‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro χ hχ
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  calc
    _ = ‖(finiteResidueCount S q a : ℂ) - (S.card : ℂ) / q.totient‖ := by
      have hcast :
          (((finiteResidueCount S q a : ℝ) - (S.card : ℝ) / q.totient : ℝ) : ℂ) =
            (finiteResidueCount S q a : ℂ) - (S.card : ℂ) / q.totient := by
        push_cast
        rfl
      rw [← hcast, Complex.norm_real, Real.norm_eq_abs]
    _ = (q.totient : ℝ)⁻¹ *
        ‖∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * finiteCenteredCharacterSum S q χ‖ := by
      rw [finiteResidueCount_centered_average S ha, norm_mul, norm_inv]
      simp
    _ ≤ (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q, ‖finiteCenteredCharacterSum S q χ‖ :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring

theorem finiteCharacterSum_changeLevel_correction (S : Finset ℕ) {q d : ℕ}
    (hd : d ∣ q) (ψ : DirichletCharacter ℂ d) :
    finiteCharacterSum S d ψ -
      finiteCharacterSum S q (DirichletCharacter.changeLevel hd ψ) =
      ∑ n ∈ S with ¬n.Coprime q, ψ n := by
  classical
  unfold finiteCharacterSum
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hcop : n.Coprime q
  · have heq : (DirichletCharacter.changeLevel hd ψ) (n : ZMod q) = ψ (n : ZMod d) := by
      simpa using ψ.changeLevel_eq_cast_of_dvd' hd (Nat.isCoprime_iff_coprime.mpr hcop)
    rw [if_neg (not_not.mpr hcop), heq, sub_self]
  · have hzero : (DirichletCharacter.changeLevel hd ψ) (n : ZMod q) = 0 :=
      MulChar.map_nonunit _ (by simpa only [ZMod.isUnit_iff_coprime] using hcop)
    simp only [hcop, not_false_eq_true, if_true, hzero, sub_zero]

/-- Centering commutes with induction of a character, so the same exact
correction applies before the conductor decomposition. -/
theorem finiteCenteredCharacterSum_changeLevel_correction (S : Finset ℕ) {q d : ℕ}
    [NeZero q] (hd : d ∣ q) (ψ : DirichletCharacter ℂ d) :
    finiteCenteredCharacterSum S d ψ -
      finiteCenteredCharacterSum S q (DirichletCharacter.changeLevel hd ψ) =
      ∑ n ∈ S with ¬n.Coprime q, ψ n := by
  classical
  have hprincipal : DirichletCharacter.changeLevel hd ψ = 1 ↔ ψ = 1 := by
    constructor
    · intro h
      apply DirichletCharacter.changeLevel_injective hd
      simpa only [DirichletCharacter.changeLevel_one] using h
    · rintro rfl
      exact DirichletCharacter.changeLevel_one hd
  unfold finiteCenteredCharacterSum
  simp only [hprincipal, sub_sub_sub_cancel_right]
  exact finiteCharacterSum_changeLevel_correction S hd ψ

/-- The character average may be indexed by primitive conductors. The
correction is a norm of a character sum, not a count of excluded elements. -/
theorem finiteResidueCount_discrepancy_conductors_le (S : Finset ℕ) {q a : ℕ}
    (hq : 0 < q) (ha : a.Coprime q) :
    |(finiteResidueCount S q a : ℝ) - (S.card : ℝ) / q.totient| ≤
      (∑ d : q.divisors, ∑ ψ : primitiveCharacters d.1,
        (‖finiteCenteredCharacterSum S d.1 ψ.1‖ +
          ‖∑ n ∈ S with ¬n.Coprime q, ψ.1 n‖)) / q.totient := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  apply (finiteResidueCount_discrepancy_le S ha).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [sum_characters_eq_sum_divisor_primitive hq]
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro ψ hψ
  have heq := finiteCenteredCharacterSum_changeLevel_correction S
    (Nat.dvd_of_mem_divisors d.2) ψ.1
  have hinduced :
      finiteCenteredCharacterSum S q
        (DirichletCharacter.changeLevel (Nat.dvd_of_mem_divisors d.2) ψ.1) =
      finiteCenteredCharacterSum S d.1 ψ.1 -
        ∑ n ∈ S with ¬n.Coprime q, ψ.1 n := by
    linear_combination -heq
  rw [hinduced]
  exact norm_sub_le _ _

/-- Below the product range, the modulus cannot contain both distinct
prime factors. Thus the noncoprime terms split into two disjoint prime
slices, with their character weights still intact. -/
theorem primeProductBlock_noncoprime_sum (P Q : Finset ℕ) (X q : ℕ)
    (hq : 0 < q) (w : ℕ → ℂ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r)
    (hsize : ∀ p ∈ P, ∀ r ∈ Q, q < p * r) :
    ∑ n ∈ primeProductBlock P Q X with ¬n.Coprime q, w n =
      (∑ p ∈ P with p ∣ q, ∑ r ∈ Q with p * r ≤ X, w (p * r)) +
      ∑ r ∈ Q with r ∣ q, ∑ p ∈ P with p * r ≤ X, w (p * r) := by
  classical
  have hind (p : ℕ) (hp : p ∈ P) (r : ℕ) (hr : r ∈ Q) :
      (if p * r ≤ X then if ¬(p * r).Coprime q then w (p * r) else 0 else 0) =
        (if p ∣ q then if p * r ≤ X then w (p * r) else 0 else 0) +
        (if r ∣ q then if p * r ≤ X then w (p * r) else 0 else 0) := by
    have hnotboth : ¬(p ∣ q ∧ r ∣ q) := by
      rintro ⟨hpq, hrq⟩
      have hdvd := ((Nat.coprime_primes (hP p hp) (hQ r hr)).mpr
        (ne_of_lt (hsep p hp r hr))).mul_dvd_of_dvd_of_dvd hpq hrq
      exact (not_le_of_gt (hsize p hp r hr)) (Nat.le_of_dvd hq hdvd)
    by_cases hcut : p * r ≤ X <;> by_cases hpq : p ∣ q <;> by_cases hrq : r ∣ q
    all_goals simp_all only [Nat.coprime_mul_iff_left,
      (hP p hp).coprime_iff_not_dvd, (hQ r hr).coprime_iff_not_dvd,
      not_true_eq_false, not_false_eq_true, and_true, and_false,
      if_true, if_false, add_zero, zero_add]
  rw [Finset.sum_filter, sum_primeProductBlock P Q X _ hP hQ hsep]
  simp only [Finset.sum_filter]
  calc
    _ = ∑ p ∈ P, ∑ r ∈ Q,
        ((if p ∣ q then if p * r ≤ X then w (p * r) else 0 else 0) +
          (if r ∣ q then if p * r ≤ X then w (p * r) else 0 else 0)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro r hr
      exact hind p hp r hr
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]
      · rw [Finset.sum_comm]
        simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]

/-- Exact prime-slice form of the imprimitive character correction. -/
theorem semiprimeBlock_changeLevel_correction (P Q : Finset ℕ) (X : ℕ)
    {q d : ℕ} (hq : 0 < q) (hd : d ∣ q) (ψ : DirichletCharacter ℂ d)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ r ∈ Q, r.Prime)
    (hsep : ∀ p ∈ P, ∀ r ∈ Q, p < r)
    (hsize : ∀ p ∈ P, ∀ r ∈ Q, q < p * r) :
    finiteCharacterSum (primeProductBlock P Q X) d ψ -
      finiteCharacterSum (primeProductBlock P Q X) q
        (DirichletCharacter.changeLevel hd ψ) =
      (∑ p ∈ P with p ∣ q, ψ p * ∑ r ∈ Q with p * r ≤ X, ψ r) +
      ∑ r ∈ Q with r ∣ q, ψ r * ∑ p ∈ P with p * r ≤ X, ψ p := by
  classical
  rw [finiteCharacterSum_changeLevel_correction,
    primeProductBlock_noncoprime_sum P Q X q hq _ hP hQ hsep hsize]
  simp only [Nat.cast_mul, map_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro p hp
  exact mul_comm _ _

end Erdos964
