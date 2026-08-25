import ErdosProblems.Erdos67.MRFiniteHalaszProductSmoothing
import ErdosProblems.Erdos67.MRHalaszBandDistance
import ErdosProblems.Erdos67.MRGSTwistedEuler

/-!
# The two-block deletion algebra in the corrected GS argument

For the two prime blocks used by the finite Halasz typical coefficient, the
inclusion--exclusion sum has just four terms.  This file records those four
terms as genuine multiplicative prime-band restrictions.  It also proves the
source inequality (A.3): deleting any collection of primes can reduce the
pretentious distance by at most a factor of two.

These statements are finite and coefficientwise.  In particular they do not
postulate the analytic prefix estimate (A.9).
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Delete every integer having a prime factor in `Q`.  Writing the deletion
as a prime-band coefficient makes multiplicativity available without a new
arithmetic-function construction. -/
def gsDeletePrimeBand (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q] : ℕ → ℂ :=
  primeBandCoefficient f (fun p ↦ ¬ Q p)

theorem primeSupported_compl_iff_not_hasPrimeFactor
    (Q : ℕ → Prop) [DecidablePred Q] {n : ℕ} (hn : 0 < n) :
    PrimeSupported (fun p ↦ ¬ Q p) n ↔ ¬ HasPrimeFactor Q n := by
  rw [hasPrimeFactor_iff]
  constructor
  · intro hs hhas
    obtain ⟨p, hpn, hpQ⟩ := hhas
    exact hs.2 p hpn hpQ
  · intro hnot
    refine ⟨hn.ne', ?_⟩
    intro p hpn hpQ
    exact hnot ⟨p, hpn, hpQ⟩

@[simp] theorem gsDeletePrimeBand_apply
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    {n : ℕ} (hn : 0 < n) :
    gsDeletePrimeBand f Q n = if HasPrimeFactor Q n then 0 else f n := by
  unfold gsDeletePrimeBand primeBandCoefficient
  rw [primeSupported_compl_iff_not_hasPrimeFactor Q hn]
  by_cases hQ : HasPrimeFactor Q n <;> simp [hQ]

theorem gsDeletePrimeBand_isMultiplicativeOnPositiveNat
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (Q : ℕ → Prop) [DecidablePred Q] :
    IsMultiplicativeOnPositiveNat (gsDeletePrimeBand f Q) := by
  exact primeBandCoefficient_isMultiplicativeOnPositiveNat hmul _

theorem norm_gsDeletePrimeBand_le_one
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q]
    {n : ℕ} (hn : 0 < n) :
    ‖gsDeletePrimeBand f Q n‖ ≤ 1 := by
  exact norm_primeBandCoefficient_le_one hbound _ hn

/-- Source equation (A.3), in squared-distance form.  On a deleted prime the
new distance term is exactly `1/p`, which dominates half of the old term; on
an undeleted prime the terms agree. -/
theorem half_pretentiousDistSq_le_deletePrimeBand
    {f g : ℕ → ℂ}
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q] (X : ℕ) :
    pretentiousDistSq f g X / 2 ≤
      pretentiousDistSq (gsDeletePrimeBand f Q) g X := by
  unfold pretentiousDistSq
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hpX
  have hp : p.Prime := (mem_primesUpTo.mp hpX).1
  rw [show gsDeletePrimeBand f Q =
      primeBandCoefficient f (fun p ↦ ¬ Q p) by rfl,
    pretentiousTerm_primeBandCoefficient f g (fun p ↦ ¬ Q p) hp]
  by_cases hQ : Q p
  · rw [if_neg]
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
        pretentiousTerm_le_two_div (hf p hp) (hg p hp)
    · simpa using hQ
  · rw [if_pos hQ]
    have hnonneg := pretentiousTerm_nonneg (hf p hp) (hg p hp)
    linarith

theorem archimedeanNonpretentious_half_deletePrimeBand
    {f : ℕ → ℂ} {A X : ℕ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q]
    (hnonpret : MRArchimedeanNonpretentious f A X) :
    ∀ t : ℝ, |t| ≤ X →
      (A : ℝ) / 2 ≤
        pretentiousDistSq (gsDeletePrimeBand f Q) (archimedeanTwist t) X := by
  intro t ht
  refine (div_le_div_of_nonneg_right (hnonpret t ht) (by norm_num)).trans ?_
  exact half_pretentiousDistSq_le_deletePrimeBand
    (fun p hp ↦ hbound p hp.pos)
    (fun p hp ↦ by rw [norm_archimedeanTwist hp.pos]) Q X

theorem gsDeletePrimeBand_archimedeanUntwist
    (f : ℕ → ℂ) (Q : ℕ → Prop) [DecidablePred Q]
    (t : ℝ) :
    gsDeletePrimeBand (archimedeanUntwist f t) Q =
      archimedeanUntwist (gsDeletePrimeBand f Q) t := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [gsDeletePrimeBand, primeBandCoefficient, PrimeSupported,
      archimedeanUntwist]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [gsDeletePrimeBand_apply (archimedeanUntwist f t) Q hnpos]
  by_cases hQ : HasPrimeFactor Q n
  · simp only [archimedeanUntwist, if_neg hn]
    rw [gsDeletePrimeBand_apply f Q hnpos]
    simp [hQ]
  · simp only [archimedeanUntwist, if_neg hn]
    rw [gsDeletePrimeBand_apply f Q hnpos]
    simp [hQ]

/-- Delete both blocks at once. -/
def gsDeleteTwoPrimeBands
    (f : ℕ → ℂ) (Q₁ Q₂ : ℕ → Prop)
    [DecidablePred Q₁] [DecidablePred Q₂] : ℕ → ℂ :=
  gsDeletePrimeBand f (fun p ↦ Q₁ p ∨ Q₂ p)

theorem hasPrimeFactor_or_iff
    (Q₁ Q₂ : ℕ → Prop) [DecidablePred Q₁] [DecidablePred Q₂]
    (n : ℕ) :
    HasPrimeFactor (fun p ↦ Q₁ p ∨ Q₂ p) n ↔
      HasPrimeFactor Q₁ n ∨ HasPrimeFactor Q₂ n := by
  simp only [hasPrimeFactor_iff]
  constructor
  · rintro ⟨p, hpn, hp | hp⟩
    · exact Or.inl ⟨p, hpn, hp⟩
    · exact Or.inr ⟨p, hpn, hp⟩
  · rintro (⟨p, hpn, hp⟩ | ⟨p, hpn, hp⟩)
    · exact ⟨p, hpn, Or.inl hp⟩
    · exact ⟨p, hpn, Or.inr hp⟩

/-- The two-block finite-Halasz coefficient is the four-term
inclusion--exclusion combination of genuine multiplicative deletions. -/
theorem finiteHalaszTypicalCoefficient_eq_twoBlock_inclusionExclusion
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    {n : ℕ} (hn : 0 < n) :
    finiteHalaszTypicalCoefficient f P₁ P₂ n =
      f n -
        gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ P₂ p) n -
        gsDeletePrimeBand f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n +
        gsDeleteTwoPrimeBands f
          (fun p ↦ ¬ P₁ p ∧ P₂ p)
          (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n := by
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  have hdel₂ := gsDeletePrimeBand_apply f Q₂ hn
  have hdel₃ := gsDeletePrimeBand_apply f Q₃ hn
  have hdel₂₃ := gsDeletePrimeBand_apply f (fun p ↦ Q₂ p ∨ Q₃ p) hn
  change (if HasPrimeFactor Q₂ n ∧ HasPrimeFactor Q₃ n then f n else 0) = _
  change _ = f n - gsDeletePrimeBand f Q₂ n - gsDeletePrimeBand f Q₃ n +
    gsDeletePrimeBand f (fun p ↦ Q₂ p ∨ Q₃ p) n
  rw [hdel₂, hdel₃, hdel₂₃]
  by_cases h₂ : HasPrimeFactor Q₂ n <;>
    by_cases h₃ : HasPrimeFactor Q₃ n <;>
      simp [h₂, h₃, hasPrimeFactor_or_iff]

theorem finiteHalaszTypicalCoefficient_archimedeanUntwist
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    (t : ℝ) :
    finiteHalaszTypicalCoefficient (archimedeanUntwist f t) P₁ P₂ =
      archimedeanUntwist (finiteHalaszTypicalCoefficient f P₁ P₂) t := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp [finiteHalaszTypicalCoefficient, archimedeanUntwist]
  unfold finiteHalaszTypicalCoefficient
  rw [archimedeanUntwist, if_neg hn, archimedeanUntwist, if_neg hn]
  split_ifs <;> simp_all

end

end Erdos67.MRHalaszBands
