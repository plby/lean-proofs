import ErdosProblems.Erdos67.StationaryEntropyBudget
import ErdosProblems.Erdos67.StationaryConcentration

/-!
# The finite prime-block entropy estimate

The result below applies the proved concentration estimate to a joint law of a
sign block, a residue block, and previous residue information. Independence and
the conditional-pair identities are explicit hypotheses of this finite lemma;
they must be obtained from the stationary model when proving discrepancy.
-/

open scoped BigOperators
open Finset

namespace Erdos67.StationaryConcentration

variable {ι α γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype γ]

/-- The centered residue indicator appearing in the dilation identity. -/
noncomputable def centeredResidueFactor (p : ℕ) (y : ZMod p) (j : ℕ) : ℝ :=
  if y = -((j : ZMod p) + 1) then (p : ℝ) - 1 else -1

theorem centeredResidueFactor_succ (p : ℕ) (y : ZMod p) (j : ℕ) :
    centeredResidueFactor p y j =
      if y = -((j + 1 : ℕ) : ZMod p) then (p : ℝ) - 1 else -1 := by
  simp only [centeredResidueFactor, Nat.cast_add, Nat.cast_one]

theorem residueObservable_eq_centered (L p : ℕ) (a : Fin L → ℝ) (y : ZMod p) :
    residueObservable L p a y =
      (∑ j, a j * centeredResidueFactor p y j.val) / L := by
  classical
  unfold residueObservable
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold centeredResidueFactor
  split_ifs <;> ring

variable {L : ℕ} (p : ι → ℕ) [∀ i, NeZero (p i)]

/-- The unnormalized sum over the residue block. -/
noncomputable def residueBlockObservable (a : α → ι → Fin L → ℝ) (δ : ι → ℝ)
    (x : α) (y : ∀ i, ZMod (p i)) : ℝ :=
  ∑ i, δ i * residueObservable L (p i) (a x i) (y i)

theorem mean_residueObservable_of_centered_pairs
    (P : FiniteEntropy.FinProb ((α × (∀ i, ZMod (p i))) × γ))
    (hL : 0 < L) (a : α → ι → Fin L → ℝ) (δ : ι → ℝ)
    (hpair : ∀ i j, (∑ z, P z * (a z.1.1 i j *
      centeredResidueFactor (p i) (z.1.2 i) j.val)) = δ i) (i : ι) :
    (∑ z, P z * residueObservable L (p i) (a z.1.1 i) (z.1.2 i)) = δ i := by
  simp_rw [residueObservable_eq_centered, ← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [hpair]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ (δ i) (Nat.cast_ne_zero.mpr hL.ne')

theorem mean_residueBlockObservable_eq_square_error
    (P : FiniteEntropy.FinProb ((α × (∀ i, ZMod (p i))) × γ))
    (hL : 0 < L) (a : α → ι → Fin L → ℝ) (δ : ι → ℝ)
    (hpair : ∀ i j, (∑ z, P z * (a z.1.1 i j *
      centeredResidueFactor (p i) (z.1.2 i) j.val)) = δ i) :
    (∑ z, P z * residueBlockObservable p a δ z.1.1 z.1.2) = ∑ i, δ i ^ 2 := by
  simp only [residueBlockObservable, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_left_comm (P _) (δ i)]
  rw [← Finset.mul_sum, mean_residueObservable_of_centered_pairs p P hL a δ hpair]
  ring

theorem conditional_residue_marginal_uniform
    (P : FiniteEntropy.FinProb ((α × (∀ i, ZMod (p i))) × γ))
    (hindep : FiniteEntropy.mapLeft P Prod.snd =
      FiniteEntropy.product FiniteEntropy.uniformVector (FiniteEntropy.sndMarginal P))
    (c : γ) :
    FiniteEntropy.sndMarginal (FiniteEntropy.conditionalLaw P c) =
      FiniteEntropy.uniformVector := by
  rw [← FiniteEntropy.conditionalLaw_map_snd, hindep,
    FiniteEntropy.conditionalLaw_product]

/-- One dyadic residue block costs at most eighteen times its conditional mutual
information. Primality is unnecessary for this finite step; only the displayed
independence and conditional-pair identities are used. -/
theorem square_error_le_eighteen_information
    (P : FiniteEntropy.FinProb ((α × (∀ i, ZMod (p i))) × γ))
    (hL : 0 < L) (hLp : ∀ i, L ≤ p i) (hpL : ∀ i, p i ≤ 2 * L)
    (a : α → ι → Fin L → ℝ) (ha : ∀ x i j, |a x i j| ≤ 1) (δ : ι → ℝ)
    (hindep : FiniteEntropy.mapLeft P Prod.snd =
      FiniteEntropy.product FiniteEntropy.uniformVector (FiniteEntropy.sndMarginal P))
    (hpair : ∀ i j, (∑ z, P z * (a z.1.1 i j *
      centeredResidueFactor (p i) (z.1.2 i) j.val)) = δ i) :
    (∑ i, δ i ^ 2) ≤ 18 * FiniteEntropy.conditionalMutualInfo P := by
  apply FiniteEntropy.square_error_le_eighteen_conditionalMutualInfo P
    (fun x y _ ↦ residueBlockObservable p a δ x y) (∑ i, δ i ^ 2)
  · exact mean_residueBlockObservable_eq_square_error p P hL a δ hpair
  · intro c _ x
    rw [conditional_residue_marginal_uniform p P hindep c]
    have h := uniform_mgf_residue_block_le p hL hLp hpL (a x) (ha x) δ (1 / 9)
    have heq : (9 / 2 : ℝ) * (1 / 9) ^ 2 * (∑ i, δ i ^ 2) =
        (∑ i, δ i ^ 2) / 18 := by ring
    simpa only [residueBlockObservable, one_div_mul_eq_div, heq] using h

end Erdos67.StationaryConcentration
