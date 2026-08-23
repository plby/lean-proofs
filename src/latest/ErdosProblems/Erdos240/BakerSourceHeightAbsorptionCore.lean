/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerParameters

/-!
# Fixed-family height absorption: elementary core

This module contains only the real inequalities needed to turn the source
exponent `C₀ Ω' log Ω' log Aₙ log N` into
`C(old) log p log N`.  It is deliberately independent of the Kummer,
auxiliary-function, and extrapolation layers.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceHeightAbsorption

open Erdos240

universe u v

/-- The strict source height attached to one fixed rational prime. -/
def normalizedPrimeHeight (p : ℕ) : ℝ :=
  max (Real.exp (Real.exp 1)) ((p : ℝ) + 1)

/-- Product of the fixed old heights, with no varying-prime argument. -/
def oldFamilyHeightProduct {ι : Type u} [Fintype ι]
    (old : ι → ℕ) : ℝ :=
  ∏ i, normalizedPrimeHeight (old i)

/-- Enumerating the fixed old family by an equivalent finite type does not
change its product of normalized heights. -/
theorem oldFamilyHeightProduct_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (old : ι → ℕ) :
    oldFamilyHeightProduct (old ∘ e) = oldFamilyHeightProduct old := by
  unfold oldFamilyHeightProduct
  exact Fintype.prod_equiv e
    (fun j ↦ normalizedPrimeHeight (old (e j)))
    (fun i ↦ normalizedPrimeHeight (old i)) (fun _ ↦ rfl)

/-- The fixed height-absorption constant used in `BakerParameters`. -/
def oldFamilyHeightConstant {ι : Type u} [Fintype ι]
    (old : ι → ℕ) : ℝ :=
  4 + Real.log (oldFamilyHeightProduct old) / Real.log 2

theorem one_le_oldFamilyHeightProduct {ι : Type u} [Fintype ι]
    (old : ι → ℕ) : 1 ≤ oldFamilyHeightProduct old := by
  unfold oldFamilyHeightProduct
  apply Finset.one_le_prod
  intro i _hi
  have hone : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (Real.exp 1) :=
        Real.exp_le_exp.mpr (Real.exp_pos 1).le
  exact hone.trans (le_max_left _ _)

theorem oldFamilyHeightConstant_pos {ι : Type u} [Fintype ι]
    (old : ι → ℕ) : 0 < oldFamilyHeightConstant old := by
  unfold oldFamilyHeightConstant
  have hlog : 0 ≤ Real.log (oldFamilyHeightProduct old) :=
    Real.log_nonneg (one_le_oldFamilyHeightProduct old)
  have hlogTwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  positivity

theorem heightConstant_eq_oldFamilyHeightConstant
    {ι : Type u} [Fintype ι] (P : VDPLParameters ι) :
    P.heightConstant = oldFamilyHeightConstant P.old := by
  rfl

/-- Product of the logarithmic fixed heights, written without any varying
prime parameter. -/
def oldFamilyOmega {ι : Type u} [Fintype ι] (old : ι → ℕ) : ℝ :=
  ∏ i, Real.log (normalizedPrimeHeight (old i))

/-- The source product `Ω'` is likewise invariant under finite
reindexing. -/
theorem oldFamilyOmega_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (old : ι → ℕ) :
    oldFamilyOmega (old ∘ e) = oldFamilyOmega old := by
  unfold oldFamilyOmega
  exact Fintype.prod_equiv e
    (fun j ↦ Real.log (normalizedPrimeHeight (old (e j))))
    (fun i ↦ Real.log (normalizedPrimeHeight (old i))) (fun _ ↦ rfl)

theorem omegaOld_eq_oldFamilyOmega {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) :
    P.OmegaOld = oldFamilyOmega P.old := by
  rfl

theorem oldFamilyOmega_pos {ι : Type u} [Fintype ι]
    (old : ι → ℕ) : 0 < oldFamilyOmega old := by
  unfold oldFamilyOmega normalizedPrimeHeight
  apply Finset.prod_pos
  intro i _hi
  apply Real.log_pos
  have he : 1 < Real.exp (Real.exp 1) := by
    calc
      (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp (Real.exp 1) :=
        Real.exp_lt_exp.mpr (Real.exp_pos 1)
  exact he.trans_le (le_max_left _ _)

theorem oldFamilyOmega_log_pos {ι : Type u} [Fintype ι] [Nonempty ι]
    (old : ι → ℕ) : 0 < Real.log (oldFamilyOmega old) := by
  have hfactor : ∀ i : ι, Real.exp 1 ≤
      Real.log (normalizedPrimeHeight (old i)) := by
    intro i
    rw [← Real.log_exp (Real.exp 1)]
    apply Real.strictMonoOn_log.monotoneOn
    · exact Real.exp_pos (Real.exp 1)
    · exact (Real.exp_pos (Real.exp 1)).trans_le
        (le_max_left _ _)
    · exact le_max_left _ _
  have homega : Real.exp 1 ≤ oldFamilyOmega old := by
    classical
    obtain ⟨i⟩ := ‹Nonempty ι›
    calc
      Real.exp 1 ≤ Real.log (normalizedPrimeHeight (old i)) := hfactor i
      _ ≤ ∏ j, Real.log (normalizedPrimeHeight (old j)) := by
        have hprod := Finset.prod_le_prod_of_subset_of_one_le
          (s := {i}) (t := Finset.univ)
          (f := fun j ↦ Real.log (normalizedPrimeHeight (old j)))
          (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
          (fun j _hj ↦ (Real.exp_pos 1).le.trans (hfactor j))
          (fun j _hj _hne ↦
            (Real.one_le_exp (by norm_num)).trans (hfactor j))
        simpa using hprod
      _ = oldFamilyOmega old := rfl
  apply Real.log_pos
  have honeExp : (1 : ℝ) < Real.exp 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  exact honeExp.trans_le homega

/-- A fixed-family multiplier which visibly has no varying-prime argument. -/
def oldFamilySourceMultiplier {ι : Type u} [Fintype ι]
    (old : ι → ℕ) : ℝ :=
  oldFamilyOmega old * Real.log (oldFamilyOmega old) *
    oldFamilyHeightConstant old

/-- The final absorbed multiplier depends only on the family itself, not on
the finite indexing type used by the concrete source argument. -/
theorem oldFamilySourceMultiplier_comp_equiv
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (old : ι → ℕ) :
    oldFamilySourceMultiplier (old ∘ e) =
      oldFamilySourceMultiplier old := by
  unfold oldFamilySourceMultiplier oldFamilyHeightConstant
  rw [oldFamilyOmega_comp_equiv e old,
    oldFamilyHeightProduct_comp_equiv e old]

theorem oldFamilySourceMultiplier_pos {ι : Type u} [Fintype ι]
    [Nonempty ι] (old : ι → ℕ) :
    0 < oldFamilySourceMultiplier old := by
  unfold oldFamilySourceMultiplier
  exact mul_pos
    (mul_pos (oldFamilyOmega_pos old) (oldFamilyOmega_log_pos old))
    (oldFamilyHeightConstant_pos old)

/-- The complete elementary inequality absorbing the varying last height.
All data on the right other than `log(newPrime)` and `logN` depend only on
the fixed old family. -/
theorem sourceExponent_le_absorbedExponent
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) {C₀ logN : ℝ}
    (hC₀ : 0 ≤ C₀) (hlogN : 0 ≤ logN) :
    C₀ * P.OmegaOld * Real.log P.OmegaOld * Real.log P.newHeight * logN ≤
      (C₀ * oldFamilySourceMultiplier P.old) *
        Real.log (P.newPrime : ℝ) * logN := by
  have hheight : Real.log P.newHeight ≤
      oldFamilyHeightConstant P.old * Real.log (P.newPrime : ℝ) := by
    rw [← heightConstant_eq_oldFamilyHeightConstant P]
    exact P.log_newHeight_le_heightConstant_mul_log_newPrime
  rw [omegaOld_eq_oldFamilyOmega P]
  unfold oldFamilySourceMultiplier
  have hfixed : 0 ≤
      C₀ * oldFamilyOmega P.old * Real.log (oldFamilyOmega P.old) := by
    exact mul_nonneg
      (mul_nonneg hC₀ (oldFamilyOmega_pos P.old).le)
      (oldFamilyOmega_log_pos P.old).le
  calc
    C₀ * oldFamilyOmega P.old * Real.log (oldFamilyOmega P.old) *
          Real.log P.newHeight * logN ≤
        C₀ * oldFamilyOmega P.old * Real.log (oldFamilyOmega P.old) *
          (oldFamilyHeightConstant P.old * Real.log (P.newPrime : ℝ)) *
            logN := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hheight hfixed) hlogN
    _ = (C₀ *
          (oldFamilyOmega P.old * Real.log (oldFamilyOmega P.old) *
            oldFamilyHeightConstant P.old)) *
          Real.log (P.newPrime : ℝ) * logN := by ring

#print axioms
  Erdos240.BakerSourceHeightAbsorption.sourceExponent_le_absorbedExponent

end Erdos240.BakerSourceHeightAbsorption
