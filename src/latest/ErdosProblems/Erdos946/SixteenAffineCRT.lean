/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SixteenAffineCongruences

open scoped ArithmeticFunction.sigma ArithmeticFunction.Omega

namespace Erdos946.SixteenAffine

open Erdos946.SixteenKey

/-- Existence of the simultaneous CRT representative.  The local subtype
keeps Mathlib's proof field available without unfolding its computed value. -/
lemma exists_affineCRT16Base : ∃ x : ℕ, ∀ i : Fin 16,
    x ≡ keyCongruence16Residue i [MOD (keyPower16 i) ^ 2] := by
  let s := Nat.chineseRemainderOfFinset keyCongruence16Residue
    (fun i : Fin 16 => (keyPower16 i) ^ 2) Finset.univ
    (by intro i _; exact keyPower16Sq_ne_zero i)
    keyPower16Sq_pairwise_coprime
  exact ⟨s, fun i => s.property i (Finset.mem_univ i)⟩

/-- The natural-number value selected from the CRT existence theorem. -/
noncomputable def affineCRT16Base : ℕ :=
  Classical.choose exists_affineCRT16Base

/-- Product of the sixteen pairwise-coprime CRT moduli. -/
noncomputable def affineCRT16Modulus : ℕ :=
  ∏ i : Fin 16, (keyPower16 i) ^ 2

/-- A strictly positive representative of the simultaneous CRT class. -/
noncomputable def affineCRT16Parameter : ℕ :=
  affineCRT16Base + affineCRT16Modulus


lemma affineCRT16Base_modEq (i : Fin 16) :
    affineCRT16Base ≡ keyCongruence16Residue i [MOD (keyPower16 i) ^ 2] := by
  exact Classical.choose_spec exists_affineCRT16Base i


lemma affineCRT16Parameter_modEq (i : Fin 16) :
    affineCRT16Parameter ≡ keyCongruence16Residue i
      [MOD (keyPower16 i) ^ 2] := by
  have hdiv : (keyPower16 i) ^ 2 ∣ affineCRT16Modulus := by
    exact Finset.dvd_prod_of_mem (f := fun j : Fin 16 => (keyPower16 j) ^ 2)
      (Finset.mem_univ i)
  have hzero : affineCRT16Modulus ≡ 0 [MOD (keyPower16 i) ^ 2] :=
    Nat.modEq_zero_iff_dvd.mpr hdiv
  simpa [affineCRT16Parameter] using (affineCRT16Base_modEq i).add hzero


lemma affineCRT16_congruence (i : Fin 16) :
    keyCongruence16Coefficient i * affineCRT16Parameter + 1 ≡ keyPower16 i
      [MOD (keyPower16 i) ^ 2] := by
  have hmul := (affineCRT16Parameter_modEq i).mul_left
    (keyCongruence16Coefficient i)
  have h := hmul.trans (keyCongruence16Residue_spec i)
  have hadd := h.add_right 1
  simpa [Nat.sub_add_cancel (show 1 ≤ keyPower16 i by
    exact (keyPower16_gt_one i).le)] using hadd


end Erdos946.SixteenAffine
