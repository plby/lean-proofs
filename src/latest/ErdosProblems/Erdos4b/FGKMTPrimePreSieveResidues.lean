/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPreSieveNormalization
import Mathlib.Data.ZMod.Basic

/-!
# Literal presieve conditions on prime-variable residues

The variable residue is required to be a unit. All original integer
forms and their signs are retained, including negative shift differences.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem isUnit_intCast_iff_natAbs_coprime (W : ℕ) (n : ℤ) :
    IsUnit (n : ZMod W) ↔ n.natAbs.Coprime W := by
  cases n with
  | ofNat n => simpa using ZMod.isUnit_iff_coprime n W
  | negSucc n =>
      have hcast : ((Int.negSucc n : ℤ) : ZMod W) = -((n + 1 : ℕ) : ZMod W) := by
        push_cast
        ring
      rw [hcast, IsUnit.neg_iff, ZMod.isUnit_iff_coprime]
      simp

theorem preSieveCondition_iff_isUnit (W : ℕ) (a : ι → ℤ) (n : ℤ) :
    preSieveCondition W a n ↔ ∀ i, IsUnit ((n : ZMod W) + (a i : ZMod W)) := by
  simp only [preSieveCondition, Nat.coprime_fintype_prod_left_iff,
    ← isUnit_intCast_iff_natAbs_coprime, Int.cast_add]

def primePreSieveCondition (W Q : ℕ) (a : ι → ℤ) (j : ι) (P : ℕ) : Prop :=
  P.Coprime W ∧ (∏ i, ((Q : ℤ) - a j * P + a i * P).natAbs).Coprime W

open scoped Classical in
def primePreSieveResidues (W Q : ℕ) (a : ι → ℤ) (j : ι) : Finset ℕ :=
  (Finset.range W).filter (primePreSieveCondition W Q a j)

theorem mem_primePreSieveResidues_iff {W Q v : ℕ} {a : ι → ℤ} {j : ι} :
    v ∈ primePreSieveResidues W Q a j ↔ v < W ∧ primePreSieveCondition W Q a j v := by
  classical
  simp only [primePreSieveResidues, Finset.mem_filter, Finset.mem_range]

theorem primePreSieveCondition_iff_isUnit (W Q P : ℕ) (a : ι → ℤ) (j : ι) :
    primePreSieveCondition W Q a j P ↔ IsUnit (P : ZMod W) ∧
      ∀ i, IsUnit ((Q : ZMod W) + ((a i : ZMod W) - a j) * (P : ZMod W)) := by
  unfold primePreSieveCondition
  rw [Nat.coprime_fintype_prod_left_iff, ← ZMod.isUnit_iff_coprime P W]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro i
  rw [← isUnit_intCast_iff_natAbs_coprime]
  have hform : (((Q : ℤ) - a j * P + a i * P : ℤ) : ZMod W) =
      (Q : ZMod W) + ((a i : ZMod W) - a j) * P := by
    push_cast
    ring
  rw [hform]

theorem primePreSieveCondition_iff_of_modEq {W Q P v : ℕ}
    (a : ι → ℤ) (j : ι) (h : P ≡ v [MOD W]) :
    primePreSieveCondition W Q a j P ↔ primePreSieveCondition W Q a j v := by
  rw [primePreSieveCondition_iff_isUnit, primePreSieveCondition_iff_isUnit,
    (ZMod.natCast_eq_natCast_iff P v W).mpr h]

open scoped Classical in
theorem sum_primePreSieve_residue_indicator {W : ℕ} (hW : 0 < W) (Q : ℕ)
    (a : ι → ℤ) (j : ι) (P : ℕ) (b : ℝ) :
    (∑ v ∈ primePreSieveResidues W Q a j, if P ≡ v [MOD W] then b else 0) =
      if primePreSieveCondition W Q a j P then b else 0 := by
  classical
  let v := P % W
  have hv : v < W := Nat.mod_lt _ hW
  have hPv : P ≡ v [MOD W] := (Nat.mod_modEq P W).symm
  have huniq (u : ℕ) (hu : u < W) (hPu : P ≡ u [MOD W]) : u = v :=
    (hPu.symm.trans hPv).eq_of_lt_of_lt hu hv
  by_cases hgood : primePreSieveCondition W Q a j P
  · rw [if_pos hgood]
    have hmem : v ∈ primePreSieveResidues W Q a j :=
      mem_primePreSieveResidues_iff.mpr
        ⟨hv, (primePreSieveCondition_iff_of_modEq a j hPv).mp hgood⟩
    rw [Finset.sum_eq_single_of_mem v hmem, if_pos hPv]
    intro u hu huv
    exact if_neg (fun hPu => huv (huniq u (mem_primePreSieveResidues_iff.mp hu).1 hPu))
  · rw [if_neg hgood]
    apply Finset.sum_eq_zero
    intro u hu
    exact if_neg (fun hPu => hgood ((primePreSieveCondition_iff_of_modEq a j hPu).mpr
      (mem_primePreSieveResidues_iff.mp hu).2))

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.primePreSieveCondition_iff_isUnit
#print axioms Erdos4b.FGKMT.sum_primePreSieve_residue_indicator
