/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 83.
https://www.erdosproblems.com/forum/thread/83

Informal authors:
- Rudolf Ahlswede
- Levon H. Khachatrian

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos83.md
-/
import ErdosProblems.Erdos83.Extremal
import ErdosProblems.Erdos83.DualLayers

/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-!
# Erdős Problem 83

Ahlswede and Khachatrian proved the sharp bound for a family of `2 * q`-subsets
of a `4 * q`-set whose members pairwise meet in at least two points.  The proof
below uses the specialized pushing--pulling argument formalized in the helper
modules under `ErdosProblems/Erdos83/`.
-/

namespace Erdos83

open Finset

/-- Erdős Problem 83: the sharp bound for two-intersecting middle-layer
families on a `4 * q`-point set. -/
theorem erdos_83 (q : ℕ) (F : Finset (Finset (Fin (4 * q))))
    (hunif : Uniform (2 * q) F) (hinter : TwoIntersecting F) :
    F.card ≤
      (Nat.choose (4 * q) (2 * q) - Nat.choose (2 * q) q ^ 2) / 2 := by
  by_cases hq0 : q = 0
  · subst q
    have hF : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      have hcard := hunif hA
      have hmeet := hinter hA hA
      rw [Finset.inter_self, hcard] at hmeet
      omega
    simp [hF]
  by_cases hq1 : q = 1
  · subst q
    have hcardle : F.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro A hA B hB
      have hmeet := hinter hA hB
      have hAcard := hunif hA
      have hBcard := hunif hB
      have hIA : A ∩ B = A :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have hIB : A ∩ B = B :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
      exact hIA.symm.trans hIB
    norm_num at hcardle ⊢
    exact hcardle
  have hq : 2 ≤ q := by omega
  obtain ⟨Fmax, hmaxUnif, hmaxInter, hmax, hmaxLeft⟩ :=
    exists_extremal_leftCompressed (4 * q) (2 * q)
  calc
    F.card ≤ Fmax.card := hmax F hunif hinter
    _ ≤ (majorityFamily q).card :=
      extremal_card_le_majority hq hmaxUnif hmaxInter hmax hmaxLeft
    _ = (Nat.choose (4 * q) (2 * q) - Nat.choose (2 * q) q ^ 2) / 2 :=
      card_majorityFamily q

end Erdos83

#print axioms Erdos83.erdos_83
