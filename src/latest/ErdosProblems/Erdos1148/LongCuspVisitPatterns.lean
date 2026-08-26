import ErdosProblems.Erdos1148.CuspVisitPatterns
import Mathlib.Data.Fintype.BigOperators

/-! # Counting cusp visit patterns in an arbitrary finite time window -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma mem_modularCuspVisitPattern_iff (H : ℝ) (n : ℕ) (x : ModularOrbitSpace) (i : Fin n) :
    i ∈ modularCuspVisitPattern H n x ↔
      modularRightTranslate (diagonalFlow (i.val : ℝ)) x ∈ modularCusp H := by
  classical
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))

lemma modularRightTranslate_diagonal_add (s t : ℝ) (x : ModularOrbitSpace) :
    modularRightTranslate (diagonalFlow t) (modularRightTranslate (diagonalFlow s) x) =
      modularRightTranslate (diagonalFlow (s + t)) x := by
  induction x using Quotient.inductionOn' with | h g =>
    change modularMk ((g * diagonalFlow s) * diagonalFlow t) =
      modularMk (g * diagonalFlow (s + t))
    rw [mul_assoc, ← diagonalFlow_add]

theorem exists_long_cusp_visit_patterns {H : ℝ} (hH : 0 < H) (m : ℕ) (hm : 0 < m)
    (hwindow : Real.exp (m : ℝ) ≤ H ^ 4) (n : ℕ) :
    ∃ P : Finset (Finset (Fin n)), P.card ≤ (m ^ 2 + 1) ^ (n / m + 1) ∧
      ∀ x : ModularOrbitSpace, modularCuspVisitPattern H n x ∈ P := by
  classical
  obtain ⟨Q, hQ, hpatterns⟩ := exists_cusp_visit_patterns hH m hwindow
  let ι := Fin (n / m + 1) → Q
  let block (i : Fin n) : Fin (n / m + 1) :=
    ⟨i.val / m, Nat.lt_succ_of_le (Nat.div_le_div_right i.isLt.le)⟩
  let offset (i : Fin n) : Fin m := ⟨i.val % m, Nat.mod_lt _ hm⟩
  let assemble : ι → Finset (Fin n) := fun f =>
    Finset.univ.filter (fun i => offset i ∈ (f (block i)).val)
  refine ⟨Finset.univ.image assemble, ?_, ?_⟩
  · calc
      _ ≤ (Finset.univ : Finset ι).card := Finset.card_image_le
      _ = Q.card ^ (n / m + 1) := by
        simp only [Finset.card_univ, ι, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
      _ ≤ (m ^ 2 + 1) ^ (n / m + 1) := Nat.pow_le_pow_left hQ _
  · intro x
    let f : ι := fun j => ⟨modularCuspVisitPattern H m
      (modularRightTranslate (diagonalFlow ((j.val * m : ℕ) : ℝ)) x), hpatterns _⟩
    apply Finset.mem_image.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    ext i
    change (i ∈ Finset.univ.filter (fun j => offset j ∈ (f (block j)).val)) ↔ _
    rw [Finset.mem_filter, and_iff_right (Finset.mem_univ i), mem_modularCuspVisitPattern_iff]
    rw [mem_modularCuspVisitPattern_iff, modularRightTranslate_diagonal_add]
    change modularRightTranslate
      (diagonalFlow ((((i.val / m) * m : ℕ) : ℝ) + (offset i).val)) x ∈ modularCusp H ↔ _
    have htime : (((i.val / m) * m : ℕ) : ℝ) + (offset i).val = (i.val : ℝ) := by
      dsimp only [offset]
      have hnat : (i.val / m) * m + i.val % m = i.val := by
        simpa only [Nat.mul_comm] using Nat.div_add_mod i.val m
      exact_mod_cast hnat
    rw [htime]

end Erdos1148.DukeArithmetic
