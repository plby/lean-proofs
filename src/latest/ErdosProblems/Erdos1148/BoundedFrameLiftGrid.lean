import ErdosProblems.Erdos1148.EntryDifferenceCloseness
import ErdosProblems.Erdos1148.LiftForwardClose
import ErdosProblems.Erdos1148.RealIntervalGrid

/-! # A polynomially sized coherent cover of bounded matrix frames -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def boundedEntryFrames (A : ℝ) : Set SL(2, ℝ) := {g | ∀ i j : Fin 2, |g i j| ≤ A}

theorem exists_bounded_frame_lift_grid {A η : ℝ} (hA : 0 ≤ A) (hη : 0 < η) :
    ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      (N : ℝ) ≤ (4 / η + 1) ^ 4 * (A + 1) ^ 8 ∧
      (⋃ i, B i) = boundedEntryFrames A ∧ ∀ i, LiftForwardClose η 0 (B i) := by
  classical
  let δ := η / (2 * (A + 1))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hscale : 2 * A * δ ≤ η := by
    dsimp only [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 2 * (A + 1) by positivity)).mpr
    nlinarith
  obtain ⟨m, a, hm, _, hcov⟩ := exists_real_interval_grid (a := -A) (b := A) (by linarith) hδ
  have hm' : (m : ℝ) ≤ (4 / η + 1) * (A + 1) ^ 2 := by
    have heq : (A - -A) / δ = (4 / η) * (A * (A + 1)) := by
      dsimp only [δ]
      field_simp
      <;> ring
    rw [heq] at hm
    have hpoly : A * (A + 1) ≤ (A + 1) ^ 2 := by nlinarith
    have hunit : (1 : ℝ) ≤ (A + 1) ^ 2 := by nlinarith [sq_nonneg A]
    calc
      _ ≤ (4 / η) * (A * (A + 1)) + 1 := hm
      _ ≤ (4 / η) * (A + 1) ^ 2 + (A + 1) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hpoly (by positivity)) hunit
      _ = _ := by ring
  let ι := (Fin 2 × Fin 2) → Fin m
  let B : ι → Set SL(2, ℝ) := fun k => boundedEntryFrames A ∩
    {g | ∀ i j : Fin 2, g i j ∈ Set.Icc (a (k (i, j))) (a (k (i, j)) + δ)}
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => B (e.symm k), ?_, ?_, ?_⟩
  · have hcard : (Fintype.card ι : ℝ) = (m : ℝ) ^ 4 := by
      simp only [ι, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Nat.cast_pow]
    rw [hcard]
    calc
      _ ≤ ((4 / η + 1) * (A + 1) ^ 2) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hm' 4
      _ = _ := by rw [mul_pow, ← pow_mul]
  · apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
      exact hk.1
    · intro g hg
      have hgrid (ij : Fin 2 × Fin 2) : ∃ k : Fin m,
          g ij.1 ij.2 ∈ Set.Icc (a k) (a k + δ) := hcov _ (abs_le.mp (hg ij.1 ij.2))
      choose k hk using hgrid
      refine Set.mem_iUnion.mpr ⟨e k, ?_⟩
      have he : e.symm (e k) = k := e.symm_apply_apply _
      rw [he]
      exact ⟨hg, fun i j => hk (i, j)⟩
  · intro k g hg h hh t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    rw [ht0, diagonalFlow_zero, mul_one, mul_one]
    apply entryCloseOne_of_entry_differences hA hδ.le hscale g h hg.1
    intro i j
    exact abs_sub_le_of_mem_same_interval (hh.2 i j) (hg.2 i j)

end Erdos1148.DukeArithmetic
