import ErdosProblems.Erdos1148.ShrinkingBowenCover

/-! # Uniform radius refinement of a finite family of coherent lift pieces -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups BigOperators

theorem exists_shrunk_finite_lift_cover {η δ S : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 2) (hδ : 0 < δ) (hS : 0 ≤ S)
    {N : ℕ} (B : Fin N → Set SL(2, ℝ)) (hB : ∀ i, LiftForwardClose η S (B i)) :
    ∃ (M : ℕ) (C : Fin M → Set SL(2, ℝ)),
      (M : ℝ) ≤ (N : ℝ) * (32 * η / δ + 1) ^ 3 ∧ (∀ j, IsCompact (C j)) ∧
      (⋃ i, B i) ⊆ ⋃ j, C j ∧ ∀ j, LiftForwardClose δ S (C j) := by
  classical
  have hex (i : Fin N) := exists_shrunk_lift_cover hη hηsmall hδ hS (B i) (hB i)
  choose n D hn hD hcov hclose using hex
  let ι := (i : Fin N) × Fin (n i)
  let e := Fintype.equivFin ι
  let C : Fin (Fintype.card ι) → Set SL(2, ℝ) := fun j => D (e.symm j).1 (e.symm j).2
  refine ⟨Fintype.card ι, C, ?_, ?_, ?_, ?_⟩
  · change (Fintype.card ((i : Fin N) × Fin (n i)) : ℝ) ≤ _
    simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      ∑ i : Fin N, (n i : ℝ) ≤ ∑ _i : Fin N, (32 * η / δ + 1) ^ 3 :=
        Finset.sum_le_sum fun i _ => hn i
      _ = _ := by simp
  · intro j
    exact hD (e.symm j).1 (e.symm j).2
  · intro g hg
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov i hi)
    refine Set.mem_iUnion.mpr ⟨e ⟨i, j⟩, ?_⟩
    change g ∈ D (e.symm (e ⟨i, j⟩)).1 (e.symm (e ⟨i, j⟩)).2
    have he : e.symm (e (⟨i, j⟩ : ι)) = ⟨i, j⟩ := e.symm_apply_apply _
    rw [he]
    exact hj
  · intro j
    exact hclose (e.symm j).1 (e.symm j).2

end Erdos1148.DukeArithmetic
