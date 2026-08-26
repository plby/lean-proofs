import ErdosProblems.Erdos1148.FiniteLiftCoverComposition

/-! # Combining finitely many coherent lift covers -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem LiftCoverBound.iUnion {η T K : ℝ} {ι : Type*} [Fintype ι]
    (E : ι → Set SL(2, ℝ)) (hE : ∀ i, LiftCoverBound η T (E i) K) :
    LiftCoverBound η T (⋃ i, E i) ((Fintype.card ι : ℝ) * K) := by
  classical
  choose n C hn hC hclose using hE
  let σ := (i : ι) × Fin (n i)
  let e := Fintype.equivFin σ
  let B : Fin (Fintype.card σ) → Set SL(2, ℝ) := fun j => C (e.symm j).1 (e.symm j).2
  refine ⟨Fintype.card σ, B, ?_, ?_, ?_⟩
  · change (Fintype.card ((i : ι) × Fin (n i)) : ℝ) ≤ _
    simp only [Fintype.card_sigma, Fintype.card_fin, Nat.cast_sum]
    calc
      _ ≤ ∑ _i : ι, K := Finset.sum_le_sum (fun i _ => hn i)
      _ = _ := by simp
  · apply Set.Subset.antisymm
    · intro g hg
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hg
      apply Set.mem_iUnion.mpr
      refine ⟨(e.symm j).1, ?_⟩
      rw [← hC (e.symm j).1]
      exact Set.mem_iUnion.mpr ⟨(e.symm j).2, hj⟩
    · intro g hg
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hg
      rw [← hC i] at hi
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
      refine Set.mem_iUnion.mpr ⟨e ⟨i, j⟩, ?_⟩
      change g ∈ C (e.symm (e ⟨i, j⟩)).1 (e.symm (e ⟨i, j⟩)).2
      have he : e.symm (e ⟨i, j⟩) = ⟨i, j⟩ := e.symm_apply_apply _
      rw [he]
      exact hj
  · intro j
    exact hclose (e.symm j).1 (e.symm j).2

end Erdos1148.DukeArithmetic
