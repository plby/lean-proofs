/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.Basic

/-!
# Erdős Problem 163: passage from Lee's large-order theorem to all orders

The deep argument naturally gives a linear bound only above a threshold.
This file proves, with no asymptotic notation, that finite Ramsey theory
absorbs all smaller target orders into the same constant.
-/

open Finset

namespace Erdos163

/-- Qualitative form of the large-order conclusion supplied by Lee's proof. -/
def LargeOrderDegenerateRamsey : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∃ C n₀ : ℕ, 1 ≤ C ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ H : SimpleGraph (Fin n),
        IsDegenerateAtMost H d → RamseyFor H (C * n)

theorem ramseyFor_zero (H : SimpleGraph (Fin 0)) : RamseyFor H 0 := by
  intro G
  left
  exact ⟨{
    toFun := id
    injective' := Function.injective_id
    map_adj' := fun {x _} _ => Fin.elim0 x
  }⟩

/-- The finite exceptional orders can be absorbed into one multiplicative constant. -/
theorem erdos_163_of_large_order (hlarge : LargeOrderDegenerateRamsey) :
    ∀ d : ℕ, 1 ≤ d →
      ∃ C : ℕ, 1 ≤ C ∧
        ∀ n : ℕ, ∀ H : SimpleGraph (Fin n),
          IsDegenerateAtMost H d → RamseyFor H (C * n) := by
  intro d hd
  obtain ⟨C₀, n₀, hC₀, hlarge_d⟩ := hlarge d hd
  let S : ℕ := (range n₀).sup fun n => Ramsey.ramseyNumber n n
  let C := max C₀ S
  refine ⟨C, hC₀.trans (le_max_left _ _), ?_⟩
  intro n H hdeg
  by_cases hnlarge : n₀ ≤ n
  · have hC₀C : C₀ ≤ C := le_max_left _ _
    have hbase := hlarge_d n hnlarge H hdeg
    intro G
    let f : Fin (C₀ * n) ↪ Fin (C * n) :=
      Fin.castLEEmb (Nat.mul_le_mul_right n hC₀C)
    rcases hbase (G.comap f) with hred | hblue
    · left
      rcases hred with ⟨e⟩
      exact ⟨{
        toFun := f ∘ e
        injective' := f.injective.comp e.injective'
        map_adj' := fun {_ _} h => by
          exact e.map_adj' h
      }⟩
    · right
      rcases hblue with ⟨e⟩
      exact ⟨{
        toFun := f ∘ e
        injective' := f.injective.comp e.injective'
        map_adj' := fun {_ _} h => by
          simpa [SimpleGraph.compl_adj] using e.map_adj' h
      }⟩
  · have hnsmall : n < n₀ := Nat.lt_of_not_ge hnlarge
    by_cases hnzero : n = 0
    · subst n
      simpa using ramseyFor_zero H
    · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hnzero
      have hRS : Ramsey.ramseyNumber n n ≤ S := by
        exact Finset.le_sup (f := fun m => Ramsey.ramseyNumber m m)
          (Finset.mem_range.mpr hnsmall)
      have hSC : S ≤ C := le_max_right _ _
      have hCn : C ≤ C * n := by
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left C hnpos
      have hRN : Ramsey.ramseyNumber n n ≤ C * n := hRS.trans (hSC.trans hCn)
      exact ramseyFor_of_ramseyProperty H
        (Ramsey.ramseyProperty_mono_vertices hRN (Ramsey.ramseyNumber_spec n n))

end Erdos163
