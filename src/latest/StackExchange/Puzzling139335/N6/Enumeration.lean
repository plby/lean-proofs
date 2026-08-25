import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Extending the three ordered corner owners to all four pieces
-/

namespace Puzzling139335.N6

/-- An injective ordered list of three of four indices extends to a
permutation, retaining those three entries exactly. -/
theorem extend_three_indices (f : Fin 3 → Fin 4) (hf : Function.Injective f) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = f 0 ∧ σ 1 = f 1 ∧ σ 2 = f 2 := by
  have hnot : ¬ Function.Surjective f := by
    intro hs
    have hcard := Fintype.card_le_of_surjective f hs
    norm_num at hcard
  simp only [Function.Surjective, not_forall, not_exists] at hnot
  obtain ⟨r, hr⟩ := hnot
  let g : Fin 4 → Fin 4 := ![f 0, f 1, f 2, r]
  have h01 : f 0 ≠ f 1 := hf.ne (by decide)
  have h02 : f 0 ≠ f 2 := hf.ne (by decide)
  have h12 : f 1 ≠ f 2 := hf.ne (by decide)
  have h0r := hr 0
  have h1r := hr 1
  have h2r := hr 2
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g]
    all_goals first | exact hr 0 rfl | exact hr 1 rfl | exact hr 2 rfl
  exact ⟨Equiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩, rfl, rfl, rfl⟩

/-- Two distinct specified indices extend to a permutation with those two
indices in the first two positions. -/
theorem extend_two_indices (i j : Fin 4) (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  let f : Fin 2 → Fin 4 := ![i, j]
  have hnot : ¬ Function.Surjective f := by
    intro hs
    have hcard := Fintype.card_le_of_surjective f hs
    norm_num at hcard
  simp only [Function.Surjective, not_forall, not_exists] at hnot
  obtain ⟨r, hr⟩ := hnot
  have hir : i ≠ r := by simpa only [f, Matrix.cons_val_zero] using hr 0
  have hjr : j ≠ r := by simpa only [f, Matrix.cons_val_one, Matrix.cons_val_zero] using hr 1
  let g : Fin 3 → Fin 4 := ![i, j, r]
  have hg : Function.Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [g]
  obtain ⟨σ, h0, h1, _⟩ := extend_three_indices g hg
  exact ⟨σ, h0, h1⟩

end Puzzling139335.N6
