import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card

/-! # Indexing a palette with its exceptional color first -/

namespace Erdos19

open Finset

theorem exists_distinguished_palette_index {C : Type*} [DecidableEq C]
    (S : Finset C) (bad : C) (hbad : bad ∈ S) :
    ∃ p : ℕ, ∃ index : Unit ⊕ Fin p ↪ C,
      p + 1 = S.card ∧ index (Sum.inl ()) = bad ∧
      (∀ x, index x ∈ S) ∧ (∀ i, index (Sum.inr i) ≠ bad) ∧
      ∀ c ∈ S, ∃ x, index x = c := by
  classical
  let P := S.erase bad
  let p := Fintype.card P
  let e : P ≃ Fin p := Fintype.equivFin P
  let good : Fin p → C := fun i ↦ (e.symm i).1
  have hgood (i : Fin p) : good i ∈ S ∧ good i ≠ bad := by
    have h := mem_erase.mp (e.symm i).2
    exact ⟨h.2, h.1⟩
  have hgoodInj : Function.Injective good := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  let index : Unit ⊕ Fin p ↪ C :=
    { toFun := Sum.elim (fun _ ↦ bad) good
      inj' := by
        intro x y hxy
        rcases x with x | x <;> rcases y with y | y
        · exact congrArg Sum.inl (Subsingleton.elim _ _)
        · exact ((hgood y).2 hxy.symm).elim
        · exact ((hgood x).2 hxy).elim
        · exact congrArg Sum.inr (hgoodInj hxy) }
  have hp : p + 1 = S.card := by
    dsimp only [p]
    rw [Fintype.card_coe]
    exact card_erase_add_one hbad
  refine ⟨p, index, hp, rfl, ?_, fun i ↦ (hgood i).2, ?_⟩
  · intro x
    rcases x with x | x
    · exact hbad
    · exact (hgood x).1
  · intro c hc
    by_cases hcb : c = bad
    · exact ⟨Sum.inl (), hcb.symm⟩
    · let x : P := ⟨c, mem_erase.mpr ⟨hcb, hc⟩⟩
      refine ⟨Sum.inr (e x), ?_⟩
      change (e.symm (e x)).1 = c
      rw [e.symm_apply_apply]

#print axioms exists_distinguished_palette_index

end Erdos19
