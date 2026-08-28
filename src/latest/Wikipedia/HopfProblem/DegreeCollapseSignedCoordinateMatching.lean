import Wikipedia.HopfProblem.DegreeCollapseMorseCoordinateSplit
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Set

/-!
# Matching finite signed coordinate systems

Equal numbers of negative coordinates give an actual coordinate bijection
preserving every sign. This is the finite algebra needed to give the two
adjacent-index endpoint charts the same transverse quadratic form.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.SignedCoordinates

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
theorem positive_of_not_negative {w : ι → ℝ}
    (hw : ∀ i, w i = -1 ∨ w i = 1) {i : ι} (hi : w i ≠ -1) : w i = 1 :=
  (hw i).resolve_left hi

/-- A proved bijection identifies two signed coordinate systems of equal signature. -/
theorem exists_equiv_of_negative_card_eq (w₀ : ι → ℝ) (w₁ : κ → ℝ)
    (h₀ : ∀ i, w₀ i = -1 ∨ w₀ i = 1) (h₁ : ∀ i, w₁ i = -1 ∨ w₁ i = 1)
    (hcard : Fintype.card ι = Fintype.card κ)
    [Fintype {i // w₀ i = -1}] [Fintype {i // w₁ i = -1}]
    (hneg : Fintype.card {i // w₀ i = -1} = Fintype.card {i // w₁ i = -1}) :
    ∃ e : ι ≃ κ, ∀ i, w₁ (e i) = w₀ i := by
  classical
  let eN : {i // w₀ i = -1} ≃ {i // w₁ i = -1} := Fintype.equivOfCardEq hneg
  have hpos : Fintype.card {i // ¬w₀ i = -1} = Fintype.card {i // ¬w₁ i = -1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard, hneg]
  let eP : {i // ¬w₀ i = -1} ≃ {i // ¬w₁ i = -1} := Fintype.equivOfCardEq hpos
  let e₀ := Equiv.sumCompl (fun i : ι => w₀ i = -1)
  let e₁ := Equiv.sumCompl (fun i : κ => w₁ i = -1)
  let e := e₀.symm.trans ((Equiv.sumCongr eN eP).trans e₁)
  refine ⟨e, ?_⟩
  intro i
  obtain ⟨z, rfl⟩ := e₀.surjective i
  simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply]
  cases z with
  | inl x =>
    change w₁ (eN x) = w₀ x
    exact (eN x).property.trans x.property.symm
  | inr x =>
    change w₁ (eP x) = w₀ x
    exact (positive_of_not_negative h₁ (eP x).property).trans
      (positive_of_not_negative h₀ x.property).symm

end Wikipedia.HopfProblem.DegreeCollapse.SignedCoordinates
