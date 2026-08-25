import Util.IncidenceGeometry.Basic

open Classical
noncomputable section

universe u v

lemma FiniteAuxiliaryFaceQuotient (Face : Type u) [Fintype Face] (FL FR : Face) :
    let sideAtom : Option Face → Prop :=
      fun x => x = none ∨ x = some FL ∨ x = some FR
    ∃ (FaceDel : Type v) (_faceDelFintype : Fintype FaceDel)
        (componentOf : Option Face → FaceDel),
      Function.Surjective componentOf ∧
        ∀ x y : Option Face,
          componentOf x = componentOf y ↔
            x = y ∨ (sideAtom x ∧ sideAtom y) := by
  classical
  let sideAtom : Option Face → Prop :=
    fun x => x = none ∨ x = some FL ∨ x = some FR
  let RawFaceDel : Type u :=
    {x : Option Face // ¬ (x = none ∨ x = some FL ∨ x = some FR)} ⊕ PUnit
  let rawComponentOf : Option Face → RawFaceDel :=
    fun x =>
      if h : x = none ∨ x = some FL ∨ x = some FR then
        Sum.inr PUnit.unit
      else
        Sum.inl ⟨x, h⟩
  have hraw_surj : Function.Surjective rawComponentOf := by
    intro Q
    cases Q with
    | inl x =>
        refine ⟨x.1, ?_⟩
        simp [rawComponentOf, x.2]
    | inr u =>
        refine ⟨none, ?_⟩
        cases u
        simp [rawComponentOf]
  have hraw_eq :
      ∀ x y : Option Face,
        rawComponentOf x = rawComponentOf y ↔
          x = y ∨ ((x = none ∨ x = some FL ∨ x = some FR) ∧
            (y = none ∨ y = some FL ∨ y = some FR)) := by
    intro x y
    constructor
    · intro hxy
      by_cases hx : x = none ∨ x = some FL ∨ x = some FR
      · by_cases hy : y = none ∨ y = some FL ∨ y = some FR
        · exact Or.inr ⟨hx, hy⟩
        · have hfalse : False := by
            simp [rawComponentOf, hx, hy] at hxy
          exact hfalse.elim
      · by_cases hy : y = none ∨ y = some FL ∨ y = some FR
        · have hfalse : False := by
            simp [rawComponentOf, hx, hy] at hxy
          exact hfalse.elim
        · left
          have hxy' := hxy
          simp [rawComponentOf, hx, hy] at hxy'
          exact congrArg Subtype.val (Sum.inl.inj hxy')
    · intro hxy
      rcases hxy with rfl | ⟨hx, hy⟩
      · rfl
      · simp [rawComponentOf, hx, hy]
  let eFin : RawFaceDel ≃ Fin (Fintype.card RawFaceDel) := Fintype.equivFin RawFaceDel
  let FaceDel := ULift.{v, 0} (Fin (Fintype.card RawFaceDel))
  let componentOf : Option Face → FaceDel := fun x => ULift.up (eFin (rawComponentOf x))
  refine ⟨FaceDel, inferInstance, componentOf, ?_, ?_⟩
  · intro Q
    rcases Q with ⟨q⟩
    rcases hraw_surj (eFin.symm q) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simp [componentOf, hx]
  · intro x y
    dsimp [sideAtom]
    constructor
    · intro hxy
      have hfin : eFin (rawComponentOf x) = eFin (rawComponentOf y) := by
        exact congrArg ULift.down hxy
      exact (hraw_eq x y).1 (eFin.injective hfin)
    · intro hxy
      have hraw : rawComponentOf x = rawComponentOf y := (hraw_eq x y).2 hxy
      simp [componentOf, hraw]
