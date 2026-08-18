import Mathlib

/-!
# Lifting equidecompositions from a torus

This file records the elementary, but useful, transfer from the unit torus to a
half-open Euclidean fundamental cube.  A torus translation has finitely many
Euclidean lifts on the cube: independently in every coordinate, it either
crosses the boundary of the cube or it does not.  Consequently, a finite
translation equidecomposition of quotient images lifts to a finite translation
equidecomposition in Euclidean space.
-/

noncomputable section

open Function Set

namespace Erdos1124.TorusTransfer

variable {ι : Type*} [Fintype ι]

/-- Euclidean space in the coordinates indexed by `ι`. -/
abbrev Euclidean (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

/-- The unit torus in the coordinates indexed by `ι`. -/
abbrev Torus (ι : Type*) := UnitAddTorus ι

/-- The coordinatewise quotient map from Euclidean space to the unit torus. -/
def quotientMap (x : Euclidean ι) : Torus ι := fun i => (x i : UnitAddCircle)

/-- The half-open fundamental cube `[0,1)^ι`. -/
def fundamentalCube : Set (Euclidean ι) :=
  {x | ∀ i, x i ∈ Set.Ico (0 : ℝ) 1}

/-- The canonical representative of a point of the unit torus in `[0,1)^ι`. -/
def representative (x : Torus ι) : Euclidean ι :=
  WithLp.toLp 2 fun i => ((AddCircle.equivIco 1 0) (x i) : ℝ)

@[simp]
theorem quotientMap_representative (x : Torus ι) : quotientMap (representative x) = x := by
  ext i
  exact AddCircle.coe_equivIco

theorem representative_mem_fundamentalCube (x : Torus ι) :
    representative x ∈ fundamentalCube := by
  intro i
  simpa [representative] using (AddCircle.equivIco 1 0 (x i)).property

theorem representative_quotientMap_of_mem {x : Euclidean ι}
    (hx : x ∈ fundamentalCube) : representative (quotientMap x) = x := by
  ext i
  simpa [representative, quotientMap] using
    (AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := 0) (by simpa using hx i))

theorem injOn_quotientMap_fundamentalCube :
    Set.InjOn (quotientMap (ι := ι)) fundamentalCube := by
  intro x hx y hy hxy
  rw [← representative_quotientMap_of_mem hx,
    ← representative_quotientMap_of_mem hy, hxy]

/-- Adding a circle element to a point in `[0,1)` either wraps once or not at all. -/
private theorem equivIco_add_coe (g : UnitAddCircle) {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    ∃ b : Bool,
      ((AddCircle.equivIco 1 0) (g + (x : UnitAddCircle)) : ℝ) =
        x + ((AddCircle.equivIco 1 0) g : ℝ) - if b then 1 else 0 := by
  let r : ℝ := ((AddCircle.equivIco 1 0) g : ℝ)
  have hr : r ∈ Set.Ico (0 : ℝ) 1 := by
    simpa [r] using (AddCircle.equivIco 1 0 g).property
  have hrcoe : (r : UnitAddCircle) = g := by
    exact AddCircle.coe_equivIco
  by_cases h : x + r < 1
  · refine ⟨false, ?_⟩
    have hmem : x + r ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith [hx.1, hr.1], h⟩
    have hcoe : ((x + r : ℝ) : UnitAddCircle) = g + (x : UnitAddCircle) := by
      rw [AddCircle.coe_add, hrcoe, add_comm]
    rw [← hcoe]
    simp only [Bool.false_eq_true, if_false, sub_zero]
    change ((AddCircle.equivIco 1 0) ((x + r : ℝ) : UnitAddCircle) : ℝ) = x + r
    have hmem' : x + r ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      simpa only [zero_add] using hmem
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hmem')
  · refine ⟨true, ?_⟩
    have hmem : x + r - 1 ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith [hx.2, hr.2]
    have hcoe : ((x + r - 1 : ℝ) : UnitAddCircle) =
        g + (x : UnitAddCircle) := by
      rw [AddCircle.coe_sub, AddCircle.coe_add, hrcoe]
      have hone : ((1 : ℝ) : UnitAddCircle) = 0 :=
        AddCircle.coe_period (p := (1 : ℝ))
      rw [hone, sub_zero, add_comm]
    rw [← hcoe]
    simp only [if_true]
    change ((AddCircle.equivIco 1 0) ((x + r - 1 : ℝ) : UnitAddCircle) : ℝ) =
      x + r - 1
    have hmem' : x + r - 1 ∈ Set.Ico (0 : ℝ) (0 + 1) := by
      simpa only [zero_add] using hmem
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq hmem')

/-- A Euclidean lift of a torus translation, with its coordinatewise wrap choices. -/
def translationLift (g : Torus ι) (wrap : ι → Bool) : Euclidean ι :=
  WithLp.toLp 2 fun i =>
    ((AddCircle.equivIco 1 0) (g i) : ℝ) - if wrap i then 1 else 0

/-- The canonical lift of a translated point uses one of the `2^|ι|` lifts of the translation. -/
theorem representative_add_quotientMap (g : Torus ι) {x : Euclidean ι}
    (hx : x ∈ fundamentalCube) :
    ∃ wrap : ι → Bool,
      representative (g + quotientMap x) = translationLift g wrap + x := by
  classical
  choose wrap hwrap using fun i => equivIco_add_coe (g i) (hx i)
  refine ⟨wrap, ?_⟩
  ext i
  simpa [representative, quotientMap, translationLift, add_comm, add_left_comm,
    add_assoc, sub_eq_add_neg] using hwrap i

/-- Lift a finite torus-translation equidecomposition of quotient images of subsets of the
fundamental cube to a finite Euclidean-translation equidecomposition.

The hypotheses `hsource` and `htarget` say that the torus equidecomposition has exactly the
coordinatewise quotient images as its source and target. -/
def liftEquidecomp {A B : Set (Euclidean ι)}
    (hA : A ⊆ fundamentalCube) (hB : B ⊆ fundamentalCube)
    (e : Equidecomp (Torus ι) (Multiplicative (Torus ι)))
    (hsource : e.source = quotientMap '' A)
    (htarget : e.target = quotientMap '' B) :
    Equidecomp (Euclidean ι) (Multiplicative (Euclidean ι)) where
  toPartialEquiv :=
    { toFun := fun x => representative (e (quotientMap x))
      invFun := fun y => representative (e.symm (quotientMap y))
      source := A
      target := B
      map_source' := by
        intro x hx
        have hqx : quotientMap x ∈ e.source := hsource.symm ▸ ⟨x, hx, rfl⟩
        have heqx : e (quotientMap x) ∈ quotientMap '' B := by
          rw [← htarget]
          exact e.apply_mem_target hqx
        obtain ⟨y, hyB, hy⟩ := heqx
        rw [← hy, representative_quotientMap_of_mem (hB hyB)]
        exact hyB
      map_target' := by
        intro y hy
        have hqy : quotientMap y ∈ e.target := htarget.symm ▸ ⟨y, hy, rfl⟩
        have hesy : e.symm (quotientMap y) ∈ quotientMap '' A := by
          rw [← hsource]
          exact e.map_target hqy
        obtain ⟨x, hxA, hx⟩ := hesy
        rw [← hx, representative_quotientMap_of_mem (hA hxA)]
        exact hxA
      left_inv' := by
        intro x hx
        have hqx : quotientMap x ∈ e.source := hsource.symm ▸ ⟨x, hx, rfl⟩
        rw [quotientMap_representative]
        change representative (e.toPartialEquiv.symm (e (quotientMap x))) = x
        rw [e.left_inv hqx,
          representative_quotientMap_of_mem (hA hx)]
      right_inv' := by
        intro y hy
        have hqy : quotientMap y ∈ e.target := htarget.symm ▸ ⟨y, hy, rfl⟩
        rw [quotientMap_representative]
        change representative (e (e.toPartialEquiv.symm (quotientMap y))) = y
        rw [e.right_inv hqy,
          representative_quotientMap_of_mem (hB hy)] }
  isDecompOn' := by
    classical
    let lifts : Finset (Multiplicative (Euclidean ι)) :=
      (e.witness ×ˢ (Finset.univ : Finset (ι → Bool))).image fun p =>
        Multiplicative.ofAdd (translationLift p.1.toAdd p.2)
    refine ⟨lifts, ?_⟩
    intro x hx
    have hqx : quotientMap x ∈ e.source := hsource.symm ▸ ⟨x, hx, rfl⟩
    obtain ⟨g, hg, heg⟩ := e.isDecompOn (quotientMap x) hqx
    obtain ⟨wrap, hwrap⟩ := representative_add_quotientMap g.toAdd (hA hx)
    refine ⟨Multiplicative.ofAdd (translationLift g.toAdd wrap), ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨(g, wrap), Finset.mem_product.2 ⟨hg, Finset.mem_univ _⟩, rfl⟩
    · change representative (e (quotientMap x)) = _
      rw [heg]
      change representative (g.toAdd + quotientMap x) = _
      simpa only [ofAdd_smul, vadd_eq_add] using hwrap

@[simp]
theorem liftEquidecomp_source {A B : Set (Euclidean ι)}
    (hA : A ⊆ fundamentalCube) (hB : B ⊆ fundamentalCube)
    (e : Equidecomp (Torus ι) (Multiplicative (Torus ι)))
    (hsource : e.source = quotientMap '' A) (htarget : e.target = quotientMap '' B) :
    (liftEquidecomp hA hB e hsource htarget).source = A := rfl

@[simp]
theorem liftEquidecomp_target {A B : Set (Euclidean ι)}
    (hA : A ⊆ fundamentalCube) (hB : B ⊆ fundamentalCube)
    (e : Equidecomp (Torus ι) (Multiplicative (Torus ι)))
    (hsource : e.source = quotientMap '' A) (htarget : e.target = quotientMap '' B) :
    (liftEquidecomp hA hB e hsource htarget).target = B := rfl

end Erdos1124.TorusTransfer
