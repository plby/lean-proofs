import Wikipedia.HopfProblem.HolomorphicPicardCechAlgebra

/-!
# Actual refinement maps on Čech classes

All maps below restrict literal sections of the original sheaf. Two choices
of a refinement function differ by an explicitly constructed coboundary;
thus the induced map on cover cohomology does not depend on that choice.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.Cech

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {ι κ μ : Type} {U : ι → Opens X} {V : κ → Opens X} {W : μ → Opens X}

/-- Restriction of a genuine cocycle along a specified refinement. -/
def refinement (r : κ → ι) (h : ∀ a, V a ≤ U (r a)) :
    CechOneCocycle F U →+ CechOneCocycle F V where
  toFun c :=
    { value := fun a b => res F (inf_le_inf (h a) (h b)) (c.value (r a) (r b))
      condition := by
        intro a b d
        simp only [res_trans]
        exact restrict_condition c
          ((inf_le_left.trans inf_le_left).trans (h a))
          ((inf_le_left.trans inf_le_right).trans (h b))
          (inf_le_right.trans (h d)) }
  map_zero' := by
    apply cocycle_ext
    intro a b
    simp
  map_add' c d := by
    apply cocycle_ext
    intro a b
    simp

@[simp] theorem refinement_value (r : κ → ι) (h : ∀ a, V a ≤ U (r a))
    (c : CechOneCocycle F U) (a b : κ) :
    (refinement F r h c).value a b =
      res F (inf_le_inf (h a) (h b)) (c.value (r a) (r b)) := rfl

def zeroRefinement (r : κ → ι) (h : ∀ a, V a ≤ U (r a)) :
    ZeroCochain F U →+ ZeroCochain F V where
  toFun b a := res F (h a) (b (r a))
  map_zero' := by ext a; exact map_zero _
  map_add' b d := by ext a; exact map_add _ _ _

@[simp] theorem zeroRefinement_apply (r : κ → ι) (h : ∀ a, V a ≤ U (r a))
    (b : ZeroCochain F U) (a : κ) :
    zeroRefinement F r h b a = res F (h a) (b (r a)) := rfl

theorem refinement_coboundary (r : κ → ι) (h : ∀ a, V a ≤ U (r a))
    (b : ZeroCochain F U) :
    refinement F r h (coboundary F U b) =
      coboundary F V (zeroRefinement F r h b) := by
  apply cocycle_ext
  intro a d
  simp only [refinement_value, coboundary_value, zeroRefinement_apply,
    map_sub, res_trans]

theorem refinement_id (c : CechOneCocycle F U) :
    refinement F id (fun _ => le_rfl) c = c := by
  apply cocycle_ext
  intro i j
  exact res_refl F _ _

theorem refinement_comp (r : κ → ι) (hr : ∀ a, V a ≤ U (r a))
    (s : μ → κ) (hs : ∀ b, W b ≤ V (s b)) (c : CechOneCocycle F U) :
    refinement F s hs (refinement F r hr c) =
      refinement F (r ∘ s) (fun b => (hs b).trans (hr (s b))) c := by
  apply cocycle_ext
  intro a b
  exact res_trans F _ _ _

/-- The induced genuine quotient homomorphism on this cover. -/
def cohomologyRefinement (r : κ → ι) (h : ∀ a, V a ≤ U (r a)) :
    CoverCohomology F U →+ CoverCohomology F V :=
  QuotientAddGroup.map (coboundary F U).range (coboundary F V).range
    (refinement F r h) (by
      rintro c ⟨b, rfl⟩
      exact ⟨zeroRefinement F r h b, (refinement_coboundary F r h b).symm⟩)

@[simp] theorem cohomologyRefinement_classOf (r : κ → ι)
    (h : ∀ a, V a ≤ U (r a)) (c : CechOneCocycle F U) :
    cohomologyRefinement F r h (classOf F U c) =
      classOf F V (refinement F r h c) := rfl

/-- An explicit zero cochain comparing two refinements of the same cover. -/
def refinementComparison (r s : κ → ι) (hr : ∀ a, V a ≤ U (r a))
    (hs : ∀ a, V a ≤ U (s a)) (c : CechOneCocycle F U) : ZeroCochain F V :=
  fun a => res F (le_inf (hr a) (hs a)) (c.value (r a) (s a))

theorem refinement_sub_refinement (r s : κ → ι)
    (hr : ∀ a, V a ≤ U (r a)) (hs : ∀ a, V a ≤ U (s a))
    (c : CechOneCocycle F U) :
    refinement F r hr c - refinement F s hs c =
      coboundary F V (refinementComparison F r s hr hs c) := by
  apply cocycle_ext
  intro a b
  simp only [sub_value, refinement_value, coboundary_value,
    refinementComparison, res_trans]
  apply sub_eq_sub_iff_add_eq_add.mpr
  exact (restrict_condition c (inf_le_left.trans (hr a))
    (inf_le_right.trans (hr b)) (inf_le_right.trans (hs b))).trans
    (restrict_condition c (inf_le_left.trans (hr a))
      (inf_le_left.trans (hs a)) (inf_le_right.trans (hs b))).symm

theorem refinement_class_independent (r s : κ → ι)
    (hr : ∀ a, V a ≤ U (r a)) (hs : ∀ a, V a ≤ U (s a))
    (c : CechOneCocycle F U) :
    classOf F V (refinement F r hr c) = classOf F V (refinement F s hs c) := by
  apply (class_eq_class_iff F V _ _).mpr
  rw [refinement_sub_refinement]
  exact ⟨_, fun _ _ => rfl⟩

theorem cohomologyRefinement_independent (r s : κ → ι)
    (hr : ∀ a, V a ≤ U (r a)) (hs : ∀ a, V a ≤ U (s a)) :
    cohomologyRefinement F r hr = cohomologyRefinement F s hs := by
  apply QuotientAddGroup.addMonoidHom_ext
  ext c
  exact refinement_class_independent F r s hr hs c

end Wikipedia.HopfProblem.HolomorphicPicard.Cech
