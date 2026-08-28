import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyMayerVietoris

/-!
# Literal section cochains for three actual open sets

The conditions below concern the original sections and restriction maps
of an actual abelian sheaf. They do not assume a comparison between Čech
groups and derived sheaf cohomology.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover

variable {X : TopCat.{0}}

abbrev Sections (F : TopCat.Sheaf AddCommGrpCat.{0} X) (W : Opens X) :=
  F.obj.obj (op W)

/-- The original restriction map of the original sheaf. -/
abbrev sectionRestrict (F : TopCat.Sheaf AddCommGrpCat.{0} X) {A B : Opens X}
    (h : A ≤ B) : Sections F B →+ Sections F A :=
  (F.obj.map (homOfLE h).op).hom

theorem sectionRestrict_comp (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    {A B C : Opens X} (hAB : A ≤ B) (hBC : B ≤ C) (s : Sections F C) :
    sectionRestrict F hAB (sectionRestrict F hBC s) =
      sectionRestrict F (hAB.trans hBC) s := by
  change (F.obj.map (homOfLE hAB).op) ((F.obj.map (homOfLE hBC).op) s) = _
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  rfl

variable (F : TopCat.Sheaf AddCommGrpCat.{0} X) (U : Fin 3 → Opens X)

def firstUnion : Opens X := U 0 ⊔ U 1

def coverOpen : Opens X := firstUnion U ⊔ U 2

def overlapUnion : Opens X := (U 0 ⊓ U 2) ⊔ (U 1 ⊓ U 2)

def tripleOpen : Opens X := (U 0 ⊓ U 1) ⊓ U 2

theorem firstUnion_inf : firstUnion U ⊓ U 2 = overlapUnion U := inf_sup_right _ _ _

theorem pairIntersection_eq : (U 0 ⊓ U 2) ⊓ (U 1 ⊓ U 2) = tripleOpen U := by
  simp only [tripleOpen, inf_assoc, inf_left_comm, inf_idem]

theorem triple_le_pair01 : tripleOpen U ≤ U 0 ⊓ U 1 := inf_le_left

theorem triple_le_pair02 : tripleOpen U ≤ U 0 ⊓ U 2 :=
  le_inf (inf_le_left.trans inf_le_left) inf_le_right

theorem triple_le_pair12 : tripleOpen U ≤ U 1 ⊓ U 2 :=
  le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- Literal ordered one-cochains, on the pairs `01`, `02`, and `12`. -/
abbrev OneCochain :=
  Sections F (U 0 ⊓ U 1) × Sections F (U 0 ⊓ U 2) × Sections F (U 1 ⊓ U 2)

/-- The literal alternating restriction map `c₀₁ - c₀₂ + c₁₂` on the triple overlap. -/
def cochainDifferential : OneCochain F U →+ Sections F (tripleOpen U) where
  toFun c := sectionRestrict F (triple_le_pair01 U) c.1 -
    sectionRestrict F (triple_le_pair02 U) c.2.1 +
      sectionRestrict F (triple_le_pair12 U) c.2.2
  map_zero' := by
    change sectionRestrict F _ (0 : Sections F (U 0 ⊓ U 1)) -
      sectionRestrict F _ (0 : Sections F (U 0 ⊓ U 2)) +
        sectionRestrict F _ (0 : Sections F (U 1 ⊓ U 2)) = 0
    simp only [map_zero, sub_self, add_zero]
  map_add' a b := by
    change sectionRestrict F _ (a.1 + b.1) -
      sectionRestrict F _ (a.2.1 + b.2.1) + sectionRestrict F _ (a.2.2 + b.2.2) = _
    simp only [map_add]
    abel

/-- Every literal three-chart one-cocycle is a difference of actual sections. -/
def CechOneExact : Prop :=
  ∀ (c01 : Sections F (U 0 ⊓ U 1)) (c02 : Sections F (U 0 ⊓ U 2))
      (c12 : Sections F (U 1 ⊓ U 2)),
    cochainDifferential F U (c01, c02, c12) = 0 →
      ∃ (b0 : Sections F (U 0)) (b1 : Sections F (U 1)) (b2 : Sections F (U 2)),
        MayerVietoris.sectionsDifference F (U 0) (U 1) (b0, b1) = c01 ∧
        MayerVietoris.sectionsDifference F (U 0) (U 2) (b0, b2) = c02 ∧
        MayerVietoris.sectionsDifference F (U 1) (U 2) (b1, b2) = c12

/-- Surjectivity of the actual alternating restriction map onto triple sections. -/
def CechTwoSurjective : Prop := Function.Surjective (cochainDifferential F U)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover
