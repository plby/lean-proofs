import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverBasic

/-!
# Gluing actual sections in the three-open argument

The actual sheaf condition glues compatible pairs of sections. Literal
three-chart Čech one-exactness then makes the actual section-difference
map for `(U₀ ∪ U₁, U₂)` surjective.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)

theorem sections_glue (A B : Opens X) (a : Sections F A) (b : Sections F B)
    (hab : sectionRestrict F (show A ⊓ B ≤ A from inf_le_left) a =
      sectionRestrict F (show A ⊓ B ≤ B from inf_le_right) b) :
    ∃ s : Sections F (A ⊔ B),
      sectionRestrict F le_sup_left s = a ∧ sectionRestrict F le_sup_right s = b := by
  let P := (sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj F
  have h := (MayerVietoris.square A B).sheafCondition_of_sheaf P
  exact ⟨h.glue a b hab, h.map_f₂₄_op_glue a b hab, h.map_f₃₄_op_glue a b hab⟩

theorem sections_ext (A B : Opens X) {s t : Sections F (A ⊔ B)}
    (hA : sectionRestrict F (show A ≤ A ⊔ B from le_sup_left) s =
      sectionRestrict F le_sup_left t)
    (hB : sectionRestrict F (show B ≤ A ⊔ B from le_sup_right) s =
      sectionRestrict F le_sup_right t) : s = t := by
  let P := (sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj F
  have h := (MayerVietoris.square A B).sheafCondition_of_sheaf P
  exact h.ext hA hB

theorem sections_ext_of_cover (A B D : Opens X) (hA : A ≤ D) (hB : B ≤ D)
    (hcover : A ⊔ B = D) {s t : Sections F D}
    (ha : sectionRestrict F hA s = sectionRestrict F hA t)
    (hb : sectionRestrict F hB s = sectionRestrict F hB t) : s = t := by
  subst D
  exact sections_ext F A B ha hb

theorem sectionsDifference_apply (A B : Opens X) (a : Sections F A) (b : Sections F B) :
    MayerVietoris.sectionsDifference F A B (a, b) =
      sectionRestrict F inf_le_left a - sectionRestrict F inf_le_right b := rfl

theorem sectionRestrict_difference (A B D : Opens X) (h : D ≤ A ⊓ B)
    (a : Sections F A) (b : Sections F B) :
    sectionRestrict F h (MayerVietoris.sectionsDifference F A B (a, b)) =
      sectionRestrict F (h.trans inf_le_left) a -
        sectionRestrict F (h.trans inf_le_right) b := by
  change sectionRestrict F h
    (sectionRestrict F inf_le_left a - sectionRestrict F inf_le_right b) = _
  exact Eq.trans (map_sub (sectionRestrict F h) _ _)
    (congrArg₂ (fun x y : Sections F D => x - y)
      (sectionRestrict_comp F h inf_le_left a) (sectionRestrict_comp F h inf_le_right b))

theorem cochainDifferential_apply (U : Fin 3 → Opens X)
    (c01 : Sections F (U 0 ⊓ U 1)) (c02 : Sections F (U 0 ⊓ U 2))
    (c12 : Sections F (U 1 ⊓ U 2)) :
    cochainDifferential F U (c01, c02, c12) =
      sectionRestrict F (triple_le_pair01 U) c01 -
        sectionRestrict F (triple_le_pair02 U) c02 +
          sectionRestrict F (triple_le_pair12 U) c12 := rfl

variable (U : Fin 3 → Opens X)

theorem pair02_le_unionIntersection : U 0 ⊓ U 2 ≤ firstUnion U ⊓ U 2 :=
  le_inf (inf_le_left.trans le_sup_left) inf_le_right

theorem pair12_le_unionIntersection : U 1 ⊓ U 2 ≤ firstUnion U ⊓ U 2 :=
  le_inf (inf_le_left.trans le_sup_right) inf_le_right

/-- A section on the actual overlap of the first union and third open
extends as a difference when literal three-chart one-cocycles split. -/
theorem union_sectionsDifference_surjective (hOne : CechOneExact F U) :
    Function.Surjective (MayerVietoris.sectionsDifference F (firstUnion U) (U 2)) := by
  intro s
  let c02 := sectionRestrict F (pair02_le_unionIntersection U) s
  let c12 := sectionRestrict F (pair12_le_unionIntersection U) s
  have hc : cochainDifferential F U (0, c02, c12) = 0 := by
    rw [cochainDifferential_apply, map_zero]
    dsimp only [c02, c12]
    rw [sectionRestrict_comp, sectionRestrict_comp]
    abel
  obtain ⟨b0, b1, b2, h01, h02, h12⟩ := hOne 0 c02 c12 hc
  have hab : sectionRestrict F (show U 0 ⊓ U 1 ≤ U 0 from inf_le_left) b0 =
      sectionRestrict F (show U 0 ⊓ U 1 ≤ U 1 from inf_le_right) b1 :=
    sub_eq_zero.mp h01
  obtain ⟨a, ha0, ha1⟩ := sections_glue F (U 0) (U 1) b0 b1 hab
  refine ⟨(a, b2), ?_⟩
  apply sections_ext_of_cover F (U 0 ⊓ U 2) (U 1 ⊓ U 2) (firstUnion U ⊓ U 2)
    (pair02_le_unionIntersection U) (pair12_le_unionIntersection U) (firstUnion_inf U).symm
  · change sectionRestrict F (pair02_le_unionIntersection U)
      (MayerVietoris.sectionsDifference F (firstUnion U) (U 2) (a, b2)) = c02
    have ha02 : sectionRestrict F
        (show U 0 ⊓ U 2 ≤ firstUnion U from inf_le_left.trans le_sup_left) a =
          sectionRestrict F inf_le_left b0 :=
      Eq.trans (sectionRestrict_comp F inf_le_left le_sup_left a).symm
        (congrArg (sectionRestrict F (show U 0 ⊓ U 2 ≤ U 0 from inf_le_left)) ha0)
    exact Eq.trans
      (sectionRestrict_difference F (firstUnion U) (U 2) (U 0 ⊓ U 2)
        (pair02_le_unionIntersection U) a b2)
      (Eq.trans (congrArg (fun z : Sections F (U 0 ⊓ U 2) =>
        z - sectionRestrict F inf_le_right b2) ha02) h02)
  · change sectionRestrict F (pair12_le_unionIntersection U)
      (MayerVietoris.sectionsDifference F (firstUnion U) (U 2) (a, b2)) = c12
    have ha12 : sectionRestrict F
        (show U 1 ⊓ U 2 ≤ firstUnion U from inf_le_left.trans le_sup_right) a =
          sectionRestrict F inf_le_left b1 :=
      Eq.trans (sectionRestrict_comp F inf_le_left le_sup_right a).symm
        (congrArg (sectionRestrict F (show U 1 ⊓ U 2 ≤ U 1 from inf_le_left)) ha1)
    exact Eq.trans
      (sectionRestrict_difference F (firstUnion U) (U 2) (U 1 ⊓ U 2)
        (pair12_le_unionIntersection U) a b2)
      (Eq.trans (congrArg (fun z : Sections F (U 1 ⊓ U 2) =>
        z - sectionRestrict F inf_le_right b2) ha12) h12)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover
