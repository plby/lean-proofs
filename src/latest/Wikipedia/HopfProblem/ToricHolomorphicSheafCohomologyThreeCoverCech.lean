import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverConnecting
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyThreeCoverRestriction

/-!
# Literal Čech equations control the actual degree-one restriction map

The source is actual `H¹(U₀ ∪ U₁)` and the target is actual
`H¹((U₀ ∩ U₂) ∪ (U₁ ∩ U₂))`. Actual section representatives and proved
connecting-map naturality turn literal Čech one-exactness into injectivity,
and literal Čech two-surjectivity into surjectivity, of this native map.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover

theorem addHom_sub_add {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (x y z : G) : f (x - y + z) = f x - f y + f z := by
  rw [map_add, map_sub]

theorem addHom_eq_of_sub_eq {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) {x y z : G} (h : x - y = z) (hy : f y = 0) : f x = f z := by
  rw [← h, map_sub, hy, sub_zero]

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  (U : Fin 3 → Opens X)

theorem overlapUnion_le_firstUnion : overlapUnion U ≤ firstUnion U :=
  sup_le_sup inf_le_left inf_le_left

theorem pairIntersection_le_pair01 : (U 0 ⊓ U 2) ⊓ (U 1 ⊓ U 2) ≤ U 0 ⊓ U 1 :=
  inf_le_inf inf_le_left inf_le_left

/-- The original degree-one open restriction used between the two MV squares. -/
abbrev unionOverlapRestriction :
    CategoryTheory.Sheaf.H'.{0} F 1 (firstUnion U) →+
      CategoryTheory.Sheaf.H'.{0} F 1 (overlapUnion U) :=
  cohomologyRestrict F 1 (overlapUnion_le_firstUnion U)

theorem sectionConnecting_first_restrict (c01 : Sections F (U 0 ⊓ U 1)) :
    unionOverlapRestriction F U (sectionConnecting F (U 0) (U 1) c01) =
      sectionConnecting F (U 0 ⊓ U 2) (U 1 ⊓ U 2)
        (sectionRestrict F (pairIntersection_le_pair01 U) c01) :=
  sectionConnecting_naturality F inf_le_left inf_le_left c01

/-- The literal Čech differential, on the actual intersection in the
second MV square, is precisely a restricted `01` section minus a pair difference. -/
theorem cochainDifferential_restrict
    (c01 : Sections F (U 0 ⊓ U 1)) (c02 : Sections F (U 0 ⊓ U 2))
    (c12 : Sections F (U 1 ⊓ U 2)) :
    sectionRestrict F (pairIntersection_eq U).le (cochainDifferential F U (c01, c02, c12)) =
      sectionRestrict F (pairIntersection_le_pair01 U) c01 -
        MayerVietoris.sectionsDifference F (U 0 ⊓ U 2) (U 1 ⊓ U 2) (c02, c12) := by
  let J := (U 0 ⊓ U 2) ⊓ (U 1 ⊓ U 2)
  have hAlg (x y z : Sections F J) : x - y + z = x - (y - z) := by abel
  change sectionRestrict F (pairIntersection_eq U).le
    (sectionRestrict F (triple_le_pair01 U) c01 -
      sectionRestrict F (triple_le_pair02 U) c02 +
        sectionRestrict F (triple_le_pair12 U) c12) =
    sectionRestrict F (pairIntersection_le_pair01 U) c01 -
      (sectionRestrict F inf_le_left c02 - sectionRestrict F inf_le_right c12)
  exact Eq.trans (addHom_sub_add (sectionRestrict F (pairIntersection_eq U).le) _ _ _)
    (Eq.trans
      (congrArg₂ (fun x y : Sections F J => x + y)
        (congrArg₂ (fun x y : Sections F J => x - y)
          (sectionRestrict_comp F (pairIntersection_eq U).le (triple_le_pair01 U) c01)
          (sectionRestrict_comp F (pairIntersection_eq U).le (triple_le_pair02 U) c02))
        (sectionRestrict_comp F (pairIntersection_eq U).le (triple_le_pair12 U) c12))
      (hAlg _ _ _))

/-- Actual one-cocycle splitting forces injectivity of the actual H¹ restriction. -/
theorem unionOverlapRestriction_injective (hOne : CechOneExact F U)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 0))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 1))] :
    Function.Injective (unionOverlapRestriction F U) := by
  apply (injective_iff_map_eq_zero (unionOverlapRestriction F U)).mpr
  intro a ha
  obtain ⟨c01, rfl⟩ := sectionConnecting_surjective F (U 0) (U 1) a
  have hz : sectionConnecting F (U 0 ⊓ U 2) (U 1 ⊓ U 2)
      (sectionRestrict F (pairIntersection_le_pair01 U) c01) = 0 :=
    Eq.trans (sectionConnecting_first_restrict F U c01).symm ha
  obtain ⟨⟨c02, c12⟩, hs⟩ :=
    (sectionConnecting_exact F (U 0 ⊓ U 2) (U 1 ⊓ U 2) _).mp hz
  have hcJ : sectionRestrict F (pairIntersection_eq U).le
      (cochainDifferential F U (c01, c02, c12)) = 0 :=
    Eq.trans (cochainDifferential_restrict F U c01 c02 c12)
      (Eq.trans (congrArg (fun z =>
        sectionRestrict F (pairIntersection_le_pair01 U) c01 - z) hs) (sub_self _))
  have hc : cochainDifferential F U (c01, c02, c12) = 0 := by
    apply Function.LeftInverse.injective
      (sectionRestrict_inverse F (pairIntersection_eq U).ge (pairIntersection_eq U).le)
    exact Eq.trans hcJ (map_zero _).symm
  obtain ⟨b0, b1, b2, h01, _, _⟩ := hOne c01 c02 c12 hc
  exact Eq.trans (congrArg (sectionConnecting F (U 0) (U 1)) h01.symm)
    (sectionConnecting_difference F (U 0) (U 1) b0 b1)

/-- Actual triple-section surjectivity forces surjectivity of the actual H¹ restriction. -/
theorem unionOverlapRestriction_surjective (hTwo : CechTwoSurjective F U)
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 0 ⊓ U 2))]
    [Subsingleton (CategoryTheory.Sheaf.H'.{0} F 1 (U 1 ⊓ U 2))] :
    Function.Surjective (unionOverlapRestriction F U) := by
  intro a
  obtain ⟨s, rfl⟩ := sectionConnecting_surjective F (U 0 ⊓ U 2) (U 1 ⊓ U 2) a
  obtain ⟨⟨c01, c02, c12⟩, hc⟩ := hTwo (sectionRestrict F (pairIntersection_eq U).ge s)
  have he : sectionRestrict F (pairIntersection_le_pair01 U) c01 -
      MayerVietoris.sectionsDifference F (U 0 ⊓ U 2) (U 1 ⊓ U 2) (c02, c12) = s :=
    Eq.trans (cochainDifferential_restrict F U c01 c02 c12).symm
      (Eq.trans (congrArg (sectionRestrict F (pairIntersection_eq U).le) hc)
        (sectionRestrict_inverse F (pairIntersection_eq U).le (pairIntersection_eq U).ge s))
  refine ⟨sectionConnecting F (U 0) (U 1) c01, ?_⟩
  exact Eq.trans (sectionConnecting_first_restrict F U c01)
    (addHom_eq_of_sub_eq (sectionConnecting F (U 0 ⊓ U 2) (U 1 ⊓ U 2)) he
      (sectionConnecting_difference F (U 0 ⊓ U 2) (U 1 ⊓ U 2) c02 c12))

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ThreeCover
