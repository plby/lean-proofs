import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySection

/-!
# Restriction compatibility of actual section product charts

Restricting a continuous covering section does not alter any quotient
representative. The resulting charts commute with the actual inclusions
both in the total space and in the products over the open base sets.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.DiagonalQuotient

variable {G B F : Type*} [Group G] [MulAction G B] [MulAction G F]
    [TopologicalSpace B] [TopologicalSpace F]
    {U V W : Opens (BaseSpace G B)}

/-- Restrict a chosen base lift to a smaller open set. -/
def sectionRestrict (h : V ≤ U) (s : C(U, B)) : C(V, B) :=
  s.comp (ContinuousMap.inclusion h)

@[simp] theorem sectionRestrict_apply (h : V ≤ U) (s : C(U, B)) (x : V) :
    sectionRestrict h s x = s (Set.inclusion h x) := rfl

theorem sectionRestrict_section (h : V ≤ U) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) (x : V) :
    baseQuotient G B (sectionRestrict h s x) = x := hs (Set.inclusion h x)

/-- The literal inclusion of the total spaces above nested open sets. -/
def sectionTotalInclusion (h : V ≤ U) :
    C(projection G B F ⁻¹' (V : Set _), projection G B F ⁻¹' (U : Set _)) :=
  ContinuousMap.inclusion (Set.preimage_mono h)

/-- Inclusion of the base open set and identity on the original fibre. -/
def sectionProductInclusion (h : V ≤ U) : C(V × F, U × F) :=
  (ContinuousMap.inclusion h).prodMap (ContinuousMap.id F)

@[simp] theorem sectionMap_restrict (h : V ≤ U) (s : C(U, B)) (x : V × F) :
    sectionMap V (sectionRestrict h s) x =
      sectionMap U s (sectionProductInclusion h x) := rfl

variable [ContinuousConstSMul G F]

/-- Inverse product charts commute with the literal total-space inclusion. -/
theorem sectionHomeomorph_restrict_symm
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (h : V ≤ U) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) (x : V × F) :
    sectionTotalInclusion h
        ((sectionHomeomorph hq V (sectionRestrict h s)
          (sectionRestrict_section h s hs)).symm x) =
      (sectionHomeomorph hq U s hs).symm (sectionProductInclusion h x) := by
  apply Subtype.ext
  rfl

/-- The actual section charts commute with restriction to a smaller open set. -/
theorem sectionHomeomorph_restrict
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (h : V ≤ U) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x)
    (x : projection G B F ⁻¹' (V : Set _)) :
    sectionHomeomorph hq U s hs (sectionTotalInclusion h x) =
      sectionProductInclusion h
        (sectionHomeomorph hq V (sectionRestrict h s)
          (sectionRestrict_section h s hs) x) := by
  apply (sectionHomeomorph hq U s hs).symm.injective
  rw [Homeomorph.symm_apply_apply, ← sectionHomeomorph_restrict_symm,
    Homeomorph.symm_apply_apply]

/-- The restriction square as an equality of actual continuous maps. -/
theorem sectionHomeomorph_restrict_comp
    (hq : IsQuotientCoveringMap (baseQuotient G B) G)
    (h : V ≤ U) (s : C(U, B))
    (hs : ∀ x : U, baseQuotient G B (s x) = x) :
    (sectionHomeomorph (F := F) hq U s hs :
        C(projection G B F ⁻¹' (U : Set _), U × F)).comp
        (sectionTotalInclusion (F := F) h) =
      (sectionProductInclusion (F := F) h).comp
        (sectionHomeomorph (F := F) hq V (sectionRestrict h s)
          (sectionRestrict_section h s hs) :
          C(projection G B F ⁻¹' (V : Set _), V × F)) := by
  apply ContinuousMap.ext
  intro x
  exact sectionHomeomorph_restrict hq h s hs x

end Wikipedia.HopfProblem.DiagonalQuotient
