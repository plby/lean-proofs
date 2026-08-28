import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsDescentHolomorphic

/-!
# Holomorphic descent of actual canonical sections

The section constructed by fibre-compatible descent is holomorphic for the
original canonical bundle atlas.  Its composition with the quotient map
is the already holomorphic inverse-pullback bundle map applied to the
upstairs section.  Native local inverse charts then prove holomorphicity
downstairs, without any regularity assumption on the chosen preimages.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsDescent

open _root_.Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
  [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]

/-- A compatible holomorphic canonical section descends holomorphically
through a surjective actual local biholomorphism. -/
theorem descendedSection_holomorphic {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : Section M) (hs : Compatible hq s)
    (hhol : ContMDiff I ((I).prod I₁) ω (sectionMap s)) :
    ContMDiff I ((I).prod I₁) ω (sectionMap (descendedSection hq hsurj s)) := by
  apply contMDiff_of_comp_surjective_localDiffeomorph hq hsurj
  have hfun : sectionMap (descendedSection hq hsurj s) ∘ q =
      forwardMap hq ∘ sectionMap s :=
    funext (descendedSectionMap_at_image hq hsurj s hs)
  rw [hfun]
  exact (forwardMap_holomorphic hq).comp hhol

/-- The descended section bundled as a genuine holomorphic section of the
original canonical line bundle. -/
def holomorphicDescendedSection {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : ContMDiffSection I ℂ ω (Atlas.core M).Fiber) (hs : Compatible hq s) :
    ContMDiffSection I ℂ ω (Atlas.core N).Fiber where
  toFun := descendedSection hq hsurj s
  contMDiff_toFun := descendedSection_holomorphic hq hsurj s hs s.contMDiff

@[simp] theorem holomorphicDescendedSection_apply {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : ContMDiffSection I ℂ ω (Atlas.core M).Fiber) (hs : Compatible hq s) (y : N) :
    holomorphicDescendedSection hq hsurj s hs y = descendedSection hq hsurj s y := rfl

theorem pullback_holomorphicDescendedSection {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : ContMDiffSection I ℂ ω (Atlas.core M).Fiber) (hs : Compatible hq s) (x : M) :
    pullbackEquiv hq x (holomorphicDescendedSection hq hsurj s hs (q x)) = s x :=
  pullback_descendedSection hq hsurj s hs x

/-- The holomorphic descent is unique among actual holomorphic sections
satisfying the native differential pullback equation. -/
theorem existsUnique_holomorphic_descent {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : ContMDiffSection I ℂ ω (Atlas.core M).Fiber) (hs : Compatible hq s) :
    ∃! t : ContMDiffSection I ℂ ω (Atlas.core N).Fiber,
      ∀ x, pullbackEquiv hq x (t (q x)) = s x := by
  refine ⟨holomorphicDescendedSection hq hsurj s hs,
    pullback_holomorphicDescendedSection hq hsurj s hs, ?_⟩
  intro t ht
  apply DFunLike.ext
  intro y
  exact congrFun (descendedSection_unique hq hsurj s hs t ht) y

theorem holomorphicDescendedSection_zero_iff_at_image {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : ContMDiffSection I ℂ ω (Atlas.core M).Fiber) (hs : Compatible hq s) (x : M) :
    holomorphicDescendedSection hq hsurj s hs (q x) = 0 ↔ s x = 0 :=
  descendedSection_zero_iff_at_image hq hsurj s hs x

theorem holomorphicDescendedSection_nowhere_zero_iff {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : ContMDiffSection I ℂ ω (Atlas.core M).Fiber) (hs : Compatible hq s) :
    (∀ y, holomorphicDescendedSection hq hsurj s hs y ≠ 0) ↔ ∀ x, s x ≠ 0 :=
  descendedSection_nowhere_zero_iff hq hsurj s hs

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsDescent
