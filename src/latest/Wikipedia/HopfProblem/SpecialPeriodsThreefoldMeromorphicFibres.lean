import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicFibresDenominators

/-!
# Genuine meromorphic restrictions to all but countably many regular fibres

Every global meromorphic function on the constructed threefold has a
finite cover by genuine local holomorphic fractions, by compactness.
The countable bad sphere-value sets of these actual denominators therefore
leave every remaining original period torus admissible for sectionwise
meromorphic pullback. No good-fibre data is assumed.
-/

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicFibres

open HolomorphicForms.RegularCover HolomorphicMeromorphic

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold Threefold.space_compact

/-- For every genuine global meromorphic function, only countably many
actual sphere values need be excluded to restrict to every native regular
period torus above the remaining values. -/
theorem exists_countable_exceptional_set (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    ∃ S : Set RiemannSphere, S.Countable ∧ ∀ z : TriangleRegularPoint,
      regularSphereValue z ∉ S → PullbackAdmissible I₂ IF (regularTorusInclusionMap z) ⊤ g := by
  classical
  have hrep : ∀ x : Threefold.Space,
      ∃ (U : Opens Threefold.Space) (p q : HolomorphicFunctionSheaf.Section IF Threefold.Space U),
        x ∈ U ∧ (∀ y : U, holomorphicGerm IF Threefold.Space U y q ≠ 0) ∧
          ∀ y : U, g ⟨y.val, by trivial⟩ = fraction IF Threefold.Space U p q y := by
    intro x
    obtain ⟨U, _, hx, p, q, hq, he⟩ := local_representation IF Threefold.Space g ⟨x, by trivial⟩
    exact ⟨U, p, q, hx, hq, he⟩
  choose U p q hx hq he using hrep
  have hcover : (univ : Set Threefold.Space) ⊆
      ⋃ x : Threefold.Space, (U x : Set Threefold.Space) := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : Threefold.Space => (U x : Set Threefold.Space)) (fun x => (U x).isOpen) hcover
  let S : Set RiemannSphere := ⋃ x ∈ (s : Set Threefold.Space), denominatorBadValues (U x) (q x)
  have hS : S.Countable := s.countable_toSet.biUnion_iff.mpr
    (fun x _ => denominatorBadValues_countable (U x) (q x) (hq x))
  refine ⟨S, hS, ?_⟩
  intro z hz t
  obtain ⟨x, hxs, htx⟩ := mem_iUnion₂.mp
    (hs (mem_univ (regularTorusInclusionMap z t.val)))
  have hzq : regularSphereValue z ∉ denominatorBadValues (U x) (q x) := by
    intro hbad
    exact hz (mem_iUnion₂.mpr ⟨x, hxs, hbad⟩)
  exact ⟨{
    domain := U x
    le_domain := le_top
    mem_domain := htx
    numerator := p x
    denominator := q x
    denominator_ne_zero := hq x
    represents := he x
    pullback_denominator_ne_zero :=
      denominatorPullbackGerm_ne_zero (U x) (q x) z hzq ⟨t.val, htx⟩ }⟩

/-- One countable exceptional sphere-value set constructed from genuine
local fractions of the given global meromorphic function. -/
noncomputable def exceptionalValues (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    Set RiemannSphere := (exists_countable_exceptional_set g).choose

theorem exceptionalValues_countable (g : HolomorphicMeromorphic.Function IF Threefold.Space) :
    (exceptionalValues g).Countable := (exists_countable_exceptional_set g).choose_spec.1

/-- Actual admissibility is proved, rather than supplied, outside the
constructed countable exceptional set. -/
theorem regularTorus_admissible (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ exceptionalValues g) :
    PullbackAdmissible I₂ IF (regularTorusInclusionMap z) ⊤ g :=
  (exists_countable_exceptional_set g).choose_spec.2 z hz

/-- The genuine globally meromorphic restriction on the original period
torus, built from actual local pulled-back fractions. -/
noncomputable def regularTorusRestriction (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ exceptionalValues g) :
    HolomorphicMeromorphic.Function I₂ (RegularTorus z) :=
  admissiblePullbackSection I₂ IF (regularTorusInclusionMap z) ⊤ g (regularTorus_admissible g z hz)

theorem regularTorusRestriction_spec (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ exceptionalValues g) :
    IsAdmissiblePullback I₂ IF (regularTorusInclusionMap z) ⊤ g (regularTorusRestriction g z hz) :=
  admissiblePullbackSection_spec I₂ IF (regularTorusInclusionMap z) ⊤ g
    (regularTorus_admissible g z hz)

/-- Restriction agrees with every genuine local fraction whose denominator
pullback is nonzero at the given torus point, including denominator-value zeros. -/
theorem regularTorusRestriction_eq_fraction (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ exceptionalValues g)
    (U : Opens Threefold.Space) (p q : HolomorphicFunctionSheaf.Section IF Threefold.Space U)
    (hq : ∀ y : U, holomorphicGerm IF Threefold.Space U y q ≠ 0)
    (he : ∀ y : U, g ⟨y.val, by trivial⟩ = fraction IF Threefold.Space U p q y)
    (t : pullbackOpen I₂ IF (regularTorusInclusionMap z) U)
    (htq : holomorphicGerm I₂ (RegularTorus z)
      (pullbackOpen I₂ IF (regularTorusInclusionMap z) U) t
      (holomorphicPullback I₂ IF (regularTorusInclusionMap z) U q) ≠ 0) :
    regularTorusRestriction g z hz ⟨t.val, by trivial⟩ =
      fraction I₂ (RegularTorus z) (pullbackOpen I₂ IF (regularTorusInclusionMap z) U)
        (holomorphicPullback I₂ IF (regularTorusInclusionMap z) U p)
        (holomorphicPullback I₂ IF (regularTorusInclusionMap z) U q) t :=
  admissiblePullbackSection_eq_fraction I₂ IF (regularTorusInclusionMap z) ⊤ g
    (regularTorus_admissible g z hz) U le_top p q hq he t htq

theorem regularTorusRestriction_unique (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ exceptionalValues g)
    (t : HolomorphicMeromorphic.Function I₂ (RegularTorus z))
    (ht : IsAdmissiblePullback I₂ IF (regularTorusInclusionMap z) ⊤ g t) :
    t = regularTorusRestriction g z hz :=
  admissiblePullbackSection_unique I₂ IF (regularTorusInclusionMap z) ⊤ g
    (regularTorus_admissible g z hz) t ht

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicFibres
