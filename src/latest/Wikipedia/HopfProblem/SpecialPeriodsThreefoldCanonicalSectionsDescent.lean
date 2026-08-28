import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackDiffeomorphBundle

/-!
# Descent of genuine canonical sections

A section upstairs descends through a surjective local biholomorphism when
its inverse derivative pullbacks agree over every fibre.  The construction
uses equality transport between actual canonical fibres.  Compatibility
proves independence of the chosen preimage, uniqueness, and exact agreement
of zero loci.  Holomorphicity is proved separately using native local inverses.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsDescent

open _root_.Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.Pullback

local notation "I" => modelWithCornersSelf ℂ Model

/-- A section of the actual canonical line bundle. -/
abbrev Section (M : Type*) [TopologicalSpace M] [ChartedSpace Model M]
    [IsManifold I ω M] := (x : M) → (Atlas.core M).Fiber x

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
  [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N]

/-- A canonical section as a map to its original bundle total space. -/
def sectionMap (s : Section M) (x : M) : (Atlas.core M).TotalSpace := ⟨x, s x⟩

@[simp] theorem sectionMap_proj (s : Section M) (x : M) :
    (sectionMap s x).proj = x := rfl

/-- Differential compatibility over the fibres of the actual base map. -/
def Compatible {q : M → N} (hq : IsLocalDiffeomorph I I ω q) (s : Section M) : Prop :=
  ∀ x y, q x = q y → forwardMap hq (sectionMap s x) = forwardMap hq (sectionMap s y)

private theorem mk_fiberTransport {x y : N} (h : x = y)
    (v : (Atlas.core N).Fiber x) :
    (⟨y, fiberTransport h v⟩ : (Atlas.core N).TotalSpace) = ⟨x, v⟩ := by
  subst y
  rfl

/-- Equality of total vectors over equal points is precisely equality after
the genuine equality-induced fibre transport. -/
theorem fiberTransport_eq_iff_totalSpace_eq {x y : N} (h : x = y)
    (v : (Atlas.core N).Fiber x) (w : (Atlas.core N).Fiber y) :
    fiberTransport h v = w ↔ (⟨x, v⟩ : (Atlas.core N).TotalSpace) = ⟨y, w⟩ := by
  subst y
  change v = w ↔ (⟨x, v⟩ : (Atlas.core N).TotalSpace) = ⟨x, w⟩
  constructor
  · exact congrArg (Bundle.TotalSpace.mk x)
  · exact congrArg (fun p : (Atlas.core N).TotalSpace => id (α := ℂ) p.2)

theorem compatible_iff_fiberTransport {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (s : Section M) :
    Compatible hq s ↔ ∀ x y (h : q x = q y),
      fiberTransport h ((pullbackEquiv hq x).symm (s x)) =
        (pullbackEquiv hq y).symm (s y) := by
  constructor
  · intro hs x y h
    exact (fiberTransport_eq_iff_totalSpace_eq h _ _).mpr (hs x y h)
  · intro hs x y h
    exact (fiberTransport_eq_iff_totalSpace_eq h _ _).mp (hs x y h)

/-- Select a genuine preimage using surjectivity; no regularity is asserted
for this choice.  The descended section's regularity follows from descent. -/
def chosenPreimage {q : M → N} (hsurj : Function.Surjective q) (y : N) : M :=
  Classical.choose (hsurj y)

omit [TopologicalSpace M] [ChartedSpace Model M] [IsManifold I ω M]
  [TopologicalSpace N] [ChartedSpace Model N] [IsManifold I ω N] in
theorem chosenPreimage_spec {q : M → N} (hsurj : Function.Surjective q) (y : N) :
    q (chosenPreimage hsurj y) = y := Classical.choose_spec (hsurj y)

/-- Transport the pushed-forward upstairs vector to the literal fibre over
the requested downstairs point. -/
def descendedSection {q : M → N} (hq : IsLocalDiffeomorph I I ω q)
    (hsurj : Function.Surjective q) (s : Section M) (y : N) : (Atlas.core N).Fiber y :=
  fiberTransport (chosenPreimage_spec hsurj y)
    ((pullbackEquiv hq (chosenPreimage hsurj y)).symm (s (chosenPreimage hsurj y)))

theorem descendedSectionMap_chosenPreimage {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : Section M) (y : N) :
    sectionMap (descendedSection hq hsurj s) y =
      forwardMap hq (sectionMap s (chosenPreimage hsurj y)) :=
  mk_fiberTransport (chosenPreimage_spec hsurj y) _

/-- The defining descent diagram commutes at every upstairs point. -/
theorem descendedSectionMap_at_image {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : Section M) (hs : Compatible hq s) (x : M) :
    sectionMap (descendedSection hq hsurj s) (q x) =
      forwardMap hq (sectionMap s x) :=
  (descendedSectionMap_chosenPreimage hq hsurj s (q x)).trans
    (hs (chosenPreimage hsurj (q x)) x (chosenPreimage_spec hsurj (q x)))

/-- The descended vector is the inverse derivative pullback of the
upstairs vector, independently of the selected preimage. -/
theorem descendedSection_at_image {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : Section M) (hs : Compatible hq s) (x : M) :
    descendedSection hq hsurj s (q x) = (pullbackEquiv hq x).symm (s x) :=
  congrArg (fun p : (Atlas.core N).TotalSpace => id (α := ℂ) p.2)
    (descendedSectionMap_at_image hq hsurj s hs x)

/-- Pulling the descended section back by the actual manifold derivative
recovers the original section exactly. -/
theorem pullback_descendedSection {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : Section M) (hs : Compatible hq s) (x : M) :
    pullbackEquiv hq x (descendedSection hq hsurj s (q x)) = s x :=
  (congrArg (pullbackEquiv hq x) (descendedSection_at_image hq hsurj s hs x)).trans
    ((pullbackEquiv hq x).apply_symm_apply (s x))

theorem descendedSection_zero_iff_at_image {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : Section M) (hs : Compatible hq s) (x : M) :
    descendedSection hq hsurj s (q x) = 0 ↔ s x = 0 := by
  rw [descendedSection_at_image hq hsurj s hs x]
  exact (pullbackEquiv hq x).symm.map_eq_zero_iff

theorem descendedSection_ne_zero_iff_at_image {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : Section M) (hs : Compatible hq s) (x : M) :
    descendedSection hq hsurj s (q x) ≠ 0 ↔ s x ≠ 0 :=
  not_congr (descendedSection_zero_iff_at_image hq hsurj s hs x)

/-- The actual zero locus pulls back to precisely the upstairs zero locus. -/
theorem descendedSection_zeroLocus_preimage {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : Section M) (hs : Compatible hq s) :
    q ⁻¹' {y | descendedSection hq hsurj s y = 0} = {x | s x = 0} := by
  ext x
  exact descendedSection_zero_iff_at_image hq hsurj s hs x

theorem descendedSection_nowhere_zero_iff {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : Section M) (hs : Compatible hq s) :
    (∀ y, descendedSection hq hsurj s y ≠ 0) ↔ ∀ x, s x ≠ 0 := by
  constructor
  · intro h x
    exact (descendedSection_ne_zero_iff_at_image hq hsurj s hs x).mp (h (q x))
  · intro h y
    obtain ⟨x, rfl⟩ := hsurj y
    exact (descendedSection_ne_zero_iff_at_image hq hsurj s hs x).mpr (h x)

/-- A section satisfying the actual pullback equation is unique. -/
theorem descendedSection_unique {q : M → N}
    (hq : IsLocalDiffeomorph I I ω q) (hsurj : Function.Surjective q)
    (s : Section M) (hs : Compatible hq s) (t : Section N)
    (ht : ∀ x, pullbackEquiv hq x (t (q x)) = s x) :
    t = descendedSection hq hsurj s := by
  funext y
  obtain ⟨x, rfl⟩ := hsurj y
  apply (pullbackEquiv hq x).injective
  exact (ht x).trans (pullback_descendedSection hq hsurj s hs x).symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical.SectionsDescent
