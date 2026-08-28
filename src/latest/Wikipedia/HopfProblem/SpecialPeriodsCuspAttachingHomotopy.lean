import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingSection

/-!
# Based contraction of the actual regular zero section near the cusp

The gluing identifies the regular zero section on the attaching region
with the section extending over the full cusp disc.  Affine contraction
in that disc gives an actual endpoint-preserving null-homotopy in the
constructed threefold, entirely inside its cusp patch.
-/

noncomputable section

open Set
open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

open Triangle

/-- The based affine disc contraction, followed by the actual extended
section, contracts every regular-section loop on the attaching region. -/
def attachedRegularSectionLoopContraction {b : OverlapBase} (p : Path b b) :
    (p.map attachedRegularSection_continuous).Homotopy
      (Path.refl (attachedRegularSection b)) := by
  let H := CuspQuotient.discLoopContraction (p.map overlapCoordinate_continuous)
  refine {
    toFun := fun u => extendedSection (H u)
    continuous_toFun := extendedSection_continuous.comp H.continuous
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · intro t
    exact (congrArg extendedSection (H.map_zero_left t)).trans
      (attachedRegularSection_eq_extended (p t)).symm
  · intro t
    exact (congrArg extendedSection (H.map_one_left t)).trans
      (attachedRegularSection_eq_extended b).symm
  · intro r t ht
    rcases ht with rfl | rfl
    · exact (congrArg extendedSection (Path.Homotopy.source H r)).trans
        ((attachedRegularSection_eq_extended b).symm.trans
          (congrArg attachedRegularSection p.source.symm))
    · exact (congrArg extendedSection (Path.Homotopy.target H r)).trans
        ((attachedRegularSection_eq_extended b).symm.trans
          (congrArg attachedRegularSection p.target.symm))

@[simp] theorem attachedRegularSectionLoopContraction_apply
    {b : OverlapBase} (p : Path b b) (u : I × I) :
    attachedRegularSectionLoopContraction p u =
      extendedSection
        (CuspQuotient.discLoopContraction (p.map overlapCoordinate_continuous) u) := rfl

/-- Every intermediate point remains in the literal cusp patch of the gluing. -/
theorem attachedRegularSectionLoopContraction_mem_cuspPatch
    {b : OverlapBase} (p : Path b b) (u : I × I) :
    attachedRegularSectionLoopContraction p u ∈ liftedPatch (some none) :=
  extendedSection_mem_cuspPatch
    (CuspQuotient.discLoopContraction (p.map overlapCoordinate_continuous) u)

/-- The based attaching loop in the actual regular section is null-homotopic. -/
theorem attachedRegularSection_loop_nullhomotopic {b : OverlapBase} (p : Path b b) :
    Path.Homotopic (p.map attachedRegularSection_continuous)
      (Path.refl (attachedRegularSection b)) :=
  ⟨attachedRegularSectionLoopContraction p⟩

/-- The actual homomorphism induced by the attached regular zero section is trivial. -/
theorem attachedRegularSection_fundamentalGroup_map_eq_one (b : OverlapBase)
    (γ : FundamentalGroup OverlapBase b) :
    FundamentalGroup.map
      ⟨attachedRegularSection, attachedRegularSection_continuous⟩ b γ = 1 := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk p =>
    exact Path.Homotopic.Quotient.eq.mpr (attachedRegularSection_loop_nullhomotopic p)

/-- A regular-base loop that stays over the cusp patch, regarded as a literal
loop in the attaching region. -/
def regularLoopInOverlap {b : regularPatch}
    (hb : (b : TriangleCompactifiedOrbitSpace) ∈ specialBaseCover.fillingPatch none)
    (p : Path b b)
    (hp : ∀ t, (p t : TriangleCompactifiedOrbitSpace) ∈ specialBaseCover.fillingPatch none) :
    Path (⟨b, hb⟩ : OverlapBase) ⟨b, hb⟩ where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] theorem regularLoopInOverlap_val {b : regularPatch}
    (hb : (b : TriangleCompactifiedOrbitSpace) ∈ specialBaseCover.fillingPatch none)
    (p : Path b b)
    (hp : ∀ t, (p t : TriangleCompactifiedOrbitSpace) ∈ specialBaseCover.fillingPatch none)
    (t : I) : (regularLoopInOverlap hb p hp t : regularPatch) = p t := rfl

theorem regularLoopInOverlap_map {b : regularPatch}
    (hb : (b : TriangleCompactifiedOrbitSpace) ∈ specialBaseCover.fillingPatch none)
    (p : Path b b)
    (hp : ∀ t, (p t : TriangleCompactifiedOrbitSpace) ∈ specialBaseCover.fillingPatch none) :
    (regularLoopInOverlap hb p hp).map attachedRegularSection_continuous =
      p.map regularSection_continuous := by
  ext t
  rfl

/-- Based contraction for a loop supplied directly in the regular base.
Only its actual containment in the cusp patch is required. -/
def regularSectionLoopContraction_of_mem {b : regularPatch} (p : Path b b)
    (hp : ∀ t, (p t : TriangleCompactifiedOrbitSpace) ∈ specialBaseCover.fillingPatch none) :
    (p.map regularSection_continuous).Homotopy (Path.refl (regularSection b)) := by
  have hb : (b : TriangleCompactifiedOrbitSpace) ∈ specialBaseCover.fillingPatch none := by
    simpa only [p.source] using hp 0
  exact (attachedRegularSectionLoopContraction (regularLoopInOverlap hb p hp)).cast
    (regularLoopInOverlap_map hb p hp) rfl

/-- The contraction of an arbitrary contained regular-base loop also stays
in the actual cusp patch throughout. -/
theorem regularSectionLoopContraction_of_mem_mem_cuspPatch
    {b : regularPatch} (p : Path b b)
    (hp : ∀ t, (p t : TriangleCompactifiedOrbitSpace) ∈ specialBaseCover.fillingPatch none)
    (u : I × I) : regularSectionLoopContraction_of_mem p hp u ∈ liftedPatch (some none) :=
  attachedRegularSectionLoopContraction_mem_cuspPatch (regularLoopInOverlap _ p hp) u

/-- Every actual regular-section loop lying over the cusp filling is based
null-homotopic after inclusion in the constructed threefold. -/
theorem regularSection_loop_nullhomotopic_of_mem {b : regularPatch} (p : Path b b)
    (hp : ∀ t, (p t : TriangleCompactifiedOrbitSpace) ∈ specialBaseCover.fillingPatch none) :
    Path.Homotopic (p.map regularSection_continuous) (Path.refl (regularSection b)) :=
  ⟨regularSectionLoopContraction_of_mem p hp⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching
