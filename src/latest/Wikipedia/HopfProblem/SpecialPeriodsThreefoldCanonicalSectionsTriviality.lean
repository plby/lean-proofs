import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsRestriction
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsFrameTrivialization

/-!
# The actual canonical trivialization of the first elliptic filling

The constructed nowhere-zero section gives a holomorphic fibrewise-linear
product trivialization of the original ambient canonical bundle.  The
inverse sends a scalar to that scalar times the actual descended section.
The generator criterion for either filling is expressed by the span of
the genuine vector in its actual canonical fibre.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "Iᴷ" => ModelWithCorners.prod
  (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace

local instance trivialityFullManifold (j : Kind) : IsManifold IF ω (SpecialFullFilling j) :=
  (specialFullFilling_construction j).2.2.1

local instance trivialitySmallManifold (j : Kind) : IsManifold IF ω (SpecialEllipticPiece j) :=
  specialEllipticPiece_isManifold j

/-- The first full ambient canonical bundle is genuinely holomorphically trivial. -/
def fullThreeTrivialization :
    Diffeomorph Iᴷ Iᴷ (Elliptic.fullBundle .three).TotalSpace (SpecialFullFilling .three × ℂ) ω :=
  SectionsFrameTrivialization.bundleBiholomorph (fullHolomorphicSection .three)
    fullSection_three_ne_zero

@[simp] theorem fullThreeTrivialization_fst (p : (Elliptic.fullBundle .three).TotalSpace) :
    (fullThreeTrivialization p).1 = p.proj := rfl

@[simp] theorem fullThreeTrivialization_symm (x : SpecialFullFilling .three) (c : ℂ) :
    fullThreeTrivialization.symm (x, c) = ⟨x, c • fullSection .three x⟩ := rfl

@[simp] theorem fullThreeTrivialization_section (x : SpecialFullFilling .three) :
    fullThreeTrivialization (fullSectionMap .three x) = (x, 1) :=
  SectionsFrameTrivialization.bundleBiholomorph_section (fullHolomorphicSection .three)
    fullSection_three_ne_zero x

/-- The same genuine trivialization on the actual small first filling. -/
def smallThreeTrivialization :
    Diffeomorph Iᴷ Iᴷ (Elliptic.bundle .three).TotalSpace (SpecialEllipticPiece .three × ℂ) ω :=
  SectionsFrameTrivialization.bundleBiholomorph (smallHolomorphicSection .three)
    smallSection_three_ne_zero

@[simp] theorem smallThreeTrivialization_fst (p : (Elliptic.bundle .three).TotalSpace) :
    (smallThreeTrivialization p).1 = p.proj := rfl

@[simp] theorem smallThreeTrivialization_symm (x : SpecialEllipticPiece .three) (c : ℂ) :
    smallThreeTrivialization.symm (x, c) = ⟨x, c • smallSection .three x⟩ := rfl

@[simp] theorem smallThreeTrivialization_section (x : SpecialEllipticPiece .three) :
    smallThreeTrivialization (smallSectionMap .three x) = (x, 1) :=
  SectionsFrameTrivialization.bundleBiholomorph_section (smallHolomorphicSection .three)
    smallSection_three_ne_zero x

/-- The actual canonical vector spans its fibre exactly where it is nonzero. -/
theorem fullSection_generates_iff_nonzero (j : Kind) (x : SpecialFullFilling j) :
    Submodule.span ℂ ({fullSection j x} : Set ((Elliptic.fullBundle j).Fiber x)) = ⊤ ↔
      fullSection j x ≠ 0 := by
  rw [Submodule.span_singleton_eq_top_iff]
  constructor
  · intro h hz
    obtain ⟨c, hc⟩ := h (1 : ℂ)
    apply one_ne_zero (α := ℂ)
    have hc' := congrArg (id (α := ℂ)) hc
    rw [hz, smul_zero] at hc'
    exact hc'.symm
  · intro hs w
    refine ⟨id (α := ℂ) w / id (α := ℂ) (fullSection j x), ?_⟩
    change (id (α := ℂ) w / id (α := ℂ) (fullSection j x)) *
      id (α := ℂ) (fullSection j x) = id (α := ℂ) w
    exact div_mul_cancel₀ _ hs

/-- For the second filling the canonical section generates exactly off
the central surface; for the first it generates everywhere. -/
theorem fullSection_generates_iff (j : Kind) (x : SpecialFullFilling j) :
    Submodule.span ℂ ({fullSection j x} : Set ((Elliptic.fullBundle j).Fiber x)) = ⊤ ↔
      SectionsUnit.vanishingOrder j = 0 ∨
        specialFullFillingProjection j x ≠ Wikipedia.HopfProblem.Elliptic.discZero :=
  (fullSection_generates_iff_nonzero j x).trans (fullSection_ne_zero_iff j x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Sections
