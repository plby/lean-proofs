import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsNative

/-!
# Actual holomorphic section spaces under native bundle comparisons

The genuine cross-cover bundle biholomorphism induces a complex-linear
equivalence on the spaces of actual native holomorphic sections.  Its
value at each base point is the original continuous-linear fibre map.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.CrossGauge

open HolomorphicCharacterBundle

variable {M ι κ : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] {I : ModelWithCorners ℂ E H}
  {A : TransitionData M ι} {B : TransitionData M κ}
  [A.IsHolomorphic I] [B.IsHolomorphic I] (G : CrossGauge I A B)

/-- Sending an actual section through the original holomorphic
bundle map remains a holomorphic section of the original target. -/
def mapSection (s : ContMDiffSection I ℂ ω A.core.Fiber) :
    ContMDiffSection I ℂ ω B.core.Fiber where
  toFun x := G.fiberEquiv x (s x)
  contMDiff_toFun := G.diffeomorph.contMDiff.comp s.contMDiff

/-- The actual inverse fibre maps give the inverse operation on sections. -/
def invMapSection (s : ContMDiffSection I ℂ ω B.core.Fiber) :
    ContMDiffSection I ℂ ω A.core.Fiber where
  toFun x := (G.fiberEquiv x).symm (s x)
  contMDiff_toFun := G.diffeomorph.symm.contMDiff.comp s.contMDiff

@[simp] theorem mapSection_apply (s : ContMDiffSection I ℂ ω A.core.Fiber) (x : M) :
    G.mapSection s x = G.fiberEquiv x (s x) := rfl

@[simp] theorem invMapSection_apply (s : ContMDiffSection I ℂ ω B.core.Fiber) (x : M) :
    G.invMapSection s x = (G.fiberEquiv x).symm (s x) := rfl

/-- A linear equivalence of the full native holomorphic section spaces,
not merely a correspondence between selected local coefficients. -/
def sectionLinearEquiv : ContMDiffSection I ℂ ω A.core.Fiber ≃ₗ[ℂ]
    ContMDiffSection I ℂ ω B.core.Fiber where
  toFun := G.mapSection
  invFun := G.invMapSection
  left_inv s := by
    apply ContMDiffSection.ext
    intro x
    exact (G.fiberEquiv x).symm_apply_apply (s x)
  right_inv s := by
    apply ContMDiffSection.ext
    intro x
    exact (G.fiberEquiv x).apply_symm_apply (s x)
  map_add' s t := by
    apply ContMDiffSection.ext
    intro x
    exact (G.fiberEquiv x).map_add (s x) (t x)
  map_smul' c s := by
    apply ContMDiffSection.ext
    intro x
    exact (G.fiberEquiv x).map_smul c (s x)

@[simp] theorem sectionLinearEquiv_apply (s : ContMDiffSection I ℂ ω A.core.Fiber) (x : M) :
    G.sectionLinearEquiv s x = G.fiberEquiv x (s x) := rfl

include G

/-- Vanishing of every target section implies vanishing of every
source section through the genuine linear equivalence. -/
theorem sections_zero_of_target
    (hzero : ∀ s : ContMDiffSection I ℂ ω B.core.Fiber, s = 0)
    (s : ContMDiffSection I ℂ ω A.core.Fiber) : s = 0 := by
  apply (G.sectionLinearEquiv).injective
  rw [map_zero]
  exact hzero _

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.CrossGauge
