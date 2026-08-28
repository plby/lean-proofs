import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDescentPullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldZeroSection
import Wikipedia.HopfProblem.TriangleUniformizationGluingRemovablePointsFinite

/-!
# Actual holomorphic descent along the sphere projection

On the regular base, the actual zero section proves that the continuous
descended function is holomorphic. The three remaining values are
removable by continuity. Thus actual pullback identifies the holomorphic
section algebras on every base open set with those on its full preimage.
No Stein factorization or higher-direct-image theorem is assumed.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

theorem descendedFunction_restrict_regular_holomorphic (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun b : sphereRegularPart U => descendedFunction U f b.val) := by
  have he : (fun b : sphereRegularPart U => descendedFunction U f b.val) =
      f ∘ sphereRegularZeroSectionOn U := by
    funext b
    simpa only [baseProjection, sphereRegularZeroSectionOn_projection,
      Function.comp_apply] using
      descendedFunction_projection U f hf (sphereRegularZeroSectionOn U b)
  rw [he]
  exact hf.comp (sphereRegularZeroSectionOn_holomorphic U)

theorem descendedFunction_holomorphicAt_regular (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f)
    (b : U) (hb : (b : RiemannSphere) ∈ sphereRegularPatch) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (descendedFunction U f) b := by
  have h := descendedFunction_restrict_regular_holomorphic U f hf
    (⟨b, hb⟩ : sphereRegularPart U)
  exact (contMDiffAt_subtype_iff (U := sphereRegularPart U)
    (f := descendedFunction U f) (x := ⟨b, hb⟩)).mp h

/-- Holomorphicity at the three exceptional values follows from the
proved continuous descent and actual finite-puncture removability. -/
theorem descendedFunction_holomorphic (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (descendedFunction U f) := by
  let S : Set U := Subtype.val ⁻¹'
    ({(∞ : RiemannSphere), ((0 : ℂ) : RiemannSphere), ((1 : ℂ) : RiemannSphere)} :
      Set RiemannSphere)
  have hS : S.Finite :=
    (((finite_singleton ((1 : ℂ) : RiemannSphere)).insert
      ((0 : ℂ) : RiemannSphere)).insert (∞ : RiemannSphere)).preimage
      Subtype.val_injective.injOn
  apply TriangleUniformizationGluing.contMDiff_of_continuous_of_finite
    (descendedFunction_continuous U f hf) hS
  intro b hb
  apply descendedFunction_holomorphicAt_regular U f hf b
  exact hb

theorem exists_unique_holomorphic_descent (U : Opens RiemannSphere)
    (f : basePreimage U → ℂ) (hf : ContMDiff IF 𝓘(ℂ) ω f) :
    ∃! g : U → ℂ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g ∧ g ∘ baseProjection U = f := by
  refine ⟨descendedFunction U f,
    ⟨descendedFunction_holomorphic U f hf, descendedFunction_comp_projection U f hf⟩, ?_⟩
  intro g hg
  exact descendedFunction_unique U f g hg.2

def descendedSection (U : Opens RiemannSphere) (f : PreimageSection U) : BaseSection U :=
  ⟨descendedFunction U f, descendedFunction_holomorphic U f f.contMDiff⟩

@[simp] theorem descendedSection_apply (U : Opens RiemannSphere)
    (f : PreimageSection U) (b : U) :
    descendedSection U f b = descendedFunction U f b := rfl

@[simp] theorem pullbackSection_descendedSection (U : Opens RiemannSphere)
    (f : PreimageSection U) : pullbackSection U (descendedSection U f) = f := by
  apply ContMDiffMap.ext
  intro x
  exact descendedFunction_projection U f f.contMDiff x

theorem pullbackSection_surjective (U : Opens RiemannSphere) :
    Function.Surjective (pullbackSection U) :=
  fun f => ⟨descendedSection U f, pullbackSection_descendedSection U f⟩

/-- Actual pullback is an isomorphism of holomorphic section algebras
on every original base open set. -/
def pullbackSectionEquiv (U : Opens RiemannSphere) :
    BaseSection U ≃ₐ[ℂ] PreimageSection U :=
  AlgEquiv.ofBijective (pullbackSection U)
    ⟨pullbackSection_injective U, pullbackSection_surjective U⟩

@[simp] theorem pullbackSectionEquiv_apply (U : Opens RiemannSphere)
    (f : BaseSection U) : pullbackSectionEquiv U f = pullbackSection U f := rfl

@[simp] theorem pullbackSectionEquiv_symm_apply (U : Opens RiemannSphere)
    (f : PreimageSection U) : (pullbackSectionEquiv U).symm f = descendedSection U f := by
  apply (pullbackSectionEquiv U).injective
  rw [AlgEquiv.apply_symm_apply, pullbackSectionEquiv_apply,
    pullbackSection_descendedSection]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold
