import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenMorseSublevel
import Wikipedia.HopfProblem.DegreeCollapseRegularSublevelHandleChain
import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainDimension

/-!
# The literal collared half has a full native smooth-boundary handle chain

The chain's terminal body is the original half, with its unchanged
topology. Its boundary carries the independently constructed native
regular-level atlas. The identity on ambient points is proved to be a
diffeomorphism from the state's original regular-fiber boundary atlas.
The whole-body and boundary point identities are retained.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}

namespace ExcellentMorsePresentation

variable (P : S.ExcellentMorsePresentation)

def sublevelBody : SmoothBoundaryBody 𝓘(ℝ, RegularLevel.Model (Vector 7)) :=
  RegularMorseSublevel.body P.sublevelFunction_smooth 0
    (RegularTimeMorse.regular_zero_not_critical P.sublevelFunction_regular)

def halfBody : SmoothBoundaryBody 𝓘(ℝ, RegularLevel.Model (Vector 7)) := by
  let _ := S.compactSpace_half
  let i : C(P.sublevelBody.boundary, S.Half) :=
    P.halfSublevelHomeomorph.symm.toHomotopyEquiv.toFun.comp P.sublevelBody.inclusion
  exact SmoothBoundaryBody.ofEmbedding i
    (P.halfSublevelHomeomorph.symm.isClosedEmbedding.comp P.sublevelBody.closedEmbedding)

def sublevelHalfBodyEquiv : SmoothBoundaryBody.Equiv P.sublevelBody P.halfBody where
  body := P.halfSublevelHomeomorph.symm
  boundary := Diffeomorph.refl 𝓘(ℝ, RegularLevel.Model (Vector 7)) P.sublevelBody.boundary ∞
  boundary_point _ := rfl

theorem halfBody_inclusion_point (p : P.halfBody.boundary) :
    (P.halfBody.inclusion p).val = p.val := rfl

def halfBodyBoundaryDiffeomorph : letI := S.zeroAtlas;
    S.Zero ≃ₘ⟮𝓡 6, 𝓘(ℝ, RegularLevel.Model (Vector 7))⟯ P.halfBody.boundary := by
  let _ := S.zeroAtlas
  let ha := RegularTimeMorse.regular_zero_not_critical P.sublevelFunction_regular
  let _ := RegularLevel.chartedSpace P.sublevelFunction_smooth ha
  let F : S.Zero → P.halfBody.boundary := fun p ↦
    ⟨p.val, neg_eq_zero.mpr ((P.zero_iff p.val).mpr p.property)⟩
  let G : P.halfBody.boundary → S.Zero := fun p ↦
    ⟨p.val, (P.zero_iff p.val).mp (neg_eq_zero.mp p.property)⟩
  refine
    { toFun := F
      invFun := G
      left_inv := fun _ ↦ Subtype.ext rfl
      right_inv := fun _ ↦ Subtype.ext rfl
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply (RegularLevel.contMDiff_iff_inclusion P.sublevelFunction_smooth ha (𝓡 6) F).mpr
    exact regularFiber_contMDiff_subtype_val S.zeroTimeMap S.time_smooth 0 S.time_regular 6 (by simp)
  · apply (regularFiber_contMDiff_iff_ambient
      S.zeroTimeMap S.time_smooth 0 S.time_regular 6 (by simp) G).mpr
    exact RegularLevel.contMDiff_inclusion P.sublevelFunction_smooth ha

theorem halfBodyBoundaryDiffeomorph_point (p : S.Zero) : letI := S.zeroAtlas;
    (P.halfBodyBoundaryDiffeomorph p).val = p.val := rfl

theorem halfBodyBoundaryDiffeomorph_inclusion (p : S.Zero) : letI := S.zeroAtlas;
    (P.halfBody.inclusion (P.halfBodyBoundaryDiffeomorph p)).val = p.val := rfl

theorem exists_fullSmoothHandleChain :
    ∃ (k : ℕ) (c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model (Vector 7)) 7
      (SmoothBoundaryBody.empty 𝓘(ℝ, RegularLevel.Model (Vector 7))) P.halfBody k),
      c.HasStandardCaps := by
  obtain ⟨k, c, hc⟩ := RegularMorseSublevel.exists_fullSmoothHandleChain
    P.sublevelFunction_smooth P.sublevelFunction_morse P.sublevelFunction_distinct 0
    (RegularTimeMorse.regular_zero_not_critical P.sublevelFunction_regular)
  have hd : Module.finrank ℝ (Vector 7) = 7 := by simp
  exact ⟨k, (c.castDimension hd).retarget P.sublevelHalfBodyEquiv,
    (c.castDimension hd).hasStandardCaps_retarget P.sublevelHalfBodyEquiv
      (c.hasStandardCaps_castDimension hd hc)⟩

end ExcellentMorsePresentation
end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
