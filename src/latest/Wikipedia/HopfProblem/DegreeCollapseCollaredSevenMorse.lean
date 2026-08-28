import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenFilling
import Wikipedia.HopfProblem.DegreeCollapseRegularTimeMorseFunction

/-!
# The same actual collared half has a native Morse presentation

The constructed Morse time has exactly the original zero fiber and
positive half, and agrees with the original time near every boundary
point. Identity maps on ambient points are proved diffeomorphisms for
the independently constructed native superlevel and regular-fiber atlases.
This prepares a handle decomposition without replacing the filling's
topology or its original boundary smooth structure.
-/

noncomputable section

open Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

structure MorsePresentation where
  function : C(S.Space, ℝ)
  smooth : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ function
  morse : IsMorse (Vector 7) function
  regular : ∀ p, function p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) function p)
  zero_iff : ∀ p, function p = 0 ↔ S.time p = 0
  nonnegative_iff : ∀ p, 0 ≤ function p ↔ 0 ≤ S.time p
  positive_iff : ∀ p, 0 < function p ↔ 0 < S.time p
  boundary_germ : ∀ p, S.time p = 0 → function =ᶠ[𝓝 p] S.time

theorem nonempty_morsePresentation : Nonempty S.MorsePresentation := by
  obtain ⟨g, hg, hm, hgerm, hzero, hhalf, hpos, hreg⟩ :=
    RegularTimeMorse.exists_morse_preserving_zero S.time_smooth S.time_regular
  exact ⟨⟨⟨g, hg.continuous⟩, hg, hm, hreg, hzero, hhalf, hpos, hgerm⟩⟩

def morsePresentation : S.MorsePresentation := Classical.choice S.nonempty_morsePresentation

namespace MorsePresentation

variable {S} (P : S.MorsePresentation)

def halfAtlas : SuperlevelAtlas (K := Vector 6) (𝓡 7) P.function :=
  Classical.choice (nonempty_superlevelAtlas P.smooth P.regular 6 (by simp))

def halfDiffeomorph : letI := S.halfChartedSpace; letI := P.halfAtlas.chartedSpace;
    S.Half ≃ₘ⟮ProductHalfSpace.model (Vector 6), ProductHalfSpace.model (Vector 6)⟯
      {p : S.Space // 0 ≤ P.function p} := by
  let := S.halfChartedSpace
  let := P.halfAtlas.chartedSpace
  refine
    { toFun := fun p ↦ ⟨p.val, (P.nonnegative_iff p.val).mpr p.property⟩
      invFun := fun p ↦ ⟨p.val, (P.nonnegative_iff p.val).mp p.property⟩
      left_inv := fun p ↦ Subtype.ext rfl
      right_inv := fun p ↦ Subtype.ext rfl
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply (P.halfAtlas.contMDiff_iff_ambient _).mpr
    exact S.contMDiff_halfInclusion
  · apply (S.halfAtlas.contMDiff_iff_ambient _).mpr
    exact P.halfAtlas.contMDiff_subtype_val

theorem halfDiffeomorph_point (p : S.Half) :
    letI := S.halfChartedSpace; letI := P.halfAtlas.chartedSpace;
    (P.halfDiffeomorph p).val = p.val := rfl

@[instance_reducible]
def zeroAtlas : ChartedSpace (Vector 6) {p : S.Space // P.function p = 0} :=
  regularFiberAtlas P.function P.smooth 0 P.regular 6 (by simp)

def zeroDiffeomorph : letI := S.zeroAtlas; letI := P.zeroAtlas;
    S.Zero ≃ₘ⟮𝓡 6, 𝓡 6⟯ {p : S.Space // P.function p = 0} := by
  let := S.zeroAtlas
  let := P.zeroAtlas
  refine
    { toFun := fun p ↦ ⟨p.val, (P.zero_iff p.val).mpr p.property⟩
      invFun := fun p ↦ ⟨p.val, (P.zero_iff p.val).mp p.property⟩
      left_inv := fun p ↦ Subtype.ext rfl
      right_inv := fun p ↦ Subtype.ext rfl
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply (regularFiber_contMDiff_iff_ambient P.function P.smooth 0 P.regular 6 (by simp) _).mpr
    exact regularFiber_contMDiff_subtype_val S.zeroTimeMap S.time_smooth 0 S.time_regular 6 (by simp)
  · apply (regularFiber_contMDiff_iff_ambient
      S.zeroTimeMap S.time_smooth 0 S.time_regular 6 (by simp) _).mpr
    exact regularFiber_contMDiff_subtype_val P.function P.smooth 0 P.regular 6 (by simp)

theorem zeroDiffeomorph_point (p : S.Zero) : letI := S.zeroAtlas; letI := P.zeroAtlas;
    (P.zeroDiffeomorph p).val = p.val := rfl

end MorsePresentation
end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
