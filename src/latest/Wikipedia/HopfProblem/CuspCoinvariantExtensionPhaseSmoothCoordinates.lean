import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyData
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothCoordinates
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealMaps

/-!
# Smooth native real period coordinates on the logarithmic cusp cover

The product rearrangement and inverse period matrix retain the original
covering-space charts. The gamma lift is their zeroth real coordinate.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase

open CuspUniformization SpecialPeriods.CuspFamily
open PeriodFamilyHolomorphicCohomology.Smooth

local notation "Ilog" => modelWithCornersSelf ℝ (ℂ × ComplexPlane₂)
local notation "IV" => modelWithCornersSelf ℝ RealPlane₄

/-- The native logarithmic-cover product rearrangement remains smooth
after restricting only the scalar field. -/
theorem logCoverProduct_contMDiff (radius : ℝ) :
    ContMDiff Ilog Ilog ∞ (logCoverProductEquiv radius) :=
  (CuspCircleNormalTrivialization.contMDiff_real_of_complex
    (logCoverProductEquiv_holomorphic radius)).of_le le_top

/-- Any original holomorphic period family has smooth inverse coordinates
on the native logarithmic cover. -/
theorem logInverseCoordinates_contMDiff (radius : ℝ)
    (P : HolomorphicPeriodMap ℂ (LogBase radius)) :
    ContMDiff Ilog IV ∞
      (fun p : LogCover radius =>
        (P.periodEquiv ⟨p.val.1, p.property⟩).symm p.val.2) := by
  have hdiff : ContDiffOn ℝ ∞ (inversePeriodCoordinates P) (logDomain radius) :=
    inversePeriodCoordinates_contDiffOn P
  have hcover : ContMDiff Ilog IV ∞
      (fun p : LogCover radius => inversePeriodCoordinates P p.val) := by
    intro p
    have h : ContMDiffAt Ilog IV ∞ (inversePeriodCoordinates P) p.val :=
      (hdiff.contDiffAt ((logDomain radius).isOpen.mem_nhds p.property)).contMDiffAt
    exact h.comp p contMDiff_subtype_val.contMDiffAt
  exact hcover.congr fun p =>
    (inversePeriodCoordinates_apply P ⟨p.val.1, p.property⟩ p.val.2).symm

/-- The genuine inverse period coordinates are jointly smooth on the
original logarithmic cover. -/
theorem logInversePeriod_contMDiff (D : Data) :
    ContMDiff Ilog IV ∞
      (fun p : LogCover D.radius =>
        (D.periods.periodEquiv ⟨p.val.1, p.property⟩).symm p.val.2) :=
  logInverseCoordinates_contMDiff D.radius D.periods

/-- The literal gamma coordinate is jointly real smooth in the original
logarithmic-cover chart. -/
theorem logGamma_contMDiff (D : Data) :
    ContMDiff Ilog 𝓘(ℝ, ℝ) ∞
      (fun p : LogCover D.radius =>
        ((D.periods.periodEquiv ⟨p.val.1, p.property⟩).symm p.val.2) 0) :=
  (contDiff_apply ℝ ℝ (0 : Fin 4)).contMDiff.comp (logInversePeriod_contMDiff D)

end Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase
