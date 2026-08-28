import Wikipedia.NoExoticSixSphere.SquareDoubleSmooth
import Wikipedia.HopfProblem.DegreeCollapseCompactFundamentalGroupFinite
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenPiOneSuccessor

/-!
# Finite generation of the actual half's fundamental group through the smooth double

The square-root section lifts every original loop. The compact native
smooth double has finitely generated fundamental group by the checked
Morse-theoretic theorem. Its actual projection therefore gives finite
generation for the original half. Only connectedness of the half and a
point on its zero seam are needed; the seam may be disconnected.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SquareDouble

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {M : Type} [TopologicalSpace M] (t : C(M, ℝ))

theorem projection_fundamentalGroup_surjective (p : Half t) :
    Surjective (FundamentalGroup.map (projection t) (sectionMap t p)) := by
  intro γ
  obtain ⟨γ⟩ := γ
  refine ⟨Path.Homotopic.Quotient.mk (γ.map (sectionMap t).continuous), ?_⟩
  apply congrArg Path.Homotopic.Quotient.mk
  ext s
  rfl

variable [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace (Half t)]
  (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
  (hr : ∀ p, t p = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t p))

include ht hr in
theorem half_fundamentalGroup_finite (p₀ : Half t) (h₀ : t p₀.val = 0) (p : Half t) :
    Group.FG (FundamentalGroup (Half t) p) := by
  let := atlas t ht hr
  let := isManifold t ht hr
  let : CompactSpace (Space t) := compact t
  let : PathConnectedSpace (Space t) := pathConnected t p₀ h₀
  let : Group.FG (FundamentalGroup (Space t) (sectionMap t p)) :=
    MorseFiniteness.compactManifold_fundamentalGroup_finite (Vector 7) (Space t) (sectionMap t p)
  exact Group.fg_of_surjective (projection_fundamentalGroup_surjective t p)

end NoExoticSixSphere.SquareDouble

namespace Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState

open NoExoticSixSphere

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  [PathConnectedSpace S.PositiveHalf]

theorem positiveHalf_fundamentalGroup_finite (b : B) (p : S.PositiveHalf) :
    Group.FG (FundamentalGroup S.PositiveHalf p) := by
  let : PathConnectedSpace (SquareDouble.Half S.zeroTimeMap) :=
    inferInstanceAs (PathConnectedSpace S.PositiveHalf)
  exact SquareDouble.half_fundamentalGroup_finite S.zeroTimeMap S.time_smooth S.time_regular
    (S.positiveBasepoint b) (S.collar.zeroPoint_time b) p

end Wikipedia.HopfProblem.DegreeCollapse.LowCollaredSevenState
