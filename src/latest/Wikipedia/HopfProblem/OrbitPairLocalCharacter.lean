import Wikipedia.HopfProblem.OrbitPairCharacterAverage
import Wikipedia.HopfProblem.OrbitPairRealCircleAction
import Mathlib.Topology.TietzeExtension
import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Smooth equivariant characters near every actual free orbit

The actual free orbit is a closed embedded circle. Extend its original
unit character by Tietze, approximate the extension smoothly in the
original threefold atlas, and take the character-weighted average.
The uniform half-unit error makes the average nonzero at the chosen
point. Its nonzero set is an invariant open neighborhood of that orbit.
-/

noncomputable section

open Set Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.chartedSpace Threefold.space_t2Space
  Threefold.space_compact Threefold.space_isSmoothRealManifold

local notation "IX" => 𝓘(ℝ, ℂ × ComplexPlane₂)
local notation "Circle" => AddCircle (1 : ℝ)

/-- A continuous global extension of the original unit character on the chosen free orbit. -/
theorem exists_orbit_character_extension (x : Threefold.Space) (hx : x ∉ VerticalAction.D₀) :
    ∃ f : C(Threefold.Space, ℂ), ∀ t : Circle,
      f (Homology.DeltaSweep.actionMap (t, x)) = (Homology.DeltaSweep.circleParameter t : ℂ) := by
  let : TietzeExtension ℂ := TietzeExtension.of_homeo Complex.equivRealProdCLM.toHomeomorph
  let χ : C(Circle, ℂ) := ⟨fun t => (Homology.DeltaSweep.circleParameter t : ℂ),
    Units.continuous_val.comp Homology.DeltaSweep.circleParameter_continuous⟩
  obtain ⟨f, hf⟩ := ContinuousMap.exists_extension
    (CircleActionSemifree.orbitMap_isClosedEmbedding x hx) χ
  refine ⟨f, fun t => ?_⟩
  exact congrArg (fun g : C(Circle, ℂ) => g t) hf

/-- Constructed smooth equivariance and nonvanishing, without a supplied slice theorem. -/
theorem exists_real_equivariant_smooth_function_at_free_point
    (x : Threefold.Space) (hx : x ∉ VerticalAction.D₀) :
    ∃ F : Threefold.Space → ℂ, ContMDiff IX 𝓘(ℝ, ℂ) ∞ F ∧
      (∀ t y, F (realCircleAction t y) = realCircleCharacter t * F y) ∧ F x ≠ 0 := by
  obtain ⟨f, hf⟩ := exists_orbit_character_extension x hx
  obtain ⟨g, hgclose, _⟩ := f.continuous.exists_contMDiff_approx IX (⊤ : ℕ∞)
    (ε := fun _ => (1 / 2 : ℝ)) continuous_const (fun _ => by norm_num)
  refine ⟨CharacterAverage.average realCircleAction realCircleCharacter g, ?_, ?_, ?_⟩
  · exact CharacterAverage.smooth realCircleAction realCircleCharacter
      realCircleAction_smooth realCircleCharacter_smooth realCircleCharacter_ne_zero g.contMDiff
  · exact CharacterAverage.equivariant realCircleAction realCircleCharacter
      realCircleAction_add realCircleAction_periodic realCircleCharacter_add
      realCircleCharacter_periodic realCircleCharacter_ne_zero g
  · apply CharacterAverage.average_ne_zero_of_orbit_close realCircleAction realCircleCharacter
      realCircleAction_smooth.continuous realCircleCharacter_smooth.continuous
      realCircleCharacter_unit g.contMDiff.continuous x
    intro t _
    have he : f (realCircleAction t x) = realCircleCharacter t := by
      rw [realCircleAction_eq, realCircleCharacter_eq]
      exact hf (t : Circle)
    rw [← he]
    exact hgclose (realCircleAction t x)

/-- Equivariance is with respect to every element of the original additive circle. -/
theorem exists_equivariant_smooth_function_at_free_point
    (x : Threefold.Space) (hx : x ∉ VerticalAction.D₀) :
    ∃ F : Threefold.Space → ℂ, ContMDiff IX 𝓘(ℝ, ℂ) ∞ F ∧
      (∀ (t : Circle) y, F (Homology.DeltaSweep.actionMap (t, y)) =
        (Homology.DeltaSweep.circleParameter t : ℂ) * F y) ∧ F x ≠ 0 := by
  obtain ⟨F, hF, he, hxF⟩ := exists_real_equivariant_smooth_function_at_free_point x hx
  refine ⟨F, hF, ?_, hxF⟩
  intro t y
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
  simpa only [realCircleAction_eq, realCircleCharacter_eq] using he s y

end Wikipedia.HopfProblem.OrbitPair
