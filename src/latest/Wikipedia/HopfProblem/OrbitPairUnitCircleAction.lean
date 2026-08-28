import Wikipedia.HopfProblem.OrbitPairLocalCharacter
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# The original action parametrized by the native unit circle

This is restriction of the original multiplicative action to unit complex
numbers, not a replacement action or atlas. The parameter comparison is
with the original additive circle used to define the orbit quotient.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.chartedSpace VerticalAction.action

local notation "IX" => 𝓘(ℝ, ℂ × ComplexPlane₂)

theorem circle_toUnits_smooth : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ Circle.toUnits := by
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by simp⟩
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact contMDiff_coe_sphere

/-- Restriction of the actual multiplicative action. -/
@[instance_reducible] def unitCircleMulAction : MulAction Circle Threefold.Space :=
  MulAction.compHom Threefold.Space Circle.toUnits

attribute [local instance] unitCircleMulAction

theorem unitCircle_smul_eq (u : Circle) (x : Threefold.Space) :
    u • x = VerticalAction.actionBiholomorph (Circle.toUnits u) x := rfl

theorem unitCircleAction_continuous : ContinuousSMul Circle Threefold.Space := by
  let := VerticalAction.action_continuous
  exact MulAction.continuousSMul_compHom circle_toUnits_smooth.continuous

theorem unitCircleAction_smooth :
    ContMDiff ((𝓡 1).prod IX) IX ∞ (fun p : Circle × Threefold.Space => p.1 • p.2) := by
  have hr : ContMDiff ((𝓘(ℝ, ℂ)).prod IX) IX ∞
      (fun p : ℂˣ × Threefold.Space => p.1 • p.2) := by
    intro p
    have hc := (VerticalAction.action_holomorphic.of_le
      (show (∞ : ℕ∞ω) ≤ ω by simp)) p
    obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp hc
    exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
  exact hr.comp ((circle_toUnits_smooth.comp contMDiff_fst).prodMk contMDiff_snd)

theorem unitCircle_exists_original_parameter (u : Circle) :
    ∃ t : AddCircle (1 : ℝ), Homology.DeltaSweep.circleParameter t = Circle.toUnits u :=
  VerticalAction.FixedCoordinates.CircleOrbit.exists_circleParameter_of_norm_eq_one
    (Circle.toUnits u) (Circle.norm_coe u)

theorem unitCircle_fixed_of_mem_D₀ (u : Circle) (x : Threefold.Space)
    (hx : x ∈ VerticalAction.D₀) : u • x = x :=
  (VerticalAction.action_fixed_iff x).mpr hx (Circle.toUnits u)

theorem quotientMap_unitCircle_smul (u : Circle) (x : Threefold.Space) :
    CircleOrbitSpace.quotientMap (u • x) = CircleOrbitSpace.quotientMap x := by
  obtain ⟨t, ht⟩ := unitCircle_exists_original_parameter u
  apply (CircleOrbitSpace.quotientMap_eq_iff _ _).mpr
  refine ⟨t, ?_⟩
  change VerticalAction.actionBiholomorph (Homology.DeltaSweep.circleParameter t) x = _
  rw [ht]
  rfl

theorem quotientMap_eq_iff_unitCircle (x y : Threefold.Space) :
    CircleOrbitSpace.quotientMap x = CircleOrbitSpace.quotientMap y ↔
      ∃ u : Circle, u • y = x := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := (CircleOrbitSpace.quotientMap_eq_iff x y).mp h
    let u : Circle := ⟨(Homology.DeltaSweep.circleParameter t : ℂ),
      mem_sphere_zero_iff_norm.mpr
        (VerticalAction.FixedCoordinates.CircleOrbit.circleParameter_norm t)⟩
    have hu : Circle.toUnits u = Homology.DeltaSweep.circleParameter t := Units.ext rfl
    refine ⟨u, ?_⟩
    rw [unitCircle_smul_eq, hu]
    exact ht
  · rintro ⟨u, rfl⟩
    exact quotientMap_unitCircle_smul u y

theorem exists_unitCircle_equivariant_smooth_function_at_free_point
    (x : Threefold.Space) (hx : x ∉ VerticalAction.D₀) :
    ∃ F : Threefold.Space → ℂ, ContMDiff IX 𝓘(ℝ, ℂ) ∞ F ∧
      (∀ (u : Circle) y, F (u • y) = (u : ℂ) * F y) ∧ F x ≠ 0 := by
  obtain ⟨F, hF, he, hxF⟩ := exists_equivariant_smooth_function_at_free_point x hx
  refine ⟨F, hF, ?_, hxF⟩
  intro u y
  obtain ⟨t, ht⟩ := unitCircle_exists_original_parameter u
  have h := he t y
  change F (VerticalAction.actionBiholomorph (Homology.DeltaSweep.circleParameter t) y) = _ at h
  rw [ht] at h
  exact h

end Wikipedia.HopfProblem.OrbitPair
