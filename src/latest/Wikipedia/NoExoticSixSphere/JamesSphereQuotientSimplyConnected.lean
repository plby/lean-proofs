import Wikipedia.NoExoticSixSphere.JamesSphereQuotientCompactFactorization

/-!
# Simple connectivity of the actual full James quotient

Every original loop lies in a finite-stage quotient. That quotient is
simply connected by its genuine cofibration and pushout. Its original
nullhomotopy maps into the full quotient, retaining the given basepoint.
This does not assert the higher metastable connectivity of the bottom sphere.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

theorem simplyConnectedSpace (n : ℕ) : SimplyConnectedSpace (Space (n + 2)) := by
  let := JamesSphere.simplyConnectedSpace n
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro x p
  obtain ⟨k, hk⟩ := exists_stage_of_continuous (n + 2) p p.continuous
  have hx : x ∈ Set.range (FiniteStage.map (n + 2) k) := by
    simpa only [p.source] using hk 0
  let a : Set.range (FiniteStage.map (n + 2) k) := ⟨x, hx⟩
  let p' : Path a a := {
    toFun := fun t ↦ ⟨p t, hk t⟩
    continuous_toFun := p.continuous.subtype_mk _
    source' := Subtype.ext p.source
    target' := Subtype.ext p.target }
  let := FiniteStage.range_simplyConnectedSpace n k
  have h := (SimplyConnectedSpace.paths_homotopic p' (Path.refl a)).map
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(Set.range (FiniteStage.map (n + 2) k), Space (n + 2)))
  have hp : p'.map continuous_subtype_val = p := by ext t; rfl
  have hr : (Path.refl a).map continuous_subtype_val = Path.refl x := rfl
  simpa only [hp, hr] using h

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
