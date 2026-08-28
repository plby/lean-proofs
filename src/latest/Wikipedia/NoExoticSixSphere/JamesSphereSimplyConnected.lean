import Wikipedia.NoExoticSixSphere.JamesSphereStageCofibration
import Wikipedia.NoExoticSixSphere.FatWedgeConnectivity
import Wikipedia.NoExoticSixSphere.DoubleMappingCylinderSimplyConnected
import Wikipedia.NoExoticSixSphere.JamesCompactFactorization
import Wikipedia.NoExoticSixSphere.JamesPathConnected
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# Simple connectivity of the actual James sphere space

For spheres of dimension at least two, every Cartesian power is simply
connected and every attaching fat wedge is path connected. The genuine
pushout and its proved cofibration identify each successive stage with
an actual double mapping cylinder up to homotopy. Van Kampen proves
simple connectivity of all stages. Every loop in the full James space
lies in a finite stage by the checked compact-factorization theorem.
-/

noncomputable section

open CategoryTheory Set
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere

theorem stage_simplyConnected (n k : ℕ) :
    SimplyConnectedSpace (James.stage (spherePole (n + 2)) k) := by
  induction k with
  | zero =>
      let : Nonempty (James.stage (spherePole (n + 2)) 0) :=
        ⟨⟨1, by change James.size (spherePole (n + 2)) 1 ≤ 0; rw [James.size_one]⟩⟩
      have hz (w : James.stage (spherePole (n + 2)) 0) : w.val = 1 :=
        (James.size_eq_zero_iff (spherePole (n + 2)) w.val).mp
          (Nat.eq_zero_of_le_zero w.property)
      let : Subsingleton (James.stage (spherePole (n + 2)) 0) :=
        ⟨fun v w ↦ Subtype.ext ((hz v).trans (hz w).symm)⟩
      infer_instance
  | succ k ih =>
      let := ih
      let : SimplyConnectedSpace (StageAttachment.lower (n + 2) k) :=
        (StageAttachment.lowerHomeomorph (n + 2) k).symm.toHomotopyEquiv.simplyConnectedSpace
      let : SimplyConnectedSpace (Fin (k + 1) → Sphere (n + 2)) :=
        FatWedge.power_simplyConnected (k + 1)
      let : PathConnectedSpace
          (StageAttachment.presentation (n + 2) k ⁻¹' StageAttachment.lower (n + 2) k) := by
        change PathConnectedSpace
          (stagePresentation (n + 2) (k + 1) ⁻¹' StageAttachment.lower (n + 2) k)
        rw [StageAttachment.boundary_eq]
        exact FatWedge.pathConnectedSpace (spherePole (n + 2)) k
      apply DoubleMappingCylinder.pushout_simplyConnectedSpace
        (QuotientAttachment.boundaryInclusion (StageAttachment.presentation (n + 2) k)
          (StageAttachment.lower (n + 2) k))
        (QuotientAttachment.boundaryMap (StageAttachment.presentation (n + 2) k)
          (StageAttachment.lower (n + 2) k)) (StageAttachment.isPushout (n + 2) k).flip
      change HomotopyExtension.HasHomotopyExtension (SubspaceCofibration.inclusion
        (stagePresentation (n + 2) (k + 1) ⁻¹' StageAttachment.lower (n + 2) k))
      rw [StageAttachment.boundary_eq]
      exact FatWedge.sphere_hasHomotopyExtension (spherePole (n + 2)) (k + 1)

theorem simplyConnectedSpace (n : ℕ) :
    SimplyConnectedSpace (James.Space (Sphere (n + 2)) (spherePole (n + 2))) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro x p
  obtain ⟨k, hk⟩ := James.exists_stage_of_continuous (spherePole (n + 2)) p p.continuous
  have hx : x ∈ James.stage (spherePole (n + 2)) k := by simpa only [p.source] using hk 0
  let p' : Path (⟨x, hx⟩ : James.stage (spherePole (n + 2)) k) ⟨x, hx⟩ :=
    { toFun := fun t ↦ ⟨p t, hk t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let := stage_simplyConnected n k
  have h := (SimplyConnectedSpace.paths_homotopic p'
    (Path.refl (⟨x, hx⟩ : James.stage (spherePole (n + 2)) k))).map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(James.stage (spherePole (n + 2)) k, _))
  have hp : p'.map continuous_subtype_val = p := by ext t; rfl
  have hr : (Path.refl (⟨x, hx⟩ : James.stage (spherePole (n + 2)) k)).map
      continuous_subtype_val = Path.refl x := rfl
  simpa only [hp, hr] using h

end NoExoticSixSphere.JamesSphere
