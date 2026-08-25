import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Defs
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Algebra of circle-path displacement

These identities are for actual continuous lifts, and apply to nonclosed paths
as well as loops.  In particular, concatenation is additive even when its
individual arcs have different endpoints.
-/

noncomputable section

namespace Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

open Set unitInterval

@[simp] theorem displacement_add (γ δ : C(I, Circle)) :
    displacement (γ + δ) = displacement γ + displacement δ := by
  rw [displacement_eq_sub_of_lift (γ + δ) (pathLift γ + pathLift δ)
    (by intro t; simp only [ContinuousMap.add_apply, AddCircle.coe_add, coe_pathLift])]
  simp only [ContinuousMap.add_apply, displacement]
  ring

@[simp] theorem displacement_neg (γ : C(I, Circle)) :
    displacement (-γ) = -displacement γ := by
  rw [displacement_eq_sub_of_lift (-γ) (-pathLift γ)
    (by intro t; simp only [ContinuousMap.neg_apply, AddCircle.coe_neg, coe_pathLift])]
  simp only [ContinuousMap.neg_apply, displacement]
  ring

@[simp] theorem displacement_sub (γ δ : C(I, Circle)) :
    displacement (γ - δ) = displacement γ - displacement δ := by
  simp only [sub_eq_add_neg, displacement_add, displacement_neg]

@[simp] theorem displacement_add_const (γ : C(I, Circle)) (x : Circle) :
    displacement (γ + ContinuousMap.const I x) = displacement γ := by simp

@[simp] theorem displacement_const_add (γ : C(I, Circle)) (x : Circle) :
    displacement (ContinuousMap.const I x + γ) = displacement γ := by simp

/-- Reversing the parameter of a continuous path. -/
def reverse (γ : C(I, Circle)) : C(I, Circle) :=
  ⟨fun t => γ (σ t), γ.continuous.comp continuous_symm⟩

@[simp] theorem reverse_apply (γ : C(I, Circle)) (t : I) :
    reverse γ t = γ (σ t) := rfl

@[simp] theorem displacement_reverse (γ : C(I, Circle)) :
    displacement (reverse γ) = -displacement γ := by
  rw [displacement_eq_sub_of_lift (reverse γ)
    ⟨fun t => pathLift γ (σ t), (pathLift γ).continuous.comp continuous_symm⟩
    (by intro t; exact coe_pathLift γ (σ t))]
  simp only [ContinuousMap.coe_mk, symm_one, symm_zero, displacement]
  ring

@[simp] theorem displacement_symm {x y : Circle} (γ : Path x y) :
    displacement (γ.symm : C(I, Circle)) = -displacement (γ : C(I, Circle)) :=
  displacement_reverse γ

/-- Concatenation adds the lift displacements, independently of the common
endpoint of the two paths. -/
theorem displacement_trans {x y z : Circle} (γ : Path x y) (δ : Path y z) :
    displacement (γ.trans δ : C(I, Circle)) = displacement γ + displacement δ := by
  let b := baseLift γ
  have hb : x = (b : Circle) := γ.source.symm.trans (coe_baseLift γ).symm
  let Γ := cover.liftPath γ b (γ.source.trans hb)
  have hδ : δ 0 = (Γ 1 : Circle) := by
    rw [δ.source]
    exact γ.target.symm.trans
      (congr_fun (cover.liftPath_lifts γ b (γ.source.trans hb)) 1).symm
  let Δ := cover.liftPath δ (Γ 1) hδ
  have htrans : cover.liftPath (γ.trans δ) b ((γ.trans δ).source.trans hb) 1 = Δ 1 := by
    exact (congrArg (fun f : C(I, ℝ) => f 1) (cover.liftPath_trans hb γ δ)).trans
      (Path.target _)
  rw [displacement_eq_liftPath (γ.trans δ) b ((γ.trans δ).source.trans hb), htrans,
    displacement_eq_liftPath γ b (γ.source.trans hb),
    displacement_eq_liftPath δ (Γ 1) hδ]
  dsimp only [Δ, Γ]
  ring

@[simp] theorem displacement_refl (x : Circle) :
    displacement (Path.refl x : C(I, Circle)) = 0 := displacement_const x

/-- Cancellation of a common interface when two boundary loops are glued. -/
theorem displacement_boundary_gluing {x y : Circle}
    (M Γ : Path x y) (N : Path y x) :
    displacement (M.trans Γ.symm : C(I, Circle)) +
        displacement (Γ.trans N : C(I, Circle)) =
      displacement (M.trans N : C(I, Circle)) := by
  rw [displacement_trans, displacement_trans, displacement_trans, displacement_symm]
  ring

/-- The displacement of a reparametrized path depends only on the endpoint
values of its lifted parameter. -/
theorem displacement_comp (γ : C(I, Circle)) (u : C(I, I))
    (hzero : u 0 = 0) (hone : u 1 = 1) :
    displacement (γ.comp u) = displacement γ := by
  rw [displacement_eq_sub_of_lift (γ.comp u) ((pathLift γ).comp u)
    (fun t => coe_pathLift γ (u t))]
  simp only [ContinuousMap.comp_apply, hzero, hone, displacement]

theorem displacement_comp_reverse (γ : C(I, Circle)) (u : C(I, I))
    (hzero : u 0 = 1) (hone : u 1 = 0) :
    displacement (γ.comp u) = -displacement γ := by
  rw [displacement_eq_sub_of_lift (γ.comp u) ((pathLift γ).comp u)
    (fun t => coe_pathLift γ (u t))]
  simp only [ContinuousMap.comp_apply, hzero, hone, displacement]
  ring

end Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

end
