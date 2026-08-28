import Wikipedia.SmoothSixDPoincare.PuncturedHandleCoordinates
import Mathlib.Topology.LocalAtTarget

/-! # Actual closed surgery pieces and their punctured parameter spaces -/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.PuncturedHandle

abbrev UnitBall (E : Type*) [NormedAddCommGroup E] := {x : E // ‖x‖ ≤ 1}

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

def ballZero : UnitBall E := ⟨0, by simp⟩

def sphereToBall (u : UnitSphere E) : UnitBall E :=
  ⟨u, (mem_sphere_zero_iff_norm.mp u.property).le⟩

def puncturedToBall (u : PuncturedBall E) : UnitBall E := ⟨u, u.property.2⟩

theorem puncturedToBall_injective : Injective (puncturedToBall (E := E)) :=
  fun _ _ h => Subtype.ext (congrArg (fun z : UnitBall E => (z : E)) h)

def oldBoundary (q : UnitSphere E × UnitSphere F) : UnitSphere E × UnitBall F :=
  (q.1, sphereToBall q.2)

def newBoundary (q : UnitSphere E × UnitSphere F) : UnitBall E × UnitSphere F :=
  (sphereToBall q.1, q.2)

def oldPunctured (p : UnitSphere E × PuncturedBall F) : UnitSphere E × UnitBall F :=
  (p.1, puncturedToBall p.2)

def newPunctured (p : PuncturedBall E × UnitSphere F) : UnitBall E × UnitSphere F :=
  (puncturedToBall p.1, p.2)

theorem oldPunctured_injective : Injective (oldPunctured (E := E) (F := F)) := by
  intro p q h
  exact Prod.ext (congrArg (fun z : UnitSphere E × UnitBall F => z.1) h)
    (puncturedToBall_injective (congrArg (fun z : UnitSphere E × UnitBall F => z.2) h))

theorem newPunctured_injective : Injective (newPunctured (E := E) (F := F)) := by
  intro p q h
  exact Prod.ext
    (puncturedToBall_injective (congrArg (fun z : UnitBall E × UnitSphere F => z.1) h))
    (congrArg (fun z : UnitBall E × UnitSphere F => z.2) h)

/-- The old punctured piece is exactly the preimage of the attaching-core complement. -/
def oldPuncturedDomain (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :
    (UnitSphere E × PuncturedBall F) ≃ₜ
      {p : UnitSphere E × UnitBall F // (p.2 : F) ≠ 0} where
  toFun p := ⟨oldPunctured p, p.2.property.1⟩
  invFun p := (p.val.1, ⟨p.val.2, p.property, p.val.2.property⟩)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun p : UnitSphere E × PuncturedBall F =>
      (p.1, (⟨(p.2 : F), p.2.property.2⟩ : UnitBall F)))
    exact continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · exact (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val)).subtype_mk _

/-- The new punctured piece is exactly the preimage of the belt-sphere complement. -/
def newPuncturedDomain (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :
    (PuncturedBall E × UnitSphere F) ≃ₜ
      {p : UnitBall E × UnitSphere F // (p.1 : E) ≠ 0} where
  toFun p := ⟨newPunctured p, p.1.property.1⟩
  invFun p := (⟨p.val.1, p.property, p.val.1.property⟩, p.val.2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun p : PuncturedBall E × UnitSphere F =>
      ((⟨(p.1 : E), p.1.property.2⟩ : UnitBall E), p.2))
    exact ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
  continuous_invFun := by
    apply Continuous.prodMk
    · exact (continuous_subtype_val.comp
        (continuous_fst.comp continuous_subtype_val)).subtype_mk _
    · exact continuous_snd.comp continuous_subtype_val

theorem oldPunctured_boundary (q : UnitSphere E × UnitSphere F) :
    oldPunctured (q.1, boundaryPoint q.2) = oldBoundary q := rfl

theorem newPunctured_boundary (q : UnitSphere E × UnitSphere F) :
    newPunctured (boundaryPoint q.1, q.2) = newBoundary q := rfl

end Wikipedia.SmoothSixDPoincare.PuncturedHandle
