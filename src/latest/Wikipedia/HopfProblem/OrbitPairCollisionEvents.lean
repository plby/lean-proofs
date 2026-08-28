import Wikipedia.HopfProblem.OrbitPairCollisionSources
import Wikipedia.HopfProblem.OrbitPairRetimingCollisionEquiv

/-!
# Collision events, retaining time and target value

All unordered pairs at one time and one target value belong to a single
event. In particular a triple point is one event, not three events. This
allows different target values at a common time to be separated without
claiming to have removed triple points.
-/

noncomputable section

open Set Function

namespace Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints

variable {M N : Type*}

def eventProjection (F : ℝ × M → N) (p : ℝ × (M × M)) : ℝ × N :=
  (p.1, F (p.1, p.2.1))

def collisionEvents (F : ℝ × M → N) : Set (ℝ × N) := eventProjection F '' doublePoints F

theorem finite_collisionEvents {F : ℝ × M → N} (hF : (doublePoints F).Finite) :
    (collisionEvents F).Finite := hF.image (eventProjection F)

theorem eventProjection_mem {F : ℝ × M → N} {p : ℝ × (M × M)} (hp : p ∈ doublePoints F) :
    eventProjection F p ∈ collisionEvents F := mem_image_of_mem _ hp

theorem collision_event_times (F : ℝ × M → N) :
    Prod.fst '' collisionEvents F = Prod.fst '' doublePoints F := by
  rw [collisionEvents, image_image]
  rfl

end Wikipedia.HopfProblem.OrbitPair.FamilyDoublePoints
