import Wikipedia.SmoothSixDPoincare.PuncturedSurgeryModels
import Wikipedia.SmoothSixDPoincare.ClosedPieceComparison

/-!
# Actual old and new boundary presentations for a surgery

The data consist of closed embedded pieces, a common exterior, exhaustive
covers, and exact common-face incidences. No homeomorphism of the deleted
complements is assumed. `MorseLevelSurgery` constructs these data for the
original Morse levels.
-/

noncomputable section

open Set Function Topology ContinuousMap Metric

namespace Wikipedia.SmoothSixDPoincare

open PuncturedHandle

structure SurgeryBoundaryPair (E F R X Y : Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y] where
  oldExterior : R → X
  newExterior : R → Y
  oldPiece : UnitSphere E × UnitBall F → X
  newPiece : UnitBall E × UnitSphere F → Y
  oldExterior_closed : IsClosedEmbedding oldExterior
  newExterior_closed : IsClosedEmbedding newExterior
  oldPiece_closed : IsClosedEmbedding oldPiece
  newPiece_closed : IsClosedEmbedding newPiece
  old_cover : range oldExterior ∪ range oldPiece = univ
  new_cover : range newExterior ∪ range newPiece = univ
  boundary : UnitSphere E × UnitSphere F → R
  old_overlap : ∀ r p, oldExterior r = oldPiece p ↔
    ∃ q, r = boundary q ∧ p = oldBoundary q
  new_overlap : ∀ r p, newExterior r = newPiece p ↔
    ∃ q, r = boundary q ∧ p = newBoundary q

namespace SurgeryBoundaryPair

variable {E F R X Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

def attachingSphere : C(UnitSphere E, X) :=
  ⟨fun u => d.oldPiece (u, ballZero),
    d.oldPiece_closed.continuous.comp (continuous_id.prodMk continuous_const)⟩

def beltSphere : C(UnitSphere F, Y) :=
  ⟨fun v => d.newPiece (ballZero, v),
    d.newPiece_closed.continuous.comp (continuous_const.prodMk continuous_id)⟩

abbrev OldComplement := (range d.attachingSphere)ᶜ
abbrev NewComplement := (range d.beltSphere)ᶜ

theorem oldPiece_mem_core_iff (p : UnitSphere E × UnitBall F) :
    d.oldPiece p ∈ range d.attachingSphere ↔ (p.2 : F) = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    have hp : (u, (ballZero : UnitBall F)) = p := d.oldPiece_closed.injective hu
    exact (congrArg (fun z : UnitSphere E × UnitBall F => (z.2 : F)) hp).symm
  · intro hp
    refine ⟨p.1, ?_⟩
    apply congrArg d.oldPiece
    exact Prod.ext rfl (Subtype.ext hp.symm)

theorem newPiece_mem_belt_iff (p : UnitBall E × UnitSphere F) :
    d.newPiece p ∈ range d.beltSphere ↔ (p.1 : E) = 0 := by
  constructor
  · rintro ⟨v, hv⟩
    have hp : ((ballZero : UnitBall E), v) = p := d.newPiece_closed.injective hv
    exact (congrArg (fun z : UnitBall E × UnitSphere F => (z.1 : E)) hp).symm
  · intro hp
    refine ⟨p.2, ?_⟩
    apply congrArg d.newPiece
    exact Prod.ext (Subtype.ext hp.symm) rfl

theorem oldExterior_avoids (r : R) : d.oldExterior r ∈ d.OldComplement := by
  rintro ⟨u, hu⟩
  obtain ⟨q, -, hq⟩ := (d.old_overlap r (u, ballZero)).mp hu.symm
  have hz : (q.2 : F) = 0 :=
    (congrArg (fun z : UnitSphere E × UnitBall F => (z.2 : F)) hq).symm
  exact (ne_of_mem_sphere q.2.property one_ne_zero) hz

theorem newExterior_avoids (r : R) : d.newExterior r ∈ d.NewComplement := by
  rintro ⟨v, hv⟩
  obtain ⟨q, -, hq⟩ := (d.new_overlap r (ballZero, v)).mp hv.symm
  have hz : (q.1 : E) = 0 :=
    (congrArg (fun z : UnitBall E × UnitSphere F => (z.1 : E)) hq).symm
  exact (ne_of_mem_sphere q.1.property one_ne_zero) hz

end SurgeryBoundaryPair

end Wikipedia.SmoothSixDPoincare
