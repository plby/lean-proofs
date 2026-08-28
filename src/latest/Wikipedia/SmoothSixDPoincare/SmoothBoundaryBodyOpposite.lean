import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyClosed
import Wikipedia.SmoothSixDPoincare.BoundaryGluingCoordinates

/-!
# A reverse-side body with the same actual native boundary

The common boundary is the original boundary itself, so there is no
unrecorded identification. Coordinate changes reparametrize only this
boundary and the corresponding old body in the gluing. These data keep
the full glued space invariant during finite chain reversal.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}

structure Opposite (U : SmoothBoundaryBody J) where
  body : TopCat.{0}
  bodyT2 : T2Space body
  bodyCompact : CompactSpace body
  inclusion : C(U.boundary, body)
  closedEmbedding : IsClosedEmbedding inclusion

attribute [instance] Opposite.bodyT2 Opposite.bodyCompact

namespace Opposite

variable {U V : SmoothBoundaryBody J}

def toBody (D : Opposite U) : SmoothBoundaryBody J :=
  SmoothBoundaryBody.ofEmbedding D.inclusion D.closedEmbedding

abbrev Glued (D : Opposite U) := BoundaryGluing.Space U.inclusion D.inclusion

instance gluedT2Space (D : Opposite U) : T2Space D.Glued :=
  BoundaryGluing.t2Space U.inclusion D.inclusion U.closedEmbedding.injective
    D.closedEmbedding.injective

def rebase (D : Opposite V) (e : Equiv U V) : Opposite U where
  body := D.body
  bodyT2 := inferInstance
  bodyCompact := inferInstance
  inclusion := D.inclusion.comp ⟨e.boundary, e.boundary.continuous⟩
  closedEmbedding := D.closedEmbedding.comp e.boundary.toHomeomorph.isClosedEmbedding

def rebaseEquiv (D : Opposite V) (e : Equiv U V) : Equiv D.toBody (D.rebase e).toBody where
  body := Homeomorph.refl _
  boundary := e.boundary.symm
  boundary_point x := (congrArg D.inclusion (e.boundary.apply_symm_apply x)).symm

def rebaseGluing (D : Opposite V) (e : Equiv U V) : D.Glued ≃ₜ (D.rebase e).Glued :=
  (BoundaryGluing.congr U.inclusion (D.rebase e).inclusion V.inclusion D.inclusion
    e.boundary.toHomeomorph e.body (Homeomorph.refl D.body) e.boundary_point (fun _ => rfl)).symm

theorem rebaseGluing_old (D : Opposite V) (e : Equiv U V) (v : V.body) :
    D.rebaseGluing e (BoundaryGluing.left V.inclusion D.inclusion v) =
      BoundaryGluing.left U.inclusion (D.rebase e).inclusion (e.body.symm v) := rfl

theorem rebaseGluing_other (D : Opposite V) (e : Equiv U V) (d : D.body) :
    D.rebaseGluing e (BoundaryGluing.right V.inclusion D.inclusion d) =
      BoundaryGluing.right U.inclusion (D.rebase e).inclusion d := rfl

def empty (U : SmoothBoundaryBody J) [IsEmpty U.boundary] : Opposite U := by
  let i : C(U.boundary, PEmpty) := ⟨isEmptyElim, by fun_prop⟩
  exact {
    body := TopCat.of PEmpty
    bodyT2 := inferInstance
    bodyCompact := inferInstance
    inclusion := i
    closedEmbedding := i.continuous.isClosedEmbedding (fun x => isEmptyElim x) }

instance empty_body_isEmpty (U : SmoothBoundaryBody J) [IsEmpty U.boundary] :
    IsEmpty (empty U).body := ⟨fun x => PEmpty.elim x⟩

def emptyGluedHomeomorph (U : SmoothBoundaryBody J) [IsEmpty U.boundary] :
    (empty U).Glued ≃ₜ U.body := BoundaryGluing.rightEmptyHomeomorph U.inclusion (empty U).inclusion

def leftEmptyGluedHomeomorph [IsEmpty U.body] (D : Opposite U) : D.Glued ≃ₜ D.body :=
  BoundaryGluing.leftEmptyHomeomorph U.inclusion D.inclusion

def toClosedEquiv [IsEmpty U.boundary] (D : Opposite U) :
    Equiv D.toBody (SmoothBoundaryBody.closed J D.body) := by
  let _ : IsEmpty D.toBody.boundary := inferInstanceAs (IsEmpty U.boundary)
  exact SmoothBoundaryBody.toClosedEquiv D.toBody (Homeomorph.refl D.body)

def emptyToEmptyEquiv (U : SmoothBoundaryBody J) [IsEmpty U.boundary] :
    Equiv (empty U).toBody (SmoothBoundaryBody.empty J) := by
  let _ : IsEmpty (empty U).toBody.body := ⟨fun x => PEmpty.elim x⟩
  exact SmoothBoundaryBody.toEmptyEquiv (empty U).toBody

end Opposite
end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
