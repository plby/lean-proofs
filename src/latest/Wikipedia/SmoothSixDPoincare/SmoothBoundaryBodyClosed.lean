import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

/-! # The canonical empty boundary and its exact whole-body equivalences -/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  (J : ModelWithCorners ℝ G H)

def closed (X : Type) [TopologicalSpace X] [T2Space X] [CompactSpace X] :
    SmoothBoundaryBody J := by
  let _ := ChartedSpace.empty H PEmpty
  let i : C(PEmpty, X) := ⟨PEmpty.elim, by fun_prop⟩
  exact ofEmbedding i (i.continuous.isClosedEmbedding (fun x => isEmptyElim x))

def empty : SmoothBoundaryBody J := closed J PEmpty

instance closed_boundary_isEmpty (X : Type)
    [TopologicalSpace X] [T2Space X] [CompactSpace X] : IsEmpty (closed J X).boundary :=
  ⟨fun x => PEmpty.elim x⟩

instance empty_body_isEmpty : IsEmpty (empty J).body := ⟨fun x => PEmpty.elim x⟩

instance empty_boundary_isEmpty : IsEmpty (empty J).boundary := ⟨fun x => PEmpty.elim x⟩

variable {J}

def closedEquiv {X Y : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] (e : X ≃ₜ Y) :
    Equiv (closed J X) (closed J Y) where
  body := e
  boundary := Diffeomorph.empty
  boundary_point x := isEmptyElim x

def toClosedEquiv (U : SmoothBoundaryBody J) [IsEmpty U.boundary]
    {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X] (e : U.body ≃ₜ X) :
    Equiv U (closed J X) where
  body := e
  boundary := Diffeomorph.empty
  boundary_point x := isEmptyElim x

def toEmptyEquiv (U : SmoothBoundaryBody J) [IsEmpty U.body] : Equiv U (empty J) := by
  let _ : IsEmpty U.boundary := ⟨fun x => isEmptyElim (U.inclusion x)⟩
  exact toClosedEquiv U (Homeomorph.empty : U.body ≃ₜ PEmpty)

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
