import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.UnitInterval

/-!
# An actual inward collar of a specified boundary inclusion

The closed cylinder embeds in the body, its zero end is the given boundary,
and deleting its inner end leaves an open subset of the body. These are
geometric data, not a smoothness assertion about the whole body.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

structure InwardBoundaryCollar (i : C(X, Y)) where
  map : C(X × unitInterval, Y)
  closedEmbedding : IsClosedEmbedding map
  zero : ∀ x, map (x, 0) = i x
  inner_open : IsOpen (map '' {q : X × unitInterval | q.2 < 1})

namespace InwardBoundaryCollar

def ofIsEmpty [IsEmpty X] [T2Space Y] (i : C(X, Y)) : InwardBoundaryCollar i where
  map := i.comp ⟨Prod.fst, continuous_fst⟩
  closedEmbedding := (i.continuous.comp continuous_fst).isClosedEmbedding
    (fun q _ _ => isEmptyElim q.1)
  zero _ := rfl
  inner_open := by
    convert isOpen_empty (X := Y) using 1
    ext y
    constructor
    · rintro ⟨q, _, _⟩
      exact isEmptyElim q.1
    · exact False.elim

variable {i : C(X, Y)} (C : InwardBoundaryCollar i)
  {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y'] {i' : C(X', Y')}

def transport (a : X ≃ₜ X') (b : Y ≃ₜ Y') (h : ∀ x, b (i x) = i' (a x)) :
    InwardBoundaryCollar i' where
  map := ⟨fun q => b (C.map (a.symm q.1, q.2)), b.continuous.comp (C.map.continuous.comp
    ((a.symm.continuous.comp continuous_fst).prodMk continuous_snd))⟩
  closedEmbedding := b.isClosedEmbedding.comp (C.closedEmbedding.comp
    (a.symm.prodCongr (Homeomorph.refl unitInterval)).isClosedEmbedding)
  zero x := by
    change b (C.map (a.symm x, 0)) = i' x
    rw [C.zero]
    exact (h (a.symm x)).trans (congrArg i' (a.apply_symm_apply x))
  inner_open := by
    have heq : (fun q : X' × unitInterval => b (C.map (a.symm q.1, q.2))) ''
        {q | q.2 < 1} = b '' (C.map '' {q : X × unitInterval | q.2 < 1}) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact ⟨_, ⟨(a.symm q.1, q.2), hq, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
        refine ⟨(a q.1, q.2), hq, ?_⟩
        exact congrArg (fun x => b (C.map (x, q.2))) (a.symm_apply_apply q.1)
    exact heq ▸ b.isOpenMap _ C.inner_open

theorem transport_map (a : X ≃ₜ X') (b : Y ≃ₜ Y') (h : ∀ x, b (i x) = i' (a x))
    (q : X' × unitInterval) : (C.transport a b h).map q = b (C.map (a.symm q.1, q.2)) := rfl

end InwardBoundaryCollar
end Wikipedia.SmoothSixDPoincare
