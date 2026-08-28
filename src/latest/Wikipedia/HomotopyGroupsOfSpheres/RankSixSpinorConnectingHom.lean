import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorConnecting
import Wikipedia.HomotopyGroupsOfSpheres.GenLoopConcatenation

/-! # The spinor connecting map respects native homotopy-group multiplication -/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.RankSixComplexProjection.SpinorFibration

open Wikipedia.HomotopyGroupsOfSpheres
open NoExoticSixSphere.CubeFirstCoordinate

variable {d : ℕ} {A : UnitSpinor}

namespace CubeLift

variable {p q : GenLoop (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)}

def slice (L : CubeLift A p) : C(I, GenLoop (Fin d) (UnitSpinor) A) :=
  ⟨fun t ↦ ⟨L.map.curry t, L.boundary t⟩, L.map.curry.continuous.subtype_mk _⟩

@[simp] theorem slice_zero (L : CubeLift A p) : L.slice 0 = GenLoop.const := by
  apply GenLoop.ext
  exact L.initial

def concatSlices (j : Fin d) (L : CubeLift A p) (K : CubeLift A q) :
    C(I, GenLoop (Fin d) (UnitSpinor) A) :=
  (genLoopTransAtMap j).comp (L.slice.prodMk K.slice)

def concatSlicesMap (j : Fin d) (L : CubeLift A p) (K : CubeLift A q) :
    C(I, C(Fin d → I, UnitSpinor)) :=
  ⟨fun t ↦ (concatSlices j L K t).val,
    continuous_subtype_val.comp (concatSlices j L K).continuous⟩

def concatMap (j : Fin d) (L : CubeLift A p) (K : CubeLift A q) :
    C(I × (Fin d → I), UnitSpinor) := (concatSlicesMap j L K).uncurry

theorem concatMap_initial (j : Fin d) (L : CubeLift A p) (K : CubeLift A q)
    (u : Fin d → I) : concatMap j L K (0, u) = A := by
  change GenLoop.transAt j (L.slice 0) (K.slice 0) u = A
  rw [slice_zero, slice_zero, genLoop_transAt_const]
  rfl

theorem concatMap_project (j : Fin d) (L : CubeLift A p) (K : CubeLift A q)
    (t : I) (u : Fin d → I) :
    fromSpinor (concatMap j L K (t, u)) =
      GenLoop.transAt j.succ p q (join d (t, u)) := by
  change fromSpinor (GenLoop.transAt j (L.slice t) (K.slice t) u) = _
  rw [genLoop_transAt_apply, genLoop_transAt_apply]
  change fromSpinor (if (u j : ℝ) ≤ 1 / 2 then
      L.map (t, Function.update u j (Set.projIcc 0 1 zero_le_one (2 * u j)))
    else K.map (t, Function.update u j (Set.projIcc 0 1 zero_le_one (2 * u j - 1)))) =
      if (u j : ℝ) ≤ 1 / 2 then
        p (Function.update (Fin.cons t u) j.succ (Set.projIcc 0 1 zero_le_one (2 * u j)))
      else q (Function.update (Fin.cons t u) j.succ
        (Set.projIcc 0 1 zero_le_one (2 * u j - 1)))
  split_ifs
  · have hu := Fin.cons_update (α := fun _ : Fin (d + 1) ↦ I) t u j
      (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (u j : ℝ)))
    exact (L.project t _).trans (congrArg p hu)
  · have hu := Fin.cons_update (α := fun _ : Fin (d + 1) ↦ I) t u j
      (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (u j : ℝ) - 1))
    exact (K.project t _).trans (congrArg q hu)

def concat (j : Fin d) (L : CubeLift A p) (K : CubeLift A q) :
    CubeLift A (GenLoop.transAt j.succ p q) where
  map := concatMap j L K
  initial := concatMap_initial j L K
  project := concatMap_project j L K
  boundary t u hu := (GenLoop.transAt j (L.slice t) (K.slice t)).property u hu

theorem concat_endpoint (j : Fin d) (L : CubeLift A p) (K : CubeLift A q) :
    (concat j L K).endpoint = GenLoop.transAt j L.endpoint K.endpoint := by
  apply GenLoop.ext
  intro u
  apply Subtype.ext
  change inner ℂ (A : Spinor) ((GenLoop.transAt j (L.slice 1) (K.slice 1) u) : Spinor) =
    (GenLoop.transAt j L.endpoint K.endpoint u : ℂ)
  rw [genLoop_transAt_apply, genLoop_transAt_apply]
  split_ifs <;> rfl

end CubeLift

theorem connecting_transAt (j : Fin d)
    (p q : GenLoop (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)) :
    connecting A d (⟦GenLoop.transAt j.succ p q⟧ :
      HomotopyGroup (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)) =
      (⟦GenLoop.transAt j (boundaryLoop A p) (boundaryLoop A q)⟧ :
        HomotopyGroup (Fin d) (Circle) 1) := by
  rw [connecting_eq_endpoint A _ (CubeLift.concat j (chosenLift A p) (chosenLift A q)),
    CubeLift.concat_endpoint]
  rfl

theorem connecting_mul [NeZero d]
    (a b : HomotopyGroup (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A)) :
    connecting A d (a * b) = connecting A d a * connecting A d b := by
  refine Quotient.inductionOn₂ a b fun p q ↦ ?_
  exact (congrArg (connecting A d)
    (HomotopyGroup.mul_spec (i := (0 : Fin d).succ) (p := p) (q := q))).trans
    ((connecting_transAt (0 : Fin d) q p).trans
      (HomotopyGroup.mul_spec (i := (0 : Fin d))
        (p := boundaryLoop A p) (q := boundaryLoop A q)).symm)

def connectingHom (A : UnitSpinor) (d : ℕ) [NeZero d] :
    HomotopyGroup (Fin (d + 1)) (OrthogonalComplexStructures.Space 6) (fromSpinor A) →*
      HomotopyGroup (Fin d) (Circle) 1 :=
  MonoidHom.mk' (connecting A d) connecting_mul

end NoExoticSixSphere.RankSixComplexProjection.SpinorFibration
