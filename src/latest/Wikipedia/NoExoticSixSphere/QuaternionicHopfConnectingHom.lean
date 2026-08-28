import Wikipedia.NoExoticSixSphere.QuaternionicHopfConnecting
import Wikipedia.HomotopyGroupsOfSpheres.GenLoopConcatenation

/-! # The explicit Hopf connecting map respects native group multiplication -/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

open CubeFirstCoordinate Wikipedia.HomotopyGroupsOfSpheres

variable {n : ℕ}

namespace CubeLift

variable {p q : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)}

def slice (L : CubeLift p) : C(I, GenLoop (Fin n) (Sphere 7) (spherePole 7)) :=
  ⟨fun t ↦ ⟨L.map.curry t, L.boundary t⟩, L.map.curry.continuous.subtype_mk _⟩

theorem slice_zero (L : CubeLift p) : L.slice 0 = GenLoop.const := by
  apply GenLoop.ext
  exact L.initial

def concatSlices (j : Fin n) (L : CubeLift p) (K : CubeLift q) :
    C(I, GenLoop (Fin n) (Sphere 7) (spherePole 7)) :=
  (genLoopTransAtMap j).comp (L.slice.prodMk K.slice)

def concatSlicesMap (j : Fin n) (L : CubeLift p) (K : CubeLift q) :
    C(I, C(Fin n → I, Sphere 7)) :=
  ⟨fun t ↦ (concatSlices j L K t).val,
    continuous_subtype_val.comp (concatSlices j L K).continuous⟩

def concatMap (j : Fin n) (L : CubeLift p) (K : CubeLift q) : C(I × (Fin n → I), Sphere 7) :=
  (concatSlicesMap j L K).uncurry

theorem concatMap_initial (j : Fin n) (L : CubeLift p) (K : CubeLift q) (u : Fin n → I) :
    concatMap j L K (0, u) = spherePole 7 := by
  change GenLoop.transAt j (L.slice 0) (K.slice 0) u = spherePole 7
  rw [slice_zero, slice_zero, genLoop_transAt_const]
  rfl

theorem concatMap_project (j : Fin n) (L : CubeLift p) (K : CubeLift q)
    (t : I) (u : Fin n → I) :
    sphereMap (concatMap j L K (t, u)) = GenLoop.transAt j.succ p q (join n (t, u)) := by
  change sphereMap (GenLoop.transAt j (L.slice t) (K.slice t) u) = _
  rw [genLoop_transAt_apply, genLoop_transAt_apply]
  change sphereMap (if (u j : ℝ) ≤ 1 / 2 then
      L.map (t, Function.update u j (Set.projIcc 0 1 zero_le_one (2 * u j)))
    else K.map (t, Function.update u j (Set.projIcc 0 1 zero_le_one (2 * u j - 1)))) =
      if (u j : ℝ) ≤ 1 / 2 then
        p (Function.update (Fin.cons t u) j.succ (Set.projIcc 0 1 zero_le_one (2 * u j)))
      else q (Function.update (Fin.cons t u) j.succ
        (Set.projIcc 0 1 zero_le_one (2 * u j - 1)))
  split_ifs
  · have hu := Fin.cons_update (α := fun _ : Fin (n + 1) ↦ I) t u j
      (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (u j : ℝ)))
    exact (L.project t _).trans (congrArg p hu)
  · have hu := Fin.cons_update (α := fun _ : Fin (n + 1) ↦ I) t u j
      (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (u j : ℝ) - 1))
    exact (K.project t _).trans (congrArg q hu)

def concat (j : Fin n) (L : CubeLift p) (K : CubeLift q) :
    CubeLift (GenLoop.transAt j.succ p q) where
  map := concatMap j L K
  initial := concatMap_initial j L K
  project := concatMap_project j L K
  boundary t u hu := (GenLoop.transAt j (L.slice t) (K.slice t)).property u hu

theorem concat_endpoint (j : Fin n) (L : CubeLift p) (K : CubeLift q) :
    (concat j L K).endpoint = GenLoop.transAt j L.endpoint K.endpoint := by
  apply GenLoop.ext
  intro u
  apply unitFiberPoint_injective
  rw [endpoint_point]
  change GenLoop.transAt j (L.slice 1) (K.slice 1) u =
    unitFiberPoint (GenLoop.transAt j L.endpoint K.endpoint u)
  rw [genLoop_transAt_apply, genLoop_transAt_apply]
  split_ifs with h
  · exact (L.endpoint_point _).symm
  · exact (K.endpoint_point _).symm

end CubeLift

theorem connecting_transAt (j : Fin n)
    (p q : GenLoop (Fin (n + 1)) (Sphere 4) (spherePole 4)) :
    connecting n (⟦GenLoop.transAt j.succ p q⟧ :
      HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4)) =
      (⟦GenLoop.transAt j (boundaryLoop p) (boundaryLoop q)⟧ :
        HomotopyGroup (Fin n) FiberGroup 1) := by
  rw [connecting_eq_endpoint _ (CubeLift.concat j (chosenLift p) (chosenLift q)),
    CubeLift.concat_endpoint]
  rfl

theorem connecting_mul [NeZero n]
    (a b : HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4)) :
    connecting n (a * b) = connecting n a * connecting n b := by
  refine Quotient.inductionOn₂ a b fun p q ↦ ?_
  exact (congrArg (connecting n)
    (HomotopyGroup.mul_spec (i := (0 : Fin n).succ) (p := p) (q := q))).trans
    ((connecting_transAt (0 : Fin n) q p).trans
      (HomotopyGroup.mul_spec (i := (0 : Fin n))
        (p := boundaryLoop p) (q := boundaryLoop q)).symm)

def connectingHom (n : ℕ) [NeZero n] :
    HomotopyGroup (Fin (n + 1)) (Sphere 4) (spherePole 4) →*
      HomotopyGroup (Fin n) FiberGroup 1 :=
  MonoidHom.mk' (connecting n) connecting_mul

end NoExoticSixSphere.QuaternionicHopf
