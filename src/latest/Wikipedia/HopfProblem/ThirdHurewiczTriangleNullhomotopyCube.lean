import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Nullhomotopies of native squares when the second homotopy group vanishes

The native quotient relation produces an actual continuous homotopy fixing
the entire cube boundary. Precomposition retains the relative condition
whenever the specified set maps into that boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Equality in Mathlib's native second homotopy group gives an actual
nullhomotopy relative to the whole square boundary. -/
def nativeSquareNullHomotopy [hπ : Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 2) X x) :
    p.val.HomotopyRel (ContinuousMap.const (Fin 2 → I) x)
      (Cube.boundary (Fin 2)) :=
  Classical.choice (show GenLoop.Homotopic p GenLoop.const from
    Quotient.exact (@Subsingleton.elim (π_ 2 X x) hπ ⟦p⟧ ⟦GenLoop.const⟧))

variable {A : Type*} [TopologicalSpace A]

/-- Literal precomposition of the native square nullhomotopy, retaining
the relative condition on any set mapped into the cube boundary. -/
def nativeSquareNullHomotopy_comp [Subsingleton (π_ 2 X x)] (p : GenLoop (Fin 2) X x)
    (r : C(A, Fin 2 → I)) (S : Set A)
    (hr : Set.MapsTo r S (Cube.boundary (Fin 2))) :
    (p.val.comp r).HomotopyRel (ContinuousMap.const A x) S where
  toFun z := nativeSquareNullHomotopy p (z.1, r z.2)
  continuous_toFun := (nativeSquareNullHomotopy p).continuous.comp
    (continuous_fst.prodMk (r.continuous.comp continuous_snd))
  map_zero_left a := (nativeSquareNullHomotopy p).apply_zero (r a)
  map_one_left a := (nativeSquareNullHomotopy p).apply_one (r a)
  prop' t _ ha := (nativeSquareNullHomotopy p).eq_fst t (hr ha)

variable [Subsingleton (π_ 2 X x)]

@[simp] theorem nativeSquareNullHomotopy_zero (p : GenLoop (Fin 2) X x)
    (s : Fin 2 → I) : nativeSquareNullHomotopy p (0, s) = p s :=
  (nativeSquareNullHomotopy p).apply_zero s

@[simp] theorem nativeSquareNullHomotopy_one (p : GenLoop (Fin 2) X x)
    (s : Fin 2 → I) : nativeSquareNullHomotopy p (1, s) = x :=
  (nativeSquareNullHomotopy p).apply_one s

theorem nativeSquareNullHomotopy_fixed (p : GenLoop (Fin 2) X x)
    (t : I) {s : Fin 2 → I} (hs : s ∈ Cube.boundary (Fin 2)) :
    nativeSquareNullHomotopy p (t, s) = x :=
  (nativeSquareNullHomotopy p).eq_snd t hs

@[simp] theorem nativeSquareNullHomotopy_comp_apply (p : GenLoop (Fin 2) X x)
    (r : C(A, Fin 2 → I)) (S : Set A)
    (hr : Set.MapsTo r S (Cube.boundary (Fin 2))) (z : I × A) :
    nativeSquareNullHomotopy_comp p r S hr z =
      nativeSquareNullHomotopy p (z.1, r z.2) := rfl

@[simp] theorem nativeSquareNullHomotopy_comp_zero (p : GenLoop (Fin 2) X x)
    (r : C(A, Fin 2 → I)) (S : Set A)
    (hr : Set.MapsTo r S (Cube.boundary (Fin 2))) (a : A) :
    nativeSquareNullHomotopy_comp p r S hr (0, a) = p (r a) :=
  (nativeSquareNullHomotopy_comp p r S hr).apply_zero a

@[simp] theorem nativeSquareNullHomotopy_comp_one (p : GenLoop (Fin 2) X x)
    (r : C(A, Fin 2 → I)) (S : Set A)
    (hr : Set.MapsTo r S (Cube.boundary (Fin 2))) (a : A) :
    nativeSquareNullHomotopy_comp p r S hr (1, a) = x :=
  (nativeSquareNullHomotopy_comp p r S hr).apply_one a

theorem nativeSquareNullHomotopy_comp_fixed (p : GenLoop (Fin 2) X x)
    (r : C(A, Fin 2 → I)) (S : Set A)
    (hr : Set.MapsTo r S (Cube.boundary (Fin 2))) (t : I) {a : A} (ha : a ∈ S) :
    nativeSquareNullHomotopy_comp p r S hr (t, a) = x :=
  (nativeSquareNullHomotopy_comp p r S hr).eq_snd t ha

end Wikipedia.HopfProblem.ThirdHurewicz
