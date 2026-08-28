import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Nullhomotopies extracted from native cubical homotopy classes

For every dimension, equality in Mathlib's native quotient gives an actual
continuous homotopy fixing the whole cube boundary. No group operation is
used, so the construction also applies in dimension zero.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

/-- Triviality of the native homotopy quotient gives a nullhomotopy
relative to the entire cube boundary, in every dimension. -/
def nativeCubeNullHomotopy [hπ : Subsingleton (π_ n X x)] (p : GenLoop (Fin n) X x) :
    p.val.HomotopyRel (ContinuousMap.const (Fin n → I) x)
      (Cube.boundary (Fin n)) :=
  Classical.choice (show GenLoop.Homotopic p GenLoop.const from
    Quotient.exact (@Subsingleton.elim (π_ n X x) hπ ⟦p⟧ ⟦GenLoop.const⟧))

variable {A : Type*} [TopologicalSpace A]

/-- Literal precomposition of the native cubical nullhomotopy, retaining
the relative condition on any set mapped into the cube boundary. -/
def nativeCubeNullHomotopy_comp [Subsingleton (π_ n X x)] (p : GenLoop (Fin n) X x)
    (r : C(A, Fin n → I)) (S : Set A)
    (hr : Set.MapsTo r S (Cube.boundary (Fin n))) :
    (p.val.comp r).HomotopyRel (ContinuousMap.const A x) S where
  toFun z := nativeCubeNullHomotopy p (z.1, r z.2)
  continuous_toFun := (nativeCubeNullHomotopy p).continuous.comp
    (continuous_fst.prodMk (r.continuous.comp continuous_snd))
  map_zero_left a := (nativeCubeNullHomotopy p).apply_zero (r a)
  map_one_left a := (nativeCubeNullHomotopy p).apply_one (r a)
  prop' t _ ha := (nativeCubeNullHomotopy p).eq_fst t (hr ha)

variable [Subsingleton (π_ n X x)]

@[simp] theorem nativeCubeNullHomotopy_zero (p : GenLoop (Fin n) X x)
    (s : Fin n → I) : nativeCubeNullHomotopy p (0, s) = p s :=
  (nativeCubeNullHomotopy p).apply_zero s

@[simp] theorem nativeCubeNullHomotopy_one (p : GenLoop (Fin n) X x)
    (s : Fin n → I) : nativeCubeNullHomotopy p (1, s) = x :=
  (nativeCubeNullHomotopy p).apply_one s

theorem nativeCubeNullHomotopy_fixed (p : GenLoop (Fin n) X x)
    (t : I) {s : Fin n → I} (hs : s ∈ Cube.boundary (Fin n)) :
    nativeCubeNullHomotopy p (t, s) = x :=
  (nativeCubeNullHomotopy p).eq_snd t hs

@[simp] theorem nativeCubeNullHomotopy_comp_apply (p : GenLoop (Fin n) X x)
    (r : C(A, Fin n → I)) (S : Set A)
    (hr : Set.MapsTo r S (Cube.boundary (Fin n))) (z : I × A) :
    nativeCubeNullHomotopy_comp p r S hr z =
      nativeCubeNullHomotopy p (z.1, r z.2) := rfl

@[simp] theorem nativeCubeNullHomotopy_comp_zero (p : GenLoop (Fin n) X x)
    (r : C(A, Fin n → I)) (S : Set A)
    (hr : Set.MapsTo r S (Cube.boundary (Fin n))) (a : A) :
    nativeCubeNullHomotopy_comp p r S hr (0, a) = p (r a) :=
  (nativeCubeNullHomotopy_comp p r S hr).apply_zero a

@[simp] theorem nativeCubeNullHomotopy_comp_one (p : GenLoop (Fin n) X x)
    (r : C(A, Fin n → I)) (S : Set A)
    (hr : Set.MapsTo r S (Cube.boundary (Fin n))) (a : A) :
    nativeCubeNullHomotopy_comp p r S hr (1, a) = x :=
  (nativeCubeNullHomotopy_comp p r S hr).apply_one a

theorem nativeCubeNullHomotopy_comp_fixed (p : GenLoop (Fin n) X x)
    (r : C(A, Fin n → I)) (S : Set A)
    (hr : Set.MapsTo r S (Cube.boundary (Fin n))) (t : I) {a : A} (ha : a ∈ S) :
    nativeCubeNullHomotopy_comp p r S hr (t, a) = x :=
  (nativeCubeNullHomotopy_comp p r S hr).eq_snd t ha

end Wikipedia.HopfProblem.HigherHurewicz
