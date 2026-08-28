import Wikipedia.HopfProblem.ThirdHurewiczCubeSubdivisionNativeBasic

/-!
# Native Duffy parametrizations of the ordered cube tetrahedra

The product parametrization sends every parameter boundary face either to
the cube boundary or to a coordinate equality plane. A cube which is based
on all those planes therefore pulls back to a genuine native three-loop.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

/-- The product parametrization of the canonical ordered tetrahedron. -/
def nativeDuffyCubeCanonical : C(NativeCube, NativeCube) where
  toFun u := ![u 0, u 0 * u 1, u 0 * u 1 * u 2]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · exact ((continuous_subtype_val.comp (continuous_apply 0)).mul
        (continuous_subtype_val.comp (continuous_apply 1))).subtype_mk _
    · exact (((continuous_subtype_val.comp (continuous_apply 0)).mul
        (continuous_subtype_val.comp (continuous_apply 1))).mul
        (continuous_subtype_val.comp (continuous_apply 2))).subtype_mk _

theorem nativeDuffyCubeCanonical_apply (u : NativeCube) :
    nativeDuffyCubeCanonical u = ![u 0, u 0 * u 1, u 0 * u 1 * u 2] := rfl

/-- The actual Duffy map with its three output coordinates permuted by `e`. -/
def nativeDuffyCube (e : Equiv.Perm (Fin 3)) : C(NativeCube, NativeCube) where
  toFun u i := nativeDuffyCubeCanonical u (e.symm i)
  continuous_toFun := continuous_pi fun i =>
    (continuous_apply (e.symm i)).comp nativeDuffyCubeCanonical.continuous

theorem nativeDuffyCube_apply (e : Equiv.Perm (Fin 3)) (u : NativeCube) (i : Fin 3) :
    nativeDuffyCube e u i = ![u 0, u 0 * u 1, u 0 * u 1 * u 2] (e.symm i) := rfl

@[simp] theorem nativeDuffyCube_coordinate_zero (e : Equiv.Perm (Fin 3))
    (u : NativeCube) : nativeDuffyCube e u (e 0) = u 0 := by
  simp [nativeDuffyCube_apply]

@[simp] theorem nativeDuffyCube_coordinate_one (e : Equiv.Perm (Fin 3))
    (u : NativeCube) : nativeDuffyCube e u (e 1) = u 0 * u 1 := by
  simp [nativeDuffyCube_apply]

@[simp] theorem nativeDuffyCube_coordinate_two (e : Equiv.Perm (Fin 3))
    (u : NativeCube) : nativeDuffyCube e u (e 2) = u 0 * u 1 * u 2 := by
  simp [nativeDuffyCube_apply]

/-- All six parameter faces land in the boundary or an internal equality plane. -/
theorem nativeDuffyCube_boundary (e : Equiv.Perm (Fin 3)) (u : NativeCube)
    (hu : u ∈ Cube.boundary (Fin 3)) :
    nativeDuffyCube e u ∈ Cube.boundary (Fin 3) ∨
      ∃ i j : Fin 3, i ≠ j ∧ nativeDuffyCube e u i = nativeDuffyCube e u j := by
  rcases hu with ⟨j, hj⟩
  fin_cases j
  · change u 0 = 0 ∨ u 0 = 1 at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨e 0, Or.inl (by simpa using hj)⟩
    · exact Or.inl ⟨e 0, Or.inr (by simpa using hj)⟩
  · change u 1 = 0 ∨ u 1 = 1 at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨e 1, Or.inl (by simp [hj])⟩
    · exact Or.inr ⟨e 0, e 1, e.injective.ne (by decide), by simp [hj]⟩
  · change u 2 = 0 ∨ u 2 = 1 at hj
    rcases hj with hj | hj
    · exact Or.inl ⟨e 2, Or.inl (by simp [hj])⟩
    · exact Or.inr ⟨e 1, e 2, e.injective.ne (by decide), by simp [hj]⟩

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem nativeDuffyCube_based (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3))
    (u : NativeCube) (hu : u ∈ Cube.boundary (Fin 3)) :
    p (nativeDuffyCube e u) = x := by
  rcases nativeDuffyCube_boundary e u hu with h | ⟨i, j, hij, h⟩
  · exact p.property _ h
  · exact hp _ i j hij h

/-- The native three-loop obtained from an internally based cube by the Duffy map. -/
def nativeDuffyCubeLoop (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) :
    GenLoop (Fin 3) X x :=
  nativeCubePullbackLoop p (nativeDuffyCube e) (nativeDuffyCube_based p hp e)

@[simp] theorem nativeDuffyCubeLoop_apply (p : GenLoop (Fin 3) X x)
    (hp : NativeCubeInternalBased p) (e : Equiv.Perm (Fin 3)) (u : NativeCube) :
    nativeDuffyCubeLoop p hp e u = p (nativeDuffyCube e u) := rfl

end Wikipedia.HopfProblem.ThirdHurewicz
