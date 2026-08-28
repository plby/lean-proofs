import Wikipedia.HopfProblem.ThirdHurewiczCubeTriangulationCover

/-!
# Pasting compatible maps on the six actual tetrahedral cylinders

The compact quotient cover gives genuine continuous pasting into an
arbitrary topological target, with exact restrictions on each tetrahedron.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeGluing

open FirstHurewicz Geometry CubeTriangulation

variable {X : Type} [TopologicalSpace X]

/-- Agreement whenever two actual tetrahedral points have the same cube image. -/
def CubeCompatible (F : Equiv.Perm (Fin 3) → C(I × Simplex 3, X)) : Prop :=
  ∀ (e f : Equiv.Perm (Fin 3)) (s t : Simplex 3),
    cubeTetrahedron e s = cubeTetrahedron f t → ∀ r : I, F e (r, s) = F f (r, t)

def cubeFamilyMap (F : Equiv.Perm (Fin 3) → C(I × Simplex 3, X)) :
    C((Σ _e : Equiv.Perm (Fin 3), I × Simplex 3), X) where
  toFun a := F a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (F e).continuous

theorem cubeFamilyMap_factorsThrough
    (F : Equiv.Perm (Fin 3) → C(I × Simplex 3, X)) (hF : CubeCompatible F) :
    Function.FactorsThrough (cubeFamilyMap F) cubeCylinderCover := by
  rintro ⟨e, r, s⟩ ⟨f, q, t⟩ h
  have hr : r = q := congrArg Prod.fst h
  have hs : cubeTetrahedron e s = cubeTetrahedron f t := congrArg Prod.snd h
  subst q
  exact hF e f s t hs r

/-- The actual continuous map pasted from the six tetrahedral cylinders. -/
def glueCubeHomotopies (F : Equiv.Perm (Fin 3) → C(I × Simplex 3, X))
    (hF : CubeCompatible F) : C(I × Cube3, X) :=
  cubeCylinderCover_isQuotientMap.lift (cubeFamilyMap F)
    (cubeFamilyMap_factorsThrough F hF)

@[simp] theorem glueCubeHomotopies_cell
    (F : Equiv.Perm (Fin 3) → C(I × Simplex 3, X)) (hF : CubeCompatible F)
    (e : Equiv.Perm (Fin 3)) (r : I) (s : Simplex 3) :
    glueCubeHomotopies F hF (r, cubeTetrahedron e s) = F e (r, s) :=
  DFunLike.congr_fun
    (cubeCylinderCover_isQuotientMap.lift_comp (cubeFamilyMap F)
      (cubeFamilyMap_factorsThrough F hF)) ⟨e, (r, s)⟩

theorem glueCubeHomotopies_comp_cell
    (F : Equiv.Perm (Fin 3) → C(I × Simplex 3, X)) (hF : CubeCompatible F)
    (e : Equiv.Perm (Fin 3)) :
    (glueCubeHomotopies F hF).comp (cubeTetrahedronCylinder e) = F e := by
  ext u
  exact glueCubeHomotopies_cell F hF e u.1 u.2

theorem glueCubeHomotopies_time
    (F : Equiv.Perm (Fin 3) → C(I × Simplex 3, X)) (hF : CubeCompatible F)
    (r : I) (g : Cube3 → X)
    (h : ∀ (e : Equiv.Perm (Fin 3)) (s : Simplex 3), F e (r, s) = g (cubeTetrahedron e s))
    (u : Cube3) : glueCubeHomotopies F hF (r, u) = g u := by
  obtain ⟨e, s, rfl⟩ := exists_cubeTetrahedron u
  exact (glueCubeHomotopies_cell F hF e r s).trans (h e s)

theorem glueCubeHomotopies_zero
    (F : Equiv.Perm (Fin 3) → C(I × Simplex 3, X)) (hF : CubeCompatible F)
    (g : C(Cube3, X))
    (h : ∀ (e : Equiv.Perm (Fin 3)) (s : Simplex 3), F e (0, s) = g (cubeTetrahedron e s))
    (u : Cube3) : glueCubeHomotopies F hF (0, u) = g u :=
  glueCubeHomotopies_time F hF 0 g h u

theorem glueCubeHomotopies_unique
    (F : Equiv.Perm (Fin 3) → C(I × Simplex 3, X)) (hF : CubeCompatible F)
    (G : C(I × Cube3, X))
    (hG : ∀ (e : Equiv.Perm (Fin 3)) (r : I) (s : Simplex 3),
      G (r, cubeTetrahedron e s) = F e (r, s)) : G = glueCubeHomotopies F hF := by
  ext u
  rcases u with ⟨r, u⟩
  obtain ⟨e, s, rfl⟩ := exists_cubeTetrahedron u
  exact (hG e r s).trans (glueCubeHomotopies_cell F hF e r s).symm

end Wikipedia.HopfProblem.ThirdHurewicz.CubeGluing
