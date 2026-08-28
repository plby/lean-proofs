import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationCover

/-!
# Continuous pasting over the permutation simplices of any finite cube

The actual compact quotient cover gives continuous pasting into an
arbitrary topological target, with exact restrictions to each simplex.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeGluing

open FirstHurewicz CubeTriangulation

variable {n : ℕ} {X : Type} [TopologicalSpace X]

/-- Agreement whenever two actual simplex points have the same cube image. -/
def CubeCompatible (F : Equiv.Perm (Fin n) → C(I × Simplex n, X)) : Prop :=
  ∀ (e f : Equiv.Perm (Fin n)) (s t : Simplex n),
    cubeSimplex e s = cubeSimplex f t → ∀ r : I, F e (r, s) = F f (r, t)

def cubeFamilyMap (F : Equiv.Perm (Fin n) → C(I × Simplex n, X)) :
    C((Σ _e : Equiv.Perm (Fin n), I × Simplex n), X) where
  toFun a := F a.fst a.snd
  continuous_toFun := continuous_sigma fun e => (F e).continuous

theorem cubeFamilyMap_factorsThrough
    (F : Equiv.Perm (Fin n) → C(I × Simplex n, X)) (hF : CubeCompatible F) :
    Function.FactorsThrough (cubeFamilyMap F) (cubeCylinderCover n) := by
  rintro ⟨e, r, s⟩ ⟨f, q, t⟩ h
  have hr : r = q := congrArg Prod.fst h
  have hs : cubeSimplex e s = cubeSimplex f t := congrArg Prod.snd h
  subst q
  exact hF e f s t hs r

/-- The actual continuous map pasted from the permutation-simplex cylinders. -/
def glueCubeHomotopies (F : Equiv.Perm (Fin n) → C(I × Simplex n, X))
    (hF : CubeCompatible F) : C(I × CubeN n, X) :=
  (cubeCylinderCover_isQuotientMap n).lift (cubeFamilyMap F)
    (cubeFamilyMap_factorsThrough F hF)

@[simp] theorem glueCubeHomotopies_cell
    (F : Equiv.Perm (Fin n) → C(I × Simplex n, X)) (hF : CubeCompatible F)
    (e : Equiv.Perm (Fin n)) (r : I) (s : Simplex n) :
    glueCubeHomotopies F hF (r, cubeSimplex e s) = F e (r, s) :=
  DFunLike.congr_fun
    ((cubeCylinderCover_isQuotientMap n).lift_comp (cubeFamilyMap F)
      (cubeFamilyMap_factorsThrough F hF)) ⟨e, (r, s)⟩

theorem glueCubeHomotopies_comp_cell
    (F : Equiv.Perm (Fin n) → C(I × Simplex n, X)) (hF : CubeCompatible F)
    (e : Equiv.Perm (Fin n)) :
    (glueCubeHomotopies F hF).comp (cubeSimplexCylinder e) = F e := by
  ext u
  exact glueCubeHomotopies_cell F hF e u.1 u.2

theorem glueCubeHomotopies_time
    (F : Equiv.Perm (Fin n) → C(I × Simplex n, X)) (hF : CubeCompatible F)
    (r : I) (g : CubeN n → X)
    (h : ∀ (e : Equiv.Perm (Fin n)) (s : Simplex n), F e (r, s) = g (cubeSimplex e s))
    (u : CubeN n) : glueCubeHomotopies F hF (r, u) = g u := by
  obtain ⟨e, s, rfl⟩ := exists_cubeSimplex u
  exact (glueCubeHomotopies_cell F hF e r s).trans (h e s)

theorem glueCubeHomotopies_zero
    (F : Equiv.Perm (Fin n) → C(I × Simplex n, X)) (hF : CubeCompatible F)
    (g : C(CubeN n, X))
    (h : ∀ (e : Equiv.Perm (Fin n)) (s : Simplex n), F e (0, s) = g (cubeSimplex e s))
    (u : CubeN n) : glueCubeHomotopies F hF (0, u) = g u :=
  glueCubeHomotopies_time F hF 0 g h u

theorem glueCubeHomotopies_unique
    (F : Equiv.Perm (Fin n) → C(I × Simplex n, X)) (hF : CubeCompatible F)
    (G : C(I × CubeN n, X))
    (hG : ∀ (e : Equiv.Perm (Fin n)) (r : I) (s : Simplex n),
      G (r, cubeSimplex e s) = F e (r, s)) : G = glueCubeHomotopies F hF := by
  ext u
  rcases u with ⟨r, u⟩
  obtain ⟨e, s, rfl⟩ := exists_cubeSimplex u
  exact (hG e r s).trans (glueCubeHomotopies_cell F hF e r s).symm

end Wikipedia.HopfProblem.HigherHurewicz.CubeGluing
