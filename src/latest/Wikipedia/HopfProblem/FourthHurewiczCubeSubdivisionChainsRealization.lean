import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionChainsSignedSum
import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometryFaces

/-!
# Realizing universal prism vertices in the native cube

The left vertex is the first interval coordinate; the right vertex is
one of the ordered vertices of an actual cube simplex. All dimensions
are left general for later higher Hurewicz constructions.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

open FirstHurewicz SingularMayerVietoris HigherHurewicz.CubeTriangulation

/-- The actual cube point associated to a universal interval-simplex vertex. -/
def prismCubeVertex {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) : CubeN (n + 1) :=
  Fin.cases (pathSimplex Path.id (stdVertices 1 z.1)) (cubeVertex e z.2)

@[simp] theorem prismCubeVertex_zero {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) :
    prismCubeVertex e z 0 = pathSimplex Path.id (stdVertices 1 z.1) := rfl

@[simp] theorem prismCubeVertex_succ {n : ℕ} (e : Equiv.Perm (Fin n))
    (z : Fin 2 × Fin (n + 1)) (i : Fin n) :
    prismCubeVertex e z i.succ = cubeVertex e z.2 i := rfl

/-- A universal prism simplex, realized by barycentric interpolation in the native cube. -/
def prismCubeSimplex {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) : C(Simplex m, CubeN (n + 1)) :=
  cubeAffineSimplex (fun j => prismCubeVertex e (v j))

theorem prismCubeVertex_swap_of_ne {n : ℕ} (e : Equiv.Perm (Fin (n + 1)))
    (i : Fin n) (z : Fin 2 × Fin (n + 2)) (hz : z.2 ≠ i.succ.castSucc) :
    prismCubeVertex e z = prismCubeVertex ((Equiv.swap i.castSucc i.succ).trans e) z := by
  funext coord
  refine Fin.cases ?_ (fun k => ?_) coord
  · rfl
  · exact congrFun (cubeVertex_swap_of_ne e i z.2 hz) k

theorem prismCubeSimplex_swap_of_omitted {m n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (v : Fin (m + 1) → Fin 2 × Fin (n + 2))
    (hv : ∀ j, (v j).2 ≠ i.succ.castSucc) :
    prismCubeSimplex e v =
      prismCubeSimplex ((Equiv.swap i.castSucc i.succ).trans e) v := by
  apply congrArg cubeAffineSimplex
  funext j
  exact prismCubeVertex_swap_of_ne e i (v j) (hv j)

theorem prismCubeSimplex_zero_of_left_zero {m n : ℕ} (e : Equiv.Perm (Fin n))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) (hv : ∀ j, (v j).1 = 0)
    (s : Simplex m) : prismCubeSimplex e v s 0 = 0 := by
  apply cubeAffineSimplex_constant_coordinate
  intro j
  simp [hv j, stdVertices]

theorem prismCubeSimplex_zero_of_last_omitted {m n : ℕ}
    (e : Equiv.Perm (Fin (n + 1)))
    (v : Fin (m + 1) → Fin 2 × Fin (n + 2))
    (hv : ∀ j, (v j).2 ≠ Fin.last (n + 1)) (s : Simplex m) :
    prismCubeSimplex e v s (e (Fin.last n)).succ = 0 := by
  apply cubeAffineSimplex_constant_coordinate
  intro j
  simp only [prismCubeVertex_succ, cubeVertex, Equiv.symm_apply_apply, Fin.val_last]
  apply if_neg
  have hne : (v j).2.val ≠ n + 1 := by
    intro h
    exact hv j (Fin.ext h)
  have hlt := (v j).2.isLt
  omega

variable {X : Type} [TopologicalSpace X]

/-- Realize formal prism chains through one fixed native cube map and coordinate order. -/
def prismCubeRealization {n : ℕ} (p : C(CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) :
    FormalChains (Fin 2 × Fin (n + 1)) (m + 1) →ₗ[ℤ] Chains X m :=
  formalLift fun v => simplexChain X m (p.comp (prismCubeSimplex e v))

@[simp] theorem prismCubeRealization_simplex {n : ℕ} (p : C(CubeN (n + 1), X))
    (e : Equiv.Perm (Fin n)) (m : ℕ) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    prismCubeRealization p e m (formalSimplex v) =
      simplexChain X m (p.comp (prismCubeSimplex e v)) := formalLift_simplex _ _

/-- Signed realization over all actual right-cube coordinate permutations. -/
def orientedPrismRealization {n : ℕ} (p : C(CubeN (n + 1), X)) (m : ℕ) :
    FormalChains (Fin 2 × Fin (n + 1)) (m + 1) →ₗ[ℤ] Chains X m :=
  formalLift fun v => ∑ e : Equiv.Perm (Fin n),
    cubeOrientation e • simplexChain X m (p.comp (prismCubeSimplex e v))

@[simp] theorem orientedPrismRealization_simplex {n : ℕ}
    (p : C(CubeN (n + 1), X)) (m : ℕ) (v : Fin (m + 1) → Fin 2 × Fin (n + 1)) :
    orientedPrismRealization p m (formalSimplex v) =
      ∑ e : Equiv.Perm (Fin n),
        cubeOrientation e • simplexChain X m (p.comp (prismCubeSimplex e v)) :=
  formalLift_simplex _ _

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
