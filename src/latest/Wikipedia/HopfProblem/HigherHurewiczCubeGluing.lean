import Wikipedia.HopfProblem.HigherHurewiczCubeGluingCompatibility

/-!
# Native boundary-fixed cube homotopies in arbitrary positive dimension

Coherent simplex homotopies paste over all affine permutation simplices.
Fixing the constant lower-dimensional simplex fixes the entire cube
boundary. Starting at the original simplex maps gives a genuine native
generalized-loop homotopy, with literal prescribed terminal restrictions.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeGluing

open FirstHurewicz CubeTriangulation SecondHurewicz.SimplyConnected

variable {n : ℕ} {X : Type} [TopologicalSpace X] {x : X}
  (H₀ : C(Simplex n, X) → C(I × Simplex n, X))
  (H₁ : C(Simplex (n + 1), X) → C(I × Simplex (n + 1), X))
  (hface : FaceCompatibleHomotopies n H₀ H₁)

/-- The actual jointly continuous homotopy obtained by finite simplex pasting. -/
def coherentCubeHomotopyMap (p : GenLoop (Fin (n + 1)) X x) : C(I × CubeN (n + 1), X) :=
  glueCubeHomotopies (fun e => H₁ (p.val.comp (cubeSimplex e)))
    (coherentCubeFamily_compatible H₀ H₁ hface p)

@[simp] theorem coherentCubeHomotopyMap_cell (p : GenLoop (Fin (n + 1)) X x)
    (e : Equiv.Perm (Fin (n + 1))) (r : I) (s : Simplex (n + 1)) :
    coherentCubeHomotopyMap H₀ H₁ hface p (r, cubeSimplex e s) =
      H₁ (p.val.comp (cubeSimplex e)) (r, s) :=
  glueCubeHomotopies_cell _ _ e r s

theorem coherentCubeHomotopyMap_zero
    (hzero : ∀ (smp : C(Simplex (n + 1), X)) (s : Simplex (n + 1)), H₁ smp (0, s) = smp s)
    (p : GenLoop (Fin (n + 1)) X x) (u : CubeN (n + 1)) :
    coherentCubeHomotopyMap H₀ H₁ hface p (0, u) = p u :=
  glueCubeHomotopies_zero _ _ p.val
    (fun e s => hzero (p.val.comp (cubeSimplex e)) s) u

variable (hconst : H₀ (ContinuousMap.const (Simplex n) x) =
  ContinuousMap.const (I × Simplex n) x)

include hconst

/-- Every point of the original cube boundary is fixed at every time. -/
theorem coherentCubeHomotopyMap_boundary (p : GenLoop (Fin (n + 1)) X x)
    (r : I) (u : CubeN (n + 1)) (hu : u ∈ Cube.boundary (Fin (n + 1))) :
    coherentCubeHomotopyMap H₀ H₁ hface p (r, u) = x := by
  obtain ⟨e, s, rfl⟩ := exists_cubeSimplex u
  rw [coherentCubeHomotopyMap_cell]
  exact coherentCubeCell_boundary H₀ H₁ hface hconst p e r s hu

/-- The terminal map is a genuine native generalized loop. -/
def coherentCubeEndpoint (p : GenLoop (Fin (n + 1)) X x) : GenLoop (Fin (n + 1)) X x :=
  ⟨timeSlice (coherentCubeHomotopyMap H₀ H₁ hface p) 1,
    fun u hu => coherentCubeHomotopyMap_boundary H₀ H₁ hface hconst p 1 u hu⟩

@[simp] theorem coherentCubeEndpoint_val (p : GenLoop (Fin (n + 1)) X x) :
    (coherentCubeEndpoint H₀ H₁ hface hconst p).val =
      timeSlice (coherentCubeHomotopyMap H₀ H₁ hface p) 1 := rfl

/-- Each original permutation cell has exactly its prescribed terminal simplex map. -/
theorem coherentCubeEndpoint_cell (p : GenLoop (Fin (n + 1)) X x)
    (e : Equiv.Perm (Fin (n + 1))) :
    (coherentCubeEndpoint H₀ H₁ hface hconst p).val.comp (cubeSimplex e) =
      timeSlice (H₁ (p.val.comp (cubeSimplex e))) 1 := by
  ext s
  exact coherentCubeHomotopyMap_cell H₀ H₁ hface p e 1 s

variable (hzero : ∀ (smp : C(Simplex (n + 1), X)) (s : Simplex (n + 1)), H₁ smp (0, s) = smp s)

include hzero

/-- The genuine homotopy relative to Mathlib's original cube boundary. -/
def coherentCubeHomotopy (p : GenLoop (Fin (n + 1)) X x) :
    p.val.HomotopyRel (coherentCubeEndpoint H₀ H₁ hface hconst p).val
      (Cube.boundary (Fin (n + 1))) where
  toHomotopy :=
    { toContinuousMap := coherentCubeHomotopyMap H₀ H₁ hface p
      map_zero_left := coherentCubeHomotopyMap_zero H₀ H₁ hface hzero p
      map_one_left _ := rfl }
  prop' r u hu :=
    (coherentCubeHomotopyMap_boundary H₀ H₁ hface hconst p r u hu).trans
      (GenLoop.boundary p u hu).symm

@[simp] theorem coherentCubeHomotopy_cell (p : GenLoop (Fin (n + 1)) X x)
    (e : Equiv.Perm (Fin (n + 1))) (r : I) (s : Simplex (n + 1)) :
    coherentCubeHomotopy H₀ H₁ hface hconst hzero p (r, cubeSimplex e s) =
      H₁ (p.val.comp (cubeSimplex e)) (r, s) :=
  coherentCubeHomotopyMap_cell H₀ H₁ hface p e r s

theorem coherentCube_homotopic (p : GenLoop (Fin (n + 1)) X x) :
    GenLoop.Homotopic p (coherentCubeEndpoint H₀ H₁ hface hconst p) :=
  ⟨coherentCubeHomotopy H₀ H₁ hface hconst hzero p⟩

/-- Equality in the actual native homotopy quotient. -/
theorem coherentCube_quotient (p : GenLoop (Fin (n + 1)) X x) :
    (⟦p⟧ : π_ (n + 1) X x) = ⟦coherentCubeEndpoint H₀ H₁ hface hconst p⟧ :=
  Quotient.sound (coherentCube_homotopic H₀ H₁ hface hconst hzero p)

end Wikipedia.HopfProblem.HigherHurewicz.CubeGluing
