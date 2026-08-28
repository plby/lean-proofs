import Wikipedia.HopfProblem.ThirdHurewiczCubeGluingCompatibility

/-!
# The actual boundary-fixed cube homotopy from coherent simplex homotopies

Coherent triangle and tetrahedron homotopies paste over the original six
affine tetrahedra. If the constant triangle is fixed, the whole cube
boundary is fixed. If tetrahedron homotopies start at the original maps,
the result is a genuine native generalized-loop homotopy, with exact
terminal restrictions on every original tetrahedron.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz.CubeGluing

open FirstHurewicz Geometry CubeTriangulation SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] {x : X}
  (H₂ : C(Simplex 2, X) → C(I × Simplex 2, X))
  (H₃ : C(Simplex 3, X) → C(I × Simplex 3, X))
  (hface : FaceCompatibleHomotopies 2 H₂ H₃)

/-- The actual jointly continuous cube homotopy obtained by finite tetrahedral pasting. -/
def coherentCubeHomotopyMap (p : GenLoop (Fin 3) X x) : C(I × Cube3, X) :=
  glueCubeHomotopies (fun e => H₃ (p.val.comp (cubeTetrahedron e)))
    (coherentCubeFamily_compatible H₂ H₃ hface p)

@[simp] theorem coherentCubeHomotopyMap_cell (p : GenLoop (Fin 3) X x)
    (e : Equiv.Perm (Fin 3)) (r : I) (s : Simplex 3) :
    coherentCubeHomotopyMap H₂ H₃ hface p (r, cubeTetrahedron e s) =
      H₃ (p.val.comp (cubeTetrahedron e)) (r, s) :=
  glueCubeHomotopies_cell _ _ e r s

theorem coherentCubeHomotopyMap_zero
    (hzero : ∀ (smp : C(Simplex 3, X)) (s : Simplex 3), H₃ smp (0, s) = smp s)
    (p : GenLoop (Fin 3) X x) (u : Cube3) :
    coherentCubeHomotopyMap H₂ H₃ hface p (0, u) = p u :=
  glueCubeHomotopies_zero _ _ p.val
    (fun e s => hzero (p.val.comp (cubeTetrahedron e)) s) u

variable (hconst : H₂ (ContinuousMap.const (Simplex 2) x) =
  ContinuousMap.const (I × Simplex 2) x)

include hconst

/-- Every point of the original cube boundary is fixed at every time. -/
theorem coherentCubeHomotopyMap_boundary (p : GenLoop (Fin 3) X x)
    (r : I) (u : Cube3) (hu : u ∈ Cube.boundary (Fin 3)) :
    coherentCubeHomotopyMap H₂ H₃ hface p (r, u) = x := by
  obtain ⟨e, s, rfl⟩ := exists_cubeTetrahedron u
  rw [coherentCubeHomotopyMap_cell]
  exact coherentCubeCell_boundary H₂ H₃ hface hconst p e r s hu

/-- The terminal map is an actual native generalized three-loop. -/
def coherentCubeEndpoint (p : GenLoop (Fin 3) X x) : GenLoop (Fin 3) X x :=
  ⟨timeSlice (coherentCubeHomotopyMap H₂ H₃ hface p) 1,
    fun u hu => coherentCubeHomotopyMap_boundary H₂ H₃ hface hconst p 1 u hu⟩

@[simp] theorem coherentCubeEndpoint_val (p : GenLoop (Fin 3) X x) :
    (coherentCubeEndpoint H₂ H₃ hface hconst p).val =
      timeSlice (coherentCubeHomotopyMap H₂ H₃ hface p) 1 := rfl

/-- Each original tetrahedron has exactly the prescribed terminal simplex map. -/
theorem coherentCubeEndpoint_cell (p : GenLoop (Fin 3) X x) (e : Equiv.Perm (Fin 3)) :
    (coherentCubeEndpoint H₂ H₃ hface hconst p).val.comp (cubeTetrahedron e) =
      timeSlice (H₃ (p.val.comp (cubeTetrahedron e))) 1 := by
  ext s
  exact coherentCubeHomotopyMap_cell H₂ H₃ hface p e 1 s

variable (hzero : ∀ (smp : C(Simplex 3, X)) (s : Simplex 3), H₃ smp (0, s) = smp s)

include hzero

/-- The genuine homotopy relative to Mathlib's original cube boundary. -/
def coherentCubeHomotopy (p : GenLoop (Fin 3) X x) :
    p.val.HomotopyRel (coherentCubeEndpoint H₂ H₃ hface hconst p).val
      (Cube.boundary (Fin 3)) where
  toHomotopy :=
    { toContinuousMap := coherentCubeHomotopyMap H₂ H₃ hface p
      map_zero_left := coherentCubeHomotopyMap_zero H₂ H₃ hface hzero p
      map_one_left _ := rfl }
  prop' r u hu :=
    (coherentCubeHomotopyMap_boundary H₂ H₃ hface hconst p r u hu).trans
      (GenLoop.boundary p u hu).symm

@[simp] theorem coherentCubeHomotopy_cell (p : GenLoop (Fin 3) X x)
    (e : Equiv.Perm (Fin 3)) (r : I) (s : Simplex 3) :
    coherentCubeHomotopy H₂ H₃ hface hconst hzero p (r, cubeTetrahedron e s) =
      H₃ (p.val.comp (cubeTetrahedron e)) (r, s) :=
  coherentCubeHomotopyMap_cell H₂ H₃ hface p e r s

theorem coherentCube_homotopic (p : GenLoop (Fin 3) X x) :
    GenLoop.Homotopic p (coherentCubeEndpoint H₂ H₃ hface hconst p) :=
  ⟨coherentCubeHomotopy H₂ H₃ hface hconst hzero p⟩

/-- Equality in the actual native third-homotopy quotient. -/
theorem coherentCube_quotient (p : GenLoop (Fin 3) X x) :
    (⟦p⟧ : π_ 3 X x) = ⟦coherentCubeEndpoint H₂ H₃ hface hconst p⟧ :=
  Quotient.sound (coherentCube_homotopic H₂ H₃ hface hconst hzero p)

end Wikipedia.HopfProblem.ThirdHurewicz.CubeGluing
