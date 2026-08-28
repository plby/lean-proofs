import Wikipedia.HopfProblem.SpecialPeriodsTrianglePresentation
import Wikipedia.HopfProblem.EllipticFlatTorus

/-!
# Real lattice coordinates for the triangle-group representation

The constructed dual integral representation acts by real-linear
equivalences on the real period coordinates.  Every such equivalence
preserves the actual standard integral lattice, in both directions.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Extension of scalars of the constructed dual integral representation. -/
def triangleRealRepresentation : TriangleGroup →* (RealPlane₄ ≃ₗ[ℝ] RealPlane₄) :=
  Matrix.SpecialLinearGroup.toLin'.comp
    ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)).comp triangleDualRepresentation)

/-- The real-linear map induced by an element of the triangle group. -/
def triangleRealEquiv (g : TriangleGroup) : RealPlane₄ ≃ₗ[ℝ] RealPlane₄ :=
  triangleRealRepresentation g

theorem triangleRealEquiv_apply (g : TriangleGroup) (x : RealPlane₄) :
    triangleRealEquiv g x =
      (triangleDualRepresentation g : LatticeMatrix).map (Int.castRingHom ℝ) *ᵥ x := rfl

@[simp] theorem triangleRealEquiv_one :
    triangleRealEquiv 1 = LinearEquiv.refl ℝ RealPlane₄ :=
  triangleRealRepresentation.map_one

theorem triangleRealEquiv_mul (g h : TriangleGroup) :
    triangleRealEquiv (g * h) = triangleRealEquiv g * triangleRealEquiv h :=
  triangleRealRepresentation.map_mul g h

theorem triangleRealEquiv_mul_apply (g h : TriangleGroup) (x : RealPlane₄) :
    triangleRealEquiv (g * h) x = triangleRealEquiv g (triangleRealEquiv h x) := by
  rw [triangleRealEquiv_mul]
  rfl

@[simp] theorem triangleRealEquiv_inv (g : TriangleGroup) :
    triangleRealEquiv g⁻¹ = (triangleRealEquiv g).symm :=
  triangleRealRepresentation.map_inv g

/-- Integral coordinate vectors transform by the original integral matrix. -/
theorem triangleRealEquiv_realCast (g : TriangleGroup) (v : Lattice) :
    triangleRealEquiv g (Elliptic.realCast v) =
      Elliptic.realCast ((triangleDualRepresentation g : LatticeMatrix) *ᵥ v) := by
  rw [triangleRealEquiv_apply]
  ext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ)
    (triangleDualRepresentation g : LatticeMatrix) v i).symm

theorem triangleRealEquiv_mem_standardLattice (g : TriangleGroup) {x : RealPlane₄}
    (hx : x ∈ standardLattice) : triangleRealEquiv g x ∈ standardLattice := by
  obtain ⟨v, rfl⟩ := (Elliptic.standardLattice_mem_iff x).mp hx
  exact (Elliptic.standardLattice_mem_iff _).mpr
    ⟨(triangleDualRepresentation g : LatticeMatrix) *ᵥ v, triangleRealEquiv_realCast g v⟩

/-- The real representation preserves the standard lattice exactly, not
merely by inclusion. -/
theorem triangleRealEquiv_map_standardLattice (g : TriangleGroup) :
    standardLattice.map ((triangleRealEquiv g).restrictScalars ℤ).toLinearMap =
      standardLattice := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact triangleRealEquiv_mem_standardLattice g hy
  · intro hx
    refine ⟨triangleRealEquiv g⁻¹ x,
      triangleRealEquiv_mem_standardLattice g⁻¹ hx, ?_⟩
    change triangleRealEquiv g (triangleRealEquiv g⁻¹ x) = x
    rw [triangleRealEquiv_inv, LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.SpecialPeriods
