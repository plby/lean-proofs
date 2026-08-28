import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangTopLattice

/-!
# The exact cokernel inside the third-exterior invariant lattice

The third-exterior column lattice has index three or four in the full
invariant lattice, independently of the retained integer shear.  The
quotient is given by an explicit residue, not merely by a rational rank
or a determinant computation.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang

open Elliptic PeriodTorusHigherHomologyExterior

/-- The actual integral fixed lattice of the original third exterior matrix. -/
def topInvariantLattice (j : Kind) : Submodule ℤ Lattice :=
  LinearMap.ker ((LocalSystemMatrices.exteriorCube j.matrix).mulVecLin - LinearMap.id)

theorem mem_topInvariantLattice (j : Kind) (v : Lattice) :
    v ∈ topInvariantLattice j ↔ LocalSystemMatrices.exteriorCube j.matrix *ᵥ v = v := by
  change LocalSystemMatrices.exteriorCube j.matrix *ᵥ v - v = 0 ↔ _
  exact sub_eq_zero

/-- The two columns land in the full original invariant lattice. -/
theorem topWangMatrix_mem_invariants (j : Kind) (c : ℤ) (a : Fin 2 → ℤ) :
    topWangMatrix j c *ᵥ a ∈ topInvariantLattice j := by
  rw [mem_topInvariantLattice]
  cases j
  · change cubeA₁ *ᵥ (topWangMatrix .three c *ᵥ a) = _
    exact ((topWangMatrix_mem_range_three_iff_fixed c _).mp ⟨a, rfl⟩).1
  · change cubeA₂ *ᵥ (topWangMatrix .four c *ᵥ a) = _
    exact ((topWangMatrix_mem_range_four_iff_fixed c _).mp ⟨a, rfl⟩).1

/-- The same integer matrix, with codomain restricted to the full invariant lattice. -/
def topWangInvariantMap (j : Kind) (c : ℤ) :
    (Fin 2 → ℤ) →ₗ[ℤ] topInvariantLattice j :=
  (topWangMatrix j c).mulVecLin.codRestrict _ (topWangMatrix_mem_invariants j c)

@[simp] theorem topWangInvariantMap_val (j : Kind) (c : ℤ) (a : Fin 2 → ℤ) :
    (topWangInvariantMap j c a).val = topWangMatrix j c *ᵥ a := rfl

theorem topWangInvariantMap_mem_range (j : Kind) (c : ℤ) (v : topInvariantLattice j) :
    v ∈ LinearMap.range (topWangInvariantMap j c) ↔
      v.val ∈ LinearMap.range (topWangMatrix j c).mulVecLin := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

/-- Only the order-four residue needs the actual shear correction. -/
def topResidueCoefficient : Kind → ℤ → ℤ
  | .three, _ => 0
  | .four, c => 2 * c

/-- The explicit residue on the full third-exterior invariant lattice. -/
def topInvariantResidue (j : Kind) (c : ℤ) :
    topInvariantLattice j →ₗ[ℤ] ZMod j.order :=
  (Int.castAddHom (ZMod j.order)).toIntLinearMap.comp
    (((LinearMap.proj 3 : Lattice →ₗ[ℤ] ℤ) +
        topResidueCoefficient j c • LinearMap.proj 1).comp (topInvariantLattice j).subtype)

@[simp] theorem topInvariantResidue_apply (j : Kind) (c : ℤ) (v : topInvariantLattice j) :
    topInvariantResidue j c v =
      ((v.val 3 + topResidueCoefficient j c * v.val 1 : ℤ) : ZMod j.order) := by
  simp [topInvariantResidue]

/-- Every integer multiple of the positive `uwδ` vector is an actual invariant. -/
def topInvariantVertical (j : Kind) (k : ℤ) : topInvariantLattice j :=
  ⟨![0, 0, 0, k], by
    rw [mem_topInvariantLattice]
    cases j
    · change cubeA₁ *ᵥ ![0, 0, 0, k] = _
      rw [cubeA₁_fixed_iff]
      constructor <;> simp
    · change cubeA₂ *ᵥ ![0, 0, 0, k] = _
      rw [cubeA₂_fixed_iff]
      constructor <;> simp⟩

@[simp] theorem topInvariantResidue_vertical (j : Kind) (c k : ℤ) :
    topInvariantResidue j c (topInvariantVertical j k) = (k : ZMod j.order) := by
  rw [topInvariantResidue_apply]
  simp [topInvariantVertical]

/-- The residue is surjective on the integral invariant lattice. -/
theorem topInvariantResidue_surjective (j : Kind) (c : ℤ) :
    Function.Surjective (topInvariantResidue j c) := by
  intro z
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨topInvariantVertical j k, topInvariantResidue_vertical j c k⟩

/-- Exactness over the integers, including the shear-sensitive order-four congruence. -/
theorem topWangInvariantMap_range_eq_ker (j : Kind) (c : ℤ) :
    LinearMap.range (topWangInvariantMap j c) = LinearMap.ker (topInvariantResidue j c) := by
  ext v
  rw [topWangInvariantMap_mem_range, LinearMap.mem_ker, topInvariantResidue_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hv := (mem_topInvariantLattice j v.val).mp v.property
  cases j
  · change cubeA₁ *ᵥ v.val = v.val at hv
    rw [topWangMatrix_mem_range_three_iff_fixed]
    simp [hv, topResidueCoefficient, Kind.order]
  · change cubeA₂ *ᵥ v.val = v.val at hv
    rw [topWangMatrix_mem_range_four_iff_fixed]
    simp [hv, topResidueCoefficient, Kind.order]

/-- The exact invariant-lattice quotient is the stated cyclic group. -/
def topWangInvariantCokernelEquiv (j : Kind) (c : ℤ) :
    (topInvariantLattice j ⧸ LinearMap.range (topWangInvariantMap j c)) ≃ₗ[ℤ] ZMod j.order :=
  (Submodule.quotEquivOfEq _ _ (topWangInvariantMap_range_eq_ker j c)).trans
    ((topInvariantResidue j c).quotKerEquivOfSurjective (topInvariantResidue_surjective j c))

@[simp] theorem topWangInvariantCokernelEquiv_mk (j : Kind) (c : ℤ)
    (v : topInvariantLattice j) :
    topWangInvariantCokernelEquiv j c (Submodule.Quotient.mk v) =
      ((v.val 3 + topResidueCoefficient j c * v.val 1 : ℤ) : ZMod j.order) := by
  change topInvariantResidue j c v = _
  exact topInvariantResidue_apply j c v

/-- The exact index is three or four, for every retained integral shear. -/
theorem topWangInvariantMap_index (j : Kind) (c : ℤ) :
    (LinearMap.range (topWangInvariantMap j c)).toAddSubgroup.index = j.order := by
  change Nat.card (topInvariantLattice j ⧸ LinearMap.range (topWangInvariantMap j c)) = _
  exact (Nat.card_congr (topWangInvariantCokernelEquiv j c).toEquiv).trans
    (Nat.card_zmod j.order)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticCapKernelWang
