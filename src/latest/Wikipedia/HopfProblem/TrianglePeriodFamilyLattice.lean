import Wikipedia.HopfProblem.TrianglePeriodFamilyLatticeLinear

/-!
# The triangle group's action on the actual real period torus

The checked integral dual representation preserves the standard lattice.
Its descended maps are continuous linear automorphisms of the actual
quotient torus.  They form a genuine permutation representation and a
selected continuous action, whose lift is the prescribed matrix action.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Each integral monodromy induces an actual linear automorphism of the
real torus, viewed as a `ℤ`-module quotient. -/
def triangleTorusLinearEquiv (g : TriangleGroup) : RealTorus₄ ≃ₗ[ℤ] RealTorus₄ :=
  Submodule.Quotient.equiv standardLattice standardLattice
    ((triangleRealEquiv g).restrictScalars ℤ) (triangleRealEquiv_map_standardLattice g)

/-- Both directions of the descended lattice automorphism are continuous
for the actual quotient topology. -/
def triangleTorusHomeomorph (g : TriangleGroup) : RealTorus₄ ≃ₜ RealTorus₄ where
  toEquiv := (triangleTorusLinearEquiv g).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp
      (triangleRealEquiv g).toContinuousLinearEquiv.continuous
  continuous_invFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp
      (triangleRealEquiv g).symm.toContinuousLinearEquiv.continuous

@[simp] theorem triangleTorusHomeomorph_mkQ (g : TriangleGroup) (x : RealPlane₄) :
    triangleTorusHomeomorph g (standardLattice.mkQ x) =
      standardLattice.mkQ (triangleRealEquiv g x) := rfl

@[simp] theorem triangleTorusHomeomorph_zero (g : TriangleGroup) :
    triangleTorusHomeomorph g 0 = 0 := (triangleTorusLinearEquiv g).map_zero

theorem triangleTorusHomeomorph_add (g : TriangleGroup) (x y : RealTorus₄) :
    triangleTorusHomeomorph g (x + y) =
      triangleTorusHomeomorph g x + triangleTorusHomeomorph g y :=
  (triangleTorusLinearEquiv g).map_add x y

@[simp] theorem triangleTorusHomeomorph_one_apply (x : RealTorus₄) :
    triangleTorusHomeomorph 1 x = x := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [triangleTorusHomeomorph_mkQ, triangleRealEquiv_one]
  rfl

@[simp] theorem triangleTorusHomeomorph_one :
    triangleTorusHomeomorph 1 = Homeomorph.refl RealTorus₄ := by
  apply Homeomorph.ext
  exact triangleTorusHomeomorph_one_apply

theorem triangleTorusHomeomorph_mul_apply (g h : TriangleGroup) (x : RealTorus₄) :
    triangleTorusHomeomorph (g * h) x =
      triangleTorusHomeomorph g (triangleTorusHomeomorph h x) := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [triangleTorusHomeomorph_mkQ, triangleTorusHomeomorph_mkQ,
    triangleTorusHomeomorph_mkQ, triangleRealEquiv_mul_apply]

theorem triangleTorusHomeomorph_mul (g h : TriangleGroup) :
    triangleTorusHomeomorph (g * h) =
      (triangleTorusHomeomorph h).trans (triangleTorusHomeomorph g) := by
  apply Homeomorph.ext
  exact triangleTorusHomeomorph_mul_apply g h

@[simp] theorem triangleTorusHomeomorph_inv (g : TriangleGroup) :
    triangleTorusHomeomorph g⁻¹ = (triangleTorusHomeomorph g).symm := by
  apply Homeomorph.ext
  intro x
  apply (triangleTorusHomeomorph g).injective
  rw [← triangleTorusHomeomorph_mul_apply, mul_inv_cancel,
    triangleTorusHomeomorph_one_apply, Homeomorph.apply_symm_apply]

/-- The descended homeomorphisms form an actual permutation representation. -/
def triangleTorusPermutationHom : TriangleGroup →* Equiv.Perm RealTorus₄ where
  toFun g := (triangleTorusHomeomorph g).toEquiv
  map_one' := by
    apply Equiv.ext
    exact triangleTorusHomeomorph_one_apply
  map_mul' g h := by
    apply Equiv.ext
    exact triangleTorusHomeomorph_mul_apply g h

@[simp] theorem triangleTorusPermutationHom_apply (g : TriangleGroup) (x : RealTorus₄) :
    triangleTorusPermutationHom g x = triangleTorusHomeomorph g x := rfl

/-- The actual selected triangle-group action on the lattice quotient.
It is not installed as a global instance. -/
@[instance_reducible] def triangleTorusAction : MulAction TriangleGroup RealTorus₄ where
  smul g x := triangleTorusHomeomorph g x
  one_smul := triangleTorusHomeomorph_one_apply
  mul_smul := triangleTorusHomeomorph_mul_apply

theorem triangleTorusAction_apply (g : TriangleGroup) (x : RealTorus₄) :
    letI := triangleTorusAction
    g • x = triangleTorusHomeomorph g x := rfl

/-- The lift formula uses the actual inverse-transpose integral representation. -/
theorem triangleTorusAction_mkQ (g : TriangleGroup) (x : RealPlane₄) :
    letI := triangleTorusAction
    g • standardLattice.mkQ x =
      standardLattice.mkQ
        ((triangleDualRepresentation g : LatticeMatrix).map (Int.castRingHom ℝ) *ᵥ x) := by
  change triangleTorusHomeomorph g (standardLattice.mkQ x) = _
  rw [triangleTorusHomeomorph_mkQ, triangleRealEquiv_apply]

/-- The monodromy action fixes the genuine zero class of the torus. -/
@[simp] theorem triangleTorusAction_zero (g : TriangleGroup) :
    letI := triangleTorusAction
    g • (0 : RealTorus₄) = 0 := triangleTorusHomeomorph_zero g

theorem triangleTorusAction_add (g : TriangleGroup) (x y : RealTorus₄) :
    letI := triangleTorusAction
    g • (x + y) = g • x + g • y := triangleTorusHomeomorph_add g x y

/-- Each group element acts continuously in the actual quotient topology. -/
theorem triangleTorusAction_continuous :
    letI := triangleTorusAction
    ContinuousConstSMul TriangleGroup RealTorus₄ := by
  let := triangleTorusAction
  exact ⟨fun g => (triangleTorusHomeomorph g).continuous⟩

/-- With the discrete topology on the abstract triangle group, this is
a jointly continuous group action. -/
theorem triangleTorusAction_continuousSMul [TopologicalSpace TriangleGroup]
    [DiscreteTopology TriangleGroup] :
    letI := triangleTorusAction
    ContinuousSMul TriangleGroup RealTorus₄ := by
  let := triangleTorusAction
  exact ⟨continuous_prod_of_discrete_left.mpr fun g => (triangleTorusHomeomorph g).continuous⟩

theorem triangleTorusAction_generator₁_mkQ (x : RealPlane₄) :
    letI := triangleTorusAction
    triangleGenerator₁ • standardLattice.mkQ x =
      standardLattice.mkQ (Elliptic.flatLinear .three x) := by
  let := triangleTorusAction
  rw [triangleTorusAction_mkQ, triangleDualRepresentation_generator₁_matrix]
  rfl

theorem triangleTorusAction_generator₂_mkQ (x : RealPlane₄) :
    letI := triangleTorusAction
    triangleGenerator₂ • standardLattice.mkQ x =
      standardLattice.mkQ (Elliptic.flatLinear .four x) := by
  let := triangleTorusAction
  rw [triangleTorusAction_mkQ, triangleDualRepresentation_generator₂_matrix]
  rfl

theorem triangleTorusAction_cusp_mkQ (x : RealPlane₄) :
    letI := triangleTorusAction
    triangleCuspGenerator • standardLattice.mkQ x =
      standardLattice.mkQ (M₀.map (Int.castRingHom ℝ) *ᵥ x) := by
  let := triangleTorusAction
  rw [triangleTorusAction_mkQ, triangleDualRepresentation_cusp_matrix]

end Wikipedia.HopfProblem.SpecialPeriods
