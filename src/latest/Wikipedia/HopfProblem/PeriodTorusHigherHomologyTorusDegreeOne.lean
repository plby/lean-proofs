import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusLoops

/-!
# The positive coordinate marking in singular degree one

The coordinate map is defined using actual positive coordinate-loop
classes. In rank four it agrees with the previously proved Hurewicz
marking of every period torus under the actual coordinate homeomorphism.
It is therefore an isomorphism, with no new homology identification
assumed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

/-- Integral additive combinations of the actual coordinate-loop classes. -/
def coordinateH1Add (n : ℕ) : (Fin n → ℤ) →+ SingularH1 (ProductTorus n) where
  toFun v := ∑ i, v i • loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1))
  map_zero' := by simp only [Pi.zero_apply, zero_zsmul, Finset.sum_const_zero]
  map_add' v w := by simp only [Pi.add_apply, add_zsmul, Finset.sum_add_distrib]

/-- The coordinate-loop combinations as a map of the actual homology module. -/
def coordinateH1 (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] SingularH1 (ProductTorus n) :=
  { toFun := coordinateH1Add n
    map_add' := (coordinateH1Add n).map_add
    map_smul' r a := by
      convert! (coordinateH1Add n).map_zsmul r a using 1
      exact int_smul_eq_zsmul .. }

@[simp] theorem coordinateH1_basis (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.basisFun ℤ (Fin n) i) =
      loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1)) := by
  simp [coordinateH1, coordinateH1Add, Pi.basisFun_apply, Pi.single_apply]

@[simp] theorem coordinateH1_single (n : ℕ) (i : Fin n) :
    coordinateH1 n (Pi.single i 1) =
      loopHomologyClass (coordinatePeriodLoop n (Pi.single i 1)) := by
  simpa only [Pi.basisFun_apply] using coordinateH1_basis n i

/-- The actual coordinate-loop marking agrees with the old geometric period marking. -/
theorem coordinateH1_four_eq_periodMarking (p : PeriodDomain) :
    coordinateH1 4 =
      (inducedHomology (periodTorusCircleHomeomorph p : C(_, _))).comp
        p.singularH1Equiv.symm.toLinearMap := by
  apply (Pi.basisFun ℤ (Fin 4)).ext
  intro i
  rw [coordinateH1_basis, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [p.singularH1Equiv_symm_apply, periodTorusCircle_inducedHomology_periodLoop]
  simp only [Pi.basisFun_apply]

/-- Every integral tuple is represented by its actual positive straight vector loop. -/
theorem coordinateH1_four_apply (p : PeriodDomain) (v : Lattice) :
    coordinateH1 4 v = loopHomologyClass (coordinatePeriodLoop 4 v) := by
  rw [coordinateH1_four_eq_periodMarking p, LinearMap.comp_apply]
  simp only [LinearEquiv.coe_coe]
  rw [p.singularH1Equiv_symm_apply, periodTorusCircle_inducedHomology_periodLoop]

/-- The rank-four coordinate-loop map is a proved isomorphism of actual singular homology. -/
theorem coordinateH1_four_bijective (p : PeriodDomain) : Function.Bijective (coordinateH1 4) := by
  rw [coordinateH1_four_eq_periodMarking p]
  exact (homeomorphHomologyEquiv (periodTorusCircleHomeomorph p) 1).bijective.comp
    p.singularH1Equiv.symm.bijective

/-- The actual positive coordinate marking as an integral linear equivalence. -/
def coordinateH1FourEquiv (p : PeriodDomain) : Lattice ≃ₗ[ℤ] SingularH1 (ProductTorus 4) :=
  LinearEquiv.ofBijective (coordinateH1 4) (coordinateH1_four_bijective p)

@[simp] theorem coordinateH1FourEquiv_apply (p : PeriodDomain) (v : Lattice) :
    coordinateH1FourEquiv p v = loopHomologyClass (coordinatePeriodLoop 4 v) :=
  coordinateH1_four_apply p v

/-- Every integral matrix acts on the actual coordinate marking by its literal entries. -/
theorem coordinateH1_matrix_natural (p : PeriodDomain) (A : LatticeMatrix) (v : Lattice) :
    inducedHomology (torusMatrixMap A) (coordinateH1 4 v) = coordinateH1 4 (A *ᵥ v) := by
  rw [coordinateH1_four_apply p, coordinateH1_four_apply p,
    torusMatrixMap_coordinatePeriodHomology]

theorem coordinateH1_matrix_intertwines (p : PeriodDomain) (A : LatticeMatrix) :
    (inducedHomology (torusMatrixMap A)).comp (coordinateH1 4) =
      (coordinateH1 4).comp A.mulVecLin := by
  apply LinearMap.ext
  intro v
  exact coordinateH1_matrix_natural p A v

/-- The old marking and the circle-coordinate marking agree on every actual class. -/
theorem periodTorusCircle_coordinateH1 (p : PeriodDomain) (a : SingularH1 p.Torus) :
    inducedHomology (periodTorusCircleHomeomorph p : C(_, _)) a =
      coordinateH1 4 (p.singularH1Equiv a) := by
  rw [coordinateH1_four_eq_periodMarking p]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
