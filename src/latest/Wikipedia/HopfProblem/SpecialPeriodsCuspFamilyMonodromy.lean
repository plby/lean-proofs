import Wikipedia.HopfProblem.SpecialPeriodsCuspData
import Wikipedia.HopfProblem.EllipticFlatTorus

/-!
# The actual integral monodromy of the cusp period family

The clockwise logarithmic deck transformation is `s ↦ s - k`.  Its
monodromy on the real coordinate torus is the integral matrix `M₀^k`,
written explicitly without a choice of coordinates on the quotient.
The same matrix gives the exact covariance of the supplied cusp periods.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspFamily

open CuspUniformization

/-- The integral monodromy of the clockwise logarithmic shift by `k`. -/
def cuspIntegralMatrix (k : ℤ) : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, k, 1, 0; -k, 0, 0, 1]

@[simp] theorem cuspIntegralMatrix_zero : cuspIntegralMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cuspIntegralMatrix]

/-- The source's clockwise generator is exactly the specified `M₀`. -/
@[simp] theorem cuspIntegralMatrix_one : cuspIntegralMatrix 1 = M₀ := rfl

theorem cuspIntegralMatrix_add (k l : ℤ) :
    cuspIntegralMatrix (k + l) = cuspIntegralMatrix k * cuspIntegralMatrix l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspIntegralMatrix, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

@[simp] theorem cuspIntegralMatrix_neg_mul (k : ℤ) :
    cuspIntegralMatrix (-k) * cuspIntegralMatrix k = 1 := by
  rw [← cuspIntegralMatrix_add, neg_add_cancel, cuspIntegralMatrix_zero]

@[simp] theorem cuspIntegralMatrix_mul_neg (k : ℤ) :
    cuspIntegralMatrix k * cuspIntegralMatrix (-k) = 1 := by
  rw [← cuspIntegralMatrix_add, add_neg_cancel, cuspIntegralMatrix_zero]

/-- The real-linear lift of the integral monodromy, with its explicit inverse. -/
def cuspRealEquiv (k : ℤ) : RealPlane₄ ≃ₗ[ℝ] RealPlane₄ where
  toFun x := ![x 0, x 1, x 2 + (k : ℝ) * x 1, x 3 - (k : ℝ) * x 0]
  invFun x := ![x 0, x 1, x 2 - (k : ℝ) * x 1, x 3 + (k : ℝ) * x 0]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring
  left_inv x := by
    ext i
    fin_cases i <;> simp
  right_inv x := by
    ext i
    fin_cases i <;> simp

theorem cuspRealEquiv_coordinates (k : ℤ) (x : RealPlane₄) :
    cuspRealEquiv k x =
      ![x 0, x 1, x 2 + (k : ℝ) * x 1, x 3 - (k : ℝ) * x 0] := rfl

theorem cuspRealEquiv_apply (k : ℤ) (x : RealPlane₄) :
    cuspRealEquiv k x = (cuspIntegralMatrix k).map (Int.castRingHom ℝ) *ᵥ x := by
  ext i
  fin_cases i <;>
    simp [cuspRealEquiv, cuspIntegralMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] <;> ring

@[simp] theorem cuspRealEquiv_zero :
    cuspRealEquiv 0 = LinearEquiv.refl ℝ RealPlane₄ := by
  ext x i
  fin_cases i <;> simp [cuspRealEquiv]

theorem cuspRealEquiv_add_apply (k l : ℤ) (x : RealPlane₄) :
    cuspRealEquiv (k + l) x = cuspRealEquiv k (cuspRealEquiv l x) := by
  ext i
  fin_cases i <;> simp [cuspRealEquiv] <;> ring

theorem cuspRealEquiv_add (k l : ℤ) :
    cuspRealEquiv (k + l) = cuspRealEquiv k * cuspRealEquiv l := by
  apply LinearEquiv.ext
  exact cuspRealEquiv_add_apply k l

@[simp] theorem cuspRealEquiv_neg (k : ℤ) :
    cuspRealEquiv (-k) = (cuspRealEquiv k).symm := by
  ext x i
  fin_cases i <;> simp [cuspRealEquiv, sub_eq_add_neg]

/-- Integral coordinates transform by the actual integral matrix. -/
theorem cuspRealEquiv_realCast (k : ℤ) (v : Lattice) :
    cuspRealEquiv k (Elliptic.realCast v) =
      Elliptic.realCast (cuspIntegralMatrix k *ᵥ v) := by
  rw [cuspRealEquiv_apply]
  ext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) (cuspIntegralMatrix k) v i).symm

/-- Extension to complex coordinates uses the very same integral matrix. -/
theorem cuspRealEquiv_complexCast (k : ℤ) (x : RealPlane₄) :
    (fun i => ((cuspRealEquiv k x) i : ℂ)) =
      (cuspIntegralMatrix k).map (Int.castRingHom ℂ) *ᵥ (fun i => (x i : ℂ)) := by
  ext i
  fin_cases i <;>
    simp [cuspRealEquiv, cuspIntegralMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] <;> ring

theorem cuspRealEquiv_mem_standardLattice (k : ℤ) {x : RealPlane₄}
    (hx : x ∈ standardLattice) : cuspRealEquiv k x ∈ standardLattice := by
  obtain ⟨v, rfl⟩ := (Elliptic.standardLattice_mem_iff x).mp hx
  exact (Elliptic.standardLattice_mem_iff _).mpr
    ⟨cuspIntegralMatrix k *ᵥ v, cuspRealEquiv_realCast k v⟩

/-- The real equivalence preserves the actual standard integral lattice. -/
theorem cuspRealEquiv_map_standardLattice (k : ℤ) :
    standardLattice.map ((cuspRealEquiv k).restrictScalars ℤ).toLinearMap =
      standardLattice := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact cuspRealEquiv_mem_standardLattice k hy
  · intro hx
    refine ⟨cuspRealEquiv (-k) x, cuspRealEquiv_mem_standardLattice (-k) hx, ?_⟩
    change cuspRealEquiv k (cuspRealEquiv (-k) x) = x
    rw [cuspRealEquiv_neg, LinearEquiv.apply_symm_apply]

/-- The descended integral linear automorphism of the quotient torus. -/
def cuspTorusLinearEquiv (k : ℤ) : RealTorus₄ ≃ₗ[ℤ] RealTorus₄ :=
  Submodule.Quotient.equiv standardLattice standardLattice
    ((cuspRealEquiv k).restrictScalars ℤ) (cuspRealEquiv_map_standardLattice k)

/-- The monodromy homeomorphism for the actual lattice quotient topology. -/
def cuspTorusHomeomorph (k : ℤ) : RealTorus₄ ≃ₜ RealTorus₄ where
  toEquiv := (cuspTorusLinearEquiv k).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp
      (cuspRealEquiv k).toContinuousLinearEquiv.continuous
  continuous_invFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp
      (cuspRealEquiv k).symm.toContinuousLinearEquiv.continuous

@[simp] theorem cuspTorusHomeomorph_mkQ (k : ℤ) (x : RealPlane₄) :
    cuspTorusHomeomorph k (standardLattice.mkQ x) =
      standardLattice.mkQ (cuspRealEquiv k x) := rfl

@[simp] theorem cuspTorusHomeomorph_zero (k : ℤ) :
    cuspTorusHomeomorph k 0 = 0 := (cuspTorusLinearEquiv k).map_zero

theorem cuspTorusHomeomorph_add (k : ℤ) (x y : RealTorus₄) :
    cuspTorusHomeomorph k (x + y) =
      cuspTorusHomeomorph k x + cuspTorusHomeomorph k y :=
  (cuspTorusLinearEquiv k).map_add x y

@[simp] theorem cuspTorusHomeomorph_zero_apply (x : RealTorus₄) :
    cuspTorusHomeomorph 0 x = x := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [cuspTorusHomeomorph_mkQ, cuspRealEquiv_zero]
  rfl

@[simp] theorem cuspTorusHomeomorph_zero_eq :
    cuspTorusHomeomorph 0 = Homeomorph.refl RealTorus₄ := by
  apply Homeomorph.ext
  exact cuspTorusHomeomorph_zero_apply

theorem cuspTorusHomeomorph_add_apply (k l : ℤ) (x : RealTorus₄) :
    cuspTorusHomeomorph (k + l) x =
      cuspTorusHomeomorph k (cuspTorusHomeomorph l x) := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [cuspTorusHomeomorph_mkQ, cuspTorusHomeomorph_mkQ,
    cuspTorusHomeomorph_mkQ, cuspRealEquiv_add_apply]

theorem cuspTorusHomeomorph_comp (k l : ℤ) :
    cuspTorusHomeomorph (k + l) =
      (cuspTorusHomeomorph l).trans (cuspTorusHomeomorph k) := by
  apply Homeomorph.ext
  exact cuspTorusHomeomorph_add_apply k l

@[simp] theorem cuspTorusHomeomorph_neg (k : ℤ) :
    cuspTorusHomeomorph (-k) = (cuspTorusHomeomorph k).symm := by
  apply Homeomorph.ext
  intro x
  apply (cuspTorusHomeomorph k).injective
  rw [← cuspTorusHomeomorph_add_apply, add_neg_cancel,
    cuspTorusHomeomorph_zero_apply, Homeomorph.apply_symm_apply]

/-- The integer monodromy action is selected locally, not globally installed. -/
@[instance_reducible] def cuspTorusAction : MulAction (Multiplicative ℤ) RealTorus₄ where
  smul k x := cuspTorusHomeomorph k.toAdd x
  one_smul := cuspTorusHomeomorph_zero_apply
  mul_smul k l := cuspTorusHomeomorph_add_apply k.toAdd l.toAdd

theorem cuspTorusAction_apply (k : Multiplicative ℤ) (x : RealTorus₄) :
    letI := cuspTorusAction
    k • x = cuspTorusHomeomorph k.toAdd x := rfl

theorem cuspTorusAction_mkQ (k : Multiplicative ℤ) (x : RealPlane₄) :
    letI := cuspTorusAction
    k • standardLattice.mkQ x =
      standardLattice.mkQ ((cuspIntegralMatrix k.toAdd).map (Int.castRingHom ℝ) *ᵥ x) := by
  change cuspTorusHomeomorph k.toAdd (standardLattice.mkQ x) = _
  rw [cuspTorusHomeomorph_mkQ, cuspRealEquiv_apply]

@[simp] theorem cuspTorusAction_zero (k : Multiplicative ℤ) :
    letI := cuspTorusAction
    k • (0 : RealTorus₄) = 0 := cuspTorusHomeomorph_zero k.toAdd

theorem cuspTorusAction_add (k : Multiplicative ℤ) (x y : RealTorus₄) :
    letI := cuspTorusAction
    k • (x + y) = k • x + k • y := cuspTorusHomeomorph_add k.toAdd x y

theorem cuspTorusAction_continuous :
    letI := cuspTorusAction
    ContinuousConstSMul (Multiplicative ℤ) RealTorus₄ := by
  let := cuspTorusAction
  exact ⟨fun k => (cuspTorusHomeomorph k.toAdd).continuous⟩

theorem cuspTorusAction_continuousSMul :
    letI := cuspTorusAction
    ContinuousSMul (Multiplicative ℤ) RealTorus₄ := by
  let := cuspTorusAction
  exact ⟨continuous_prod_of_discrete_left.mpr
    fun k => (cuspTorusHomeomorph k.toAdd).continuous⟩

/-- The clockwise source generator acts by the literal matrix `M₀`. -/
theorem cuspTorusAction_generator_mkQ (x : RealPlane₄) :
    letI := cuspTorusAction
    Multiplicative.ofAdd (1 : ℤ) • standardLattice.mkQ x =
      standardLattice.mkQ (M₀.map (Int.castRingHom ℝ) *ᵥ x) := by
  let := cuspTorusAction
  rw [cuspTorusAction_mkQ]
  rfl

@[simp] theorem cusp_exponential_sub_int (s : ℂ) (k : ℤ) :
    exponential (s - (k : ℂ)) = exponential s := by
  rw [sub_eq_add_neg, ← Int.cast_neg, exponential_add, exponential_int, mul_one]

/-- Exact covariance of the supplied cusp period matrix under every
clockwise integral deck transformation. -/
theorem cuspPeriodPoint_matrix_covariance (μ b h : ℂ → ℂ) (s : ℂ) (k : ℤ) :
    (cuspPeriodPoint μ b h (s - (k : ℂ))).matrix *
        (cuspIntegralMatrix k).map (Int.castRingHom ℂ) =
      (cuspPeriodPoint μ b h s).matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PeriodPoint.matrix, cuspPeriodPoint, cuspIntegralMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, cusp_exponential_sub_int] <;> ring

end Wikipedia.HopfProblem.SpecialPeriods.CuspFamily
