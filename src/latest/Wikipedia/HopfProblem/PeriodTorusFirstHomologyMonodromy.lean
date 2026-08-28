import Wikipedia.HopfProblem.PeriodTorusFirstHomologyPeriodDomain
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# Integral singular first homology of the period changes

The biholomorphisms of the actual period tori carry their marked straight
period loops to the loops specified by the integral matrices `A₁`, `A₂`,
and `M₀`. Naturality of the actual singular chain map then identifies their
maps on integral singular first homology, in the source's column basis.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodDomain

open FirstHurewicz

/-- The inverse cusp change of marking is exactly the matrix `M₀` in the
original column basis. -/
theorem cusp_inverse_transpose : (T₁ * T₂).transpose = M₀ := by decide

/-- Covariance of the full period matrix under the first period change. -/
theorem step₁_matrix_covariance (p : PeriodDomain) :
    p.step₁.val.matrix * A₁.map (Int.castRingHom ℂ) = p.val.R₁ * p.val.matrix := by
  change p.val.step₁.matrix * A₁.map (Int.castRingHom ℂ) = _
  rw [p.val.step₁_matrix (p.val.τ_ne_zero p.property.1), Matrix.mul_assoc]
  have h : (T₁.map (Int.castRingHom ℂ)).transpose * A₁.map (Int.castRingHom ℂ) = 1 := by
    change T₁.transpose.map (Int.castRingHom ℂ) * A₁.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₁.transpose * A₁ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

/-- Covariance of the full period matrix under the second period change. -/
theorem step₂_matrix_covariance (p : PeriodDomain) :
    p.step₂.val.matrix * A₂.map (Int.castRingHom ℂ) = p.val.R₂ * p.val.matrix := by
  change p.val.step₂.matrix * A₂.map (Int.castRingHom ℂ) = _
  rw [p.val.step₂_matrix (p.val.τ_ne_zero p.property.1), Matrix.mul_assoc]
  have h : (T₂.map (Int.castRingHom ℂ)).transpose * A₂.map (Int.castRingHom ℂ) = 1 := by
    change T₂.transpose.map (Int.castRingHom ℂ) * A₂.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₂.transpose * A₂ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

/-- At the cusp the complex linear factor is the identity. -/
theorem step₀_matrix_covariance (p : PeriodDomain) :
    p.step₀.val.matrix * M₀.map (Int.castRingHom ℂ) = p.val.matrix := by
  change p.val.step₀.matrix * M₀.map (Int.castRingHom ℂ) = _
  rw [p.val.step₀_matrix, Matrix.mul_assoc]
  have h : (T₀.map (Int.castRingHom ℂ)).transpose * M₀.map (Int.castRingHom ℂ) = 1 := by
    change T₀.transpose.map (Int.castRingHom ℂ) * M₀.map (Int.castRingHom ℂ) = 1
    rw [← Matrix.map_mul, show T₀.transpose * M₀ = 1 by decide]
    simp
  rw [h, Matrix.mul_one]

/-- The underlying actual continuous map of the first biholomorphism. -/
def step₁ContinuousMap (p : PeriodDomain) : C(p.Torus, p.step₁.Torus) :=
  ⟨p.step₁Biholomorph, p.step₁Biholomorph.continuous⟩

/-- The underlying actual continuous map of the second biholomorphism. -/
def step₂ContinuousMap (p : PeriodDomain) : C(p.Torus, p.step₂.Torus) :=
  ⟨p.step₂Biholomorph, p.step₂Biholomorph.continuous⟩

/-- The underlying actual continuous map of the cusp biholomorphism. -/
def step₀ContinuousMap (p : PeriodDomain) : C(p.Torus, p.step₀.Torus) :=
  ⟨p.step₀Biholomorph, p.step₀Biholomorph.continuous⟩

@[simp] theorem step₁ContinuousMap_mkQ (p : PeriodDomain) (z : ComplexPlane₂) :
    p.step₁ContinuousMap (p.lattice.mkQ z) = p.step₁.lattice.mkQ (p.val.R₁ *ᵥ z) :=
  p.step₁Biholomorph_mkQ z

@[simp] theorem step₂ContinuousMap_mkQ (p : PeriodDomain) (z : ComplexPlane₂) :
    p.step₂ContinuousMap (p.lattice.mkQ z) = p.step₂.lattice.mkQ (p.val.R₂ *ᵥ z) :=
  p.step₂Biholomorph_mkQ z

@[simp] theorem step₀ContinuousMap_mkQ (p : PeriodDomain) (z : ComplexPlane₂) :
    p.step₀ContinuousMap (p.lattice.mkQ z) = p.step₀.lattice.mkQ z := rfl

@[simp] theorem step₁ContinuousMap_zero (p : PeriodDomain) :
    p.step₁ContinuousMap 0 = 0 := by
  simpa only [map_zero, Matrix.mulVec_zero] using p.step₁ContinuousMap_mkQ 0

@[simp] theorem step₂ContinuousMap_zero (p : PeriodDomain) :
    p.step₂ContinuousMap 0 = 0 := by
  simpa only [map_zero, Matrix.mulVec_zero] using p.step₂ContinuousMap_mkQ 0

@[simp] theorem step₀ContinuousMap_zero (p : PeriodDomain) :
    p.step₀ContinuousMap 0 = 0 := by
  simpa only [map_zero] using p.step₀ContinuousMap_mkQ 0

private theorem integerCast_mulVec (A : LatticeMatrix) (c : Lattice) :
    (fun i => ((A *ᵥ c) i : ℂ)) =
      A.map (Int.castRingHom ℂ) *ᵥ (fun i => (c i : ℂ)) := by
  funext i
  exact (Int.castRingHom ℂ).map_mulVec A c i

/-- The first complex linear map sends the actual period of `c` to the
target period of `A₁ c`. -/
theorem step₁_periodVector (p : PeriodDomain) (c : Lattice) :
    p.step₁.periodVector (A₁ *ᵥ c) = p.val.R₁ *ᵥ p.periodVector c := by
  simp only [periodVector_apply, integerCast_mulVec, Matrix.mulVec_mulVec,
    p.step₁_matrix_covariance]

/-- The second complex linear map sends the actual period of `c` to the
target period of `A₂ c`. -/
theorem step₂_periodVector (p : PeriodDomain) (c : Lattice) :
    p.step₂.periodVector (A₂ *ᵥ c) = p.val.R₂ *ᵥ p.periodVector c := by
  simp only [periodVector_apply, integerCast_mulVec, Matrix.mulVec_mulVec,
    p.step₂_matrix_covariance]

/-- The identical complex vector has target cusp marking `M₀ c`. -/
theorem step₀_periodVector (p : PeriodDomain) (c : Lattice) :
    p.step₀.periodVector (M₀ *ᵥ c) = p.periodVector c := by
  simp only [periodVector_apply, integerCast_mulVec, Matrix.mulVec_mulVec,
    p.step₀_matrix_covariance]

/-- Equality of the actual mapped straight loops for the first period change. -/
theorem step₁_periodLoop (p : PeriodDomain) (c : Lattice) :
    (p.periodLoop c).map p.step₁ContinuousMap.continuous =
      (p.step₁.periodLoop (A₁ *ᵥ c)).cast
        p.step₁ContinuousMap_zero p.step₁ContinuousMap_zero := by
  ext t
  change p.step₁ContinuousMap (p.periodLoop c t) = p.step₁.periodLoop (A₁ *ᵥ c) t
  rw [periodLoop_apply, step₁ContinuousMap_mkQ, periodLoop_apply,
    Matrix.mulVec_smul, step₁_periodVector]

/-- Equality of the actual mapped straight loops for the second period change. -/
theorem step₂_periodLoop (p : PeriodDomain) (c : Lattice) :
    (p.periodLoop c).map p.step₂ContinuousMap.continuous =
      (p.step₂.periodLoop (A₂ *ᵥ c)).cast
        p.step₂ContinuousMap_zero p.step₂ContinuousMap_zero := by
  ext t
  change p.step₂ContinuousMap (p.periodLoop c t) = p.step₂.periodLoop (A₂ *ᵥ c) t
  rw [periodLoop_apply, step₂ContinuousMap_mkQ, periodLoop_apply,
    Matrix.mulVec_smul, step₂_periodVector]

/-- Equality of the actual mapped straight loops for the cusp period change. -/
theorem step₀_periodLoop (p : PeriodDomain) (c : Lattice) :
    (p.periodLoop c).map p.step₀ContinuousMap.continuous =
      (p.step₀.periodLoop (M₀ *ᵥ c)).cast
        p.step₀ContinuousMap_zero p.step₀ContinuousMap_zero := by
  ext t
  change p.step₀ContinuousMap (p.periodLoop c t) = p.step₀.periodLoop (M₀ *ᵥ c) t
  rw [periodLoop_apply, step₀ContinuousMap_mkQ, periodLoop_apply, step₀_periodVector]

/-- The actual singular homology map sends a marked period loop by `A₁`. -/
theorem step₁_inducedHomology_periodLoop (p : PeriodDomain) (c : Lattice) :
    inducedHomology p.step₁ContinuousMap (loopHomologyClass (p.periodLoop c)) =
      loopHomologyClass (p.step₁.periodLoop (A₁ *ᵥ c)) := by
  rw [inducedHomology_loopHomologyClass, p.step₁_periodLoop]
  rfl

/-- The actual singular homology map sends a marked period loop by `A₂`. -/
theorem step₂_inducedHomology_periodLoop (p : PeriodDomain) (c : Lattice) :
    inducedHomology p.step₂ContinuousMap (loopHomologyClass (p.periodLoop c)) =
      loopHomologyClass (p.step₂.periodLoop (A₂ *ᵥ c)) := by
  rw [inducedHomology_loopHomologyClass, p.step₂_periodLoop]
  rfl

/-- The actual singular homology map sends a marked cusp period loop by `M₀`. -/
theorem step₀_inducedHomology_periodLoop (p : PeriodDomain) (c : Lattice) :
    inducedHomology p.step₀ContinuousMap (loopHomologyClass (p.periodLoop c)) =
      loopHomologyClass (p.step₀.periodLoop (M₀ *ᵥ c)) := by
  rw [inducedHomology_loopHomologyClass, p.step₀_periodLoop]
  rfl

/-- The first biholomorphism acts on actual integral singular first homology
by `A₁` in the source's column marking. -/
theorem step₁_singularH1 (p : PeriodDomain) (a : SingularH1 p.Torus) :
    p.step₁.singularH1Equiv (inducedHomology p.step₁ContinuousMap a) =
      A₁ *ᵥ p.singularH1Equiv a := by
  obtain ⟨c, rfl⟩ := p.singularH1Equiv.symm.surjective a
  rw [p.singularH1Equiv_symm_apply, p.step₁_inducedHomology_periodLoop,
    p.step₁.singularH1Equiv_periodLoop, p.singularH1Equiv_periodLoop]

/-- The second biholomorphism acts on actual integral singular first homology
by `A₂` in the source's column marking. -/
theorem step₂_singularH1 (p : PeriodDomain) (a : SingularH1 p.Torus) :
    p.step₂.singularH1Equiv (inducedHomology p.step₂ContinuousMap a) =
      A₂ *ᵥ p.singularH1Equiv a := by
  obtain ⟨c, rfl⟩ := p.singularH1Equiv.symm.surjective a
  rw [p.singularH1Equiv_symm_apply, p.step₂_inducedHomology_periodLoop,
    p.step₂.singularH1Equiv_periodLoop, p.singularH1Equiv_periodLoop]

/-- The cusp biholomorphism acts on actual integral singular first homology
by `M₀` in the source's column marking. -/
theorem step₀_singularH1 (p : PeriodDomain) (a : SingularH1 p.Torus) :
    p.step₀.singularH1Equiv (inducedHomology p.step₀ContinuousMap a) =
      M₀ *ᵥ p.singularH1Equiv a := by
  obtain ⟨c, rfl⟩ := p.singularH1Equiv.symm.surjective a
  rw [p.singularH1Equiv_symm_apply, p.step₀_inducedHomology_periodLoop,
    p.step₀.singularH1Equiv_periodLoop, p.singularH1Equiv_periodLoop]

/-- Conjugating the actual first singular homology map by the proved
source and target markings gives the integral matrix map `A₁`. -/
theorem step₁_singularH1_conjugate (p : PeriodDomain) :
    p.step₁.singularH1Equiv.toLinearMap.comp
      ((inducedHomology p.step₁ContinuousMap).comp p.singularH1Equiv.symm.toLinearMap) =
        A₁.mulVecLin := by
  apply LinearMap.ext
  intro c
  change p.step₁.singularH1Equiv
    (inducedHomology p.step₁ContinuousMap (p.singularH1Equiv.symm c)) = A₁ *ᵥ c
  rw [p.step₁_singularH1, LinearEquiv.apply_symm_apply]

/-- Conjugating the actual second singular homology map gives `A₂`. -/
theorem step₂_singularH1_conjugate (p : PeriodDomain) :
    p.step₂.singularH1Equiv.toLinearMap.comp
      ((inducedHomology p.step₂ContinuousMap).comp p.singularH1Equiv.symm.toLinearMap) =
        A₂.mulVecLin := by
  apply LinearMap.ext
  intro c
  change p.step₂.singularH1Equiv
    (inducedHomology p.step₂ContinuousMap (p.singularH1Equiv.symm c)) = A₂ *ᵥ c
  rw [p.step₂_singularH1, LinearEquiv.apply_symm_apply]

/-- Conjugating the actual cusp singular homology map gives `M₀`. -/
theorem step₀_singularH1_conjugate (p : PeriodDomain) :
    p.step₀.singularH1Equiv.toLinearMap.comp
      ((inducedHomology p.step₀ContinuousMap).comp p.singularH1Equiv.symm.toLinearMap) =
        M₀.mulVecLin := by
  apply LinearMap.ext
  intro c
  change p.step₀.singularH1Equiv
    (inducedHomology p.step₀ContinuousMap (p.singularH1Equiv.symm c)) = M₀ *ᵥ c
  rw [p.step₀_singularH1, LinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.PeriodDomain
