import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Biholomorphisms of the period tori

This file turns the matrix covariance identities of §3 into maps of the
actual complex quotients. An integral change of generators does not change
the column lattice; a complex linear change of coordinates then descends to
a biholomorphism.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem

namespace DiscreteQuotient

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : Submodule ℤ E) (K : Submodule ℤ F) [DiscreteTopology L] [DiscreteTopology K]

/-- A complex linear equivalence carrying one discrete lattice onto another
induces a genuine biholomorphism of their quotient complex manifolds. -/
def linearBiholomorph (e : E ≃L[ℂ] F)
    (h : L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap = K) :
    Diffeomorph (modelWithCornersSelf ℂ E) (modelWithCornersSelf ℂ F) (E ⧸ L) (F ⧸ K) ω where
  toEquiv := (Submodule.Quotient.equiv L K (e.toLinearEquiv.restrictScalars ℤ) h).toEquiv
  contMDiff_toFun := by
    apply contMDiff_of_comp_mkQ
    exact (contMDiff_mkQ K ω).comp e.contDiff.contMDiff
  contMDiff_invFun := by
    apply contMDiff_of_comp_mkQ
    exact (contMDiff_mkQ L ω).comp e.symm.contDiff.contMDiff

@[simp] theorem linearBiholomorph_mkQ (e : E ≃L[ℂ] F)
    (h : L.map (e.toLinearEquiv.restrictScalars ℤ).toLinearMap = K) (z : E) :
    linearBiholomorph L K e h (L.mkQ z) = K.mkQ (e z) := rfl

end DiscreteQuotient

/-- Integral column span; unlike the complex span, this remembers the torus. -/
def columnLattice (P : Matrix (Fin 2) (Fin 4) ℂ) : Submodule ℤ ComplexPlane₂ :=
  Submodule.span ℤ (Set.range P.col)

theorem column_mul_mem (P : Matrix (Fin 2) (Fin 4) ℂ) (A : LatticeMatrix) (j : Fin 4) :
    (P * A.map (Int.castRingHom ℂ)).col j ∈ columnLattice P := by
  have he : (P * A.map (Int.castRingHom ℂ)).col j = ∑ k, A k j • P.col k := by
    ext i
    simp [Matrix.mul_apply, Matrix.col, Matrix.transpose_apply, zsmul_eq_mul, mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))

theorem columnLattice_mul_le (P : Matrix (Fin 2) (Fin 4) ℂ) (A : LatticeMatrix) :
    columnLattice (P * A.map (Int.castRingHom ℂ)) ≤ columnLattice P := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact column_mul_mem P A j

theorem columnLattice_mul_eq (P : Matrix (Fin 2) (Fin 4) ℂ) (A B : LatticeMatrix)
    (hAB : A * B = 1) : columnLattice (P * A.map (Int.castRingHom ℂ)) = columnLattice P := by
  apply le_antisymm (columnLattice_mul_le P A)
  have hP : (P * A.map (Int.castRingHom ℂ)) * B.map (Int.castRingHom ℂ) = P := by
    rw [Matrix.mul_assoc, ← Matrix.map_mul, hAB]
    simp
  have h := columnLattice_mul_le (P * A.map (Int.castRingHom ℂ)) B
  rwa [hP] at h

theorem map_columnLattice (P : Matrix (Fin 2) (Fin 4) ℂ) (R : Matrix (Fin 2) (Fin 2) ℂ) :
    (columnLattice P).map (R.mulVecLin.restrictScalars ℤ) = columnLattice (R * P) := by
  rw [columnLattice, columnLattice, Submodule.map_span]
  congr 1
  rw [← Set.range_comp]
  congr 1

namespace PeriodDomain

def step₁ (p : PeriodDomain) : PeriodDomain := ⟨p.val.step₁, p.val.step₁_admissible p.property⟩
def step₂ (p : PeriodDomain) : PeriodDomain := ⟨p.val.step₂, p.val.step₂_admissible p.property⟩
def step₀ (p : PeriodDomain) : PeriodDomain := ⟨p.val.step₀, p.val.step₀_admissible p.property⟩

def R₁Equiv (p : PeriodDomain) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  (Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin 2)) p.val.R₁
    (isUnit_iff_ne_zero.mpr (by
      rw [PeriodPoint.det_R₁]
      exact div_ne_zero (by norm_num) (p.val.τ_ne_zero p.property.1)))).toContinuousLinearEquiv

def R₂Equiv (p : PeriodDomain) : ComplexPlane₂ ≃L[ℂ] ComplexPlane₂ :=
  (Matrix.toLinearEquiv (Pi.basisFun ℂ (Fin 2)) p.val.R₂
    (isUnit_iff_ne_zero.mpr (by
      rw [PeriodPoint.det_R₂]
      exact div_ne_zero one_ne_zero (p.val.τ_ne_zero p.property.1)))).toContinuousLinearEquiv

theorem R₁Equiv_apply (p : PeriodDomain) (z : ComplexPlane₂) :
    p.R₁Equiv z = p.val.R₁ *ᵥ z := by
  simp [R₁Equiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

theorem R₂Equiv_apply (p : PeriodDomain) (z : ComplexPlane₂) :
    p.R₂Equiv z = p.val.R₂ *ᵥ z := by
  simp [R₂Equiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]

theorem R₁Equiv_map_lattice (p : PeriodDomain) :
    p.lattice.map (p.R₁Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap = p.step₁.lattice := by
  have he : (p.R₁Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.val.R₁.mulVecLin.restrictScalars ℤ := by
    exact LinearMap.ext fun z => R₁Equiv_apply p z
  change (columnLattice p.val.matrix).map _ = columnLattice p.val.step₁.matrix
  rw [he, map_columnLattice, p.val.step₁_matrix (p.val.τ_ne_zero p.property.1)]
  exact (columnLattice_mul_eq _ T₁.transpose A₁ (by decide)).symm

theorem R₂Equiv_map_lattice (p : PeriodDomain) :
    p.lattice.map (p.R₂Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap = p.step₂.lattice := by
  have he : (p.R₂Equiv.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.val.R₂.mulVecLin.restrictScalars ℤ := by
    exact LinearMap.ext fun z => R₂Equiv_apply p z
  change (columnLattice p.val.matrix).map _ = columnLattice p.val.step₂.matrix
  rw [he, map_columnLattice, p.val.step₂_matrix (p.val.τ_ne_zero p.property.1)]
  exact (columnLattice_mul_eq _ T₂.transpose A₂ (by decide)).symm

/-- The first generator gives a biholomorphism between the actual period tori. -/
def step₁Biholomorph (p : PeriodDomain) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂)
      p.Torus p.step₁.Torus ω :=
  DiscreteQuotient.linearBiholomorph p.lattice p.step₁.lattice p.R₁Equiv p.R₁Equiv_map_lattice

/-- The second generator gives a biholomorphism between the actual period tori. -/
def step₂Biholomorph (p : PeriodDomain) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂)
      p.Torus p.step₂.Torus ω :=
  DiscreteQuotient.linearBiholomorph p.lattice p.step₂.lattice p.R₂Equiv p.R₂Equiv_map_lattice

theorem step₀_lattice (p : PeriodDomain) : p.step₀.lattice = p.lattice := by
  change columnLattice p.val.step₀.matrix = columnLattice p.val.matrix
  rw [p.val.step₀_matrix]
  exact columnLattice_mul_eq _ T₀.transpose (T₁ * T₂).transpose (by decide)

/-- At the cusp, the complex linear factor is the identity and only the
integral marking changes. -/
def step₀Biholomorph (p : PeriodDomain) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂) (modelWithCornersSelf ℂ ComplexPlane₂)
      p.Torus p.step₀.Torus ω :=
  DiscreteQuotient.linearBiholomorph p.lattice p.step₀.lattice
    (ContinuousLinearEquiv.refl ℂ ComplexPlane₂) (by
      change p.lattice.map (LinearMap.id : ComplexPlane₂ →ₗ[ℤ] ComplexPlane₂) = p.step₀.lattice
      simpa only [Submodule.map_id] using p.step₀_lattice.symm)

@[simp] theorem step₁Biholomorph_mkQ (p : PeriodDomain) (z : ComplexPlane₂) :
    p.step₁Biholomorph (p.lattice.mkQ z) = p.step₁.lattice.mkQ (p.val.R₁ *ᵥ z) := by
  simp only [step₁Biholomorph, DiscreteQuotient.linearBiholomorph_mkQ, R₁Equiv_apply]

@[simp] theorem step₂Biholomorph_mkQ (p : PeriodDomain) (z : ComplexPlane₂) :
    p.step₂Biholomorph (p.lattice.mkQ z) = p.step₂.lattice.mkQ (p.val.R₂ *ᵥ z) := by
  simp only [step₂Biholomorph, DiscreteQuotient.linearBiholomorph_mkQ, R₂Equiv_apply]

@[simp] theorem step₀Biholomorph_mkQ (p : PeriodDomain) (z : ComplexPlane₂) :
    p.step₀Biholomorph (p.lattice.mkQ z) = p.step₀.lattice.mkQ z := rfl

end PeriodDomain

end Wikipedia.HopfProblem
