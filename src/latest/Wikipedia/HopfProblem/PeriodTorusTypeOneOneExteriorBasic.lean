import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorBasis
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorDual

/-!
# Integral exterior forms on the actual period lattice

The covectors below are the coordinate projections dual to the ordered lattice
basis `(γ̂, û, ŵ, δ̂)`. The forms are elements of Mathlib's exterior powers and
exterior algebra. No identification with singular or de Rham cohomology is
assumed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTypeOneOne

open PeriodTorusHigherHomologyExterior LocalSystemMatrices

/-- The actual integral dual of the period lattice. -/
abbrev IntegralCovector := Module.Dual ℤ Lattice

/-- The actual exterior algebra of the integral dual lattice. -/
abbrev IntegralExterior := ExteriorAlgebra ℤ IntegralCovector

/-- The ordered integral covectors `(γ,u,w,δ)`. -/
def latticeCovector (i : Fin 4) : IntegralCovector := LinearMap.proj i

@[simp] theorem latticeCovector_apply (i : Fin 4) (x : Lattice) :
    latticeCovector i x = x i := rfl

theorem latticeCovector_eq_dualBasis (i : Fin 4) :
    latticeCovector i = latticeBasis.dualBasis i := by
  ext x
  simp [latticeBasis]

/-- A genuine degree-two exterior product of two marked covectors. -/
def exteriorPair (i j : Fin 4) : ⋀[ℤ]^2 IntegralCovector :=
  exteriorPower.ιMulti ℤ 2 ![latticeCovector i, latticeCovector j]

theorem exteriorPair_coe (i j : Fin 4) :
    (exteriorPair i j : IntegralExterior) =
      ExteriorAlgebra.ι ℤ (latticeCovector i) *
        ExteriorAlgebra.ι ℤ (latticeCovector j) := by
  simp [exteriorPair, ExteriorAlgebra.ιMulti_succ_apply]

/-- The dual-lattice exterior basis in the order `01,02,03,12,13,23`. -/
def integralSquareBasis : Module.Basis (Fin 6) ℤ (⋀[ℤ]^2 IntegralCovector) :=
  (latticeBasis.dualBasis.exteriorPower 2).reindex pairSubsetEquiv.symm

theorem integralSquareBasis_apply (i : Fin 6) :
    integralSquareBasis i = exteriorPair (pairIndices i 0) (pairIndices i 1) := by
  rw [integralSquareBasis, Module.Basis.reindex_apply]
  change latticeBasis.dualBasis.exteriorPower 2 (pairSubset i) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, pairSubset_ordered]
  unfold exteriorPair
  congr 1
  funext j
  fin_cases j <;> simp [Function.comp_apply, latticeCovector_eq_dualBasis]

/-- Integral six-coordinate forms, as an equivalence with the actual exterior power. -/
def integralExteriorForm : (Fin 6 → ℤ) ≃ₗ[ℤ] (⋀[ℤ]^2 IntegralCovector) :=
  integralSquareBasis.equivFun.symm

theorem integralExteriorForm_apply (E : Fin 6 → ℤ) :
    integralExteriorForm E =
      E 0 • exteriorPair 0 1 + E 1 • exteriorPair 0 2 +
      E 2 • exteriorPair 0 3 + E 3 • exteriorPair 1 2 +
      E 4 • exteriorPair 1 3 + E 5 • exteriorPair 2 3 := by
  simp only [integralExteriorForm, Module.Basis.equivFun_symm_apply,
    integralSquareBasis_apply, Fin.sum_univ_succ, pairIndices]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  abel

/-- The source form `η = u ∧ w + 6 γ ∧ δ`, in its actual degree-two exterior power. -/
def etaExteriorPower : ⋀[ℤ]^2 IntegralCovector :=
  exteriorPair 1 2 + (6 : ℤ) • exteriorPair 0 3

/-- The same form viewed in the actual exterior algebra. -/
def etaExterior : IntegralExterior := etaExteriorPower

theorem integralExteriorForm_eta :
    integralExteriorForm ![0, 0, 6, 1, 0, 0] = etaExteriorPower := by
  rw [integralExteriorForm_apply]
  simp [etaExteriorPower, add_comm]

theorem etaExterior_eq :
    etaExterior =
      ExteriorAlgebra.ι ℤ (latticeCovector 1) * ExteriorAlgebra.ι ℤ (latticeCovector 2) +
      (6 : ℤ) • (ExteriorAlgebra.ι ℤ (latticeCovector 0) *
        ExteriorAlgebra.ι ℤ (latticeCovector 3)) := by
  simp only [etaExterior, etaExteriorPower, Submodule.coe_add, Submodule.coe_smul,
    exteriorPair_coe]

/-- The positively ordered top exterior product on the dual lattice. -/
def volumeExteriorPower : ⋀[ℤ]^4 IntegralCovector :=
  exteriorPower.ιMulti ℤ 4 latticeCovector

/-- The volume element in the exterior algebra. -/
def volumeExterior : IntegralExterior := volumeExteriorPower

theorem volumeExterior_eq :
    volumeExterior =
      ExteriorAlgebra.ι ℤ (latticeCovector 0) * ExteriorAlgebra.ι ℤ (latticeCovector 1) *
      ExteriorAlgebra.ι ℤ (latticeCovector 2) * ExteriorAlgebra.ι ℤ (latticeCovector 3) := by
  simp [volumeExterior, volumeExteriorPower, ExteriorAlgebra.ιMulti_succ_apply,
    Matrix.vecTail, mul_assoc]

/-- The positively ordered top exterior product on the original integral lattice. -/
def latticeVolume : ⋀[ℤ]^4 Lattice := exteriorPower.ιMulti ℤ 4 latticeBasis

/-- The actual determinant pairing of the two ordered volume elements is one. -/
theorem volumeExteriorPower_pairing :
    dualPairingEquiv 4 volumeExteriorPower latticeVolume = 1 := by
  rw [volumeExteriorPower, latticeVolume, dualPairingEquiv_ιMulti_ιMulti]
  have hmatrix : Matrix.of (fun i j => latticeCovector j (latticeBasis i)) =
      (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
    ext i j
    simp [latticeBasis, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hmatrix, Matrix.det_one]

/-- Evaluation of an arbitrary integer multiple of the volume element. -/
theorem smul_volumeExteriorPower_pairing (n : ℤ) :
    dualPairingEquiv 4 (n • volumeExteriorPower) latticeVolume = n := by
  rw [map_smul, LinearMap.smul_apply, volumeExteriorPower_pairing, smul_eq_mul, mul_one]

theorem smul_volumeExteriorPower_eq_zero_iff (n : ℤ) :
    n • volumeExteriorPower = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hpair := smul_volumeExteriorPower_pairing n
    rw [h, map_zero, LinearMap.zero_apply] at hpair
    exact hpair.symm
  · rintro rfl
    exact zero_smul _ _

theorem smul_volumeExterior_eq_zero_iff (n : ℤ) :
    n • volumeExterior = 0 ↔ n = 0 := by
  rw [← smul_volumeExteriorPower_eq_zero_iff n]
  constructor
  · intro h
    exact Subtype.ext h
  · intro h
    exact congrArg Subtype.val h

theorem volumeExteriorPower_ne_zero : volumeExteriorPower ≠ 0 := by
  simpa using (smul_volumeExteriorPower_eq_zero_iff 1).not.mpr (by decide : (1 : ℤ) ≠ 0)

theorem volumeExterior_ne_zero : volumeExterior ≠ 0 := by
  simpa using (smul_volumeExterior_eq_zero_iff 1).not.mpr (by decide : (1 : ℤ) ≠ 0)

end Wikipedia.HopfProblem.PeriodTorusTypeOneOne
