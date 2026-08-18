/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.BombieriVaaler
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The rational-subspace form of the Bombieri--Vaaler lemma

`BombieriVaaler.lean` proves the determinantal statement for an integer
matrix.  This file packages exactly the data occurring when that matrix is
an integral basis of a proper rational subspace, and translates its kernel
conclusion into an integral normal vector to the whole subspace.

No rank or properness hypothesis is hidden in a typeclass.  Full row rank is
certified by the explicitly selected nonsingular coordinate minor; properness
is certified by an explicitly selected ambient coordinate outside that minor;
and `span_eq` says exactly which real subspace the integer rows represent.
-/

namespace Erdos186.CFP.Bilu.SubspaceLattice

open scoped BigOperators
open RealInnerProductSpace
open Module
open Erdos186.CFP.Bilu.BombieriVaaler

variable {r n : ℕ}

section CovolumeOfBasis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- For a real basis in an inner-product space, the square of the covolume
of its integral span is its Gram determinant.  This is the coordinate-free
link between Mathlib's `ZLattice.covolume` and Euclidean row covolume. -/
theorem covolume_span_basis_sq_eq_det_gram
    (b : Basis (Fin r) ℝ E) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) ^ 2 =
      (Matrix.gram ℝ b).det := by
  let b₀ : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
    stdOrthonormalBasis ℝ E
  have hrank : Module.finrank ℝ E = r := by
    simpa using Module.finrank_eq_card_basis b
  let e : Fin (Module.finrank ℝ E) ≃ Fin r := Fin.castOrderIso hrank
  let o : OrthonormalBasis (Fin r) ℝ E := b₀.reindex e
  have hoVolume : MeasureTheory.volume.real (ZSpan.fundamentalDomain o.toBasis) = 1 := by
    rw [MeasureTheory.measureReal_def]
    have hfd : MeasureTheory.volume (ZSpan.fundamentalDomain o.toBasis) = 1 := by
      rw [MeasureTheory.measure_congr
        (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis MeasureTheory.volume)]
      exact o.volume_parallelepiped
    rw [hfd]
    simp
  have hcov :
      ZLattice.covolume (Submodule.span ℤ (Set.range b)) = |o.toBasis.det b| := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain
      (Submodule.span ℤ (Set.range b)) MeasureTheory.volume
      (ZSpan.isAddFundamentalDomain b MeasureTheory.volume),
      ZSpan.measureReal_fundamentalDomain b MeasureTheory.volume o.toBasis,
      hoVolume, mul_one]
  rw [hcov, sq_abs, o.toBasis.det_apply]
  rw [Matrix.gram_eq_conjTranspose_mul o b, Matrix.det_mul,
    Matrix.det_conjTranspose]
  have hm : o.toBasis.toMatrix b =
      Matrix.of fun i j ↦ o.repr (b j) i := by
    ext i j
    rfl
  rw [hm]
  simp [pow_two]

end CovolumeOfBasis

/-- Embed an integral coordinate vector in real Euclidean space. -/
def integralReal (x : Fin n → ℤ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun j ↦ (x j : ℝ)

@[simp]
theorem integralReal_apply (x : Fin n → ℤ) (j : Fin n) :
    integralReal x j = (x j : ℝ) := rfl

@[simp]
theorem integralReal_eq_zero_iff (x : Fin n → ℤ) :
    integralReal x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext j
    have hj : (x j : ℝ) = 0 := by
      change integralReal x j = 0
      rw [h]
      rfl
    exact_mod_cast hj
  · rintro rfl
    ext j
    simp [integralReal]

/-- The integer-linear embedding of the standard lattice in Euclidean
space. -/
def integralRealLinear : (Fin n → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin n) where
  toFun := integralReal
  map_add' := by
    intro x y
    ext j
    simp [integralReal]
  map_smul' := by
    intro a x
    ext j
    simp [integralReal]

/-- The standard lattice `ℤⁿ`, regarded as a submodule of Euclidean
space. -/
def ambientIntegralPoints : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
  LinearMap.range (integralRealLinear (n := n))

/-- The literal lattice `L ∩ ℤⁿ`, living inside the subtype `L`. -/
def integralPoints (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Submodule ℤ L :=
  (ambientIntegralPoints (n := n)).comap
    (L.subtype.restrictScalars ℤ)

theorem mem_integralPoints_iff
    {L : Submodule ℝ (EuclideanSpace ℝ (Fin n))} {y : L} :
    y ∈ integralPoints L ↔
      ∃ x : Fin n → ℤ, integralReal x = (y : EuclideanSpace ℝ (Fin n)) := by
  rfl

/-- An explicit integral presentation of a proper rational subspace.

The rows of `A` span `L`.  The coordinate map `minorColumns` selects a
nonsingular `r × r` minor, hence certifies full row rank.  The coordinate
`extraColumn`, outside the selected minor, certifies that the represented
subspace is proper in the ambient coordinate space. -/
structure Presentation (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) where
  /-- Integral row vectors. -/
  A : Matrix (Fin r) (Fin n) ℤ
  /-- Columns of a full-rank coordinate minor. -/
  minorColumns : Fin r → Fin n
  minorColumns_injective : Function.Injective minorColumns
  /-- An ambient coordinate not used by the selected minor. -/
  extraColumn : Fin n
  extraColumn_not_mem : extraColumn ∉ Set.range minorColumns
  /-- The selected integral minor is nonsingular. -/
  minor_det_ne_zero : (coordinateMinor A minorColumns).det ≠ 0
  /-- The real span of the integral rows is precisely the represented subspace. -/
  span_eq : Submodule.span ℝ (Set.range (realRow A)) = L

namespace Presentation

variable {L : Submodule ℝ (EuclideanSpace ℝ (Fin n))}

/-- The nonsingular coordinate minor really does certify that the integral
rows are linearly independent over `ℝ`.  Thus, together with `span_eq`, the
rows in a `Presentation` are an explicit basis of `L`. -/
theorem rows_linearIndependent (P : Presentation (r := r) L) :
    LinearIndependent ℝ (realRow P.A) := by
  let B : Matrix (Fin r) (Fin r) ℝ :=
    (coordinateMinor P.A P.minorColumns).map (Int.castRingHom ℝ)
  have hBdet : B.det ≠ 0 := by
    rw [show B.det = ((coordinateMinor P.A P.minorColumns).det : ℝ) by
      exact ((Int.castRingHom ℝ).map_det
        (coordinateMinor P.A P.minorColumns)).symm]
    exact_mod_cast P.minor_det_ne_zero
  have hB : LinearIndependent ℝ B.row :=
    Matrix.linearIndependent_rows_of_det_ne_zero hBdet
  rw [Fintype.linearIndependent_iff] at hB ⊢
  intro g hg i
  apply hB g
  · funext k
    have hk := congrArg
      (fun v : EuclideanSpace ℝ (Fin n) ↦ v (P.minorColumns k)) hg
    simpa [B, realRow, coordinateMinor, PiLp.toLp_apply] using hk

/-- The integral rows, bundled as an honest real basis of the represented
subspace.  This is derived from, rather than added to, the presentation:
the nonsingular minor supplies independence and `span_eq` supplies spanning. -/
noncomputable def rowBasis (P : Presentation (r := r) L) :
    Basis (Fin r) ℝ L :=
  (Basis.span P.rows_linearIndependent).map
    (LinearEquiv.ofEq _ _ P.span_eq)

@[simp]
theorem rowBasis_coe (P : Presentation (r := r) L) (i : Fin r) :
    (P.rowBasis i : EuclideanSpace ℝ (Fin n)) = realRow P.A i := by
  simp [rowBasis]

/-- The intrinsic integral row lattice inside the represented real
subspace. -/
noncomputable def rowLattice (P : Presentation (r := r) L) : Submodule ℤ L :=
  Submodule.span ℤ (Set.range P.rowBasis)

/-- The displayed integral row basis is saturated when it generates every
integral point of the represented rational subspace, i.e. when its row
lattice is literally `L ∩ ℤⁿ`. -/
def IsSaturated (P : Presentation (r := r) L) : Prop :=
  P.rowLattice = integralPoints L

/-- The intrinsic lattice covolume has the same square as the displayed
row parallelepiped. -/
theorem rowLattice_covolume_sq_eq_rowCovolume_sq
    (P : Presentation (r := r) L) :
    ZLattice.covolume P.rowLattice ^ 2 = rowCovolume P.A ^ 2 := by
  rw [rowCovolume_sq_eq_det_gram]
  have h := covolume_span_basis_sq_eq_det_gram P.rowBasis
  rw [show P.rowLattice = Submodule.span ℤ (Set.range P.rowBasis) from rfl]
  rw [show Matrix.gram ℝ P.rowBasis =
      Matrix.gram ℝ (realRow P.A) by
    ext i j
    simp only [Matrix.gram_apply]
    rw [← P.rowBasis_coe i, ← P.rowBasis_coe j]
    rfl] at h
  exact h

/-- The displayed Euclidean row covolume is exactly Mathlib's intrinsic
`ZLattice.covolume` of the integral row lattice. -/
theorem rowLattice_covolume_eq_rowCovolume
    (P : Presentation (r := r) L) :
    ZLattice.covolume P.rowLattice = rowCovolume P.A := by
  have hsquare := P.rowLattice_covolume_sq_eq_rowCovolume_sq
  have hleft : 0 ≤ ZLattice.covolume P.rowLattice :=
    ENNReal.toReal_nonneg
  have hright : 0 ≤ rowCovolume P.A := rowCovolume_nonneg P.A
  nlinarith

/-- The Euclidean covolume of the explicit integral row basis. -/
noncomputable def determinant (P : Presentation (r := r) L) : ℝ :=
  rowCovolume P.A

theorem rowLattice_covolume_eq_determinant
    (P : Presentation (r := r) L) :
    ZLattice.covolume P.rowLattice = P.determinant :=
  P.rowLattice_covolume_eq_rowCovolume

theorem determinant_nonneg (P : Presentation (r := r) L) :
    0 ≤ P.determinant :=
  rowCovolume_nonneg P.A

theorem determinant_eq_sqrt_det_gram (P : Presentation (r := r) L) :
    P.determinant = Real.sqrt (Matrix.gram ℝ (realRow P.A)).det :=
  rowCovolume_eq_sqrt_det_gram P.A

/-- Matrix orthogonality is Euclidean orthogonality to each integral row. -/
theorem inner_integralReal_eq_mulVec (P : Presentation (r := r) L)
    (x : Fin n → ℤ) (i : Fin r) :
    ⟪realRow P.A i, integralReal x⟫ =
      ((Matrix.mulVec P.A x i : ℤ) : ℝ) := by
  simp [PiLp.inner_apply, Matrix.mulVec, dotProduct, mul_comm]

/-- If an integral vector is killed by the row matrix, it is orthogonal to
every vector of the represented real subspace. -/
theorem orthogonal_to_subspace_of_mulVec_eq_zero
    (P : Presentation (r := r) L) (x : Fin n → ℤ)
    (hx : Matrix.mulVec P.A x = 0) :
    ∀ y ∈ L, ⟪y, integralReal x⟫ = 0 := by
  intro y hy
  rw [← P.span_eq] at hy
  refine Submodule.span_induction
    (p := fun y _ ↦ ⟪y, integralReal x⟫ = 0) ?_ ?_ ?_ ?_ hy
  · rintro z ⟨i, rfl⟩
    rw [P.inner_integralReal_eq_mulVec x i, congrFun hx i]
    simp
  · simp
  · intro u v _ _ hu hv
    simp [inner_add_left, hu, hv]
  · intro a u _ hu
    simp [inner_smul_left, hu]

/-- **Bombieri--Vaaler for an explicitly presented rational subspace.**

There is a nonzero integral normal vector to `L`, and every coordinate is at
most the Euclidean covolume of the integral row basis. -/
theorem exists_integral_normal_abs_le_determinant
    (P : Presentation (r := r) L) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (∀ y ∈ L, ⟪y, integralReal x⟫ = 0) ∧
      ∀ j, ((|x j| : ℤ) : ℝ) ≤ P.determinant := by
  obtain ⟨x, hx0, hxker, hxbound⟩ :=
    exists_ne_zero_mulVec_eq_zero_abs_cast_le_rowCovolume
      P.A P.minorColumns P.minorColumns_injective P.extraColumn
      P.extraColumn_not_mem P.minor_det_ne_zero
  exact ⟨x, hx0, P.orthogonal_to_subspace_of_mulVec_eq_zero x hxker, hxbound⟩

/-- Intrinsic lattice formulation of Bilu's Lemma 6.10.  The bound is
Mathlib's `ZLattice.covolume` of the integral row lattice, with the equality
to the displayed Gram determinant proved above rather than assumed. -/
theorem exists_integral_normal_abs_le_covolume
    (P : Presentation (r := r) L) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (∀ y ∈ L, ⟪y, integralReal x⟫ = 0) ∧
      ∀ j, ((|x j| : ℤ) : ℝ) ≤ ZLattice.covolume P.rowLattice := by
  rw [P.rowLattice_covolume_eq_determinant]
  exact P.exists_integral_normal_abs_le_determinant

/-- Literal rational-subspace form of Bilu's Lemma 6.10.  Saturation is
stated explicitly: when the displayed rows form a `ℤ`-basis of
`L ∩ ℤⁿ`, the normal-vector bound is the covolume of that full
intersection lattice. -/
theorem exists_integral_normal_abs_le_integralPoints_covolume
    (P : Presentation (r := r) L) (hSat : P.IsSaturated) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (∀ y ∈ L, ⟪y, integralReal x⟫ = 0) ∧
      ∀ j, ((|x j| : ℤ) : ℝ) ≤ ZLattice.covolume (integralPoints L) := by
  rw [← hSat]
  exact P.exists_integral_normal_abs_le_covolume

/-- Square-root-of-Gram form, matching the usual determinant notation for
the row lattice in Bilu's Lemma 6.10. -/
theorem exists_integral_normal_abs_le_sqrt_det_gram
    (P : Presentation (r := r) L) :
    ∃ x : Fin n → ℤ, x ≠ 0 ∧
      (∀ y ∈ L, ⟪y, integralReal x⟫ = 0) ∧
      ∀ j, ((|x j| : ℤ) : ℝ) ≤
        Real.sqrt (Matrix.gram ℝ (realRow P.A)).det := by
  simpa [P.determinant_eq_sqrt_det_gram] using
    P.exists_integral_normal_abs_le_determinant

end Presentation

end Erdos186.CFP.Bilu.SubspaceLattice

#print axioms Erdos186.CFP.Bilu.SubspaceLattice.Presentation.exists_integral_normal_abs_le_integralPoints_covolume
