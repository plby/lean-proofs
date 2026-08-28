import Wikipedia.HopfProblem.EllipticData
import Wikipedia.HopfProblem.PeriodMonodromy

/-!
# Real coordinates on the actual elliptic period tori

The period columns identify the real coordinate space with the actual
complex covering space.  Under this identification, equality in the
complex torus is exactly congruence modulo the integral coordinate lattice.
This bridge transports the explicit affine freeness calculations to the
complex quotients, without replacing those quotients by formal models.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

/-- The real-linear period-coordinate equivalence. -/
def periodEquiv (p : PeriodDomain) : RealCoordinates ≃L[ℝ] ComplexPlane₂ :=
  p.basis.equivFun.symm.toContinuousLinearEquiv

theorem periodEquiv_apply (p : PeriodDomain) (x : RealCoordinates) :
    periodEquiv p x = ∑ i, x i • p.basis i :=
  p.basis.equivFun_symm_apply x

theorem periodEquiv_matrix (p : PeriodDomain) (x : RealCoordinates) :
    periodEquiv p x = p.val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [periodEquiv_apply]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, PeriodDomain.basis_apply,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  change (x k : ℂ) * p.val.matrix i k = p.val.matrix i k * (x k : ℂ)
  exact mul_comm _ _

theorem periodEquiv_realCast (p : PeriodDomain) (v : Lattice) :
    periodEquiv p (realCast v) = ∑ i, v i • p.basis i := by
  rw [periodEquiv_apply]
  simp only [realCast, Int.cast_smul_eq_zsmul]

/-- The integer vectors map onto precisely the period lattice. -/
theorem periodEquiv_mem_lattice_iff (p : PeriodDomain) (x : RealCoordinates) :
    periodEquiv p x ∈ p.lattice ↔ ∃ v : Lattice, x = realCast v := by
  rw [p.lattice_eq_span_basis, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, (periodEquiv p).injective ?_⟩
    rw [periodEquiv_realCast]
    exact hv.symm
  · rintro ⟨v, rfl⟩
    exact ⟨v, (periodEquiv_realCast p v).symm⟩

/-- The actual period-torus projection in real coordinates. -/
def flatProjection (p : PeriodDomain) (x : RealCoordinates) : p.Torus :=
  p.lattice.mkQ (periodEquiv p x)

theorem flatProjection_continuous (p : PeriodDomain) : Continuous (flatProjection p) :=
  p.lattice.continuous_mkQ.comp (periodEquiv p).continuous

theorem flatProjection_surjective (p : PeriodDomain) :
    Function.Surjective (flatProjection p) :=
  p.lattice.mkQ_surjective.comp (periodEquiv p).surjective

/-- Equality in the complex quotient is exactly integral congruence. -/
theorem flatProjection_eq_iff (p : PeriodDomain) (x y : RealCoordinates) :
    flatProjection p x = flatProjection p y ↔ FlatCongruent x y := by
  change (Submodule.Quotient.mk (periodEquiv p x) : p.Torus) =
    Submodule.Quotient.mk (periodEquiv p y) ↔ _
  rw [Submodule.Quotient.eq, ← map_sub, periodEquiv_mem_lattice_iff]
  rfl

@[simp] theorem flatProjection_add (p : PeriodDomain) (x y : RealCoordinates) :
    flatProjection p (x + y) = flatProjection p x + flatProjection p y := by
  simp only [flatProjection, map_add]

@[simp] theorem flatProjection_realCast (p : PeriodDomain) (v : Lattice) :
    flatProjection p (realCast v) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero p.lattice).mpr
  exact (periodEquiv_mem_lattice_iff p _).mpr ⟨v, rfl⟩

end Wikipedia.HopfProblem.Elliptic
