import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.EllipticAffineMaps

/-!
# The affine elliptic action on the real period torus

The space here is the actual quotient by the standard integral lattice,
with its quotient topology.  Conjugating an explicit fixed-period
biholomorphism produces the affine homeomorphism on this quotient.  Its
lift formula shows that the resulting map is precisely `x ↦ A x + v/m`,
independently of the fixed period used to construct the homeomorphism.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

private theorem sum_zsmul_basisFun (v : Lattice) :
    (∑ i, v i • Pi.basisFun ℝ (Fin 4) i) = realCast v := by
  ext k
  simp [Pi.basisFun_apply, realCast, Pi.single_apply]

/-- Membership in the standard lattice means having integral coordinates. -/
theorem standardLattice_mem_iff (x : RealCoordinates) :
    x ∈ standardLattice ↔ ∃ v : Lattice, x = realCast v := by
  rw [standardLattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, hv.symm.trans (sum_zsmul_basisFun v)⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, sum_zsmul_basisFun v⟩

/-- Equality of classes in the real torus is exactly integral congruence. -/
theorem flatTorus_mkQ_eq_iff (x y : RealCoordinates) :
    standardLattice.mkQ x = standardLattice.mkQ y ↔ FlatCongruent x y := by
  change (Submodule.Quotient.mk x : RealTorus₄) = Submodule.Quotient.mk y ↔ _
  rw [Submodule.Quotient.eq, standardLattice_mem_iff]
  rfl

theorem periodEquiv_map_standardLattice (p : PeriodDomain) :
    standardLattice.map ((periodEquiv p).toLinearEquiv.restrictScalars ℤ).toLinearMap =
      p.lattice := by
  ext z
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (periodEquiv_mem_lattice_iff p x).mpr ((standardLattice_mem_iff x).mp hx)
  · intro hz
    refine ⟨(periodEquiv p).symm z, ?_, (periodEquiv p).apply_symm_apply z⟩
    apply (standardLattice_mem_iff _).mpr
    apply (periodEquiv_mem_lattice_iff p _).mp
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz

/-- Period coordinates identify the actual real and complex lattice quotients. -/
def flatTorusPeriodHomeomorph (p : PeriodDomain) : RealTorus₄ ≃ₜ p.Torus where
  toEquiv := (Submodule.Quotient.equiv standardLattice p.lattice
    ((periodEquiv p).toLinearEquiv.restrictScalars ℤ)
    (periodEquiv_map_standardLattice p)).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact p.lattice.continuous_mkQ.comp (periodEquiv p).continuous
  continuous_invFun := by
    apply p.lattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp (periodEquiv p).symm.continuous

@[simp] theorem flatTorusPeriodHomeomorph_mkQ (p : PeriodDomain) (x : RealCoordinates) :
    flatTorusPeriodHomeomorph p (standardLattice.mkQ x) = flatProjection p x := rfl

@[simp] theorem flatTorusPeriodHomeomorph_symm_flatProjection
    (p : PeriodDomain) (x : RealCoordinates) :
    (flatTorusPeriodHomeomorph p).symm (flatProjection p x) = standardLattice.mkQ x := by
  rw [← flatTorusPeriodHomeomorph_mkQ, Homeomorph.symm_apply_apply]

/-- The actual affine homeomorphism of the real coordinate torus.
No invariance assumption on `v` is needed for the homeomorphism itself. -/
def flatTorusAffine (j : Kind) (v : Lattice) : RealTorus₄ ≃ₜ RealTorus₄ :=
  ((flatTorusPeriodHomeomorph (exampleFixedPeriod j).val).trans
    (affineBiholomorph j (exampleFixedPeriod j) v).toHomeomorph).trans
      (flatTorusPeriodHomeomorph (exampleFixedPeriod j).val).symm

/-- The defining affine lift, on every representative of the real torus. -/
@[simp] theorem flatTorusAffine_mkQ (j : Kind) (v : Lattice) (x : RealCoordinates) :
    flatTorusAffine j v (standardLattice.mkQ x) =
      standardLattice.mkQ (flatAffine j v x) := by
  change (flatTorusPeriodHomeomorph (exampleFixedPeriod j).val).symm
    (affineBiholomorph j (exampleFixedPeriod j) v
      (flatTorusPeriodHomeomorph (exampleFixedPeriod j).val (standardLattice.mkQ x))) = _
  rw [flatTorusPeriodHomeomorph_mkQ, affineBiholomorph_flatProjection,
    flatTorusPeriodHomeomorph_symm_flatProjection]

/-- The map intertwines with the affine biholomorphism at every fixed period,
not only the explicit period used in its construction. -/
theorem flatTorusAffine_periodHomeomorph (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (y : RealTorus₄) :
    flatTorusPeriodHomeomorph p.val (flatTorusAffine j v y) =
      affineBiholomorph j p v (flatTorusPeriodHomeomorph p.val y) := by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  rw [flatTorusAffine_mkQ, flatTorusPeriodHomeomorph_mkQ,
    flatTorusPeriodHomeomorph_mkQ, affineBiholomorph_flatProjection]

theorem flatTorusAffine_iterate_mkQ (j : Kind) (v : Lattice)
    (r : ℕ) (x : RealCoordinates) :
    (flatTorusAffine j v)^[r] (standardLattice.mkQ x) =
      standardLattice.mkQ ((flatAffine j v)^[r] x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      flatTorusAffine_mkQ]

/-- The invariant integral twist makes the `m`-th iterate the identity. -/
theorem flatTorusAffine_iterate_order (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (y : RealTorus₄) :
    (flatTorusAffine j v)^[j.order] y = y := by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  rw [flatTorusAffine_iterate_mkQ]
  exact (flatTorus_mkQ_eq_iff _ _).mpr (flatAffine_iterate_order_congruent j v hv x)

/-- Every nonidentity iterate of an admissible twist is fixed-point-free. -/
theorem flatTorusAffine_iterate_ne (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hr : 0 < r) (hrm : r < j.order)
    (y : RealTorus₄) : (flatTorusAffine j v)^[r] y ≠ y := by
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective y
  rw [flatTorusAffine_iterate_mkQ]
  exact fun h => flatAffine_iterate_not_congruent j v hv r hr hrm x
    ((flatTorus_mkQ_eq_iff _ _).mp h)

/-- The underlying permutation of the actual real torus. -/
def flatTorusPermutation (j : Kind) (v : Lattice) : Equiv.Perm RealTorus₄ :=
  (flatTorusAffine j v).toEquiv

theorem flatTorusPermutation_pow_mkQ (j : Kind) (v : Lattice)
    (r : ℕ) (x : RealCoordinates) :
    (flatTorusPermutation j v ^ r) (standardLattice.mkQ x) =
      standardLattice.mkQ ((flatAffine j v)^[r] x) := by
  rw [Equiv.Perm.coe_pow]
  exact flatTorusAffine_iterate_mkQ j v r x

theorem flatTorusPermutation_pow_order (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : flatTorusPermutation j v ^ j.order = 1 := by
  apply Equiv.ext
  intro y
  rw [Equiv.Perm.coe_pow]
  exact flatTorusAffine_iterate_order j v hv y

theorem flatTorusPermutation_pow_ne (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hr : 0 < r) (hrm : r < j.order)
    (y : RealTorus₄) : (flatTorusPermutation j v ^ r) y ≠ y := by
  rw [Equiv.Perm.coe_pow]
  exact flatTorusAffine_iterate_ne j v hv r hr hrm y

/-- The exact freeness criterion on the actual quotient space. -/
theorem flatTorusPermutation_free_iff (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    (∀ r : ℕ, 0 < r → r < j.order → ∀ y : RealTorus₄,
      (flatTorusPermutation j v ^ r) y ≠ y) ↔ AdmissibleTwist j v := by
  constructor
  · intro h
    apply (flatAffine_free_iff j v hv).mp
    intro r hr hrm x hx
    apply h r hr hrm (standardLattice.mkQ x)
    rw [flatTorusPermutation_pow_mkQ]
    exact (flatTorus_mkQ_eq_iff _ _).mpr hx
  · intro ha
    exact flatTorusPermutation_pow_ne j v ha

/-- For an admissible twist the permutation has order exactly `m`, not merely
order dividing `m`. -/
theorem flatTorusPermutation_orderOf (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) : orderOf (flatTorusPermutation j v) = j.order := by
  apply (orderOf_eq_iff j.order_pos).mpr
  refine ⟨flatTorusPermutation_pow_order j v hv.1, ?_⟩
  intro r hrm hr heq
  apply flatTorusPermutation_pow_ne j v hv r hr hrm (0 : RealTorus₄)
  rw [heq]
  rfl

/-- The two twists selected in §5 give actual finite free torus homeomorphisms. -/
theorem mainFlatTorus_finite_free (j : Kind) :
    flatTorusPermutation j j.twist ^ j.order = 1 ∧
      ∀ r : ℕ, 0 < r → r < j.order → ∀ y : RealTorus₄,
        (flatTorusPermutation j j.twist ^ r) y ≠ y :=
  ⟨flatTorusPermutation_pow_order j j.twist j.matrix_fixes_twist,
    flatTorusPermutation_pow_ne j j.twist (mainTwist_admissible j)⟩

end Wikipedia.HopfProblem.Elliptic
