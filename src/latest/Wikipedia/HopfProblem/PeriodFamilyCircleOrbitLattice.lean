import Wikipedia.HopfProblem.PeriodFamilyCircleOrbitLinearBasic

/-!
# The literal three-period lattice of the vertical-circle quotient

The projected periods are a real basis of `ℂ × ℝ`.  Their integral span has
columns `(6μ, 1)`, `(τ, 0)`, and `(1, 0)`.  We use its native quotient
topology throughout; no product decomposition of a varying family is asserted.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

/-- The three projected period columns form a real basis. -/
def orbitBasis (p : PeriodDomain) : Module.Basis (Fin 3) ℝ (ℂ × ℝ) :=
  (Pi.basisFun ℝ (Fin 3)).map (projectedPeriods p).toLinearEquiv

@[simp] theorem orbitBasis_apply (p : PeriodDomain) (i : Fin 3) :
    orbitBasis p i = projectedPeriods p (Pi.basisFun ℝ (Fin 3) i) := rfl

@[simp] theorem orbitBasis_zero (p : PeriodDomain) :
    orbitBasis p 0 = (6 * p.val.μ, 1) := by
  simp [orbitBasis_apply, projectedPeriods_apply, Pi.basisFun_apply]

@[simp] theorem orbitBasis_one (p : PeriodDomain) :
    orbitBasis p 1 = (p.val.τ, 0) := by
  simp [orbitBasis_apply, projectedPeriods_apply, Pi.basisFun_apply]

@[simp] theorem orbitBasis_two (p : PeriodDomain) :
    orbitBasis p 2 = (1, 0) := by
  simp [orbitBasis_apply, projectedPeriods_apply, Pi.basisFun_apply]

/-- The actual projected integer-period lattice. -/
def orbitLattice (p : PeriodDomain) : Submodule ℤ (ℂ × ℝ) :=
  Submodule.span ℤ (range (fun i => projectedPeriods p (Pi.basisFun ℝ (Fin 3) i)))

theorem orbitLattice_eq_span_basis (p : PeriodDomain) :
    orbitLattice p = Submodule.span ℤ (range (orbitBasis p)) := rfl

theorem sum_zsmul_orbitBasis (p : PeriodDomain) (n : Fin 3 → ℤ) :
    ∑ i, n i • orbitBasis p i = projectedPeriods p (fun i => (n i : ℝ)) := by
  simp only [Fin.sum_univ_three, orbitBasis_zero, orbitBasis_one, orbitBasis_two,
    projectedPeriods_apply]
  ext <;> simp [zsmul_eq_mul, mul_comm, mul_assoc]

theorem mem_orbitLattice_iff_projectedPeriods (p : PeriodDomain) (z : ℂ × ℝ) :
    z ∈ orbitLattice p ↔
      ∃ n : Fin 3 → ℤ, z = projectedPeriods p (fun i => (n i : ℝ)) := by
  rw [orbitLattice_eq_span_basis, Submodule.mem_span_range_iff_exists_fun]
  simp only [sum_zsmul_orbitBasis, eq_comm]

/-- Integral membership retains all three original projected columns. -/
theorem mem_orbitLattice_iff (p : PeriodDomain) (z : ℂ × ℝ) :
    z ∈ orbitLattice p ↔ ∃ n : Fin 3 → ℤ,
      z = (6 * p.val.μ * (n 0 : ℂ) + p.val.τ * (n 1 : ℂ) + (n 2 : ℂ),
        (n 0 : ℝ)) := by
  rw [mem_orbitLattice_iff_projectedPeriods]
  simp only [projectedPeriods_apply, Complex.ofReal_intCast]

instance orbitLattice_discrete (p : PeriodDomain) : DiscreteTopology (orbitLattice p) := by
  rw [orbitLattice_eq_span_basis]
  infer_instance

instance orbitLattice_isZLattice (p : PeriodDomain) : IsZLattice ℝ (orbitLattice p) := by
  constructor
  rw [orbitLattice_eq_span_basis]
  exact ZSpan.span_top (orbitBasis p)

instance orbitLattice_addSubgroup_discrete (p : PeriodDomain) :
    DiscreteTopology (orbitLattice p).toAddSubgroup :=
  inferInstanceAs (DiscreteTopology (orbitLattice p))

instance orbitLattice_isClosed (p : PeriodDomain) :
    IsClosed (orbitLattice p : Set (ℂ × ℝ)) := by
  change IsClosed ((orbitLattice p).toAddSubgroup : Set (ℂ × ℝ))
  exact AddSubgroup.isClosed_of_discrete (H := (orbitLattice p).toAddSubgroup)

theorem orbitLattice_rank (p : PeriodDomain) :
    Module.finrank ℤ (orbitLattice p) = 3 := by
  rw [ZLattice.rank ℝ (orbitLattice p), Module.finrank_eq_card_basis (orbitBasis p)]
  rfl

/-- The fixed-period orbit model, with its actual lattice quotient topology. -/
abbrev OrbitModel (p : PeriodDomain) := (ℂ × ℝ) ⧸ orbitLattice p

/-- The native quotient projection. -/
def orbitClass (p : PeriodDomain) : (ℂ × ℝ) →ₗ[ℤ] OrbitModel p :=
  (orbitLattice p).mkQ

theorem orbitClass_continuous (p : PeriodDomain) : Continuous (orbitClass p) :=
  (orbitLattice p).continuous_mkQ

theorem orbitClass_isOpenMap (p : PeriodDomain) : IsOpenMap (orbitClass p) :=
  (orbitLattice p).isOpenMap_mkQ

theorem orbitClass_surjective (p : PeriodDomain) : Function.Surjective (orbitClass p) :=
  (orbitLattice p).mkQ_surjective

theorem orbitClass_isQuotientMap (p : PeriodDomain) : IsQuotientMap (orbitClass p) :=
  (orbitLattice p).isQuotientMap_mkQ

theorem orbitClass_eq_iff (p : PeriodDomain) (z w : ℂ × ℝ) :
    orbitClass p z = orbitClass p w ↔ z - w ∈ orbitLattice p :=
  Submodule.Quotient.eq (orbitLattice p)

instance orbitModel_t3 (p : PeriodDomain) : T3Space (OrbitModel p) := inferInstance

instance orbitModel_secondCountable (p : PeriodDomain) :
    SecondCountableTopology (OrbitModel p) :=
  (orbitClass_isQuotientMap p).secondCountableTopology (orbitClass_isOpenMap p)

instance orbitModel_pathConnected (p : PeriodDomain) : PathConnectedSpace (OrbitModel p) :=
  (orbitClass_surjective p).pathConnectedSpace (orbitClass_continuous p)

instance orbitModel_compact (p : PeriodDomain) : CompactSpace (OrbitModel p) := by
  have hper : ∀ z w, w ∈ orbitLattice p → orbitClass p (z + w) = orbitClass p z := by
    intro z w hw
    have hw' : orbitClass p w = 0 := (Submodule.Quotient.mk_eq_zero (orbitLattice p)).mpr hw
    rw [map_add, hw', add_zero]
  have hc := IsZLattice.isCompact_range_of_periodic (orbitLattice p) (orbitClass p)
    (orbitClass_continuous p) hper
  exact ⟨by simpa only [range_eq_univ.mpr (orbitClass_surjective p)] using hc⟩

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
