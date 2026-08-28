import Wikipedia.HopfProblem.PeriodTori

/-!
# The elliptic factor and its actual return translation

The two columns `τ, 1` define a discrete full lattice in the original complex
line.  Its quotient carries the native quotient topology.  The return map
is translation by the class of `-6μ`; its integer powers retain this literal
complex-coordinate formula.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyCircleOrbit

/-- Real coordinates for the two actual elliptic period columns. -/
def ellipticCoordinates (p : PeriodDomain) : (Fin 2 → ℝ) ≃ₗ[ℝ] ℂ where
  toFun x := p.val.τ * (x 0 : ℂ) + (x 1 : ℂ)
  invFun z := ![z.im / p.val.τ.im, z.re - p.val.τ.re * (z.im / p.val.τ.im)]
  left_inv x := by
    have hτ : p.val.τ.im ≠ 0 := ne_of_gt p.property.1
    ext i
    fin_cases i <;> simp [Complex.mul_re, Complex.mul_im, hτ]
  right_inv z := by
    have hτ : p.val.τ.im ≠ 0 := ne_of_gt p.property.1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    field_simp
  map_add' x y := by
    simp only [Pi.add_apply, Complex.ofReal_add, mul_add]
    ring
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_mul,
      RingHom.id_apply]
    ring

/-- The real basis consisting of `τ` and `1`, in that order. -/
def ellipticBasis (p : PeriodDomain) : Module.Basis (Fin 2) ℝ ℂ :=
  (Pi.basisFun ℝ (Fin 2)).map (ellipticCoordinates p)

theorem ellipticBasis_apply (p : PeriodDomain) (i : Fin 2) :
    ellipticBasis p i = ![p.val.τ, 1] i := by
  fin_cases i <;> simp [ellipticBasis, ellipticCoordinates, Pi.basisFun_apply]

/-- The integral span of the two original elliptic periods. -/
def ellipticLattice (p : PeriodDomain) : Submodule ℤ ℂ :=
  Submodule.span ℤ (Set.range ![p.val.τ, (1 : ℂ)])

theorem ellipticLattice_eq_span_basis (p : PeriodDomain) :
    ellipticLattice p = Submodule.span ℤ (Set.range (ellipticBasis p)) := by
  unfold ellipticLattice
  apply congrArg (Submodule.span ℤ)
  apply congrArg Set.range
  funext i
  exact (ellipticBasis_apply p i).symm

theorem ellipticLattice_mem_iff (p : PeriodDomain) (z : ℂ) :
    z ∈ ellipticLattice p ↔ ∃ m n : ℤ, z = p.val.τ * (m : ℂ) + (n : ℂ) := by
  rw [ellipticLattice, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v 0, v 1, ?_⟩
    simpa [Fin.sum_univ_two, zsmul_eq_mul, mul_comm] using hv.symm
  · rintro ⟨m, n, rfl⟩
    refine ⟨![m, n], ?_⟩
    simp [Fin.sum_univ_two, zsmul_eq_mul, mul_comm]

instance ellipticLattice_discrete (p : PeriodDomain) : DiscreteTopology (ellipticLattice p) := by
  rw [ellipticLattice_eq_span_basis]
  infer_instance

instance ellipticLattice_isZLattice (p : PeriodDomain) : IsZLattice ℝ (ellipticLattice p) := by
  constructor
  rw [ellipticLattice_eq_span_basis]
  exact ZSpan.span_top (ellipticBasis p)

instance ellipticLattice_addSubgroup_discrete (p : PeriodDomain) :
    DiscreteTopology (ellipticLattice p).toAddSubgroup :=
  inferInstanceAs (DiscreteTopology (ellipticLattice p))

instance ellipticLattice_isClosed (p : PeriodDomain) :
    IsClosed (ellipticLattice p : Set ℂ) := by
  change IsClosed ((ellipticLattice p).toAddSubgroup : Set ℂ)
  exact AddSubgroup.isClosed_of_discrete (H := (ellipticLattice p).toAddSubgroup)

/-- The elliptic curve with its unchanged quotient topology. -/
abbrev EllipticModel (p : PeriodDomain) := ℂ ⧸ ellipticLattice p

/-- The native additive quotient map from the complex line. -/
def ellipticClass (p : PeriodDomain) : ℂ →ₗ[ℤ] EllipticModel p :=
  (ellipticLattice p).mkQ

theorem ellipticClass_eq_iff (p : PeriodDomain) (z w : ℂ) :
    ellipticClass p z = ellipticClass p w ↔ z - w ∈ ellipticLattice p :=
  Submodule.Quotient.eq (ellipticLattice p)

theorem ellipticClass_eq_iff_exists (p : PeriodDomain) (z w : ℂ) :
    ellipticClass p z = ellipticClass p w ↔
      ∃ m n : ℤ, z - w = p.val.τ * (m : ℂ) + (n : ℂ) := by
  rw [ellipticClass_eq_iff, ellipticLattice_mem_iff]

theorem ellipticClass_continuous (p : PeriodDomain) : Continuous (ellipticClass p) :=
  (ellipticLattice p).continuous_mkQ

theorem ellipticClass_surjective (p : PeriodDomain) : Function.Surjective (ellipticClass p) :=
  (ellipticLattice p).mkQ_surjective

theorem ellipticClass_isOpenMap (p : PeriodDomain) : IsOpenMap (ellipticClass p) :=
  (ellipticLattice p).isOpenMap_mkQ

theorem ellipticClass_isOpenQuotientMap (p : PeriodDomain) :
    IsOpenQuotientMap (ellipticClass p) :=
  (ellipticLattice p).isOpenQuotientMap_mkQ

instance ellipticModel_t2 (p : PeriodDomain) : T2Space (EllipticModel p) := inferInstance

instance ellipticModel_compact (p : PeriodDomain) : CompactSpace (EllipticModel p) := by
  have hper : ∀ z w : ℂ, w ∈ ellipticLattice p →
      ellipticClass p (z + w) = ellipticClass p z := by
    intro z w hw
    have hw' : ellipticClass p w = 0 :=
      (Submodule.Quotient.mk_eq_zero (ellipticLattice p)).mpr hw
    rw [map_add, hw', add_zero]
  have hc := IsZLattice.isCompact_range_of_periodic (ellipticLattice p)
    (ellipticClass p) (ellipticClass_continuous p) hper
  exact ⟨by simpa only [Set.range_eq_univ.mpr (ellipticClass_surjective p)] using hc⟩

/-- The native elliptic return map; the deck action uses its inverse. -/
def returnTranslation (p : PeriodDomain) : EllipticModel p ≃ₜ EllipticModel p :=
  Homeomorph.subRight (ellipticClass p (6 * p.val.μ))

@[simp] theorem returnTranslation_apply (p : PeriodDomain) (x : EllipticModel p) :
    returnTranslation p x = x - ellipticClass p (6 * p.val.μ) := rfl

@[simp] theorem returnTranslation_symm_apply (p : PeriodDomain) (x : EllipticModel p) :
    (returnTranslation p).symm x = x + ellipticClass p (6 * p.val.μ) := rfl

@[simp] theorem returnTranslation_class (p : PeriodDomain) (z : ℂ) :
    returnTranslation p (ellipticClass p z) = ellipticClass p (z - 6 * p.val.μ) := by
  rw [returnTranslation_apply, map_sub]

theorem returnTranslation_zpow_apply (p : PeriodDomain) (n : ℤ) (x : EllipticModel p) :
    (returnTranslation p ^ n) x = x - n • ellipticClass p (6 * p.val.μ) := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Homeomorph.mul_apply, ih, returnTranslation_apply, add_zsmul]
    simp only [one_zsmul]
    abel
  | pred n ih =>
    rw [zpow_sub_one, Homeomorph.mul_apply, Homeomorph.inv_apply, ih,
      returnTranslation_symm_apply, sub_zsmul]
    simp only [one_zsmul]
    abel

theorem returnTranslation_zpow_class (p : PeriodDomain) (n : ℤ) (z : ℂ) :
    (returnTranslation p ^ n) (ellipticClass p z) =
      ellipticClass p (z - (n : ℂ) * (6 * p.val.μ)) := by
  rw [returnTranslation_zpow_apply, map_sub, ← map_zsmul]
  simp only [zsmul_eq_mul]

end Wikipedia.HopfProblem.PeriodFamilyCircleOrbit
