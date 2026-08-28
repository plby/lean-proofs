import Wikipedia.HopfProblem.PeriodTorusFirstHomology
import Wikipedia.HopfProblem.PeriodMonodromy

/-!
# Integral singular homology in the period-domain marking

The four columns of the actual period-domain matrix are indexed by the
source's ordered dual basis `(γ̂,û,ŵ,δ̂)`. Their integral combinations
identify the actual lattice with `ℤ⁴`. Monodromy of the actual quotient
covering gives the correspondingly marked fundamental group, and the
proved first Hurewicz isomorphism gives the genuine singular homology.

The straight loop to the period vector of `c` has coordinate `c`, so both
the order and sign of the marking are determined geometrically.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodDomain

open FirstHurewicz

variable (p : PeriodDomain)

/-- The integral combination of the four actual period columns. -/
def periodVector : Lattice →+ ComplexPlane₂ where
  toFun c := p.val.matrix *ᵥ (fun i => (c i : ℂ))
  map_zero' := by
    simp only [Pi.zero_apply, Int.cast_zero]
    exact Matrix.mulVec_zero _
  map_add' c d := by
    simp only [Pi.add_apply, Int.cast_add]
    exact Matrix.mulVec_add _ _ _

@[simp] theorem periodVector_apply (c : Lattice) :
    p.periodVector c = p.val.matrix *ᵥ (fun i => (c i : ℂ)) := rfl

theorem periodVector_eq_sum (c : Lattice) :
    p.periodVector c = ∑ i, c i • p.basis i := by
  ext j
  simp [periodVector, Matrix.mulVec, dotProduct, p.basis_apply, zsmul_eq_mul, mul_comm]

theorem periodVector_injective : Function.Injective p.periodVector := by
  intro c d h
  have hi : LinearIndependent ℤ p.basis := p.basis.linearIndependent.restrict_scalars' ℤ
  apply funext
  apply (Fintype.linearIndependent_iffₛ.mp hi) c d
  rw [← p.periodVector_eq_sum, ← p.periodVector_eq_sum]
  exact h

/-- Membership in the actual lattice is exactly an integral period combination. -/
theorem mem_lattice_iff (z : ComplexPlane₂) :
    z ∈ p.lattice ↔ ∃ c : Lattice, p.periodVector c = z := by
  rw [p.lattice_eq_span_basis, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (p.periodVector_eq_sum c).trans hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, (p.periodVector_eq_sum c).symm.trans hc⟩

theorem periodVector_mem_lattice (c : Lattice) : p.periodVector c ∈ p.lattice :=
  (p.mem_lattice_iff _).mpr ⟨c, rfl⟩

/-- The explicit map from integral coordinates to the actual discrete lattice. -/
def periodLatticeMap : Lattice →+ p.lattice :=
  p.periodVector.codRestrict p.lattice.toAddSubgroup p.periodVector_mem_lattice

@[simp] theorem periodLatticeMap_coe (c : Lattice) :
    (p.periodLatticeMap c : ComplexPlane₂) = p.periodVector c := rfl

theorem periodLatticeMap_bijective : Function.Bijective p.periodLatticeMap := by
  constructor
  · intro c d h
    exact p.periodVector_injective (congrArg Subtype.val h)
  · intro z
    obtain ⟨c, hc⟩ := (p.mem_lattice_iff z).mp z.property
    exact ⟨c, Subtype.ext hc⟩

/-- The four columns give an integral marking of the genuine lattice. -/
def periodLatticeEquiv : Lattice ≃+ p.lattice :=
  AddEquiv.ofBijective p.periodLatticeMap p.periodLatticeMap_bijective

def latticeEquiv : p.lattice ≃+ Lattice := p.periodLatticeEquiv.symm

@[simp] theorem periodLatticeEquiv_coe (c : Lattice) :
    (p.periodLatticeEquiv c : ComplexPlane₂) = p.periodVector c := rfl

theorem periodVector_latticeEquiv (z : p.lattice) :
    p.periodVector (p.latticeEquiv z) = z :=
  congrArg Subtype.val (p.periodLatticeEquiv.apply_symm_apply z)

/-- The actual lattice quotient is a quotient covering map. -/
theorem quotientCovering :
    IsAddQuotientCoveringMap p.lattice.mkQ p.lattice.toAddSubgroup := by
  apply p.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
  change IsDiscrete (p.lattice : Set ComplexPlane₂)
  let : DiscreteTopology (p.lattice : Set ComplexPlane₂) := p.lattice_discrete
  exact DiscreteTopology.isDiscrete

/-- The zero point in the covering vector space above the torus origin. -/
def zeroLift : p.lattice.mkQ ⁻¹' ({0} : Set p.Torus) := ⟨0, by simp⟩

/-- Actual covering monodromy, marked by the four ordered period columns. -/
def fundamentalGroupEquiv : FundamentalGroup p.Torus 0 ≃* Multiplicative Lattice :=
  ((p.quotientCovering.fundamentalGroupEquiv p.zeroLift).trans
    MulOpposite.opMulEquiv.symm).trans p.latticeEquiv.toMultiplicative

theorem fundamentalGroupEquiv_monodromy (g : FundamentalGroup p.Torus 0) :
    p.periodVector (p.fundamentalGroupEquiv g).toAdd =
      (p.quotientCovering.isCoveringMap.monodromy g p.zeroLift : ComplexPlane₂) := by
  have h := p.quotientCovering.unop_fundamentalGroupToMulOpposite_smul
    (e := p.zeroLift) (γ := g)
  change p.periodVector (p.latticeEquiv
    (p.quotientCovering.fundamentalGroupToMulOpposite p.zeroLift g).unop.toAdd) = _
  rw [p.periodVector_latticeEquiv]
  change ((p.quotientCovering.fundamentalGroupToMulOpposite
    p.zeroLift g).unop.toAdd : ComplexPlane₂) + 0 = _ at h
  simpa only [add_zero] using h

@[simp] theorem mkQ_periodVector (c : Lattice) : p.lattice.mkQ (p.periodVector c) = 0 :=
  (Submodule.Quotient.mk_eq_zero p.lattice).mpr (p.periodVector_mem_lattice c)

/-- The projection of the straight segment from zero to an integral period. -/
def periodLoop (c : Lattice) : Path (0 : p.Torus) 0 :=
  ((Path.segment (0 : ComplexPlane₂) (p.periodVector c)).map
    p.lattice.continuous_mkQ).cast (map_zero p.lattice.mkQ).symm
      (p.mkQ_periodVector c).symm

theorem periodLoop_apply (c : Lattice) (t : unitInterval) :
    p.periodLoop c t = p.lattice.mkQ ((t : ℝ) • p.periodVector c) := by
  simp only [periodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add]

theorem periodLoop_monodromy (c : Lattice) :
    p.quotientCovering.isCoveringMap.monodromy
      (loopQuotient (p.periodLoop c)) p.zeroLift =
        ⟨p.periodVector c, p.mkQ_periodVector c⟩ := by
  apply p.quotientCovering.isCoveringMap.monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk (Path.segment (0 : ComplexPlane₂) (p.periodVector c)))
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- The actual lifted endpoint fixes the sign and order of the marking. -/
@[simp] theorem fundamentalGroupEquiv_periodLoop (c : Lattice) :
    p.fundamentalGroupEquiv (loopQuotient (p.periodLoop c)) = Multiplicative.ofAdd c := by
  apply Multiplicative.toAdd.injective
  apply p.periodVector_injective
  rw [p.fundamentalGroupEquiv_monodromy, p.periodLoop_monodromy]
  rfl

theorem fundamentalGroupEquiv_symm_apply (c : Lattice) :
    p.fundamentalGroupEquiv.symm (Multiplicative.ofAdd c) =
      loopQuotient (p.periodLoop c) := by
  apply p.fundamentalGroupEquiv.injective
  rw [MulEquiv.apply_symm_apply, p.fundamentalGroupEquiv_periodLoop]

/-- The source's column marking on Mathlib's actual integral singular first homology. -/
def singularH1Equiv : SingularH1 p.Torus ≃ₗ[ℤ] Lattice :=
  singularH1EquivOfPi1 (0 : p.Torus) p.fundamentalGroupEquiv

@[simp] theorem singularH1Equiv_loopHomologyClass (q : Path (0 : p.Torus) 0) :
    p.singularH1Equiv (loopHomologyClass q) =
      (p.fundamentalGroupEquiv (loopQuotient q)).toAdd :=
  singularH1EquivOfPi1_loopHomologyClass (0 : p.Torus) p.fundamentalGroupEquiv q

@[simp] theorem singularH1Equiv_periodLoop (c : Lattice) :
    p.singularH1Equiv (loopHomologyClass (p.periodLoop c)) = c := by
  rw [p.singularH1Equiv_loopHomologyClass, p.fundamentalGroupEquiv_periodLoop]
  rfl

/-- Every homology class in this marking is represented by the indicated
actual straight period loop. -/
@[simp] theorem singularH1Equiv_symm_apply (c : Lattice) :
    p.singularH1Equiv.symm c = loopHomologyClass (p.periodLoop c) := by
  apply p.singularH1Equiv.injective
  rw [LinearEquiv.apply_symm_apply, p.singularH1Equiv_periodLoop]

theorem singularH1_free : Module.Free ℤ (SingularH1 p.Torus) :=
  Module.Free.of_equiv p.singularH1Equiv.symm

theorem singularH1_finite : Module.Finite ℤ (SingularH1 p.Torus) :=
  Module.Finite.of_surjective p.singularH1Equiv.symm.toLinearMap
    p.singularH1Equiv.symm.surjective

theorem singularH1_finrank : Module.finrank ℤ (SingularH1 p.Torus) = 4 := by
  rw [p.singularH1Equiv.finrank_eq]
  simp [Lattice]

theorem singularH1_torsionFree : Module.IsTorsionFree ℤ (SingularH1 p.Torus) := by
  let := p.singularH1_free
  infer_instance

end Wikipedia.HopfProblem.PeriodDomain
