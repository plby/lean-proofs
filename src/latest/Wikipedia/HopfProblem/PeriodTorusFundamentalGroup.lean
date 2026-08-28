import Wikipedia.HopfProblem.MatrixPeriodTori
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# The marked fundamental group of a period torus

The covering in this file is the actual quotient map from `ℂ²` to the
period torus. The integral marking sends the lattice vector `m + Z n` to
the pair `(m, n)`. The corresponding fundamental-group isomorphism is
constructed by lifting loops through this covering, not by postulating a
presentation of the fundamental group.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.FullPeriodMatrix

/-- The ordered integral coordinates for the period matrix `(1, Z)`. -/
abbrev IntegerPeriods := (Fin 2 → ℤ) × (Fin 2 → ℤ)

variable (p : FullPeriodMatrix)

/-- The period vector with integral coordinates `(m,n)` is `m + Z n`. -/
def periodVector : IntegerPeriods →+ ComplexPlane₂ where
  toFun c := (fun i => (c.1 i : ℂ)) + p.matrix *ᵥ (fun i => (c.2 i : ℂ))
  map_zero' := by ext i; simp [Matrix.mulVec, dotProduct]
  map_add' c d := by
    ext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Int.cast_add,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

theorem periodVector_apply (m n : Fin 2 → ℤ) :
    p.periodVector (m, n) = (fun i => (m i : ℂ)) +
      p.matrix *ᵥ (fun i => (n i : ℂ)) := rfl

theorem periodVector_eq_periodLinear (c : IntegerPeriods) :
    p.periodVector c = p.periodLinear
      ((fun i => (c.1 i : ℝ)), (fun i => (c.2 i : ℝ))) := by
  ext i
  simp [periodVector, periodLinear]

theorem periodVector_injective : Function.Injective p.periodVector := by
  intro c d h
  rw [p.periodVector_eq_periodLinear, p.periodVector_eq_periodLinear] at h
  have he := p.periodLinear_bijective.1 h
  apply Prod.ext
  · ext i
    have hi : (c.1 i : ℝ) = (d.1 i : ℝ) := congrFun (congrArg Prod.fst he) i
    exact_mod_cast hi
  · ext i
    have hi : (c.2 i : ℝ) = (d.2 i : ℝ) := congrFun (congrArg Prod.snd he) i
    exact_mod_cast hi

theorem periodVector_mem_lattice (c : IntegerPeriods) :
    p.periodVector c ∈ p.lattice :=
  (p.mem_lattice_iff _).mpr ⟨c.1, c.2, rfl⟩

/-- The explicit additive marking from integer coordinates to the lattice. -/
def periodLatticeMap : IntegerPeriods →+ p.lattice :=
  p.periodVector.codRestrict p.lattice.toAddSubgroup p.periodVector_mem_lattice

@[simp] theorem periodLatticeMap_coe (c : IntegerPeriods) :
    (p.periodLatticeMap c : ComplexPlane₂) = p.periodVector c := rfl

theorem periodLatticeMap_bijective : Function.Bijective p.periodLatticeMap := by
  constructor
  · intro c d h
    exact p.periodVector_injective (congrArg Subtype.val h)
  · intro z
    obtain ⟨m, n, hmn⟩ := (p.mem_lattice_iff z).mp z.property
    exact ⟨(m, n), Subtype.ext hmn.symm⟩

/-- The four integral periods form a basis of the actual discrete lattice. -/
def periodLatticeEquiv : IntegerPeriods ≃+ p.lattice :=
  AddEquiv.ofBijective p.periodLatticeMap p.periodLatticeMap_bijective

/-- Read the two integer pairs from a lattice vector. -/
def latticeEquiv : p.lattice ≃+ IntegerPeriods := p.periodLatticeEquiv.symm

@[simp] theorem periodLatticeEquiv_coe (c : IntegerPeriods) :
    (p.periodLatticeEquiv c : ComplexPlane₂) = p.periodVector c := rfl

@[simp] theorem latticeEquiv_periodLatticeEquiv (c : IntegerPeriods) :
    p.latticeEquiv (p.periodLatticeEquiv c) = c :=
  p.periodLatticeEquiv.symm_apply_apply c

theorem periodVector_latticeEquiv (z : p.lattice) :
    p.periodVector (p.latticeEquiv z) = z :=
  congrArg Subtype.val (p.periodLatticeEquiv.apply_symm_apply z)

/-- The lattice quotient is a genuine quotient covering map. -/
theorem quotientCovering :
    IsAddQuotientCoveringMap p.lattice.mkQ p.lattice.toAddSubgroup := by
  apply p.lattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
  change IsDiscrete (p.lattice : Set ComplexPlane₂)
  let : DiscreteTopology (p.lattice : Set ComplexPlane₂) := p.lattice_discrete
  exact DiscreteTopology.isDiscrete

/-- The selected lift of the zero basepoint. -/
def zeroLift : p.lattice.mkQ ⁻¹' ({0} : Set p.Torus) :=
  ⟨0, by simp⟩

/-- Monodromy gives the actual fundamental group with its `(m,n)` marking. -/
def fundamentalGroupEquiv :
    FundamentalGroup p.Torus 0 ≃* Multiplicative IntegerPeriods :=
  ((p.quotientCovering.fundamentalGroupEquiv p.zeroLift).trans
    MulOpposite.opMulEquiv.symm).trans p.latticeEquiv.toMultiplicative

/-- The marked period is exactly the endpoint of the lift of a loop
starting at zero. This characterizes the integral marking geometrically. -/
theorem fundamentalGroupEquiv_monodromy (γ : FundamentalGroup p.Torus 0) :
    p.periodVector (p.fundamentalGroupEquiv γ).toAdd =
      (p.quotientCovering.isCoveringMap.monodromy γ p.zeroLift : ComplexPlane₂) := by
  have h := p.quotientCovering.unop_fundamentalGroupToMulOpposite_smul
    (e := p.zeroLift) (γ := γ)
  change p.periodVector
      (p.latticeEquiv (p.quotientCovering.fundamentalGroupToMulOpposite
        p.zeroLift γ).unop.toAdd) = _
  rw [p.periodVector_latticeEquiv]
  change ((p.quotientCovering.fundamentalGroupToMulOpposite
    p.zeroLift γ).unop.toAdd : ComplexPlane₂) + 0 = _ at h
  simpa only [add_zero] using h

@[simp] theorem mkQ_periodVector (c : IntegerPeriods) :
    p.lattice.mkQ (p.periodVector c) = 0 :=
  (Submodule.Quotient.mk_eq_zero p.lattice).mpr (p.periodVector_mem_lattice c)

/-- The loop obtained by projecting the straight segment from zero to an
integral period. -/
def periodLoop (c : IntegerPeriods) : Path (0 : p.Torus) 0 :=
  ((Path.segment (0 : ComplexPlane₂) (p.periodVector c)).map
    p.lattice.continuous_mkQ).cast (map_zero p.lattice.mkQ).symm
      (p.mkQ_periodVector c).symm

theorem periodLoop_apply (c : IntegerPeriods) (t : unitInterval) :
    p.periodLoop c t = p.lattice.mkQ ((t : ℝ) • p.periodVector c) := by
  simp only [periodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add]

/-- A straight period loop lifts to the corresponding straight segment,
so its lifted endpoint is the specified period vector. -/
theorem periodLoop_monodromy (c : IntegerPeriods) :
    p.quotientCovering.isCoveringMap.monodromy
      (FundamentalGroup.fromPath ⟦p.periodLoop c⟧) p.zeroLift =
        ⟨p.periodVector c, p.mkQ_periodVector c⟩ := by
  apply p.quotientCovering.isCoveringMap.monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk (Path.segment (0 : ComplexPlane₂) (p.periodVector c)))
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- The isomorphism sends the class of `t ↦ t(m + Z n)` to `(m,n)`,
with the stated order and sign of the integral coordinates. -/
@[simp] theorem fundamentalGroupEquiv_periodLoop (c : IntegerPeriods) :
    p.fundamentalGroupEquiv (FundamentalGroup.fromPath ⟦p.periodLoop c⟧) =
      Multiplicative.ofAdd c := by
  apply Multiplicative.toAdd.injective
  apply p.periodVector_injective
  rw [p.fundamentalGroupEquiv_monodromy, p.periodLoop_monodromy]
  rfl

/-- Every marked fundamental-group element is represented by its straight
period loop. -/
theorem fundamentalGroupEquiv_symm_apply (c : IntegerPeriods) :
    p.fundamentalGroupEquiv.symm (Multiplicative.ofAdd c) =
      FundamentalGroup.fromPath ⟦p.periodLoop c⟧ := by
  apply p.fundamentalGroupEquiv.injective
  rw [p.fundamentalGroupEquiv.apply_symm_apply]
  exact (p.fundamentalGroupEquiv_periodLoop c).symm

end Wikipedia.HopfProblem.FullPeriodMatrix
