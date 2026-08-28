import Wikipedia.HopfProblem.TrianglePeriodFamilyLattice
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyPeriodDomain
import Wikipedia.HopfProblem.FirstHurewiczNaturality

/-!
# The actual singular homology marking of the flat period torus

The standard integral lattice gives a genuine quotient covering of the
real coordinate torus. Its lifted endpoints mark the fundamental group
by the source's ordered integral column coordinates. The proved first
Hurewicz equivalence then marks actual integral singular first homology.

Straight period loops fix the sign and order of this marking. Mapping
these loops by the actual triangle torus homeomorphism computes the
actual singular-homology action as the integral dual representation.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.FlatTorus

open FirstHurewicz SpecialPeriods

/-- The standard integral period in the ordered real column coordinates. -/
def periodVector : Lattice →+ RealPlane₄ where
  toFun := Elliptic.realCast
  map_zero' := by ext i; simp [Elliptic.realCast]
  map_add' c d := by ext i; simp [Elliptic.realCast]

@[simp] theorem periodVector_apply (c : Lattice) :
    periodVector c = Elliptic.realCast c := rfl

theorem periodVector_injective : Function.Injective periodVector := by
  intro c d h
  ext i
  have hi : (c i : ℝ) = (d i : ℝ) := congrFun h i
  exact_mod_cast hi

theorem periodVector_mem_standardLattice (c : Lattice) : periodVector c ∈ standardLattice :=
  (Elliptic.standardLattice_mem_iff _).mpr ⟨c, rfl⟩

/-- The integral coordinates map to the actual standard lattice. -/
def periodLatticeMap : Lattice →+ standardLattice :=
  periodVector.codRestrict standardLattice.toAddSubgroup periodVector_mem_standardLattice

@[simp] theorem periodLatticeMap_coe (c : Lattice) :
    (periodLatticeMap c : RealPlane₄) = Elliptic.realCast c := rfl

theorem periodLatticeMap_bijective : Function.Bijective periodLatticeMap := by
  constructor
  · intro c d h
    exact periodVector_injective (congrArg Subtype.val h)
  · intro z
    obtain ⟨c, hc⟩ := (Elliptic.standardLattice_mem_iff z).mp z.property
    exact ⟨c, Subtype.ext hc.symm⟩

/-- The source's ordered four integral columns mark the genuine lattice. -/
def periodLatticeEquiv : Lattice ≃+ standardLattice :=
  AddEquiv.ofBijective periodLatticeMap periodLatticeMap_bijective

def latticeEquiv : standardLattice ≃+ Lattice := periodLatticeEquiv.symm

@[simp] theorem periodLatticeEquiv_coe (c : Lattice) :
    (periodLatticeEquiv c : RealPlane₄) = Elliptic.realCast c := rfl

theorem periodVector_latticeEquiv (z : standardLattice) :
    periodVector (latticeEquiv z) = z :=
  congrArg Subtype.val (periodLatticeEquiv.apply_symm_apply z)

/-- The actual standard-lattice quotient, with its covering topology. -/
theorem quotientCovering :
    IsAddQuotientCoveringMap standardLattice.mkQ standardLattice.toAddSubgroup := by
  apply standardLattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
  change IsDiscrete (standardLattice : Set RealPlane₄)
  let : DiscreteTopology (standardLattice : Set RealPlane₄) := standardLattice_discrete
  exact DiscreteTopology.isDiscrete

/-- The zero lift of the genuine quotient-torus origin. -/
def zeroLift : standardLattice.mkQ ⁻¹' ({0} : Set RealTorus₄) := ⟨0, by simp⟩

/-- The actual covering-monodromy marking of the flat torus fundamental group. -/
def fundamentalGroupEquiv : FundamentalGroup RealTorus₄ 0 ≃* Multiplicative Lattice :=
  ((quotientCovering.fundamentalGroupEquiv zeroLift).trans
    MulOpposite.opMulEquiv.symm).trans latticeEquiv.toMultiplicative

theorem fundamentalGroupEquiv_monodromy (γ : FundamentalGroup RealTorus₄ 0) :
    periodVector (fundamentalGroupEquiv γ).toAdd =
      (quotientCovering.isCoveringMap.monodromy γ zeroLift : RealPlane₄) := by
  have h := quotientCovering.unop_fundamentalGroupToMulOpposite_smul
    (e := zeroLift) (γ := γ)
  change periodVector
    (latticeEquiv (quotientCovering.fundamentalGroupToMulOpposite zeroLift γ).unop.toAdd) = _
  rw [periodVector_latticeEquiv]
  change ((quotientCovering.fundamentalGroupToMulOpposite zeroLift γ).unop.toAdd :
    RealPlane₄) + 0 = _ at h
  simpa only [add_zero] using h

@[simp] theorem mkQ_periodVector (c : Lattice) : standardLattice.mkQ (periodVector c) = 0 :=
  (Submodule.Quotient.mk_eq_zero standardLattice).mpr (periodVector_mem_standardLattice c)

/-- The quotient of the straight segment from zero to the integral real vector. -/
def periodLoop (c : Lattice) : Path (0 : RealTorus₄) 0 :=
  ((Path.segment (0 : RealPlane₄) (periodVector c)).map
    standardLattice.continuous_mkQ).cast (map_zero standardLattice.mkQ).symm
      (mkQ_periodVector c).symm

theorem periodLoop_apply (c : Lattice) (t : unitInterval) :
    periodLoop c t = standardLattice.mkQ ((t : ℝ) • Elliptic.realCast c) := by
  change standardLattice.mkQ (Path.segment (0 : RealPlane₄) (Elliptic.realCast c) t) = _
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add]

/-- The actual lift of the straight quotient loop ends at the indicated period. -/
theorem periodLoop_monodromy (c : Lattice) :
    quotientCovering.isCoveringMap.monodromy (loopQuotient (periodLoop c)) zeroLift =
      ⟨periodVector c, mkQ_periodVector c⟩ := by
  apply quotientCovering.isCoveringMap.monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk (Path.segment (0 : RealPlane₄) (periodVector c)))
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- Lifted endpoints give exactly the prescribed ordered integral coordinates. -/
@[simp] theorem fundamentalGroupEquiv_periodLoop (c : Lattice) :
    fundamentalGroupEquiv (loopQuotient (periodLoop c)) = Multiplicative.ofAdd c := by
  apply Multiplicative.toAdd.injective
  apply periodVector_injective
  rw [fundamentalGroupEquiv_monodromy, periodLoop_monodromy]
  rfl

theorem fundamentalGroupEquiv_symm_apply (c : Lattice) :
    fundamentalGroupEquiv.symm (Multiplicative.ofAdd c) = loopQuotient (periodLoop c) := by
  apply fundamentalGroupEquiv.injective
  rw [MulEquiv.apply_symm_apply, fundamentalGroupEquiv_periodLoop]

/-- The source-column marking of Mathlib's actual integral singular first homology. -/
def singularH1Equiv : SingularH1 RealTorus₄ ≃ₗ[ℤ] Lattice :=
  singularH1EquivOfPi1 (0 : RealTorus₄) fundamentalGroupEquiv

@[simp] theorem singularH1Equiv_loopHomologyClass (p : Path (0 : RealTorus₄) 0) :
    singularH1Equiv (loopHomologyClass p) = (fundamentalGroupEquiv (loopQuotient p)).toAdd :=
  singularH1EquivOfPi1_loopHomologyClass (0 : RealTorus₄) fundamentalGroupEquiv p

@[simp] theorem singularH1Equiv_periodLoop (c : Lattice) :
    singularH1Equiv (loopHomologyClass (periodLoop c)) = c := by
  rw [singularH1Equiv_loopHomologyClass, fundamentalGroupEquiv_periodLoop]
  rfl

/-- Every marked homology class is represented by its actual straight period loop. -/
@[simp] theorem singularH1Equiv_symm_apply (c : Lattice) :
    singularH1Equiv.symm c = loopHomologyClass (periodLoop c) := by
  apply singularH1Equiv.injective
  rw [LinearEquiv.apply_symm_apply, singularH1Equiv_periodLoop]

/-- The actual triangle torus homeomorphism maps a straight integral loop
to the straight loop of the integral dual matrix applied to its coordinate. -/
theorem periodLoop_map_triangle (g : TriangleGroup) (c : Lattice) :
    (periodLoop c).map (triangleTorusHomeomorph g).continuous =
      (periodLoop ((triangleDualRepresentation g : LatticeMatrix) *ᵥ c)).cast
        (triangleTorusHomeomorph_zero g) (triangleTorusHomeomorph_zero g) := by
  ext t
  change triangleTorusHomeomorph g (periodLoop c t) =
    periodLoop ((triangleDualRepresentation g : LatticeMatrix) *ᵥ c) t
  rw [periodLoop_apply, triangleTorusHomeomorph_mkQ, periodLoop_apply,
    map_smul, triangleRealEquiv_realCast]

/-- Naturality of the actual singular chain functor computes the map on
the genuine homology class of each straight integral loop. -/
theorem inducedHomology_periodLoop_triangle (g : TriangleGroup) (c : Lattice) :
    inducedHomology (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄))
      (loopHomologyClass (periodLoop c)) =
        loopHomologyClass (periodLoop ((triangleDualRepresentation g : LatticeMatrix) *ᵥ c)) := by
  rw [inducedHomology_loopHomologyClass, periodLoop_map_triangle]
  rfl

/-- The actual induced map on integral singular first homology is the
source's dual integral representation in the proved column marking. -/
theorem singularH1Equiv_inducedHomology_triangle (g : TriangleGroup)
    (a : SingularH1 RealTorus₄) :
    singularH1Equiv
      (inducedHomology (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) a) =
        (triangleDualRepresentation g : LatticeMatrix) *ᵥ singularH1Equiv a := by
  obtain ⟨c, rfl⟩ := singularH1Equiv.symm.surjective a
  rw [singularH1Equiv_symm_apply, inducedHomology_periodLoop_triangle,
    singularH1Equiv_periodLoop, singularH1Equiv_periodLoop]

/-- The same actual singular-homology computation as equality of integral
linear maps after conjugating by the geometrically determined marking. -/
theorem singularH1_triangle_conjugate (g : TriangleGroup) :
    singularH1Equiv.toLinearMap.comp
      ((inducedHomology (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄))).comp
        singularH1Equiv.symm.toLinearMap) =
      Matrix.toLin' (triangleDualRepresentation g : LatticeMatrix) := by
  apply LinearMap.ext
  intro c
  change singularH1Equiv
    (inducedHomology (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄))
      (singularH1Equiv.symm c)) = _
  rw [singularH1Equiv_inducedHomology_triangle, LinearEquiv.apply_symm_apply]
  rfl

theorem singularH1_free : Module.Free ℤ (SingularH1 RealTorus₄) :=
  Module.Free.of_equiv singularH1Equiv.symm

theorem singularH1_finite : Module.Finite ℤ (SingularH1 RealTorus₄) :=
  Module.Finite.of_surjective singularH1Equiv.symm.toLinearMap singularH1Equiv.symm.surjective

theorem singularH1_finrank : Module.finrank ℤ (SingularH1 RealTorus₄) = 4 := by
  rw [singularH1Equiv.finrank_eq]
  simp [Lattice]

end Wikipedia.HopfProblem.TrianglePeriodFamily.FlatTorus
