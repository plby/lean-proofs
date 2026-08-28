import Wikipedia.HopfProblem.PeriodTorusFundamentalGroup
import Wikipedia.HopfProblem.FirstHurewiczEquivalence
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The marked integral singular homology of a period torus

The first Hurewicz theorem converts the actual lattice-cover monodromy
isomorphism into an isomorphism on Mathlib's actual integral singular
homology. A straight loop representing the period `m + Z n` has exactly
the coordinates `(m,n)`, with no change of order or sign.

The first part provides the same conversion for any path-connected
space whose actual fundamental group has been identified with an
additive abelian group.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FirstHurewicz

variable {X : Type} [TopologicalSpace X] (b : X)
variable {A : Type*} [AddCommGroup A] [Module ℤ A]

/-- An actual abelian fundamental-group computation gives the
corresponding identification of its actual abelianization. -/
def abelianPi1EquivOfPi1 (e : FundamentalGroup X b ≃* Multiplicative A) :
    AbelianPi1 X b ≃ₗ[ℤ] A :=
  (e.abelianizationCongr.trans
    (Abelianization.equivOfComm (H := Multiplicative A)).symm).toAdditiveLeft.toIntLinearEquiv

@[simp] theorem abelianPi1EquivOfPi1_of
    (e : FundamentalGroup X b ≃* Multiplicative A) (g : FundamentalGroup X b) :
    abelianPi1EquivOfPi1 b e (Additive.ofMul (Abelianization.of g)) = (e g).toAdd := rfl

variable [PathConnectedSpace X]

/-- Transport a proved abelian fundamental-group computation through the
genuine first Hurewicz isomorphism into actual integral singular homology. -/
def singularH1EquivOfPi1 (e : FundamentalGroup X b ≃* Multiplicative A) :
    SingularH1 X ≃ₗ[ℤ] A :=
  (firstHurewiczEquiv b).symm.trans (abelianPi1EquivOfPi1 b e)

/-- The identification evaluates on the actual Hurewicz class of any
fundamental-group element as the given marked group isomorphism. -/
@[simp] theorem singularH1EquivOfPi1_hurewiczFunction
    (e : FundamentalGroup X b ≃* Multiplicative A) (g : FundamentalGroup X b) :
    singularH1EquivOfPi1 b e (hurewiczFunction b g) = (e g).toAdd := by
  change abelianPi1EquivOfPi1 b e
    ((firstHurewiczEquiv b).symm
      (firstHurewiczEquiv b (Additive.ofMul (Abelianization.of g)))) = _
  rw [LinearEquiv.symm_apply_apply, abelianPi1EquivOfPi1_of]

/-- In particular, a genuine singular loop cycle has its marked
fundamental-group coordinates. -/
@[simp] theorem singularH1EquivOfPi1_loopHomologyClass
    (e : FundamentalGroup X b ≃* Multiplicative A) (p : Path b b) :
    singularH1EquivOfPi1 b e (loopHomologyClass p) = (e (loopQuotient p)).toAdd :=
  singularH1EquivOfPi1_hurewiczFunction b e (loopQuotient p)

@[simp] theorem singularH1EquivOfPi1_symm_apply
    (e : FundamentalGroup X b ≃* Multiplicative A) (a : A) :
    (singularH1EquivOfPi1 b e).symm a =
      hurewiczFunction b (e.symm (Multiplicative.ofAdd a)) := by
  apply (singularH1EquivOfPi1 b e).injective
  rw [LinearEquiv.apply_symm_apply, singularH1EquivOfPi1_hurewiczFunction,
    MulEquiv.apply_symm_apply]
  rfl

end Wikipedia.HopfProblem.FirstHurewicz

namespace Wikipedia.HopfProblem.FullPeriodMatrix

open FirstHurewicz

variable (p : FullPeriodMatrix)

/-- The actual singular first homology of the period torus, in the
ordered integral coordinates of the lattice `(1,Z)`. -/
def singularH1Equiv : SingularH1 p.Torus ≃ₗ[ℤ] IntegerPeriods :=
  singularH1EquivOfPi1 (0 : p.Torus) p.fundamentalGroupEquiv

@[simp] theorem singularH1Equiv_hurewiczFunction (g : FundamentalGroup p.Torus 0) :
    p.singularH1Equiv (hurewiczFunction (0 : p.Torus) g) =
      (p.fundamentalGroupEquiv g).toAdd :=
  singularH1EquivOfPi1_hurewiczFunction (0 : p.Torus) p.fundamentalGroupEquiv g

@[simp] theorem singularH1Equiv_loopHomologyClass (q : Path (0 : p.Torus) 0) :
    p.singularH1Equiv (loopHomologyClass q) =
      (p.fundamentalGroupEquiv (loopQuotient q)).toAdd :=
  singularH1EquivOfPi1_loopHomologyClass (0 : p.Torus) p.fundamentalGroupEquiv q

/-- The singular cycle of the straight marked period loop has exactly
the prescribed pair of integer coordinates. -/
@[simp] theorem singularH1Equiv_periodLoop (c : IntegerPeriods) :
    p.singularH1Equiv (loopHomologyClass (p.periodLoop c)) = c := by
  rw [p.singularH1Equiv_loopHomologyClass]
  change (p.fundamentalGroupEquiv (FundamentalGroup.fromPath ⟦p.periodLoop c⟧)).toAdd = c
  rw [p.fundamentalGroupEquiv_periodLoop]
  rfl

/-- The inverse homology marking consists of actual straight period-loop classes. -/
@[simp] theorem singularH1Equiv_symm_apply (c : IntegerPeriods) :
    p.singularH1Equiv.symm c = loopHomologyClass (p.periodLoop c) := by
  apply p.singularH1Equiv.injective
  rw [LinearEquiv.apply_symm_apply, p.singularH1Equiv_periodLoop]

/-- The actual marked period classes form an integral linear parametrization
of the genuine singular homology group. -/
def periodHomology : IntegerPeriods →ₗ[ℤ] SingularH1 p.Torus :=
  p.singularH1Equiv.symm.toLinearMap

@[simp] theorem periodHomology_apply (c : IntegerPeriods) :
    p.periodHomology c = loopHomologyClass (p.periodLoop c) :=
  p.singularH1Equiv_symm_apply c

theorem periodHomology_bijective : Function.Bijective p.periodHomology :=
  p.singularH1Equiv.symm.bijective

/-- The marked homology class records the endpoint of the actual lifted loop. -/
theorem singularH1Equiv_monodromy (g : FundamentalGroup p.Torus 0) :
    p.periodVector (p.singularH1Equiv (hurewiczFunction (0 : p.Torus) g)) =
      (p.quotientCovering.isCoveringMap.monodromy g p.zeroLift : ComplexPlane₂) := by
  rw [p.singularH1Equiv_hurewiczFunction, p.fundamentalGroupEquiv_monodromy]

theorem singularH1_free : Module.Free ℤ (SingularH1 p.Torus) :=
  Module.Free.of_equiv p.singularH1Equiv.symm

theorem singularH1_finite : Module.Finite ℤ (SingularH1 p.Torus) :=
  Module.Finite.of_surjective p.singularH1Equiv.symm.toLinearMap
    p.singularH1Equiv.symm.surjective

theorem singularH1_finrank : Module.finrank ℤ (SingularH1 p.Torus) = 4 := by
  rw [p.singularH1Equiv.finrank_eq]
  simp [IntegerPeriods]

theorem singularH1_torsionFree : Module.IsTorsionFree ℤ (SingularH1 p.Torus) := by
  let := p.singularH1_free
  infer_instance

end Wikipedia.HopfProblem.FullPeriodMatrix
