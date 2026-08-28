import Wikipedia.HopfProblem.SphereHomologyCoefficientsChains
import Wikipedia.HopfProblem.SphereHomologyCoefficientsAlgebra
import Mathlib.Algebra.Module.Torsion.Free

/-!
# The genuine coefficient homology sequence and scalar-quotient comparison

The short exact sequence of native singular chain complexes supplies its
actual connecting homomorphism.  If multiplication by `p` is injective on
the preceding integral homology, this connecting map vanishes and native
homology with coefficients `ℤ/p` is canonically the scalar quotient of
the integral group.  No universal-coefficient theorem is assumed.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SphereHomologyCoefficients

open SingularMayerVietoris

attribute [local instance] Submodule.Quotient.module

variable (p : ℕ) (hp : p ≠ 0) (X : Type) [TopologicalSpace X]

include hp

/-- The actual connecting homomorphism of the proved coefficient chain sequence. -/
def bockstein (n : ℕ) : ModHomology p X (n + 1) →ₗ[ℤ] SingularHomology X n :=
  connectingMap (coefficientChainSequence_shortExact p hp X) n

/-- Exactness at the middle integral homology group, in every degree. -/
theorem scalarImage_eq_reduction_ker (n : ℕ) :
    scalarImage p (SingularHomology X n) = LinearMap.ker (reductionHomologyMap p X n) := by
  have h := exact_at_middleHomology (coefficientChainSequence_shortExact p hp X) n
  change LinearMap.range (homologyLinearMap (multiplicationChainMap p X) n) =
    LinearMap.ker (reductionHomologyMap p X n) at h
  rw [multiplicationChainMap_homology] at h
  exact h

/-- The Bockstein image is precisely the `p`-torsion in the preceding integral group. -/
theorem bockstein_range (n : ℕ) :
    LinearMap.range (bockstein p hp X n) =
      LinearMap.ker ((p : ℤ) • (LinearMap.id :
        SingularHomology X n →ₗ[ℤ] SingularHomology X n)) := by
  have h := exact_at_leftHomology (coefficientChainSequence_shortExact p hp X) n
  change LinearMap.range (bockstein p hp X n) =
    LinearMap.ker (homologyLinearMap (multiplicationChainMap p X) n) at h
  rw [multiplicationChainMap_homology] at h
  exact h

/-- Exactness at native homology with finite cyclic coefficients. -/
theorem reductionHomologyMap_range_succ (n : ℕ) :
    LinearMap.range (reductionHomologyMap p X (n + 1)) =
      LinearMap.ker (bockstein p hp X n) :=
  exact_at_rightHomology (coefficientChainSequence_shortExact p hp X) n

/-- Coefficient reduction is always onto actual degree-zero homology. -/
theorem reductionHomologyMap_surjective_zero :
    Function.Surjective (reductionHomologyMap p X 0) :=
  homologyLinearMap_second_zero_surjective (coefficientChainSequence_shortExact p hp X)

/-- The actual connecting map vanishes when its precise torsion target is zero. -/
theorem bockstein_eq_zero_of_injective (n : ℕ)
    (hinj : Function.Injective ((p : ℤ) • (LinearMap.id :
      SingularHomology X n →ₗ[ℤ] SingularHomology X n))) :
    bockstein p hp X n = 0 := by
  apply LinearMap.range_eq_bot.mp
  rw [bockstein_range, LinearMap.ker_eq_bot.mpr hinj]

/-- Torsion-freeness of the preceding integral group kills the actual Bockstein. -/
theorem bockstein_eq_zero (n : ℕ) [Module.IsTorsionFree ℤ (SingularHomology X n)] :
    bockstein p hp X n = 0 := by
  apply bockstein_eq_zero_of_injective
  change Function.Injective (fun a : SingularHomology X n => (p : ℤ) • a)
  intro a b hab
  apply smul_right_injective (SingularHomology X n)
    (show (p : ℤ) ≠ 0 by exact_mod_cast hp)
  exact (int_smul_eq_zsmul (SingularHomology X n).isModule (p : ℤ) a).trans
    (hab.trans (int_smul_eq_zsmul (SingularHomology X n).isModule (p : ℤ) b).symm)

/-- In positive degrees, a torsion-free preceding integral group makes reduction onto. -/
theorem reductionHomologyMap_surjective_succ (n : ℕ)
    [Module.IsTorsionFree ℤ (SingularHomology X n)] :
    Function.Surjective (reductionHomologyMap p X (n + 1)) := by
  apply LinearMap.range_eq_top.mp
  rw [reductionHomologyMap_range_succ p hp X n, bockstein_eq_zero p hp X n,
    LinearMap.ker_zero]

/-- The unified reduction-surjectivity statement; the zero-degree case needs no torsion input. -/
theorem reductionHomologyMap_surjective (n : ℕ)
    [hprev : Module.IsTorsionFree ℤ (SingularHomology X (n - 1))] :
    Function.Surjective (reductionHomologyMap p X n) := by
  cases n with
  | zero => exact reductionHomologyMap_surjective_zero p hp X
  | succ n =>
    let : Module.IsTorsionFree ℤ (SingularHomology X n) :=
      Eq.mp (congrArg (fun k : ℕ => Module.IsTorsionFree ℤ (SingularHomology X k))
        (Nat.add_sub_cancel n 1)) hprev
    exact reductionHomologyMap_surjective_succ p hp X n

/-- The actual coefficient-change comparison, constructed from the proved native exact sequence. -/
def modHomologyQuotientEquiv (n : ℕ)
    [Module.IsTorsionFree ℤ (SingularHomology X (n - 1))] :
    (SingularHomology X n ⧸ scalarImage p (SingularHomology X n)) ≃ₗ[ℤ]
      ModHomology p X n := by
  let e₁ := Submodule.quotEquivOfEq _ _ (scalarImage_eq_reduction_ker p hp X n)
  let e₂ := (reductionHomologyMap p X n).quotKerEquivOfSurjective
    (reductionHomologyMap_surjective p hp X n)
  let e₃ := e₁.trans e₂
  let ea : (SingularHomology X n ⧸ scalarImage p (SingularHomology X n)) ≃+
      ModHomology p X n :=
    { toEquiv := e₃.toEquiv
      map_add' := fun x y => e₃.map_add x y }
  exact ea.toIntLinearEquiv

@[simp] theorem modHomologyQuotientEquiv_mk (n : ℕ)
    [Module.IsTorsionFree ℤ (SingularHomology X (n - 1))]
    (a : SingularHomology X n) :
    modHomologyQuotientEquiv p hp X n (Submodule.Quotient.mk a) =
      reductionHomologyMap p X n a := rfl

@[simp] theorem modHomologyQuotientEquiv_symm_reduction (n : ℕ)
    [Module.IsTorsionFree ℤ (SingularHomology X (n - 1))]
    (a : SingularHomology X n) :
    (modHomologyQuotientEquiv p hp X n).symm (reductionHomologyMap p X n a) =
      Submodule.Quotient.mk a := by
  apply (modHomologyQuotientEquiv p hp X n).injective
  rw [LinearEquiv.apply_symm_apply, modHomologyQuotientEquiv_mk]

/-- An actual infinite cyclic integral marking gives the corresponding coefficient marking. -/
def modHomologyEquivZMod (n : ℕ)
    [Module.IsTorsionFree ℤ (SingularHomology X (n - 1))]
    (e : SingularHomology X n ≃ₗ[ℤ] ℤ) : ModHomology p X n ≃ₗ[ℤ] ZMod p :=
  (modHomologyQuotientEquiv p hp X n).symm.trans (scalarQuotientEquivZMod p e)

@[simp] theorem modHomologyEquivZMod_reduction (n : ℕ)
    [Module.IsTorsionFree ℤ (SingularHomology X (n - 1))]
    (e : SingularHomology X n ≃ₗ[ℤ] ℤ) (a : SingularHomology X n) :
    modHomologyEquivZMod p hp X n e (reductionHomologyMap p X n a) = (e a : ZMod p) := by
  rw [modHomologyEquivZMod, LinearEquiv.trans_apply,
    modHomologyQuotientEquiv_symm_reduction, scalarQuotientEquivZMod_mk]

/-- Vanishing of an integral group transfers when the preceding group is torsion-free. -/
theorem modHomology_subsingleton (n : ℕ)
    [Module.IsTorsionFree ℤ (SingularHomology X (n - 1))]
    [Subsingleton (SingularHomology X n)] : Subsingleton (ModHomology p X n) :=
  (reductionHomologyMap_surjective p hp X n).subsingleton

end Wikipedia.HopfProblem.SphereHomologyCoefficients
