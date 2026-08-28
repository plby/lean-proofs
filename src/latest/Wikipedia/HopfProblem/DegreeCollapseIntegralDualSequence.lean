import Wikipedia.HopfProblem.SingularCohomologyFreeComplex
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Integral duality for actual degreewise split chain sequences

The integral dual need not preserve arbitrary short exact sequences.
Projectivity of each actual quotient chain module supplies a genuine
degreewise splitting. Its opposite dual splitting proves exactness of
the original reversed integral cochain row.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralDualSequence

open SingularCohomologyFree

def sequence (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (dualMap S.g) (dualMap S.f)
    (by rw [← dualMap_comp, S.zero, dualMap_zero])

theorem sequence_degree_shortExact (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ))
    (hS : S.ShortExact) (n : ℕ) [Projective (S.X₃.X n)] :
    ((sequence S).map
      (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.up ℕ) n)).ShortExact := by
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  let : Projective
      ((S.map (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)).X₃) :=
    inferInstanceAs (Projective (S.X₃.X n))
  exact ((hd.splittingOfProjective.op).map integralDualFunctor).shortExact

theorem sequence_shortExact (S : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ))
    (hS : S.ShortExact) [∀ n, Projective (S.X₃.X n)] : (sequence S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact (sequence S)
    (fun n => sequence_degree_shortExact S hS n)

/-- Actual chain-row morphisms induce original precomposition on every reversed term. -/
def sequenceMap {S T : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)} (φ : S ⟶ T) :
    sequence T ⟶ sequence S where
  τ₁ := dualMap φ.τ₃
  τ₂ := dualMap φ.τ₂
  τ₃ := dualMap φ.τ₁
  comm₁₂ := by
    change dualMap φ.τ₃ ≫ dualMap S.g = dualMap T.g ≫ dualMap φ.τ₂
    rw [← dualMap_comp, ← dualMap_comp]
    exact congrArg dualMap φ.comm₂₃.symm
  comm₂₃ := by
    change dualMap φ.τ₂ ≫ dualMap S.f = dualMap T.f ≫ dualMap φ.τ₁
    rw [← dualMap_comp, ← dualMap_comp]
    exact congrArg dualMap φ.comm₁₂.symm

end Wikipedia.HopfProblem.DegreeCollapse.IntegralDualSequence
