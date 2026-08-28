import Wikipedia.NoExoticSixSphere.RelativeIntegralChainsFree
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSingular
import Mathlib.GroupTheory.OrderOfElement

/-!
# Integral relative third cohomology vanishes for the required filling data

Use the genuine relative singular-chain complex and its constructed free
chain modules. Vanishing of H2 and finite H3 give zero integral H3-dual;
the proved local universal-coefficient evaluation is injective. The pair
sequence supplies the relative hypotheses from the actual ambient and
boundary groups. No Poincare--Lefschetz duality is assumed or concluded.
-/

noncomputable section

open Function CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCohomology

open SingularMayerVietoris SingularCohomologyFree
open NoExoticSixSphere.RelativeSingularHomology

theorem finite_integral_dual_subsingleton {H : Type*} [AddCommGroup H] [Module ℤ H] [Finite H] :
    Subsingleton (H →ₗ[ℤ] ℤ) := by
  have hz (f : H →ₗ[ℤ] ℤ) (x : H) : f x = 0 := by
    have hx : Nat.card H • x = 0 := card_nsmul_eq_zero'
    have h := congrArg f hx
    rw [map_nsmul, map_zero] at h
    have hn : (Nat.card H : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr Nat.card_pos.ne'
    exact (mul_eq_zero.mp (show (Nat.card H : ℤ) * f x = 0 by
      simpa only [nsmul_eq_mul] using h)).resolve_left hn
  exact ⟨fun f g ↦ LinearMap.ext (fun x ↦ (hz f x).trans (hz g x).symm)⟩

theorem cohomology_succ_subsingleton (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    [∀ k, Module.Free ℤ (K.X k)] [Subsingleton (K.homology n)] [Finite (K.homology (n + 1))] :
    Subsingleton (Cohomology K (n + 1)) := by
  let : Module.Free ℤ (K.homology n) := Module.Free.of_subsingleton ℤ _
  let : Subsingleton (K.homology (n + 1) →ₗ[ℤ] ℤ) := finite_integral_dual_subsingleton
  exact (LocalEvaluation.cohomologyEvaluation_succ_injective K n).subsingleton

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem toRelative_surjective (n : ℕ) [Subsingleton (SingularHomology U n)] :
    Surjective (toRelative U (n + 1)) := by
  intro c
  have hc : c ∈ LinearMap.ker (connecting U n) := Subsingleton.elim _ _
  rw [← exact_at_relative] at hc
  exact hc

theorem relative_cohomology_succ_subsingleton (n : ℕ)
    [Subsingleton (Homology U n)] [Finite (Homology U (n + 1))] :
    Subsingleton (Cohomology (complex U) (n + 1)) := by
  let (k : ℕ) : Module.Free ℤ ((complex U).X k) := chains_free U k
  exact cohomology_succ_subsingleton (complex U) n

/-- Only the two stated boundary degrees are needed for this integral vanishing. -/
theorem relative_third_cohomology_subsingleton
    [Subsingleton (SingularHomology U 1)] [Subsingleton (SingularHomology U 2)]
    [Subsingleton (SingularHomology X 2)] [Finite (SingularHomology X 3)] :
    Subsingleton (Cohomology (complex U) 3) := by
  let : Subsingleton (Homology U 2) := (toRelative_surjective U 1).subsingleton
  let : Finite (Homology U 3) := Finite.of_surjective _ (toRelative_surjective U 2)
  exact relative_cohomology_succ_subsingleton U 2

end Wikipedia.HopfProblem.DegreeCollapse.RelativeIntegralCohomology
