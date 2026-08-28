import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalBoundaries

/-!
# Injectivity of the actual evaluation map from one preceding degree

The kernel is computed on literal cocycle representatives.  If a
cocycle evaluates to zero on homology, it vanishes on all cycles; the
preceding-degree boundary retraction then constructs its actual
coboundary primitive.  No other homology group is assumed projective.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation

open SingularMayerVietoris.ModuleHomology

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- A literal coboundary criterion gives injectivity of the already defined evaluation map. -/
theorem cohomologyEvaluation_injective_of_boundary_factorization
    (hfactor : ∀ φ : K.X n →ₗ[ℤ] ℤ,
      (∀ z : Cycle K n, φ z.val = 0) →
        ∃ ψ : K.X (n - 1) →ₗ[ℤ] ℤ, ψ.comp (K.d n (n - 1)).hom = φ) :
    Function.Injective (cohomologyEvaluation K n) := by
  intro a b hab
  have hz : cohomologyEvaluation K n (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := cocycleClass_surjective (dualComplex K) n (a - b)
  have hφ (z : Cycle K n) : c.val z.val = 0 := by
    have h := congrArg (fun f : K.homology n →ₗ[ℤ] ℤ => f (cycleClass K n z)) hz
    rw [← hc, cohomologyEvaluation_cocycle_cycle] at h
    exact h
  obtain ⟨ψ, hψ⟩ := hfactor c.val hφ
  have hc₀ : cocycleClass (dualComplex K) n c = 0 :=
    (cocycleClass_eq_zero_iff (dualComplex K) n c).mpr ⟨ψ, hψ⟩
  exact sub_eq_zero.mp (hc.symm.trans hc₀)

/-- In positive degree, only the immediately preceding homology and
its outgoing boundary image enter the injectivity proof. -/
theorem cohomologyEvaluation_succ_injective_of_outgoing_projective
    [Module.Projective ℤ (OutgoingImage K n)] [Module.Projective ℤ (K.homology n)] :
    Function.Injective (cohomologyEvaluation K (n + 1)) := by
  apply cohomologyEvaluation_injective_of_boundary_factorization K (n + 1)
  intro φ hφ
  change ∃ ψ : K.X n →ₗ[ℤ] ℤ, ψ.comp (K.d (n + 1) n).hom = φ
  exact exists_coboundary_of_vanishing_on_cycles K n φ hφ

/-- Degree-zero evaluation is injective without any projectivity assumption. -/
theorem cohomologyEvaluation_zero_injective :
    Function.Injective (cohomologyEvaluation K 0) := by
  apply cohomologyEvaluation_injective_of_boundary_factorization K 0
  intro φ hφ
  have hd : K.d 0 0 = 0 := K.shape _ _ (by simp)
  have hφ₀ : φ = 0 := by
    ext x
    exact hφ (mkCycle K 0 x (by rw [hd]; rfl))
  exact ⟨0, by rw [hφ₀]; rfl⟩

end Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation
