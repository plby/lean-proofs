import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSplitting

/-!
# Surjectivity of degreewise integral cohomology evaluation

Only the image of the outgoing chain differential needs to be
projective.  A homology functional pulls back to the genuine cycles;
extending across their split inclusion gives a literal closed cochain.
No projectivity hypothesis is placed on any homology group.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation

open SingularMayerVietoris.ModuleHomology

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- Extend a homology functional to a cocycle in the original dual complex. -/
theorem exists_cocycle_of_functional [Module.Projective ℤ (OutgoingImage K n)]
    (φ : K.homology n →ₗ[ℤ] ℤ) :
    ∃ c : Cocycle (dualComplex K) n,
      ∀ z : Cycle K n, c.val z.val = φ (cycleClass K n z) := by
  obtain ⟨ψ, hψ⟩ := exists_extension_from_cycles K n (φ.comp (cycleClass K n))
  have hc : ((dualComplex K).d n (n + 1)).hom ψ = 0 := by
    ext b
    change ψ ((K.d (n + 1) n).hom b) = 0
    have hb := hψ (boundaryCycle K n b)
    simpa only [boundaryCycle_val, LinearMap.comp_apply, cycleClass_boundary, map_zero] using hb
  exact ⟨mkCocycle (dualComplex K) n ψ hc, hψ⟩

/-- The canonical evaluation map is onto if the single outgoing image is projective. -/
theorem cohomologyEvaluation_surjective_of_outgoing_projective
    [Module.Projective ℤ (OutgoingImage K n)] :
    Function.Surjective (cohomologyEvaluation K n) := by
  intro φ
  obtain ⟨c, hc⟩ := exists_cocycle_of_functional K n φ
  refine ⟨cocycleClass (dualComplex K) n c, ?_⟩
  ext a
  obtain ⟨z, rfl⟩ := cycleClass_surjective K n a
  rw [cohomologyEvaluation_cocycle_cycle]
  exact hc z

/-- There is no outgoing image in degree zero. -/
theorem outgoingImage_zero_eq_bot :
    OutgoingImage K 0 = ⊥ := by
  have hd : K.d 0 ((ComplexShape.down ℕ).next 0) = 0 := K.shape _ _ (by simp)
  change LinearMap.range (K.d 0 ((ComplexShape.down ℕ).next 0)).hom = ⊥
  rw [hd, ModuleCat.hom_zero, LinearMap.range_zero]

/-- Degree-zero surjectivity needs no chain or homology projectivity hypothesis. -/
theorem cohomologyEvaluation_zero_surjective :
    Function.Surjective (cohomologyEvaluation K 0) := by
  have : Subsingleton (OutgoingImage K 0) := by
    rw [outgoingImage_zero_eq_bot K]
    infer_instance
  exact cohomologyEvaluation_surjective_of_outgoing_projective K 0

end Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation
