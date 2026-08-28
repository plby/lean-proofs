import Wikipedia.NoExoticSixSphere.ModTwoCohomologyEvaluation
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSplitting
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSurjective

/-!
# Extending actual homology functionals to mod-two cocycles

Projectivity of the outgoing differential image splits the original
cycle inclusion. Composing that retraction with a homology functional
constructs an actual closed cochain with the specified evaluations.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoCohomologyEvaluation

open SingularCohomologyFree.LocalEvaluation

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- A functional on original homology extends to an actual mod-two cocycle. -/
theorem exists_cocycle_of_functional [Module.Projective ℤ (OutgoingImage K n)]
    (φ : K.homology n →ₗ[ℤ] ZMod 2) :
    ∃ α : Cocycle K n, ∀ z : ModuleHomology.Cycle K n,
      cochainValue K n α z.val = φ (ModuleHomology.cycleClass K n z) := by
  obtain ⟨r, hr⟩ := exists_cycle_retraction K n
  let ψ := φ.comp ((ModuleHomology.cycleClass K n).comp r)
  have hψ : ((ModTwoDualComplex.complex K).d n (n + 1)).hom ψ.toAddMonoidHom = 0 := by
    apply AddMonoidHom.ext
    intro b
    change φ (ModuleHomology.cycleClass K n (r ((K.d (n + 1) n).hom b))) = 0
    have hb := hr (ModuleHomology.boundaryCycle K n b)
    rw [ModuleHomology.boundaryCycle_val] at hb
    rw [hb, ModuleHomology.cycleClass_boundary, map_zero]
  refine ⟨SingularCohomologyFree.mkCocycle (ModTwoDualComplex.complex K) n
    ψ.toAddMonoidHom hψ, ?_⟩
  intro z
  exact congrArg (fun w => φ (ModuleHomology.cycleClass K n w)) (hr z)

/-- Original evaluation is surjective when this outgoing boundary image is projective. -/
theorem evaluation_surjective_of_outgoing_projective
    [Module.Projective ℤ (OutgoingImage K n)] : Function.Surjective (evaluation K n) := by
  intro φ
  obtain ⟨α, hα⟩ := exists_cocycle_of_functional K n φ
  refine ⟨SingularCohomologyFree.cocycleClass (ModTwoDualComplex.complex K) n α, ?_⟩
  apply LinearMap.ext
  intro a
  obtain ⟨z, rfl⟩ := ModuleHomology.cycleClass_surjective K n a
  exact (evaluation_cocycle_cycle K n α z).trans (hα z)

/-- No projectivity hypothesis is needed for surjectivity in degree zero. -/
theorem evaluation_zero_surjective : Function.Surjective (evaluation K 0) := by
  have : Subsingleton (OutgoingImage K 0) := by
    rw [outgoingImage_zero_eq_bot K]
    infer_instance
  exact evaluation_surjective_of_outgoing_projective K 0

end NoExoticSixSphere.ModTwoCohomologyEvaluation
