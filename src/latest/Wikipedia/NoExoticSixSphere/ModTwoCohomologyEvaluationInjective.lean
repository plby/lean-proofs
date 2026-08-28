import Wikipedia.NoExoticSixSphere.ModTwoCohomologyEvaluationSurjective
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalBoundaries

/-!
# Detecting actual mod-two cohomology classes by evaluation

If a cocycle vanishes on all actual cycles, the preceding boundary
retraction constructs an actual cochain primitive. This proves
injectivity of the previously constructed evaluation map under the
specified local projectivity hypotheses, with no global decomposition.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoCohomologyEvaluation

open SingularCohomologyFree.LocalEvaluation

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- A literal cochain primitive criterion makes original evaluation injective. -/
theorem evaluation_injective_of_factorization
    (hfactor : ∀ φ : K.X n →+ ZMod 2,
      (∀ z : ModuleHomology.Cycle K n, φ z.val = 0) →
        ∃ ψ : K.X (n - 1) →+ ZMod 2, ψ.comp (K.d n (n - 1)).hom.toAddMonoidHom = φ) :
    Function.Injective (evaluation K n) := by
  intro a b hab
  have hz : evaluation K n (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨α, hα⟩ :=
    SingularCohomologyFree.cocycleClass_surjective (ModTwoDualComplex.complex K) n (a - b)
  have hφ (z : ModuleHomology.Cycle K n) : cochainValue K n α z.val = 0 := by
    have he : evaluation K n
        (SingularCohomologyFree.cocycleClass (ModTwoDualComplex.complex K) n α) = 0 := by
      rw [hα]
      exact hz
    exact (evaluation_cocycle_cycle K n α z).symm.trans
      (congrArg (fun f : K.homology n →ₗ[ℤ] ZMod 2 => f (ModuleHomology.cycleClass K n z)) he)
  obtain ⟨ψ, hψ⟩ := hfactor (cochainValue K n α) hφ
  have hzero := (SingularCohomologyFree.cocycleClass_eq_zero_iff
    (ModTwoDualComplex.complex K) n α).mpr ⟨ψ, hψ⟩
  exact sub_eq_zero.mp (hα.symm.trans hzero)

/-- The original preceding boundary retraction supplies the mod-two cochain primitive. -/
theorem exists_primitive_of_vanishing_on_cycles
    [Module.Projective ℤ (OutgoingImage K n)] [Module.Projective ℤ (K.homology n)]
    (φ : K.X (n + 1) →+ ZMod 2)
    (hφ : ∀ z : ModuleHomology.Cycle K (n + 1), φ z.val = 0) :
    ∃ ψ : K.X n →+ ZMod 2, ψ.comp (K.d (n + 1) n).hom.toAddMonoidHom = φ := by
  let φlin := ConstantSheafSingularComparison.addHomToIntLinearMap φ
  have hker : LinearMap.ker (K.d (n + 1) n).hom ≤ LinearMap.ker φlin := by
    intro x hx
    exact hφ (ModuleHomology.mkCycle K (n + 1) x
      (by change (K.d (n + 1) n).hom x = 0; exact hx))
  obtain ⟨ψ₀, hψ₀⟩ := exists_factor_through_range (K.d (n + 1) n).hom φlin hker
  obtain ⟨r, hr⟩ := exists_boundary_retraction K n
  refine ⟨(ψ₀.comp r).toAddMonoidHom, ?_⟩
  apply AddMonoidHom.ext
  intro x
  change ψ₀ (r ((K.d (n + 1) n).hom x)) = φ x
  have hrx := hr ((K.d (n + 1) n).hom.rangeRestrict x)
  change r ((K.d (n + 1) n).hom x) = (K.d (n + 1) n).hom.rangeRestrict x at hrx
  rw [hrx]
  exact LinearMap.congr_fun hψ₀ x

/-- Only projectivity in the immediately preceding degree is needed for injectivity. -/
theorem evaluation_succ_injective_of_outgoing_projective
    [Module.Projective ℤ (OutgoingImage K n)] [Module.Projective ℤ (K.homology n)] :
    Function.Injective (evaluation K (n + 1)) := by
  apply evaluation_injective_of_factorization K (n + 1)
  intro φ hφ
  exact exists_primitive_of_vanishing_on_cycles K n φ hφ

/-- Degree-zero evaluation is injective without any projectivity assumption. -/
theorem evaluation_zero_injective : Function.Injective (evaluation K 0) := by
  apply evaluation_injective_of_factorization K 0
  intro φ hφ
  have hd : K.d 0 0 = 0 := K.shape _ _ (by simp)
  have hφzero : φ = 0 := by
    apply AddMonoidHom.ext
    intro x
    exact hφ (ModuleHomology.mkCycle K 0 x (by rw [hd]; rfl))
  exact ⟨0, by rw [hφzero]; rfl⟩

/-- Actual degree-zero cohomology is identified by its original evaluation map. -/
def evaluationZeroEquiv : Cohomology K 0 ≃ₗ[ℤ] (K.homology 0 →ₗ[ℤ] ZMod 2) :=
  LinearEquiv.ofBijective (evaluation K 0)
    ⟨evaluation_zero_injective K, evaluation_zero_surjective K⟩

theorem evaluationZeroEquiv_toLinearMap : (evaluationZeroEquiv K).toLinearMap = evaluation K 0 :=
  rfl

end NoExoticSixSphere.ModTwoCohomologyEvaluation
