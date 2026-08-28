import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenCapOriginal
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSingular

/-!
# Complementary integral cap evaluation in dimension seven

The original cap maps in degrees three and four are transposes under
ordinary integral evaluation. Both use the same original fundamental
cycle, and the signed cup-one identity proves their equality there.
Every integral functional on actual third homology consequently has a
dual fourth-homology class. No finiteness of third homology or vanishing
of fourth homology is assumed.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenDuality

open FirstHurewicz SingularCohomologyFree SingularMayerVietoris SingularCohomologyCup
open NoExoticSixSphere IntegralSevenLinking

variable {X : Type} [TopologicalSpace X]

def capSevenFourCycle (α : Cocycle (singularCochainComplex X) 3)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    ModuleHomology.Cycle (singularComplex X) 4 :=
  ModuleHomology.mkCycle (singularComplex X) 4
    (IntegralCap.capInDegree (p := 3) (q := 4) rfl α.val Ω.val)
    (IntegralCap.cap_is_cycle_of_boundary_killed 3 3 α.val
      (cocycle_condition (singularCochainComplex X) 3 α) Ω.val
      (by rw [ModuleHomology.cycle_condition, map_zero]))

theorem capSevenFourCycle_val (α : Cocycle (singularCochainComplex X) 3)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    (capSevenFourCycle α Ω).val =
      IntegralCap.capInDegree (p := 3) (q := 4) rfl α.val Ω.val := rfl

theorem cupOne44_zero_right (α : Cochain X 4) :
    IntegralCupOne.cupOne44 α (0 : Cochain X 4) = 0 := by
  simpa only [zero_smul] using
    IntegralCupOne.cupOne44_smul_right α (0 : Cochain X 4) (0 : ℤ)

theorem complementary_cup_cycle (α : Cocycle (singularCochainComplex X) 3)
    (β : Cocycle (singularCochainComplex X) 4)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    cup α.val β.val Ω.val = cup β.val α.val Ω.val := by
  have h := IntegralCupOne.cup_commutator_cycle β.val α.val
    (cocycle_condition (singularCochainComplex X) 4 β) Ω
  rw [show coboundary α.val = 0 from
    cocycle_condition (singularCochainComplex X) 3 α,
    cupOne44_zero_right, LinearMap.zero_apply, neg_zero] at h
  exact (sub_eq_zero.mp h).symm

theorem complementary_cap_cycle_evaluation
    (α : Cocycle (singularCochainComplex X) 3)
    (β : Cocycle (singularCochainComplex X) 4)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    singularEvaluation X 4 (cocycleClass (singularCochainComplex X) 4 β)
        (ModuleHomology.cycleClass (singularComplex X) 4 (capSevenFourCycle α Ω)) =
      singularEvaluation X 3 (cocycleClass (singularCochainComplex X) 3 α)
        (ModuleHomology.cycleClass (singularComplex X) 3 (capSevenCycle β Ω)) := by
  rw [singularEvaluation_cocycle_cycle, singularEvaluation_cocycle_cycle]
  change β.val (IntegralCap.capInDegree (p := 3) (q := 4) rfl α.val Ω.val) =
    α.val (IntegralCap.capInDegree (p := 4) (q := 3) rfl β.val Ω.val)
  rw [IntegralCap.evaluate_cap, IntegralCap.evaluate_cap]
  exact complementary_cup_cycle α β Ω

theorem relative_capSevenFourCycle (U : Set X) (α : RelativeIntegralCap.Cocycle U 3)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    RelativeIntegralCap.capCycles U 3 4 α.val (RelativeIntegralCap.cocycle_coboundary_zero U 3 α)
      (ModuleHomology.mapCycles (RelativeSingularHomology.projection U) 7 Ω) =
    capSevenFourCycle (mapCocycles (RelativeIntegralCap.toAbsoluteMap U) 3 α) Ω := by
  apply Subtype.ext
  rw [RelativeIntegralCap.capCycles_val, ModuleHomology.mapCycles_val,
    capSevenFourCycle_val, mapCocycles_val]
  change RelativeIntegralCap.capInDegree U (p := 3) (q := 4) rfl α.val
      (RelativeSingularHomology.quotientMap U 7 Ω.val) =
    IntegralCap.capInDegree (p := 3) (q := 4) rfl
      (RelativeIntegralCap.toAbsolute U 3 α.val) Ω.val
  exact RelativeIntegralCap.capInDegree_quotientMap (X := X) U
    (p := 3) (q := 4) (n := 7) rfl α.val Ω.val

theorem relative_capProduct_three_projected (U : Set X)
    (α : RelativeIntegralCap.Cocycle U 3)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    RelativeIntegralCap.capProductInDegree U (p := 3) (q := 4) rfl
      (cocycleClass (RelativeIntegralCap.cochainComplex U) 3 α)
      ((HomologicalComplex.homologyMap (RelativeSingularHomology.projection U) 7).hom
        (ModuleHomology.cycleClass (singularComplex X) 7 Ω)) =
    ModuleHomology.cycleClass (singularComplex X) 4
      (capSevenFourCycle (mapCocycles (RelativeIntegralCap.toAbsoluteMap U) 3 α) Ω) := by
  change RelativeIntegralCap.capProduct U 3 4 _ _ = _
  rw [ModuleHomology.homologyMap_cycleClass, RelativeIntegralCap.capProduct_cocycle_cycle,
    relative_capSevenFourCycle]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 7)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

theorem absoluteDualityMap_three_projected_cocycle
    (α : RelativeIntegralCap.Cocycle (Set.univ : Set M)ᶜ 3)
    (Ω : ModuleHomology.Cycle (singularComplex M) 7)
    (hΩ : ModuleHomology.cycleClass (singularComplex M) 7 Ω =
      IntegralManifoldFundamentalClass.fundamentalClass (E := E) 4 M) :
    IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 3 4 rfl
      (cocycleClass (singularCochainComplex M) 3
        (mapCocycles (RelativeIntegralCap.toAbsoluteMap (Set.univ : Set M)ᶜ) 3 α)) =
    ModuleHomology.cycleClass (singularComplex M) 4
      (capSevenFourCycle
        (mapCocycles (RelativeIntegralCap.toAbsoluteMap (Set.univ : Set M)ᶜ) 3 α) Ω) := by
  rw [← homologyMap_cocycleClass]
  change IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 3 4 rfl
    (IntegralSupportedCohomology.toAbsolute Set.univ 3
      (cocycleClass (RelativeIntegralCap.cochainComplex (Set.univ : Set M)ᶜ) 3 α)) = _
  refine (IntegralCompactSupportCap.absoluteDualityMap_forget (E := E) 4 M 3 4 rfl ⊤
    (cocycleClass (RelativeIntegralCap.cochainComplex (Set.univ : Set M)ᶜ) 3 α)).trans ?_
  change RelativeIntegralCap.capProductInDegree (Set.univ : Set M)ᶜ (p := 3) (q := 4) rfl _
    (SupportedRelativeHomology.fromAbsolute (ModuleCat.of ℤ ℤ) Set.univ 7
      (IntegralManifoldFundamentalClass.fundamentalClass (E := E) 4 M)) = _
  rw [← hΩ]
  exact relative_capProduct_three_projected (Set.univ : Set M)ᶜ α Ω

theorem exists_absoluteDualityMap_three_cycle (a : SingularCohomology M 3)
    (Ω : ModuleHomology.Cycle (singularComplex M) 7)
    (hΩ : ModuleHomology.cycleClass (singularComplex M) 7 Ω =
      IntegralManifoldFundamentalClass.fundamentalClass (E := E) 4 M) :
    ∃ α : Cocycle (singularCochainComplex M) 3,
      cocycleClass (singularCochainComplex M) 3 α = a ∧
      IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 3 4 rfl a =
        ModuleHomology.cycleClass (singularComplex M) 4 (capSevenFourCycle α Ω) := by
  obtain ⟨γ, hγ⟩ := cocycleClass_surjective
    (RelativeIntegralCap.cochainComplex (Set.univ : Set M)ᶜ) 3
    ((IntegralSupportedCohomology.absoluteEquiv (X := M) 3).symm a)
  let α := mapCocycles (RelativeIntegralCap.toAbsoluteMap (Set.univ : Set M)ᶜ) 3 γ
  have hα : cocycleClass (singularCochainComplex M) 3 α = a := by
    change cocycleClass (singularCochainComplex M) 3
      (mapCocycles (RelativeIntegralCap.toAbsoluteMap (Set.univ : Set M)ᶜ) 3 γ) = a
    rw [← homologyMap_cocycleClass, hγ]
    exact (IntegralSupportedCohomology.absoluteEquiv (X := M) 3).apply_symm_apply a
  refine ⟨α, hα, ?_⟩
  rw [← hα]
  exact absoluteDualityMap_three_projected_cocycle (E := E) M γ Ω hΩ

theorem absoluteDualityMap_evaluation_transpose
    (a : SingularCohomology M 3) (b : SingularCohomology M 4) :
    singularEvaluation M 4 b
        (IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 3 4 rfl a) =
      singularEvaluation M 3 a
        (IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 4 3 rfl b) := by
  obtain ⟨Ω, hΩ⟩ := IntegralManifoldFundamentalClass.exists_fundamental_cycle (E := E) 4 M
  obtain ⟨α, hα, hcα⟩ := exists_absoluteDualityMap_three_cycle (E := E) M a Ω hΩ
  obtain ⟨β, hβ, hcβ⟩ := exists_absoluteDualityMap_cycle (E := E) M b Ω hΩ
  rw [hcα, hcβ, ← hα, ← hβ]
  exact complementary_cap_cycle_evaluation α β Ω

theorem exists_dual_evaluation (σ : SingularHomology M 3 →ₗ[ℤ] ℤ) :
    ∃ z : SingularHomology M 4, ∀ b : SingularCohomology M 4,
      singularEvaluation M 4 b z =
        σ (IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 4 3 rfl b) := by
  obtain ⟨a, ha⟩ := LocalEvaluation.singularEvaluation_surjective M 3 σ
  refine ⟨IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 3 4 rfl a, ?_⟩
  intro b
  rw [absoluteDualityMap_evaluation_transpose, ha]

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenDuality
