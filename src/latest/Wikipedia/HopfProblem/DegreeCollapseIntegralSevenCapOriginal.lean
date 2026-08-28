import Wikipedia.HopfProblem.DegreeCollapseIntegralSevenCapCycles
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportCap

/-!
# The original absolute cap map on actual fundamental cycles

Whole-support cochains lift every original absolute class. Projection
of the original fundamental cycle computes the original relative cap,
whose value is the literal absolute capped cycle used for torsion symmetry.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenLinking

open FirstHurewicz SingularCohomologyFree SingularMayerVietoris
open NoExoticSixSphere

variable {X : Type} [TopologicalSpace X]

theorem relative_capSevenCycle (U : Set X) (α : RelativeIntegralCap.Cocycle U 4)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    RelativeIntegralCap.capCycles U 4 3 α.val (RelativeIntegralCap.cocycle_coboundary_zero U 4 α)
      (ModuleHomology.mapCycles (RelativeSingularHomology.projection U) 7 Ω) =
    capSevenCycle (mapCocycles (RelativeIntegralCap.toAbsoluteMap U) 4 α) Ω := by
  apply Subtype.ext
  rw [RelativeIntegralCap.capCycles_val, ModuleHomology.mapCycles_val,
    capSevenCycle_val, mapCocycles_val]
  change RelativeIntegralCap.capInDegree U (p := 4) (q := 3) rfl α.val
      (RelativeSingularHomology.quotientMap U 7 Ω.val) =
    IntegralCap.capInDegree (p := 4) (q := 3) rfl
      (RelativeIntegralCap.toAbsolute U 4 α.val) Ω.val
  exact RelativeIntegralCap.capInDegree_quotientMap (X := X) U
    (p := 4) (q := 3) (n := 7) rfl α.val Ω.val

theorem relative_capProduct_projected (U : Set X) (α : RelativeIntegralCap.Cocycle U 4)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    RelativeIntegralCap.capProductInDegree U (p := 4) (q := 3) rfl
      (cocycleClass (RelativeIntegralCap.cochainComplex U) 4 α)
      ((HomologicalComplex.homologyMap (RelativeSingularHomology.projection U) 7).hom
        (ModuleHomology.cycleClass (singularComplex X) 7 Ω)) =
    ModuleHomology.cycleClass (singularComplex X) 3
      (capSevenCycle (mapCocycles (RelativeIntegralCap.toAbsoluteMap U) 4 α) Ω) := by
  change RelativeIntegralCap.capProduct U 4 3 _ _ = _
  rw [ModuleHomology.homologyMap_cycleClass, RelativeIntegralCap.capProduct_cocycle_cycle,
    relative_capSevenCycle]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 7)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [SimplyConnectedSpace M]

theorem absoluteDualityMap_projected_cocycle
    (α : RelativeIntegralCap.Cocycle (Set.univ : Set M)ᶜ 4)
    (Ω : ModuleHomology.Cycle (singularComplex M) 7)
    (hΩ : ModuleHomology.cycleClass (singularComplex M) 7 Ω =
      IntegralManifoldFundamentalClass.fundamentalClass (E := E) 4 M) :
    IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 4 3 rfl
      (cocycleClass (singularCochainComplex M) 4
        (mapCocycles (RelativeIntegralCap.toAbsoluteMap (Set.univ : Set M)ᶜ) 4 α)) =
    ModuleHomology.cycleClass (singularComplex M) 3
      (capSevenCycle
        (mapCocycles (RelativeIntegralCap.toAbsoluteMap (Set.univ : Set M)ᶜ) 4 α) Ω) := by
  rw [← homologyMap_cocycleClass]
  change IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 4 3 rfl
    (IntegralSupportedCohomology.toAbsolute Set.univ 4
      (cocycleClass (RelativeIntegralCap.cochainComplex (Set.univ : Set M)ᶜ) 4 α)) = _
  refine (IntegralCompactSupportCap.absoluteDualityMap_forget (E := E) 4 M 4 3 rfl ⊤
    (cocycleClass (RelativeIntegralCap.cochainComplex (Set.univ : Set M)ᶜ) 4 α)).trans ?_
  change RelativeIntegralCap.capProductInDegree (Set.univ : Set M)ᶜ (p := 4) (q := 3) rfl _
    (SupportedRelativeHomology.fromAbsolute (ModuleCat.of ℤ ℤ) Set.univ 7
      (IntegralManifoldFundamentalClass.fundamentalClass (E := E) 4 M)) = _
  rw [← hΩ]
  exact relative_capProduct_projected (Set.univ : Set M)ᶜ α Ω

theorem exists_absoluteDualityMap_cycle (a : SingularCohomology M 4)
    (Ω : ModuleHomology.Cycle (singularComplex M) 7)
    (hΩ : ModuleHomology.cycleClass (singularComplex M) 7 Ω =
      IntegralManifoldFundamentalClass.fundamentalClass (E := E) 4 M) :
    ∃ α : Cocycle (singularCochainComplex M) 4,
      cocycleClass (singularCochainComplex M) 4 α = a ∧
      IntegralCompactSupportCap.absoluteDualityMap (E := E) 4 M 4 3 rfl a =
        ModuleHomology.cycleClass (singularComplex M) 3 (capSevenCycle α Ω) := by
  obtain ⟨γ, hγ⟩ := cocycleClass_surjective
    (RelativeIntegralCap.cochainComplex (Set.univ : Set M)ᶜ) 4
    ((IntegralSupportedCohomology.absoluteEquiv (X := M) 4).symm a)
  let α := mapCocycles (RelativeIntegralCap.toAbsoluteMap (Set.univ : Set M)ᶜ) 4 γ
  have hα : cocycleClass (singularCochainComplex M) 4 α = a := by
    change cocycleClass (singularCochainComplex M) 4
      (mapCocycles (RelativeIntegralCap.toAbsoluteMap (Set.univ : Set M)ᶜ) 4 γ) = a
    rw [← homologyMap_cocycleClass, hγ]
    exact (IntegralSupportedCohomology.absoluteEquiv (X := M) 4).apply_symm_apply a
  refine ⟨α, hα, ?_⟩
  rw [← hα]
  exact absoluteDualityMap_projected_cocycle (E := E) M γ Ω hΩ

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenLinking
