import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionNormalizedCocycle
import Wikipedia.HopfProblem.DegreeCollapseIntegralCochainExtension
import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionSingular
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainBasic

/-!
# A normalized original cocycle for a rationally lifted character

For an injective continuous map, the original simplex bases discharge
all projectivity and integral-cochain extension inputs. A character
whose original pullback lifts to rational homology has an original
cocycle representative vanishing strictly on the source chains, with
the prescribed rational primitive on every original source cycle.
The source homology need not be finite.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open FirstHurewicz SingularCohomologyFree SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_singular_normalized_cocycle (f : C(X, Y)) (hf : Function.Injective f) (n : ℕ)
    [Finite (SingularHomology Y n)] [Subsingleton (SingularHomology Y (n + 1))]
    (χ : SingularHomology Y n →+ RationalResidue.Value) (F : SingularHomology X n →+ ℚ)
    (hF : ∀ a : SingularHomology X n,
      χ (singularHomologyMap f n a) = RationalResidue.residue (F a)) :
    ∃ c : Cocycle (singularCochainComplex Y) (n + 1),
      (singularTorsionEvaluation Y n
        (cocycleClass (singularCochainComplex Y) (n + 1) c)).toAddMonoidHom = χ ∧
      c.val.comp (inducedChain f (n + 1)) = 0 ∧
      ∀ z : ModuleHomology.Cycle (singularComplex X) n,
        rationalPrimitive (singularComplex Y) n c (inducedChain f n z.val) =
          F (ModuleHomology.cycleClass (singularComplex X) n z) := by
  let χ' : SingularHomology Y n →ₗ[ℤ] RationalResidue.Value :=
    ConstantSheafSingularComparison.addHomToIntLinearMap χ
  let F' : SingularHomology X n →ₗ[ℤ] ℚ :=
    ConstantSheafSingularComparison.addHomToIntLinearMap F
  obtain ⟨a, ha⟩ := (singularTorsionEvaluation_bijective Y n).2 χ'
  obtain ⟨c, hc⟩ := cocycleClass_surjective (singularCochainComplex Y) (n + 1) a
  have hτ : singularTorsionEvaluation Y n
      (cocycleClass (singularCochainComplex Y) (n + 1) c) = χ' := by rw [hc, ha]
  let (j : ℕ) : Module.Free ℤ ((singularComplex X).X j) := Module.Free.of_basis (chainBasis X j)
  let : Module.Projective ℤ (LocalEvaluation.OutgoingImage (singularComplex X) n) :=
    SingularCohomologyFreeEvaluation.submodule_projective_int
      (LinearMap.range ((singularComplex X).d n ((ComplexShape.down ℕ).next n)).hom)
  have hExt (β : (singularComplex X).X n →ₗ[ℤ] ℤ) :
      ∃ B : (singularComplex Y).X n →ₗ[ℤ] ℤ, B.comp ((singularChainMap f).f n).hom = β :=
    IntegralCochainExtension.exists_cochain_extension f hf n β
  have hχ (b : SingularHomology X n) :
      torsionEvaluation (singularComplex Y) n
        (cocycleClass (singularCochainComplex Y) (n + 1) c)
        ((HomologicalComplex.homologyMap (singularChainMap f) n).hom b) =
          RationalResidue.residue (F' b) := by
    change singularTorsionEvaluation Y n
      (cocycleClass (singularCochainComplex Y) (n + 1) c) (singularHomologyMap f n b) = _
    rw [hτ]
    exact hF b
  obtain ⟨c', hclass, hzero, hval⟩ :=
    exists_normalized_cocycle (n := n) (singularChainMap f) hExt c F' hχ
  refine ⟨c', ?_, hzero, hval⟩
  apply AddMonoidHom.ext
  intro b
  change singularTorsionEvaluation Y n
    (cocycleClass (singularCochainComplex Y) (n + 1) c') b = χ b
  rw [hclass, hτ]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
