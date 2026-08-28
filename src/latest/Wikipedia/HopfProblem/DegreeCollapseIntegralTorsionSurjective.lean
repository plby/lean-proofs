import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionInjective

/-!
# Every character of the original finite homology has an integral cohomology representative

Extend the character from the original cycles into the injective rational
quotient, lift it to a rational cochain on the projective chain module,
and lift its integer-valued original coboundary to an integral cocycle.
The checked primitive formula proves that its actual torsion evaluation
is the prescribed character.
-/

noncomputable section

open CategoryTheory Function

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open SingularCohomologyFree SingularMayerVietoris.ModuleHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
  [Finite (K.homology n)] [Subsingleton (K.homology (n + 1))]

theorem torsionEvaluation_surjective [Module.Projective ℤ (K.X n)] :
    Surjective (torsionEvaluation K n) := by
  intro χ
  let : Module ℤ (Cycle K n) := (Cycle K n).module
  obtain ⟨ψ, hψ⟩ := Module.Injective.extension_property
    (R := ℤ) (M := RationalResidue.Value) (P := Cycle K n) (P' := K.X n)
    (Cycle K n).subtype Subtype.val_injective (χ.comp (cycleClass K n))
  obtain ⟨ν, hν⟩ := RationalResidue.exists_rational_lift ψ
  have hz : ∀ b : K.X (n + 1),
      RationalResidue.residue ((ν.comp (K.d (n + 1) n).hom) b) = 0 := by
    intro b
    calc
      RationalResidue.residue (ν ((K.d (n + 1) n).hom b)) =
          ψ ((K.d (n + 1) n).hom b) := LinearMap.congr_fun hν _
      _ = χ (cycleClass K n (boundaryCycle K n b)) :=
        LinearMap.congr_fun hψ (boundaryCycle K n b)
      _ = 0 := by rw [cycleClass_boundary, map_zero]
  obtain ⟨α, hα⟩ := RationalResidue.exists_integer_lift (ν.comp (K.d (n + 1) n).hom) hz
  have hc : ((dualComplex K).d (n + 1) (n + 1 + 1)).hom α = 0 := by
    ext b
    change α ((K.d (n + 1 + 1) (n + 1)).hom b) = 0
    apply RationalResidue.integralCast_injective
    have hd : (K.d (n + 1) n).hom ((K.d (n + 1 + 1) (n + 1)).hom b) = 0 :=
      congrArg (fun f : K.X (n + 1 + 1) ⟶ K.X n ↦ f.hom b)
        (K.d_comp_d (n + 1 + 1) (n + 1) n)
    calc
      RationalResidue.integralCast (α ((K.d (n + 1 + 1) (n + 1)).hom b)) =
          ν ((K.d (n + 1) n).hom ((K.d (n + 1 + 1) (n + 1)).hom b)) :=
        LinearMap.congr_fun hα _
      _ = RationalResidue.integralCast 0 := by rw [hd, map_zero, map_zero]
  let c := mkCocycle (dualComplex K) (n + 1) α hc
  refine ⟨cocycleClass (dualComplex K) (n + 1) c, ?_⟩
  ext a
  obtain ⟨z, rfl⟩ := cycleClass_surjective K n a
  rw [torsionEvaluation_cocycle_cycle]
  have he := rational_eq_on_cycles_of_same_boundary K n
    (rationalPrimitive K n c) ν ((rationalPrimitive_spec K n c).trans hα) z
  calc
    RationalResidue.residue (rationalPrimitive K n c z.val) =
        RationalResidue.residue (ν z.val) := congrArg RationalResidue.residue he
    _ = ψ z.val := LinearMap.congr_fun hν _
    _ = χ (cycleClass K n z) := LinearMap.congr_fun hψ z

theorem torsionEvaluation_bijective [∀ j, Module.Free ℤ (K.X j)] :
    Bijective (torsionEvaluation K n) :=
  ⟨torsionEvaluation_injective_of_free K n, torsionEvaluation_surjective K n⟩

def torsionEvaluationEquiv [∀ j, Module.Free ℤ (K.X j)] :
    Cohomology K (n + 1) ≃ₗ[ℤ] (K.homology n →ₗ[ℤ] RationalResidue.Value) :=
  LinearEquiv.ofBijective (torsionEvaluation K n) (torsionEvaluation_bijective K n)

theorem torsionEvaluationEquiv_toLinearMap [∀ j, Module.Free ℤ (K.X j)] :
    (torsionEvaluationEquiv K n).toLinearMap = torsionEvaluation K n := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
