import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionInjective

/-!
# Integral primitives on a possibly infinite-homology subcomplex

If the original torsion character pulls back to the residue of a rational
homology functional, the original pulled-back cocycle has an integral
primitive. Only the ambient homology is finite. The primitive retains
its exact value on every original cycle of the subcomplex.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open SingularCohomologyFree SingularCohomologyFree.LocalEvaluation
open SingularMayerVietoris.ModuleHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L) (n : ℕ)
  [Finite (L.homology n)] [Subsingleton (L.homology (n + 1))]

theorem exists_integral_restrictionPrimitive
    [Module.Projective ℤ (OutgoingImage K n)]
    (c : Cocycle (dualComplex L) (n + 1)) (F : K.homology n →ₗ[ℤ] ℚ)
    (hF : ∀ a : K.homology n,
      torsionEvaluation L n (cocycleClass (dualComplex L) (n + 1) c)
        ((HomologicalComplex.homologyMap f n).hom a) = RationalResidue.residue (F a)) :
    ∃ β : K.X n →ₗ[ℤ] ℤ,
      β.comp (K.d (n + 1) n).hom = c.val.comp (f.f (n + 1)).hom ∧
      ∀ z : Cycle K n, (β z.val : ℚ) =
        rationalPrimitive L n c ((f.f n).hom z.val) - F (cycleClass K n z) := by
  let : Module ℤ (Cycle K n) := (Cycle K n).module
  let g : Cycle K n →ₗ[ℤ] ℚ :=
    ((rationalPrimitive L n c).comp (f.f n).hom).comp (Cycle K n).subtype -
      F.comp (cycleClass K n)
  have hg : ∀ z : Cycle K n, RationalResidue.residue (g z) = 0 := by
    intro z
    have he := hF (cycleClass K n z)
    rw [homologyMap_cycleClass, torsionEvaluation_cocycle_cycle, mapCycles_val] at he
    change RationalResidue.residue
      (rationalPrimitive L n c ((f.f n).hom z.val) - F (cycleClass K n z)) = 0
    rw [map_sub, he, sub_self]
  obtain ⟨γ, hγ⟩ := RationalResidue.exists_integer_lift g hg
  obtain ⟨β, hβ⟩ := exists_extension_from_cycles K n γ
  have hval (z : Cycle K n) : (β z.val : ℚ) =
      rationalPrimitive L n c ((f.f n).hom z.val) - F (cycleClass K n z) :=
    (congrArg RationalResidue.integralCast (hβ z)).trans (LinearMap.congr_fun hγ z)
  refine ⟨β, ?_, hval⟩
  ext b
  apply RationalResidue.integralCast_injective
  have he := hval (boundaryCycle K n b)
  rw [cycleClass_boundary, map_zero, sub_zero] at he
  have hd : (f.f n).hom ((K.d (n + 1) n).hom b) =
      (L.d (n + 1) n).hom ((f.f (n + 1)).hom b) :=
    congrArg (fun g : K.X (n + 1) ⟶ L.X n ↦ g.hom b) (f.comm (n + 1) n).symm
  change (β ((K.d (n + 1) n).hom b) : ℚ) =
    rationalPrimitive L n c ((f.f n).hom ((K.d (n + 1) n).hom b)) at he
  rw [hd, rationalPrimitive_boundary] at he
  exact he

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
