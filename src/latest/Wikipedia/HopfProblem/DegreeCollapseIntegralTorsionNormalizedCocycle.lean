import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionRestriction

/-!
# A cohomologous original cocycle with an exact rational restriction

Subtract the coboundary of an extended integral restriction primitive.
The original cohomology class is unchanged, the cocycle restricts to
zero as an actual cochain, and its rational primitive has the prescribed
values on all original subcomplex cycles. No finite subcomplex homology
is assumed.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open SingularCohomologyFree SingularCohomologyFree.LocalEvaluation
open SingularMayerVietoris.ModuleHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable (L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
  [Finite (L.homology n)] [Subsingleton (L.homology (n + 1))]

theorem rationalPrimitive_sub_coboundary_cycle
    (c : Cocycle (dualComplex L) (n + 1)) (B : L.X n →ₗ[ℤ] ℤ) (z : Cycle L n) :
    rationalPrimitive L n (c - coboundaryCocycle (dualComplex L) (n + 1) B) z.val =
      rationalPrimitive L n c z.val - (B z.val : ℚ) := by
  apply rational_eq_on_cycles_of_same_boundary L n
    (rationalPrimitive L n (c - coboundaryCocycle (dualComplex L) (n + 1) B))
    (rationalPrimitive L n c - RationalResidue.integralCast.comp B) ?_ z
  ext b
  change rationalPrimitive L n (c - coboundaryCocycle (dualComplex L) (n + 1) B)
      ((L.d (n + 1) n).hom b) =
    rationalPrimitive L n c ((L.d (n + 1) n).hom b) -
      (B ((L.d (n + 1) n).hom b) : ℚ)
  rw [rationalPrimitive_boundary, rationalPrimitive_boundary]
  exact Int.cast_sub _ _

variable {L n}
variable {K : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L)

theorem exists_normalized_cocycle
    [Module.Projective ℤ (OutgoingImage K n)]
    (hExt : ∀ β : K.X n →ₗ[ℤ] ℤ, ∃ B : L.X n →ₗ[ℤ] ℤ, B.comp (f.f n).hom = β)
    (c : Cocycle (dualComplex L) (n + 1)) (F : K.homology n →ₗ[ℤ] ℚ)
    (hF : ∀ a : K.homology n,
      torsionEvaluation L n (cocycleClass (dualComplex L) (n + 1) c)
        ((HomologicalComplex.homologyMap f n).hom a) = RationalResidue.residue (F a)) :
    ∃ c' : Cocycle (dualComplex L) (n + 1),
      cocycleClass (dualComplex L) (n + 1) c' = cocycleClass (dualComplex L) (n + 1) c ∧
      c'.val.comp (f.f (n + 1)).hom = 0 ∧
      ∀ z : Cycle K n,
        rationalPrimitive L n c' ((f.f n).hom z.val) = F (cycleClass K n z) := by
  obtain ⟨β, hβd, hβ⟩ := exists_integral_restrictionPrimitive f n c F hF
  obtain ⟨B, hB⟩ := hExt β
  have hBeq (x : K.X n) : B ((f.f n).hom x) = β x := LinearMap.congr_fun hB x
  let c' := c - coboundaryCocycle (dualComplex L) (n + 1) B
  have hclass : cocycleClass (dualComplex L) (n + 1) c' =
      cocycleClass (dualComplex L) (n + 1) c := by
    have hz : cocycleClass (dualComplex L) (n + 1)
        (coboundaryCocycle (dualComplex L) (n + 1) B) = 0 :=
      (cocycleClass_eq_zero_iff (dualComplex L) (n + 1) _).mpr ⟨B, rfl⟩
    change cocycleClass (dualComplex L) (n + 1)
      (c - coboundaryCocycle (dualComplex L) (n + 1) B) = _
    rw [map_sub, hz, sub_zero]
  refine ⟨c', hclass, ?_, ?_⟩
  · ext b
    change c.val ((f.f (n + 1)).hom b) -
      B ((L.d (n + 1) n).hom ((f.f (n + 1)).hom b)) = 0
    have hd : (L.d (n + 1) n).hom ((f.f (n + 1)).hom b) =
        (f.f n).hom ((K.d (n + 1) n).hom b) :=
      congrArg (fun g : K.X (n + 1) ⟶ L.X n ↦ g.hom b) (f.comm (n + 1) n)
    have hb : β ((K.d (n + 1) n).hom b) = c.val ((f.f (n + 1)).hom b) :=
      LinearMap.congr_fun hβd b
    rw [hd, hBeq, hb, sub_self]
  · intro z
    have he := rationalPrimitive_sub_coboundary_cycle L n c B (mapCycles f n z)
    rw [mapCycles_val] at he
    change rationalPrimitive L n c' ((f.f n).hom z.val) =
      rationalPrimitive L n c ((f.f n).hom z.val) - (B ((f.f n).hom z.val) : ℚ) at he
    rw [he, hBeq, hβ]
    ring

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
