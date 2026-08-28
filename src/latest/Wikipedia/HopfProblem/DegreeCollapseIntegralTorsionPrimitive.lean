import Wikipedia.HopfProblem.DegreeCollapseRationalResidueExtensions
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSplitting

/-!
# Rational primitives of the original integral cocycles

When the next integral homology vanishes, an original integral cocycle
annihilates all cycles in that degree. It factors through the actual
boundary image. Injectivity of the rational coefficient module extends
that factor to an original rational cochain, with the exact original
coboundary equal to the integral cocycle's rational image.
-/

noncomputable section

open CategoryTheory Function

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open SingularCohomologyFree SingularCohomologyFree.LocalEvaluation
open SingularMayerVietoris.ModuleHomology

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

theorem cocycle_zero_on_cycles [Subsingleton (K.homology n)]
    (c : Cocycle (dualComplex K) n) (z : Cycle K n) : c.val z.val = 0 := by
  have hz : cycleClass K n z = 0 := Subsingleton.elim _ _
  exact (cocycleEvaluation_cycleClass K n c z).symm.trans (by rw [hz, map_zero])

variable [Subsingleton (K.homology (n + 1))]

theorem exists_rationalPrimitive (c : Cocycle (dualComplex K) (n + 1)) :
    ∃ f : K.X n →ₗ[ℤ] ℚ,
      f.comp (K.d (n + 1) n).hom = RationalResidue.integralCast.comp c.val := by
  have hk : LinearMap.ker (K.d (n + 1) n).hom ≤
      LinearMap.ker (RationalResidue.integralCast.comp c.val) := by
    intro x hx
    let z : Cycle K (n + 1) := mkCycle K (n + 1) x
      (by change (K.d (n + 1) n).hom x = 0; exact hx)
    change RationalResidue.integralCast (c.val x) = 0
    exact (congrArg RationalResidue.integralCast
      (cocycle_zero_on_cycles K (n + 1) c z)).trans (map_zero _)
  let : Module ℤ (LinearMap.range (K.d (n + 1) n).hom) :=
    (LinearMap.range (K.d (n + 1) n).hom).module
  obtain ⟨ψ, hψ⟩ := exists_factor_through_range (K.d (n + 1) n).hom
    (RationalResidue.integralCast.comp c.val) hk
  obtain ⟨f, hf⟩ := Module.Injective.extension_property
    (R := ℤ) (M := ℚ) (P := LinearMap.range (K.d (n + 1) n).hom) (P' := K.X n)
    (LinearMap.range (K.d (n + 1) n).hom).subtype Subtype.val_injective ψ
  refine ⟨f, ?_⟩
  calc
    f.comp (K.d (n + 1) n).hom =
        (f.comp (LinearMap.range (K.d (n + 1) n).hom).subtype).comp
          (K.d (n + 1) n).hom.rangeRestrict := rfl
    _ = ψ.comp (K.d (n + 1) n).hom.rangeRestrict := by rw [hf]
    _ = RationalResidue.integralCast.comp c.val := hψ

def rationalPrimitive (c : Cocycle (dualComplex K) (n + 1)) : K.X n →ₗ[ℤ] ℚ :=
  (exists_rationalPrimitive K n c).choose

theorem rationalPrimitive_spec (c : Cocycle (dualComplex K) (n + 1)) :
    (rationalPrimitive K n c).comp (K.d (n + 1) n).hom =
      RationalResidue.integralCast.comp c.val :=
  (exists_rationalPrimitive K n c).choose_spec

theorem rationalPrimitive_boundary (c : Cocycle (dualComplex K) (n + 1))
    (b : K.X (n + 1)) :
    rationalPrimitive K n c ((K.d (n + 1) n).hom b) = (c.val b : ℚ) :=
  LinearMap.congr_fun (rationalPrimitive_spec K n c) b

theorem rationalPrimitive_bounding_formula (c : Cocycle (dualComplex K) (n + 1))
    (z : Cycle K n) (l : ℤ) (hl : l ≠ 0) (b : K.X (n + 1))
    (hb : (K.d (n + 1) n).hom b = l • z.val) :
    rationalPrimitive K n c z.val = (c.val b : ℚ) / (l : ℚ) := by
  have he := rationalPrimitive_boundary K n c b
  rw [hb, map_zsmul, zsmul_eq_mul] at he
  apply (eq_div_iff (Int.cast_ne_zero.mpr hl)).mpr
  exact (mul_comm _ _).trans he

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
