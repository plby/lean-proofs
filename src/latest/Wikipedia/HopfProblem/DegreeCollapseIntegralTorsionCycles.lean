import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionPrimitive
import Mathlib.GroupTheory.OrderOfElement

/-!
# Rational primitives agree on the original finite-homology cycles

The actual homology-class map shows that the group cardinality times
each original cycle bounds an original chain. Rational functionals with
the same original coboundary therefore agree on cycles. This removes
the primitive choice and proves additivity and integer linearity there.
-/

noncomputable section

open CategoryTheory Function

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open SingularCohomologyFree SingularMayerVietoris.ModuleHomology

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

theorem exists_card_boundary (z : Cycle K n) :
    ∃ b : K.X (n + 1), (K.d (n + 1) n).hom b = Nat.card (K.homology n) • z.val := by
  have hz : cycleClass K n (Nat.card (K.homology n) • z) = 0 := by
    rw [map_nsmul]
    exact card_nsmul_eq_zero'
  exact (cycleClass_eq_zero_iff K n _).mp hz

variable [Finite (K.homology n)]

theorem rational_eq_on_cycles_of_same_boundary (f g : K.X n →ₗ[ℤ] ℚ)
    (hfg : f.comp (K.d (n + 1) n).hom = g.comp (K.d (n + 1) n).hom)
    (z : Cycle K n) : f z.val = g z.val := by
  obtain ⟨b, hb⟩ := exists_card_boundary K n z
  have he := LinearMap.congr_fun hfg b
  change f ((K.d (n + 1) n).hom b) = g ((K.d (n + 1) n).hom b) at he
  rw [hb, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at he
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne') he

variable [Subsingleton (K.homology (n + 1))]

theorem rationalPrimitive_add_on_cycles (c d : Cocycle (dualComplex K) (n + 1))
    (z : Cycle K n) :
    rationalPrimitive K n (c + d) z.val =
      rationalPrimitive K n c z.val + rationalPrimitive K n d z.val := by
  apply rational_eq_on_cycles_of_same_boundary K n
    (rationalPrimitive K n (c + d)) (rationalPrimitive K n c + rationalPrimitive K n d) ?_ z
  ext b
  change rationalPrimitive K n (c + d) ((K.d (n + 1) n).hom b) =
    rationalPrimitive K n c ((K.d (n + 1) n).hom b) +
      rationalPrimitive K n d ((K.d (n + 1) n).hom b)
  rw [rationalPrimitive_boundary, rationalPrimitive_boundary, rationalPrimitive_boundary]
  simp only [Submodule.coe_add, LinearMap.add_apply, Int.cast_add]

theorem rationalPrimitive_smul_on_cycles (r : ℤ) (c : Cocycle (dualComplex K) (n + 1))
    (z : Cycle K n) :
    rationalPrimitive K n (r • c) z.val = r • rationalPrimitive K n c z.val := by
  apply rational_eq_on_cycles_of_same_boundary K n
    (rationalPrimitive K n (r • c)) (r • rationalPrimitive K n c) ?_ z
  ext b
  change rationalPrimitive K n (r • c) ((K.d (n + 1) n).hom b) =
    r • rationalPrimitive K n c ((K.d (n + 1) n).hom b)
  rw [rationalPrimitive_boundary, rationalPrimitive_boundary]
  simp only [Submodule.coe_smul, LinearMap.smul_apply, zsmul_eq_mul, Int.cast_mul, Int.cast_id]

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
