import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionSurjective

/-!
# A common integral denominator for the original torsion evaluation

The cardinality of the original finite homology annihilates the original
cohomology through the proved evaluation injection. Each cocycle therefore
has an integral primitive after this common multiplication. Its value on
an original cycle computes the original torsion character exactly.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open SingularCohomologyFree SingularMayerVietoris.ModuleHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
  [Finite (K.homology n)] [Subsingleton (K.homology (n + 1))]

theorem cohomology_card_nsmul_eq_zero [∀ j, Module.Free ℤ (K.X j)]
    (a : Cohomology K (n + 1)) : Nat.card (K.homology n) • a = 0 := by
  apply torsionEvaluation_injective_of_free K n
  rw [map_nsmul, map_zero]
  ext b
  change Nat.card (K.homology n) • torsionEvaluation K n a b = 0
  rw [← map_nsmul, card_nsmul_eq_zero', map_zero]

theorem exists_integer_cardPrimitive [∀ j, Module.Free ℤ (K.X j)]
    (c : Cocycle (dualComplex K) (n + 1)) :
    ∃ u : K.X n →ₗ[ℤ] ℤ,
      u.comp (K.d (n + 1) n).hom = Nat.card (K.homology n) • c.val := by
  have hc : cocycleClass (dualComplex K) (n + 1) (Nat.card (K.homology n) • c) = 0 := by
    rw [map_nsmul]
    exact cohomology_card_nsmul_eq_zero K n _
  exact (cocycleClass_eq_zero_iff (dualComplex K) (n + 1) _).mp hc

theorem torsionEvaluation_cardPrimitive_formula
    (c : Cocycle (dualComplex K) (n + 1)) (u : K.X n →ₗ[ℤ] ℤ)
    (hu : u.comp (K.d (n + 1) n).hom = Nat.card (K.homology n) • c.val)
    (z : Cycle K n) :
    torsionEvaluation K n (cocycleClass (dualComplex K) (n + 1) c) (cycleClass K n z) =
      RationalResidue.residue ((u z.val : ℚ) / (Nat.card (K.homology n) : ℚ)) := by
  obtain ⟨b, hb⟩ := exists_card_boundary K n z
  have he : u z.val = c.val b := by
    have he := LinearMap.congr_fun hu b
    change u ((K.d (n + 1) n).hom b) = Nat.card (K.homology n) • c.val b at he
    rw [hb, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at he
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr Nat.card_pos.ne') he
  have hl : (Nat.card (K.homology n) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hb' : (K.d (n + 1) n).hom b = (Nat.card (K.homology n) : ℤ) • z.val := by
    simpa only [natCast_zsmul] using hb
  rw [torsionEvaluation_bounding_formula K n c z _ hl b hb', ← he]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
