import Wikipedia.NoExoticSixSphere.RelativeCoefficientSequence

/-!
# Vanishing from the actual relative coefficient sequence

If an integral relative homology group vanishes and multiplication by the
coefficient modulus is injective in the preceding group, the corresponding
native finite-cyclic group vanishes. The proof uses the actual Bockstein
and reduction exactness, including the degree immediately above a free
top local integral group.
-/

noncomputable section

namespace NoExoticSixSphere.RelativeCoefficients

variable {X : Type} [TopologicalSpace X]

/-- Native finite-coefficient vanishing, with the Bockstein obstruction killed explicitly. -/
theorem modHomology_subsingleton_of_mul_injective (p : ℕ) (hp : p ≠ 0) (U : Set X) (n : ℕ)
    [Subsingleton (RelativeSingularHomology.Homology U (n + 1))]
    (hm : Function.Injective ((p : ℤ) •
      (LinearMap.id : RelativeSingularHomology.Homology U n →ₗ[ℤ]
        RelativeSingularHomology.Homology U n))) : Subsingleton (ModHomology p U (n + 1)) := by
  have hz (a : ModHomology p U (n + 1)) : a = 0 := by
    have hk : bockstein p hp U n a ∈ LinearMap.ker ((p : ℤ) •
        (LinearMap.id : RelativeSingularHomology.Homology U n →ₗ[ℤ]
          RelativeSingularHomology.Homology U n)) := by
      rw [← bockstein_range p hp U n]
      exact ⟨a, rfl⟩
    have hb : bockstein p hp U n a = 0 := hm (hk.trans (map_zero _).symm)
    have hr : a ∈ LinearMap.range (reductionMap p U (n + 1)) := by
      rw [reductionMap_range p hp U n]
      exact hb
    obtain ⟨z, rfl⟩ := hr
    rw [Subsingleton.elim z 0, map_zero]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- A marking by the original integral group proves injectivity of nonzero multiplication. -/
theorem multiplication_injective_of_int_equiv (p : ℕ) (hp : p ≠ 0) (U : Set X) (n : ℕ)
    (e : RelativeSingularHomology.Homology U n ≃ₗ[ℤ] ℤ) :
    Function.Injective ((p : ℤ) • (LinearMap.id : RelativeSingularHomology.Homology U n →ₗ[ℤ]
      RelativeSingularHomology.Homology U n)) := by
  intro a b hab
  apply e.injective
  change (p : ℤ) • a = (p : ℤ) • b at hab
  have he := congrArg e hab
  simp only [map_zsmul, zsmul_eq_mul] at he
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hp) he

end NoExoticSixSphere.RelativeCoefficients
