import ErdosProblems.Erdos240.External.Towers.ClassField.KummerTheory.KummerRadicalExtension

/-!
# Comparing chosen Kummer roots with roots in an intermediate field

If a power class becomes an `n`th power in an intermediate field, then the
chosen root of its canonical representative in the fixed algebraic closure
already belongs to that field.  The key point is that one root together with
the primitive `n`th roots of unity makes `X^n-a` split completely.
-/

namespace Towers.CField.KTheory

noncomputable section

open Polynomial

universe u

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω]

private theorem representative_power_witness
    (n : ℕ) {a : Kˣ} {b : PowerClassGroup K n}
    (h : powerClass n a = b) :
    ∃ d : Kˣ, powerClassRepresentative K n b * d ^ n = a := by
  have hclasses :
      powerClass n (powerClassRepresentative K n b) = powerClass n a := by
    rw [power_class_representative, h]
  obtain ⟨z, hz, heq⟩ := (QuotientGroup.mk'_eq_mk' _).mp hclasses
  obtain ⟨d, rfl⟩ := hz
  exact ⟨d, heq⟩

omit [IsAlgClosure K Ω] in
/-- A power class in the radical subgroup has a root of its canonical
representative inside the intermediate field. -/
theorem root_class_representative
    (n : ℕ) (L : IntermediateField K Ω)
    (b : PowerClassGroup K n)
    (hb : b ∈ radicalPowerClasses K Ω n L) :
    ∃ y : Lˣ, y ^ n =
      Units.map (algebraMap K L) (powerClassRepresentative K n b) := by
  obtain ⟨a, haRadical, hab⟩ := hb
  obtain ⟨x, hxpow⟩ := haRadical
  obtain ⟨d, hd⟩ := representative_power_witness K n hab
  let f : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  let dL : Lˣ := f d
  refine ⟨x * dL⁻¹, ?_⟩
  rw [mul_pow, inv_pow, hxpow, ← map_pow]
  change f a * (f (d ^ n))⁻¹ = f (powerClassRepresentative K n b)
  have hdmapped : f a =
      f (powerClassRepresentative K n b) * f d ^ n := by
    simpa using congrArg f hd.symm
  rw [hdmapped, map_pow]
  group

/-- If a class belongs to the radical subgroup of `L`, the globally chosen
Kummer root representing that class lies in `L`. -/
theorem kummer_radical_classes
    (n : ℕ) (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (L : IntermediateField K Ω)
    (b : PowerClassGroup K n)
    (hb : b ∈ radicalPowerClasses K Ω n L) :
    kummerRoot K Ω n hn b ∈ L := by
  obtain ⟨y, hypow⟩ :=
    root_class_representative K Ω n L b hb
  let a : K := ((powerClassRepresentative K n b : Kˣ) : K)
  have hy : (y : L) ^ n = algebraMap K L a := by
    exact congrArg Units.val hypow
  have hsplitL :
      ((X ^ n - C a).map (algebraMap K L)).Splits := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
      using X_pow_sub_C_splits_of_isPrimitiveRoot
        (hζ.map_of_injective (algebraMap K L).injective) hy
  have hroot : kummerRoot K Ω n hn b ∈ (X ^ n - C a).rootSet Ω := by
    rw [mem_rootSet_of_ne (X_pow_sub_C_ne_zero hn a)]
    simp [a, kummerRoot_pow K Ω n hn b]
  have hsplitΩ :
      ((X ^ n - C a).map (algebraMap K Ω)).Splits := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
      using X_pow_sub_C_splits_of_isPrimitiveRoot
        (hζ.map_of_injective (algebraMap K Ω).injective)
        (kummerRoot_pow K Ω n hn b)
  exact ((IntermediateField.splits_iff_mem hsplitΩ).1 hsplitL)
    _ hroot

/-- Radical generation is contained in any intermediate field in which all
the generating classes become `n`th powers. -/
theorem field_radical_classes
    (n : ℕ) (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (L : IntermediateField K Ω)
    (B : PCSubgro K n)
    (hB : B.carrier ≤ radicalPowerClasses K Ω n L) :
    kummerField K Ω n hn B ≤ L := by
  rw [kummerField, IntermediateField.adjoin_le_iff]
  rintro x ⟨b, rfl⟩
  exact kummer_radical_classes
    K Ω n hn hζ L b.1 (hB b.2)

end

end Towers.CField.KTheory
