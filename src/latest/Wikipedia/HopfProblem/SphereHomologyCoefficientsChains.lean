import Wikipedia.HopfProblem.SphereHomologyCoefficientsChainsFunctor

/-!
# The native short exact singular-chain coefficient sequence

For a nonzero natural number `p`, this is the actual short exact sequence
`0 → C(X; ℤ) → C(X; ℤ) → C(X; ℤ/p) → 0`, whose first map is multiplication
by `p` and whose second map is the native coefficient reduction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SphereHomologyCoefficients

theorem multiplicationCoefficient_comp_reduction (p : ℕ) :
    ((p : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) ≫ reductionCoefficient p = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (((p : ℤ) * z : ℤ) : ZMod p) = 0
  simp

/-- The elementary coefficient sequence before applying the singular-chain functor. -/
def coefficientSequence (p : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.mk ((p : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) (reductionCoefficient p)
    (multiplicationCoefficient_comp_reduction p)

theorem coefficientSequence_shortExact (p : ℕ) (hp : p ≠ 0) :
    (coefficientSequence p).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    change ∀ z : ℤ, (z : ZMod p) = 0 → ∃ a : ℤ, (p : ℤ) * a = z
    intro z hz
    obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hz
    exact ⟨a, ha.symm⟩
  mono_f := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective (fun a : ℤ => (p : ℤ) * a)
    intro a b h
    exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hp) h
  epi_g := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective (fun a : ℤ => (a : ZMod p))
    exact ZMod.intCast_surjective

/-- The composition of the two literal native chain maps vanishes. -/
theorem multiplicationChainMap_comp_reduction (p : ℕ)
    (X : Type) [TopologicalSpace X] :
    multiplicationChainMap p X ≫ reductionChainMap p X = 0 := by
  rw [← coefficientComplexMap_multiplication p X]
  change (nativeCoefficientFunctor X).map ((p : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) ≫
    (nativeCoefficientFunctor X).map (reductionCoefficient p) = 0
  rw [← CategoryTheory.Functor.map_comp, multiplicationCoefficient_comp_reduction,
    CategoryTheory.Functor.map_zero]

/-- The coefficient sequence on the original native chain complexes and maps. -/
def coefficientChainSequence (p : ℕ) (X : Type) [TopologicalSpace X] :
    ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (multiplicationChainMap p X) (reductionChainMap p X)
    (multiplicationChainMap_comp_reduction p X)

@[simp] theorem coefficientChainSequence_f (p : ℕ) (X : Type) [TopologicalSpace X] :
    (coefficientChainSequence p X).f = multiplicationChainMap p X := rfl

@[simp] theorem coefficientChainSequence_g (p : ℕ) (X : Type) [TopologicalSpace X] :
    (coefficientChainSequence p X).g = reductionChainMap p X := rfl

/-- Identification of the literal sequence with the image of the coefficient sequence. -/
theorem coefficientChainSequence_eq_map (p : ℕ) (X : Type) [TopologicalSpace X] :
    coefficientChainSequence p X =
      (coefficientSequence p).map (nativeCoefficientFunctor X) := by
  change ShortComplex.mk (multiplicationChainMap p X) (reductionChainMap p X) _ =
    ShortComplex.mk (coefficientComplexMap ((p : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) X)
      (reductionChainMap p X) _
  congr 1
  exact (coefficientComplexMap_multiplication p X).symm

/-- Short exactness of the actual native coefficient chain sequence. -/
theorem coefficientChainSequence_shortExact (p : ℕ) (hp : p ≠ 0)
    (X : Type) [TopologicalSpace X] :
    (coefficientChainSequence p X).ShortExact := by
  rw [coefficientChainSequence_eq_map]
  exact nativeCoefficientFunctor_shortExact X (coefficientSequence p)
    (coefficientSequence_shortExact p hp)

end Wikipedia.HopfProblem.SphereHomologyCoefficients
