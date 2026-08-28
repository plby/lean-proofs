import Wikipedia.NoExoticSixSphere.CompactManifoldFundamentalSupport
import Wikipedia.NoExoticSixSphere.AbsoluteSupportedHomology

/-!
# The constructed global mod-two fundamental class

For a compact manifold without boundary, the unique whole-support class
is transported to the original absolute singular homology by the actual
empty-subspace projection. Its localizations are the constructed nonzero
local classes. This proves existence and uniqueness, not Poincaré duality.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ManifoldFundamentalClass

open SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [CompactSpace M]

/-- The unique constructed whole-support relative class. -/
def supportedClass : Homology (ModuleCat.of ℤ (ZMod 2)) (Set.univ : Set M) (n + 3) :=
  Classical.choose (compactManifold_existsUnique_fundamentalClass (E := E) n
    (Set.univ : Set M) isCompact_univ)

theorem supportedClass_isFundamentalOn :
    IsFundamentalOn (E := E) n (Set.univ : Set M) (supportedClass (E := E) n M) :=
  (Classical.choose_spec (compactManifold_existsUnique_fundamentalClass (E := E) n
    (Set.univ : Set M) isCompact_univ)).1

/-- The fundamental class in the native absolute singular homology object. -/
def fundamentalClass : ModHomology 2 M (n + 3) :=
  (absoluteEquiv (X := M) (ModuleCat.of ℤ (ZMod 2)) (n + 3)).symm
    (supportedClass (E := E) n M)

theorem fromAbsolute_fundamentalClass :
    fromAbsolute (ModuleCat.of ℤ (ZMod 2)) (Set.univ : Set M) (n + 3)
        (fundamentalClass (E := E) n M) = supportedClass (E := E) n M :=
  (absoluteEquiv (X := M) (ModuleCat.of ℤ (ZMod 2)) (n + 3)).apply_symm_apply _

/-- The original projection to the relative homology at a point. -/
abbrev localize (x : M) :
    ModHomology 2 M (n + 3) →ₗ[ℤ] RelativeCoefficients.ModHomology 2 ({x}ᶜ : Set M) (n + 3) :=
  fromAbsolute (ModuleCat.of ℤ (ZMod 2)) {x} (n + 3)

theorem localize_fundamentalClass (x : M) :
    localize n M x (fundamentalClass (E := E) n M) =
      ModTwoLocalClass.manifoldClass (E := E) n x := by
  have he := LinearMap.congr_fun
    (restrict_fromAbsolute (ModuleCat.of ℤ (ZMod 2))
      (Set.subset_univ ({x} : Set M)) (n + 3)) (fundamentalClass (E := E) n M)
  exact he.symm.trans ((congrArg
    (evaluate (ModuleCat.of ℤ (ZMod 2)) (Set.univ : Set M) x (Set.mem_univ x) (n + 3))
      (fromAbsolute_fundamentalClass (E := E) n M)).trans
        (supportedClass_isFundamentalOn (E := E) n M x (Set.mem_univ x)))

/-- The actual fundamental class of a nonempty compact manifold is nonzero. -/
theorem fundamentalClass_ne_zero [Nonempty M] : fundamentalClass (E := E) n M ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty M›
  intro he
  have hx := localize_fundamentalClass (E := E) n M x
  rw [he, map_zero] at hx
  exact ModTwoLocalClass.manifoldClass_ne_zero (E := E) n x hx.symm

/-- The original local projections characterize the absolute fundamental class uniquely. -/
theorem fundamentalClass_unique (a : ModHomology 2 M (n + 3))
    (ha : ∀ x : M, localize n M x a = ModTwoLocalClass.manifoldClass (E := E) n x) :
    a = fundamentalClass (E := E) n M := by
  apply (absoluteEquiv (X := M) (ModuleCat.of ℤ (ZMod 2)) (n + 3)).injective
  apply compactManifold_detected (E := E) n (Set.univ : Set M) isCompact_univ
  intro x hx
  have he := LinearMap.congr_fun (restrict_fromAbsolute (ModuleCat.of ℤ (ZMod 2))
    (Set.subset_univ ({x} : Set M)) (n + 3)) a
  have hf := LinearMap.congr_fun (restrict_fromAbsolute (ModuleCat.of ℤ (ZMod 2))
    (Set.subset_univ ({x} : Set M)) (n + 3)) (fundamentalClass (E := E) n M)
  exact he.trans ((ha x).trans ((localize_fundamentalClass (E := E) n M x).symm.trans hf.symm))

/-- Existence and uniqueness are proved in the native absolute homology, not a model group. -/
theorem existsUnique_fundamentalClass :
    ∃! a : ModHomology 2 M (n + 3),
      ∀ x : M, localize n M x a = ModTwoLocalClass.manifoldClass (E := E) n x :=
  ⟨fundamentalClass (E := E) n M, localize_fundamentalClass (E := E) n M,
    fun a ha => fundamentalClass_unique (E := E) n M a ha⟩

include E in
/-- The native absolute homology of a compact manifold vanishes above its dimension. -/
theorem above_subsingleton (k : ℕ) (hk : n + 3 < k) : Subsingleton (ModHomology 2 M k) := by
  let := compactManifold_above_subsingleton (E := E) n (Set.univ : Set M) isCompact_univ k hk
  exact (absoluteEquiv (X := M) (ModuleCat.of ℤ (ZMod 2)) k).injective.subsingleton

/-- The global class restricts to a fundamental class on every subset. -/
theorem fromAbsolute_isFundamentalOn (K : Set M) :
    IsFundamentalOn (E := E) n K
      (fromAbsolute (ModuleCat.of ℤ (ZMod 2)) K (n + 3) (fundamentalClass (E := E) n M)) := by
  have h := (supportedClass_isFundamentalOn (E := E) n M).restrict n (Set.subset_univ K)
  have he := LinearMap.congr_fun (restrict_fromAbsolute (ModuleCat.of ℤ (ZMod 2))
    (Set.subset_univ K) (n + 3)) (fundamentalClass (E := E) n M)
  rw [LinearMap.comp_apply, fromAbsolute_fundamentalClass (E := E) n M] at he
  exact he ▸ h

/-- An actual native singular cycle represents the constructed fundamental class. -/
theorem exists_fundamental_cycle :
    ∃ c : ModuleHomology.Cycle (modComplex 2 M) (n + 3),
      ModuleHomology.cycleClass (modComplex 2 M) (n + 3) c = fundamentalClass (E := E) n M :=
  ModuleHomology.cycleClass_surjective (modComplex 2 M) (n + 3) (fundamentalClass (E := E) n M)

end NoExoticSixSphere.ManifoldFundamentalClass
