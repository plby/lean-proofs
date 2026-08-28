import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology
import Wikipedia.NoExoticSixSphere.ModTwoLocalClassUniqueness

/-!
# Supported classes in actual open neighborhoods

For a closed support inside an open neighborhood, excision identifies the
native supported relative homology groups by inclusion. The original local
evaluation maps commute with that inclusion. In the mod-two manifold case,
these maps carry a fundamental relative class on the neighborhood to a
fundamental relative class on the original space.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {M : Type} [TopologicalSpace M]

/-- The original support as a subset of the chosen neighborhood. -/
def supportIn (U K : Set M) : Set U := Subtype.val ⁻¹' K

/-- Inclusion of the actual pairs with the same support. -/
def inclusionChain (A : ModuleCat.{0} ℤ) (U K : Set M) :
    Complex A (supportIn U K) ⟶ Complex A K :=
  RelativeCoefficients.mapChain A (subtypeInclusion U)
    (show Set.MapsTo (subtypeInclusion U) (supportIn U K)ᶜ Kᶜ from fun _ hx => hx)

abbrev inclusionMap (A : ModuleCat.{0} ℤ) (U K : Set M) (n : ℕ) :
    Homology A (supportIn U K) n →ₗ[ℤ] Homology A K n :=
  homologyLinearMap (inclusionChain A U K) n

omit [TopologicalSpace M] in
theorem support_complement_cover (U K : Set M) (hKU : K ⊆ U) : U ∪ Kᶜ = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ K
  · exact Or.inl (hKU hx)
  · exact Or.inr hx

/-- Closed support inside the actual open neighborhood gives native coefficient excision. -/
theorem inclusionChain_quasiIso (p : ℕ) (hp : p ≠ 0) (U K : Set M)
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) :
    QuasiIso (inclusionChain (ModuleCat.of ℤ (ZMod p)) U K) :=
  RelativeCoefficients.modExcisionChainMap_quasiIso p hp U Kᶜ hU hK.isOpen_compl
    (support_complement_cover U K hKU)

/-- Supported relative homology is computed inside any such actual open neighborhood. -/
def inclusionEquiv (p : ℕ) (hp : p ≠ 0) (U K : Set M)
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (n : ℕ) :
    Homology (ModuleCat.of ℤ (ZMod p)) (supportIn U K) n ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ (ZMod p)) K n := by
  let := inclusionChain_quasiIso p hp U K hU hK hKU
  exact (isoOfQuasiIsoAt (inclusionChain (ModuleCat.of ℤ (ZMod p)) U K) n).toLinearEquiv

theorem inclusionEquiv_toLinearMap (p : ℕ) (hp : p ≠ 0) (U K : Set M)
    (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (n : ℕ) :
    (inclusionEquiv p hp U K hU hK hKU n).toLinearMap =
      inclusionMap (ModuleCat.of ℤ (ZMod p)) U K n := rfl

/-- The local evaluation square commutes on the original chain maps. -/
theorem inclusion_evaluation_chain (p : ℕ) (U K : Set M) (x : U) (hx : (x : M) ∈ K) :
    inclusionChain (ModuleCat.of ℤ (ZMod p)) U K ≫
        restrictChain (ModuleCat.of ℤ (ZMod p))
          (show {(x : M)} ⊆ K from Set.singleton_subset_iff.mpr hx) =
      restrictChain (ModuleCat.of ℤ (ZMod p))
          (show {x} ⊆ supportIn U K from Set.singleton_subset_iff.mpr hx) ≫
        RelativeCoefficients.modNeighborhoodChainMap p U x := by
  change RelativeCoefficients.mapChain _ (subtypeInclusion U) _ ≫
      RelativeCoefficients.mapChain _ (ContinuousMap.id M) _ =
    RelativeCoefficients.mapChain _ (ContinuousMap.id U) _ ≫
      RelativeCoefficients.mapChain _ (subtypeInclusion U) _
  rw [← RelativeCoefficients.mapChain_comp, ← RelativeCoefficients.mapChain_comp]
  rfl

/-- Evaluation of an included supported class is its original neighborhood evaluation
followed by the native local inclusion map. -/
theorem evaluate_inclusion (p : ℕ) (U K : Set M) (x : U) (hx : (x : M) ∈ K) (n : ℕ) :
    (evaluate (ModuleCat.of ℤ (ZMod p)) K (x : M) hx n).comp
        (inclusionMap (ModuleCat.of ℤ (ZMod p)) U K n) =
      (RelativeCoefficients.modNeighborhoodMap p U x n).comp
        (evaluate (ModuleCat.of ℤ (ZMod p)) (supportIn U K) x hx n) := by
  have h := congrArg (fun k => homologyLinearMap k n) (inclusion_evaluation_chain p U K x hx)
  simp only [homologyLinearMap_comp] at h
  exact h

end NoExoticSixSphere.SupportedRelativeHomology

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace E M]
  (U : Set M) (hU : IsOpen U) [ChartedSpace E U]

include hU

/-- The native neighborhood inclusion preserves the canonical nonzero local mod-two class. -/
theorem neighborhoodMap_manifoldClass (x : U) :
    RelativeCoefficients.modNeighborhoodMap 2 U x (n + 3)
        (ModTwoLocalClass.manifoldClass (E := E) n x) =
      ModTwoLocalClass.manifoldClass (E := E) n (x : M) :=
  ModTwoLocalClass.injective_map_manifoldClass (E := E) n x (x : M)
    (RelativeCoefficients.modNeighborhoodMap 2 U x (n + 3))
    (RelativeCoefficients.modNeighborhoodEquiv 2 (by decide) U hU x (n + 3)).injective

/-- An actual fundamental relative class in an open neighborhood remains fundamental
when included into the original manifold. This does not assume or produce existence. -/
theorem IsFundamentalOn.inclusion {K : Set M} (hKU : K ⊆ U)
    {c : Homology (ModuleCat.of ℤ (ZMod 2)) (supportIn U K) (n + 3)}
    (hc : IsFundamentalOn (E := E) n (supportIn U K) c) :
    IsFundamentalOn (E := E) n K (inclusionMap (ModuleCat.of ℤ (ZMod 2)) U K (n + 3) c) := by
  intro x hx
  let y : U := ⟨x, hKU hx⟩
  have he := LinearMap.congr_fun (evaluate_inclusion 2 U K y hx (n + 3)) c
  exact he.trans ((congrArg (RelativeCoefficients.modNeighborhoodMap 2 U y (n + 3))
    (hc y hx)).trans (neighborhoodMap_manifoldClass (E := E) n U hU y))

end NoExoticSixSphere.SupportedRelativeHomology
