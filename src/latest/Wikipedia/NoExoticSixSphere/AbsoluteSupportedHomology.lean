import Wikipedia.NoExoticSixSphere.CoefficientChainPresentation
import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology

/-!
# Original absolute homology and support in the whole space

The native singular chains of an empty space vanish because no singular
simplex exists. The projection to the relative complex of the empty
subspace is therefore an isomorphism, not merely a quasi-isomorphism.
This identifies support in the whole space with the original absolute
homology, retaining the projection map and all its support restrictions.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem FirstHurewicz SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.CoefficientChains

variable (A : ModuleCat.{0} ℤ) (X : Type) [TopologicalSpace X] [IsEmpty X]

/-- No simplex exists in an empty space, so every native coefficient chain is zero. -/
theorem empty_subsingleton (n : ℕ) : Subsingleton (Chains A X n) := by
  have hz : ∀ c : Chains A X n, c = 0 := by
    intro c
    obtain ⟨f, rfl⟩ := fromFinsupp_surjective A X n c
    have hf : f = 0 := by
      apply Finsupp.ext
      intro σ
      exact isEmptyElim (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))))
    rw [hf, map_zero]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end NoExoticSixSphere.CoefficientChains

namespace NoExoticSixSphere.RelativeCoefficients

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X]

/-- The actual chain inclusion of the empty subspace is zero. -/
theorem inclusion_empty_eq_zero : inclusion A (∅ : Set X) = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  have hc : c = 0 := (CoefficientChains.empty_subsingleton A (∅ : Set X) n).elim c 0
  rw [hc, map_zero]
  rfl

/-- The original projection to the relative complex of the empty subspace is an isomorphism. -/
theorem projection_empty_isIso : IsIso (projection A (∅ : Set X)) := by
  change IsIso (cokernel.π (inclusion A (∅ : Set X)))
  rw [inclusion_empty_eq_zero]
  infer_instance

end NoExoticSixSphere.RelativeCoefficients

namespace NoExoticSixSphere.SupportedRelativeHomology

variable (A : ModuleCat.{0} ℤ) {X : Type} [TopologicalSpace X]

/-- The original map from absolute homology to homology with the specified support. -/
abbrev fromAbsolute (K : Set X) (n : ℕ) :
    (coefficientComplex A X).homology n →ₗ[ℤ] Homology A K n :=
  homologyLinearMap (RelativeCoefficients.projection A Kᶜ) n

/-- Support restriction commutes with the original absolute-to-relative map. -/
theorem restrict_fromAbsolute {K L : Set X} (h : K ⊆ L) (n : ℕ) :
    (restrict A h n).comp (fromAbsolute A L n) = fromAbsolute A K n := by
  have he := RelativeCoefficients.projection_mapChain A (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from fun _ hy hx => hy (h hx))
  rw [RelativeCoefficients.spaceMap_id, Category.id_comp] at he
  exact (homologyLinearMap_comp _ _ n).symm.trans (congrArg (fun f => homologyLinearMap f n) he)

/-- The original whole-support projection gives an actual absolute homology equivalence. -/
def absoluteEquiv (n : ℕ) :
    (coefficientComplex A X).homology n ≃ₗ[ℤ] Homology A (Set.univ : Set X) n := by
  have : IsIso (RelativeCoefficients.projection A ((Set.univ : Set X)ᶜ)) := by
    rw [Set.compl_univ]
    exact RelativeCoefficients.projection_empty_isIso A
  exact ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (asIso (RelativeCoefficients.projection A ((Set.univ : Set X)ᶜ)))).toLinearEquiv

theorem absoluteEquiv_toLinearMap (n : ℕ) :
    (absoluteEquiv (X := X) A n).toLinearMap = fromAbsolute A Set.univ n := rfl

end NoExoticSixSphere.SupportedRelativeHomology
