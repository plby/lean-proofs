import Wikipedia.NoExoticSixSphere.RelativeModTwoCapAbsolute
import Wikipedia.NoExoticSixSphere.ModTwoDualFunctor

/-!
# Extension of actual cohomology supports

Supported cohomology is the actual relative cohomology of the complement.
As supports grow, the original identity maps of pairs act by cochain
precomposition. These maps form the directed system for compact supports.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X : Type} [TopologicalSpace X]

/-- The original relative cochain complex of the support complement. -/
abbrev complex (K : Set X) := RelativeModTwoCochains.complex Kᶜ

/-- Actual relative cohomology with the specified support. -/
abbrev Cohomology (K : Set X) (p : ℕ) := (complex K).homology p

/-- Extension of support on the original cochains. -/
def extendCochain {K L : Set X} (h : K ⊆ L) : complex K ⟶ complex L :=
  ModTwoDualComplex.map (SupportedRelativeHomology.restrictChain (ModuleCat.of ℤ ℤ) h)

theorem extendCochain_refl (K : Set X) :
    extendCochain (Set.Subset.refl K) = 𝟙 (complex K) := by
  unfold extendCochain
  rw [SupportedRelativeHomology.restrictChain_refl, ModTwoDualComplex.map_id]

theorem extendCochain_trans {K L N : Set X} (hKL : K ⊆ L) (hLN : L ⊆ N) :
    extendCochain (hKL.trans hLN) = extendCochain hKL ≫ extendCochain hLN := by
  unfold extendCochain
  rw [SupportedRelativeHomology.restrictChain_trans, ModTwoDualComplex.map_comp]

/-- The actual map on cohomology obtained by extending support. -/
abbrev extend {K L : Set X} (h : K ⊆ L) (p : ℕ) : Cohomology K p →ₗ[ℤ] Cohomology L p :=
  (HomologicalComplex.homologyMap (extendCochain h) p).hom

theorem extend_refl (K : Set X) (p : ℕ) :
    extend (Set.Subset.refl K) p = LinearMap.id := by
  change (HomologicalComplex.homologyMap (extendCochain (Set.Subset.refl K)) p).hom = _
  rw [extendCochain_refl, HomologicalComplex.homologyMap_id]
  rfl

theorem extend_trans {K L N : Set X} (hKL : K ⊆ L) (hLN : L ⊆ N) (p : ℕ) :
    extend (hKL.trans hLN) p = (extend hLN p).comp (extend hKL p) := by
  change (HomologicalComplex.homologyMap (extendCochain (hKL.trans hLN)) p).hom = _
  rw [extendCochain_trans, HomologicalComplex.homologyMap_comp]
  rfl

/-- Extension of support is exactly the original pair-map pullback. -/
theorem extend_eq_pullback {K L : Set X} (h : K ⊆ L) (p : ℕ) :
    extend h p = RelativeModTwoCochains.cohomologyPullback (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) Lᶜ Kᶜ from fun _ hx hy => hx (h hy)) p := rfl

end NoExoticSixSphere.SupportedModTwoCohomology
