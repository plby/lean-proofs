import Wikipedia.NoExoticSixSphere.ModTwoDualComplex

/-!
# Functoriality of the original mod-two dual maps

The actual precomposition maps preserve identities, reverse composition,
and carry a genuine chain isomorphism to a genuine cochain isomorphism.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.ModTwoDualComplex

variable {K L N : ChainComplex (ModuleCat.{0} ℤ) ℕ}

theorem map_id (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) : map (𝟙 K) = 𝟙 (complex K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  apply AddMonoidHom.ext
  intro c
  rfl

theorem map_comp (f : K ⟶ L) (g : L ⟶ N) : map (f ≫ g) = map g ≫ map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  apply AddMonoidHom.ext
  intro c
  rfl

/-- A genuine chain isomorphism gives the original contravariant cochain isomorphism. -/
def mapIso (e : K ≅ L) : complex L ≅ complex K where
  hom := map e.hom
  inv := map e.inv
  hom_inv_id := by rw [← map_comp, e.inv_hom_id, map_id]
  inv_hom_id := by rw [← map_comp, e.hom_inv_id, map_id]

end NoExoticSixSphere.ModTwoDualComplex
