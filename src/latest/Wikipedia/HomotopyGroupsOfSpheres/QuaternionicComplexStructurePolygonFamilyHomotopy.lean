import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonFamilyPaths

/-!
# Polygon homotopies realize as relative path-family homotopies

The entire path stays in the complex-structure locus. Both endpoint slices
and every protected parameter remain fixed throughout the realized homotopy.
-/

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures ComplexStructureVertices

variable {n m : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def realizedFamilyHomotopy
    (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (p q : C(X, ComplexStructureVertices.Space n m)) (hp : ∀ x, p x ∈ admissible a b m)
    (hq : ∀ x, q x ∈ admissible a b m) (S : Set X) (F : p.HomotopyRel q S)
    (hF : ∀ r x, F (r, x) ∈ admissible a b m) :
    (realizedFamily a b τ hτ p hp).HomotopyRel (realizedFamily a b τ hτ q hq)
      {v | v.1 = 0 ∨ v.1 = 1 ∨ v.2 ∈ S} where
  toContinuousMap := (family a b τ hτ).comp {
    toFun z := (⟨F (z.1, z.2.2), hF z.1 z.2.2⟩, (z.2.1 : ℝ))
    continuous_toFun := by
      have hv : Continuous (fun z : I × (I × X) ↦
          (⟨F (z.1, z.2.2), hF z.1 z.2.2⟩ : admissible a b m)) :=
        (F.continuous.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).subtype_mk _
      have ht : Continuous (fun z : I × (I × X) ↦ (z.2.1 : ℝ)) :=
        continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
      exact hv.prodMk ht }
  map_zero_left z := by
    apply toSymplectic_injective
    change toSymplectic (path a b τ hτ (F (0, z.2)) (hF 0 z.2) (z.1 : ℝ)) =
      toSymplectic (path a b τ hτ (p z.2) (hp z.2) (z.1 : ℝ))
    rw [path_toSymplectic, path_toSymplectic, F.apply_zero]
  map_one_left z := by
    apply toSymplectic_injective
    change toSymplectic (path a b τ hτ (F (1, z.2)) (hF 1 z.2) (z.1 : ℝ)) =
      toSymplectic (path a b τ hτ (q z.2) (hq z.2) (z.1 : ℝ))
    rw [path_toSymplectic, path_toSymplectic, F.apply_one]
  prop' r z hz := by
    rcases z with ⟨t, x⟩
    change path a b τ hτ (F (r, x)) (hF r x) (t : ℝ) = path a b τ hτ (p x) (hp x) (t : ℝ)
    rcases hz with ht | ht | hx
    · change t = 0 at ht
      subst t
      change path a b τ hτ (F (r, x)) (hF r x) 0 = path a b τ hτ (p x) (hp x) 0
      rw [← hzero, path_start, path_start]
    · change t = 1 at ht
      subst t
      change path a b τ hτ (F (r, x)) (hF r x) 1 = path a b τ hτ (p x) (hp x) 1
      rw [← hone, path_end, path_end]
    · apply toSymplectic_injective
      have he : F (r, x) = p x := F.prop r x hx
      rw [path_toSymplectic, path_toSymplectic, he]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
