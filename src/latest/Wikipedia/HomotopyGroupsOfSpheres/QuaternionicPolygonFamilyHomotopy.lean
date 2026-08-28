import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonFamilyPaths

/-!
# Polygon-family homotopies realize as homotopies of actual paths

The path endpoints and the protected parameter set remain fixed at every
homotopy time. Admissibility is required throughout the vertex homotopy.
-/

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization VertexSpace

variable {n m : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def realizedFamilyHomotopy
    (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (p q : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible a b m)
    (hq : ∀ x, q x ∈ admissible a b m) (S : Set X) (F : p.HomotopyRel q S)
    (hF : ∀ r x, F (r, x) ∈ admissible a b m) :
    (realizedFamily a b τ p hp).HomotopyRel (realizedFamily a b τ q hq)
      {v | v.1 = 0 ∨ v.1 = 1 ∨ v.2 ∈ S} where
  toContinuousMap := (family a b τ).comp {
    toFun z := (⟨F (z.1, z.2.2), hF z.1 z.2.2⟩, (z.2.1 : ℝ))
    continuous_toFun := by
      have hv : Continuous (fun z : I × (I × X) ↦
          (⟨F (z.1, z.2.2), hF z.1 z.2.2⟩ : admissible a b m)) :=
        (F.continuous.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).subtype_mk _
      have ht : Continuous (fun z : I × (I × X) ↦ (z.2.1 : ℝ)) :=
        continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
      exact hv.prodMk ht }
  map_zero_left v := by
    change path a b τ (F (0, v.2)) (v.1 : ℝ) = path a b τ (p v.2) (v.1 : ℝ)
    rw [F.apply_zero]
  map_one_left v := by
    change path a b τ (F (1, v.2)) (v.1 : ℝ) = path a b τ (q v.2) (v.1 : ℝ)
    rw [F.apply_one]
  prop' r v hv := by
    rcases v with ⟨t, x⟩
    change path a b τ (F (r, x)) (t : ℝ) = path a b τ (p x) (t : ℝ)
    rcases hv with ht | ht | hx
    · change t = 0 at ht
      subst t
      change path a b τ (F (r, x)) 0 = path a b τ (p x) 0
      rw [← hzero, path_start a b τ hτ (hF r x), path_start a b τ hτ (hp x)]
    · change t = 1 at ht
      subst t
      change path a b τ (F (r, x)) 1 = path a b τ (p x) 1
      rw [← hone, path_end a b τ hτ (hF r x), path_end a b τ hτ (hp x)]
    · have he : F (r, x) = p x := F.prop r x hx
      rw [he]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
