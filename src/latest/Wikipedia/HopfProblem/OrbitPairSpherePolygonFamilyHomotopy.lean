import Wikipedia.HopfProblem.OrbitPairSpherePolygonFamilyPaths

/-!
# Realizing polygon homotopies as homotopies of actual sphere paths

The path endpoints and every protected parameter remain fixed at all homotopy
times. The only geometric input is admissibility throughout the given vertex
homotopy. The result is an actual jointly continuous two-parameter homotopy.
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace

variable {n m : ℕ} {X : Type*} [TopologicalSpace X]

def realizedFamilyHomotopy (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (p q : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible (costDomain n) a b m)
    (hq : ∀ x, q x ∈ admissible (costDomain n) a b m) (S : Set X) (F : p.HomotopyRel q S)
    (hF : ∀ r x, F (r, x) ∈ admissible (costDomain n) a b m) :
    (realizedFamily a b τ hτ p hp).HomotopyRel (realizedFamily a b τ hτ q hq)
      {v | v.1 = 0 ∨ v.1 = 1 ∨ v.2 ∈ S} where
  toContinuousMap := (family a b τ hτ).comp {
    toFun z := (⟨F (z.1, z.2.2), hF z.1 z.2.2⟩, (z.2.1 : ℝ))
    continuous_toFun := by
      have hv : Continuous (fun z : I × (I × X) =>
          (⟨F (z.1, z.2.2), hF z.1 z.2.2⟩ : admissible (costDomain n) a b m)) :=
        (F.continuous.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).subtype_mk _
      have ht : Continuous (fun z : I × (I × X) => (z.2.1 : ℝ)) :=
        continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
      exact hv.prodMk ht }
  map_zero_left v := by
    apply Subtype.ext
    change ambientPath a b τ (F (0, v.2)) (v.1 : ℝ) = ambientPath a b τ (p v.2) (v.1 : ℝ)
    rw [F.apply_zero]
  map_one_left v := by
    apply Subtype.ext
    change ambientPath a b τ (F (1, v.2)) (v.1 : ℝ) = ambientPath a b τ (q v.2) (v.1 : ℝ)
    rw [F.apply_one]
  prop' r v hv := by
    rcases v with ⟨t, x⟩
    apply Subtype.ext
    change ambientPath a b τ (F (r, x)) (t : ℝ) = ambientPath a b τ (p x) (t : ℝ)
    rcases hv with ht | ht | hx
    · change t = 0 at ht
      subst t
      change ambientPath a b τ (F (r, x)) 0 = ambientPath a b τ (p x) 0
      rw [← hzero, ambientPath_before a b τ hτ _ le_rfl,
        ambientPath_before a b τ hτ _ le_rfl]
    · change t = 1 at ht
      subst t
      change ambientPath a b τ (F (r, x)) 1 = ambientPath a b τ (p x) 1
      rw [← hone, ambientPath_after a b τ hτ (hF r x) le_rfl,
        ambientPath_after a b τ hτ (hp x) le_rfl]
    · have he : F (r, x) = p x := F.prop r x hx
      rw [he]

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
