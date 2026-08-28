import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonRealization
import Mathlib.Topology.Order.Compact

/-!
# Realizing continuous polygon families as unit-interval paths

The energy bound is obtained for the finite polygon family. No energy
regularity of a continuous path before replacement is assumed.
-/

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization VertexSpace

variable {n m : ℕ} {X : Type*} [TopologicalSpace X]

noncomputable def realizedFamily (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (p : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible a b m) :
    C(I × X, symplecticSubgroup n) :=
  (family a b τ).comp {
    toFun q := (⟨p q.2, hp q.2⟩, (q.1 : ℝ))
    continuous_toFun := by
      have hv : Continuous (fun q : I × X ↦ (⟨p q.2, hp q.2⟩ : admissible a b m)) :=
        (p.continuous.comp continuous_snd).subtype_mk _
      have ht : Continuous (fun q : I × X ↦ (q.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      exact hv.prodMk ht }

theorem realizedFamily_zero (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0)
    (p : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible a b m) (x : X) :
    realizedFamily a b τ p hp (0, x) = a := by
  change path a b τ (p x) 0 = a
  rw [← hzero]
  exact path_start a b τ hτ (hp x)

theorem realizedFamily_one (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hone : τ (Fin.last (m + 1)) = 1)
    (p : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible a b m) (x : X) :
    realizedFamily a b τ p hp (1, x) = b := by
  change path a b τ (p x) 1 = b
  rw [← hone]
  exact path_end a b τ hτ (hp x)

theorem exists_family_energy_bound [CompactSpace X]
    (a b : symplecticSubgroup n) (τ : Fin (m + 2) → ℝ)
    (p : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible a b m) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x, energy a b τ (p x) ≤ E := by
  have hE : Continuous (fun x ↦ energy a b τ (p x)) :=
    (contMDiffOn_energy a b τ).continuousOn.comp_continuous p.continuous hp
  obtain ⟨E, hE⟩ := (isCompact_range hE).bddAbove
  exact ⟨max E 0, le_max_right _ _, fun x ↦ (hE ⟨x, rfl⟩).trans (le_max_left _ _)⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
