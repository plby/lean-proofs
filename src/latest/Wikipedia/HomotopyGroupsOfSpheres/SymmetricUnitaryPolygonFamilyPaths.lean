import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonRealization
import Mathlib.Topology.Order.Compact

/-!
# Continuous path families from symmetric determinant-one polygons

The realized family has the prescribed endpoints. Compact parameter families
have a finite energy bound after polygonal replacement; no regularity of an
original continuous path is assumed here.
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ} {X : Type*} [TopologicalSpace X]

def realizedFamily (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (p : C(X, VertexSpace.Space N m))
    (hp : ∀ x, p x ∈ admissible a b m) : C(I × X, SpecialSpace N) :=
  (family a b τ hτ).comp {
    toFun q := (⟨p q.2, hp q.2⟩, (q.1 : ℝ))
    continuous_toFun := by
      have hv : Continuous (fun q : I × X ↦ (⟨p q.2, hp q.2⟩ : admissible a b m)) :=
        (p.continuous.comp continuous_snd).subtype_mk _
      have ht : Continuous (fun q : I × X ↦ (q.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      exact hv.prodMk ht }

theorem realizedFamily_zero (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0)
    (p : C(X, VertexSpace.Space N m))
    (hp : ∀ x, p x ∈ admissible a b m) (x : X) :
    realizedFamily a b τ hτ p hp (0, x) = a := by
  change path a b τ hτ (p x) (hp x) 0 = a
  rw [← hzero]
  exact path_start a b τ hτ (p x) (hp x)

theorem realizedFamily_one (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hone : τ (Fin.last (m + 1)) = 1)
    (p : C(X, VertexSpace.Space N m))
    (hp : ∀ x, p x ∈ admissible a b m) (x : X) :
    realizedFamily a b τ hτ p hp (1, x) = b := by
  change path a b τ hτ (p x) (hp x) 1 = b
  rw [← hone]
  exact path_end a b τ hτ (p x) (hp x)

theorem exists_family_energy_bound [CompactSpace X]
    (a b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (p : C(X, VertexSpace.Space N m)) (hp : ∀ x, p x ∈ admissible a b m) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x, energy a b τ (p x) ≤ E := by
  have hE : Continuous (fun x ↦ energy a b τ (p x)) :=
    (continuousOn_energy a b τ).comp_continuous p.continuous hp
  obtain ⟨E, hE⟩ := (isCompact_range hE).bddAbove
  exact ⟨max E 0, le_max_right _ _, fun x ↦ (hE ⟨x, rfl⟩).trans (le_max_left _ _)⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
