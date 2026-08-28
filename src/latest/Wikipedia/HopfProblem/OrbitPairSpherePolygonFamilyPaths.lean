import Wikipedia.HopfProblem.OrbitPairSpherePolygonRealization
import Mathlib.Topology.Order.Compact

/-!
# Realization of continuous sphere-polygon families

The vertex family gives a jointly continuous family of actual unit-interval
sphere paths with its fixed endpoints. Compact parameter spaces give a finite
bound on the polygon energy; no finite-energy assumption on an earlier
continuous path is made.
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace

variable {n m : ℕ} {X : Type*} [TopologicalSpace X]

def realizedFamily (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (p : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible (costDomain n) a b m) :
    C(I × X, Sphere n) :=
  (family a b τ hτ).comp {
    toFun q := (⟨p q.2, hp q.2⟩, (q.1 : ℝ))
    continuous_toFun := by
      have hv : Continuous (fun q : I × X =>
          (⟨p q.2, hp q.2⟩ : admissible (costDomain n) a b m)) :=
        (p.continuous.comp continuous_snd).subtype_mk _
      have ht : Continuous (fun q : I × X => (q.1 : ℝ)) :=
        continuous_subtype_val.comp continuous_fst
      exact hv.prodMk ht }

theorem realizedFamily_zero (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0)
    (p : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible (costDomain n) a b m) (x : X) :
    realizedFamily a b τ hτ p hp (0, x) = a := by
  change path a b τ hτ ⟨p x, hp x⟩ 0 = a
  rw [← hzero]
  exact path_start a b τ hτ _

theorem realizedFamily_one (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hone : τ (Fin.last (m + 1)) = 1)
    (p : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible (costDomain n) a b m) (x : X) :
    realizedFamily a b τ hτ p hp (1, x) = b := by
  change path a b τ hτ ⟨p x, hp x⟩ 1 = b
  rw [← hone]
  exact path_end a b τ hτ _

theorem exists_family_energy_bound [CompactSpace X] (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (p : C(X, Space n m)) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ x, energy a b τ (p x) ≤ E := by
  have hE := (continuous_energy a b τ).comp p.continuous
  obtain ⟨E, hE⟩ := (isCompact_range hE).bddAbove
  exact ⟨max E 0, le_max_right _ _, fun x => (hE ⟨x, rfl⟩).trans (le_max_left _ _)⟩

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
