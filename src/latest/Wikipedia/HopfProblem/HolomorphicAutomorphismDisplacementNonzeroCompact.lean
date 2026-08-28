import Mathlib.Order.Filter.Finite
import Mathlib.Topology.MetricSpace.Sequences

/-!
# A fixed-label convergent subsequence in a finite compact family

For a sequence whose points lie in finitely many labelled compact sets,
one can keep the label constant and extract a convergent subsequence in
that same compact set. The index type needs no topology or nonemptiness
assumption.
-/

open Filter Set
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement

/-- Pass to one fixed compact-set label and a convergent subsequence,
retaining a strictly increasing map to the original sequence indices. -/
theorem exists_fixed_index_tendsto_subseq {ι E : Type*} [Finite ι]
    [PseudoMetricSpace E] (K : ι → Set E) (hK : ∀ i, IsCompact (K i))
    (idx : ℕ → ι) (z : ℕ → E) (hz : ∀ n, z n ∈ K (idx n)) :
    ∃ i, ∃ z0 ∈ K i, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ (∀ n, idx (φ n) = i) ∧ Tendsto (z ∘ φ) atTop (𝓝 z0) := by
  have hfrequent : ∃ i, ∃ᶠ n in atTop, idx n = i :=
    frequently_exists.mp (Frequently.of_forall fun n => ⟨idx n, rfl⟩)
  obtain ⟨i, hi⟩ := hfrequent
  obtain ⟨ψ, hψ, hidx⟩ := extraction_of_frequently_atTop hi
  have hmem : ∀ n, z (ψ n) ∈ K i := by
    intro n
    simpa only [hidx n] using hz (ψ n)
  obtain ⟨z0, hz0, χ, hχ, hlim⟩ := (hK i).tendsto_subseq hmem
  exact ⟨i, z0, hz0, ψ ∘ χ, hψ.comp hχ, fun n => hidx (χ n), hlim⟩

end Wikipedia.HopfProblem.HolomorphicAutomorphism.Displacement
