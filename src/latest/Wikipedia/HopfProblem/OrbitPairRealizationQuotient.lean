import Wikipedia.HopfProblem.OrbitPairRealizationColimit

/-!
# The characteristic-simplex quotient map onto native realization

The source is the topological disjoint union of actual geometric simplices,
indexed by all simplices of the simplicial set. Its projection onto
mathlib's realization is proved surjective and coinducing.
-/

noncomputable section

open CategoryTheory Simplicial Topology

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable (S : SSet)

abbrev Parameters := Σ a : (Σ n : ℕ, S _⦋n⦌), Simplex a.1

def projection : C(Parameters S, SSet.toTop.obj S) where
  toFun a := characteristic S a.1.1 a.1.2 a.2
  continuous_toFun := continuous_sigma (fun a ↦ (characteristic S a.1 a.2).continuous)

theorem projection_apply (n : ℕ) (x : S _⦋n⦌) (t : Simplex n) :
    projection S ⟨⟨n, x⟩, t⟩ = characteristic S n x t := rfl

theorem projection_surjective : Function.Surjective (projection S) := by
  intro y
  obtain ⟨n, x, t, ht⟩ := exists_characteristic S y
  exact ⟨⟨⟨n, x⟩, t⟩, ht⟩

theorem projection_isQuotientMap : IsQuotientMap (projection S) := by
  rw [isQuotientMap_iff]
  refine ⟨.of_isOpen_preimage_iff_isOpen (fun U ↦ ?_), projection_surjective S⟩
  rw [isOpen_sigma_iff, isOpen_iff_characteristic]
  constructor
  · intro h n x
    exact h ⟨n, x⟩
  · intro h a
    exact h a.1 a.2

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
