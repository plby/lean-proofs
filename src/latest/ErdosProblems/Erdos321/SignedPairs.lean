import Mathlib

namespace Erdos321

/-- Canonical signed coefficient vectors on `B`: choose a positive support `U`,
then a negative support `V` in its complement. -/
def disjointPairs (B : Finset ℕ) :
    Finset (Σ _ : Finset ℕ, Finset ℕ) :=
  B.powerset.sigma (fun U => (B \ U).powerset)

/-- There are exactly three choices (`-1,0,+1`) per element. -/
theorem card_disjointPairs (B : Finset ℕ) :
    (disjointPairs B).card = 3 ^ B.card := by
  rw [disjointPairs, Finset.card_sigma]
  simp_rw [Finset.card_powerset]
  have hsdiff : ∀ U ∈ B.powerset, (B \ U).card = B.card - U.card := by
    intro U hU
    exact Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hU)
  calc
    (∑ U ∈ B.powerset, 2 ^ (B \ U).card) =
        ∑ U ∈ B.powerset, 2 ^ (B.card - U.card) := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [hsdiff U hU]
    _ = 3 ^ B.card := by
      simpa using (Finset.sum_pow_mul_eq_add_pow (R := ℕ) 1 2 B)

/-- Cancelling common elements from two subsets produces one of the canonical
`3^|B|` disjoint signed pairs. -/
theorem sdiff_pair_mem_disjointPairs {B U V : Finset ℕ}
    (hU : U ⊆ B) (hV : V ⊆ B) :
    Sigma.mk (U \ V) (V \ U) ∈ disjointPairs B := by
  rw [disjointPairs, Finset.mem_sigma]
  constructor
  · exact Finset.mem_powerset.mpr (Finset.sdiff_subset.trans hU)
  · rw [Finset.mem_powerset]
    intro a ha
    have haV : a ∈ V := (Finset.mem_sdiff.mp ha).1
    have haU : a ∉ U := (Finset.mem_sdiff.mp ha).2
    exact Finset.mem_sdiff.mpr ⟨hV haV, fun haUV => haU (Finset.mem_sdiff.mp haUV).1⟩

end Erdos321
