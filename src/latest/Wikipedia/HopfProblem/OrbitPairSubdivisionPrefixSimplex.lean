import Wikipedia.HopfProblem.OrbitPairSubdivisionSortedWeights

/-!
# Native prefix simplices and explicit barycentric preimages

A permutation of the original vertices determines a simplex in the native
subdivision: its successive vertices are the nonempty prefixes. The sorted
coordinate weights on this simplex reconstruct the original coordinates.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz RealizationSimplex

variable {n : ℕ}

def prefixChain (p : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) where
  finset := ((Finset.Iic j).map p.toEmbedding).map ⟨ULift.up, ULift.up_injective⟩
  nonempty := ⟨ULift.up (p j), by simp⟩
  comparable a b := le_total a.val b.val

theorem prefixChain_mem (p : Equiv.Perm (Fin (n + 1))) (j i : Fin (n + 1)) :
    ULift.up i ∈ (prefixChain.{u} p j).finset ↔ p.symm i ≤ j := by
  simp [prefixChain]

theorem prefixChain_card (p : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    (prefixChain.{u} p j).finset.card = j.val + 1 := by
  simp [prefixChain]

theorem prefixChain_monotone (p : Equiv.Perm (Fin (n + 1))) :
    Monotone (prefixChain.{u} p) := by
  intro j l hjl
  change (prefixChain p j).finset ⊆ (prefixChain p l).finset
  rintro ⟨i⟩ hi
  exact (prefixChain_mem p l i).mpr (((prefixChain_mem p j i).mp hi).trans hjl)

def prefixSimplex (p : Equiv.Perm (Fin (n + 1))) :
    (SimplexCategory.sd.{u}.obj ⦋n⦌) _⦋n⦌ :=
  (prefixChain_monotone.{u} p).functor

theorem chainWeight_prefix_sorted (p : Equiv.Perm (Fin (n + 1)))
    (r : Fin (n + 1) → ℝ) (hr : Antitone r) (h0 : ∀ j, 0 ≤ r j)
    (h1 : ∑ j, r j = 1) (j : Fin (n + 1)) :
    chainWeight (prefixChain.{u} p) (sortedWeights r hr h0 h1) j = coordinateGap r j := by
  change (((j.val + 1 : ℕ) : ℝ) * coordinateGap r j) / (prefixChain p j).finset.card = _
  rw [prefixChain_card]
  have hc : ((j.val + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  field_simp

theorem chainCoordinate_prefix_sorted (p : Equiv.Perm (Fin (n + 1)))
    (r : Fin (n + 1) → ℝ) (hr : Antitone r) (h0 : ∀ j, 0 ≤ r j)
    (h1 : ∑ j, r j = 1) (i : Fin (n + 1)) :
    chainCoordinate (prefixChain.{u} p) (sortedWeights r hr h0 h1) i = r (p.symm i) := by
  classical
  unfold chainCoordinate
  simp_rw [prefixChain_mem, chainWeight_prefix_sorted]
  exact coordinateGap_tail r (p.symm i)

theorem barycentricMap_prefixSimplex (p : Equiv.Perm (Fin (n + 1)))
    (r : Fin (n + 1) → ℝ) (hr : Antitone r) (h0 : ∀ j, 0 ≤ r j)
    (h1 : ∑ j, r j = 1) (i : Fin (n + 1)) :
    barycentricMap n (characteristic (SimplexCategory.sd.{u}.obj ⦋n⦌) n (prefixSimplex p)
      (sortedWeights r hr h0 h1)) i = r (p.symm i) :=
  (barycentricMap_characteristic_apply n n (prefixSimplex p) (sortedWeights r hr h0 h1) i).trans
    (chainCoordinate_prefix_sorted p r hr h0 h1 i)

end Wikipedia.HopfProblem.OrbitPair.Subdivision
