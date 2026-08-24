import ErdosProblems.Erdos360.FiberCoherence

open scoped Pointwise

namespace Erdos360

/-- Pull the common dense quotient fibre back to the original cyclic group.
If its subgroup is on the cube-root scale, the existing dense-coset covering
lemma produces a long-progression cover of the entire cyclic set. -/
theorem zmodQuotRem_common_dense_large_subgroup_cover
    {m d : ℕ} [NeZero d] [NeZero (m * d)]
    (D : Finset (ZMod (m * d))) (hm : 0 < m)
    (hA : (firstCoordinateSet (zmodQuotRemImage m d D)).Nonempty)
    (hAzero : 0 ∈ firstCoordinateSet (zmodQuotRemImage m d D))
    (hAcard : 6 ≤ (firstCoordinateSet (zmodQuotRemImage m d D)).card)
    (hgcd : (firstCoordinateSet (zmodQuotRemImage m d D)).gcd
      (fun n ↦ (n : ℤ)) = 1)
    (hsmall : 2 * (zmodQuotRemImage m d D +
        zmodQuotRemImage m d D).card <
      5 * (zmodQuotRemImage m d D).card) :
    ∃ base ∈ firstCoordinateSet (zmodQuotRemImage m d D),
      ∃ H : AddSubgroup (ZMod d),
        ContainedInAddCoset H
            (coordinateFiber (zmodQuotRemImage m d D) base) ∧
          2 * Nat.card H <
            3 * (coordinateFiber (zmodQuotRemImage m d D) base).card ∧
          (∀ a ∈ firstCoordinateSet (zmodQuotRemImage m d D),
            (coordinateFiber (zmodQuotRemImage m d D) a).card ≤
              (coordinateFiber (zmodQuotRemImage m d D) base).card) ∧
          (∀ a ∈ firstCoordinateSet (zmodQuotRemImage m d D),
            ContainedInAddCoset H
              (coordinateFiber (zmodQuotRemImage m d D) a)) ∧
          (D.card ≤ (Nat.card H) ^ 3 →
            ∃ mass : ℕ, 2 * mass < 3 * (D + D).card ∧
              HasLongProgressionCover (shiftedZmodValues D) mass) := by
  classical
  obtain ⟨base, hbase, H, hbaseCos, hHdense, hbaseMax, hAll⟩ :=
    exists_common_dense_coset_of_small_doubling
      (zmodQuotRemImage m d D) hA hAzero hAcard hgcd hsmall
  refine ⟨base, hbase, H, hbaseCos, hHdense, hbaseMax, hAll, ?_⟩
  intro hlarge
  let C := cyclicRemainderFiber D base
  let K := H.map (zmodQuotientEmbedding m d)
  have hC : C.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcardZero :
        (coordinateFiber (zmodQuotRemImage m d D) base).card = 0 := by
      rw [← card_cyclicRemainderFiber hm D base]
      simpa [C] using congrArg Finset.card hEmpty
    have hfiberNe := coordinateFiber_nonempty_iff.mpr hbase
    exact (Finset.card_pos.mpr hfiberNe).ne' hcardZero
  have hCD : C ⊆ D := by
    intro z hz
    exact (Finset.mem_filter.mp hz).1
  have hKcos : ContainedInAddCoset K C := by
    exact cyclicRemainderFiber_containedIn_map D base H hbaseCos
  have hKdense : 2 * Nat.card K < 3 * C.card := by
    rw [show Nat.card K = Nat.card H by
      exact natCard_map_zmodQuotientEmbedding hm H]
    rw [card_cyclicRemainderFiber hm D base]
    exact hHdense
  have hKlarge : D.card ≤ (Nat.card K) ^ 3 := by
    rw [show Nat.card K = Nat.card H by
      exact natCard_map_zmodQuotientEmbedding hm H]
    exact hlarge
  exact dense_coset_large_subgroup_cover hC hCD hKcos hKdense hKlarge

end Erdos360
