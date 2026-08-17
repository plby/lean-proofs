/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos223.CarrierOddExactCore

/-!
# Stable exact cores for odd-dimensional diameter graphs

A fixed aligned family of retained cross-unit triples cuts out the retained
vertices complete to every foreign seed triple.  This exact core lies on a
weak odd carrier for `p ≥ 4`, and its complement has an explicit stability
error bound.
-/

open scoped SimpleGraph

namespace Erdos223.CarrierOdd

noncomputable section

variable {p : ℕ} {epsilon : ℝ} {A : Finset (Point (2 * p + 1))}

def stableExactCoreVertices
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A}) :
    Finset {q : Point (2 * p + 1) // q ∈ A} := by
  classical
  exact Finset.univ.filter fun q ↦
    q ∉ P.exceptional ∧ ∀ j, j ≠ P.color q → ∀ a,
      (diameterGraph A).Adj q (x j a)

def stableExactCore
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A}) :
    Finset (Point (2 * p + 1)) :=
  (stableExactCoreVertices P x).map
    ⟨Subtype.val, Subtype.val_injective⟩

lemma stableExactCore_subset
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A}) :
    stableExactCore P x ⊆ A := by
  intro q hq
  obtain ⟨v, _hv, rfl⟩ := Finset.mem_map.mp hq
  exact v.2

def stableExactCorePart
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A})
    (q : {q : Point (2 * p + 1) // q ∈ stableExactCore P x}) : Fin p :=
  P.color ⟨q.1, stableExactCore_subset P x q.2⟩

lemma mem_stableExactCoreVertices_of_mem_core
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A})
    (q : {q : Point (2 * p + 1) // q ∈ stableExactCore P x}) :
    (⟨q.1, stableExactCore_subset P x q.2⟩ :
      {q : Point (2 * p + 1) // q ∈ A}) ∈ stableExactCoreVertices P x := by
  obtain ⟨v, hv, heq⟩ := Finset.mem_map.mp q.2
  have hveq : v = ⟨q.1, stableExactCore_subset P x q.2⟩ := by
    apply Subtype.ext
    exact heq
  simpa [hveq] using hv

/-- The vertices complete to a fixed aligned seed family form an exact
cross-unit core and hence, for `p ≥ 4`, lie on one weak odd carrier. -/
theorem isWeakCarrierSet_stableExactCore
    (hp : 4 ≤ p)
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A})
    (hinj : ∀ i, Function.Injective (x i))
    (hcross : ∀ {i j : Fin p}, i ≠ j → ∀ a b,
      (diameterGraph A).Adj (x i a) (x j b)) :
    IsWeakCarrierSet (p := p) (stableExactCore P x) := by
  let y : Fin p → Fin 3 → Point (2 * p + 1) := fun i a ↦ (x i a).1
  apply isWeakCarrierSet_of_exact_cross_unit_triples_four hp
    (stableExactCorePart P x) y
  · intro i a b hab
    apply hinj i
    exact Subtype.ext hab
  · intro i j hij a b
    exact (diameterGraph_adj A (x i a) (x j b)).1 (hcross hij a b)
  · intro q j hj a
    let qA : {q : Point (2 * p + 1) // q ∈ A} :=
      ⟨q.1, stableExactCore_subset P x q.2⟩
    have hqmem := mem_stableExactCoreVertices_of_mem_core P x q
    have hqprop := (Finset.mem_filter.mp hqmem).2
    have hj' : j ≠ P.color qA := by simpa [stableExactCorePart, qA] using hj
    exact (diameterGraph_adj A qA (x j a)).1 (hqprop.2 j hj' a)

/-- If the seed triples are aligned with the retained color classes, the
exact core loses at most the exceptional set and the union of the `3p`
retained nonneighbor sets of the seed vertices. -/
theorem card_stableExactCore_lower
    (P : Stability.StablePartition (diameterGraph A) p epsilon)
    (x : Fin p → Fin 3 → {q : Point (2 * p + 1) // q ∈ A})
    (hxretained : ∀ i a,
      x i a ∈ Stability.retainedFiber P.color P.exceptional i) :
    A.card ≤ (stableExactCore P x).card +
      (3 * p + 1) * ⌈epsilon * (A.card : ℝ)⌉₊ := by
  classical
  let B : ℕ := ⌈epsilon * (A.card : ℝ)⌉₊
  let Bad : Finset {q : Point (2 * p + 1) // q ∈ A} :=
    Finset.univ.biUnion fun ia : Fin p × Fin 3 ↦
      Stability.retainedCrossNonneighbors (diameterGraph A)
        P.color P.exceptional (x ia.1 ia.2)
  have hseedColor (i : Fin p) (a : Fin 3) : P.color (x i a) = i :=
    (Stability.mem_retainedFiber P.color P.exceptional i (x i a)).mp
      (hxretained i a) |>.1
  have hbadOne (i : Fin p) (a : Fin 3) :
      (Stability.retainedCrossNonneighbors (diameterGraph A)
        P.color P.exceptional (x i a)).card ≤ B := by
    have hs := P.crossNonneighbors_small i (x i a) (hxretained i a)
    have hceil : epsilon * (A.card : ℝ) ≤ (B : ℝ) := by
      exact Nat.le_ceil (epsilon * (A.card : ℝ))
    have hceil' : epsilon * (Fintype.card
        {q : Point (2 * p + 1) // q ∈ A} : ℝ) ≤ (B : ℝ) := by
      simpa using hceil
    have hlt : ((Stability.retainedCrossNonneighbors (diameterGraph A)
        P.color P.exceptional (x i a)).card : ℝ) < (B : ℝ) :=
      hs.trans_le hceil'
    have hnat : (Stability.retainedCrossNonneighbors (diameterGraph A)
        P.color P.exceptional (x i a)).card < B := by exact_mod_cast hlt
    omega
  have hBad : Bad.card ≤ (p * 3) * B := by
    calc
      Bad.card ≤ ∑ ia ∈ (Finset.univ : Finset (Fin p × Fin 3)),
          (Stability.retainedCrossNonneighbors (diameterGraph A)
            P.color P.exceptional (x ia.1 ia.2)).card := Finset.card_biUnion_le
      _ ≤ ∑ _ia ∈ (Finset.univ : Finset (Fin p × Fin 3)), B := by
        exact Finset.sum_le_sum fun ia _ ↦ hbadOne ia.1 ia.2
      _ = (p * 3) * B := by simp
  have hExceptional : P.exceptional.card ≤ B := by
    have hceil : epsilon * (A.card : ℝ) ≤ (B : ℝ) := by
      exact Nat.le_ceil (epsilon * (A.card : ℝ))
    have hceil' : epsilon * (Fintype.card
        {q : Point (2 * p + 1) // q ∈ A} : ℝ) ≤ (B : ℝ) := by
      simpa using hceil
    have hlt : (P.exceptional.card : ℝ) < (B : ℝ) :=
      P.exceptional_small.trans_le hceil'
    have hnat : P.exceptional.card < B := by exact_mod_cast hlt
    omega
  let S : Finset {q : Point (2 * p + 1) // q ∈ A} :=
    Finset.univ \ (P.exceptional ∪ Bad)
  have hSsub : S ⊆ stableExactCoreVertices P x := by
    intro q hq
    have hqm := Finset.mem_sdiff.mp hq
    have hqnotE : q ∉ P.exceptional := fun hqE ↦
      hqm.2 (Finset.mem_union_left Bad hqE)
    change q ∈ Finset.univ.filter (fun q ↦
      q ∉ P.exceptional ∧ ∀ j, j ≠ P.color q → ∀ a,
        (diameterGraph A).Adj q (x j a))
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ q, hqnotE, ?_⟩
    intro j hj a
    by_contra hnot
    apply hqm.2
    apply Finset.mem_union_right P.exceptional
    simp only [Bad, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨(j, a), ?_⟩
    rw [Stability.mem_retainedCrossNonneighbors]
    refine ⟨hqnotE, ?_, ?_⟩
    · simpa [hseedColor j a] using hj
    · intro hadj
      exact hnot (((diameterGraph A).adj_comm _ _).mp hadj)
  have hScard : S.card ≤ (stableExactCoreVertices P x).card :=
    Finset.card_le_card hSsub
  have hUnionSub : P.exceptional ∪ Bad ⊆
      (Finset.univ : Finset {q : Point (2 * p + 1) // q ∈ A}) :=
    Finset.subset_univ _
  have hdecomp : S.card + (P.exceptional ∪ Bad).card = A.card := by
    change (Finset.univ \ (P.exceptional ∪ Bad)).card +
      (P.exceptional ∪ Bad).card = A.card
    rw [Finset.card_sdiff_of_subset hUnionSub, Finset.card_univ,
      Fintype.card_coe]
    exact Nat.sub_add_cancel (by
      simpa using Finset.card_le_card hUnionSub)
  have hUnion : (P.exceptional ∪ Bad).card ≤
      P.exceptional.card + Bad.card := Finset.card_union_le _ _
  have hcoreVertices : A.card ≤ (stableExactCoreVertices P x).card +
      P.exceptional.card + Bad.card := by omega
  have hcardMap : (stableExactCore P x).card =
      (stableExactCoreVertices P x).card := by
    simp [stableExactCore]
  rw [hcardMap]
  change A.card ≤ (stableExactCoreVertices P x).card + (3 * p + 1) * B
  have hid : (p * 3) * B + B = (3 * p + 1) * B := by ring
  omega

end

end Erdos223.CarrierOdd

