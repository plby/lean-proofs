/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos88.LocalToPrescribed
import ErdosProblems.Erdos88.Switching

/-!
# KSSS Section 13: bounded windows to exact induced-edge counts

This module specializes the finite switching machinery to the unbiased
induced-edge statistic.  It proves every deterministic and finite-probability
step from the raw moment estimate of KSSS Lemma 13.4 to the local point lower
bound required for Erdős Problem 88.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos88
namespace Switching

noncomputable def edgeScore {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) : ℤ := inducedEdges G U

lemma edgeScore_eq_edgeCount {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (Fin n)) :
    edgeScore G U = (AKSGraph.edgeCount G U : ℤ) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  change (inducedEdges G U : ℤ) =
    ((G.edgeFinset.filter fun e ↦ e.toFinset ⊆ U).card : ℤ)
  exact_mod_cast inducedEdges_eq_card_filter G U

/-- Exact unbiased form of the switch increment (KSSS (4.12)): replacing
`y` by `z` changes the induced edge count by the difference of their degrees
into `U \ {y}`. -/
lemma switchIncrement_edgeScore {n : ℕ} (G : SimpleGraph (Fin n))
    {U : Finset (Fin n)} {y z : Fin n} (hy : y ∈ U) (hz : z ∉ U) :
    switchIncrement (edgeScore G) U y z =
      (AKSGraph.degreeInto G z (U.erase y) : ℤ) -
        (AKSGraph.degreeInto G y (U.erase y) : ℤ) := by
  let W : Finset (Fin n) :=
    @Finset.erase (Fin n) (instDecidableEqFin n) U y
  have hzErase : z ∉ W := by
    intro hzW
    apply hz
    exact Finset.mem_of_mem_erase (show z ∈ U.erase y from hzW)
  have hU : insert y W = U := by
    simpa only [W] using Finset.insert_erase hy
  have hswap : swapSubset U y z = insert z W := by
    classical
    ext w
    simp [swapSubset, W]
  have hzEdge :
      (AKSGraph.edgeCount G (insert z W) : ℤ) =
        (AKSGraph.edgeCount G W : ℤ) +
          (AKSGraph.degreeInto G z W : ℤ) := by
    exact_mod_cast AKSGraph.edgeCount_insert G z W hzErase
  have hyEdge :
      (AKSGraph.edgeCount G U : ℤ) =
        (AKSGraph.edgeCount G W : ℤ) +
          (AKSGraph.degreeInto G y W : ℤ) := by
    have hyInsert :
        (AKSGraph.edgeCount G (insert y W) : ℤ) =
          (AKSGraph.edgeCount G W : ℤ) +
            (AKSGraph.degreeInto G y W : ℤ) := by
      exact_mod_cast AKSGraph.edgeCount_insert G y W (by simpa [W])
    simpa only [hU] using hyInsert
  have hreplace := congrArg₂ (fun a b : ℤ ↦ a - b) hzEdge hyEdge
  rw [switchIncrement, edgeScore_eq_edgeCount, edgeScore_eq_edgeCount,
    hswap]
  change (AKSGraph.edgeCount G (insert z W) : ℤ) -
      (AKSGraph.edgeCount G U : ℤ) =
    (AKSGraph.degreeInto G z W : ℤ) -
      (AKSGraph.degreeInto G y W : ℤ)
  calc
    _ = (AKSGraph.edgeCount G W : ℤ) +
          (AKSGraph.degreeInto G z W : ℤ) -
        ((AKSGraph.edgeCount G W : ℤ) +
          (AKSGraph.degreeInto G y W : ℤ)) := hreplace
    _ = (AKSGraph.degreeInto G z W : ℤ) -
          (AKSGraph.degreeInto G y W : ℤ) := by ring

section SwitchingReservoir

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

private lemma card_filter_product_le_mul_of_fiber_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (p : α → β → Prop)
    [DecidablePred fun ab : α × β ↦ p ab.1 ab.2]
    [∀ a, DecidablePred (p a)] (b : ℕ)
    (h : ∀ a ∈ S, (T.filter (p a)).card ≤ b) :
    ((S ×ˢ T).filter fun ab ↦ p ab.1 ab.2).card ≤ S.card * b := by
  rw [Finset.card_filter]
  calc
    _ = ∑ a ∈ S, ∑ b ∈ T, if p a b then 1 else 0 := by
      exact Finset.sum_product S T
        (fun ab ↦ if p ab.1 ab.2 then 1 else 0)
    _ = ∑ a ∈ S, (T.filter (p a)).card := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.card_filter]
    _ ≤ ∑ _a ∈ S, b := by
      exact Finset.sum_le_sum fun a ha ↦ h a ha
    _ = S.card * b := by simp

private lemma card_good_pairs
    {α : Type*} [DecidableEq α] (S : Finset α)
    (bad0 : α → Prop) (bad1 bad2 : α → α → Prop)
    [DecidablePred bad0]
    [DecidablePred fun ab : α × α ↦ bad1 ab.1 ab.2]
    [DecidablePred fun ab : α × α ↦ bad2 ab.1 ab.2]
    [∀ a, DecidablePred (bad1 a)] [∀ a, DecidablePred (bad2 a)]
    (b : ℕ)
    (h0 : (S.filter bad0).card ≤ b)
    (h1 : ∀ a ∈ S, ¬bad0 a → (S.filter (bad1 a)).card ≤ b)
    (h2 : ∀ a ∈ S, ¬bad0 a → (S.filter (bad2 a)).card ≤ b)
    (hsmall : 6 * b ≤ S.card) :
    S.card * S.card ≤ 2 *
      ((S ×ˢ S).filter fun ab ↦
        ¬bad0 ab.1 ∧ ¬bad1 ab.1 ab.2 ∧ ¬bad2 ab.1 ab.2).card := by
  classical
  let P := S ×ˢ S
  let Good := P.filter fun ab ↦
    ¬bad0 ab.1 ∧ ¬bad1 ab.1 ab.2 ∧ ¬bad2 ab.1 ab.2
  let Bad := P \ Good
  let A0 := (S.filter bad0) ×ˢ S
  let A1 := P.filter fun ab ↦ ¬bad0 ab.1 ∧ bad1 ab.1 ab.2
  let A2 := P.filter fun ab ↦ ¬bad0 ab.1 ∧ bad2 ab.1 ab.2
  have hBadSub : Bad ⊆ A0 ∪ (A1 ∪ A2) := by
    intro ab hab
    simp only [Bad, Good, P, A0, A1, A2, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_product, Finset.mem_union] at hab ⊢
    rcases hab with ⟨habP, hnot⟩
    have hnotGood :
        ¬(¬bad0 ab.1 ∧ ¬bad1 ab.1 ab.2 ∧ ¬bad2 ab.1 ab.2) := by
      exact fun hgood ↦ hnot ⟨habP, hgood⟩
    simp only [not_and_or, not_not] at hnotGood
    rcases hnotGood with h0bad | h1bad | h2bad
    · exact Or.inl ⟨⟨habP.1, h0bad⟩, habP.2⟩
    · by_cases h0bad : bad0 ab.1
      · exact Or.inl ⟨⟨habP.1, h0bad⟩, habP.2⟩
      · exact Or.inr (Or.inl ⟨habP, h0bad, h1bad⟩)
    · by_cases h0bad : bad0 ab.1
      · exact Or.inl ⟨⟨habP.1, h0bad⟩, habP.2⟩
      · exact Or.inr (Or.inr ⟨habP, h0bad, h2bad⟩)
  have hA0 : A0.card ≤ b * S.card := by
    simp only [A0, Finset.card_product]
    exact Nat.mul_le_mul_right S.card h0
  have hA1 : A1.card ≤ S.card * b := by
    apply card_filter_product_le_mul_of_fiber_le S S
      (fun a z ↦ ¬bad0 a ∧ bad1 a z) b
    intro a ha
    by_cases hbad : bad0 a
    · simp [hbad]
    · simpa [hbad] using h1 a ha hbad
  have hA2 : A2.card ≤ S.card * b := by
    apply card_filter_product_le_mul_of_fiber_le S S
      (fun a z ↦ ¬bad0 a ∧ bad2 a z) b
    intro a ha
    by_cases hbad : bad0 a
    · simp [hbad]
    · simpa [hbad] using h2 a ha hbad
  have hBad : Bad.card ≤ 3 * (S.card * b) := by
    have hu0 : (A0 ∪ (A1 ∪ A2)).card ≤ A0.card + (A1 ∪ A2).card :=
      Finset.card_union_le A0 (A1 ∪ A2)
    have hu12 : (A1 ∪ A2).card ≤ A1.card + A2.card :=
      Finset.card_union_le A1 A2
    calc
      Bad.card ≤ (A0 ∪ (A1 ∪ A2)).card := Finset.card_le_card hBadSub
      _ ≤ A0.card + (A1 ∪ A2).card := hu0
      _ ≤ A0.card + (A1.card + A2.card) := Nat.add_le_add_left hu12 _
      _ ≤ (S.card * b) + ((S.card * b) + (S.card * b)) := by
        simpa [Nat.mul_comm] using Nat.add_le_add hA0 (Nat.add_le_add hA1 hA2)
      _ = 3 * (S.card * b) := by omega
  have hGoodSub : Good ⊆ P := by
    exact Finset.filter_subset _ _
  have hBadCard : Bad.card = P.card - Good.card := by
    exact Finset.card_sdiff_of_subset hGoodSub
  have hPCard : P.card = S.card * S.card := by
    simpa only [P] using Finset.card_product S S
  have haccount : S.card * S.card ≤ Good.card + 3 * (S.card * b) := by
    rw [← hPCard]
    omega
  have herror : 6 * (S.card * b) ≤ S.card * S.card := by
    have hmul := Nat.mul_le_mul_left S.card hsmall
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  change S.card * S.card ≤ 2 * Good.card
  omega

/-- The directed exclusive-neighbour count is a degree into the part of
`S₀` missed by the other vertex. -/
lemma exclusiveNeighborCount_eq (G : SimpleGraph V) (S₀ : Finset V)
    (z y : V) :
    exclusiveNeighborCount G S₀ z y =
      (neighborsIn G z (S₀ \ neighborsIn G y S₀)).card := by
  classical
  simp only [exclusiveNeighborCount, neighborsIn]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  aesop

/-- The reverse exclusive-neighbour count is the non-neighbour portion of
the first vertex's neighbourhood in `S₀`. -/
lemma exclusiveNeighborCount_reverse_eq (G : SimpleGraph V) (S₀ : Finset V)
    (z y : V) :
    exclusiveNeighborCount G S₀ y z =
      ((neighborsIn G y S₀) \ neighborsIn G z (neighborsIn G y S₀)).card := by
  classical
  simp only [exclusiveNeighborCount, neighborsIn]
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  aesop

/-- Three nonexceptionality certificates imply that an ordered pair belongs
to the KSSS switching reservoir. -/
lemma mem_switchingPairs_of_nonexceptional
    (G : SimpleGraph V) (S S₀ : Finset V) (rho : ℝ) (q : ℕ)
    (hrho : 0 < rho)
    (hq : q ≤ Nat.ceil (rho ^ 2 * (S₀.card : ℝ)))
    {y z : V} (hyS : y ∈ S) (hzS : z ∈ S)
    (hy : y ∉ exceptionalVertices G S₀ rho)
    (hz0 : z ∉ exceptionalVertices G
      (S₀ \ neighborsIn G y S₀) rho)
    (hz1 : z ∉ exceptionalVertices G (neighborsIn G y S₀) rho) :
    (y, z) ∈ switchingPairs G S S₀ q := by
  classical
  rw [mem_switchingPairs_iff]
  refine ⟨hyS, hzS, ?_, ?_⟩
  · simp only [mem_exceptionalVertices, not_or, not_le] at hy hz0
    rw [exclusiveNeighborCount_eq]
    have hscale :
        rho ^ 2 * (S₀.card : ℝ) <
          rho * ((S₀ \ neighborsIn G y S₀).card : ℝ) := by
      nlinarith [hrho]
    have hreal : rho ^ 2 * (S₀.card : ℝ) ≤
        ((neighborsIn G z (S₀ \ neighborsIn G y S₀)).card : ℝ) :=
      (hscale.trans hz0.1).le
    exact hq.trans (Nat.ceil_le.mpr hreal)
  · simp only [mem_exceptionalVertices, not_or, not_le] at hy hz1
    rw [exclusiveNeighborCount_reverse_eq]
    have hscale :
        rho ^ 2 * (S₀.card : ℝ) <
          rho * ((neighborsIn G y S₀).card : ℝ) := by
      nlinarith [hrho]
    have hreal : rho ^ 2 * (S₀.card : ℝ) ≤
        (((neighborsIn G y S₀) \
          neighborsIn G z (neighborsIn G y S₀)).card : ℝ) :=
      (hscale.trans hz1.2).le
    exact hq.trans (Nat.ceil_le.mpr hreal)

/-- KSSS Lemma 13.5 in a parameter-explicit finite form.  If the rich-set
exception budget is at most one sixth of `S`, then at least half of the
ordered pairs of `S` lie in the symmetric switching reservoir. -/
lemma switchingPairs_large_of_richOn
    (G : SimpleGraph V) (S S₀ : Finset V) (delta rho alpha : ℝ)
    (q b : ℕ) (hSS₀ : S ⊆ S₀)
    (hrich : RichOn G S₀ delta rho alpha)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1) (hdelta : delta ≤ rho)
    (hb : (S₀.card : ℝ) ^ alpha ≤ (b : ℝ))
    (hsmall : 6 * b ≤ S.card)
    (hq : q ≤ Nat.ceil (rho ^ 2 * (S₀.card : ℝ))) :
    S.card * S.card ≤ 2 * (switchingPairs G S S₀ q).card := by
  classical
  let bad0 : V → Prop := fun y ↦ y ∈ exceptionalVertices G S₀ rho
  let bad1 : V → V → Prop := fun y z ↦
    z ∈ exceptionalVertices G (S₀ \ neighborsIn G y S₀) rho
  let bad2 : V → V → Prop := fun y z ↦
    z ∈ exceptionalVertices G (neighborsIn G y S₀) rho
  have hS₀size : delta * (S₀.card : ℝ) ≤ (S₀.card : ℝ) := by
    calc
      delta * (S₀.card : ℝ) ≤ rho * (S₀.card : ℝ) :=
        mul_le_mul_of_nonneg_right hdelta (Nat.cast_nonneg _)
      _ ≤ 1 * (S₀.card : ℝ) :=
        mul_le_mul_of_nonneg_right hrhoOne (Nat.cast_nonneg _)
      _ = (S₀.card : ℝ) := one_mul _
  have h0 : (S.filter bad0).card ≤ b := by
    have hrich0 := hrich S₀ Finset.Subset.rfl hS₀size
    have hsub : S.filter bad0 ⊆ exceptionalVertices G S₀ rho ∩ S₀ := by
      intro y hy
      simp only [Finset.mem_filter, bad0, Finset.mem_inter] at hy ⊢
      exact ⟨hy.2, hSS₀ hy.1⟩
    have hsubReal : ((S.filter bad0).card : ℝ) ≤
        ((exceptionalVertices G S₀ rho ∩ S₀).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hreal : ((S.filter bad0).card : ℝ) ≤ (b : ℝ) :=
      hsubReal.trans (hrich0.trans hb)
    exact_mod_cast hreal
  have h1 : ∀ y ∈ S, ¬bad0 y → (S.filter (bad1 y)).card ≤ b := by
    intro y hyS hyGood
    have hyNon : y ∉ exceptionalVertices G S₀ rho := by
      simpa only [bad0] using hyGood
    have hyBounds :
        rho * (S₀.card : ℝ) < ((neighborsIn G y S₀).card : ℝ) ∧
          rho * (S₀.card : ℝ) <
            ((S₀ \ neighborsIn G y S₀).card : ℝ) := by
      simpa only [mem_exceptionalVertices, not_or, not_le] using hyNon
    let W := S₀ \ neighborsIn G y S₀
    have hWsub : W ⊆ S₀ := Finset.sdiff_subset
    have hWsize : delta * (S₀.card : ℝ) ≤ (W.card : ℝ) := by
      exact (mul_le_mul_of_nonneg_right hdelta (Nat.cast_nonneg _)).trans
        hyBounds.2.le
    have hrichW := hrich W hWsub hWsize
    have hsub : S.filter (bad1 y) ⊆ exceptionalVertices G W rho ∩ S₀ := by
      intro z hz
      simp only [Finset.mem_filter, bad1, Finset.mem_inter] at hz ⊢
      exact ⟨by simpa only [W] using hz.2, hSS₀ hz.1⟩
    have hsubReal : ((S.filter (bad1 y)).card : ℝ) ≤
        ((exceptionalVertices G W rho ∩ S₀).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hreal : ((S.filter (bad1 y)).card : ℝ) ≤ (b : ℝ) :=
      hsubReal.trans (hrichW.trans hb)
    exact_mod_cast hreal
  have h2 : ∀ y ∈ S, ¬bad0 y → (S.filter (bad2 y)).card ≤ b := by
    intro y hyS hyGood
    have hyNon : y ∉ exceptionalVertices G S₀ rho := by
      simpa only [bad0] using hyGood
    have hyBounds :
        rho * (S₀.card : ℝ) < ((neighborsIn G y S₀).card : ℝ) ∧
          rho * (S₀.card : ℝ) <
            ((S₀ \ neighborsIn G y S₀).card : ℝ) := by
      simpa only [mem_exceptionalVertices, not_or, not_le] using hyNon
    let W := neighborsIn G y S₀
    have hWsub : W ⊆ S₀ := by
      intro z hz
      exact (mem_neighborsIn.mp hz).1
    have hWsize : delta * (S₀.card : ℝ) ≤ (W.card : ℝ) := by
      exact (mul_le_mul_of_nonneg_right hdelta (Nat.cast_nonneg _)).trans
        hyBounds.1.le
    have hrichW := hrich W hWsub hWsize
    have hsub : S.filter (bad2 y) ⊆ exceptionalVertices G W rho ∩ S₀ := by
      intro z hz
      simp only [Finset.mem_filter, bad2, Finset.mem_inter] at hz ⊢
      exact ⟨by simpa only [W] using hz.2, hSS₀ hz.1⟩
    have hsubReal : ((S.filter (bad2 y)).card : ℝ) ≤
        ((exceptionalVertices G W rho ∩ S₀).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hreal : ((S.filter (bad2 y)).card : ℝ) ≤ (b : ℝ) :=
      hsubReal.trans (hrichW.trans hb)
    exact_mod_cast hreal
  let Good := (S ×ˢ S).filter fun yz ↦
    ¬bad0 yz.1 ∧ ¬bad1 yz.1 yz.2 ∧ ¬bad2 yz.1 yz.2
  have hGoodCount : S.card * S.card ≤ 2 * Good.card := by
    exact card_good_pairs S bad0 bad1 bad2 b h0 h1 h2 hsmall
  have hGoodSub : Good ⊆ switchingPairs G S S₀ q := by
    intro yz hyz
    simp only [Good, Finset.mem_filter, Finset.mem_product] at hyz
    exact mem_switchingPairs_of_nonexceptional G S S₀ rho q hrho hq
      hyz.1.1 hyz.1.2
      (by simpa only [bad0] using hyz.2.1)
      (by simpa only [bad1] using hyz.2.2.1)
      (by simpa only [bad2] using hyz.2.2.2)
  exact hGoodCount.trans (Nat.mul_le_mul_left 2 (Finset.card_le_card hGoodSub))

/-- The exact integer threshold in KSSS (4.50). -/
noncomputable def switchingThreshold (rho : ℝ) (S₀ : Finset V) : ℕ :=
  Nat.ceil (rho ^ 2 * (S₀.card : ℝ))

/-- Direct form of KSSS Lemma 13.5 for the threshold used in (4.50). -/
lemma switchingPairs_large_of_richOn_threshold
    (G : SimpleGraph V) (S S₀ : Finset V) (delta rho alpha : ℝ)
    (b : ℕ) (hSS₀ : S ⊆ S₀)
    (hrich : RichOn G S₀ delta rho alpha)
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1) (hdelta : delta ≤ rho)
    (hb : (S₀.card : ℝ) ^ alpha ≤ (b : ℝ))
    (hsmall : 6 * b ≤ S.card) :
    S.card * S.card ≤
      2 * (switchingPairs G S S₀ (switchingThreshold rho S₀)).card := by
  apply switchingPairs_large_of_richOn G S S₀ delta rho alpha
    (switchingThreshold rho S₀) b hSS₀ hrich hrho hrhoOne hdelta hb hsmall
  exact le_rfl

end SwitchingReservoir

noncomputable def switchingLabels (B : ℕ) : Finset ℤ :=
  Finset.Icc (-(B : ℤ)) (B : ℤ)

@[simp] lemma switchingLabels_card (B : ℕ) :
    (switchingLabels B).card = 2 * B + 1 := by
  rw [switchingLabels, Int.card_Icc]
  norm_num
  omega

/-- The ordered tuple occurring in a raw window moment has at most `4B+2`
coordinates, exactly the dimension bound used in KSSS Lemma 13.4. -/
lemma switchingTuple_dimension_le {B : ℕ} (a : ℤ → ℕ)
    (ha : ∀ ell ∈ switchingLabels B, a ell ≤ 2) :
    Nat.card (RawTupleIndex (switchingLabels B) a) ≤ 4 * B + 2 := by
  calc
    _ ≤ 2 * (switchingLabels B).card :=
      card_rawTupleIndex_le_two_mul (switchingLabels B) a ha
    _ = 4 * B + 2 := by rw [switchingLabels_card]; omega

lemma switchingLabels_nonempty (B : ℕ) : (switchingLabels B).Nonempty := by
  refine ⟨0, ?_⟩
  simp [switchingLabels]

lemma neg_mem_switchingLabels {B : ℕ} {ell : ℤ}
    (h : ell ∈ switchingLabels B) : -ell ∈ switchingLabels B := by
  simp only [switchingLabels, Finset.mem_Icc] at h ⊢
  omega

lemma indicator_score_window_partition {n B : ℕ}
    (score : Finset (Fin n) → ℤ) (x : ℤ) (U : Finset (Fin n)) :
    indicator (|score U - x| ≤ (B : ℤ)) =
      ∑ ell ∈ switchingLabels B, indicator (score U = x + ell) := by
  classical
  simp only [indicator]
  by_cases hw : |score U - x| ≤ (B : ℤ)
  · rw [if_pos hw]
    let ell : ℤ := score U - x
    have hell : ell ∈ switchingLabels B := by
      simp only [switchingLabels, Finset.mem_Icc, ell]
      exact (abs_le.mp hw)
    rw [Finset.sum_eq_single ell]
    · simp [ell]
    · intro b hb hbe
      have hne : score U ≠ x + b := by
        intro heq
        apply hbe
        dsimp only [ell]
        omega
      simp [hne]
    · intro hellnot
      exact (hellnot hell).elim
  · rw [if_neg hw]
    symm
    apply Finset.sum_eq_zero
    intro ell hell
    have hne : score U ≠ x + ell := by
      intro heq
      apply hw
      simp only [switchingLabels, Finset.mem_Icc] at hell
      apply (abs_le).2
      constructor <;> omega
    simp [hne]

lemma score_point_mem_window {n B : ℕ}
    (score : Finset (Fin n) → ℤ) (x ell : ℤ)
    (hell : ell ∈ switchingLabels B) (U : Finset (Fin n))
    (hpoint : score U = x + ell) : |score U - x| ≤ (B : ℤ) := by
  simp only [switchingLabels, Finset.mem_Icc] at hell
  apply (abs_le).2
  constructor <;> omega

lemma score_target_mem_window {n B : ℕ}
    (score : Finset (Fin n) → ℤ) (x : ℤ) (U : Finset (Fin n))
    (htarget : score U = x) : |score U - x| ≤ (B : ℤ) := by
  rw [htarget, sub_self, abs_zero]
  positivity

lemma bernoulliWeight_half_switching {V : Type*} [Fintype V]
    (W : Finset V) :
    Probability.bernoulliWeight (1 / 2 : ℝ) W =
      (1 / 2 : ℝ) ^ Fintype.card V := by
  classical
  rw [Probability.bernoulliWeight, Erdos202.ParkPham.bernoulliMass]
  have hcardUniv : W.card ≤ (Finset.univ : Finset V).card :=
    Finset.card_le_card (by simp)
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [← pow_add]
  congr 1
  exact (Nat.add_sub_of_le hcardUniv).trans (Finset.card_univ.trans rfl)

lemma uniformMeanOn_indicator_eq_eventProbability_half
    {V : Type*} [Fintype V] (P : Finset V → Prop) [DecidablePred P] :
    uniformMeanOn (Finset.univ : Finset (Finset V))
        (fun U ↦ indicator (P U)) =
      Probability.eventProbability (1 / 2 : ℝ) P := by
  classical
  rw [uniformMeanOn, Probability.eventProbability]
  unfold Probability.expectation
  simp only [indicator]
  simp_rw [bernoulliWeight_half_switching]
  rw [← Finset.mul_sum]
  simp only [Finset.card_univ, Fintype.card_finset, one_div, inv_pow]
  rw [div_eq_mul_inv, mul_comm]
  norm_num [Nat.cast_pow]
  norm_cast
  simpa using
    (Finset.sum_boole (R := ℕ) P (Finset.univ : Finset (Finset V)))

/-- The precise remaining graph-specific input from KSSS Section 13:
Lemma 13.4 for the unbiased induced-edge statistic, with the switching set
and its symmetry included. -/
def KSSSUnbiasedSwitchingMoments : Prop :=
  ∀ (C A : ℝ), 0 < C → 0 < A →
    ∃ (B : ℕ) (lower upper : ℝ),
      0 < lower ∧ 0 < upper ∧ ∃ N : ℕ,
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n → RamseyFree C G →
          ∀ x : ℕ,
            |(x : ℝ) - (1 / 4 : ℝ) * (G.edgeFinset.card : ℝ)| ≤
                A * (n : ℝ) ^ (3 / 2 : ℝ) →
              ∃ T : Finset (Fin n × Fin n),
                IsSymmetric T ∧
                  RawMomentComparison
                    (Finset.univ : Finset (Finset (Fin n)))
                    (fun U ↦ |edgeScore G U - (x : ℤ)| ≤ (B : ℤ))
                    (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
                    (switchingLabels B)
                    ((T.card : ℝ) / Real.sqrt n)
                    ((n : ℝ) ^ (3 / 2 : ℝ)) lower upper

theorem ksssUnbiasedEdgeLocalLower_of_switchingMoments
    (hmoments : KSSSUnbiasedSwitchingMoments) :
    KSSSUnbiasedEdgeLocalLower := by
  intro C A hC hA
  obtain ⟨B, lower, upper, hlower, hupper, N, hN⟩ :=
    hmoments C A hC hA
  let labels := switchingLabels B
  have hlabels : labels.Nonempty := switchingLabels_nonempty B
  have hcardPos : 0 < (labels.card : ℝ) := by
    exact_mod_cast hlabels.card_pos
  let kappa : ℝ :=
    (lower / (labels.card : ℝ)) ^ 4 / upper ^ 3
  have hkappa : 0 < kappa := by
    dsimp only [kappa]
    positivity
  refine ⟨kappa, hkappa, max N 1, ?_⟩
  intro n G hn hG x hx
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  obtain ⟨T, hT, hraw⟩ := hN n G hnN hG x hx
  let score : Finset (Fin n) → ℤ := edgeScore G
  let Y : ℤ → Finset (Fin n) → ℝ := fun ell U ↦
    (switchingCount T score ell U : ℝ)
  have hbound := windowRawMomentComparison_force_pointProbability
    (Finset.univ : Finset (Finset (Fin n))) (by simp)
    labels hlabels
    (fun ell U ↦ score U = (x : ℤ) + ell)
    (fun U ↦ |score U - (x : ℤ)| ≤ (B : ℤ))
    (fun U ↦ score U = (x : ℤ))
    (fun ell ↦ -ell) Y
    ((T.card : ℝ) / Real.sqrt n)
    ((n : ℝ) ^ (3 / 2 : ℝ)) lower upper
    (by intro ell hell U hU; positivity)
    (by simpa only [score, Y, labels] using hraw)
    (by
      intro U hU
      exact indicator_score_window_partition score (x : ℤ) U)
    (by
      intro ell hell U hpoint
      exact score_point_mem_window score (x : ℤ) ell
        (by simpa only [labels] using hell) U hpoint)
    (by
      intro U htarget
      exact score_target_mem_window score (x : ℤ) U htarget)
    (by
      intro ell hell
      exact neg_mem_switchingLabels (by simpa only [labels] using hell))
    (by
      intro ell hell
      simpa only [Y] using
        (uniformMeanOn_switching_reversal hT ell (x : ℤ)).symm)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn1
  calc
    kappa * (n : ℝ) ^ (-(3 / 2 : ℝ)) =
        (lower / (labels.card : ℝ)) ^ 4 /
          (upper ^ 3 * (n : ℝ) ^ (3 / 2 : ℝ)) := by
      rw [show (-(3 / 2 : ℝ)) = -(3 / 2 : ℝ) by ring,
        Real.rpow_neg hnreal.le]
      dsimp only [kappa]
      field_simp
    _ ≤ uniformMeanOn (Finset.univ : Finset (Finset (Fin n)))
        (fun U ↦ indicator (score U = (x : ℤ))) := hbound
    _ = Probability.eventProbability (1 / 2 : ℝ)
        (fun U : Finset (Fin n) ↦ inducedEdges G U = x) := by
      rw [uniformMeanOn_indicator_eq_eventProbability_half]
      unfold Probability.eventProbability Probability.expectation
      apply Finset.sum_congr rfl
      intro U hU
      have hi : score U = (x : ℤ) ↔ inducedEdges G U = x := by
        simp only [score, edgeScore]
        exact_mod_cast Iff.rfl
      by_cases ht : inducedEdges G U = x
      · have hs := hi.mpr ht
        simp [ht, hs]
      · have hs : ¬score U = (x : ℤ) := fun hs ↦ ht (hi.mp hs)
        simp [ht, hs]

/-- Exact final reduction: the source-shaped Section 13 raw moment theorem
already implies Erdős Problem 88, with no need for the stronger biased local
limit theorem. -/
theorem erdos_88_of_switchingMoments
    (hmoments : KSSSUnbiasedSwitchingMoments) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          HomogeneousFree epsilon G →
            ∀ m : ℕ, (m : ℝ) ≤ delta * (n : ℝ) ^ 2 →
              ∃ S : Finset (Fin n), inducedEdges G S = m :=
  erdos_88_of_unbiasedEdgeLocalLower
    (ksssUnbiasedEdgeLocalLower_of_switchingMoments hmoments)

end Switching
end Erdos88
