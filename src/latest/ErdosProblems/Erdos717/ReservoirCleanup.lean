/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Cleaning the DRC neighborhood and counting good intermediate vertices. -/

import ErdosProblems.Erdos717.RouteReservoir

open Function Set
open SimpleGraph

namespace Erdos717

def badNeighborFinset {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X T : Finset V) (L : ℕ) (v : V) : Finset V :=
  X.filter fun w => (commonNeighborFinset G T v w).card < L

theorem sum_card_badNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X T : Finset V) (L : ℕ) :
    ∑ v ∈ X, (badNeighborFinset G X T L v).card =
      ((X ×ˢ X).filter fun p =>
        (commonNeighborFinset G T p.1 p.2).card < L).card := by
  classical
  simp only [badNeighborFinset, Finset.card_eq_sum_ones,
    Finset.sum_filter, Finset.card_product]
  rw [Finset.sum_product]

/-- Delete the vertices incident with too many low-codegree ordered pairs and
keep a fixed one-fifth subset of the survivors. -/
theorem exists_clean_reservoir_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X T : Finset V) (L : ℕ) (hX : 0 < X.card)
    (hfew : 40 * ((X ×ˢ X).filter fun p =>
      (commonNeighborFinset G T p.1 p.2).card < L).card ≤ X.card * X.card) :
    ∃ U : Finset V,
      U ⊆ X ∧ U.card = X.card / 5 ∧
      ∀ v ∈ U, 4 * (badNeighborFinset G X T L v).card < X.card := by
  classical
  let badV : Finset V := X.filter fun v =>
    X.card ≤ 4 * (badNeighborFinset G X T L v).card
  let B := ((X ×ˢ X).filter fun p =>
    (commonNeighborFinset G T p.1 p.2).card < L).card
  have hbadVsub : badV ⊆ X := Finset.filter_subset _ _
  have hbadMul : badV.card * X.card ≤ 4 * B := by
    calc
      badV.card * X.card = ∑ _v ∈ badV, X.card := by simp
      _ ≤ ∑ v ∈ badV, 4 * (badNeighborFinset G X T L v).card := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.mem_filter.mp hv).2
      _ = 4 * ∑ v ∈ badV, (badNeighborFinset G X T L v).card := by
        rw [Finset.mul_sum]
      _ ≤ 4 * ∑ v ∈ X, (badNeighborFinset G X T L v).card :=
        Nat.mul_le_mul_left 4 (Finset.sum_le_sum_of_subset hbadVsub)
      _ = 4 * B := by
        rw [sum_card_badNeighborFinset]
  have hbadTen : 10 * badV.card ≤ X.card := by
    apply Nat.le_of_mul_le_mul_right (c := X.card) _ hX
    calc
      (10 * badV.card) * X.card = 10 * (badV.card * X.card) := by ring
      _ ≤ 10 * (4 * B) := Nat.mul_le_mul_left 10 hbadMul
      _ = 40 * B := by ring
      _ ≤ X.card * X.card := by simpa [B] using hfew
  let goodV := X \ badV
  have hgoodCard : X.card / 5 ≤ goodV.card := by
    have hcard : goodV.card = X.card - badV.card := by
      rw [show goodV = X \ badV by rfl, Finset.card_sdiff]
      have hinter : badV ∩ X = badV := Finset.inter_eq_left.mpr hbadVsub
      rw [hinter]
    rw [hcard]
    omega
  obtain ⟨U, hUgood, hUcard⟩ := Finset.exists_subset_card_eq hgoodCard
  refine ⟨U, hUgood.trans Finset.sdiff_subset, hUcard, ?_⟩
  · intro v hv
    have hvGood := hUgood hv
    have hvX : v ∈ X := (Finset.mem_sdiff.mp hvGood).1
    have hvNotBad : v ∉ badV := (Finset.mem_sdiff.mp hvGood).2
    have hnot : ¬X.card ≤ 4 * (badNeighborFinset G X T L v).card := by
      intro h
      exact hvNotBad (Finset.mem_filter.mpr ⟨hvX, h⟩)
    omega

/-- Intermediate vertices outside `U` which have large common-neighbour sets
with both endpoints. -/
def goodIntermediateFinset {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X U T : Finset V) (L : ℕ) (v w : V) : Finset V :=
  (((X \ U).erase v).erase w).filter fun x =>
    L ≤ (commonNeighborFinset G T v x).card ∧
    L ≤ (commonNeighborFinset G T x w).card

/-- Two clean vertices retain linearly many good intermediate vertices. -/
theorem five_mul_card_goodIntermediate_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X U T : Finset V) (L : ℕ)
    (hXlarge : 20 ≤ X.card) (hUcard : U.card = X.card / 5)
    {v w : V} (hv : v ∈ U) (hw : w ∈ U)
    (hvGood : 4 * (badNeighborFinset G X T L v).card < X.card)
    (hwGood : 4 * (badNeighborFinset G X T L w).card < X.card) :
    X.card ≤ 5 * (goodIntermediateFinset G X U T L v w).card := by
  classical
  let Q := goodIntermediateFinset G X U T L v w
  let Nv := badNeighborFinset G X T L v
  let Nw := badNeighborFinset G X T L w
  let E := U ∪ Nv ∪ Nw ∪ {v, w}
  have hcover : X ⊆ Q ∪ E := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Finset.mem_union_right _ <| by simp [E, hxU]
    by_cases hxv : x = v
    · exact Finset.mem_union_right _ <| by simp [E, hxv]
    by_cases hxw : x = w
    · exact Finset.mem_union_right _ <| by simp [E, hxw]
    by_cases hbadV : (commonNeighborFinset G T v x).card < L
    · exact Finset.mem_union_right _ <| by
        simp [E, Nv, badNeighborFinset, hx, hbadV]
    by_cases hbadW : (commonNeighborFinset G T x w).card < L
    · exact Finset.mem_union_right _ <| by
        have hbadW' : (commonNeighborFinset G T w x).card < L := by
          simpa only [commonNeighborFinset_comm G T w x] using hbadW
        simp [E, Nw, badNeighborFinset, hx, hbadW']
    · apply Finset.mem_union_left
      simp [Q, goodIntermediateFinset, hx, hxU, hxv, hxw,
        Nat.le_of_not_gt hbadV, Nat.le_of_not_gt hbadW]
  have hEcard : E.card ≤ U.card + Nv.card + Nw.card + 2 := by
    calc
      E.card ≤ (U ∪ Nv ∪ Nw).card + ({v, w} : Finset V).card := by
        simpa [E, union_assoc] using Finset.card_union_le (U ∪ Nv ∪ Nw) {v, w}
      _ ≤ (U ∪ Nv).card + Nw.card + ({v, w} : Finset V).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ U.card + Nv.card + Nw.card + ({v, w} : Finset V).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ U.card + Nv.card + Nw.card + 2 := by
        gcongr
        exact Finset.card_insert_le _ _ |>.trans <| by simp
  have hcount : X.card ≤ Q.card + E.card :=
    (Finset.card_le_card hcover).trans (Finset.card_union_le Q E)
  change 4 * Nv.card < X.card at hvGood
  change 4 * Nw.card < X.card at hwGood
  rw [hUcard] at hEcard
  change X.card ≤ 5 * Q.card
  omega

end Erdos717
