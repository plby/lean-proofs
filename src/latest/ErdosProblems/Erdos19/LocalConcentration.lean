import ErdosProblems.Erdos19.BalancedPartition

/-! # Concentration using only the sampled coordinates that matter -/

namespace Erdos19

open Finset

theorem uniform_abs_deviation_cardRatio_le_fintype
    {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [Nonempty K]
    (hn : 0 < Fintype.card V) (F : (V → K) → ℝ)
    (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (hLip : ∀ x y : V → K, ∀ i : V, (∀ j, j ≠ i → x j = y j) →
      |F x - F y| ≤ c) :
    (({z : V → K | t ≤ |F z - finiteAverage F|} : Set (V → K)).ncard : ℝ) /
        Fintype.card (V → K) ≤
      2 * Real.exp (-t ^ 2 / (2 * Fintype.card V * c ^ 2)) := by
  classical
  let E := Fintype.equivFin V
  let A : (Fin (Fintype.card V) → K) ≃ (V → K) :=
    Equiv.arrowCongr E.symm (Equiv.refl K)
  have hlocal : RealCoordinateLipschitzFin (fun z ↦ F (A z)) c := by
    intro x y i hxy
    apply hLip (A x) (A y) (E.symm i)
    intro j hji
    change x (E j) = y (E j)
    apply hxy
    intro heq
    apply hji
    apply E.injective
    simpa only [E.apply_symm_apply] using heq
  have htail := uniform_abs_deviation_cardRatio_le (Fintype.card V) hn
    (fun z ↦ F (A z)) c t hc ht hlocal
  rw [finiteAverage_comp_equiv A F] at htail
  have hcard := ncard_setOf_comp_equiv A (fun z ↦ t ≤ |F z - finiteAverage F|)
  rw [hcard, Fintype.card_congr A] at htail
  exact htail

theorem uniformBinCount_restrict {V K : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq K] (S : Finset V) (a : K) (z : V → K) :
    uniformBinCount S a z = uniformBinCount (univ : Finset S) a (fun x ↦ z x.1) := by
  classical
  change (∑ v ∈ S, if z v = a then (1 : ℝ) else 0) =
    ∑ v : S, if z v.1 = a then (1 : ℝ) else 0
  exact Finset.sum_subtype S (fun _ ↦ Iff.rfl) _

/-- The variance parameter is the size of `S`, not the total number of
sampled coordinates. This matters when the coordinates are graph edges. -/
theorem bin_count_deviation_cardRatio_le
    {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K] [Nonempty K]
    [DecidableEq K] (S : Finset V) (hS : S.Nonempty) (a : K)
    (t : ℝ) (ht : 0 ≤ t) :
    (({z : V → K | t ≤ |uniformBinCount S a z - (S.card : ℝ) / Fintype.card K|} :
      Set (V → K)).ncard : ℝ) / Fintype.card (V → K) ≤
        2 * Real.exp (-t ^ 2 / (2 * S.card)) := by
  classical
  let P : (S → K) → Prop := fun z ↦
    t ≤ |uniformBinCount univ a z - (S.card : ℝ) / Fintype.card K|
  have hratio := eventRatio_eq_of_restriction S P
    {z : V → K | t ≤ |uniformBinCount S a z - (S.card : ℝ) / Fintype.card K|}
    (fun z ↦ by
      change (t ≤ |uniformBinCount S a z - (S.card : ℝ) / Fintype.card K|) ↔ _
      rw [uniformBinCount_restrict S a z])
  rw [hratio]
  have hn : 0 < Fintype.card S := by simpa only [Fintype.card_coe] using card_pos.mpr hS
  have htail := uniform_abs_deviation_cardRatio_le_fintype hn
    (uniformBinCount (univ : Finset S) a) 1 t (by norm_num) ht
    (uniformBinCount_coordinate_bound _ _)
  simpa only [P, finiteAverage_uniformBinCount, card_univ, Fintype.card_coe,
    one_pow, mul_one] using htail

#print axioms uniform_abs_deviation_cardRatio_le_fintype
#print axioms bin_count_deviation_cardRatio_le

end Erdos19
