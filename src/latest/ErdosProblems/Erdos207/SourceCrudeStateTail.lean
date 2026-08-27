/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCrudeTailExpressions

/-! # The exact generalized global crude event has an explicit additive-error tail -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem source_crudeStatistic_tail
    {Ω V I : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype I] {ell q s : ℕ}
    {W : Vortex V ell} {F : I → ForbiddenFamilyOn V} {order : I → ℕ} {y z : I → ℝ≥0}
    (hF : ∀ i, SourceVortexWellSpread W (order i) (F i) (y i) (z i))
    (horder : ∀ i, order i ≤ q) (hidentical : ∀ i i', order i = order i' → F i = F i')
    (w : ℝ≥0) (hw : 1 ≤ w) (L : FiniteLaw Ω) (J : Ω → ForbiddenFamilyOn V)
    (S : Ω → GreedyStateOn V) (available old : Ω → TripleSystemOn V)
    (hstate : L.SupportedOn (fun x ↦ GreedyInvariant (J x) (S x) ∧
      (S x).available ⊆ available x ∧ Disjoint (available x) (old x) ∧
      (∀ U ∈ available x, W.level U = Fin.last ell) ∧
      ∀ C ∈ J x, C ⊆ available x ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old x))
    (A epsilon : ℝ≥0) (K : CrudeThresholds)
    (hK : ∀ i : CrudeStatisticIndex V q, 0 < crudeThreshold K i)
    (hjoint : ∀ H : TripleSystemOn V, H.card ≤ s * (2 * q) →
      L.probability (fun x ↦ H ⊆ old x ∪ (S x).chosen) ≤
        A * setWeight (vortexTripleWeight W w) H + epsilon)
    (i : CrudeStatisticIndex V q) :
    L.probability (fun x ↦ crudeThreshold K i ≤ crudeStatistic (J x) (S x) i) ≤
      sourceCrudeTailBound W order z s w A epsilon K i := by
  classical
  rcases i with ⟨j, roots⟩ | i
  · have hbudget := j.budget
    have hjq := j.order_le
    have htail := localizedRooted_source_orders_tail_additive (q := q) (j := j.order) (c := j.chosen) (s := s)
      (fun i : {i : I // j.order ≤ order i} ↦ hF i.1)
      (fun i ↦ ⟨i.2, horder i.1⟩) {roots.1.1, roots.1.2} (card_pair roots.2) hbudget w hw
      L (fun x ↦ forbiddenFamilyOfOrder (J x) j.order) J S available old (by
        intro x hx
        have hd := hstate x hx
        exact ⟨hd.1, fun U hU ↦ hd.2.2.2.1 U (hd.2.1 hU), hd.2.2.1,
          source_cover_restrict_order F order (J x) (available x) (old x) j.order (by omega)
            (fun i E hE ↦ ((hF i).uniform E hE).1) hd.2.2.2.2⟩)
      A epsilon (K.rooted j.order j.chosen) (hK (.inl (j, roots))) (by
        intro H hH
        exact hjoint H (hH.trans (Nat.mul_le_mul_left s (by omega))))
    exact htail
  rcases i with ⟨T, P⟩ | i
  · exact localizedPair_source_orders_tail_additive (s := s) hF horder T P w hw L J available old
      (fun x ↦ (S x).chosen) (by
        intro x hx
        have hd := hstate x hx
        exact ⟨hd.2.2.2.1, hd.2.2.1, hd.2.2.2.2⟩)
      A epsilon K.pair (hK (.inr (.inl (T, P)))) (by
        intro H hH
        exact hjoint H (hH.trans (Nat.mul_le_mul_left s (by omega))))
  rcases i with ⟨T, T'⟩ | ⟨j, T⟩
  · exact localizedCommon_selected_source_orders_tail_additive (t := s) hF horder hidentical
      T T' w hw L J available old (fun x ↦ (S x).chosen) (by
        intro x hx
        have hd := hstate x hx
        exact ⟨hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2⟩)
      A epsilon K.common (hK (.inr (.inr (.inl (T, T'))))) hjoint
  · have hbudget := j.budget
    have ha : 1 ≤ (j.order - 2) - j.chosen - 1 := by omega
    have htail := localizedGain_source_orders_tail_additive (m := j.order - 2) (c := j.chosen) (t := s)
      hF horder hidentical ha T w hw L (fun x ↦ forbiddenFamilyOfOrder (J x) j.order) J J S available old (by
        intro x hx
        have hd := hstate x hx
        exact ⟨hd.1, fun _ hC ↦ (mem_forbiddenFamilyOfOrder.mp hC).2, hd.2.2.1, hd.2.2.2.1,
          fun C hC ↦ hd.2.2.2.2 C (mem_forbiddenFamilyOfOrder.mp hC).1, hd.2.2.2.2⟩)
      A epsilon (K.gain j.order j.chosen) (hK (.inr (.inr (.inr (j, T))))) hjoint
    have hexp : (j.order - 2) - j.chosen - 2 = j.order - j.chosen - 4 := by omega
    simpa only [hexp, sourceCrudeTailBound, sourceMomentTailExpression, crudeThreshold,
      crudeStatistic] using htail

theorem source_crudeState_failure_le_sum
    {Ω V I : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype I] {ell q s : ℕ}
    {W : Vortex V ell} {F : I → ForbiddenFamilyOn V} {order : I → ℕ} {y z : I → ℝ≥0}
    (hF : ∀ i, SourceVortexWellSpread W (order i) (F i) (y i) (z i))
    (horder : ∀ i, order i ≤ q) (hidentical : ∀ i i', order i = order i' → F i = F i')
    (w : ℝ≥0) (hw : 1 ≤ w) (L : FiniteLaw Ω) (J : Ω → ForbiddenFamilyOn V)
    (S : Ω → GreedyStateOn V) (available old : Ω → TripleSystemOn V)
    (hstate : L.SupportedOn (fun x ↦ GreedyInvariant (J x) (S x) ∧
      (S x).available ⊆ available x ∧ Disjoint (available x) (old x) ∧
      (∀ U ∈ available x, W.level U = Fin.last ell) ∧
      ∀ C ∈ J x, C ⊆ available x ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old x))
    (A epsilon : ℝ≥0) (K : CrudeThresholds)
    (hK : ∀ i : CrudeStatisticIndex V q, 0 < crudeThreshold K i)
    (hjoint : ∀ H : TripleSystemOn V, H.card ≤ s * (2 * q) →
      L.probability (fun x ↦ H ⊆ old x ∪ (S x).chosen) ≤
        A * setWeight (vortexTripleWeight W w) H + epsilon) :
    L.probability (fun x ↦ ¬ CrudeStateBounds (J x) (S x) q K) ≤
      ∑ i : CrudeStatisticIndex V q, sourceCrudeTailBound W order z s w A epsilon K i := by
  classical
  have hsum := L.probability_exists_le (univ : Finset (CrudeStatisticIndex V q))
    (fun i x ↦ crudeThreshold K i ≤ crudeStatistic (J x) (S x) i)
  have hsum' := hsum.trans (sum_le_sum (fun i _ ↦
    source_crudeStatistic_tail hF horder hidentical w hw L J S available old hstate A epsilon K hK hjoint i))
  simpa only [CrudeStateBounds, not_forall, not_lt, mem_univ, true_and] using hsum'

end

end Erdos207
