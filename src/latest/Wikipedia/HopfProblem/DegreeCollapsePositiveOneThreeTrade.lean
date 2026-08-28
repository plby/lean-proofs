import Wikipedia.HopfProblem.DegreeCollapsePositiveBirthAtCut
import Wikipedia.HopfProblem.DegreeCollapsePositiveOneTwoCancellation
import Wikipedia.HopfProblem.DegreeCollapseIndexedRemovalCount

/-!
# The actual positive one-to-three handle trade on the same original state

Choose the first positive one-handle, construct the original positive
two/three cut and an actual point on it, then perform the supported birth
above that cut. The new two-handle is first above the unchanged cut and
the old one-handle remains first positive. The actual relative one/two
cancellation deletes them. Total critical count is unchanged; index one
decreases by one and index three increases by one. Every other indexed
count and the entire original nonpositive germ are retained.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] [PathConnectedSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_positive_one_to_three_handle_trade
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hnobirth : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      nativeMorseIndex (Vector 7) P.function p ≠ 0)
    (q₀ : criticalPoints (Vector 7) P.function) (hq₀ : 0 < P.function q₀)
    (hq₀one : nativeMorseIndex (Vector 7) P.function q₀ = 1) :
    ∃ R : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) R.function).ncard =
        (criticalPoints (Vector 7) P.function).ncard ∧
      nativeMorseCount (Vector 7) R.function 1 + 1 = nativeMorseCount (Vector 7) P.function 1 ∧
      nativeMorseCount (Vector 7) R.function 3 = nativeMorseCount (Vector 7) P.function 3 + 1 ∧
      (∀ j, j ≠ 1 → j ≠ 3 →
        nativeMorseCount (Vector 7) R.function j = nativeMorseCount (Vector 7) P.function j) ∧
      ∀ w, S.time w ≤ 0 → R.function =ᶠ[𝓝 w] P.function := by
  classical
  obtain ⟨q, hq, hqone, hfirst⟩ := P.exists_first_positive_one_handle horder hnobirth q₀ hq₀ hq₀one
  obtain ⟨A⟩ := nonempty_adaptedSurgeryWindows P.smooth P.morse P.distinct
  obtain ⟨a, ha, hfr, hqa, hhigh, hlow⟩ := A.exists_ordered_index_cut_above 0 horder q hq
    (show nativeMorseIndex (Vector 7) P.function q ≤ 2 by omega)
  have hneg : Module.finrank ℝ (A.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (A.data q).chart).symm.trans hqone
  have hsplit := (A.data q).chart.finrank_negative_add_positive
  simp only [finrank_euclideanSpace_fin] at hsplit
  let : Fact (Module.finrank ℝ (A.data q).chart.PositiveCoordinates = 5 + 1) := ⟨by omega⟩
  obtain ⟨v, t, ht⟩ := A.exists_belt_point_reaching_level_above_cut P.smooth q 5 hq hqa
    hlow (by decide)
  let z : {y : S.Space // P.function y = a} :=
    ⟨A.flow t ((A.data q).surgery.beltSphere v).val, ht⟩
  obtain ⟨Q, r, s, hir, his, har, hrs, hcountbirth, hcrit, hkeep, hnegative,
      heq, hgr, hgap, hcount₂, hcount₃, hother⟩ :=
    P.exists_positive_two_three_birth_above_cut A ha hfr z
  let qQ : criticalPoints (Vector 7) Q.function :=
    ⟨q.val, (hcrit q.val).mpr (Or.inl q.property)⟩
  let rQ : criticalPoints (Vector 7) Q.function :=
    ⟨r, (hcrit r).mpr (Or.inr (Or.inl rfl))⟩
  have hQq : Q.function qQ = P.function q := (hkeep q.val q.property).self_of_nhds
  have hqQ : nativeMorseIndex (Vector 7) Q.function qQ = 1 :=
    (nativeMorseIndex_congr_germ (hkeep q.val q.property)).trans hqone
  have hqpositive : 0 < Q.function qQ := by rw [hQq]; exact hq
  have hQqa : Q.function qQ < a := by rw [hQq]; exact hqa
  have hfirstQ (p : criticalPoints (Vector 7) Q.function) (hp : 0 < Q.function p) :
      Q.function qQ ≤ Q.function p := by
    rcases (hcrit p.val).mp p.property with hold | hpr | hps
    · have hv := (hkeep p.val hold).self_of_nhds
      rw [hQq, hv]
      exact hfirst ⟨p.val, hold⟩ (by rwa [hv] at hp)
    · rw [hpr]
      exact (hQqa.trans har).le
    · rw [hps]
      exact (hQqa.trans (har.trans hrs)).le
  have hnewlow (p : criticalPoints (Vector 7) Q.function)
      (hp : 0 < Q.function p) (hpa : Q.function p ≤ a) :
      nativeMorseIndex (Vector 7) Q.function p ≤ 2 := by
    rcases (hcrit p.val).mp p.property with hold | hpr | hps
    · have hv := (hkeep p.val hold).self_of_nhds
      rw [nativeMorseIndex_congr_germ (hkeep p.val hold)]
      exact hlow ⟨p.val, hold⟩ (by rwa [hv] at hp) (by rwa [hv] at hpa)
    · exact (har.not_ge (hpr ▸ hpa)).elim
    · exact ((har.trans hrs).not_ge (hps ▸ hpa)).elim
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows Q.smooth Q.morse Q.distinct
  obtain ⟨T, _, _, _, hupper, _⟩ :=
    T₀.exists_same_flow_windows_avoiding_level Q.smooth Q.morse hgr
  obtain ⟨R, hcountcancel, hcritcancel, hindices, hnegativeR⟩ :=
    P.cancel_positive_one_two_pair_at_retained_cut Q A T ha hfr hgr heq hhigh
      (fun p hp hpa => (hlow p hp hpa).trans (by decide)) qQ rQ hqQ hir hqpositive hfirstQ
      (hupper qQ hQqa).le har hgap hnewlow
  have hneq : qQ.val ≠ rQ.val := fun h => (hQqa.trans har).ne (congrArg Q.function h)
  obtain ⟨hremove₁, hremove₂, hremoveOther⟩ := nativeMorseCount_adjacent_removed_of_index_eq
    Q.finite_criticalPoints qQ.property rQ.property hneq hcritcancel hindices hqQ hir
  have htotal : (criticalPoints (Vector 7) R.function).ncard =
      (criticalPoints (Vector 7) P.function).ncard :=
    Nat.add_right_cancel (hcountcancel.trans hcountbirth)
  have hcount₁ : nativeMorseCount (Vector 7) Q.function 1 =
      nativeMorseCount (Vector 7) P.function 1 :=
    hother 1 (by decide) (by decide)
  have hcountR₂ : nativeMorseCount (Vector 7) R.function 2 =
      nativeMorseCount (Vector 7) P.function 2 :=
    Nat.add_right_cancel (hremove₂.trans hcount₂)
  refine ⟨R, htotal, hremove₁.trans hcount₁,
    (hremoveOther 3 (by decide) (by decide)).trans hcount₃, ?_, ?_⟩
  · intro j hj1 hj3
    by_cases hj2 : j = 2
    · subst j
      exact hcountR₂
    · exact (hremoveOther j hj1 hj2).trans (hother j hj2 hj3)
  · intro w hw
    exact (hnegativeR w hw).trans (hnegative w hw)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
