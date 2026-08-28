import Wikipedia.HopfProblem.DegreeCollapsePositiveThreeFourBirthAtCut
import Wikipedia.HopfProblem.DegreeCollapsePositiveTwoThreeCancellation
import Wikipedia.HopfProblem.DegreeCollapseTwoRegularCutWindows
import Wikipedia.HopfProblem.DegreeCollapsePositiveIndexCut
import Wikipedia.HopfProblem.DegreeCollapseIndexedRemovalCount

/-!
# The actual positive two-to-four handle trade on the original collared state

Construct a positive three/four cut, perform a supported three/four birth,
and cancel the first positive two-handle with the new three-handle using
the constructed meridian, native isotopy, and actual transverse flow tubes.
Total critical count and the entire original nonpositive germ are retained.
Index two decreases by one, index four increases by one, and every other
indexed count stays unchanged.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris

variable {B : Type} [TopologicalSpace B] [SimplyConnectedSpace B]
  [Subsingleton (SingularHomology B 2)] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_positive_two_to_four_handle_trade
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hlower : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      2 ≤ nativeMorseIndex (Vector 7) P.function p)
    (q₀ : criticalPoints (Vector 7) P.function) (hq₀ : 0 < P.function q₀)
    (hi₀ : nativeMorseIndex (Vector 7) P.function q₀ = 2) :
    ∃ R : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) R.function).ncard =
        (criticalPoints (Vector 7) P.function).ncard ∧
      nativeMorseCount (Vector 7) R.function 2 + 1 = nativeMorseCount (Vector 7) P.function 2 ∧
      nativeMorseCount (Vector 7) R.function 4 = nativeMorseCount (Vector 7) P.function 4 + 1 ∧
      (∀ j, j ≠ 2 → j ≠ 4 →
        nativeMorseCount (Vector 7) R.function j = nativeMorseCount (Vector 7) P.function j) ∧
      ∀ w, S.time w ≤ 0 → R.function =ᶠ[𝓝 w] P.function := by
  classical
  obtain ⟨q, hq, hi, hfirst⟩ :=
    P.exists_first_positive_of_index_lower_bound horder hlower q₀ hq₀ hi₀
  obtain ⟨A⟩ := nonempty_adaptedSurgeryWindows P.smooth P.morse P.distinct
  obtain ⟨a, ha, hfr, hqa, hhigh, hlow⟩ := A.exists_ordered_index_cut_above 0 horder q hq
    (show nativeMorseIndex (Vector 7) P.function q ≤ 3 by omega)
  have hneg : Module.finrank ℝ (A.data q).chart.NegativeCoordinates = 2 :=
    (nativeMorseIndex_eq_chart (A.data q).chart).symm.trans hi
  have hsplit := (A.data q).chart.finrank_negative_add_positive
  simp only [finrank_euclideanSpace_fin] at hsplit
  let : Fact (Module.finrank ℝ (A.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  obtain ⟨v, t, ht⟩ := A.exists_belt_point_reaching_level_above_cut P.smooth q 4 hq hqa
    hlow (by decide)
  let z : {y : S.Space // P.function y = a} :=
    ⟨A.flow t ((A.data q).surgery.beltSphere v).val, ht⟩
  obtain ⟨Q, r, s, hir, his, har, hrs, hcountbirth, hcrit, hkeep, hnegative,
      heq, hgr, hgap, hcount₃, hcount₄, hother⟩ :=
    P.exists_positive_three_four_birth_above_cut A ha hfr z
  let qQ : criticalPoints (Vector 7) Q.function :=
    ⟨q.val, (hcrit q.val).mpr (Or.inl q.property)⟩
  let rQ : criticalPoints (Vector 7) Q.function :=
    ⟨r, (hcrit r).mpr (Or.inr (Or.inl rfl))⟩
  have hQq : Q.function qQ = P.function q := (hkeep q.val q.property).self_of_nhds
  have hqQ : nativeMorseIndex (Vector 7) Q.function qQ = 2 :=
    (nativeMorseIndex_congr_germ (hkeep q.val q.property)).trans hi
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
      nativeMorseIndex (Vector 7) Q.function p ≤ 3 := by
    rcases (hcrit p.val).mp p.property with hold | hpr | hps
    · have hv := (hkeep p.val hold).self_of_nhds
      rw [nativeMorseIndex_congr_germ (hkeep p.val hold)]
      exact hlow ⟨p.val, hold⟩ (by rwa [hv] at hp) (by rwa [hv] at hpa)
    · exact (har.not_ge (hpr ▸ hpa)).elim
    · exact ((har.trans hrs).not_ge (hps ▸ hpa)).elim
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows Q.smooth Q.morse Q.distinct
  obtain ⟨T, _, _, _, _, _, hzeroLower, hupper, _⟩ :=
    T₀.exists_same_flow_windows_avoiding_two_levels Q.smooth Q.morse
      (RegularTimeMorse.regular_zero_not_critical Q.regular) hgr
  obtain ⟨R, hcountcancel, hcritcancel, hindices, hnegativeR⟩ :=
    P.cancel_positive_two_three_pair_at_retained_cut Q A T ha hfr hgr heq hhigh hlow
      qQ rQ hqQ hir hqpositive hfirstQ (hzeroLower qQ hqpositive).le
      (hupper qQ hQqa).le har hgap hnewlow
  have hneq : qQ.val ≠ rQ.val := fun h => (hQqa.trans har).ne (congrArg Q.function h)
  obtain ⟨hremove₂, hremove₃, hremoveOther⟩ := nativeMorseCount_adjacent_removed_of_index_eq
    Q.finite_criticalPoints qQ.property rQ.property hneq hcritcancel hindices hqQ hir
  have htotal : (criticalPoints (Vector 7) R.function).ncard =
      (criticalPoints (Vector 7) P.function).ncard :=
    Nat.add_right_cancel (hcountcancel.trans hcountbirth)
  have hcount₂ : nativeMorseCount (Vector 7) Q.function 2 =
      nativeMorseCount (Vector 7) P.function 2 := hother 2 (by decide) (by decide)
  have hcountR₃ : nativeMorseCount (Vector 7) R.function 3 =
      nativeMorseCount (Vector 7) P.function 3 :=
    Nat.add_right_cancel (hremove₃.trans hcount₃)
  refine ⟨R, htotal, hremove₂.trans hcount₂,
    (hremoveOther 4 (by decide) (by decide)).trans hcount₄, ?_, ?_⟩
  · intro j hj2 hj4
    by_cases hj3 : j = 3
    · subst j
      exact hcountR₃
    · exact (hremoveOther j hj2 hj3).trans (hother j hj3 hj4)
  · intro w hw
    exact (hnegativeR w hw).trans (hnegative w hw)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
