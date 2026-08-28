import Wikipedia.HopfProblem.DegreeCollapseNegatedMorseOrder
import Wikipedia.HopfProblem.DegreeCollapsePositiveDualCut
import Wikipedia.HopfProblem.DegreeCollapseSublevelBirthAtCut
import Wikipedia.HopfProblem.DegreeCollapseDualOneTwoCancellation
import Wikipedia.HopfProblem.DegreeCollapseIndexedRemovalCount

/-!
# The actual supported one-to-three trade for the negated presentation

The original positive index ordering and unique positive maximum supply
the negative cut, first one-handle, and unique minimum below zero.
Construct the two/three birth below zero, retain the original fiber,
and cancel the actual one/two pair. The complete upper germ stays fixed,
total count is unchanged, and the exact indexed trade is established.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_negated_one_to_three_handle_trade
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hmaximum : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → 0 < P.function q →
      nativeMorseIndex (Vector 7) P.function p = 7 →
      nativeMorseIndex (Vector 7) P.function q = 7 → p = q)
    (p₀ : criticalPoints (Vector 7) P.function) (hp₀ : 0 < P.function p₀)
    (hindex₀ : nativeMorseIndex (Vector 7) P.function p₀ = 6) :
    ∃ h : S.Space → ℝ, ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ h ∧ IsMorse (Vector 7) h ∧
      InjOn h (criticalPoints (Vector 7) h) ∧
      (criticalPoints (Vector 7) h).ncard =
        (criticalPoints (Vector 7) (fun x => -P.function x)).ncard ∧
      nativeMorseCount (Vector 7) h 1 + 1 =
        nativeMorseCount (Vector 7) (fun x => -P.function x) 1 ∧
      nativeMorseCount (Vector 7) h 3 =
        nativeMorseCount (Vector 7) (fun x => -P.function x) 3 + 1 ∧
      (∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount (Vector 7) h j =
        nativeMorseCount (Vector 7) (fun x => -P.function x) j) ∧
      (∀ x, 0 ≤ -P.function x → h =ᶠ[𝓝 x] (fun y => -P.function y)) ∧
      ∀ x, h x < 0 ↔ -P.function x < 0 := by
  classical
  let f : S.Space → ℝ := fun x => -P.function x
  have hf : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ f := P.smooth.neg
  have hm : IsMorse (Vector 7) f := isMorse_neg P.morse
  have hcritf : criticalPoints (Vector 7) f = criticalPoints (Vector 7) P.function :=
    criticalPoints_neg P.function
  obtain ⟨T, a, ha, _, hreg, hhighN, hlowN, _, hregP, hhighP, hlowP⟩ :=
    P.exists_negated_two_three_cut horder p₀ hp₀ hindex₀
  let q₀ : criticalPoints (Vector 7) f := ⟨p₀.val, hcritf.symm ▸ p₀.property⟩
  have hq₀one : nativeMorseIndex (Vector 7) f q₀ = 1 := by
    have hs : nativeMorseIndex (Vector 7) f q₀ +
        nativeMorseIndex (Vector 7) P.function p₀ = 7 := P.negated_native_index_add q₀
    omega
  obtain ⟨q, hqnegative, hqone, hbefore⟩ := T.exists_first_index_one_below_cut 0
    (P.negated_index_order_below_zero horder) q₀ (neg_neg_of_pos hp₀) hq₀one
  have hqa : f q < a := by
    apply lt_of_not_ge
    intro haq
    have hh := hhighN q haq hqnegative
    simp only [GLOrthonormalization.Vector] at hh hqone
    omega
  have hneg : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hqone
  have hsplit := (T.data q).chart.finrank_negative_add_positive
  simp only [finrank_euclideanSpace_fin] at hsplit
  let : Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 5 + 1) := ⟨by omega⟩
  obtain ⟨v, t, ht⟩ := T.exists_belt_point_reaching_level hf q 5 hqa hlowN (by decide)
  let z : {y : S.Space // f y = a} := ⟨T.flow t ((T.data q).surgery.beltSphere v).val, ht⟩
  obtain ⟨g, r, s, hg, hmg, hinjg, hir, his, har, hrs, hsnegative, hbirth, hcrit,
      hkeep, hupper, hcut, heq, hgr, hgap, hcount₂, hcount₃, hother⟩ :=
    exists_two_three_birth_between_cuts hf hm T (by simp) ha hreg z
  obtain ⟨m₀, hmpositive, hmseven, _⟩ := P.exists_positive_index_seven_point
  let mF : criticalPoints (Vector 7) f := ⟨m₀.val, hcritf.symm ▸ m₀.property⟩
  have hmzero : nativeMorseIndex (Vector 7) f mF = 0 := by
    have hs : nativeMorseIndex (Vector 7) f mF +
        nativeMorseIndex (Vector 7) P.function m₀ = 7 := P.negated_native_index_add mF
    omega
  let mG : criticalPoints (Vector 7) g :=
    ⟨mF.val, (hcrit mF.val).mpr (Or.inl mF.property)⟩
  let qG : criticalPoints (Vector 7) g :=
    ⟨q.val, (hcrit q.val).mpr (Or.inl q.property)⟩
  let rG : criticalPoints (Vector 7) g := ⟨r, (hcrit r).mpr (Or.inr (Or.inl rfl))⟩
  have hmG : nativeMorseIndex (Vector 7) g mG = 0 :=
    (nativeMorseIndex_congr_germ (hkeep mF.val mF.property)).trans hmzero
  have hqG : nativeMorseIndex (Vector 7) g qG = 1 :=
    (nativeMorseIndex_congr_germ (hkeep q.val q.property)).trans hqone
  have hvalueq : g qG = f q := (hkeep q.val q.property).self_of_nhds
  have hqcut : g qG < a := by rw [hvalueq]; exact hqa
  have hbeforeG (p : criticalPoints (Vector 7) g) (hp : g p < g qG) :
      nativeMorseIndex (Vector 7) g p = 0 := by
    rcases (hcrit p.val).mp p.property with hold | hpr | hps
    · have hv := (hkeep p.val hold).self_of_nhds
      rw [nativeMorseIndex_congr_germ (hkeep p.val hold)]
      apply hbefore ⟨p.val, hold⟩
      change f p.val < f q
      rw [← hv, ← hvalueq]
      exact hp
    · exact (lt_asymm (hqcut.trans har) (hpr ▸ hp)).elim
    · exact (lt_asymm (hqcut.trans (har.trans hrs)) (hps ▸ hp)).elim
  have hminimumG (p : criticalPoints (Vector 7) g) (hp : g p < 0)
      (hpzero : nativeMorseIndex (Vector 7) g p = 0) : p = mG := by
    rcases (hcrit p.val).mp p.property with hold | hpr | hps
    · let pF : criticalPoints (Vector 7) f := ⟨p.val, hold⟩
      let pP : criticalPoints (Vector 7) P.function := ⟨p.val, hcritf ▸ hold⟩
      have hfzero : nativeMorseIndex (Vector 7) f pF = 0 :=
        (nativeMorseIndex_congr_germ (hkeep p.val hold)).symm.trans hpzero
      have hs : nativeMorseIndex (Vector 7) f pF +
          nativeMorseIndex (Vector 7) P.function pP = 7 := P.negated_native_index_add pF
      have hseven : nativeMorseIndex (Vector 7) P.function pP = 7 := by omega
      have hnegative : f p.val < 0 := by rwa [(hkeep p.val hold).self_of_nhds] at hp
      have he := hmaximum pP m₀ (neg_neg_iff_pos.mp hnegative) hmpositive hseven hmseven
      exact Subtype.ext (congrArg (fun x : criticalPoints (Vector 7) P.function => x.val) he)
    · have hz : nativeMorseIndex (Vector 7) g r = 0 := hpr ▸ hpzero
      simp only [GLOrthonormalization.Vector] at hz hir
      omega
    · have hz : nativeMorseIndex (Vector 7) g s = 0 := hps ▸ hpzero
      simp only [GLOrthonormalization.Vector] at hz his
      omega
  have hnewlow (p : criticalPoints (Vector 7) g) (hp : g p ≤ a) :
      nativeMorseIndex (Vector 7) g p ≤ 2 := by
    rcases (hcrit p.val).mp p.property with hold | hpr | hps
    · have hv := (hkeep p.val hold).self_of_nhds
      rw [nativeMorseIndex_congr_germ (hkeep p.val hold)]
      exact hlowN ⟨p.val, hold⟩ (by rwa [hv] at hp)
    · exact (har.not_ge (hpr ▸ hp)).elim
    · exact ((har.trans hrs).not_ge (hps ▸ hp)).elim
  have hfiber (y : S.Space) : g y = a ↔ P.function y = -a := by
    apply (heq y).trans
    change (-P.function y = a ↔ P.function y = -a)
    constructor <;> intro hy <;> linarith
  obtain ⟨A⟩ := nonempty_adaptedSurgeryWindows P.smooth P.morse P.distinct
  obtain ⟨h, hh, hmh, hinjh, hcancel, hcritH, hindicesH, hupperH, hcutH⟩ :=
    P.cancel_dual_one_two_pair_at_retained_fiber A (neg_pos.mpr ha) hregP
      (fun p hp => (by decide : 3 ≤ 5).trans (hhighP p hp)) hlowP
      hg hmg hinjg hgr hfiber mG qG rG hmG hqG hir hbeforeG hminimumG hqcut har
      (hrs.trans hsnegative) hgap hnewlow
  have hneq : qG.val ≠ rG.val := fun h => (hqcut.trans har).ne (congrArg g h)
  obtain ⟨hremove₁, hremove₂, hremoveOther⟩ := nativeMorseCount_adjacent_removed_of_index_eq
    (Wikipedia.SmoothSixDPoincare.ManifoldMorse.finite_criticalPoints hg hmg)
      qG.property rG.property hneq hcritH hindicesH hqG hir
  have htotal : (criticalPoints (Vector 7) h).ncard = (criticalPoints (Vector 7) f).ncard :=
    Nat.add_right_cancel (hcancel.trans hbirth)
  have hcount₁ : nativeMorseCount (Vector 7) g 1 = nativeMorseCount (Vector 7) f 1 :=
    hother 1 (by decide) (by decide)
  have hcountH₂ : nativeMorseCount (Vector 7) h 2 = nativeMorseCount (Vector 7) f 2 :=
    Nat.add_right_cancel (hremove₂.trans hcount₂)
  refine ⟨h, hh, hmh, hinjh, htotal, hremove₁.trans hcount₁,
    (hremoveOther 3 (by decide) (by decide)).trans hcount₃, ?_, ?_, ?_⟩
  · intro j hj1 hj3
    by_cases hj2 : j = 2
    · subst j
      exact hcountH₂
    · exact (hremoveOther j hj1 hj2).trans (hother j hj2 hj3)
  · intro x hx
    exact (hupperH x (by rw [(hupper x hx).self_of_nhds]; exact hx)).trans (hupper x hx)
  · intro x
    exact (hcutH x).trans (hcut x)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
