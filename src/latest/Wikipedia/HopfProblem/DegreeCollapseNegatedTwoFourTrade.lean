import Wikipedia.HopfProblem.DegreeCollapseNegatedMorseOrder
import Wikipedia.HopfProblem.DegreeCollapsePositiveDualThreeFourCut
import Wikipedia.HopfProblem.DegreeCollapseSublevelThreeFourBirthAtCut
import Wikipedia.HopfProblem.DegreeCollapseDualTwoThreeCancellation
import Wikipedia.HopfProblem.DegreeCollapseIndexedRemovalCount

/-!
# The supported two-to-four trade for the negated original presentation

The positive index ordering, absence of index six, and unique positive
maximum supply a first negative two-handle and a unique minimum below
zero. Construct a three/four birth, place its whole attaching sphere on
the actual transverse meridian, and cancel the two/three pair. The full
upper germ stays fixed and the exact indexed count change is proved.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation SingularMayerVietoris
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] [Subsingleton (SingularHomology B 2)]
  {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_negated_two_to_four_handle_trade
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (hmaximum : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → 0 < P.function q →
      nativeMorseIndex (Vector 7) P.function p = 7 →
      nativeMorseIndex (Vector 7) P.function q = 7 → p = q)
    (hnosix : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      nativeMorseIndex (Vector 7) P.function p ≠ 6)
    (p₀ : criticalPoints (Vector 7) P.function) (hp₀ : 0 < P.function p₀)
    (hindex₀ : nativeMorseIndex (Vector 7) P.function p₀ = 5) :
    ∃ h : S.Space → ℝ, ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ h ∧ IsMorse (Vector 7) h ∧
      InjOn h (criticalPoints (Vector 7) h) ∧
      (criticalPoints (Vector 7) h).ncard =
        (criticalPoints (Vector 7) (fun x => -P.function x)).ncard ∧
      nativeMorseCount (Vector 7) h 2 + 1 =
        nativeMorseCount (Vector 7) (fun x => -P.function x) 2 ∧
      nativeMorseCount (Vector 7) h 4 =
        nativeMorseCount (Vector 7) (fun x => -P.function x) 4 + 1 ∧
      (∀ j, j ≠ 2 → j ≠ 4 → nativeMorseCount (Vector 7) h j =
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
    P.exists_negated_three_four_cut horder p₀ hp₀ hindex₀
  let q₀ : criticalPoints (Vector 7) f := ⟨p₀.val, hcritf.symm ▸ p₀.property⟩
  have hq₀two : nativeMorseIndex (Vector 7) f q₀ = 2 := by
    have hs : nativeMorseIndex (Vector 7) f q₀ +
        nativeMorseIndex (Vector 7) P.function p₀ = 7 := P.negated_native_index_add q₀
    omega
  have hnoone (p : criticalPoints (Vector 7) f) (hp : f p < 0) :
      nativeMorseIndex (Vector 7) f p ≠ 1 := by
    intro hi
    let pP : criticalPoints (Vector 7) P.function := ⟨p.val, hcritf ▸ p.property⟩
    have hs : nativeMorseIndex (Vector 7) f p +
        nativeMorseIndex (Vector 7) P.function pP = 7 := P.negated_native_index_add p
    exact hnosix pP (neg_neg_iff_pos.mp hp) (by omega)
  obtain ⟨q, hqnegative, hqtwo, hbefore⟩ := T.exists_first_index_two_below_cut 0
    (P.negated_index_order_below_zero horder) hnoone q₀ (neg_neg_of_pos hp₀) hq₀two
  have hqa : f q < a := by
    apply lt_of_not_ge
    intro haq
    have hh := hhighN q haq hqnegative
    simp only [GLOrthonormalization.Vector] at hh hqtwo
    omega
  have hneg : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 2 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hqtwo
  have hsplit := (T.data q).chart.finrank_negative_add_positive
  simp only [finrank_euclideanSpace_fin] at hsplit
  let : Fact (Module.finrank ℝ (T.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by omega⟩
  obtain ⟨v, t, ht⟩ := T.exists_belt_point_reaching_level hf q 4 hqa hlowN (by decide)
  let z : {y : S.Space // f y = a} := ⟨T.flow t ((T.data q).surgery.beltSphere v).val, ht⟩
  obtain ⟨g, r, s, hg, hmg, hinjg, hir, his, har, hrs, hsnegative, hbirth, hcrit,
      hkeep, hupper, hcut, heq, hgr, hgap, hcount₃, hcount₄, hother⟩ :=
    exists_three_four_birth_between_cuts hf hm T (by simp) ha hreg z
  obtain ⟨m₀, hmpositive, hmseven, _⟩ := P.exists_positive_index_seven_point
  let mF : criticalPoints (Vector 7) f := ⟨m₀.val, hcritf.symm ▸ m₀.property⟩
  let mG : criticalPoints (Vector 7) g :=
    ⟨mF.val, (hcrit mF.val).mpr (Or.inl mF.property)⟩
  let qG : criticalPoints (Vector 7) g :=
    ⟨q.val, (hcrit q.val).mpr (Or.inl q.property)⟩
  let rG : criticalPoints (Vector 7) g := ⟨r, (hcrit r).mpr (Or.inr (Or.inl rfl))⟩
  have hqG : nativeMorseIndex (Vector 7) g qG = 2 :=
    (nativeMorseIndex_congr_germ (hkeep q.val q.property)).trans hqtwo
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
      nativeMorseIndex (Vector 7) g p ≤ 3 := by
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
    P.cancel_dual_two_three_pair_at_retained_fiber A (neg_pos.mpr ha) hregP
      hhighP hlowP
      hg hmg hinjg hgr hfiber mG qG rG hqG hir hbeforeG hminimumG hqcut har
      (hrs.trans hsnegative) hgap hnewlow
  have hneq : qG.val ≠ rG.val := fun h => (hqcut.trans har).ne (congrArg g h)
  obtain ⟨hremove₂, hremove₃, hremoveOther⟩ := nativeMorseCount_adjacent_removed_of_index_eq
    (Wikipedia.SmoothSixDPoincare.ManifoldMorse.finite_criticalPoints hg hmg)
      qG.property rG.property hneq hcritH hindicesH hqG hir
  have htotal : (criticalPoints (Vector 7) h).ncard = (criticalPoints (Vector 7) f).ncard :=
    Nat.add_right_cancel (hcancel.trans hbirth)
  have hcount₂ : nativeMorseCount (Vector 7) g 2 = nativeMorseCount (Vector 7) f 2 :=
    hother 2 (by decide) (by decide)
  have hcountH₃ : nativeMorseCount (Vector 7) h 3 = nativeMorseCount (Vector 7) f 3 :=
    Nat.add_right_cancel (hremove₃.trans hcount₃)
  refine ⟨h, hh, hmh, hinjh, htotal, hremove₂.trans hcount₂,
    (hremoveOther 4 (by decide) (by decide)).trans hcount₄, ?_, ?_, ?_⟩
  · intro j hj2 hj4
    by_cases hj3 : j = 3
    · subst j
      exact hcountH₃
    · exact (hremoveOther j hj2 hj3).trans (hother j hj3 hj4)
  · intro x hx
    exact (hupperH x (by rw [(hupper x hx).self_of_nhds]; exact hx)).trans (hupper x hx)
  · intro x
    exact (hcutH x).trans (hcut x)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
