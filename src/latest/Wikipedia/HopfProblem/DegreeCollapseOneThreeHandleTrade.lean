import Wikipedia.HopfProblem.DegreeCollapseUniqueMinimumOneTwoCancellation
import Wikipedia.HopfProblem.DegreeCollapseBirthCutIndexControl
import Wikipedia.HopfProblem.DegreeCollapseIndexedRemovalCount

/-!
# An actual one-to-three handle trade at a regular middle cut

A supported indexed two/three birth is constructed in the supplied regular
band above the middle cut. Its exact critical-set, value, germ, and index
formulas supply every hypothesis of the unique-minimum one/two cancellation.
The resulting excellent Morse function has the same total critical count,
one fewer index-one point, one more index-three point, and all other index
counts unchanged. No newborn function or geometric cancellation data is input.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}

open Classical in
theorem exists_one_to_three_handle_trade
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    (m q : criticalPoints E f) (hm0 : nativeMorseIndex E f m = 0)
    (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : criticalPoints E f, nativeMorseIndex E f z = 0 → z = m)
    {a l u : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hhigh : ∀ z : criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2)
    (hqa : f q < a) (hal : a < l)
    (hband : ∀ y, f y ∈ Ioo a u → y ∉ criticalPoints E f)
    {x : M} (hx : f x ∈ Ioo l u) :
    ∃ h : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧ IsMorse E h ∧
      InjOn h (criticalPoints E h) ∧ (criticalPoints E h).ncard = (criticalPoints E f).ncard ∧
      nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
      nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
      ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  let U : Set M := f ⁻¹' Ioo l u
  have hU : IsOpen U := isOpen_Ioo.preimage hf.continuous
  have hbirthband : ∀ y, f y ∈ Ioo l u → y ∉ criticalPoints E f :=
    fun y hy => hband y ⟨hal.trans hy.1, hy.2⟩
  obtain ⟨g, b₂, b₃, hg, hmg, hinjg, -, -, hi₂, hi₃, h₂₃, hv₂, hv₃,
      hcountbirth, hcrit, hexterior, hkeep, hcount₂, hcount₃, hcountOther⟩ :=
    exists_excellent_indexed_morse_birth hf hm S.distinct hbirthband hx
      (k := 2) (by omega) hU hx
  have hcrit' (z : M) (hz : z ∈ criticalPoints E g) :
      z ∈ criticalPoints E f ∨ z = b₂ ∨ z = b₃ := (hcrit z).mp hz
  have hab₂ : a < g b₂ := hal.trans hv₂.1
  have hab₃ : a < g b₃ := hal.trans hv₃.1
  obtain ⟨heq, -⟩ := birth_preserves_lower_levels hf.continuous hg
    (show U ⊆ {y : M | l < f y} from fun _ hy => hy.1) hexterior hkeep hcrit'
      hv₂.1.le hv₃.1.le hal
  have hgr := regular_level_of_retained_critical_germs hreg hcrit' hkeep hab₂ hab₃
  have hgap := birth_first_new_value_gap hcrit' hkeep hreg hband hv₂.2 h₂₃
  have hnewlow := birth_preserves_lower_index_bound hcrit' hkeep hab₂ hab₃ hlow
  let mg : criticalPoints E g := ⟨m.val, (hcrit m.val).mpr (Or.inl m.property)⟩
  let qg : criticalPoints E g := ⟨q.val, (hcrit q.val).mpr (Or.inl q.property)⟩
  let rg : criticalPoints E g := ⟨b₂, (hcrit b₂).mpr (Or.inr (Or.inl rfl))⟩
  have hmg0 : nativeMorseIndex E g mg = 0 :=
    (nativeMorseIndex_congr_germ (hkeep m.val m.property)).trans hm0
  have hqg1 : nativeMorseIndex E g qg = 1 :=
    (nativeMorseIndex_congr_germ (hkeep q.val q.property)).trans hq1
  have hminG : ∀ z : criticalPoints E g, nativeMorseIndex E g z = 0 → z = mg := by
    intro z hz
    apply Subtype.ext
    exact birth_preserves_unique_index_zero m hcrit' hkeep
      (by rw [hi₂]; omega) (by rw [hi₃]; omega) hminimum z.val z.property hz
  have hqga : g qg < a := by
    change g q.val < a
    rw [(hkeep q.val q.property).self_of_nhds]
    exact hqa
  obtain ⟨h, hh, hmh, hinjh, hcountcancel, hcritcancel, hindices⟩ :=
    cancel_one_two_pair_at_unchanged_cut_of_unique_minimum S hf hg hmg hinjg e hdim
      hreg hgr heq hhigh (fun z hz => (hlow z hz).trans (by omega))
      mg qg rg hmg0 hqg1 hi₂ hminG hqga hab₂ hgap hnewlow
  have hq₂ : qg.val ≠ rg.val := fun he => (hqga.trans hab₂).ne (congrArg g he)
  obtain ⟨hremove₁, hremove₂, hremoveOther⟩ := nativeMorseCount_adjacent_removed_of_index_eq
    (finite_criticalPoints hg hmg) qg.property rg.property hq₂ hcritcancel hindices hqg1 hi₂
  have htotal : (criticalPoints E h).ncard = (criticalPoints E f).ncard :=
    Nat.add_right_cancel (hcountcancel.trans hcountbirth)
  have hcount₁ : nativeMorseCount E g 1 = nativeMorseCount E f 1 :=
    hcountOther 1 (by omega) (by omega)
  have hcountₕ₂ : nativeMorseCount E h 2 = nativeMorseCount E f 2 :=
    Nat.add_right_cancel (hremove₂.trans hcount₂)
  refine ⟨h, hh, hmh, hinjh, htotal, hremove₁.trans hcount₁,
    (hremoveOther 3 (by omega) (by omega)).trans hcount₃, ?_⟩
  intro j hj1 hj3
  by_cases hj2 : j = 2
  · subst j
    exact hcountₕ₂
  · exact (hremoveOther j hj1 hj2).trans (hcountOther j hj2 hj3)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
