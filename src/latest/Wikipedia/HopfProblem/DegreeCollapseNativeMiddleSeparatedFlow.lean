import Wikipedia.HopfProblem.DegreeCollapseMiddleFlowSeparation
import Wikipedia.HopfProblem.DegreeCollapseH2ZeroMiddleElimination

/-!
# A constructed native flow with separated middle basins

Realize the entire middle block at the actual first upper level. Its full
canonical attaching sections exclude every nonconstant middle-to-middle
trajectory for that same flow. All original critical chart germs are kept.
The compact simply connected H2-zero manifold supplies the middle-only
Morse system, so no separated flow or homotopy-sphere premise is an input.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
  (S : AdaptedSurgeryWindows E f)

theorem middle_label_surjective
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (n : ℕ) (hn : 0 + n < S.toSurgeryWindows.count)
    (hcount : n + 2 = S.toSurgeryWindows.count)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3) :
    ∃ j : Fin n, nativeMiddleBlockPoint S 0 n hn j = q := by
  let W := S.toSurgeryWindows
  have hpos := W.count_pos hf
  obtain ⟨i, rfl⟩ := W.point.surjective q
  have hfirst : nativeMorseIndex E f (W.first hpos) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (W.first hpos)).chart).trans (W.first_index_zero hf hpos)
  have hlast : nativeMorseIndex E f (W.last hpos) = 6 :=
    (nativeMorseIndex_eq_chart (S.data (W.last hpos)).chart).trans
      ((W.last_index_dimension hf hpos).trans hdim)
  have hi0 : i.val ≠ 0 := by
    intro hi
    have he : W.point i = W.first hpos := congrArg W.point (Fin.ext hi)
    rw [he, hfirst] at hq
    omega
  have hilast : i.val ≠ W.count - 1 := by
    intro hi
    have he : W.point i = W.last hpos := congrArg W.point (Fin.ext hi)
    rw [he, hlast] at hq
    omega
  let j : Fin n := ⟨i.val - 1, by have hi := i.isLt; change n + 2 = W.count at hcount; omega⟩
  refine ⟨j, ?_⟩
  apply congrArg W.point
  apply Fin.ext
  change 0 + (i.val - 1) + 1 = i.val
  omega

theorem middle_label_above_first_cut
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n : ℕ) (hn : 0 + n < S.toSurgeryWindows.count) (j : Fin n) :
    S.toSurgeryWindows.upper (S.toSurgeryWindows.first (S.toSurgeryWindows.count_pos hf)) <
      S.toSurgeryWindows.lower (nativeMiddleBlockPoint S 0 n hn j) := by
  apply S.toSurgeryWindows.separated
  apply S.toSurgeryWindows.point_strictMono
  change 0 < 0 + j.val + 1
  omega

theorem exists_separated_middle_flow
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hone : nativeMorseCount E f 1 = 0) (htwo : nativeMorseCount E f 2 = 0)
    (hfour : nativeMorseCount E f 4 = 0) (hfive : nativeMorseCount E f 5 = 0) :
    let a := S.toSurgeryWindows.upper (S.toSurgeryWindows.first (S.toSurgeryWindows.count_pos hf))
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ p, (T.data p).chart = (S.data p).chart) ∧
      (∀ p, (T.data p).radius < (S.data p).radius) ∧
      (∀ p ∈ criticalPoints E f, ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
      NoMiddleConnections T ∧
      ∀ (p : criticalPoints E f), nativeMorseIndex E f p = 3 →
        a < T.toSurgeryWindows.lower p ∧
        ∀ u : sphere (0 : (T.data p).chart.NegativeCoordinates) 1,
          ((T.data p).surgery.attachingSphere u).val ∈ FlowCancellation.levelBasin T.flow f a := by
  let a := S.toSurgeryWindows.upper (S.toSurgeryWindows.first (S.toSurgeryWindows.count_pos hf))
  obtain ⟨r, n, hprefix, hn, hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr, -⟩ := native_middle_block_counts S.toSurgeryWindows hf r n hprefix hn hthree hafter
  have hr0 : r = 0 := hr.symm.trans htwo
  clear hr
  subst r
  have hcount : n + 2 = S.toSurgeryWindows.count := by
    simpa only [Nat.zero_add] using middle_blocks_complete_of_no_four_five
      S.toSurgeryWindows hf hdim 0 n hprefix hn hthree hafter hsix hfour hfive
  let p := nativeMiddleBlockPoint S 0 n hn
  have hp (j : Fin n) : nativeMorseIndex E f (p j) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hthree ⟨0 + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  have ha := (S.data (S.toSurgeryWindows.first (S.toSurgeryWindows.count_pos hf))).upper_regular
  obtain ⟨T, hcharts, hradii, hgerms, α, hα⟩ :=
    S.exists_ordered_middle_family hf hm hdim 0 n hn hthree
      (fun q => (S.data q).radius) (fun q => (S.data q).radius_pos)
  obtain ⟨γ, hγ, -, horbit⟩ := T.exists_canonical_middle_family hf ha p hp α hα
  let _ := RegularLevel.chartedSpace hf ha
  have habove (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3) : a < f q := by
    obtain ⟨j, rfl⟩ := middle_label_surjective S hf hdim n hn hcount q hq
    exact (middle_label_above_first_cut S hf n hn j).trans
      (S.toSurgeryWindows.lower_lt_value (p j))
  have hsections (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3) :
      ∃ δ : C(Hemisphere.Sphere 2, {y : M // f y = a}), ∀ x, ∃ t : ℝ,
        T.flow t (nativeIndexThreeAttachingSphere T q hq x).val = (δ x).val := by
    obtain ⟨j, rfl⟩ := middle_label_surjective S hf hdim n hn hcount q hq
    exact ⟨⟨γ j, (hγ.1 j).continuous⟩, horbit j⟩
  refine ⟨T, hcharts, hradii, hgerms, noMiddleConnections_of_sections T hf habove hsections, ?_⟩
  intro q hq
  obtain ⟨j, rfl⟩ := middle_label_surjective S hf hdim n hn hcount q hq
  constructor
  · have hsep := middle_label_above_first_cut S hf n hn j
    have hrad := hradii (p j)
    have hpos := (T.data (p j)).radius_pos
    have hpos' := (S.data (p j)).radius_pos
    change a < f (p j) - (S.data (p j)).radius ^ 2 at hsep
    change a < f (p j) - (T.data (p j)).radius ^ 2
    nlinarith
  · intro u
    let _ : Fact (Module.finrank ℝ (T.data (p j)).chart.NegativeCoordinates = 2 + 1) :=
      ⟨(nativeMorseIndex_eq_chart (T.data (p j)).chart).symm.trans (hp j)⟩
    obtain ⟨z, rfl⟩ := (SphereCoordinates.standardParametrization
      (T.data (p j)).chart.NegativeCoordinates 2).surjective u
    obtain ⟨t, ht⟩ := horbit j z
    exact ⟨t, (congrArg f ht).trans (γ j z).property⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality
