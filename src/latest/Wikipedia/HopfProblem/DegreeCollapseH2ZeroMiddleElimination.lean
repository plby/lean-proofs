import Wikipedia.HopfProblem.DegreeCollapseH2ZeroMiddleMatrix
import Wikipedia.HopfProblem.DegreeCollapseSimplyConnectedOuterElimination
import Wikipedia.HopfProblem.DegreeCollapseMinimalMiddleIndices
import Wikipedia.HopfProblem.DegreeCollapseMiddleBlocksExhausted

/-!
# Native Morse systems with only indices zero, three, and six

Actual H2 vanishing supplies the canonical middle matrix. Native geometric
cancellation excludes index two by total-count minimality; negation excludes
index four on the same function. Combining this with the constructed outer
elimination gives a native ordered system with unique extrema and only
middle handles on any compact simply connected H2-zero six-manifold.
No assumption on H3, homotopy-sphere equivalence, or duality theorem is used.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.HomologyVanishing


open SingularMayerVietoris

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M] [Subsingleton (SingularHomology M 2)] {f : M → ℝ}

theorem minimal_ordered_index_two_count_zero
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (hminimal : ∀ v : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v → IsMorse E v →
      InjOn v (criticalPoints E v) → (criticalPoints E f).ncard ≤
        (criticalPoints E v).ncard) : nativeMorseCount E f 2 = 0 := by
  obtain ⟨r, n, htwo, hrc, hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr, hn⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r n htwo hrc hthree hafter
  rw [hr]
  by_contra hnot
  have hrpos : 0 < r := Nat.pos_of_ne_zero hnot
  obtain ⟨T, -, hradii, -, α, hα⟩ := S.exists_ordered_middle_family hf hm hdim
    r n hrc hthree (fun p => (S.data p).radius) (fun p => (S.data p).radius_pos)
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  let a := S.toSurgeryWindows.upper q
  let p := nativeMiddleBlockPoint S r n hrc
  have hp (j : Fin n) : nativeMorseIndex E f (p j) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hthree ⟨r + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  have hlower (j : Fin n) : a < T.toSurgeryWindows.lower (p j) := by
    have hqj : f q < f (p j) :=
      S.toSurgeryWindows.point_strictMono (by change r < r + j.val + 1; omega)
    have hsep := S.separated q (p j) hqj
    have hh := mul_pos (sub_pos.mpr (hradii (p j)))
      (add_pos (S.data (p j)).radius_pos (T.data (p j)).radius_pos)
    change a < f (p j) - (T.data (p j)).radius ^ 2
    change a < f (p j) - (S.data (p j)).radius ^ 2 at hsep
    nlinarith
  obtain ⟨β, hβ, -, hβflow⟩ :=
    T.exists_canonical_middle_family hf (S.data q).upper_regular p hp α hα
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let γ : Fin n → C(S₂, {y : M // f y = a}) := fun j => ⟨β j, (hβ.1 j).continuous⟩
  let B := S.toSurgeryWindows.indexTwoBasis hf r (by omega) htwo
  have hsurj := canonical_middle_matrix_surjective S T hf hdim horder hzero hone
    r n hr hn hrc hp hlower B γ hβflow
  obtain ⟨hindex, hprimitive, hnull, hcut, hcomplete, hbelow,
    δ, hδ, -, B', -, hsurj'⟩ := exists_native_belt_cut_family S T hf hdim horder
      hzero hone r n hr hn hrpos hrc hradii hlower B γ hβ hsurj
  obtain ⟨v, hv, hmv, hinj, hcard⟩ := cancel_from_complete_middle_family
    T hf hm hdim horder q hindex hnull hprimitive hcut p hp hcomplete hbelow B' δ hδ hsurj'
  have hmin := hminimal v hv hmv hinj
  omega

theorem minimal_ordered_index_four_count_zero
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hsix : nativeMorseCount E f 6 = 1) (hfive : nativeMorseCount E f 5 = 0)
    (hminimal : ∀ v : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v → IsMorse E v →
      InjOn v (criticalPoints E v) → (criticalPoints E f).ncard ≤
        (criticalPoints E v).ncard) : nativeMorseCount E f 4 = 0 := by
  obtain ⟨T⟩ := nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
    (distinct_critical_values_neg S.distinct)
  have horderN : ∀ p q : criticalPoints E (fun x => -f x), -f p < -f q →
      nativeMorseIndex E (fun x => -f x) p ≤ nativeMorseIndex E (fun x => -f x) q := by
    intro p q hpq
    let pf : criticalPoints E f := ⟨p.val, by simpa only [criticalPoints_neg] using p.property⟩
    let qf : criticalPoints E f := ⟨q.val, by simpa only [criticalPoints_neg] using q.property⟩
    have hrev := horder qf pf (neg_lt_neg_iff.mp hpq)
    have hp := nativeMorseIndex_neg_add (S.data pf).chart
    have hq := nativeMorseIndex_neg_add (S.data qf).chart
    change nativeMorseIndex E f q.val ≤ nativeMorseIndex E f p.val at hrev
    change nativeMorseIndex E (fun x => -f x) p.val + nativeMorseIndex E f p.val = _ at hp
    change nativeMorseIndex E (fun x => -f x) q.val + nativeMorseIndex E f q.val = _ at hq
    omega
  have hn6 := nativeMorseCount_neg hf hm (k := 6) (by omega)
  have hn5 := nativeMorseCount_neg hf hm (k := 5) (by omega)
  have hn4 := nativeMorseCount_neg hf hm (k := 4) (by omega)
  simp only [hdim, Nat.reduceSub] at hn6 hn5 hn4
  have hh := minimal_ordered_index_two_count_zero T hf.neg (isMorse_neg hm)
    hdim horderN (hn6.trans hsix) (hn5.trans hfive) (minimal_excellent_morse_neg hminimal)
  rwa [hn4] at hh

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.HomologyVanishing

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.SimplyConnected

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]

variable (E M) in
theorem exists_minimal_ordered_morse_with_only_middle_handles
    (hdim : Module.finrank ℝ E = 6) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse E f ∧
      ∃ S : AdaptedSurgeryWindows E f,
        (∀ p q : criticalPoints E f, f p < f q →
          nativeMorseIndex E f p ≤ nativeMorseIndex E f q) ∧
        nativeMorseCount E f 0 = 1 ∧ nativeMorseCount E f 6 = 1 ∧
        nativeMorseCount E f 1 = 0 ∧ nativeMorseCount E f 2 = 0 ∧
        nativeMorseCount E f 4 = 0 ∧ nativeMorseCount E f 5 = 0 ∧
        (∀ p : criticalPoints E f,
          nativeMorseIndex E f p = 0 ∨ nativeMorseIndex E f p = 3 ∨
            nativeMorseIndex E f p = 6) ∧
        ∀ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g → IsMorse E g →
          InjOn g (criticalPoints E g) →
          (criticalPoints E f).ncard ≤ (criticalPoints E g).ncard := by
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩ :=
    exists_minimal_ordered_morse_system_without_outer_indices E M hdim
  have htwo := HomologyVanishing.minimal_ordered_index_two_count_zero S hf hm hdim
    horder hzero hone hminimal
  have hfour := HomologyVanishing.minimal_ordered_index_four_count_zero S hf hm hdim
    horder hsix hfive hminimal
  refine ⟨f, hf, hm, S, horder, hzero, hsix, hone, htwo, hfour, hfive, ?_, hminimal⟩
  intro p
  have hle := nativeMorseIndex_le (E := E) (f := f) (p := p.val)
  have hne1 := native_index_excluded_of_count_zero S.toSurgeryWindows hone p.val p.property
  have hne2 := native_index_excluded_of_count_zero S.toSurgeryWindows htwo p.val p.property
  have hne4 := native_index_excluded_of_count_zero S.toSurgeryWindows hfour p.val p.property
  have hne5 := native_index_excluded_of_count_zero S.toSurgeryWindows hfive p.val p.property
  omega

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.SimplyConnected
