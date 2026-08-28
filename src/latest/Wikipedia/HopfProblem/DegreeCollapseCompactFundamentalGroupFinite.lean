import Wikipedia.HopfProblem.DegreeCollapseMorseFundamentalGroupFinite
import Wikipedia.HopfProblem.DegreeCollapseMinimalMinimumCount
import Wikipedia.SmoothSixDPoincare.MorseSurgeryEndpoints
import Wikipedia.SmoothSixDPoincare.MorseBandHomology
import Wikipedia.SmoothSixDPoincare.SublevelDiskHomology

/-!

# Finite generation of the original compact manifold fundamental group

Use the native Morse system with a unique minimum. Its first sublevel is
an actual disk, and every later handle has positive index. Finite
generation propagates through those handles and the actual regular-band
homeomorphisms. The final sublevel is the whole original manifold.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseFiniteness

open Wikipedia.SmoothSixDPoincare ManifoldMorse MorseCancellation

section Windows

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
  {f : M → ℝ} (S : SurgeryWindows E f)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hMin : nativeMorseCount E f 0 = 1)

include S hf hMin

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem later_index_positive (j : Fin S.count) (hj : j.val ≠ 0) :
    0 < Module.finrank ℝ (S.data (S.point j)).chart.NegativeCoordinates := by
  apply Nat.pos_of_ne_zero
  intro hz
  obtain ⟨m, hm⟩ := Set.ncard_eq_one.mp hMin
  have hc := S.count_pos hf
  have hfirst : nativeMorseIndex E f (S.first hc) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hc)).chart).trans
      (S.first_index_zero hf hc)
  have hjIndex : nativeMorseIndex E f (S.point j) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.point j)).chart).trans hz
  have hjm : (S.point j).val = m := by
    have hmem : (S.point j).val ∈
        {x : M | x ∈ criticalPoints E f ∧ nativeMorseIndex E f x = 0} :=
      ⟨(S.point j).property, hjIndex⟩
    rw [hm] at hmem
    exact hmem
  have hfm : (S.first hc).val = m := by
    have hmem : (S.first hc).val ∈
        {x : M | x ∈ criticalPoints E f ∧ nativeMorseIndex E f x = 0} :=
      ⟨(S.first hc).property, hfirst⟩
    rw [hm] at hmem
    exact hmem
  have he : j = ⟨0, hc⟩ := S.point.injective (Subtype.ext (hjm.trans hfm.symm))
  exact hj (congrArg Fin.val he)

theorem upper_pathConnected_and_fundamentalGroup_finite (j : Fin S.count) :
    PathConnectedSpace {x : M // f x ≤ S.upper (S.point j)} ∧
      ∀ x : {x : M // f x ≤ S.upper (S.point j)},
        Group.FG (FundamentalGroup {x : M // f x ≤ S.upper (S.point j)} x) := by
  have H : ∀ i : ℕ, ∀ hi : i < S.count,
      PathConnectedSpace {x : M // f x ≤ S.upper (S.point ⟨i, hi⟩)} ∧
        ∀ x : {x : M // f x ≤ S.upper (S.point ⟨i, hi⟩)},
          Group.FG (FundamentalGroup {x : M // f x ≤ S.upper (S.point ⟨i, hi⟩)} x) := by
    intro i
    induction i with
    | zero =>
      intro hi
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hi
      let : ContractibleSpace {x : M // f x ≤ S.upper (S.point ⟨0, hi⟩)} :=
        D.contractibleSpace
      exact ⟨inferInstance, fun _ ↦ inferInstance⟩
    | succ i ih =>
      intro hi
      have hi' : i < S.count := by omega
      have hPrev := ih hi'
      let : PathConnectedSpace {x : M //
          f x ≤ f (S.point ⟨i, hi'⟩) + (S.data (S.point ⟨i, hi'⟩)).radius ^ 2} := hPrev.1
      obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf ⟨i, hi'⟩ ⟨i + 1, hi⟩ rfl
      let e := (S.data (S.point ⟨i, hi'⟩)).bandSublevelHomeomorph
        (S.data (S.point ⟨i + 1, hi⟩)) T.toHomeomorph hT
      let : PathConnectedSpace {x : M //
          f x ≤ f (S.point ⟨i + 1, hi⟩) - (S.data (S.point ⟨i + 1, hi⟩)).radius ^ 2} :=
        FundamentalGroupTools.pathConnected_of_homotopyEquiv e.toHomotopyEquiv.symm
      have hOld := FundamentalGroupFiniteness.of_homotopyEquiv e.toHomotopyEquiv hPrev.2
      have hIndex := later_index_positive S hf hMin ⟨i + 1, hi⟩ (by simp)
      exact ⟨upper_pathConnected_of_positive_index _ hf.continuous hIndex,
        upper_fundamentalGroup_finite_of_positive_index _ hf.continuous hIndex hOld⟩
  exact H j.val j.isLt

theorem manifold_fundamentalGroup_finite (x : M) :
    Group.FG (FundamentalGroup M x) := by
  have hc := S.count_pos hf
  let j : Fin S.count := ⟨S.count - 1, Nat.sub_lt hc zero_lt_one⟩
  have hLast := (upper_pathConnected_and_fundamentalGroup_finite S hf hMin j).2
  have hall : ∀ y : M, f y ≤ S.upper (S.last hc) := by
    intro y
    have hy : y ∈ ({z : M | f z ≤ S.upper (S.last hc)} : Set M) := by
      rw [S.last_upper_univ hf hc]
      exact Set.mem_univ y
    exact hy
  let e : {y : M // f y ≤ S.upper (S.last hc)} ≃ₜ M := {
    toFun := Subtype.val
    invFun := fun y ↦ ⟨y, hall y⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := continuous_subtype_val
    continuous_invFun := continuous_id.subtype_mk _ }
  exact FundamentalGroupFiniteness.of_homotopyEquiv e.toHomotopyEquiv hLast x

end Windows

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]

include E in
theorem compactManifold_fundamentalGroup_finite (x : M) :
    Group.FG (FundamentalGroup M x) := by
  obtain ⟨f, hf, _, S, _, hMin, _, _⟩ :=
    MorseCancellation.exists_minimal_ordered_morse_system_with_unique_extrema E M
  exact manifold_fundamentalGroup_finite S.toSurgeryWindows hf hMin x

end Wikipedia.HopfProblem.DegreeCollapse.MorseFiniteness
