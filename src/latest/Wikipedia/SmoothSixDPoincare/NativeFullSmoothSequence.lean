import Wikipedia.SmoothSixDPoincare.NativeFullSmoothInterval
import Wikipedia.SmoothSixDPoincare.MorseSurgeryEndpoints
import Mathlib.Data.List.OfFn

/-!
# The entire original Morse sequence as a full smooth handle chain

Every critical point occurs in its original order. The chain starts with
the actual empty lower sublevel and ends with the actual final upper
sublevel, which is homeomorphic to the whole original manifold.
No elimination of intermediate handles is asserted here.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] in
theorem intervalIndices_eq_ofFn (i : Fin S.count) (n : ℕ) (h : i.val + n < S.count) :
    S.intervalIndices i n h = List.ofFn (fun j : Fin (n + 1) =>
      Module.finrank ℝ (S.data (S.point ⟨i.val + j.val,
        by have := j.isLt; omega⟩)).chart.NegativeCoordinates) := by
  induction n with
  | zero =>
      simp only [intervalIndices, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Nat.add_zero]
  | succ n ih =>
      rw [intervalIndices, List.ofFn_succ', List.concat_eq_append, ih]
      rfl

open Classical in
theorem exists_fullSmoothSequence (hs : S.HasSmoothExteriors hf) (hcount : 0 < S.count) :
    ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        ((S.data (S.first hcount)).lowerSmoothBody hf)
        ((S.data (S.last hcount)).upperSmoothBody hf) S.count,
      c.indices = List.ofFn (fun i : Fin S.count =>
        Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) := by
  let i : Fin S.count := ⟨0, hcount⟩
  have hn : S.count - 1 + 1 = S.count := by omega
  have h : i.val + (S.count - 1) < S.count := by dsimp [i]; omega
  obtain ⟨c, hc, -⟩ := S.exists_fullSmoothInterval hf hs i (S.count - 1) h
  let d := c.castLength hn
  have hend : S.intervalEnd i (S.count - 1) h =
      (⟨S.count - 1, Nat.sub_lt hcount zero_lt_one⟩ : Fin S.count) := by
    apply Fin.ext
    exact Nat.zero_add _
  have hd : d.indices = List.ofFn (fun j : Fin S.count =>
      Module.finrank ℝ (S.data (S.point j)).chart.NegativeCoordinates) := by
    rw [FullSmoothHandleChain.castLength_indices, hc, S.intervalIndices_eq_ofFn]
    rw [List.ofFn_congr hn]
    apply congrArg List.ofFn
    funext j
    apply congrArg (fun t : Fin S.count =>
      Module.finrank ℝ (S.data (S.point t)).chart.NegativeCoordinates)
    apply Fin.ext
    exact Nat.zero_add _
  change ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
      ((S.data (S.point i)).lowerSmoothBody hf)
      ((S.data (S.point ⟨S.count - 1, Nat.sub_lt hcount zero_lt_one⟩)).upperSmoothBody hf) S.count,
    c.indices = _
  rw [← hend]
  exact ⟨d, hd⟩

include hf in
theorem first_lowerSmoothBody_isEmpty (hcount : 0 < S.count) :
    IsEmpty ((S.data (S.first hcount)).lowerSmoothBody hf).body := by
  refine ⟨fun x => ?_⟩
  exact (not_le_of_gt (S.lower_lt_value (S.first hcount)))
    ((S.first_globalMin hf hcount x.val).trans x.property)

def last_upperSmoothBodyHomeomorph (hcount : 0 < S.count) :
    ((S.data (S.last hcount)).upperSmoothBody hf).body ≃ₜ M where
  toFun := Subtype.val
  invFun x := ⟨x, (S.last_globalMax hf hcount x).trans (S.value_lt_upper (S.last hcount)).le⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

theorem last_upperSmoothBodyHomeomorph_point (hcount : 0 < S.count)
    (x : ((S.data (S.last hcount)).upperSmoothBody hf).body) :
    S.last_upperSmoothBodyHomeomorph hf hcount x = x.val := rfl

include hf in
theorem last_upperSmoothBoundary_isEmpty (hcount : 0 < S.count) :
    IsEmpty ((S.data (S.last hcount)).upperSmoothBody hf).boundary := by
  refine ⟨fun x => ?_⟩
  have h := S.last_globalMax hf hcount x.val
  rw [x.property] at h
  exact (not_le_of_gt (S.value_lt_upper (S.last hcount))) h

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
