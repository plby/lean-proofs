import Mathlib
import ErdosProblems.Erdos336.PiecewiseBohrTransfer

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Reassembling arbitrarily large local Bohr patterns
-/

namespace Erdos336

open PiecewiseBohrTransfer

/-- If every centered finite portion of an orbit patch has some translate in
`P`, then compactness of the target group synchronizes the translating orbit
points.  A smaller open orbit patch, intersected with a thick union of the
translated intervals, is contained in `P`. -/
theorem piecewise_patch_of_local_orbit_patterns
    {K : Type*} [NormedAddCommGroup K] [CompactSpace K]
    (φ : ℤ →+ K) {U : Set K} {P : Set ℤ}
    (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hlocal : ∀ R : ℕ, ∃ c : ℤ, ∀ x : ℤ,
      x.natAbs ≤ R → φ x ∈ U → x + c ∈ P) :
    ∃ W : Set K, ∃ T : Set ℤ,
      IsOpen W ∧ W.Nonempty ∧ ThickZ T ∧
      ∀ n : ℤ, φ n ∈ W → n ∈ T → n ∈ P := by
  choose c hc using hlocal
  obtain ⟨z, σ, hσmono, hσlim⟩ :=
    CompactSpace.tendsto_subseq (fun R : ℕ => φ (c R))
  obtain ⟨u, huU⟩ := hUne
  obtain ⟨ε, hεpos, hballU⟩ := (Metric.isOpen_iff.mp hUopen) u huU
  have hthird : 0 < ε / 3 := by positivity
  have hconv : ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ‖φ (c (σ j)) - z‖ < ε / 3 := by
    rw [NormedAddCommGroup.tendsto_atTop] at hσlim
    simpa [Function.comp_def] using hσlim (ε / 3) hthird
  obtain ⟨J, hJ⟩ := hconv
  let W : Set K := Metric.ball (z + u) (ε / 3)
  let T : Set ℤ := {n | ∃ j : ℕ, J ≤ j ∧ ∃ x : ℤ,
    x.natAbs ≤ σ j ∧ n = x + c (σ j)}
  refine ⟨W, T, Metric.isOpen_ball, ?_, ?_, ?_⟩
  · exact ⟨z + u, Metric.mem_ball_self hthird⟩
  · intro F
    let R : ℕ := F.sup Int.natAbs
    let j : ℕ := max J R
    refine ⟨c (σ j), ?_⟩
    intro x hxF
    have hxR : x.natAbs ≤ R := Finset.le_sup hxF
    have hjJ : J ≤ j := le_max_left _ _
    have hRj : R ≤ j := le_max_right _ _
    have hjσ : j ≤ σ j := hσmono.le_apply
    refine ⟨j, hjJ, x, ?_, by omega⟩
    omega
  · intro n hnW hnT
    obtain ⟨j, hjJ, x, hxσ, rfl⟩ := hnT
    apply hc (σ j) x hxσ
    apply hballU
    have hshift : ‖φ (c (σ j)) - z‖ < ε / 3 := hJ j hjJ
    have hnclose : ‖φ (x + c (σ j)) - (z + u)‖ < ε / 3 := by
      simpa [W, Metric.mem_ball, dist_eq_norm] using hnW
    have hid : φ x - u =
        (φ (x + c (σ j)) - (z + u)) + (z - φ (c (σ j))) := by
      simp only [map_add]
      abel
    rw [Metric.mem_ball, dist_eq_norm, hid]
    calc
      ‖φ (x + c (σ j)) - (z + u) + (z - φ (c (σ j)))‖
          ≤ ‖φ (x + c (σ j)) - (z + u)‖ + ‖z - φ (c (σ j))‖ := norm_add_le _ _
      _ < ε / 3 + ε / 3 := by
        gcongr
        calc
          ‖z - φ (c (σ j))‖ = ‖φ (c (σ j)) - z‖ := norm_sub_rev _ _
          _ < ε / 3 := hshift
      _ < ε := by linarith

end Erdos336
