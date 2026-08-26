import Mathlib
import ErdosProblems.Erdos336.ConditionalFinal
import ErdosProblems.Erdos336.ExtremalExistence
import ErdosProblems.Erdos336.BlockScaleAsymptotic

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Eventual finite bounds suffice for the final asymptotic reduction
-/

namespace Erdos336

open Filter Topology

/-- The logically minimal finite input: only sufficiently large orders matter
for the limit. -/
def HasEventualCyclicRemovalUpperThird : Prop :=
  ∃ M : ℕ → ℕ,
    (∀ᶠ h : ℕ in atTop, CyclicRemovalBound h (M h)) ∧
    Tendsto (fun h : ℕ => (M h : ℝ) / (h : ℝ) ^ 2)
      atTop (𝓝 (1 / 3 : ℝ))

/-- Pointwise form of F-045's upper bound; its proof only uses the cyclic
bound at `r+1`. -/
theorem extremal_upper_of_one_cyclic_bound
    {H : ℕ → ℕ} (hH : IsExtremalFunction H)
    {r M : ℕ} (hr : 2 ≤ r)
    (hM : CyclicRemovalBound (r + 1) M) :
    H r ≤ M + 4 * r + r := by
  obtain ⟨A, hatMost, horder⟩ := (hH r hr).1
  obtain ⟨b, hbA⟩ := eventuallyAtMost_nonempty hatMost
  let D : Set ℤ := TranslateNatSet A b
  have hzeroD : (0 : ℤ) ∈ D := zero_mem_translateNatSet hbA
  have hparent : EventuallyWithOneExtra D (-(b : ℤ)) r :=
    eventuallyWithOneExtra_translate hatMost
  have hexactD : EventuallyExactlyZ D (H r) :=
    eventuallyExactlyZ_translate horder.1
  have hboundD : EventuallyExactlyZ D (M + 4 * r + r) :=
    eventuallyExactlyZ_of_cyclic_bound_auto_patch hzeroD hparent hexactD hM
  have hboundA : EventuallyExactly A (M + 4 * r + r) :=
    eventuallyExactly_of_eventuallyExactlyZ_translate hboundD
  by_contra hnot
  have hlt : M + 4 * r + r < H r := Nat.lt_of_not_ge hnot
  exact horder.2 _ hlt hboundA

/-- Eventual cyclic removal bounds with normalized value `1/3` already solve
the original asymptotic problem. -/
theorem problem336_of_eventual_cyclicRemovalUpperThird
    (hfinite : HasEventualCyclicRemovalUpperThird) :
    HasProblem336Value (1 / 3 : ℝ) := by
  obtain ⟨M, hMev, hMtend⟩ := hfinite
  have hexists : ∃ H : ℕ → ℕ, IsExtremalFunction H :=
    exists_extremalFunction_of_eventual_cyclicRemovalBound hMev
  refine ⟨hexists, ?_⟩
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 hMev
  intro H hH
  let lower : ℕ → ℝ := fun r =>
    ((3 * (r / 3) ^ 2 + 4 * (r / 3) : ℕ) : ℝ) / (r : ℝ) ^ 2
  let upper : ℕ → ℝ := fun r =>
    ((M (r + 1) + 4 * r + r : ℕ) : ℝ) / (r : ℝ) ^ 2
  have hlower : Tendsto lower atTop (𝓝 (1 / 3 : ℝ)) := by
    simpa [lower] using tendsto_floor_thirds_lower_expression
  have hMshift : Tendsto
      (fun r : ℕ => (M (r + 1) : ℝ) / ((r + 1 : ℕ) : ℝ) ^ 2)
      atTop (𝓝 (1 / 3 : ℝ)) := by
    exact (tendsto_add_atTop_iff_nat 1).2 hMtend
  have hinv : Tendsto (fun r : ℕ => (1 : ℝ) / (r : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1
  have hratio : Tendsto
      (fun r : ℕ => (((r + 1 : ℕ) : ℝ) / (r : ℝ)) ^ 2)
      atTop (𝓝 1) := by
    have hbase : Tendsto
        (fun r : ℕ => ((r + 1 : ℕ) : ℝ) / (r : ℝ))
        atTop (𝓝 1) := by
      have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
        tendsto_const_nhds
      have h : Tendsto (fun r : ℕ => (1 : ℝ) + 1 / (r : ℝ))
          atTop (𝓝 1) := by simpa using hone.add hinv
      apply h.congr'
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with r hr0
      push_cast
      field_simp
    simpa using hbase.pow 2
  have hmain : Tendsto
      (fun r : ℕ => (M (r + 1) : ℝ) / (r : ℝ) ^ 2)
      atTop (𝓝 (1 / 3 : ℝ)) := by
    have hp : Tendsto
        (fun r : ℕ =>
          ((M (r + 1) : ℝ) / ((r + 1 : ℕ) : ℝ) ^ 2) *
            (((r + 1 : ℕ) : ℝ) / (r : ℝ)) ^ 2)
        atTop (𝓝 (1 / 3 : ℝ)) := by
      simpa using hMshift.mul hratio
    apply hp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with r hr0
    have hrR : (r : ℝ) ≠ 0 := by positivity
    have hr1R : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hlinear : Tendsto
      (fun r : ℕ => ((4 * r + r : ℕ) : ℝ) / (r : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have hfive : Tendsto (fun _ : ℕ => (5 : ℝ)) atTop (𝓝 5) :=
      tendsto_const_nhds
    have h : Tendsto (fun r : ℕ => (5 : ℝ) * (1 / (r : ℝ)))
        atTop (𝓝 0) := by simpa using hfive.mul hinv
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with r hr0
    push_cast
    field_simp
    ring
  have hupper : Tendsto upper atTop (𝓝 (1 / 3 : ℝ)) := by
    have hs : Tendsto
        (fun r : ℕ =>
          (M (r + 1) : ℝ) / (r : ℝ) ^ 2 +
            ((4 * r + r : ℕ) : ℝ) / (r : ℝ) ^ 2)
        atTop (𝓝 (1 / 3 : ℝ)) := by
      simpa using hmain.add hlinear
    apply hs.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with r hr0
    dsimp [upper]
    push_cast
    have hrR : (r : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hlower_le : ∀ᶠ r : ℕ in atTop,
      lower r ≤ (H r : ℝ) / (r : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop 3] with r hr3
    have hpoint := extremal_lower_bound_floor_thirds hH hr3
    dsimp [lower]
    gcongr
  have hle_upper : ∀ᶠ r : ℕ in atTop,
      (H r : ℝ) / (r : ℝ) ^ 2 ≤ upper r := by
    filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop a]
      with r hr2 hra
    have hMr : CyclicRemovalBound (r + 1) (M (r + 1)) :=
      ha (r + 1) (by omega)
    have hpoint := extremal_upper_of_one_cyclic_bound hH hr2 hMr
    dsimp [upper]
    gcongr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower hupper hlower_le hle_upper

/-- Hence the single high-power structural statement isolated in F-068 is
sufficient for Erdős Problem 336. -/
theorem problem336_of_highPowerRankDenseStructure
    (hstruct : HasHighPowerRankDenseStructure) :
    HasProblem336Value (1 / 3 : ℝ) := by
  apply problem336_of_eventual_cyclicRemovalUpperThird
  exact ⟨structuralRemovalCost,
    eventually_cyclicRemovalBound_structuralCost hstruct,
    tendsto_structuralRemovalCost_third⟩

end Erdos336
