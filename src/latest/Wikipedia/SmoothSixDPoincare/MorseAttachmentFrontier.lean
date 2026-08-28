import Wikipedia.SmoothSixDPoincare.MorseModelFlow

/-!
# The exact frontier of the quadratic Morse attachment

The lower sublevel with its curved handle adjoined is the union of the two
inequalities `Q ≤ -ρ²` and `‖v‖ ≤ ρ`. Its interior uses the strict inequalities.
To exclude every other interior point, increase the positive radial coordinate
slightly; this simultaneously increases the norm and the quadratic height.
-/

noncomputable section

open Set Filter Metric
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare.MorseHandle

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def attachmentRegion (ρ : ℝ) : Set (N × P) :=
  {z | quadratic z ≤ -(ρ ^ 2)} ∪ range (modelMap ρ)

omit [NormedSpace ℝ N] [NormedSpace ℝ P] in
theorem continuous_quadratic : Continuous (quadratic (N := N) (P := P)) := by
  unfold quadratic
  fun_prop

theorem isClosed_attachmentRegion {ρ : ℝ} (hρ : 0 < ρ) :
    IsClosed (attachmentRegion (N := N) (P := P) ρ) := by
  have heq : attachmentRegion (N := N) (P := P) ρ =
      {z | quadratic z ≤ -(ρ ^ 2)} ∪ {z | ‖z.2‖ ≤ ρ} := by
    ext z
    exact mem_lower_union_handle_iff hρ z
  rw [heq]
  exact (isClosed_le continuous_quadratic continuous_const).union
    (isClosed_le continuous_snd.norm continuous_const)

/-- Equality in both defining lower bounds prevents interior membership, including at the corner. -/
theorem notMem_interior_attachmentRegion_of_bounds {ρ : ℝ} (hρ : 0 < ρ) (z : N × P)
    (hq : -(ρ ^ 2) ≤ quadratic z) (hv : ρ ≤ ‖z.2‖) :
    z ∉ interior (attachmentRegion ρ) := by
  intro hi
  have hpath : ContinuousAt (fun r : ℝ => (z.1, r • z.2)) 1 := by fun_prop
  have hnear : ∀ᶠ r : ℝ in 𝓝 1, (z.1, r • z.2) ∈ attachmentRegion ρ := by
    apply hpath.preimage_mem_nhds
    simpa only [one_smul, Prod.eta] using mem_interior_iff_mem_nhds.mp hi
  obtain ⟨r, hr, hmem⟩ := hnear.exists_gt
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hvpos : 0 < ‖z.2‖ := hρ.trans_le hv
  have hnorm : ‖r • z.2‖ = r * ‖z.2‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos]
  have hnormlt : ‖z.2‖ < ‖r • z.2‖ := by
    rw [hnorm]
    nlinarith
  have hquadlt : quadratic z < quadratic (z.1, r • z.2) := by
    unfold quadratic
    nlinarith [norm_nonneg (r • z.2), norm_nonneg z.2]
  rcases (mem_lower_union_handle_iff hρ (z.1, r • z.2)).mp hmem with h | h
  · exact (not_lt_of_ge h) (hq.trans_lt hquadlt)
  · exact (not_lt_of_ge h) (hv.trans_lt hnormlt)

theorem mem_interior_attachmentRegion_iff {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ interior (attachmentRegion ρ) ↔ quadratic z < -(ρ ^ 2) ∨ ‖z.2‖ < ρ := by
  constructor
  · intro hi
    by_cases hq : quadratic z < -(ρ ^ 2)
    · exact Or.inl hq
    by_cases hv : ‖z.2‖ < ρ
    · exact Or.inr hv
    exact (notMem_interior_attachmentRegion_of_bounds hρ z
      (le_of_not_gt hq) (le_of_not_gt hv) hi).elim
  · rintro (hq | hv)
    · apply interior_maximal (t := {w | quadratic w < -(ρ ^ 2)}) _
        (isOpen_lt continuous_quadratic continuous_const) hq
      intro w hw
      exact (mem_lower_union_handle_iff hρ w).mpr (Or.inl hw.le)
    · apply interior_maximal (t := {w : N × P | ‖w.2‖ < ρ}) _
        (isOpen_lt continuous_snd.norm continuous_const) hv
      intro w hw
      exact (mem_lower_union_handle_iff hρ w).mpr (Or.inr hw.le)

/-- The two entire frontier pieces, with their shared corner included in both. -/
theorem mem_frontier_attachmentRegion_iff {ρ : ℝ} (hρ : 0 < ρ) (z : N × P) :
    z ∈ frontier (attachmentRegion ρ) ↔
      (quadratic z = -(ρ ^ 2) ∧ ρ ≤ ‖z.2‖) ∨
        (‖z.2‖ = ρ ∧ -(ρ ^ 2) ≤ quadratic z) := by
  rw [frontier, (isClosed_attachmentRegion hρ).closure_eq]
  change (z ∈ attachmentRegion ρ ∧ z ∉ interior (attachmentRegion ρ)) ↔ _
  rw [mem_interior_attachmentRegion_iff hρ]
  rw [show z ∈ attachmentRegion ρ ↔
    quadratic z ≤ -(ρ ^ 2) ∨ ‖z.2‖ ≤ ρ from mem_lower_union_handle_iff hρ z]
  constructor
  · rintro ⟨hmem, hnot⟩
    have hq : -(ρ ^ 2) ≤ quadratic z := le_of_not_gt (fun h => hnot (Or.inl h))
    have hv : ρ ≤ ‖z.2‖ := le_of_not_gt (fun h => hnot (Or.inr h))
    rcases hmem with h | h
    · exact Or.inl ⟨le_antisymm h hq, hv⟩
    · exact Or.inr ⟨le_antisymm h hv, hq⟩
  · rintro (⟨hq, hv⟩ | ⟨hv, hq⟩)
    · refine ⟨Or.inl hq.le, ?_⟩
      rintro (h | h)
      · exact hq.not_lt h
      · exact (not_lt_of_ge hv) h
    · refine ⟨Or.inr hv.le, ?_⟩
      rintro (h | h)
      · exact (not_lt_of_ge hq) h
      · exact hv.not_lt h

/-- Within the actual handle, precisely its positive boundary face survives on the frontier. -/
theorem modelMap_mem_frontier_attachmentRegion_iff {ρ : ℝ} (hρ : 0 < ρ)
    (z : UnitDisk N × UnitDisk P) :
    modelMap ρ z ∈ frontier (attachmentRegion ρ) ↔ ‖(z.2 : P)‖ = 1 := by
  have hv : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
  have hnorm : ‖(modelMap ρ z).2‖ = ρ * ‖(z.2 : P)‖ := by
    change ‖ρ • (z.2 : P)‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
  rw [mem_frontier_attachmentRegion_iff hρ]
  constructor
  · intro hz
    have hlo : ρ ≤ ‖(modelMap ρ z).2‖ := by
      rcases hz with hz | hz
      · exact hz.2
      · exact hz.1.ge
    rw [hnorm] at hlo
    nlinarith
  · intro hz
    refine Or.inr ⟨?_, ?_⟩
    · rw [hnorm, hz, mul_one]
    · exact ((mem_range_modelMap_iff hρ (modelMap ρ z)).mp ⟨z, rfl⟩).2

end Wikipedia.SmoothSixDPoincare.MorseHandle
