import Wikipedia.SmoothSixDPoincare.CompactSmoothCutoff

/-!
# Arbitrarily small compactly supported extensions of a zero-valued smooth germ

The support is kept in the prescribed open domain. Multiplication by a
constructed scalar cutoff preserves the entire germ, while a smaller open
neighborhood gives a uniform bound on the values of the extension.
-/

noncomputable section

open Set Function Filter Topology Metric
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Extend a smooth germ vanishing at zero, with arbitrary positive size and support control. -/
theorem exists_small_supported_germ {L : P → E} {U : Set P}
    (hU : IsOpen U) (hzero : (0 : P) ∈ U) (hL : ContDiffOn ℝ ∞ L U)
    (hLzero : L 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : P → E, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ U ∧
      (∀ u, ‖b u‖ < ε) ∧ b =ᶠ[𝓝 (0 : P)] L ∧ b 0 = 0 := by
  let V : Set P := U ∩ L ⁻¹' ball (0 : E) ε
  have hV : IsOpen V := hL.continuousOn.isOpen_inter_preimage hU isOpen_ball
  have hzeroV : (0 : P) ∈ V := ⟨hzero, by simpa [hLzero] using hε⟩
  obtain ⟨β, hβ, hβcompact, hβsupport, hβone, hβrange⟩ :=
    exists_compact_smooth_cutoff isCompact_singleton hV (singleton_subset_iff.mpr hzeroV)
  let b : P → E := fun u => β u • L u
  have hfix (u : P) (hu : u ∉ tsupport β) : β u = 0 := by
    by_contra hne
    exact hu (subset_tsupport β hne)
  have hsmooth : ContDiff ℝ ∞ b := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    by_cases hu : u ∈ U
    · exact hβ.contDiffAt.smul (hL.contDiffAt (hU.mem_nhds hu))
    · have hnot : u ∉ tsupport β := fun h => hu (hβsupport h).1
      have hc : ContDiffAt ℝ ∞ (fun _ : P => (0 : E)) u := contDiffAt_const
      apply hc.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport β).isOpen_compl.mem_nhds hnot] with v hv
      change β v • L v = 0
      rw [hfix v hv, zero_smul]
  have hsupport : tsupport b ⊆ tsupport β := by
    apply closure_mono
    intro u hu hβu
    apply hu
    change β u • L u = 0
    rw [hβu, zero_smul]
  have hcompact : HasCompactSupport b := HasCompactSupport.intro hβcompact.isCompact
    (fun u hu => by change β u • L u = 0; rw [hfix u hu, zero_smul])
  have hsmall (u : P) : ‖b u‖ < ε := by
    by_cases hu : u ∈ tsupport β
    · have hLu : ‖L u‖ < ε := mem_ball_zero_iff.mp (hβsupport hu).2
      change ‖β u • L u‖ < ε
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβrange u).1]
      exact (mul_le_of_le_one_left (norm_nonneg (L u)) (hβrange u).2).trans_lt hLu
    · change ‖β u • L u‖ < ε
      rw [hfix u hu, zero_smul, norm_zero]
      exact hε
  have hgerm : b =ᶠ[𝓝 (0 : P)] L := by
    filter_upwards [hβone.filter_mono (nhds_le_nhdsSet (mem_singleton (0 : P)))] with u hu
    change β u • L u = L u
    rw [hu, one_smul]
  exact ⟨b, hsmooth, hcompact, hsupport.trans (hβsupport.trans inter_subset_left),
    hsmall, hgerm, hgerm.eq_of_nhds.trans hLzero⟩

end Wikipedia.SmoothSixDPoincare
