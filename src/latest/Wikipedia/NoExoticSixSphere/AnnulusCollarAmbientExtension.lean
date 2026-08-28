import Wikipedia.NoExoticSixSphere.SphereAnnulusCoordinates
import Mathlib.Analysis.Complex.Tietze

/-!
# An ambient annulus extension retaining both original collars

Extend the actual annulus map into its Euclidean target, then install the
two prescribed ambient collar maps with disjoint scalar transitions.
Agreement on the original collars ensures no annulus value is changed.
The extension agrees with the inner collar near the entire inner boundary
and with the outer collar near the entire outer boundary.
-/

noncomputable section

open Set Metric

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_ambient_extension (G : C(domain n, F))
    (H₀ H₁ : C(Vector (n + 1), F))
    (h₀ : ∀ x : domain n, ‖x.val‖ ≤ 4 / 3 → H₀ x.val = G x)
    (h₁ : ∀ x : domain n, 7 / 4 ≤ ‖x.val‖ → H₁ x.val = G x) :
    ∃ B : C(Vector (n + 1), F), (∀ x : domain n, B x.val = G x) ∧
      (∀ x, ‖x‖ ≤ 5 / 4 → B x = H₀ x) ∧
      ∀ x, 11 / 6 ≤ ‖x‖ → B x = H₁ x := by
  obtain ⟨A, hA⟩ := G.exists_restrict_eq (isClosed_domain n)
  have hAG (x : domain n) : A x.val = G x := ContinuousMap.congr_fun hA x
  let χ₀ : ContDiffBump (0 : Vector (n + 1)) := {
    rIn := 5 / 4
    rOut := 4 / 3
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num }
  let χ₁ : ContDiffBump (0 : Vector (n + 1)) := {
    rIn := 7 / 4
    rOut := 11 / 6
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num }
  let T : C(Vector (n + 1), F) :=
    ⟨fun x ↦ χ₁ x • A x + (1 - χ₁ x) • H₁ x,
      (χ₁.continuous.smul A.continuous).add
        ((continuous_const.sub χ₁.continuous).smul H₁.continuous)⟩
  let B : C(Vector (n + 1), F) :=
    ⟨fun x ↦ χ₀ x • H₀ x + (1 - χ₀ x) • T x,
      (χ₀.continuous.smul H₀.continuous).add
        ((continuous_const.sub χ₀.continuous).smul T.continuous)⟩
  refine ⟨B, ?_, ?_, ?_⟩
  · intro x
    change χ₀ x.val • H₀ x.val +
      (1 - χ₀ x.val) • (χ₁ x.val • A x.val + (1 - χ₁ x.val) • H₁ x.val) = G x
    by_cases hx : ‖x.val‖ ≤ 4 / 3
    · have hχ₁ : χ₁ x.val = 1 := χ₁.one_of_mem_closedBall
        (mem_closedBall_zero_iff.mpr (by change ‖x.val‖ ≤ 7 / 4; linarith))
      rw [hχ₁, one_smul, sub_self, zero_smul, add_zero, hAG, h₀ x hx,
        ← add_smul, add_sub_cancel, one_smul]
    · have hχ₀ : χ₀ x.val = 0 := χ₀.zero_of_le_dist (by
        change 4 / 3 ≤ dist x.val 0
        rw [dist_zero_right]
        exact (lt_of_not_ge hx).le)
      rw [hχ₀, zero_smul, sub_zero, one_smul, zero_add]
      by_cases hy : 7 / 4 ≤ ‖x.val‖
      · rw [hAG, h₁ x hy, ← add_smul, add_sub_cancel, one_smul]
      · have hχ₁ : χ₁ x.val = 1 := χ₁.one_of_mem_closedBall
          (mem_closedBall_zero_iff.mpr (le_of_not_ge hy))
        rw [hχ₁, one_smul, sub_self, zero_smul, add_zero, hAG]
  · intro x hx
    have hχ₀ : χ₀ x = 1 := χ₀.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
    change χ₀ x • H₀ x + (1 - χ₀ x) • T x = H₀ x
    rw [hχ₀, one_smul, sub_self, zero_smul, add_zero]
  · intro x hx
    have hχ₀ : χ₀ x = 0 := χ₀.zero_of_le_dist (by
      change 4 / 3 ≤ dist x 0
      rw [dist_zero_right]
      linarith)
    have hχ₁ : χ₁ x = 0 := χ₁.zero_of_le_dist (by
      simpa only [dist_zero_right] using hx)
    change χ₀ x • H₀ x + (1 - χ₀ x) •
      (χ₁ x • A x + (1 - χ₁ x) • H₁ x) = H₁ x
    rw [hχ₀, zero_smul, sub_zero, one_smul, zero_add,
      hχ₁, zero_smul, sub_zero, one_smul, zero_add]

end NoExoticSixSphere.SphereAnnulus
