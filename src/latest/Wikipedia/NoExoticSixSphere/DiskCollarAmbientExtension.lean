import Wikipedia.NoExoticSixSphere.DiskRadialCollar
import Mathlib.Analysis.Complex.Tietze

/-!
# An ambient extension retaining an exact outer disk collar

Tietze extends the original closed-disk map. A scalar bump installs the
prescribed continuous collar outside radius two thirds. Since the two
maps already agree on the outer half-annulus, this changes none of the
original disk values. In particular a smooth prescribed collar is smooth
on a full ambient neighborhood, not merely on the inside of the sphere.
-/

noncomputable section

open Set Metric

namespace NoExoticSixSphere.DiskCollarAmbientExtension

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_extension (G : C(Disk (E := Vector (n + 1)), F))
    (H : C(Vector (n + 1), F))
    (hH : ∀ x : Disk (E := Vector (n + 1)), 1 / 2 ≤ ‖x.val‖ → H x.val = G x) :
    ∃ B : C(Vector (n + 1), F),
      (∀ x : Disk (E := Vector (n + 1)), B x.val = G x) ∧
      ∀ x, 2 / 3 ≤ ‖x‖ → B x = H x := by
  obtain ⟨A, hA⟩ := G.exists_restrict_eq isClosed_closedBall
  have hAG (x : Disk (E := Vector (n + 1))) : A x.val = G x :=
    ContinuousMap.congr_fun hA x
  let χ : ContDiffBump (0 : Vector (n + 1)) := {
    rIn := 1 / 2
    rOut := 2 / 3
    rIn_pos := by norm_num
    rIn_lt_rOut := by norm_num
  }
  let B : C(Vector (n + 1), F) :=
    ⟨fun x ↦ χ x • A x + (1 - χ x) • H x,
      (χ.continuous.smul A.continuous).add
        ((continuous_const.sub χ.continuous).smul H.continuous)⟩
  refine ⟨B, ?_, ?_⟩
  · intro x
    change χ x.val • A x.val + (1 - χ x.val) • H x.val = G x
    by_cases hx : ‖x.val‖ ≤ 1 / 2
    · have hχ : χ x.val = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
      rw [hχ, one_smul, sub_self, zero_smul, add_zero, hAG]
    · rw [hAG, hH x (le_of_not_ge hx), ← add_smul, add_sub_cancel, one_smul]
  · intro x hx
    have hχ : χ x = 0 := χ.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
    change χ x • A x + (1 - χ x) • H x = H x
    rw [hχ, zero_smul, sub_zero, one_smul, zero_add]

end NoExoticSixSphere.DiskCollarAmbientExtension
