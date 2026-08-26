import ErdosProblems.Erdos421.BuchstabNumericBounds

/-! # A differentiable extension of each upper Buchstab branch -/

namespace Erdos421

open MeasureTheory Topology

noncomputable def buchstabExtension (n : ℕ) (u : ℝ) : ℝ :=
  (1 + ∫ t in (2 : ℝ)..u, finiteBuchstab n (t - 1)) / u

theorem buchstabExtension_eq (n : ℕ) {u : ℝ} (hu : 2 ≤ u) :
    buchstabExtension n u = finiteBuchstab (n + 1) u :=
  (finiteBuchstab_step n hu).symm

theorem buchstabExtension_hasDerivAt (n : ℕ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (buchstabExtension n)
      ((finiteBuchstab n (u - 1) - buchstabExtension n u) / u) u := by
  have hc : Continuous (fun t : ℝ ↦ finiteBuchstab n (t - 1)) :=
    (finiteBuchstab_continuous n).comp (continuous_id.sub continuous_const)
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 2 u)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd := ((hasDerivAt_const u (1 : ℝ)).add hi).div (hasDerivAt_id u) hu
  dsimp only [Pi.add_apply, id_eq] at hd
  convert hd using 1 <;> first | rfl | (dsimp only [buchstabExtension]; field_simp; ring)

theorem buchstabExtension_continuousOn (n : ℕ) :
    ContinuousOn (buchstabExtension n) (Set.Ioi 0) := by
  intro u hu
  exact (buchstabExtension_hasDerivAt n (ne_of_gt hu)).continuousAt.continuousWithinAt

theorem buchstabExtension_deriv_continuousOn (n : ℕ) :
    ContinuousOn (deriv (buchstabExtension n)) (Set.Ioi 0) := by
  have hc : ContinuousOn (fun u : ℝ ↦
      (finiteBuchstab n (u - 1) - buchstabExtension n u) / u) (Set.Ioi 0) :=
    (((finiteBuchstab_continuous n).comp (continuous_id.sub continuous_const)).continuousOn.sub
      (buchstabExtension_continuousOn n)).div continuousOn_id (fun _ hu ↦ ne_of_gt hu)
  apply hc.congr
  intro u hu
  exact (buchstabExtension_hasDerivAt n (ne_of_gt hu)).deriv

theorem finiteBuchstab_le_one (n : ℕ) {u : ℝ} (hu : 1 ≤ u) : finiteBuchstab n u ≤ 1 := by
  by_cases hu2 : u ≤ 2
  · rw [finiteBuchstab_initial n ⟨hu, hu2⟩]
    exact (div_le_one (by linarith : 0 < u)).mpr hu
  · exact (finiteBuchstab_upper n (by linarith)).trans (by norm_num)

theorem buchstabExtension_deriv_abs_le (n : ℕ) {u : ℝ} (hu : 2 ≤ u) :
    |deriv (buchstabExtension n) u| ≤ 2 / u := by
  have hup : 0 < u := by linarith
  rw [(buchstabExtension_hasDerivAt n hup.ne').deriv, abs_div, abs_of_pos hup,
    buchstabExtension_eq n hu]
  apply div_le_div_of_nonneg_right _ hup.le
  calc
    _ ≤ |finiteBuchstab n (u - 1)| + |finiteBuchstab (n + 1) u| := abs_sub _ _
    _ = finiteBuchstab n (u - 1) + finiteBuchstab (n + 1) u := by
      rw [abs_of_pos (finiteBuchstab_pos n (u - 1)), abs_of_pos (finiteBuchstab_pos (n + 1) u)]
    _ ≤ _ := by linarith [finiteBuchstab_le_one n (show 1 ≤ u - 1 by linarith),
        finiteBuchstab_le_one (n + 1) (show 1 ≤ u by linarith)]

end Erdos421
