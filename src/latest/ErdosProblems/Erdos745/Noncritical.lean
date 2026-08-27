import ErdosProblems.Erdos745.LogarithmicLower
import ErdosProblems.Erdos745.SubcriticalUpper
import ErdosProblems.Erdos745.MacroscopicUniqueness

/-!
# The exact logarithmic scale throughout the noncritical regime

Every parameter is fixed while the vertex count tends to infinity. The
theorems require no supplied random-graph estimates or moment assumptions.
-/

open Filter
open scoped Topology

namespace Erdos745

noncomputable section

/-- The first-order logarithmic law for every fixed positive noncritical density. -/
def NoncriticalLogarithmicAsymptotic : Prop :=
  ∀ lam : ℝ, 0 < lam → lam ≠ 1 → ∀ ε : ℝ, 0 < ε →
    WithHighProbabilityAt lam (fun n G ↦
      |secondOrder n G / Real.log (n : ℝ) - logarithmicConstant lam| < ε)

/-- Fixed positive logarithmic bounds hold with probability tending to one. -/
def NoncriticalLogarithmicScaling : Prop :=
  ∀ lam : ℝ, 0 < lam → lam ≠ 1 → ∃ c C : ℝ, 0 < c ∧ c < C ∧
    WithHighProbabilityAt lam (fun n G ↦
      c * Real.log (n : ℝ) ≤ secondOrder n G ∧ secondOrder n G ≤ C * Real.log (n : ℝ))

theorem noncritical_logarithmic_upper {lam A : ℝ} (hlam : 0 < lam) (hne : lam ≠ 1)
    (hA : logarithmicConstant lam < A) :
    WithHighProbabilityAt lam (fun n G ↦ secondOrder n G ≤ A * Real.log (n : ℝ)) := by
  rcases lt_or_gt_of_ne hne with hl | hl
  · exact subcritical_logarithmic_upper hlam hl hA
  · exact kss_logarithmic lam hl A hA

theorem withHighProbabilityAt_inter {lam : ℝ}
    {P Q : (n : ℕ) → SimpleGraph (Fin n) → Prop}
    (hP : WithHighProbabilityAt lam P) (hQ : WithHighProbabilityAt lam Q) :
    WithHighProbabilityAt lam (fun n G ↦ P n G ∧ Q n G) := by
  unfold WithHighProbabilityAt at *
  have ht := (hP.add hQ).sub (tendsto_const_nhds (x := (1 : ℝ)))
  norm_num only at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le ht tendsto_const_nhds
    (fun n ↦ probability_inter_ge lam n (P n) (Q n))
    (fun n ↦ probability_le_one _ _ _)

theorem withHighProbabilityAt_mono_eventually {lam : ℝ}
    {P Q : (n : ℕ) → SimpleGraph (Fin n) → Prop}
    (hP : WithHighProbabilityAt lam P) (hPQ : ∀ᶠ n in atTop, ∀ G, P n G → Q n G) :
    WithHighProbabilityAt lam Q := by
  unfold WithHighProbabilityAt at *
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hP tendsto_const_nhds
    (hPQ.mono fun _ hn ↦ probability_mono hn)
    (Eventually.of_forall fun n ↦ probability_le_one _ _ _)

theorem noncritical_logarithmic_asymptotic : NoncriticalLogarithmicAsymptotic := by
  intro lam hlam hne ε hε
  let a := logarithmicConstant lam
  have ha : 0 < a := logarithmicConstant_pos_of_ne_one hlam hne
  let B := max (a - ε / 2) (a / 2)
  have hBpos : 0 < B := (half_pos ha).trans_le (le_max_right _ _)
  have hBa : B < logarithmicConstant lam := by
    apply max_lt <;> dsimp [a] at * <;> linarith
  have hA : logarithmicConstant lam < a + ε / 2 := by dsimp [a]; linarith
  have hboth := withHighProbabilityAt_inter (noncritical_logarithmic_lower hlam hne hBpos hBa)
    (noncritical_logarithmic_upper hlam hne hA)
  apply withHighProbabilityAt_mono_eventually hboth
  filter_upwards [eventually_ge_atTop 2] with n hn
  intro G hG
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hlo : B ≤ secondOrder n G / Real.log (n : ℝ) := (le_div_iff₀ hlog).mpr hG.1
  have hup : secondOrder n G / Real.log (n : ℝ) ≤ a + ε / 2 := (div_le_iff₀ hlog).mpr hG.2
  have hB : a - ε / 2 ≤ B := le_max_left _ _
  apply abs_lt.mpr
  change -ε < secondOrder n G / Real.log (n : ℝ) - a ∧
    secondOrder n G / Real.log (n : ℝ) - a < ε
  constructor <;> linarith

theorem noncritical_logarithmic_scaling : NoncriticalLogarithmicScaling := by
  intro lam hlam hne
  let a := logarithmicConstant lam
  have ha : 0 < a := logarithmicConstant_pos_of_ne_one hlam hne
  refine ⟨a / 2, 2 * a, by positivity, by linarith, ?_⟩
  apply withHighProbabilityAt_inter
  · exact noncritical_logarithmic_lower hlam hne (by positivity) (by change a / 2 < a; linarith)
  · exact noncritical_logarithmic_upper hlam hne (by change a < 2 * a; linarith)

/-- Compatibility with the previously declared full first-order KSS target. -/
theorem kss_logarithmic_asymptotic : KSSLogarithmicAsymptotic := by
  intro lam hlam
  exact noncritical_logarithmic_asymptotic lam (by linarith) (ne_of_gt hlam)

end

end Erdos745
