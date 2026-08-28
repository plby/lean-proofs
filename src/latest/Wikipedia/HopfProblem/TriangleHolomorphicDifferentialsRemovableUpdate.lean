import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Actual analytic updates at removable punctures

A finite punctured limit specifies the value of an actual analytic
extension. The same construction handles a bounded analytic puncture,
and two such prescribed limits produce an entire two-point update.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovable

theorem update_eventuallyEq_of_ne {F : ℂ → ℂ} {a b v : ℂ} (hab : a ≠ b) :
    Function.update F b v =ᶠ[𝓝 a] F := by
  filter_upwards [eventually_ne_nhds hab] with z hz
  simp only [Function.update_of_ne hz]

theorem analyticAt_update_of_ne {F : ℂ → ℂ} {a b v : ℂ}
    (hF : AnalyticAt ℂ F a) (hab : a ≠ b) :
    AnalyticAt ℂ (Function.update F b v) a :=
  hF.congr (update_eventuallyEq_of_ne hab).symm

/-- The finite punctured limit is the actual removable value. -/
theorem analyticAt_update_of_tendsto {F : ℂ → ℂ} {b v : ℂ}
    (hF : ∀ᶠ z in 𝓝[≠] b, AnalyticAt ℂ F z)
    (ht : Tendsto F (𝓝[≠] b) (𝓝 v)) :
    AnalyticAt ℂ (Function.update F b v) b := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [hF, self_mem_nhdsWithin] with z hz hzb
    exact (analyticAt_update_of_ne hz hzb).differentiableAt
  · exact continuousAt_update_same.mpr ht

theorem exists_analytic_extension_of_tendsto {F : ℂ → ℂ} {b v : ℂ}
    (hF : ∀ᶠ z in 𝓝[≠] b, AnalyticAt ℂ F z)
    (ht : Tendsto F (𝓝[≠] b) (𝓝 v)) :
    ∃ Fext : ℂ → ℂ, AnalyticAt ℂ Fext b ∧
      Fext =ᶠ[𝓝[≠] b] F ∧ Fext b = v :=
  ⟨Function.update F b v, analyticAt_update_of_tendsto hF ht,
    Function.update_eventuallyEq_nhdsNE F b b v, by simp⟩

/-- Eventual boundedness is sufficient for the actual finite punctured limit. -/
theorem tendsto_limUnder_of_eventually_bounded {F : ℂ → ℂ} {b : ℂ} {M : ℝ}
    (hF : ∀ᶠ z in 𝓝[≠] b, AnalyticAt ℂ F z)
    (hbound : ∀ᶠ z in 𝓝[≠] b, ‖F z‖ ≤ M) :
    Tendsto F (𝓝[≠] b) (𝓝 (limUnder (𝓝[≠] b) F)) := by
  have hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] b) (fun z => ‖F z - F b‖) := by
    refine ⟨M + ‖F b‖, eventually_map.mpr ?_⟩
    filter_upwards [hbound] with z hz
    exact norm_sub_le_of_le hz le_rfl
  exact Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    (hF.mono fun _ h => h.differentiableAt) hb

theorem analyticAt_update_limUnder_of_eventually_bounded {F : ℂ → ℂ} {b : ℂ} {M : ℝ}
    (hF : ∀ᶠ z in 𝓝[≠] b, AnalyticAt ℂ F z)
    (hbound : ∀ᶠ z in 𝓝[≠] b, ‖F z‖ ≤ M) :
    AnalyticAt ℂ (Function.update F b (limUnder (𝓝[≠] b) F)) b :=
  analyticAt_update_of_tendsto hF (tendsto_limUnder_of_eventually_bounded hF hbound)

theorem exists_analytic_extension_of_eventually_bounded {F : ℂ → ℂ} {b : ℂ} {M : ℝ}
    (hF : ∀ᶠ z in 𝓝[≠] b, AnalyticAt ℂ F z)
    (hbound : ∀ᶠ z in 𝓝[≠] b, ‖F z‖ ≤ M) :
    ∃ Fext : ℂ → ℂ, AnalyticAt ℂ Fext b ∧
      Fext =ᶠ[𝓝[≠] b] F ∧ Fext b = limUnder (𝓝[≠] b) F :=
  exists_analytic_extension_of_tendsto hF (tendsto_limUnder_of_eventually_bounded hF hbound)

/-- Change the actual scalar function at the two specified points only. -/
def patchTwo (F : ℂ → ℂ) (a b va vb : ℂ) : ℂ → ℂ :=
  Function.update (Function.update F a va) b vb

@[simp] theorem patchTwo_left (F : ℂ → ℂ) {a b : ℂ} (va vb : ℂ) (hab : a ≠ b) :
    patchTwo F a b va vb a = va := by simp [patchTwo, hab]

@[simp] theorem patchTwo_right (F : ℂ → ℂ) (a b va vb : ℂ) :
    patchTwo F a b va vb b = vb := by simp [patchTwo]

theorem patchTwo_eq_of_ne (F : ℂ → ℂ) {a b z : ℂ} (va vb : ℂ)
    (hza : z ≠ a) (hzb : z ≠ b) : patchTwo F a b va vb z = F z := by
  simp only [patchTwo, Function.update_of_ne hza, Function.update_of_ne hzb]

theorem patchTwo_eventuallyEq_nhdsNE (F : ℂ → ℂ) (a b va vb c : ℂ) :
    patchTwo F a b va vb =ᶠ[𝓝[≠] c] F :=
  (Function.update_eventuallyEq_nhdsNE (Function.update F a va) b c vb).trans
    (Function.update_eventuallyEq_nhdsNE F a c va)

/-- The finite update leaves every reciprocal-coordinate germ at infinity unchanged. -/
theorem patchTwo_eventuallyEq_cocompact (F : ℂ → ℂ) (a b va vb : ℂ) :
    patchTwo F a b va vb =ᶠ[cocompact ℂ] F := by
  have ha : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ a := isCompact_singleton.compl_mem_cocompact
  have hb : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ b := isCompact_singleton.compl_mem_cocompact
  filter_upwards [ha, hb] with z hza hzb
  exact patchTwo_eq_of_ne F va vb hza hzb

/-- Two finite punctured limits and analyticity elsewhere give an actual
entire function, with no global extension premise. -/
theorem patchTwo_entire {F : ℂ → ℂ} {a b va vb : ℂ} (hab : a ≠ b)
    (hF : ∀ z, z ≠ a → z ≠ b → AnalyticAt ℂ F z)
    (ha : Tendsto F (𝓝[≠] a) (𝓝 va)) (hb : Tendsto F (𝓝[≠] b) (𝓝 vb)) :
    ∀ z, AnalyticAt ℂ (patchTwo F a b va vb) z := by
  have hFa : ∀ᶠ z in 𝓝[≠] a, AnalyticAt ℂ F z := by
    filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hab] with z hza hzb
    exact hF z hza hzb
  have hFb : ∀ᶠ z in 𝓝[≠] b, AnalyticAt ℂ F z := by
    filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hab.symm] with z hzb hza
    exact hF z hza hzb
  intro z
  by_cases hza : z = a
  · subst z
    exact analyticAt_update_of_ne (analyticAt_update_of_tendsto hFa ha) hab
  by_cases hzb : z = b
  · subst z
    rw [patchTwo, Function.update_comm hab]
    exact analyticAt_update_of_ne (analyticAt_update_of_tendsto hFb hb) hab.symm
  exact analyticAt_update_of_ne (analyticAt_update_of_ne (hF z hza hzb) hza) hzb

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovable
