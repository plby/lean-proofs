import Wikipedia.HopfProblem.DegreeCollapseStationaryPairWeight
import Wikipedia.HopfProblem.DegreeCollapseSmallNativeFieldBlocks
import Wikipedia.HopfProblem.DegreeCollapseMorseRearrangementFromWeight

/-!
# Constructed native critical-value rearrangement with no connecting orbit

For an isolated ordered critical pair of the actual Morse function, an
unchanged complete descending field with model germs and no selected
connection constructs the separating weight and the new global Morse
function. Small whole blocks, both regular bridges, the middle cylinder,
compact endpoint sections, plateau germs and the weight are all derived.
The targets can occur in the opposite order. The original critical set
and every intrinsic Morse index are preserved.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

theorem exists_morse_rearrangement_of_no_connection {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : InjOn f (criticalPoints E f))
    {p q : M} (cp : SignedMorseChart (E := E) f p) (cq : SignedMorseChart (E := E) f q)
    (hfp : ∀ᶠ y in 𝓝 p, V y = cp.descentField y)
    (hfq : ∀ᶠ y in 𝓝 q, V y = cq.descentField y)
    {l u p' q' : ℝ} (hp : f p ∈ Ioo l u) (hq : f q ∈ Ioo l u) (hpq : f p < f q)
    (hp' : p' ∈ Ioo l u) (hq' : q' ∈ Ioo l u)
    (hpair : ∀ z ∈ criticalPoints E f, f z ∈ Icc l u → z = p ∨ z = q)
    (hnoconnection : ∀ x, ¬(Tendsto (fun t => F t x) atBot (𝓝 q) ∧
      Tendsto (fun t => F t x) atTop (𝓝 p))) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      criticalPoints E g = criticalPoints E f ∧ g p = p' ∧ g q = q' ∧
      (∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) g x (V x) < 0) ∧
      (∀ x, f x ∉ Ioo l u → g =ᶠ[𝓝 x] f) ∧
      (g =ᶠ[𝓝 p] fun x => f x + (p' - f p)) ∧
      (g =ᶠ[𝓝 q] fun x => f x + (q' - f q)) ∧
      (∀ x ∈ criticalPoints E f, x ≠ p → x ≠ q → g =ᶠ[𝓝 x] f) ∧
      (∀ x ∈ criticalPoints E f, nativeMorseIndex E g x = nativeMorseIndex E f x) := by
  obtain ⟨a, hpa, haq⟩ := exists_between hpq
  obtain ⟨rp, hrp, hrpa, hbp, hfieldp⟩ :=
    exists_small_native_morse_field_block cp hfp (sub_pos.mpr hpa)
  obtain ⟨rq, hrq, hrqa, hbq, hfieldq⟩ :=
    exists_small_native_morse_field_block cq hfq (sub_pos.mpr haq)
  have hpa' : f p + rp ^ 2 ≤ a := by linarith
  have haq' : a ≤ f q - rq ^ 2 := by linarith
  have hregular (x : M) (hx : f x ∈ Ioo (f p) (f q)) : x ∉ criticalPoints E f := by
    intro hcrit
    rcases hpair x hcrit ⟨hp.1.le.trans hx.1.le, hx.2.le.trans hq.2.le⟩ with heq | heq
    · rw [heq] at hx
      exact lt_irrefl _ hx.1
    · rw [heq] at hx
      exact lt_irrefl _ hx.2
  have hbandp : ∀ x, f x ∈ Icc (f p + rp ^ 2) a → x ∉ criticalPoints E f := by
    intro x hx
    apply hregular x
    exact ⟨by nlinarith [hx.1, sq_pos_of_pos hrp], hx.2.trans_lt haq⟩
  have hbandq : ∀ x, f x ∈ Icc a (f q - rq ^ 2) → x ∉ criticalPoints E f := by
    intro x hx
    apply hregular x
    exact ⟨hpa.trans_le hx.1, by nlinarith [hx.2, sq_pos_of_pos hrq]⟩
  obtain ⟨W, hW, hWrange, hWinv, hWp, hWq⟩ := exists_stationary_pair_weight hf hV F hF
    hzero hdesc hinj cp cq hrp hrq (hp.1.trans hpa) (haq.trans hq.2) hpair
    hbp hbq hfieldp hfieldq hpa' haq' hbandp hbandq hnoconnection
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, hexterior, hpgerm, hqgerm, hothers, -⟩ :=
    exists_rearranged_morse_function_of_stationary_weight hf hm F hF hdesc hp hq hp' hq'
      (fun x hx hband => hpair x hx ⟨hband.1.le, hband.2.le⟩) hW hWrange hWinv hWp hWq
  refine ⟨g, hg, hmg, hcrit, hgp, hgq, hdescent, hexterior, hpgerm, hqgerm, hothers, ?_⟩
  intro x hx
  by_cases hxp : x = p
  · subst x
    exact nativeMorseIndex_of_add_const_germ cp hpgerm
  by_cases hxq : x = q
  · subst x
    exact nativeMorseIndex_of_add_const_germ cq hqgerm
  exact nativeMorseIndex_congr_germ (hothers x hx hxp hxq)

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
