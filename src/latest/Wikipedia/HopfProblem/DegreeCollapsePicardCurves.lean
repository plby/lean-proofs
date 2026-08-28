import Wikipedia.HopfProblem.DegreeCollapseSmoothPicard

/-!
# Ordinary ODE curves and smooth endpoints from the Picard path family

The integral equation gives an ordinary curve on the real time line, with
its exact differential equation on the fixed path interval. Evaluating the
smooth path family at the fixed interior time `1` gives a jointly smooth
endpoint map. Identification with the original native flow is still needed.
-/

noncomputable section

open Set Function
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SmoothODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def picardCurve (v : C(E, E)) (p : E) (τ : ℝ) (u : C(PathTime, E)) (t : ℝ) : E :=
  p + τ • (∫ s in (0 : ℝ)..t, v (u (pathClamp s)))

omit [FiniteDimensional ℝ E] in
theorem picardCurve_zero (v : C(E, E)) (p : E) (τ : ℝ) (u : C(PathTime, E)) :
    picardCurve v p τ u 0 = p := by
  simp only [picardCurve, intervalIntegral.integral_same, smul_zero, add_zero]

theorem hasDerivAt_picardCurve (v : C(E, E)) (p : E) (τ : ℝ) (u : C(PathTime, E)) (t : ℝ) :
    HasDerivAt (picardCurve v p τ u) (τ • v (u (pathClamp t))) t :=
  ((hasDerivAt_pathPrimitive (v.comp u) t).const_smul τ).const_add p

omit [FiniteDimensional ℝ E] in
theorem picardCurve_eq_path (v : C(E, E)) {p : E} {τ : ℝ} {u : C(PathTime, E)}
    (heq : ∀ t : PathTime, u t = p + τ •
      (∫ s in (0 : ℝ)..(t : ℝ), v (u (pathClamp s))))
    {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) : picardCurve v p τ u t = u (pathClamp t) := by
  have hc : pathClamp t = ⟨t, ht⟩ := projIcc_of_mem _ ht
  rw [hc]
  exact (heq ⟨t, ht⟩).symm

/-- The actual integral curve solves the scaled vector field throughout the fixed interval. -/
theorem hasDerivAt_picardCurve_of_fixedPoint (v : C(E, E)) {p : E} {τ : ℝ}
    {u : C(PathTime, E)}
    (heq : ∀ t : PathTime, u t = p + τ •
      (∫ s in (0 : ℝ)..(t : ℝ), v (u (pathClamp s))))
    {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    HasDerivAt (picardCurve v p τ u) (τ • v (picardCurve v p τ u t)) t := by
  rw [picardCurve_eq_path v heq ht]
  exact hasDerivAt_picardCurve v p τ u t

/-- Fixed interior-time evaluation of the constructed path family is jointly smooth. -/
theorem exists_smooth_picard_endpoints (v : C(E, E)) (hv : ContDiff ℝ ∞ v) (x : E) :
    ∃ (U : Set (E × ℝ)) (u : E × ℝ → C(PathTime, E)) (g : E × ℝ → E),
      IsOpen U ∧ (x, 0) ∈ U ∧ u (x, 0) = ContinuousMap.const PathTime x ∧
      ContDiffOn ℝ ∞ u U ∧ ContDiffOn ℝ ∞ g U ∧
      (∀ q, g q = u q ⟨1, by norm_num⟩) ∧
      ∀ q ∈ U, (picardCurve v q.1 q.2 (u q) 0 = q.1) ∧
        (picardCurve v q.1 q.2 (u q) 1 = g q) ∧
        (∀ t ∈ Icc (-2 : ℝ) 2, picardCurve v q.1 q.2 (u q) t = u q (pathClamp t)) ∧
        ∀ t ∈ Icc (-2 : ℝ) 2, HasDerivAt (picardCurve v q.1 q.2 (u q))
          (q.2 • v (picardCurve v q.1 q.2 (u q) t)) t := by
  obtain ⟨U, u, hU, hx, hux, hu, heq⟩ := exists_smooth_picard_paths v hv x
  let g (q : E × ℝ) := u q ⟨1, by norm_num⟩
  let L : C(PathTime, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ (⟨1, by norm_num⟩ : PathTime)
  have hg : ContDiffOn ℝ ∞ g U :=
    L.contDiff.comp_contDiffOn hu
  refine ⟨U, u, g, hU, hx, hux, hu, hg, fun _ => rfl, ?_⟩
  intro q hq
  refine ⟨picardCurve_zero v _ _ _, ?_,
    fun t ht => picardCurve_eq_path v (heq q hq) ht,
    fun t ht => hasDerivAt_picardCurve_of_fixedPoint v (heq q hq) ht⟩
  have hh := picardCurve_eq_path v (heq q hq) (t := 1) (by norm_num)
  have hc : pathClamp 1 = (⟨1, by norm_num⟩ : PathTime) := projIcc_of_mem _ (by norm_num)
  exact hh.trans (congrArg (u q) hc)

end Wikipedia.HopfProblem.DegreeCollapse.SmoothODE
