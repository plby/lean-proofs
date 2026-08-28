import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The tangent-space criterion for parametric regular values

For a surjective total derivative, the parameter projection from its kernel
is onto exactly when the spatial derivative is onto. The kernel is supplied
as the actual range of a tangent inclusion; no complementary subspace is
substituted for that range.
-/

namespace NoExoticSixSphere.ParametricRegular

open Function

variable {P E F K : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

theorem surjective_projection_iff (L : P × E →L[ℝ] F) (T : K →L[ℝ] P × E)
    (hL : Surjective L) (hT : T.range = L.ker) :
    Surjective ((ContinuousLinearMap.fst ℝ P E).comp T) ↔
      Surjective (L.comp (ContinuousLinearMap.inr ℝ P E)) := by
  constructor
  · intro hp y
    obtain ⟨⟨p, x⟩, hpx⟩ := hL y
    obtain ⟨u, hu⟩ := hp p
    have hzero : L (T u) = 0 := by
      have hmem : T u ∈ T.range := ⟨u, rfl⟩
      rw [hT] at hmem
      exact hmem
    refine ⟨x - (T u).2, ?_⟩
    have he : (0, x - (T u).2) = (p, x) - T u := by
      apply Prod.ext
      · change 0 = p - (T u).1
        change (T u).1 = p at hu
        rw [hu, sub_self]
      · rfl
    change L (0, x - (T u).2) = y
    rw [he, map_sub, hpx, hzero, sub_zero]
  · intro hx p
    obtain ⟨x, hx⟩ := hx (-L (p, 0))
    have hzero : L (p, x) = 0 := by
      have he : (p, x) = (p, 0) + (0, x) := by ext <;> simp
      rw [he, map_add]
      change L (p, 0) + L (0, x) = 0
      change L (0, x) = -L (p, 0) at hx
      rw [hx, add_neg_cancel]
    have hmem : (p, x) ∈ T.range := by rw [hT]; exact hzero
    obtain ⟨u, hu⟩ := hmem
    exact ⟨u, congrArg Prod.fst hu⟩

theorem range_composed_inclusion {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V →L[ℝ] F) (J : W →L[ℝ] V) (T : K →L[ℝ] W)
    (hJ : Surjective J) (hT : T.range = (L.comp J).ker) :
    (J.comp T).range = L.ker := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    have hmem : T u ∈ T.range := ⟨u, rfl⟩
    rw [hT] at hmem
    exact hmem
  · intro hv
    obtain ⟨w, hw⟩ := hJ v
    have hmem : w ∈ T.range := by
      rw [hT]
      change L (J w) = 0
      rw [hw]
      exact hv
    obtain ⟨u, hu⟩ := hmem
    exact ⟨u, (congrArg J hu).trans hw⟩

end NoExoticSixSphere.ParametricRegular
