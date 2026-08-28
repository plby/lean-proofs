import Wikipedia.HopfProblem.DegreeCollapseSupportedCuspPairs

/-!
# Native immersion and transversality for the supported cusp

Away from source zero, the first five unchanged derivative coordinates
already detect every nonzero tangent vector. Near zero the full map is the
original polynomial cusp. At its two endpoint preimages the full germs also
agree with that model, so the new double point is natively transverse.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization WhitneyCusp

theorem fderiv_first_five {β : Vector 3 → ℝ} (hβ : ContDiff ℝ ∞ β)
    (t : ℝ) (x v : Vector 3) (i : Fin 5) :
    fderiv ℝ (map β t) x v i.castSucc = differential (-1) x v i.castSucc := by
  have hs : ContDiff ℝ ∞ (map β t) :=
    (contDiff_map hβ).comp
      (show ContDiff ℝ ∞ (fun y : Vector 3 ↦ (t, y)) from contDiff_const.prodMk contDiff_id)
  have hf : DifferentiableAt ℝ (map β t) x := hs.differentiable (by simp) x
  let P : Vector 6 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 ↦ ℝ) i.castSucc
  have h₁ : HasFDerivAt (fun y ↦ map β t y i.castSucc)
      (P.comp (fderiv ℝ (map β t) x)) x :=
    ((PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 (map β t x) i.castSucc).hasFDerivAt).comp
      x hf.hasFDerivAt
  have h₂ : HasFDerivAt (fun y ↦ WhitneyCusp.map (-1) y i.castSucc)
      (P.comp (differential (-1) x)) x :=
    ((PiLp.hasStrictFDerivAt_apply (𝕜 := ℝ) 2 (WhitneyCusp.map (-1) x) i.castSucc).hasFDerivAt).comp
      x (WhitneyCusp.hasStrictFDerivAt_map (-1) x).hasFDerivAt
  have he : (fun y ↦ map β t y i.castSucc) =
      (fun y ↦ WhitneyCusp.map (-1) y i.castSucc) := by
    funext y
    fin_cases i <;> rfl
  have hL := h₁.unique (he.symm ▸ h₂)
  exact DFunLike.congr_fun hL v

theorem injective_fderiv_off_zero {β : Vector 3 → ℝ} (hβ : ContDiff ℝ ∞ β)
    (t : ℝ) (x : Vector 3) (hx : x ≠ 0) : Injective (fderiv ℝ (map β t) x) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hc (i : Fin 5) : differential (-1) x v i.castSucc = 0 := by
    rw [← fderiv_first_five hβ t x v i, hv]
    rfl
  have h₀ : v 0 = 0 := hc 0
  have h₁ : v 1 = 0 := hc 1
  by_cases hv₂ : v 2 = 0
  · ext i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact hv₂
  have h₂ : 2 * x 2 * v 2 = 0 := hc 2
  have h₃ : x 2 * v 0 + x 0 * v 2 = 0 := hc 3
  have h₄ : x 2 * v 1 + x 1 * v 2 = 0 := hc 4
  have hx₂ : x 2 = 0 := by
    have h := (mul_eq_zero.mp h₂).resolve_right hv₂
    linarith
  have hx₀ : x 0 = 0 := by
    rw [h₀, mul_zero, zero_add] at h₃
    exact (mul_eq_zero.mp h₃).resolve_right hv₂
  have hx₁ : x 1 = 0 := by
    rw [h₁, mul_zero, zero_add] at h₄
    exact (mul_eq_zero.mp h₄).resolve_right hv₂
  apply (hx ?_).elim
  ext i
  fin_cases i
  · exact hx₀
  · exact hx₁
  · exact hx₂

theorem injective_fderiv_of_parameter_ne_zero (β : Cutoff) {t : ℝ} (ht : t ≠ 0)
    (x : Vector 3) : Injective (fderiv ℝ (map β.value t) x) := by
  by_cases hx : x = 0
  · subst x
    rw [(map_eq_cusp_near β t (by simp : ‖(0 : Vector 3)‖ < 2)).fderiv_eq]
    exact (WhitneyCusp.injective_fderiv_iff t 0).mpr (Or.inl ht)
  · exact injective_fderiv_off_zero β.smooth t x hx

theorem surjective_endpoint_tangent_sum (β : Cutoff) (x y : Vector 3)
    (hne : x ≠ y) (heq : map β.value 1 x = map β.value 1 y) :
    Surjective ((fderiv ℝ (map β.value 1) x).coprod (fderiv ℝ (map β.value 1) y)) := by
  have hnorm : ‖x‖ < 2 ∧ ‖y‖ < 2 := by
    rcases (endpoint_map_eq_iff β x y).mp heq with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hne h).elim
    · simp [norm_axis]
    · simp [norm_axis]
  have hx := (map_eq_cusp_near β 1 hnorm.1).fderiv_eq (𝕜 := ℝ)
  have hy := (map_eq_cusp_near β 1 hnorm.2).fderiv_eq (𝕜 := ℝ)
  rw [hx, hy, WhitneyCusp.fderiv_map, WhitneyCusp.fderiv_map]
  have heq' : WhitneyCusp.map 1 x = WhitneyCusp.map 1 y := by
    rw [← map_eq_cusp_of_one 1 (β.one x hnorm.1.le),
      ← map_eq_cusp_of_one 1 (β.one y hnorm.2.le)]
    exact heq
  have htrans := (WhitneyCusp.transverse_double_point 1 x y heq' hne).surjective
  rw [WhitneyCusp.fderiv_difference] at htrans
  intro w
  obtain ⟨⟨v₁, v₂⟩, hv⟩ := htrans w
  refine ⟨(v₁, -v₂), ?_⟩
  change differential 1 x v₁ + differential 1 y (-v₂) = w
  rw [map_neg, ← sub_eq_add_neg]
  exact hv

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp
