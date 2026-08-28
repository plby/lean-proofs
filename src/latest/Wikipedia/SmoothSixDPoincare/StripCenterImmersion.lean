import Wikipedia.SmoothSixDPoincare.StripCoordinateBlend

/-!
# Immersion of the constructed strip along its center

The exact straight center section fixes the horizontal derivative. A nonzero
vertical normal component then makes the full planar derivative injective,
even when the vertical derivative has additional components tangent to the sheet.
-/

noncomputable section

open Function
open Filter Topology

namespace Wikipedia.SmoothSixDPoincare.StripCoordinates

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem horizontal_derivative_of_center {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) (hc : ∀ s, F (s, 0) = center s) :
    fderiv ℝ F (t, 0) (1, 0) = center 1 := by
  have hd := hasDerivAt_horizontalSlice hF
  have heq : (fun s : ℝ => F (s, 0)) = center := funext hc
  rw [heq] at hd
  have hcenter : HasDerivAt (center : ℝ → Space A B) (center 1) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))).prodMk
      (hasDerivAt_const t (0 : B))
  exact hd.unique hcenter

/-- A complete center germ suffices to identify the horizontal strip derivative. -/
theorem horizontal_derivative_of_center_germ {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0))
    (hc : (fun s : ℝ => F (s, 0)) =ᶠ[𝓝 t] center) :
    fderiv ℝ F (t, 0) (1, 0) = center 1 := by
  have hd := hasDerivAt_horizontalSlice hF
  have hcenter : HasDerivAt (center : ℝ → Space A B) (center 1) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : A))).prodMk
      (hasDerivAt_const t (0 : B))
  exact hd.unique (hcenter.congr_of_eventuallyEq hc)

theorem normalDerivative_eq_snd_fderiv {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) :
    normalDerivative F t = (fderiv ℝ F (t, 0) (0, 1)).2 := by
  have hd := hF.hasFDerivAt.snd
  rw [normalDerivative, hd.fderiv]
  rfl

/-- The horizontal center tangent and a nonzero vertical normal component are independent. -/
theorem injective_of_horizontal_and_normal (L : (ℝ × ℝ) →L[ℝ] Space A B)
    (hh : L (1, 0) = center 1) (hn : (L (0, 1)).2 ≠ 0) : Injective L := by
  have hker : ∀ p : ℝ × ℝ, L p = 0 → p = 0 := by
    rintro ⟨a, b⟩ hp
    have hsplit : (a, b) = a • ((1 : ℝ), 0) + b • (0, 1) := by
      ext <;> simp
    rw [hsplit, map_add, map_smul, map_smul, hh] at hp
    have hb0 : b • (L (0, 1)).2 = 0 := by
      simpa [center] using congrArg Prod.snd hp
    have hb : b = 0 := (smul_eq_zero.mp hb0).resolve_right hn
    subst b
    have ha : a = 0 := by
      simpa [center] using congrArg (fun q : Space A B => q.1.1) hp
    subst a
    rfl
  intro p q hpq
  apply sub_eq_zero.mp
  apply hker
  rw [map_sub, hpq, sub_self]

/-- The actual strip map is immersive wherever its vertical normal derivative is nonzero. -/
theorem injective_fderiv_at_center {F : (ℝ × ℝ) → Space A B} {t : ℝ}
    (hF : DifferentiableAt ℝ F (t, 0)) (hc : ∀ s, F (s, 0) = center s)
    (hn : normalDerivative F t ≠ 0) : Injective (fderiv ℝ F (t, 0)) := by
  apply injective_of_horizontal_and_normal (fderiv ℝ F (t, 0))
    (horizontal_derivative_of_center hF hc)
  rwa [← normalDerivative_eq_snd_fderiv hF]

end Wikipedia.SmoothSixDPoincare.StripCoordinates
