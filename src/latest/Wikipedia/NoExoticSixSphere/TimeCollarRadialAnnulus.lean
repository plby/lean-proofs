import Wikipedia.NoExoticSixSphere.TimeCollarInteriorHomotopy
import Wikipedia.NoExoticSixSphere.TimeCollarRadialDisk
import Wikipedia.NoExoticSixSphere.RadialAnnulusGluing

/-!
# An actual positive-time annulus with prescribed collars

Given a homotopy in the nonnegative half, move its endpoints along the
two prescribed collars. Transfer the resulting homotopy to positive time,
restoring both new endpoints exactly, and glue both collars back. The
original boundary spheres and the entire chosen collars are unchanged.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace NoExoticSixSphere.TimeCollarAnnulus

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse TimeCollar

variable {M : Type} [TopologicalSpace M] (t : M → ℝ)

def halfRadialHomotopy {p : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (g : Vector (p + 1) → M) (hg : ContinuousOn g {x | a ≤ ‖x‖ ∧ ‖x‖ ≤ b})
    (hnn : ∀ x, a ≤ ‖x‖ → ‖x‖ ≤ b → 0 ≤ t (g x))
    (f₀ f₁ : C(Sphere p, NonnegativeHalf t))
    (hb₀ : ∀ s, g (a • s.val) = (f₀ s).val)
    (hb₁ : ∀ s, g (b • s.val) = (f₁ s).val) : f₀.Homotopy f₁ := by
  let radius : unitInterval → ℝ := fun u ↦ a + (b - a) * (u : ℝ)
  have hradius (u : unitInterval) : a ≤ radius u ∧ radius u ≤ b := by
    have h₀ := mul_nonneg (sub_nonneg.mpr hab) u.property.1
    have h₁ := mul_le_mul_of_nonneg_left u.property.2 (sub_nonneg.mpr hab)
    dsimp only [radius]
    constructor <;> nlinarith
  have hc : Continuous radius :=
    continuous_const.add (continuous_const.mul continuous_subtype_val)
  have hray (z : unitInterval × Sphere p) :
      a ≤ ‖radius z.1 • z.2.val‖ ∧ ‖radius z.1 • z.2.val‖ ≤ b := by
    rw [norm_smul, Real.norm_of_nonneg (ha.trans (hradius z.1).1),
      ClosedHemisphere.unit_norm, mul_one]
    exact hradius z.1
  exact {
    toFun := fun z ↦ ⟨g (radius z.1 • z.2.val), hnn _ (hray z).1 (hray z).2⟩
    continuous_toFun := (hg.comp_continuous
      ((hc.comp continuous_fst).smul (continuous_subtype_val.comp continuous_snd))
      hray).subtype_mk _
    map_zero_left := fun s ↦ by
      apply Subtype.ext
      change g ((a + (b - a) * (0 : ℝ)) • s.val) = (f₀ s).val
      simpa only [mul_zero, add_zero] using hb₀ s
    map_one_left := fun s ↦ by
      apply Subtype.ext
      change g ((a + (b - a) * (1 : ℝ)) • s.val) = (f₁ s).val
      simpa only [mul_one, add_sub_cancel] using hb₁ s }

theorem exists_positive_cylinder_with_prescribed_collars {p : ℕ} {B : Type}
    [TopologicalSpace B] (C : TimeCollar t B)
    (f₀ f₁ : C(Sphere p, {x : M // t x = 0}))
    (H : ((TimeCollarDisk.zeroToHalf t).comp f₀).Homotopy
      ((TimeCollarDisk.zeroToHalf t).comp f₁))
    (ρ₀ ρ₁ : ℝ) (hρ₀ : 1 < ρ₀) (hρ : ρ₀ < ρ₁) (hρ₁ : ρ₁ < 2)
    (g₀ g₁ : Vector (p + 1) → M)
    (hg₀ : ContinuousOn g₀ {x | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₀})
    (hg₁ : ContinuousOn g₁ {x | ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ 2})
    (hb₀ : ∀ s : Sphere p, g₀ s.val = (f₀ s).val)
    (hb₁ : ∀ s : Sphere p, g₁ ((2 : ℝ) • s.val) = (f₁ s).val)
    (hp₀ : ∀ x, 1 < ‖x‖ → ‖x‖ ≤ ρ₀ → 0 < t (g₀ x))
    (hp₁ : ∀ x, ρ₁ ≤ ‖x‖ → ‖x‖ < 2 → 0 < t (g₁ x)) :
    ∃ J : C(unitInterval × Sphere p, M),
      (∀ s : Sphere p, J (0, s) = g₀ (ρ₀ • s.val)) ∧
      (∀ s : Sphere p, J (1, s) = g₁ (ρ₁ • s.val)) ∧
      ∀ z, 0 < t (J z) := by
  have hn (u : ℝ) (hu : 0 ≤ u) (s : Sphere p) : ‖u • s.val‖ = u := by
    rw [norm_smul, Real.norm_of_nonneg hu, ClosedHemisphere.unit_norm, mul_one]
  have hnn₀ (x : Vector (p + 1)) (hx₀ : 1 ≤ ‖x‖) (hx₁ : ‖x‖ ≤ ρ₀) :
      0 ≤ t (g₀ x) := by
    by_cases hx : ‖x‖ = 1
    · let s : Sphere p := ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩
      exact ((congrArg t (hb₀ s)).trans (f₀ s).property).ge
    · exact (hp₀ x (lt_of_le_of_ne hx₀ (Ne.symm hx)) hx₁).le
  have hnn₁ (x : Vector (p + 1)) (hx₀ : ρ₁ ≤ ‖x‖) (hx₁ : ‖x‖ ≤ 2) :
      0 ≤ t (g₁ x) := by
    by_cases hx : ‖x‖ = 2
    · let s : Sphere p := ⟨(1 / 2 : ℝ) • x, by
        rw [mem_sphere_zero_iff_norm, norm_smul, hx]
        norm_num⟩
      have he : (2 : ℝ) • s.val = x := by
        change (2 : ℝ) • ((1 / 2 : ℝ) • x) = x
        rw [smul_smul]
        norm_num
      have hz : t (g₁ x) = 0 := by
        rw [← he, hb₁]
        exact (f₁ s).property
      exact hz.ge
    · exact (hp₁ x hx₀ (lt_of_le_of_ne hx₁ hx)).le
  have hρ₀pos : 0 ≤ ρ₀ := (zero_lt_one.trans hρ₀).le
  have hρ₁pos : 0 ≤ ρ₁ := hρ₀pos.trans hρ.le
  have hcut₀ (s : Sphere p) : 1 ≤ ‖ρ₀ • s.val‖ ∧ ‖ρ₀ • s.val‖ ≤ ρ₀ := by
    rw [hn ρ₀ hρ₀pos]
    exact ⟨hρ₀.le, le_rfl⟩
  have hcut₁ (s : Sphere p) : ρ₁ ≤ ‖ρ₁ • s.val‖ ∧ ‖ρ₁ • s.val‖ ≤ 2 := by
    rw [hn ρ₁ hρ₁pos]
    exact ⟨le_rfl, hρ₁.le⟩
  have hc₀ : Continuous (fun s : Sphere p ↦ ρ₀ • s.val) :=
    (continuous_const : Continuous (fun _ : Sphere p ↦ ρ₀)).smul continuous_subtype_val
  have hc₁ : Continuous (fun s : Sphere p ↦ ρ₁ • s.val) :=
    (continuous_const : Continuous (fun _ : Sphere p ↦ ρ₁)).smul continuous_subtype_val
  let fInner₀ : C(Sphere p, C.positiveInterior) :=
    ⟨fun s ↦ ⟨g₀ (ρ₀ • s.val), hp₀ _ (by rw [hn ρ₀ hρ₀pos]; exact hρ₀)
      (hcut₀ s).2⟩,
      (hg₀.comp_continuous hc₀ hcut₀).subtype_mk _⟩
  let fInner₁ : C(Sphere p, C.positiveInterior) :=
    ⟨fun s ↦ ⟨g₁ (ρ₁ • s.val), hp₁ _ (hcut₁ s).1
      (by rw [hn ρ₁ hρ₁pos]; exact hρ₁)⟩,
      (hg₁.comp_continuous hc₁ hcut₁).subtype_mk _⟩
  let H₀ : ((TimeCollarDisk.zeroToHalf t).comp f₀).Homotopy
      (C.interiorToHalf.comp fInner₀) :=
    halfRadialHomotopy t 1 ρ₀ zero_le_one hρ₀.le g₀ hg₀ hnn₀
      ((TimeCollarDisk.zeroToHalf t).comp f₀) (C.interiorToHalf.comp fInner₀)
      (fun s ↦ by
        change g₀ ((1 : ℝ) • s.val) = (f₀ s).val
        rw [one_smul]
        exact hb₀ s) (fun _ ↦ rfl)
  let H₁ : (C.interiorToHalf.comp fInner₁).Homotopy
      ((TimeCollarDisk.zeroToHalf t).comp f₁) :=
    halfRadialHomotopy t ρ₁ 2 hρ₁pos hρ₁.le g₁ hg₁ hnn₁
      (C.interiorToHalf.comp fInner₁) ((TimeCollarDisk.zeroToHalf t).comp f₁)
      (fun _ ↦ rfl) hb₁
  let J : fInner₀.Homotopy fInner₁ :=
    interiorHomotopyOfHalfHomotopy C fInner₀ fInner₁ ((H₀.symm.trans H).trans H₁.symm)
  let JM : C(unitInterval × Sphere p, M) :=
    ⟨fun z ↦ (J z).val, continuous_subtype_val.comp J.continuous⟩
  have hJ₀ (s : Sphere p) : JM (0, s) = g₀ (ρ₀ • s.val) :=
    congrArg (fun z : C.positiveInterior ↦ z.val) (J.map_zero_left s)
  have hJ₁ (s : Sphere p) : JM (1, s) = g₁ (ρ₁ • s.val) :=
    congrArg (fun z : C.positiveInterior ↦ z.val) (J.map_one_left s)
  exact ⟨JM, hJ₀, hJ₁, fun z ↦ (J z).property⟩

theorem exists_annulus_with_prescribed_collars {p : ℕ} {B : Type} [TopologicalSpace B]
    (C : TimeCollar t B) (b : Sphere p)
    (f₀ f₁ : C(Sphere p, {x : M // t x = 0}))
    (H : ((TimeCollarDisk.zeroToHalf t).comp f₀).Homotopy
      ((TimeCollarDisk.zeroToHalf t).comp f₁))
    (ρ₀ ρ₁ : ℝ) (hρ₀ : 1 < ρ₀) (hρ : ρ₀ < ρ₁) (hρ₁ : ρ₁ < 2)
    (g₀ g₁ : Vector (p + 1) → M)
    (hg₀ : ContinuousOn g₀ {x | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ ρ₀})
    (hg₁ : ContinuousOn g₁ {x | ρ₁ ≤ ‖x‖ ∧ ‖x‖ ≤ 2})
    (hb₀ : ∀ s : Sphere p, g₀ s.val = (f₀ s).val)
    (hb₁ : ∀ s : Sphere p, g₁ ((2 : ℝ) • s.val) = (f₁ s).val)
    (hp₀ : ∀ x, 1 < ‖x‖ → ‖x‖ ≤ ρ₀ → 0 < t (g₀ x))
    (hp₁ : ∀ x, ρ₁ ≤ ‖x‖ → ‖x‖ < 2 → 0 < t (g₁ x)) :
    ∃ G : C(SphereAnnulus.domain p, M),
      (∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ ρ₀ → G x = g₀ x.val) ∧
      (∀ x : SphereAnnulus.domain p, ρ₁ ≤ ‖x.val‖ → G x = g₁ x.val) ∧
      ∀ x : SphereAnnulus.domain p, 1 < ‖x.val‖ → ‖x.val‖ < 2 → 0 < t (G x) := by
  obtain ⟨JM, hJ₀, hJ₁, hJpos⟩ := exists_positive_cylinder_with_prescribed_collars
    t C f₀ f₁ H ρ₀ ρ₁ hρ₀ hρ hρ₁ g₀ g₁ hg₀ hg₁ hb₀ hb₁ hp₀ hp₁
  exact RadialAnnulusGluing.exists_map b ρ₀ ρ₁ hρ g₀ g₁
    (hg₀.mono (fun _ hx ↦ ⟨hx.1.1, hx.2⟩))
    (hg₁.mono (fun _ hx ↦ ⟨hx.2, hx.1.2⟩)) JM hJ₀ hJ₁ {x | 0 < t x}
    hJpos (fun x _ hx hrx ↦ hp₀ x hx hrx)
    (fun x _ hx hrx ↦ hp₁ x hrx hx)

end NoExoticSixSphere.TimeCollarAnnulus
