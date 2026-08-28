import Wikipedia.HopfProblem.RiemannSphereMobiusNormalization
import Wikipedia.HopfProblem.RiemannSphereMobiusCircleAlgebra

/-!
# Cross-ratio normalization of the unit disc

For three distinct boundary points, the genuine sphere automorphism maps
the unit circle to the extended real line. Its restriction to the open disc
is bijective onto one open half-plane, selected by an explicit nonzero real
orientation constant.
-/

noncomputable section

open Set OnePoint
open scoped ContDiff

namespace Wikipedia.HopfProblem.RiemannSphere

open MobiusCircle

/-- The finite copy in the sphere of a set of complex numbers. -/
def finiteImage (s : Set ℂ) : Set RiemannSphere := ((↑) : ℂ → RiemannSphere) '' s

@[simp] theorem coe_mem_finiteImage_iff (s : Set ℂ) (z : ℂ) :
    (z : RiemannSphere) ∈ finiteImage s ↔ z ∈ s := by
  simp [finiteImage]

@[simp] theorem infty_not_mem_finiteImage (s : Set ℂ) :
    (∞ : RiemannSphere) ∉ finiteImage s := by
  simp [finiteImage]

/-- The standard open unit disc inside the sphere. -/
def sphereUnitDisc : Set RiemannSphere := finiteImage {z : ℂ | ‖z‖ < 1}

/-- The standard unit circle inside the sphere. -/
def sphereUnitCircle : Set RiemannSphere := finiteImage {z : ℂ | ‖z‖ = 1}

/-- The real axis together with infinity. -/
def sphereRealCircle : Set RiemannSphere :=
  finiteImage {z : ℂ | z.im = 0} ∪ {(∞ : RiemannSphere)}

/-- A half-plane selected by the sign of a nonzero real number. -/
def sphereHalfPlane (k : ℝ) : Set RiemannSphere :=
  finiteImage {z : ℂ | 0 < k * z.im}

@[simp] theorem coe_mem_sphereRealCircle_iff (z : ℂ) :
    (z : RiemannSphere) ∈ sphereRealCircle ↔ z.im = 0 := by
  simp [sphereRealCircle]

@[simp] theorem infty_mem_sphereRealCircle :
    (∞ : RiemannSphere) ∈ sphereRealCircle := by
  simp [sphereRealCircle]

variable {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
variable (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)

include ha hb hc in
theorem threePointBiholomorph_mapsTo_circle :
    MapsTo (threePointBiholomorph a b c hab hac hbc) sphereUnitCircle sphereRealCircle := by
  rintro p ⟨z, hz, rfl⟩
  by_cases hzc : z = c
  · subst z
    simp
  · rw [threePointBiholomorph_coe a b c hab hac hbc z hzc,
      coe_mem_sphereRealCircle_iff]
    exact crossRatio_im_eq_zero_of_norm_eq_one ha hb hc hab.symm hz

include ha hb hc in
theorem threePointBiholomorph_mem_halfPlane_iff (p : RiemannSphere) :
    threePointBiholomorph a b c hab hac hbc p ∈ sphereHalfPlane (orientation a b c) ↔
      p ∈ sphereUnitDisc := by
  induction p using OnePoint.rec with
  | infty =>
    rw [threePointBiholomorph_infty]
    change ((coefficient a b c : ℂ) : RiemannSphere) ∈
      finiteImage {z : ℂ | 0 < orientation a b c * z.im} ↔
        (∞ : RiemannSphere) ∈ finiteImage {z : ℂ | ‖z‖ < 1}
    simp only [coe_mem_finiteImage_iff, mem_ofPred_eq, infty_not_mem_finiteImage, iff_false]
    exact le_of_lt (orientation_mul_coefficient_im_neg ha hb hc hab.symm hbc hac)
      |>.not_gt
  | coe z =>
    by_cases hzc : z = c
    · subst z
      rw [threePointBiholomorph_third]
      simp [sphereHalfPlane, sphereUnitDisc, hc]
    · rw [threePointBiholomorph_coe a b c hab hac hbc z hzc]
      simp only [sphereHalfPlane, sphereUnitDisc, coe_mem_finiteImage_iff, mem_ofPred_eq]
      exact orientation_mul_crossRatio_im_pos_iff ha hb hc hab.symm hbc hac hzc

include ha hb hc in
/-- The actual fixed-atlas sphere automorphism restricts to a bijection
from the open disc onto its oriented half-plane. -/
theorem threePointBiholomorph_bijOn_disc :
    BijOn (threePointBiholomorph a b c hab hac hbc)
      sphereUnitDisc (sphereHalfPlane (orientation a b c)) := by
  refine ⟨?_, (threePointBiholomorph a b c hab hac hbc).injective.injOn, ?_⟩
  · intro p hp
    exact (threePointBiholomorph_mem_halfPlane_iff hab hac hbc ha hb hc p).mpr hp
  · intro q hq
    obtain ⟨p, rfl⟩ := (threePointBiholomorph a b c hab hac hbc).surjective q
    exact ⟨p, (threePointBiholomorph_mem_halfPlane_iff hab hac hbc ha hb hc p).mp hq, rfl⟩

include ha hb hc in
theorem threePointBiholomorph_image_disc :
    threePointBiholomorph a b c hab hac hbc '' sphereUnitDisc =
      sphereHalfPlane (orientation a b c) :=
  (threePointBiholomorph_bijOn_disc hab hac hbc ha hb hc).image_eq

include ha hb hc hab hac hbc in
/-- The same bijection in the ordinary complex coordinates of both open sets. -/
theorem crossRatio_bijOn_disc :
    BijOn (crossRatio a b c) {z : ℂ | ‖z‖ < 1}
      {z : ℂ | 0 < orientation a b c * z.im} := by
  have hpole : ∀ z : ℂ, ‖z‖ < 1 → z ≠ c := by
    intro z hz he
    subst z
    exact (not_lt_of_ge hc.ge) hz
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact (orientation_mul_crossRatio_im_pos_iff ha hb hc hab.symm hbc hac (hpole z hz)).mpr hz
  · intro z hz w hw he
    have hs : threePointBiholomorph a b c hab hac hbc (z : RiemannSphere) =
        threePointBiholomorph a b c hab hac hbc (w : RiemannSphere) := by
      rw [threePointBiholomorph_coe a b c hab hac hbc z (hpole z hz),
        threePointBiholomorph_coe a b c hab hac hbc w (hpole w hw)]
      exact congrArg ((↑) : ℂ → RiemannSphere) he
    exact OnePoint.coe_injective ((threePointBiholomorph a b c hab hac hbc).injective hs)
  · intro w hw
    have hw' : (w : RiemannSphere) ∈ sphereHalfPlane (orientation a b c) := by
      simpa only [sphereHalfPlane, coe_mem_finiteImage_iff, mem_ofPred_eq] using hw
    obtain ⟨p, hp, he⟩ := (threePointBiholomorph_bijOn_disc hab hac hbc ha hb hc).surjOn hw'
    obtain ⟨z, hz, rfl⟩ := hp
    refine ⟨z, hz, ?_⟩
    rw [threePointBiholomorph_coe a b c hab hac hbc z (hpole z hz)] at he
    exact OnePoint.coe_injective he

theorem halfPlane_eq_upper_or_lower {k : ℝ} (hk : k ≠ 0) :
    {z : ℂ | 0 < k * z.im} = {z : ℂ | 0 < z.im} ∨
      {z : ℂ | 0 < k * z.im} = {z : ℂ | z.im < 0} := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · right
    ext z
    simp only [mem_ofPred_eq, mul_pos_iff, not_lt_of_ge hk.le, hk,
      false_and, true_and, false_or]
  · left
    ext z
    exact mul_pos_iff_of_pos_left hk

include ha hb hc hab hac hbc in
/-- In particular the image is one of the two ordinary open half-planes. -/
theorem crossRatio_bijOn_upper_or_lower :
    BijOn (crossRatio a b c) {z : ℂ | ‖z‖ < 1} {z : ℂ | 0 < z.im} ∨
      BijOn (crossRatio a b c) {z : ℂ | ‖z‖ < 1} {z : ℂ | z.im < 0} := by
  have h := crossRatio_bijOn_disc hab hac hbc ha hb hc
  rcases halfPlane_eq_upper_or_lower (orientation_ne_zero ha hb hc hab.symm hbc hac) with hu | hl
  · exact Or.inl (hu ▸ h)
  · exact Or.inr (hl ▸ h)

include ha hb hc in
theorem threePointBiholomorph_mem_realCircle_iff (p : RiemannSphere) :
    threePointBiholomorph a b c hab hac hbc p ∈ sphereRealCircle ↔
      p ∈ sphereUnitCircle := by
  induction p using OnePoint.rec with
  | infty =>
    rw [threePointBiholomorph_infty, coe_mem_sphereRealCircle_iff]
    have hneq : (coefficient a b c).im ≠ 0 := by
      intro he
      have hn := orientation_ne_zero ha hb hc hab.symm hbc hac
      apply hn
      simp [orientation, he]
    simpa only [sphereUnitCircle, infty_not_mem_finiteImage, iff_false, coefficient] using hneq
  | coe z =>
    by_cases hzc : z = c
    · subst z
      simp [sphereUnitCircle, hc]
    · rw [threePointBiholomorph_coe a b c hab hac hbc z hzc,
        coe_mem_sphereRealCircle_iff]
      simp only [sphereUnitCircle, coe_mem_finiteImage_iff, mem_ofPred_eq]
      exact crossRatio_im_eq_zero_iff ha hb hc hab.symm hbc hac hzc

include ha hb hc in
/-- In fact the unit circle maps onto the whole extended real line. -/
theorem threePointBiholomorph_bijOn_circle :
    BijOn (threePointBiholomorph a b c hab hac hbc) sphereUnitCircle sphereRealCircle := by
  refine ⟨threePointBiholomorph_mapsTo_circle hab hac hbc ha hb hc,
    (threePointBiholomorph a b c hab hac hbc).injective.injOn, ?_⟩
  intro q hq
  obtain ⟨p, rfl⟩ := (threePointBiholomorph a b c hab hac hbc).surjective q
  exact ⟨p, (threePointBiholomorph_mem_realCircle_iff hab hac hbc ha hb hc p).mp hq, rfl⟩

include hab hc in
/-- The ordinary cross-ratio formula is holomorphic throughout the open disc. -/
theorem crossRatio_holomorphicOn_disc :
    ContDiffOn ℂ ω (crossRatio a b c) {z : ℂ | ‖z‖ < 1} := by
  intro z hz
  have hzc : z ≠ c := by
    intro he
    subst z
    exact (not_lt_of_ge hc.ge) hz
  have hden : (z - c) * (b - a) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hzc) (sub_ne_zero.mpr hab.symm)
  have hn : ContDiffAt ℂ ω (fun w : ℂ => (w - a) * (b - c)) z :=
    (contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const
  have hd : ContDiffAt ℂ ω (fun w : ℂ => (w - c) * (b - a)) z :=
    (contDiffAt_id.sub contDiffAt_const).mul contDiffAt_const
  exact (hn.div hd hden).contDiffWithinAt

end Wikipedia.HopfProblem.RiemannSphere
