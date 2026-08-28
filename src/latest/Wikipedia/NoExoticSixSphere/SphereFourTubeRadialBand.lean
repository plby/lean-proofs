import Wikipedia.NoExoticSixSphere.SphereFourTubeTimeBands
import Wikipedia.NoExoticSixSphere.SphereRadialHeightCoordinates
import Wikipedia.NoExoticSixSphere.TimeBandSumCoordinates

/-!
# Actual radial coordinates on the new tube time band

The inverse collar uses `sqrt (1 + time)` in the normal four-plane.
The time interval lies strictly above the singular radius zero. Both
inverse identities and continuity are checked in the original tube.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

def innerTimeBand (τ : M → ℝ) (δ : ℝ) : Set (TimeBand τ δ) :=
  {x | x.val ∈ openRegion Φ (3 / 2)}

theorem isOpen_innerTimeBand (hΦ : Φ.source = univ) (τ : M → ℝ) (δ : ℝ) :
    IsOpen (innerTimeBand Φ τ δ) :=
  (isOpen_openRegion Φ hΦ (3 / 2)).preimage continuous_subtype_val

theorem radialPoint_band_bounds {δ : ℝ} (hδ : δ ≤ 1 / 2)
    (p : Ioo (-δ) δ × (Sphere 3 × Sphere 3)) :
    -1 < p.1.val ∧
      ‖SphereRadialHeightCoordinates.point (p.2.2, p.1.val)‖ < 3 / 2 ∧
      ‖SphereRadialHeightCoordinates.point (p.2.2, p.1.val)‖ ^ 2 - 1 = p.1.val := by
  obtain ⟨hp0, hp1⟩ := p.1.property
  have ht : -1 < p.1.val := by linarith
  have hs : (Real.sqrt (1 + p.1.val)) ^ 2 = 1 + p.1.val :=
    Real.sq_sqrt (by linarith)
  rw [SphereRadialHeightCoordinates.norm_point]
  dsimp only
  refine ⟨ht, ?_, ?_⟩
  · nlinarith [Real.sqrt_nonneg (1 + p.1.val)]
  · linarith

theorem exists_inner_time_coordinates (hΦ : Φ.source = univ) (τ : C(M, ℝ))
    (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)
    (b : Sphere 3) (δ : ℝ) (hδ : δ ≤ 1 / 2) :
    ∃ e : innerTimeBand Φ τ δ ≃ₜ Ioo (-δ) δ × (Sphere 3 × Sphere 3),
      (∀ x, (e x).1.val = τ x.val.val) ∧
      ∀ p, (e.symm p).val.val =
        Φ (p.2.1, SphereRadialHeightCoordinates.point (p.2.2, p.1.val)) := by
  haveI : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨by simp⟩
  let P := Ioo (-δ) δ × (Sphere 3 × Sphere 3)
  let X := innerTimeBand Φ τ δ
  let F : P → Sphere 3 × Vector 4 := fun p ↦
    (p.2.1, SphereRadialHeightCoordinates.point (p.2.2, p.1.val))
  have hFt (p : P) : τ (Φ (F p)) = p.1.val :=
    (hinner (F p) (radialPoint_band_bounds hδ p).2.1.le).trans
      (radialPoint_band_bounds hδ p).2.2
  have hFmem (p : P) : Φ (F p) ∈ openRegion Φ (3 / 2) :=
    ⟨F p, ⟨mem_univ _, mem_ball_zero_iff.mpr (radialPoint_band_bounds hδ p).2.1⟩, rfl⟩
  let f : P → X := fun p ↦ ⟨⟨Φ (F p), by rw [hFt]; exact p.1.property⟩, hFmem p⟩
  have hxt (x : X) : x.val.val ∈ Φ.target ∧ ‖(Φ.symm x.val.val).2‖ < 3 / 2 :=
    (mem_openRegion_iff Φ hΦ (3 / 2) x.val.val).mp x.property
  have htime (x : X) : τ x.val.val = ‖(Φ.symm x.val.val).2‖ ^ 2 - 1 := by
    have h := hinner (Φ.symm x.val.val) (hxt x).2.le
    have he : Φ (Φ.symm x.val.val) = x.val.val := Φ.toPartialEquiv.right_inv (hxt x).1
    rwa [he] at h
  have hne (x : X) : (Φ.symm x.val.val).2 ≠ 0 := by
    intro hz
    have hx := x.val.property.1
    have ht := htime x
    rw [hz, norm_zero] at ht
    norm_num at ht
    linarith
  let g : X → P := fun x ↦
    (⟨τ x.val.val, x.val.property⟩,
      ((Φ.symm x.val.val).1, SphereRadialRetraction.retract b (Φ.symm x.val.val).2))
  have hleft : LeftInverse g f := by
    intro p
    have hΦp : Φ.symm (Φ (F p)) = F p :=
      Φ.toPartialEquiv.left_inv (hΦ.symm ▸ mem_univ (F p))
    apply Prod.ext
    · apply Subtype.ext
      exact hFt p
    · apply Prod.ext
      · change (Φ.symm (Φ (F p))).1 = p.2.1
        rw [hΦp]
      · change SphereRadialRetraction.retract b (Φ.symm (Φ (F p))).2 = p.2.2
        rw [hΦp]
        exact congrArg Prod.fst (SphereRadialHeightCoordinates.inverse_point b
          (p := (p.2.2, p.1.val)) (radialPoint_band_bounds hδ p).1)
  have hright : RightInverse g f := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change Φ ((Φ.symm x.val.val).1,
      SphereRadialHeightCoordinates.point
        (SphereRadialRetraction.retract b (Φ.symm x.val.val).2, τ x.val.val)) = x.val.val
    rw [htime x]
    have he : SphereRadialHeightCoordinates.point
        (SphereRadialRetraction.retract b (Φ.symm x.val.val).2,
          ‖(Φ.symm x.val.val).2‖ ^ 2 - 1) = (Φ.symm x.val.val).2 :=
      SphereRadialHeightCoordinates.point_inverse b (hne x)
    rw [he]
    exact Φ.toPartialEquiv.right_inv (hxt x).1
  have hFc : Continuous F := by
    apply Continuous.prodMk (continuous_fst.comp continuous_snd)
    exact (Real.continuous_sqrt.comp
      (continuous_const.add (continuous_subtype_val.comp continuous_fst))).smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  have hfc : Continuous f := by
    exact (((contMDiff Φ hΦ).continuous.comp hFc).subtype_mk _).subtype_mk _
  have hxc : Continuous (fun x : X ↦ x.val.val) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hΦc : Continuous (fun x : X ↦ Φ.symm x.val.val) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous hxc (fun x ↦ (hxt x).1)
  have hgc : Continuous g := by
    apply Continuous.prodMk ((τ.continuous.comp hxc).subtype_mk _)
    apply Continuous.prodMk hΦc.fst
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (SphereRadialRetraction.contMDiffAt_retract (n := 3) b (hne x)).continuousAt.comp
      (f := fun y : X ↦ (Φ.symm y.val.val).2) hΦc.snd.continuousAt
  let e : P ≃ₜ X :=
    { toFun := f, invFun := g, left_inv := hleft, right_inv := hright,
      continuous_toFun := hfc, continuous_invFun := hgc }
  exact ⟨e.symm, fun _ ↦ rfl, fun _ ↦ rfl⟩

end NoExoticSixSphere.SphereFourTube
