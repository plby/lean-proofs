import Wikipedia.HopfProblem.DegreeCollapseReflectedSlabSmoothInclusion

/-!
# A genuine product collar in the reflected fiber's native atlas

Both directions are checked against the independently constructed regular
fiber atlases. The collar is the literal pair of its time and endpoint-fiber
point, and its full normal frame was already identified on this same set.
-/

noncomputable section

open Function Set Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

abbrev EndpointFiber := {x : Sphere m // d.leftMap x = b}

def seamBand : Opens (Fiber d) :=
  ⟨{p | p.val.1 ∈ seamCollarTimes d},
    (seamCollarTimes d).isOpen.preimage (continuous_fst.comp continuous_subtype_val)⟩

def seamForward (p : seamCollarTimes d × EndpointFiber d) : seamBand d :=
  ⟨seamCollarPoint d p.1.val p.1.property p.2, p.1.property⟩

def seamBackward (p : seamBand d) : seamCollarTimes d × EndpointFiber d :=
  (⟨p.val.val.1, p.property⟩,
    ⟨p.val.val.2, (map_on_seamCollar d p.val.val.1 p.property p.val.val.2).symm.trans
      p.val.property⟩)

theorem seamBackward_forward (p : seamCollarTimes d × EndpointFiber d) :
    seamBackward d (seamForward d p) = p := rfl

theorem seamForward_backward (p : seamBand d) :
    seamForward d (seamBackward d p) = p := rfl

variable (k : ℕ) (hd : m = n + k)

theorem contMDiff_seamForward : letI := fiberAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 k)) (𝓡 (k + 1)) ∞ (seamForward d) := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  apply (ContMDiff.subtypeVal_comp_iff (seamBand d) (seamForward d)).mp
  apply (regularFiber_contMDiff_iff_ambient (map d) (contMDiff_map d) b (regular_map d)
    (k + 1) (CylinderFiberNormalFrame.dimension_eq hd) _).mpr
  exact (contMDiff_subtype_val.comp contMDiff_fst).prodMk
    ((regularFiber_contMDiff_subtype_val d.leftMap d.smooth_left b d.regular_left k
      (by simpa using hd)).comp contMDiff_snd)

theorem contMDiff_seamBackward : letI := fiberAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    ContMDiff (𝓡 (k + 1)) ((𝓘(ℝ, ℝ)).prod (𝓡 k)) ∞ (seamBackward d) := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  have hs : ContMDiff (𝓡 (k + 1)) ((𝓘(ℝ, ℝ)).prod (𝓡 m)) ∞
      (fun p : seamBand d ↦ p.val.val) :=
    (regularFiber_contMDiff_subtype_val (map d) (contMDiff_map d) b (regular_map d)
      (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)).comp contMDiff_subtype_val
  have ht : ContMDiff (𝓡 (k + 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : seamBand d ↦ (seamBackward d p).1) :=
    (ContMDiff.subtypeVal_comp_iff (seamCollarTimes d) _).mp (contMDiff_fst.comp hs)
  have hx : ContMDiff (𝓡 (k + 1)) (𝓡 k) ∞
      (fun p : seamBand d ↦ (seamBackward d p).2) :=
    (regularFiber_contMDiff_iff_ambient d.leftMap d.smooth_left b d.regular_left k
      (by simpa using hd) _).mpr (contMDiff_snd.comp hs)
  exact ht.prodMk hx

def seamDiffeomorph : letI := fiberAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (seamCollarTimes d × EndpointFiber d) ≃ₘ⟮(𝓘(ℝ, ℝ)).prod (𝓡 k), 𝓡 (k + 1)⟯
      seamBand d := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  exact
    { toFun := seamForward d
      invFun := seamBackward d
      left_inv := seamBackward_forward d
      right_inv := seamForward_backward d
      contMDiff_toFun := contMDiff_seamForward d k hd
      contMDiff_invFun := contMDiff_seamBackward d k hd }

theorem seamDiffeomorph_point (p : seamCollarTimes d × EndpointFiber d) :
    letI := fiberAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (seamDiffeomorph d k hd p).val.val = (p.1.val, p.2.val) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
