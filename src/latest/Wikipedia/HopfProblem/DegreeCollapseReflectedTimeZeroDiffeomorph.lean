import Wikipedia.HopfProblem.DegreeCollapseReflectedHalfAtlas

/-!
# The native time-zero fiber is the original endpoint regular fiber

The literal seam map and spatial projection are inverse. Their smoothness
is checked using the regular-fiber criteria at both levels of inclusion,
so the original endpoint atlas is preserved rather than transported.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def timeZeroMap : C(Fiber d, ℝ) := ⟨time d, continuous_time d⟩

abbrev TimeZero := {p : Fiber d // time d p = 0}

def endpointToTimeZero (x : EndpointFiber d) : TimeZero d :=
  ⟨seamCollarPoint d 0 (zero_mem_seamCollarTimes d) x, rfl⟩

def timeZeroToEndpoint (p : TimeZero d) : EndpointFiber d :=
  ⟨p.val.val.2, by
    have ht : p.val.val.1 ∈ seamCollarTimes d := by
      change time d p.val ∈ seamCollarTimes d
      rw [p.property]
      exact zero_mem_seamCollarTimes d
    exact (map_on_seamCollar d p.val.val.1 ht p.val.val.2).symm.trans p.val.property⟩

theorem timeZeroToEndpoint_forward (x : EndpointFiber d) :
    timeZeroToEndpoint d (endpointToTimeZero d x) = x := rfl

theorem endpointToTimeZero_backward (p : TimeZero d) :
    endpointToTimeZero d (timeZeroToEndpoint d p) = p :=
  Subtype.ext (Subtype.ext (Prod.ext p.property.symm rfl))

variable (k : ℕ) (hd : m = n + k)

@[instance_reducible]
def timeZeroAtlas : letI := fiberAtlas d k hd;
    ChartedSpace (Vector k) (TimeZero d) := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  exact regularFiberAtlas (timeZeroMap d) (contMDiff_time d k hd) 0
    (regular_time_zero d k hd) k (by simp [Nat.add_comm])

theorem contMDiff_endpointToTimeZero : letI := fiberAtlas d k hd;
    letI := timeZeroAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    ContMDiff (𝓡 k) (𝓡 k) ∞ (endpointToTimeZero d) := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  let := timeZeroAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  apply (regularFiber_contMDiff_iff_ambient (timeZeroMap d) (contMDiff_time d k hd) 0
    (regular_time_zero d k hd) k (by simp [Nat.add_comm]) _).mpr
  apply (regularFiber_contMDiff_iff_ambient (map d) (contMDiff_map d) b (regular_map d)
    (k + 1) (CylinderFiberNormalFrame.dimension_eq hd) _).mpr
  exact contMDiff_const.prodMk (regularFiber_contMDiff_subtype_val d.leftMap d.smooth_left b
    d.regular_left k (by simpa using hd))

theorem contMDiff_timeZeroToEndpoint : letI := fiberAtlas d k hd;
    letI := timeZeroAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    ContMDiff (𝓡 k) (𝓡 k) ∞ (timeZeroToEndpoint d) := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  let := timeZeroAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  apply (regularFiber_contMDiff_iff_ambient d.leftMap d.smooth_left b d.regular_left k
    (by simpa using hd) (timeZeroToEndpoint d)).mpr
  have hz : ContMDiff (𝓡 k) (𝓡 (k + 1)) ∞ (Subtype.val : TimeZero d → Fiber d) :=
    regularFiber_contMDiff_subtype_val (timeZeroMap d) (contMDiff_time d k hd) 0
      (regular_time_zero d k hd) k (by simp [Nat.add_comm])
  have hc : ContMDiff (𝓡 (k + 1)) ((𝓘(ℝ, ℝ)).prod (𝓡 m)) ∞
      (Subtype.val : Fiber d → ℝ × Sphere m) :=
    regularFiber_contMDiff_subtype_val (map d) (contMDiff_map d) b (regular_map d)
      (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  exact contMDiff_snd.comp (hc.comp hz)

def timeZeroDiffeomorph : letI := fiberAtlas d k hd;
    letI := timeZeroAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    EndpointFiber d ≃ₘ⟮𝓡 k, 𝓡 k⟯ TimeZero d := by
  let := fiberAtlas d k hd
  let := timeZeroAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  exact
    { toFun := endpointToTimeZero d
      invFun := timeZeroToEndpoint d
      left_inv := timeZeroToEndpoint_forward d
      right_inv := endpointToTimeZero_backward d
      contMDiff_toFun := contMDiff_endpointToTimeZero d k hd
      contMDiff_invFun := contMDiff_timeZeroToEndpoint d k hd }

theorem timeZeroDiffeomorph_point (x : EndpointFiber d) : letI := fiberAtlas d k hd;
    letI := timeZeroAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (timeZeroDiffeomorph d k hd x).val.val = (0, x.val) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
