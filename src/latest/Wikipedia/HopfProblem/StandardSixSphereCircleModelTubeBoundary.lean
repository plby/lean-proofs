import Wikipedia.HopfProblem.StandardSixSphereCircleModelTubeHomeomorph

/-!
# The closed tube, its literal radius boundary, and the restriction square

The radius boundary is a subset of the original standard sphere.  Its
parametrization agrees with the previously fixed `boundaryPoint` exactly.
-/

noncomputable section

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube

def closedMap (r : ℝ) (hr1 : r < 1) (q : ClosedDomain r) : Sphere :=
  (closedHomeomorph r hr1 q).val

theorem isClosedEmbedding_closedMap (r : ℝ) (hr1 : r < 1) :
    Topology.IsClosedEmbedding (closedMap r hr1) :=
  (isClosed_closedTube r).isClosedEmbedding_subtypeVal.comp
    (closedHomeomorph r hr1).isClosedEmbedding

theorem range_closedMap (r : ℝ) (hr1 : r < 1) : Set.range (closedMap r hr1) = closedTube r := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact (closedHomeomorph r hr1 q).property
  · intro hp
    exact ⟨(closedHomeomorph r hr1).symm ⟨p, hp⟩,
      congrArg Subtype.val ((closedHomeomorph r hr1).apply_symm_apply ⟨p, hp⟩)⟩

def closedToOpenDomain (r R : ℝ) (hrR : r < R) (q : ClosedDomain r) : OpenDomain R :=
  (q.1, ⟨q.2.val, (mem_normalBall R _).mpr ((closedBall_norm_le r q.2).trans_lt hrR)⟩)

def closedTubeInOpen (r R : ℝ) (hrR : r < R) (p : ↥(closedTube r)) : ↥(openTube R) :=
  ⟨p.val, p.property.trans_lt hrR⟩

/-- Both tube maps use the same formula on a smaller closed disk. -/
theorem openHomeomorph_closedToOpenDomain (r R : ℝ) (hrR : r < R)
    (hR1 : R ≤ 1) (hr1 : r < 1) (q : ClosedDomain r) :
    openHomeomorph R hR1 (closedToOpenDomain r R hrR q) =
      closedTubeInOpen r R hrR (closedHomeomorph r hr1 q) := rfl

def radiusLevel (r : ℝ) : Set Sphere := {p | ‖normal p.val‖ = r}

theorem isClosed_radiusLevel (r : ℝ) : IsClosed (radiusLevel r) :=
  isClosed_eq (continuous_normal.comp continuous_subtype_val).norm continuous_const

theorem baseFactor_normal_of_level (r : ℝ) (p : ↥(radiusLevel r)) :
    baseFactor (normal p.val.val) = boundaryBaseRadius r := by
  change Real.sqrt (1 - ‖normal p.val.val‖ ^ 2) = Real.sqrt (1 - r ^ 2)
  rw [show ‖normal p.val.val‖ = r from p.property]

def boundaryForward (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) : ↥(radiusLevel r) :=
  ⟨(boundaryPoint r hr hr1 q).val, normalRadius_boundaryPoint r hr hr1 q⟩

theorem scaled_normal_mem_sphere (r : ℝ) (hr : 0 < r) (p : ↥(radiusLevel r)) :
    r⁻¹ • normal p.val.val ∈ NormalSphere := by
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hr, show ‖normal p.val.val‖ = r from p.property, inv_mul_cancel₀ hr.ne']

def boundaryInverse (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (p : ↥(radiusLevel r)) : BaseSphere × NormalSphere :=
  (normalizedBase p.val ((show ‖normal p.val.val‖ = r from p.property).trans_lt hr1),
    ⟨r⁻¹ • normal p.val.val, scaled_normal_mem_sphere r hr p⟩)

theorem boundaryInverse_boundaryForward (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) :
    boundaryInverse r hr hr1 (boundaryForward r hr hr1 q) = q := by
  apply Prod.ext
  · apply Subtype.ext
    change ‖base (boundaryAmbient r q)‖⁻¹ • base (boundaryAmbient r q) = q.1.val
    rw [base_boundaryAmbient, norm_smul, Real.norm_eq_abs,
      abs_of_pos (boundaryBaseRadius_pos hr hr1), baseSphere_norm, mul_one,
      inv_smul_smul₀ (boundaryBaseRadius_pos hr hr1).ne']
  · apply Subtype.ext
    change r⁻¹ • normal (boundaryAmbient r q) = q.2.val
    rw [normal_boundaryAmbient, inv_smul_smul₀ hr.ne']

theorem boundaryForward_boundaryInverse (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (p : ↥(radiusLevel r)) :
    boundaryForward r hr hr1 (boundaryInverse r hr hr1 p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  have hp : ‖normal p.val.val‖ < 1 :=
    (show ‖normal p.val.val‖ = r from p.property).trans_lt hr1
  have hb : ‖base p.val.val‖ = boundaryBaseRadius r :=
    (base_norm_eq_baseFactor p.val hp.le).trans (baseFactor_normal_of_level r p)
  change join (boundaryBaseRadius r • (‖base p.val.val‖⁻¹ • base p.val.val))
    (r • (r⁻¹ • normal p.val.val)) = p.val.val
  rw [← hb, smul_inv_smul₀ (base_norm_pos p.val hp).ne', smul_inv_smul₀ hr.ne',
    join_base_normal]

theorem continuous_boundaryForward (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Continuous (boundaryForward r hr hr1) :=
  (continuous_subtype_val.comp (continuous_boundaryPoint r hr hr1)).subtype_mk _

theorem continuous_boundaryInverse (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Continuous (boundaryInverse r hr hr1) := by
  have hb : Continuous (fun p : ↥(radiusLevel r) => normalizedBase p.val
      ((show ‖normal p.val.val‖ = r from p.property).trans_lt hr1)) :=
    continuous_normalizedBase Subtype.val continuous_subtype_val _
  have hn : Continuous (fun p : ↥(radiusLevel r) => normal p.val.val) :=
    continuous_normal.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hs : Continuous (fun p : ↥(radiusLevel r) => r⁻¹ • normal p.val.val) :=
    (continuous_const : Continuous (fun _ : ↥(radiusLevel r) => r⁻¹)).smul hn
  exact hb.prodMk (hs.subtype_mk _)

/-- The entire literal radius boundary, with the original `S² × S³` marking. -/
def boundaryHomeomorph (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    BaseSphere × NormalSphere ≃ₜ ↥(radiusLevel r) where
  toFun := boundaryForward r hr hr1
  invFun := boundaryInverse r hr hr1
  left_inv := boundaryInverse_boundaryForward r hr hr1
  right_inv := boundaryForward_boundaryInverse r hr hr1
  continuous_toFun := continuous_boundaryForward r hr hr1
  continuous_invFun := continuous_boundaryInverse r hr hr1

@[simp] theorem boundaryHomeomorph_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) :
    (boundaryHomeomorph r hr hr1 q).val = (boundaryPoint r hr hr1 q).val := rfl

@[simp] theorem boundaryHomeomorph_val_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) :
    (boundaryHomeomorph r hr hr1 q).val.val =
      join (boundaryBaseRadius r • q.1.val) (r • q.2.val) := rfl

@[simp] theorem boundaryHomeomorph_symm_snd_val (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (p : ↥(radiusLevel r)) :
    ((boundaryHomeomorph r hr hr1).symm p).2.val = r⁻¹ • normal p.val.val := rfl

theorem isClosedEmbedding_boundaryMap (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Topology.IsClosedEmbedding (fun q => (boundaryHomeomorph r hr hr1 q).val) :=
  (isClosed_radiusLevel r).isClosedEmbedding_subtypeVal.comp
    (boundaryHomeomorph r hr hr1).isClosedEmbedding

theorem norm_smul_normalSphere {r : ℝ} (hr : 0 ≤ r) (u : NormalSphere) :
    ‖r • u.val‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, normalSphere_norm, mul_one]

def boundaryIntoClosed (r : ℝ) (hr : 0 < r) (q : BaseSphere × NormalSphere) : ClosedDomain r :=
  (q.1, ⟨r • q.2.val, by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul_normalSphere hr.le]
      using (le_refl r)⟩)

def boundaryLevelIntoClosed (r : ℝ) (p : ↥(radiusLevel r)) : ↥(closedTube r) :=
  ⟨p.val, (show ‖normal p.val.val‖ = r from p.property).le⟩

theorem baseFactor_smul_normalSphere {r : ℝ} (hr : 0 ≤ r) (u : NormalSphere) :
    baseFactor (r • u.val) = boundaryBaseRadius r := by
  unfold baseFactor boundaryBaseRadius
  rw [norm_smul_normalSphere hr u]

/-- The closed-tube parametrization restricts to the fixed boundary marking exactly. -/
theorem closedHomeomorph_boundaryIntoClosed (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (q : BaseSphere × NormalSphere) :
    closedHomeomorph r hr1 (boundaryIntoClosed r hr q) =
      boundaryLevelIntoClosed r (boundaryHomeomorph r hr hr1 q) := by
  apply Subtype.ext
  apply Subtype.ext
  change ambient q.1 (r • q.2.val) =
    join (boundaryBaseRadius r • q.1.val) (r • q.2.val)
  rw [ambient, baseFactor_smul_normalSphere hr.le]

end Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube
