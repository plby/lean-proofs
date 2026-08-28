import Wikipedia.HopfProblem.StandardSixSphereCircleModelBoundary

/-!
# Coordinates for the actual equatorial tube in the standard six-sphere

The normal coordinate is the original last four Euclidean coordinates.
The base coordinate is the unit direction of the original first three.
No topology or charted space is replaced.
-/

noncomputable section

namespace Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube

def normalBall (r : ℝ) : TopologicalSpace.Opens Normal where
  carrier := Metric.ball 0 r
  is_open' := Metric.isOpen_ball

def openTube (r : ℝ) : TopologicalSpace.Opens Sphere where
  carrier := {p | ‖normal p.val‖ < r}
  is_open' := isOpen_lt (continuous_normal.comp continuous_subtype_val).norm continuous_const

def closedTube (r : ℝ) : Set Sphere := {p | ‖normal p.val‖ ≤ r}

theorem isClosed_closedTube (r : ℝ) : IsClosed (closedTube r) :=
  isClosed_le (continuous_normal.comp continuous_subtype_val).norm continuous_const

@[simp] theorem mem_normalBall (r : ℝ) (y : Normal) :
    y ∈ normalBall r ↔ ‖y‖ < r := by
  simp only [normalBall, TopologicalSpace.Opens.mem_mk, Metric.mem_ball, dist_zero_right]

@[simp] theorem mem_openTube (r : ℝ) (p : Sphere) :
    p ∈ openTube r ↔ ‖normal p.val‖ < r := Iff.rfl

@[simp] theorem mem_closedTube (r : ℝ) (p : Sphere) :
    p ∈ closedTube r ↔ ‖normal p.val‖ ≤ r := Iff.rfl

def baseFactor (y : Normal) : ℝ := Real.sqrt (1 - ‖y‖ ^ 2)

theorem baseFactor_nonneg (y : Normal) : 0 ≤ baseFactor y := Real.sqrt_nonneg _

theorem baseFactor_pos {y : Normal} (hy : ‖y‖ < 1) : 0 < baseFactor y := by
  apply Real.sqrt_pos.mpr
  nlinarith [norm_nonneg y]

theorem baseFactor_sq {y : Normal} (hy : ‖y‖ ≤ 1) :
    baseFactor y ^ 2 = 1 - ‖y‖ ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [norm_nonneg y]

theorem continuous_baseFactor : Continuous baseFactor :=
  Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2))

/-- The exact formula `(b,y) ↦ (sqrt (1-‖y‖²) b,y)` in standard Euclidean space. -/
def ambient (b : BaseSphere) (y : Normal) : Ambient := join (baseFactor y • b.val) y

@[simp] theorem base_ambient (b : BaseSphere) (y : Normal) :
    base (ambient b y) = baseFactor y • b.val := base_join _ _

@[simp] theorem normal_ambient (b : BaseSphere) (y : Normal) : normal (ambient b y) = y :=
  normal_join _ _

theorem norm_base_ambient (b : BaseSphere) (y : Normal) :
    ‖base (ambient b y)‖ = baseFactor y := by
  rw [base_ambient, norm_smul, Real.norm_eq_abs, abs_of_nonneg (baseFactor_nonneg y),
    baseSphere_norm, mul_one]

theorem ambient_mem_sphere (b : BaseSphere) (y : Normal) (hy : ‖y‖ ≤ 1) :
    ambient b y ∈ Sphere := by
  apply mem_sphere_of_norm_sq
  rw [norm_sq_eq, norm_base_ambient, normal_ambient, baseFactor_sq hy]
  ring

def point (b : BaseSphere) (y : Normal) (hy : ‖y‖ ≤ 1) : Sphere :=
  ⟨ambient b y, ambient_mem_sphere b y hy⟩

@[simp] theorem point_val (b : BaseSphere) (y : Normal) (hy : ‖y‖ ≤ 1) :
    (point b y hy).val = ambient b y := rfl

@[simp] theorem normal_point (b : BaseSphere) (y : Normal) (hy : ‖y‖ ≤ 1) :
    normal (point b y hy).val = y := normal_ambient b y

theorem base_norm_pos (p : Sphere) (hp : ‖normal p.val‖ < 1) :
    0 < ‖base p.val‖ := by
  have h := sphere_norm_sq p
  nlinarith [norm_nonneg (base p.val), norm_nonneg (normal p.val)]

theorem base_ne_zero (p : Sphere) (hp : ‖normal p.val‖ < 1) : base p.val ≠ 0 :=
  norm_pos_iff.mp (base_norm_pos p hp)

theorem base_norm_eq_baseFactor (p : Sphere) (hp : ‖normal p.val‖ ≤ 1) :
    ‖base p.val‖ = baseFactor (normal p.val) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (baseFactor_nonneg _)).mp
  rw [baseFactor_sq hp]
  linarith [sphere_norm_sq p]

theorem normalizedBase_mem_sphere (p : Sphere) (hp : ‖normal p.val‖ < 1) :
    ‖base p.val‖⁻¹ • base p.val ∈ BaseSphere := by
  simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_nonneg (norm_nonneg (base p.val))]
  exact inv_mul_cancel₀ (base_norm_pos p hp).ne'

def normalizedBase (p : Sphere) (hp : ‖normal p.val‖ < 1) : BaseSphere :=
  ⟨‖base p.val‖⁻¹ • base p.val, normalizedBase_mem_sphere p hp⟩

@[simp] theorem normalizedBase_val (p : Sphere) (hp : ‖normal p.val‖ < 1) :
    (normalizedBase p hp).val = ‖base p.val‖⁻¹ • base p.val := rfl

theorem normalizedBase_point (b : BaseSphere) (y : Normal) (hy : ‖y‖ ≤ 1)
    (hp : ‖normal (point b y hy).val‖ < 1) : normalizedBase (point b y hy) hp = b := by
  apply Subtype.ext
  change ‖base (ambient b y)‖⁻¹ • base (ambient b y) = b.val
  rw [norm_base_ambient, base_ambient]
  have hpos : 0 < baseFactor y := baseFactor_pos (by simpa only [normal_point] using hp)
  exact inv_smul_smul₀ hpos.ne' b.val

theorem ambient_normalizedBase (p : Sphere) (hp : ‖normal p.val‖ < 1) :
    ambient (normalizedBase p hp) (normal p.val) = p.val := by
  rw [ambient, normalizedBase_val, ← base_norm_eq_baseFactor p hp.le,
    smul_inv_smul₀ (base_norm_pos p hp).ne', join_base_normal]

theorem point_normalizedBase (p : Sphere) (hp : ‖normal p.val‖ < 1) :
    point (normalizedBase p hp) (normal p.val) hp.le = p :=
  Subtype.ext (ambient_normalizedBase p hp)

theorem continuous_ambient : Continuous (fun q : BaseSphere × Normal => ambient q.1 q.2) := by
  have hb : Continuous (fun q : BaseSphere × Normal => q.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hf : Continuous (fun q : BaseSphere × Normal => baseFactor q.2) :=
    continuous_baseFactor.comp continuous_snd
  have hp : Continuous (fun q : BaseSphere × Normal => (baseFactor q.2 • q.1.val, q.2)) :=
    (hf.smul hb).prodMk continuous_snd
  exact Continuous.comp (g := fun z : Base × Normal => join z.1 z.2)
    (f := fun q : BaseSphere × Normal => (baseFactor q.2 • q.1.val, q.2)) continuous_join hp

theorem continuous_normalizedBase {X : Type*} [TopologicalSpace X]
    (f : X → Sphere) (hf : Continuous f) (h : ∀ x, ‖normal (f x).val‖ < 1) :
    Continuous (fun x => normalizedBase (f x) (h x)) := by
  have hb : Continuous (fun x => base (f x).val) :=
    continuous_base.comp (continuous_subtype_val.comp hf)
  have hs : Continuous (fun x => ‖base (f x).val‖⁻¹) :=
    hb.norm.inv₀ (fun x => (base_norm_pos (f x) (h x)).ne')
  exact (hs.smul hb).subtype_mk _

end Wikipedia.HopfProblem.StandardSixSphereCircleModel.Tube
