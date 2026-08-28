import Wikipedia.HopfProblem.DegreeCollapseOrthogonalHopfMap

/-!
# The two sphere maps in orthogonal Hopf stabilization

Retain the original orthogonal family and separate an added identity
block. Its Hopf formula and the radial suspension of the original Hopf
formula both define continuous maps on the same actual Hilbert-sum
sphere. No comparison of their homotopy classes is assumed here.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere GLOrthonormalization Filter

namespace Wikipedia.HopfProblem.DegreeCollapse.HopfBlockGeometry

open OrthogonalHopfMap

variable {P E G : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {n : ℕ}

abbrev Triple (E B G : Type*) := WithLp 2 (E × WithLp 2 (B × G))

def head (x : Triple E (Vector n) G) : WithLp 2 (E × Vector n) :=
  WithLp.toLp 2 (x.fst, x.snd.fst)

omit [NormedSpace ℝ E] [NormedSpace ℝ G] in
theorem continuous_head : Continuous (head : Triple E (Vector n) G → _) :=
  (WithLp.prod_continuous_toLp 2 E (Vector n)).comp
    ((WithLp.continuous_fst 2 E _).prodMk
      ((WithLp.continuous_fst 2 (Vector n) G).comp (WithLp.continuous_snd 2 E _)))

theorem norm_vector (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : WithLp 2 (E × Vector n)) : ‖vector f p x‖ = ‖x‖ ^ 2 := by
  have h := vector_norm_sq f p x
  rw [← WithLp.prod_norm_sq_eq_of_L2] at h
  nlinarith [norm_nonneg (vector f p x), sq_nonneg ‖x‖]

def suspendedHead (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : WithLp 2 (E × Vector n)) : WithLp 2 (ℝ × Vector n) :=
  ‖x‖⁻¹ • vector f p x

theorem suspendedHead_norm (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : WithLp 2 (E × Vector n)) : ‖suspendedHead f p x‖ = ‖x‖ := by
  rw [suspendedHead, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), norm_vector]
  by_cases hx : ‖x‖ = 0
  · rw [hx, inv_zero, zero_mul]
  · rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]

theorem suspendedHead_zero (f : C(P × UnitSphere E, OrthogonalOperators n)) (p : P) :
    suspendedHead f p 0 = 0 := by
  simp only [suspendedHead, norm_zero, inv_zero, zero_smul]

theorem continuous_suspendedHead (f : C(P × UnitSphere E, OrthogonalOperators n)) :
    Continuous (fun z : P × WithLp 2 (E × Vector n) ↦ suspendedHead f z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z.2 = 0
  · change Tendsto _ (𝓝 z) (𝓝 (suspendedHead f z.1 z.2))
    rw [hz, suspendedHead_zero]
    apply squeeze_zero_norm (fun w : P × WithLp 2 (E × Vector n) ↦
      (suspendedHead_norm f w.1 w.2).le)
    have ht := (continuous_snd.norm :
      Continuous (fun w : P × WithLp 2 (E × Vector n) ↦ ‖w.2‖)).continuousAt (x := z)
    change Tendsto (fun w : P × WithLp 2 (E × Vector n) ↦ ‖w.2‖)
      (𝓝 z) (𝓝 ‖z.2‖) at ht
    simpa only [hz, norm_zero] using ht
  · exact ((continuous_snd.continuousAt.norm).inv₀ (norm_ne_zero_iff.mpr hz)).smul
      (continuous_vector f).continuousAt

def blockVector (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : Triple E (Vector n) G) : Triple ℝ (Vector n) G :=
  WithLp.toLp 2 (‖x.fst‖ ^ 2 - ‖x.snd.fst‖ ^ 2 - ‖x.snd.snd‖ ^ 2,
    WithLp.toLp 2 ((2 : ℝ) • RadialSphereAction.value (action f) p x.fst x.snd.fst,
      (2 * ‖x.fst‖) • x.snd.snd))

theorem blockVector_norm_sq (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : Triple E (Vector n) G) :
    ‖blockVector f p x‖ ^ 2 = ‖x‖ ^ 4 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖‖x.fst‖ ^ 2 - ‖x.snd.fst‖ ^ 2 - ‖x.snd.snd‖ ^ 2‖ ^ 2 +
    ‖WithLp.toLp 2 ((2 : ℝ) • RadialSphereAction.value (action f) p x.fst x.snd.fst,
      (2 * ‖x.fst‖) • x.snd.snd)‖ ^ 2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖‖x.fst‖ ^ 2 - ‖x.snd.fst‖ ^ 2 - ‖x.snd.snd‖ ^ 2‖ ^ 2 +
    (‖(2 : ℝ) • RadialSphereAction.value (action f) p x.fst x.snd.fst‖ ^ 2 +
      ‖(2 * ‖x.fst‖) • x.snd.snd‖ ^ 2) = _
  have hx := WithLp.prod_norm_sq_eq_of_L2 x
  rw [WithLp.prod_norm_sq_eq_of_L2 x.snd] at hx
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    RadialSphereAction.value_norm (action f) (action_norm f)]
  calc
    _ = (‖x.fst‖ ^ 2 + (‖x.snd.fst‖ ^ 2 + ‖x.snd.snd‖ ^ 2)) ^ 2 := by ring
    _ = ‖x‖ ^ 4 := by rw [← hx]; ring

theorem continuous_blockVector (f : C(P × UnitSphere E, OrthogonalOperators n)) :
    Continuous (fun z : P × Triple E (Vector n) G ↦ blockVector f z.1 z.2) := by
  have ha : Continuous (fun z : P × Triple E (Vector n) G ↦ z.2.fst) :=
    (WithLp.continuous_fst 2 E _).comp continuous_snd
  have hb : Continuous (fun z : P × Triple E (Vector n) G ↦ z.2.snd.fst) :=
    (WithLp.continuous_fst 2 (Vector n) G).comp
      ((WithLp.continuous_snd 2 E _).comp continuous_snd)
  have hc : Continuous (fun z : P × Triple E (Vector n) G ↦ z.2.snd.snd) :=
    (WithLp.continuous_snd 2 (Vector n) G).comp
      ((WithLp.continuous_snd 2 E _).comp continuous_snd)
  have hr := (RadialSphereAction.continuous_value (action f) (action_norm f)
    (continuous_action f)).comp (continuous_fst.prodMk (ha.prodMk hb))
  have htwo : Continuous (fun _ : P × Triple E (Vector n) G ↦ (2 : ℝ)) := continuous_const
  exact (WithLp.prod_continuous_toLp 2 ℝ _).comp
    ((((ha.norm.pow 2).sub (hb.norm.pow 2)).sub (hc.norm.pow 2)).prodMk
      ((WithLp.prod_continuous_toLp 2 (Vector n) G).comp
        ((htwo.smul hr).prodMk ((htwo.mul ha.norm).smul hc))))

def suspendedVector (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : Triple E (Vector n) G) : Triple ℝ (Vector n) G :=
  WithLp.toLp 2 ((suspendedHead f p (head x)).fst,
    WithLp.toLp 2 ((suspendedHead f p (head x)).snd, x.snd.snd))

omit [NormedSpace ℝ G] in
theorem suspendedVector_norm_sq (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : Triple E (Vector n) G) : ‖suspendedVector f p x‖ ^ 2 = ‖x‖ ^ 2 := by
  have ht := WithLp.prod_norm_sq_eq_of_L2 (suspendedVector f p x)
  rw [WithLp.prod_norm_sq_eq_of_L2 (suspendedVector f p x).snd] at ht
  have hh := WithLp.prod_norm_sq_eq_of_L2 (suspendedHead f p (head x))
  rw [suspendedHead_norm, WithLp.prod_norm_sq_eq_of_L2 (head x)] at hh
  have hx := WithLp.prod_norm_sq_eq_of_L2 x
  rw [WithLp.prod_norm_sq_eq_of_L2 x.snd] at hx
  change ‖suspendedVector f p x‖ ^ 2 = ‖(suspendedHead f p (head x)).fst‖ ^ 2 +
    (‖(suspendedHead f p (head x)).snd‖ ^ 2 + ‖x.snd.snd‖ ^ 2) at ht
  simp only [Real.norm_eq_abs, sq_abs] at ht
  change ‖x.fst‖ ^ 2 + ‖x.snd.fst‖ ^ 2 =
    ‖(suspendedHead f p (head x)).fst‖ ^ 2 + ‖(suspendedHead f p (head x)).snd‖ ^ 2 at hh
  simp only [Real.norm_eq_abs, sq_abs] at hh
  linarith

omit [NormedSpace ℝ G] in
theorem continuous_suspendedVector (f : C(P × UnitSphere E, OrthogonalOperators n)) :
    Continuous (fun z : P × Triple E (Vector n) G ↦ suspendedVector f z.1 z.2) := by
  have hp : Continuous (fun z : P × Triple E (Vector n) G ↦ z.1) := continuous_fst
  have hx : Continuous (fun z : P × Triple E (Vector n) G ↦ z.2) := continuous_snd
  have hhead : Continuous (fun z : P × Triple E (Vector n) G ↦ head z.2) :=
    (continuous_head (E := E) (G := G) (n := n)).comp hx
  have hpair : Continuous (fun z : P × Triple E (Vector n) G ↦ (z.1, head z.2)) :=
    hp.prodMk hhead
  have hh : Continuous (fun z : P × Triple E (Vector n) G ↦ suspendedHead f z.1 (head z.2)) :=
    Continuous.comp
      (g := fun z : P × WithLp 2 (E × Vector n) ↦ suspendedHead f z.1 z.2)
      (f := fun z : P × Triple E (Vector n) G ↦ (z.1, head z.2))
      (continuous_suspendedHead (P := P) (E := E) (n := n) f) hpair
  have hc : Continuous (fun z : P × Triple E (Vector n) G ↦ z.2.snd.snd) :=
    (WithLp.continuous_snd 2 (Vector n) G).comp
      ((WithLp.continuous_snd 2 E _).comp continuous_snd)
  exact (WithLp.prod_continuous_toLp 2 ℝ _).comp
    (((WithLp.continuous_fst 2 ℝ (Vector n)).comp hh).prodMk
      ((WithLp.prod_continuous_toLp 2 (Vector n) G).comp
        (((WithLp.continuous_snd 2 ℝ (Vector n)).comp hh).prodMk hc)))

theorem blockVector_mem_sphere (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : UnitSphere (Triple E (Vector n) G)) :
    blockVector f p x.val ∈ UnitSphere (Triple ℝ (Vector n) G) := by
  rw [mem_sphere_zero_iff_norm]
  have h := blockVector_norm_sq f p x.val
  rw [mem_sphere_zero_iff_norm.mp x.property, one_pow] at h
  nlinarith [norm_nonneg (blockVector f p x.val)]

def blockMap (f : C(P × UnitSphere E, OrthogonalOperators n)) :
    C(P × UnitSphere (Triple E (Vector n) G), UnitSphere (Triple ℝ (Vector n) G)) :=
  ⟨fun z ↦ ⟨blockVector f z.1 z.2.val, blockVector_mem_sphere f z.1 z.2⟩,
    ((continuous_blockVector f).comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

omit [NormedSpace ℝ G] in
theorem suspendedVector_mem_sphere (f : C(P × UnitSphere E, OrthogonalOperators n))
    (p : P) (x : UnitSphere (Triple E (Vector n) G)) :
    suspendedVector f p x.val ∈ UnitSphere (Triple ℝ (Vector n) G) := by
  rw [mem_sphere_zero_iff_norm]
  have h := suspendedVector_norm_sq f p x.val
  rw [mem_sphere_zero_iff_norm.mp x.property, one_pow] at h
  nlinarith [norm_nonneg (suspendedVector f p x.val)]

def suspendedMap (f : C(P × UnitSphere E, OrthogonalOperators n)) :
    C(P × UnitSphere (Triple E (Vector n) G), UnitSphere (Triple ℝ (Vector n) G)) :=
  ⟨fun z ↦ ⟨suspendedVector f z.1 z.2.val, suspendedVector_mem_sphere f z.1 z.2⟩,
    ((continuous_suspendedVector f).comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

end Wikipedia.HopfProblem.DegreeCollapse.HopfBlockGeometry
