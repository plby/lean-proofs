import Wikipedia.HopfProblem.OrbitPairSpherePairedGeodesic

/-!
# Smooth squared-angle energy on an actual neighborhood of the sphere diagonal

The squared length of the recovered tangent vector is a smooth ambient
extension of squared spherical angle. Rotation invariance proves this
identity for both variable unit endpoints. Consequently the literal
arccos-squared formula is smooth in the sphere's native product atlas on
an open neighborhood of the entire diagonal, despite arccos itself being
singular there. This is the local energy used for finite sphere polygons.
-/

noncomputable section

open scoped ContDiff Manifold
open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePairedGeodesic

open NoExoticSixSphere GLOrthonormalization SphereTangentExponential SphereGeodesicTransport

variable {n : ℕ} {x : Vector n} {ε : ℝ} (d : LocalLogData x ε)

def cost (p : Vector n × Vector n) : ℝ := ‖d.log (backward x p.1 p.2)‖ ^ 2

theorem contDiffOn_cost : ContDiffOn ℝ ∞ (cost d) (domain d) := by
  intro p hp
  have hr : ContDiffAt ℝ ∞ (fun q : Vector n × Vector n => backward x q.1 q.2) p :=
    contDiffAt_backward contDiffAt_const contDiffAt_fst contDiffAt_snd hp.1 hp.2.1
  have hl : ContDiffAt ℝ ∞ (fun q : Vector n × Vector n => d.log (backward x q.1 q.2)) p :=
    ContDiffAt.comp (g := d.log) (f := fun q : Vector n × Vector n => backward x q.1 q.2)
      p (d.contDiffOn_log.contDiffAt (d.isOpen_domain.mem_nhds hp.2.2)) hr
  exact (hl.norm_sq (𝕜 := ℝ)).contDiffWithinAt

theorem cost_nonneg (p : Vector n × Vector n) : 0 ≤ cost d p := sq_nonneg _

theorem cost_diagonal (hx : ‖x‖ = 1) {a : Vector n} (ha : ‖a‖ = 1) : cost d (a, a) = 0 := by
  rw [cost, backward_base hx ha, d.log_base, norm_zero, zero_pow (by decide)]

theorem energy_segment_eq_cost (hx : ‖x‖ = 1) (a b : Vector n) (l u : ℝ) :
    SpherePathEnergy.energy (segment d a b l u) l u = cost d (a, b) / (u - l) := by
  rw [energy_segment]
  exact SphereTangentExponential.energy_segment hx _ l u

theorem cost_eq_angle (hx : ‖x‖ = 1) (hε : ε ≤ Real.pi / 2)
    {a b : Vector n} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hp : (a, b) ∈ domain d) :
    cost d (a, b) = Real.arccos (inner ℝ a b) ^ 2 := by
  have hv := (d.norm_log_lt hp.2.2).le.trans hε
  have h := endpoint_angle_sq hx (d.log (backward x a b)) hv
  rw [d.curve_log hx ((norm_backward x a b).trans hb) hp.2.2] at h
  have hi := (localRotationEquiv x a).inner_map_map x (backward x a b)
  change inner ℝ (forward x a x) (forward x a (backward x a b)) =
    inner ℝ x (backward x a b) at hi
  rw [forward_base hx ha, forward_backward] at hi
  rw [← hi] at h
  exact h.symm

section NativeSphere

variable {m : ℕ} {a : Vector (m + 1)} {δ : ℝ} (D : LocalLogData a δ)

def sphereCost (m : ℕ) (p : Sphere m × Sphere m) : ℝ :=
  Real.arccos (inner ℝ p.1.val p.2.val) ^ 2

theorem continuous_sphereCost (m : ℕ) : Continuous (sphereCost m) := by
  unfold sphereCost
  fun_prop

def sphereDomain : Set (Sphere m × Sphere m) :=
  {p | (p.1.val, p.2.val) ∈ domain D}

theorem isOpen_sphereDomain : IsOpen (sphereDomain D) :=
  (isOpen_domain D).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

theorem contMDiffOn_sphereCost (ha : ‖a‖ = 1) (hδ : δ ≤ Real.pi / 2) :
    ContMDiffOn ((𝓡 m).prod (𝓡 m)) 𝓘(ℝ, ℝ) ∞ (sphereCost m) (sphereDomain D) := by
  letI : Fact (Module.finrank ℝ (Vector (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hcoe : ContMDiff (𝓡 m) 𝓘(ℝ, Vector (m + 1)) ∞
      (fun p : Sphere m => p.val) := contMDiff_coe_sphere
  have hv : ContMDiff ((𝓡 m).prod (𝓡 m))
      𝓘(ℝ, Vector (m + 1) × Vector (m + 1)) ∞
      (fun p : Sphere m × Sphere m => (p.1.val, p.2.val)) :=
    (hcoe.comp contMDiff_fst).prodMk_space (hcoe.comp contMDiff_snd)
  have hc : ContMDiffOn ((𝓡 m).prod (𝓡 m)) 𝓘(ℝ, ℝ) ∞
      (fun p : Sphere m × Sphere m => cost D (p.1.val, p.2.val)) (sphereDomain D) :=
    (contDiffOn_cost D).contMDiffOn.comp hv.contMDiffOn (fun p hp => hp)
  apply hc.congr
  intro p hp
  exact (cost_eq_angle D ha hδ (ClosedHemisphere.unit_norm p.1)
    (ClosedHemisphere.unit_norm p.2) hp).symm

theorem exists_smooth_cost_near_diagonal (m : ℕ) (p : Sphere m) :
    ∃ U : Set (Sphere m × Sphere m), IsOpen U ∧ (p, p) ∈ U ∧
      ContMDiffOn ((𝓡 m).prod (𝓡 m)) 𝓘(ℝ, ℝ) ∞ (sphereCost m) U := by
  have hp := ClosedHemisphere.unit_norm p
  obtain ⟨D⟩ := nonempty_localLogData hp (by positivity : 0 < Real.pi / 4)
  refine ⟨sphereDomain D, isOpen_sphereDomain D, base_mem_domain D hp,
    contMDiffOn_sphereCost D hp ?_⟩
  linarith [Real.pi_pos]

theorem exists_open_diagonal_cost_domain (m : ℕ) :
    ∃ U : Set (Sphere m × Sphere m), IsOpen U ∧ (∀ p : Sphere m, (p, p) ∈ U) ∧
      ContMDiffOn ((𝓡 m).prod (𝓡 m)) 𝓘(ℝ, ℝ) ∞ (sphereCost m) U := by
  choose U hU hp hs using exists_smooth_cost_near_diagonal m
  refine ⟨⋃ p, U p, isOpen_iUnion hU, fun p => mem_iUnion.mpr ⟨p, hp p⟩, ?_⟩
  intro q hq
  obtain ⟨p, hpq⟩ := mem_iUnion.mp hq
  exact ((hs p).contMDiffAt ((hU p).mem_nhds hpq)).contMDiffWithinAt

end NativeSphere

end Wikipedia.HopfProblem.OrbitPair.SpherePairedGeodesic
