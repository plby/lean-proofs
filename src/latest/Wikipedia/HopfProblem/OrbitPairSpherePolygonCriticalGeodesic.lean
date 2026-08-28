import Wikipedia.HopfProblem.OrbitPairSpherePolygonGenerators

/-!
# Realization of a stationary sphere polygon by an actual great circle

The common skew generator is the wedge of the initial vertex with its
actual initial tangent velocity. Its sphere exponential samples all the
vertices. The Hilbert--Schmidt norm identifies every edge speed with that
initial speed, so the polygon energy is exactly speed squared times total
time. On a partition of [0,1], the resulting smooth sphere path has the
same endpoints, samples, and actual integral energy as the polygon.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization CayleyTransform SkewWedge HilbertSchmidt
  SphereVertexSpace SphereAngle SphereTangentExponential SpherePairedGeodesic

variable {n m : ℕ}

theorem inner_outgoingLog (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (i : Fin (m + 1)) :
    inner ℝ (vertices a b v i.castSucc).val (outgoingLog a b τ v i) = 0 := by
  rw [outgoingLog, real_inner_smul_right,
    inner_logVector (ClosedHemisphere.unit_norm _), mul_zero]

def initialTangent (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) : Tangent a.val :=
  ⟨outgoingLog a b τ v 0, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    (inner_outgoingLog a b τ v 0)⟩

theorem generator_initialTangent (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) :
    generator a.val (initialTangent a b τ v) = edgeGenerator a b τ v 0 := rfl

theorem vertices_eq_curve_of_stationary (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) (j : Fin (m + 2)) :
    (vertices a b v j).val = curve a.val (initialTangent a b τ v) (τ j - τ 0) := by
  rw [curve, generator_initialTangent]
  exact vertices_eq_exp_of_stationary a b τ hτ v hv hstat j

theorem initialTangent_ne_zero_of_endpoints_ne (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) (hab : a ≠ b) : initialTangent a b τ v ≠ 0 := by
  intro hz
  have he := vertices_eq_curve_of_stationary a b τ hτ v hv hstat (Fin.last (m + 1))
  rw [vertices_last, hz, curve_zero_velocity] at he
  exact hab (Subtype.ext he.symm)

theorem exists_greatCircle_of_stationary (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) (hab : a ≠ b) :
    ∃ y : Vector (n + 1), ∃ w : ℝ, 0 < w ∧ ‖y‖ = 1 ∧ inner ℝ a.val y = 0 ∧
      w = ‖initialTangent a b τ v‖ ∧
      ∀ j : Fin (m + 2), (vertices a b v j).val =
        SphereGreatCircle.curve a.val y w (τ j - τ 0) := by
  let V := initialTangent a b τ v
  have hV : V ≠ 0 := initialTangent_ne_zero_of_endpoints_ne a b τ hτ v hv hstat hab
  have hn : 0 < ‖V‖ := norm_pos_iff.mpr hV
  refine ⟨‖V‖⁻¹ • (V : Vector (n + 1)), ‖V‖, hn, ?_, ?_, rfl, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    change ‖V‖⁻¹ * ‖V‖ = 1
    exact inv_mul_cancel₀ (ne_of_gt hn)
  · rw [real_inner_smul_right, inner_tangent, mul_zero]
  · intro j
    rw [vertices_eq_curve_of_stationary a b τ hτ v hv hstat j]
    exact curve_formula_of_ne_zero (ClosedHemisphere.unit_norm a) V hV (τ j - τ 0)

theorem squareNorm_edgeGenerator (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (i : Fin (m + 1)) :
    squareNorm (edgeGenerator a b τ v i : Vector (n + 1) →L[ℝ] Vector (n + 1)) =
      2 * ‖outgoingLog a b τ v i‖ ^ 2 := by
  change innerForm (operator (vertices a b v i.castSucc).val (outgoingLog a b τ v i))
    (operator (vertices a b v i.castSucc).val (outgoingLog a b τ v i)) = _
  rw [innerForm_operator, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    ClosedHemisphere.unit_norm, inner_outgoingLog, one_pow, one_mul, zero_mul, sub_zero]

theorem norm_outgoingLog_sq_eq_of_stationary (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) (i : Fin (m + 1)) :
    ‖outgoingLog a b τ v i‖ ^ 2 = ‖initialTangent a b τ v‖ ^ 2 := by
  have he := congrArg
    (fun K : SkewOperators (n + 1) => squareNorm (K : Vector (n + 1) →L[ℝ] Vector (n + 1)))
    (edgeGenerator_eq_first_of_stationary a b τ v hv hstat i)
  rw [squareNorm_edgeGenerator, squareNorm_edgeGenerator] at he
  change ‖outgoingLog a b τ v i‖ ^ 2 = ‖outgoingLog a b τ v 0‖ ^ 2
  linarith

theorem edge_energy_eq_speed_sq_mul (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m) (i : Fin (m + 1)) :
    sphereCost n (edge a b v i) / (τ i.succ - τ i.castSucc) =
      ‖outgoingLog a b τ v i‖ ^ 2 * (τ i.succ - τ i.castSucc) := by
  have hpos : 0 < τ i.succ - τ i.castSucc :=
    sub_pos.mpr (hτ (show i.castSucc < i.succ by simp))
  have hlog : ‖logVector (vertices a b v i.castSucc).val (vertices a b v i.succ).val‖ =
      Real.arccos (inner ℝ (vertices a b v i.castSucc).val (vertices a b v i.succ).val) :=
    norm_logVector (x := (vertices a b v i.castSucc).val) (y := (vertices a b v i.succ).val)
      (ClosedHemisphere.unit_norm _) (ClosedHemisphere.unit_norm _) (hv i)
  rw [outgoingLog, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hpos), hlog]
  change Real.arccos (inner ℝ (vertices a b v i.castSucc).val (vertices a b v i.succ).val) ^ 2 /
      (τ i.succ - τ i.castSucc) = _
  field_simp

theorem sum_steps (τ : Fin (m + 2) → ℝ) :
    (∑ i : Fin (m + 1), (τ i.succ - τ i.castSucc)) = τ (Fin.last (m + 1)) - τ 0 := by
  rw [Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun i => τ i.succ), Fin.sum_univ_succ (fun i => τ i.castSucc)]
  simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero]
  ring

theorem energy_eq_speed_sq_mul_of_stationary (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) :
    energy a b τ v = ‖initialTangent a b τ v‖ ^ 2 * (τ (Fin.last (m + 1)) - τ 0) := by
  unfold energy
  simp_rw [edge_energy_eq_speed_sq_mul a b τ hτ v hv,
    norm_outgoingLog_sq_eq_of_stationary a b τ v hv hstat]
  rw [← Finset.mul_sum, sum_steps]

theorem realized_critical_geodesic (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hlast : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hstat : IsStationary a b τ v) :
    ∃ γ : ℝ → Vector (n + 1), ContDiff ℝ ∞ γ ∧ (∀ t, ‖γ t‖ = 1) ∧
      γ 0 = a.val ∧ γ 1 = b.val ∧
      (∀ j : Fin (m + 2), γ (τ j) = (vertices a b v j).val) ∧
      SpherePathEnergy.energy γ 0 1 = energy a b τ v := by
  refine ⟨curve a.val (initialTangent a b τ v), contDiff_curve _ _,
    norm_curve (ClosedHemisphere.unit_norm a) _, curve_zero _ _, ?_, ?_, ?_⟩
  · have he := vertices_eq_curve_of_stationary a b τ hτ v hv hstat (Fin.last (m + 1))
    simpa only [vertices_last, hzero, hlast, sub_zero] using he.symm
  · intro j
    simpa only [hzero, sub_zero] using (vertices_eq_curve_of_stationary a b τ hτ v hv hstat j).symm
  · rw [energy_curve (ClosedHemisphere.unit_norm a),
      energy_eq_speed_sq_mul_of_stationary a b τ hτ v hv hstat, hzero, hlast,
      sub_zero, mul_one]

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
