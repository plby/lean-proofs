import Wikipedia.HopfProblem.OrbitPairSpherePolygonCurveDerivative

/-!
# Actual derivatives of normalized sphere variations at every time

The derivative of normalization is computed from the derivative of norm
squared. It depends continuously on the nonzero affine point and the
prescribed velocity. Applying it to the native normalized vertex curves
gives actual tangent velocities at every parameter value.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SphereNormalVariation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalizeVelocity (x w : E) : E :=
  ‖x‖⁻¹ • w - (inner ℝ x w / ‖x‖ ^ 3) • x

theorem hasDerivAt_normalize {f : ℝ → E} {f' : E} {s : ℝ}
    (hf : HasDerivAt f f' s) (hn : f s ≠ 0) :
    HasDerivAt (fun r => NormedSpace.normalize (f r)) (normalizeVelocity (f s) f') s := by
  have hnorm : ‖f s‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hsq := (hf.norm_sq).sqrt (pow_ne_zero 2 hnorm)
  have hd : HasDerivAt (fun r => ‖f r‖) (2 * inner ℝ (f s) f' / (2 * ‖f s‖)) s := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using hsq
  have hcoef : -(2 * inner ℝ (f s) f' / (2 * ‖f s‖)) / ‖f s‖ ^ 2 =
      -(inner ℝ (f s) f' / ‖f s‖ ^ 3) := by field_simp
  simpa only [normalizeVelocity, NormedSpace.normalize, Pi.inv_apply, hcoef,
    neg_smul, sub_eq_add_neg] using! (hd.inv hnorm).fun_smul hf

theorem hasDerivAt_normalize_affine (x w : E) (s : ℝ) (hn : x + s • w ≠ 0) :
    HasDerivAt (fun r : ℝ => NormedSpace.normalize (x + r • w))
      (normalizeVelocity (x + s • w) w) s := by
  have hf : HasDerivAt (fun r : ℝ => x + r • w) w s := by
    simpa only [one_smul, zero_add, id_eq, Pi.add_apply] using!
      (hasDerivAt_const s x).add ((hasDerivAt_id s).smul_const w)
  exact hasDerivAt_normalize hf hn

theorem normalizeVelocity_of_unit_orthogonal {x w : E} (hx : ‖x‖ = 1)
    (hw : inner ℝ x w = 0) : normalizeVelocity x w = w := by
  simp only [normalizeVelocity, hx, hw, inv_one, one_pow, zero_div,
    one_smul, zero_smul, sub_zero]

theorem continuousAt_normalizeVelocity {X : Type*} [TopologicalSpace X]
    {x w : X → E} {p : X} (hx : ContinuousAt x p) (hw : ContinuousAt w p) (hn : x p ≠ 0) :
    ContinuousAt (fun q => normalizeVelocity (x q) (w q)) p := by
  have hnorm : ‖x p‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  exact ((hx.norm.inv₀ hnorm).smul hw).sub
    (((hx.inner hw).div (hx.norm.pow 3) (pow_ne_zero 3 hnorm)).smul hx)

end Wikipedia.HopfProblem.OrbitPair.SphereNormalVariation

namespace Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

open NoExoticSixSphere GLOrthonormalization SphereNormalVariation

variable {n m : ℕ}

theorem hasDerivAt_normalVariation_at (v : Space n m) (W : Field v) (s : ℝ) (j : Fin m) :
    HasDerivAt (fun r => (normalVariation v W r j).val)
      (normalizeVelocity ((v j).val + s • (W j : Vector (n + 1))) (W j : Vector (n + 1))) s :=
  hasDerivAt_normalize_affine (v j).val (W j) s (affineField_ne_zero v (s • W) j)

def normalVelocityField (v : Space n m) (W : Field v) (s : ℝ) : Field (normalVariation v W s) :=
  fun j => ⟨normalizeVelocity ((v j).val + s • (W j : Vector (n + 1))) (W j : Vector (n + 1)),
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      (SphereAngle.inner_derivative_of_unit (hasDerivAt_normalVariation_at v W s j)
        (fun r => ClosedHemisphere.unit_norm (normalVariation v W r j)))⟩

theorem normalVelocityField_apply (v : Space n m) (W : Field v) (s : ℝ) (j : Fin m) :
    (normalVelocityField v W s j : Vector (n + 1)) =
      normalizeVelocity ((v j).val + s • (W j : Vector (n + 1))) (W j : Vector (n + 1)) := rfl

end Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace

variable {n m : ℕ}

theorem hasDerivAt_energy_normalVariation_at (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (W : Field v) (s : ℝ)
    (hs : normalVariation v W s ∈ admissible (costDomain n) a b m) :
    HasDerivAt (fun r => energy a b τ (normalVariation v W r))
      (-2 * ∑ j : Fin m, inner ℝ (normalVelocityField v W s j : Vector (n + 1))
        (balance a b τ (normalVariation v W s) j)) s :=
  hasDerivAt_energy_curve a b τ (contMDiff_normalVariation v W) s hs
    (normalVelocityField v W s) (hasDerivAt_normalVariation_at v W s)

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
