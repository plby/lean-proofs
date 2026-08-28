import Wikipedia.HopfProblem.OrbitPairSpherePolygonCurveDerivative
import Wikipedia.HopfProblem.OrbitPairSpherePolygonHessian

/-!
# The actual sphere polygon differential vanishes exactly at zero balance

The product of the actual tangent planes has the same dimension as the
native chart model. Its already-checked injective chart derivative is
therefore surjective. The normalized first variation consequently tests
every chart tangent, and zero balance is equivalent to a zero manifold
differential, not merely to a selected collection of zero derivatives.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

open NoExoticSixSphere GLOrthonormalization SphereTangentExponential

variable {n m : ℕ}

theorem finrank_field (v : Space n m) : Module.finrank ℝ (Field v) = m * n := by
  letI : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hj (j : Fin m) : Module.finrank ℝ (Tangent (v j).val) = n := by
    apply Submodule.finrank_orthogonal_span_singleton
    apply norm_pos_iff.mp
    rw [ClosedHemisphere.unit_norm]
    norm_num
  change Module.finrank ℝ (∀ j : Fin m, Tangent (v j).val) = m * n
  simp only [Module.finrank_pi_fintype, hj, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

theorem normalChartTangent_surjective (v : Space n m) :
    Function.Surjective (normalChartTangent v) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (normalChartTangent v).toLinearMap)
    ((finrank_field v).trans (finrank_model n m).symm)).mp (normalChartTangent_injective v)

end Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace

variable {n m : ℕ}

theorem localEnergy_derivative_pairing (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m) (W : Field v) :
    fderiv ℝ (localEnergy a b τ v) 0 (normalChartTangent v W) =
      -2 * ∑ j : Fin m, inner ℝ (W j : Vector (n + 1)) (balance a b τ v j) := by
  have hf := ((contDiffAt_localEnergy a b τ v hv).differentiableAt (by simp)).hasFDerivAt
  have hq := hasDerivAt_normalVariation_centeredCoordinates v W
  have hz : coordinates v (normalVariation v W 0) = 0 := by
    rw [normalVariation_zero, coordinates_self]
  have hf' : HasFDerivAt (localEnergy a b τ v) (fderiv ℝ (localEnergy a b τ v) 0)
      (coordinates v (normalVariation v W 0)) := by rwa [hz]
  have hc := hf'.comp_hasDerivAt 0 hq
  have heq : (fun s => energy a b τ (normalVariation v W s)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => localEnergy a b τ v (coordinates v (normalVariation v W s))) := by
    filter_upwards [eventually_normalVariation_source v W] with s hs
    exact congrArg (energy a b τ) (fromCoordinates_coordinates v (normalVariation v W s) hs).symm
  exact (hc.congr_of_eventuallyEq heq).unique (hasDerivAt_energy_normalVariation a b τ v hv W)

theorem mfderiv_energy_eq_zero_of_localEnergy (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hzero : fderiv ℝ (localEnergy a b τ v) 0 = 0) :
    mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0 := by
  have hf : HasFDerivAt (localEnergy a b τ v) (0 : Model n m →L[ℝ] ℝ) 0 := by
    have h := ((contDiffAt_localEnergy a b τ v hv).differentiableAt (by simp)).hasFDerivAt
    rwa [hzero] at h
  have hf' : HasFDerivAt (localEnergy a b τ v) (0 : Model n m →L[ℝ] ℝ)
      (atVertices v v - atVertices v v) := by simpa only [sub_self] using hf
  have hshift : HasFDerivAt (fun K : Model n m => K - atVertices v v)
      (ContinuousLinearMap.id ℝ (Model n m)) (atVertices v v) := by
    simpa only [id_eq] using
      (hasFDerivAt_id (𝕜 := ℝ) (atVertices v v)).sub_const (atVertices v v)
  have hc : HasFDerivAt (fun K : Model n m => localEnergy a b τ v (K - atVertices v v))
      (0 : Model n m →L[ℝ] ℝ) (atVertices v v) := by
    simpa only [ContinuousLinearMap.zero_comp] using!
      HasFDerivAt.comp (g := localEnergy a b τ v)
        (f := fun K : Model n m => K - atVertices v v) (atVertices v v) hf' hshift
  have hraw : HasFDerivAt (fun K : Model n m => energy a b τ ((atVertices v).symm K))
      (0 : Model n m →L[ℝ] ℝ) (atVertices v v) := by
    simpa only [localEnergy, fromCoordinates, sub_add_cancel] using hc
  have hd : HasMFDerivAt 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v 0 := by
    refine ⟨(continuous_energy a b τ).continuousAt, ?_⟩
    change HasFDerivWithinAt (fun K : Model n m => energy a b τ ((atVertices v).symm K))
      (0 : Model n m →L[ℝ] ℝ) (range id) (atVertices v v)
    rw [range_id, hasFDerivWithinAt_univ]
    exact hraw
  exact hd.mfderiv

theorem mfderiv_energy_eq_zero_iff (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m) :
    mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0 ↔ balance a b τ v = 0 := by
  constructor
  · exact balance_eq_zero_of_mfderiv_eq_zero a b τ v hv
  · intro hbal
    apply mfderiv_energy_eq_zero_of_localEnergy a b τ v hv
    apply ContinuousLinearMap.ext
    intro Z
    obtain ⟨W, rfl⟩ := normalChartTangent_surjective v Z
    rw [localEnergy_derivative_pairing a b τ v hv W, hbal]
    simp only [Pi.zero_apply, inner_zero_right, Finset.sum_const_zero, mul_zero, zero_apply]

def balanceSquareNorm (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) : ℝ :=
  ∑ j : Fin m, ‖balance a b τ v j‖ ^ 2

theorem balanceSquareNorm_nonneg (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) :
    0 ≤ balanceSquareNorm a b τ v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem balanceSquareNorm_eq_zero_iff (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) : balanceSquareNorm a b τ v = 0 ↔ balance a b τ v = 0 := by
  constructor
  · intro h
    have he := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => sq_nonneg ‖balance a b τ v j‖)).mp h
    funext j
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (he j (Finset.mem_univ j)))
  · intro h
    simp only [balanceSquareNorm, h, Pi.zero_apply, norm_zero,
      zero_pow (show (2 : ℕ) ≠ 0 by decide), Finset.sum_const_zero]

theorem balanceSquareNorm_pos_of_noncritical (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0) :
    0 < balanceSquareNorm a b τ v := by
  apply lt_of_le_of_ne (balanceSquareNorm_nonneg a b τ v)
  intro h
  exact hcrit ((mfderiv_energy_eq_zero_iff a b τ v hv).mpr
    ((balanceSquareNorm_eq_zero_iff a b τ v).mp h.symm))

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
