import Wikipedia.HopfProblem.OrbitPairSphereVertexVariation
import Wikipedia.HopfProblem.OrbitPairSphereNormalVariation

/-!
# Normalized variations of actual sphere vertices

These variations agree literally with samples of normalized path variations.
They are smooth in the full finite tangent field, and their ambient velocity
at parameter zero is exactly that field. A zero field gives a constant curve.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

open NoExoticSixSphere GLOrthonormalization SphereTangentExponential

variable {n m : ℕ}

theorem affineField_ne_zero (v : Space n m) (W : Field v) (j : Fin m) :
    (v j).val + (W j : Vector (n + 1)) ≠ 0 := by
  intro he
  have hi := congrArg (fun z => inner ℝ (v j).val z) he
  simp only [inner_add_right, real_inner_self_eq_norm_sq, ClosedHemisphere.unit_norm,
    inner_tangent, one_pow, add_zero, inner_zero_right] at hi
  norm_num at hi

def normalMap (v : Space n m) (W : Field v) : Space n m := fun j =>
  ⟨NormedSpace.normalize ((v j).val + (W j : Vector (n + 1))), by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize (affineField_ne_zero v W j)⟩

theorem normalMap_zero (v : Space n m) : normalMap v 0 = v := by
  funext j
  apply Subtype.ext
  change NormedSpace.normalize ((v j).val + 0) = (v j).val
  rw [add_zero]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (v j))

def fieldEval (v : Space n m) (j : Fin m) : Field v →L[ℝ] Vector (n + 1) :=
  (((ℝ ∙ (v j).val)ᗮ).subtypeL).comp (ContinuousLinearMap.proj j)

theorem fieldEval_apply (v : Space n m) (j : Fin m) (W : Field v) :
    fieldEval v j W = (W j : Vector (n + 1)) := rfl

theorem contMDiff_normalMap_eval (v : Space n m) (j : Fin m) :
    ContMDiff 𝓘(ℝ, Field v) (𝓡 n) ∞ (fun W => normalMap v W j) := by
  letI : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have ha : ContMDiff 𝓘(ℝ, Field v) 𝓘(ℝ, Vector (n + 1)) ∞
      (fun W : Field v => (v j).val + (W j : Vector (n + 1))) :=
    contMDiff_const.add (fieldEval v j).contDiff.contMDiff
  exact (contMDiff_normalize ha (fun W => affineField_ne_zero v W j)).codRestrict_sphere
    (fun W => (normalMap v W j).property)

theorem contMDiff_normalMap (v : Space n m) :
    ContMDiff 𝓘(ℝ, Field v) 𝓘(ℝ, Model n m) ∞ (normalMap v) :=
  contMDiff_of_coordinate (contMDiff_normalMap_eval v)

def normalVariation (v : Space n m) (W : Field v) (s : ℝ) : Space n m :=
  normalMap v (s • W)

theorem normalVariation_val (v : Space n m) (W : Field v) (s : ℝ) (j : Fin m) :
    (normalVariation v W s j).val =
      NormedSpace.normalize ((v j).val + s • (W j : Vector (n + 1))) := rfl

theorem normalVariation_zero (v : Space n m) (W : Field v) : normalVariation v W 0 = v := by
  rw [normalVariation, zero_smul, normalMap_zero]

theorem normalVariation_zero_field (v : Space n m) (s : ℝ) : normalVariation v 0 s = v := by
  rw [normalVariation, smul_zero, normalMap_zero]

theorem contMDiff_normalVariation (v : Space n m) (W : Field v) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Model n m) ∞ (normalVariation v W) :=
  (contMDiff_normalMap v).comp (contMDiff_id.smul contMDiff_const)

theorem hasDerivAt_normalVariation_eval (v : Space n m) (W : Field v) (j : Fin m) :
    HasDerivAt (fun s => (normalVariation v W s j).val) (W j : Vector (n + 1)) 0 := by
  have hd := SphereNormalVariation.hasDerivAt_family_zero
    (γ := fun _ : ℝ => (v j).val) (V := fun _ : ℝ => (W j : Vector (n + 1)))
    (fun _ => ClosedHemisphere.unit_norm (v j)) (fun _ => inner_tangent _ (W j)) (0 : ℝ)
  simpa only [SphereNormalVariation.family, normalVariation_val] using hd

end Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace
