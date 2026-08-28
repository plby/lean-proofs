import Wikipedia.HopfProblem.OrbitPairSphereNormalVertexVariation

/-!
# Independent actual chart tangents of normalized sphere vertex variations

The normalization map from the finite product of actual tangent planes into
the original vertex manifold is smooth. Its derivative in the existing
product chart is a continuous linear map. Applying the inverse chart and
the original sphere inclusion recovers each prescribed ambient velocity,
so this chart derivative is injective. This connects negative field families
to independent native manifold tangents, not merely to distinct curves.
-/

noncomputable section

open Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

open NoExoticSixSphere GLOrthonormalization

variable {n m : ℕ}

def normalCoordinates (v : Space n m) (W : Field v) : Model n m :=
  atVertices v (normalMap v W)

theorem normalCoordinates_zero (v : Space n m) : normalCoordinates v 0 = atVertices v v := by
  rw [normalCoordinates, normalMap_zero]

theorem contDiffAt_normalCoordinates (v : Space n m) :
    ContDiffAt ℝ ∞ (normalCoordinates v) 0 := by
  have hc := (contMDiffAt_iff_target.mp ((contMDiff_normalMap v) 0)).2
  rw [normalMap_zero, extChartAt_coe, chartAt_eq, modelWithCornersSelf_coe] at hc
  simp only [Function.id_comp] at hc
  exact hc.contDiffAt

def normalChartTangent (v : Space n m) : Field v →L[ℝ] Model n m :=
  fderiv ℝ (normalCoordinates v) 0

theorem hasDerivAt_normalVariation_coordinates (v : Space n m) (W : Field v) :
    HasDerivAt (fun s => atVertices v (normalVariation v W s)) (normalChartTangent v W) 0 := by
  have hc : HasFDerivAt (normalCoordinates v) (normalChartTangent v) 0 :=
    ((contDiffAt_normalCoordinates v).differentiableAt (by simp)).hasFDerivAt
  have hs : HasDerivAt (fun s : ℝ => s • W) W 0 := by
    simpa only [one_smul] using! (hasDerivAt_id (0 : ℝ)).smul_const W
  have hc' : HasFDerivAt (normalCoordinates v) (normalChartTangent v) ((0 : ℝ) • W) := by
    simpa only [zero_smul] using hc
  simpa only [normalCoordinates, normalVariation, Function.comp_apply] using!
    hc'.comp_hasDerivAt 0 hs

theorem contDiffAt_inverse_eval_val (v : Space n m) (j : Fin m) :
    ContDiffAt ℝ ∞ (fun K : Model n m => ((atVertices v).symm K j).val) (atVertices v v) := by
  letI : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  have hcoe : ContMDiff (𝓡 n) 𝓘(ℝ, Vector (n + 1)) ∞
      (fun x : Sphere n => x.val) := contMDiff_coe_sphere
  have hs : ContMDiffAt 𝓘(ℝ, Model n m) (𝓡 n) ∞
      (fun K : Model n m => (atVertices v).symm K j) (atVertices v v) :=
    contMDiffAt_inverse_eval v j
  exact (ContMDiffAt.comp (g := fun x : Sphere n => x.val)
    (f := fun K : Model n m => (atVertices v).symm K j)
    (atVertices v v) hcoe.contMDiffAt hs).contDiffAt

theorem eventually_normalVariation_source (v : Space n m) (W : Field v) :
    ∀ᶠ s in 𝓝 (0 : ℝ), normalVariation v W s ∈ (atVertices v).source := by
  have hc := (contMDiff_normalVariation v W).continuous.continuousAt (x := (0 : ℝ))
  change Tendsto (normalVariation v W) (𝓝 0) (𝓝 (normalVariation v W 0)) at hc
  rw [normalVariation_zero] at hc
  exact hc.eventually ((atVertices v).open_source.mem_nhds (mem_atVertices_source v))

theorem normalChartTangent_injective (v : Space n m) :
    Function.Injective (normalChartTangent v) := by
  apply (injective_iff_map_eq_zero (normalChartTangent v)).mpr
  intro W hW
  funext j
  apply Subtype.ext
  let g : Model n m → Vector (n + 1) := fun K => ((atVertices v).symm K j).val
  have hg : HasFDerivAt g (fderiv ℝ g (atVertices v v)) (atVertices v (normalVariation v W 0)) := by
    rw [normalVariation_zero]
    exact ((contDiffAt_inverse_eval_val v j).differentiableAt (by simp)).hasFDerivAt
  have hd := hg.comp_hasDerivAt 0 (hasDerivAt_normalVariation_coordinates v W)
  rw [hW, map_zero] at hd
  have heq : (fun s => g (atVertices v (normalVariation v W s))) =ᶠ[𝓝 (0 : ℝ)]
      (fun s => (normalVariation v W s j).val) := by
    filter_upwards [eventually_normalVariation_source v W] with s hs
    exact congrArg (fun z : Space n m => (z j).val) ((atVertices v).left_inv hs)
  have hz : HasDerivAt (fun s => (normalVariation v W s j).val) 0 0 :=
    hd.congr_of_eventuallyEq heq.symm
  exact (hasDerivAt_normalVariation_eval v W j).unique hz

theorem independent_normal_chart_tangents (v : Space n m) {d : ℕ}
    (R : (Fin d → ℝ) →ₗ[ℝ] Field v) (hR : Function.Injective R) :
    Function.Injective (fun c =>
      deriv (fun s => atVertices v (normalVariation v (R c) s)) 0) := by
  intro c e h
  change deriv (fun s => atVertices v (normalVariation v (R c) s)) 0 =
    deriv (fun s => atVertices v (normalVariation v (R e) s)) 0 at h
  rw [(hasDerivAt_normalVariation_coordinates v (R c)).deriv,
    (hasDerivAt_normalVariation_coordinates v (R e)).deriv] at h
  exact hR (normalChartTangent_injective v h)

end Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace
