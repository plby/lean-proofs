import Wikipedia.HopfProblem.ConifoldPolarBasic
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Native smooth-sphere interfaces for the explicit polar maps

The inverse is real analytic from the usual Euclidean-times-sphere atlas to
the original ambient matrix space.  Every smooth matrix-valued map into the
determinant-one locus has smooth polar coordinates in that same native target
atlas.  No charted-space instance is transported onto the matrix group.
-/

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Elementwise

namespace Wikipedia.HopfProblem.ConifoldPolar

open ConifoldStandardBoundary

local instance matrixTopology : TopologicalSpace MatrixSpace :=
  (inferInstance : PseudoMetricSpace MatrixSpace).toUniformSpace.toTopologicalSpace

local instance matrixChartedSpace : ChartedSpace MatrixSpace MatrixSpace :=
  chartedSpaceSelf MatrixSpace

/-- The ambient normed-space topology is literally the original entrywise product topology. -/
theorem matrixTopology_eq_pi :
    matrixTopology = inferInstanceAs (TopologicalSpace (Fin 2 → Fin 2 → ℂ)) := rfl

/-- The pre-existing product of Euclidean three-space and the stereographic three-sphere atlas. -/
abbrev ProductModel := ModelWithCorners.prod 𝓘(ℝ, Base) (𝓡 3)

private theorem contMDiff_normalSphere_val {n : ℕ∞ω} :
    ContMDiff (𝓡 3) 𝓘(ℝ, Normal) n (fun z : NormalSphere => z.val) := by
  have : Fact (Module.finrank ℝ Normal = 3 + 1) := ⟨by simp [Normal]⟩
  exact contMDiff_coe_sphere (n := 3) (m := n)

private theorem contMDiff_product_base {n : ℕ∞ω} :
    ContMDiff ProductModel 𝓘(ℝ, Base) n (fun q : Base × NormalSphere => q.1) :=
  contMDiff_fst

private theorem contMDiff_product_sphere {n : ℕ∞ω} :
    ContMDiff ProductModel (𝓡 3) n (fun q : Base × NormalSphere => q.2) :=
  contMDiff_snd

private theorem contMDiff_product_normal {n : ℕ∞ω} :
    ContMDiff ProductModel 𝓘(ℝ, Normal) n (fun q : Base × NormalSphere => q.2.val) :=
  (contMDiff_normalSphere_val (n := n)).comp (contMDiff_product_sphere (n := n))

private theorem contMDiff_product_coordinates {n : ℕ∞ω} :
    ContMDiff ProductModel 𝓘(ℝ, Base × Normal) n
      (fun q : Base × NormalSphere => (q.1, q.2.val)) :=
  (contMDiff_product_base (n := n)).prodMk_space (contMDiff_product_normal (n := n))

/-- The original matrix formula is analytic on the native Euclidean-times-sphere product. -/
theorem contMDiff_inverse_val {n : ℕ∞ω} :
    ContMDiff ProductModel 𝓘(ℝ, MatrixSpace) n
      (fun q : Base × NormalSphere => (inverse q).val) := by
  have hi := (inverseMatrix_contDiff (n := n)).comp_contMDiff
    (contMDiff_product_coordinates (n := n))
  exact hi

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace X] [ChartedSpace H X]
  {I : ModelWithCorners ℝ E H} {n : ℕ∞ω} [IsManifold I n X]

/-- Polar coordinates are smooth whenever the actual matrix-valued map is smooth.
No source atlas is transported through the polar homeomorphism. -/
theorem contMDiff_forward_of_matrix (f : X → SpecialLinear)
    (hf : ContMDiff I 𝓘(ℝ, MatrixSpace) n (fun x => (f x).val)) :
    ContMDiff I ProductModel n (fun x => forward (f x)) := by
  have : Fact (Module.finrank ℝ Normal = 3 + 1) := ⟨by simp [Normal]⟩
  have hb : ContMDiff I 𝓘(ℝ, Base) n
      (fun x => baseCoordinates (positivePart (f x).val)) :=
    baseCoordinates_contDiff.comp_contMDiff (positivePart_contDiff.comp_contMDiff hf)
  have hz : ContMDiff I 𝓘(ℝ, Normal) n
      (fun x => normalCoordinates (unitaryPart (f x).val)) :=
    normalCoordinates_contDiff.comp_contMDiff (unitaryPart_contDiff.comp_contMDiff hf)
  have hs : ContMDiff I (𝓡 3) n (fun x => (forward (f x)).2) :=
    hz.codRestrict_sphere (fun x => normalCoordinates_unitaryPart_mem_sphere (f x))
  exact hb.prodMk hs

end Wikipedia.HopfProblem.ConifoldPolar
