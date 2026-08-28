import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryOrthogonalSmoothness
import Wikipedia.NoExoticSixSphere.OrthogonalVertexFamilies

/-! # Finite products of symmetric determinant-one vertices and their smooth atlas -/

noncomputable section

@[instance_reducible] private def orthogonalModelNormedSpace (d m : ℕ) :
    NormedSpace ℝ (NoExoticSixSphere.OrthogonalVertexSpace.Model d m) := inferInstance

open scoped Matrix.Norms.Frobenius Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.VertexSpace

open RealSymmetricMixing LocalLogarithm

abbrev Space (N : Type*) [Fintype N] [DecidableEq N] (m : ℕ) := Fin m → SpecialSpace N
abbrev Model (N : Type*) [Fintype N] (m : ℕ) := Fin m → DirectionSpace N

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

local instance orthogonalModelSpace :
    NormedSpace ℝ (NoExoticSixSphere.OrthogonalVertexSpace.Model (2 * Fintype.card N) m) :=
  orthogonalModelNormedSpace _ _

def atVertices (v : Space N m) : OpenPartialHomeomorph (Space N m) (Model N m) :=
  OpenPartialHomeomorph.pi (fun i ↦ atPoint (v i))

theorem mem_atVertices_source (v : Space N m) : v ∈ (atVertices v).source :=
  fun i _ ↦ mem_atPoint_source (v i)

theorem atVertices_self (v : Space N m) : atVertices v v = 0 :=
  funext (fun i ↦ atPoint_self (v i))

theorem atVertices_symm_zero (v : Space N m) : (atVertices v).symm 0 = v := by
  have h := (atVertices v).left_inv (mem_atVertices_source v)
  rwa [atVertices_self] at h

instance chartedSpace (N : Type*) [Fintype N] [DecidableEq N] (m : ℕ) :
    NormedChartedSpace (Model N m) (Space N m) where
  atlas := range atVertices
  chartAt := atVertices
  mem_chart_source := mem_atVertices_source
  chart_mem_atlas v := ⟨v, rfl⟩

theorem contDiffOn_transition (v w : Space N m) :
    ContDiffOn ℝ ∞ ((atVertices v).symm.trans (atVertices w))
      ((atVertices v).symm.trans (atVertices w)).source := by
  apply contDiffOn_pi.mpr
  intro i
  have hm : MapsTo (fun K : Model N m ↦ K i)
      ((atVertices v).symm.trans (atVertices w)).source
      ((atPoint (v i)).symm.trans (atPoint (w i))).source :=
    fun _ h ↦ ⟨h.1 i (mem_univ i), h.2 i (mem_univ i)⟩
  exact (LocalLogarithm.contDiffOn_transition (v i) (w i)).comp
    (contDiff_apply ℝ (DirectionSpace N) i).contDiffOn hm

instance isManifold (N : Type*) [Fintype N] [DecidableEq N] (m : ℕ) :
    IsManifold 𝓘(ℝ, Model N m) ∞ (Space N m) :=
  isManifold_of_contDiffOn 𝓘(ℝ, Model N m) ∞ (Space N m) (by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, range_id, preimage_id, inter_univ] using!
        contDiffOn_transition v w)

theorem contDiff_symm_matrix_eval (v : Space N m) (i : Fin m) :
    ContDiff ℝ ∞ (fun K : Model N m ↦ matrix ((atVertices v).symm K i)) := by
  have hk : ContDiff ℝ ∞ (fun K : Model N m ↦ K i) := contDiff_apply ℝ (DirectionSpace N) i
  exact (contDiff_const.mul (contDiff_exponential_matrix.comp hk)).mul contDiff_const

local instance matrixSelfChart :
    NormedChartedSpace (Matrix N N ℂ) (Matrix N N ℂ) := chartedSpaceSelf _

local instance modelSelfChart :
    NormedChartedSpace (Model N m) (Model N m) := chartedSpaceSelf _

theorem contMDiff_matrix_eval (i : Fin m) :
    ContMDiff 𝓘(ℝ, Model N m) 𝓘(ℝ, Matrix N N ℂ) ∞
      (fun v : Space N m ↦ matrix (v i)) := by
  intro v
  rw [contMDiffAt_iff_source]
  change ContMDiffWithinAt 𝓘(ℝ, Model N m) 𝓘(ℝ, Matrix N N ℂ) ∞
    (fun K : Model N m ↦ matrix ((atVertices v).symm K i)) (range id) _
  rw [range_id, contMDiffWithinAt_univ]
  simpa only [] using! (contDiff_symm_matrix_eval v i).contMDiff.contMDiffAt

theorem contMDiff_eval (i : Fin m) :
    ContMDiff 𝓘(ℝ, Model N m) 𝓘(ℝ, DirectionSpace N) ∞ (fun v : Space N m ↦ v i) :=
  Smoothness.contMDiff_iff_matrix.mpr (contMDiff_matrix_eval i)

def forget (v : Space N m) :
    NoExoticSixSphere.OrthogonalVertexSpace.Space (2 * Fintype.card N) m :=
  fun i ↦ ComplexMatrixRealRepresentation.specialOrthogonal (v i)

theorem contMDiff_forget :
    ContMDiff 𝓘(ℝ, Model N m)
      𝓘(ℝ, NoExoticSixSphere.OrthogonalVertexSpace.Model (2 * Fintype.card N) m) ∞
        (forget (N := N) (m := m)) := by
  apply NoExoticSixSphere.OrthogonalVertexSpace.contMDiff_iff_coordinatewise.mpr
  intro i
  exact ComplexMatrixRealRepresentation.contMDiff_specialOrthogonal.comp (contMDiff_eval i)

theorem continuous_forget : Continuous (forget (N := N) (m := m)) :=
  contMDiff_forget.continuous

theorem contMDiff_forget_chart (v : Space N m) :
    ContMDiff 𝓘(ℝ, Model N m)
      𝓘(ℝ, NoExoticSixSphere.OrthogonalVertexSpace.Model (2 * Fintype.card N) m) ∞
        (fun K : Model N m ↦ forget ((atVertices v).symm K)) := by
  apply NoExoticSixSphere.OrthogonalVertexSpace.contMDiff_iff_operator_family.mpr
  intro i
  have h := (ComplexMatrixRealRepresentation.contDiff_action (N := N)).comp
    (contDiff_symm_matrix_eval v i)
  simpa only [] using! h.contMDiff

theorem forget_injective : Function.Injective (forget (N := N) (m := m)) := by
  intro v w h
  funext i
  apply Subtype.ext
  apply Subtype.ext
  exact ComplexMatrixRealRepresentation.orthogonal_injective (congrFun h i)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.VertexSpace
