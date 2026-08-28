import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCompatibleLogarithm

/-! # The original finite product of symplectic polygon vertices and its Cayley atlas -/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.VertexSpace

open NoExoticSixSphere.GLOrthonormalization

abbrev Space (n m : ℕ) := Fin m → symplecticSubgroup n
abbrev Model (n m : ℕ) := Fin m → SkewSpace n

variable {n m : ℕ}

def atVertices (v : Space n m) : OpenPartialHomeomorph (Space n m) (Model n m) :=
  OpenPartialHomeomorph.pi (fun i => CayleyAtlas.atOperator (v i))

theorem atVertices_apply (v w : Space n m) (i : Fin m) :
    atVertices v w i = CayleyAtlas.atOperator (v i) (w i) := rfl

theorem atVertices_symm_apply (v : Space n m) (K : Model n m) (i : Fin m) :
    (atVertices v).symm K i = (CayleyAtlas.atOperator (v i)).symm (K i) := rfl

theorem mem_atVertices_source (v : Space n m) : v ∈ (atVertices v).source :=
  fun i _ => CayleyAtlas.mem_atOperator_source (v i)

instance chartedSpace (n m : ℕ) : ChartedSpace (Model n m) (Space n m) where
  atlas := range atVertices
  chartAt := atVertices
  mem_chart_source := mem_atVertices_source
  chart_mem_atlas v := ⟨v, rfl⟩

theorem contDiffOn_transition (v w : Space n m) :
    ContDiffOn ℝ ∞ ((atVertices v).symm.trans (atVertices w))
      ((atVertices v).symm.trans (atVertices w)).source := by
  apply contDiffOn_pi.mpr
  intro i
  have hmaps : MapsTo (fun K : Model n m => K i)
      ((atVertices v).symm.trans (atVertices w)).source
      ((CayleyAtlas.atOperator (v i)).symm.trans (CayleyAtlas.atOperator (w i))).source := by
    intro K hK
    exact ⟨hK.1 i (mem_univ i), hK.2 i (mem_univ i)⟩
  exact (CayleyAtlas.contDiffOn_transition (v i) (w i)).comp
    (contDiff_apply ℝ (SkewSpace n) i).contDiffOn hmaps

instance isManifold (n m : ℕ) : IsManifold 𝓘(ℝ, Model n m) ∞ (Space n m) :=
  isManifold_of_contDiffOn 𝓘(ℝ, Model n m) ∞ (Space n m) (by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, range_id, preimage_id, inter_univ] using
        contDiffOn_transition v w)

theorem contDiff_symm_operator_eval (v : Space n m) (i : Fin m) :
    ContDiff ℝ ∞ (fun K : Model n m => ((atVertices v).symm K i).val.val.val) := by
  change ContDiff ℝ ∞ (fun K : Model n m =>
    (v i).val.val.val.comp (NoExoticSixSphere.CayleyTransform.operator (toOrthogonalSkew n (K i))))
  have hK : ContDiff ℝ ∞ (fun K : Model n m => K i) := contDiff_apply ℝ (SkewSpace n) i
  have hC : ContDiff ℝ ∞ (fun K : Model n m =>
      NoExoticSixSphere.CayleyTransform.operator (toOrthogonalSkew n (K i))) :=
    (CayleyAtlas.contDiff_cayleyOperator (n := n)).comp hK
  exact contDiff_const.clm_comp hC

theorem contMDiff_operator_eval (i : Fin m) :
    ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
      (fun v : Space n m => (v i).val.val.val) := by
  intro v
  rw [contMDiffAt_iff_source]
  change ContMDiffWithinAt 𝓘(ℝ, Model n m)
    𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
    (fun K => ((atVertices v).symm K i).val.val.val) (range id) _
  rw [range_id, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  exact (contDiff_symm_operator_eval v i).contDiffAt

theorem contMDiff_eval (i : Fin m) :
    ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, SkewSpace n) ∞ (fun v : Space n m => v i) :=
  Smoothness.contMDiff_iff_operator.mpr (contMDiff_operator_eval i)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.VertexSpace
