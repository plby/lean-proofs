import Wikipedia.HopfProblem.OrbitPairSphereVertexCoordinates

/-!
# Global inverses of the actual stereographic product charts

For these specific sphere charts the target is all of the Euclidean model.
Thus their inverses, and the translated inverses used for local energy, are
globally smooth. The forward chart still has only its original open source.
The centered open partial homeomorphism records these actual maps for the
generic chart-supported deformation theorems.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

open NoExoticSixSphere

variable {n m : ℕ}

theorem sphereChart_target (x : Sphere n) : (sphereChart x).target = univ := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  change (extChartAt (𝓡 n) x).target = univ
  rw [extChartAt_target]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    preimage_id, range_id, inter_univ]
  change (stereographic' n (-x)).target = univ
  exact stereographic'_target (-x)

theorem atVertices_target (v : Space n m) : (atVertices v).target = univ := by
  apply eq_univ_of_forall
  intro K
  change ∀ j ∈ (univ : Set (Fin m)), K j ∈ (sphereChart (v j)).target
  intro j _
  rw [sphereChart_target]
  exact mem_univ _

theorem coordinateDomain_eq_univ (v : Space n m) : coordinateDomain v = univ := by
  ext K
  simp only [coordinateDomain, atVertices_target, mem_setOf_eq, mem_univ]

theorem contMDiff_atVertices_symm (v : Space n m) :
    ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, Model n m) ∞ (atVertices v).symm := by
  intro K
  exact contMDiffAt_atVertices_symm v K (by rw [atVertices_target]; exact mem_univ _)

theorem contMDiff_fromCoordinates (v : Space n m) :
    ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, Model n m) ∞ (fromCoordinates v) := by
  apply contMDiffOn_univ.mp
  simpa only [coordinateDomain_eq_univ] using contMDiffOn_fromCoordinates v

def centeredChart (v : Space n m) : OpenPartialHomeomorph (Space n m) (Model n m) :=
  (atVertices v).trans (Homeomorph.subRight (atVertices v v)).toOpenPartialHomeomorph

theorem centeredChart_apply (v w : Space n m) : centeredChart v w = coordinates v w := rfl

theorem centeredChart_symm_apply (v : Space n m) (K : Model n m) :
    (centeredChart v).symm K = fromCoordinates v K := rfl

theorem centeredChart_source (v : Space n m) :
    (centeredChart v).source = (atVertices v).source := by
  simp only [centeredChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]

theorem mem_centeredChart_source (v : Space n m) : v ∈ (centeredChart v).source := by
  rw [centeredChart_source]
  exact mem_atVertices_source v

theorem centeredChart_target (v : Space n m) : (centeredChart v).target = univ := by
  simp only [centeredChart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, atVertices_target, preimage_univ, inter_univ]

theorem centeredChart_self (v : Space n m) : centeredChart v v = 0 := coordinates_self v

theorem centeredChart_symm_zero (v : Space n m) : (centeredChart v).symm 0 = v :=
  fromCoordinates_zero v

theorem contMDiff_centeredChart_symm (v : Space n m) :
    ContMDiff 𝓘(ℝ, Model n m) 𝓘(ℝ, Model n m) ∞ (centeredChart v).symm :=
  contMDiff_fromCoordinates v

end Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace
