import Wikipedia.HopfProblem.OrbitPairSphereLocalEnergy
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# The native finite product of sphere vertices

The topology is the original product topology. Finite products of the
original sphere charts supply the atlas, and coordinate evaluation is smooth
into the original sphere atlas. This is the finite-dimensional manifold on
which the polygon energy and its actual critical points will be studied.
-/

noncomputable section

open scoped ContDiff Manifold
open Set

namespace Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

open NoExoticSixSphere

abbrev Space (n m : ℕ) := Fin m → Sphere n

abbrev Model (n m : ℕ) := Fin m → EuclideanSpace ℝ (Fin n)

variable {n m : ℕ}

def sphereChart (x : Sphere n) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) (Sphere n) (EuclideanSpace ℝ (Fin n)) ∞ :=
  modelChartPartialDiffeomorph (I := 𝓡 n) x

theorem mem_sphereChart_source (x : Sphere n) : x ∈ (sphereChart x).source :=
  mem_extChartAt_source x

def atVertices (v : Space n m) : OpenPartialHomeomorph (Space n m) (Model n m) :=
  OpenPartialHomeomorph.pi (fun i => (sphereChart (v i)).toOpenPartialHomeomorph)

theorem atVertices_apply (v w : Space n m) (i : Fin m) :
    atVertices v w i = sphereChart (v i) (w i) := rfl

theorem atVertices_symm_apply (v : Space n m) (K : Model n m) (i : Fin m) :
    (atVertices v).symm K i = (sphereChart (v i)).symm (K i) := rfl

theorem mem_atVertices_source (v : Space n m) : v ∈ (atVertices v).source :=
  fun i _ => mem_sphereChart_source (v i)

instance chartedSpace (n m : ℕ) : ChartedSpace (Model n m) (Space n m) where
  atlas := range atVertices
  chartAt := atVertices
  mem_chart_source := mem_atVertices_source
  chart_mem_atlas v := ⟨v, rfl⟩

theorem chartAt_eq (v : Space n m) : chartAt (Model n m) v = atVertices v := rfl

theorem contDiffOn_transition (v w : Space n m) :
    ContDiffOn ℝ ∞ ((atVertices v).symm.trans (atVertices w))
      ((atVertices v).symm.trans (atVertices w)).source := by
  apply contDiffOn_pi.mpr
  intro i
  have hmaps : MapsTo (fun K : Model n m => K i)
      ((atVertices v).symm.trans (atVertices w)).source
      ((sphereChart (v i)).symm.trans (sphereChart (w i))).source := by
    intro K hK
    exact ⟨hK.1 i (mem_univ i), hK.2 i (mem_univ i)⟩
  exact ((sphereChart (v i)).symm.trans (sphereChart (w i))).contMDiffOn_toFun.contDiffOn.comp
    (contDiff_apply ℝ (EuclideanSpace ℝ (Fin n)) i).contDiffOn hmaps

instance isManifold (n m : ℕ) : IsManifold 𝓘(ℝ, Model n m) ∞ (Space n m) :=
  isManifold_of_contDiffOn 𝓘(ℝ, Model n m) ∞ (Space n m) (by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, range_id, preimage_id, inter_univ] using
        contDiffOn_transition v w)

theorem contMDiffAt_sphereChart_symm (x : Sphere n) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (sphereChart x).symm (sphereChart x x) :=
  (sphereChart x).contMDiffOn_invFun.contMDiffAt
    ((sphereChart x).open_target.mem_nhds ((sphereChart x).map_source' (mem_sphereChart_source x)))

theorem contMDiffAt_inverse_eval (v : Space n m) (i : Fin m) :
    ContMDiffAt 𝓘(ℝ, Model n m) (𝓡 n) ∞
      (fun K : Model n m => (sphereChart (v i)).symm (K i)) ((atVertices v) v) := by
  have he : ContMDiff 𝓘(ℝ, Model n m) (𝓡 n) ∞
      (fun K : Model n m => K i) := (contDiff_apply ℝ (EuclideanSpace ℝ (Fin n)) i).contMDiff
  exact ContMDiffAt.comp
    (g := (sphereChart (v i)).symm) (f := fun K : Model n m => K i)
    ((atVertices v) v) (contMDiffAt_sphereChart_symm (v i)) he.contMDiffAt

theorem contMDiff_eval (i : Fin m) :
    ContMDiff 𝓘(ℝ, Model n m) (𝓡 n) ∞ (fun v : Space n m => v i) := by
  intro v
  apply contMDiffAt_iff_source.mpr
  rw [extChartAt_coe_symm, extChartAt_coe, chartAt_eq,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm]
  simp only [Function.comp_id, Function.id_comp, range_id, contMDiffWithinAt_univ]
  simpa only [Function.comp_def, atVertices_symm_apply] using contMDiffAt_inverse_eval v i

theorem finrank_model (n m : ℕ) : Module.finrank ℝ (Model n m) = m * n := by
  change Module.finrank ℝ (Fin m → EuclideanSpace ℝ (Fin n)) = m * n
  simp only [Module.finrank_pi_fintype, finrank_euclideanSpace_fin, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace
