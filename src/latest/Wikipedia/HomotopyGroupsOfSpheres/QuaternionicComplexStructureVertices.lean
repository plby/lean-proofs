import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureTransitions
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicVertexFamilies

/-!
# Local coordinates for finite products of quaternionic complex structures

The model at a vertex tuple is the product of its actual anticommuting skew
spaces. These local models may depend on the tuple. Their chart transitions
are smooth, and the inverse chart gives a smooth family of symplectic vertices.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructureVertices

open ComplexStructures

abbrev Space (n m : ℕ) := Fin m → ComplexStructures.Space n

abbrev Model {n m : ℕ} (v : Space n m) := (i : Fin m) → AntiSkewSpace (v i)

variable {n m : ℕ}

def forget (v : Space n m) : VertexSpace.Space n m := fun i ↦ toSymplectic (v i)

theorem continuous_forget : Continuous (forget : Space n m → VertexSpace.Space n m) :=
  continuous_pi (fun i ↦ continuous_toSymplectic.comp (continuous_apply i))

theorem forget_injective : Function.Injective (forget : Space n m → VertexSpace.Space n m) := by
  intro v w h
  funext i
  exact toSymplectic_injective (congrFun h i)

def atVertices (v : Space n m) : OpenPartialHomeomorph (Space n m) (Model v) :=
  OpenPartialHomeomorph.pi (fun i ↦ Cayley.chart (v i))

theorem atVertices_apply (v w : Space n m) (i : Fin m) :
    atVertices v w i = Cayley.chart (v i) (w i) := rfl

theorem atVertices_symm_apply (v : Space n m) (K : Model v) (i : Fin m) :
    (atVertices v).symm K i = Cayley.point (v i) (K i) := rfl

theorem self_mem_source (v : Space n m) : v ∈ (atVertices v).source :=
  fun i _ ↦ Cayley.self_mem_chart_source (v i)

theorem atVertices_self (v : Space n m) : atVertices v v = 0 :=
  funext (fun i ↦ Cayley.chart_self (v i))

theorem atVertices_symm_zero (v : Space n m) : (atVertices v).symm 0 = v :=
  funext (fun i ↦ Cayley.chart_symm_zero (v i))

theorem target_eq_univ (v : Space n m) : (atVertices v).target = univ := by
  apply Set.eq_univ_of_forall
  intro K i _
  exact mem_univ (K i)

theorem continuous_atVertices_symm (v : Space n m) : Continuous (atVertices v).symm :=
  continuous_pi (fun i ↦ (Cayley.continuous_point (v i)).comp (continuous_apply i))

theorem contDiffOn_transition (v w : Space n m) :
    ContDiffOn ℝ ∞ ((atVertices v).symm.trans (atVertices w))
      ((atVertices v).symm.trans (atVertices w)).source := by
  apply contDiffOn_pi.mpr
  intro i
  have hev : ContDiff ℝ ∞ (fun K : Model v ↦ K i) := contDiff_pi.mp contDiff_id i
  have hmaps : MapsTo (fun K : Model v ↦ K i)
      ((atVertices v).symm.trans (atVertices w)).source
      ((Cayley.chart (v i)).symm.trans (Cayley.chart (w i))).source :=
    fun _ hK ↦ ⟨hK.1 i (mem_univ i), hK.2 i (mem_univ i)⟩
  exact (Cayley.contDiffOn_transition (v i) (w i)).comp hev.contDiffOn hmaps

theorem contMDiff_forget_chart (v : Space n m) :
    ContMDiff 𝓘(ℝ, Model v) 𝓘(ℝ, VertexSpace.Model n m) ∞
      (fun K : Model v ↦ forget ((atVertices v).symm K)) := by
  apply VertexSpace.contMDiff_iff_coordinatewise.mpr
  intro i
  have hev : ContDiff ℝ ∞ (fun K : Model v ↦ K i) := contDiff_pi.mp contDiff_id i
  exact (Cayley.contMDiff_point_toSymplectic (v i)).comp hev.contMDiff

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructureVertices
