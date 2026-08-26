import ErdosProblems.Erdos547.FractionalGallaiEdmonds
import ErdosProblems.Erdos547.FractionalCompactness

/-!
# Neighbourhood-saturation maximizers in a Gallai–Edmonds partition

The support is enlarged to include all separator-to-singleton edges. The
covering and support constraints are closed, so an optimum exists. The
alternating-path properties of these optima are proved separately.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

def singletonVertices (D : GallaiEdmondsPartition G) : Finset V :=
  (D.blocks.filter fun C ↦ C.card = 1).biUnion id

def Allowed (D : GallaiEdmondsPartition G) (u v : V) : Prop :=
  D.CompletionSupport u v ∨ (u ∈ D.separator ∧ v ∈ D.singletonVertices) ∨
    (v ∈ D.separator ∧ u ∈ D.singletonVertices)

def IsFractionalGE (D : GallaiEdmondsPartition G) (μ : FractionalMatching G) : Prop :=
  (∀ u ∈ D.separator ∪ D.nontrivialVertices, μ.load u = 1) ∧
    ∀ u v, ¬ D.Allowed u v → μ.weight u v = 0

theorem exists_fractionalGE (D : GallaiEdmondsPartition G) :
    ∃ μ : FractionalMatching G, D.IsFractionalGE μ := by
  obtain ⟨μ, hS, hB, hsupp⟩ := D.exists_fractional_completion
  refine ⟨μ, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact hS u hu
    · exact hB u hu
  · intro u v h
    exact hsupp u v (fun huv ↦ h (Or.inl huv))

def geConstraints (D : GallaiEdmondsPartition G) : Set (V → V → ℝ) := {f |
  (∀ u ∈ D.separator ∪ D.nontrivialVertices, (∑ v, f u v) = 1) ∧
    ∀ u v, ¬ D.Allowed u v → f u v = 0}

theorem isClosed_geConstraints (D : GallaiEdmondsPartition G) : IsClosed D.geConstraints := by
  have hcov : IsClosed {f : V → V → ℝ |
      ∀ u ∈ D.separator ∪ D.nontrivialVertices, (∑ v, f u v) = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun _ ↦
      isClosed_eq (by fun_prop) continuous_const
  have hsupp : IsClosed {f : V → V → ℝ | ∀ u v, ¬ D.Allowed u v → f u v = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_eq (by fun_prop) continuous_const
  exact hcov.inter hsupp

/-- Neighbourhood saturation attains its maximum over all fractional GE
matchings on this fixed decomposition. -/
theorem exists_max_saturation (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V) :
    ∃ μ : FractionalMatching G, D.IsFractionalGE μ ∧
      ∀ ν : FractionalMatching G, D.IsFractionalGE ν →
        w.saturation ν.load c ≤ w.saturation μ.load c := by
  obtain ⟨μ₀, hμ₀⟩ := D.exists_fractionalGE
  exact exists_maximizing_fractional_with_constraints G D.geConstraints D.isClosed_geConstraints
    ⟨μ₀, hμ₀⟩ (fun f ↦ ∑ u, min (w.weight c u) (∑ v, f u v)) (by fun_prop)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.exists_max_saturation
