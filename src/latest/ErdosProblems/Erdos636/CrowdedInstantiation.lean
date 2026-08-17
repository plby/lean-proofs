/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos636.OuterSwitchingPath

open Classical SimpleGraph

namespace Erdos636
namespace OuterSwitchingPath

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

lemma RawPath.W_subset_endpoints
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (P : RawPath S) (i : ℕ) :
    P.W i ⊆ S.Wminus ∪ S.Wplus := by
  rw [RawPath.W]
  exact Finset.union_subset
    ((permutationPrefix_subset _ _ _).trans Finset.subset_union_left)
    ((permutationPrefix_subset _ _ _).trans Finset.subset_union_right)

lemma CrowdedPath.W_subset_endpoints
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window) (i : ℕ) :
    Q.W i ⊆ S.Wminus ∪ S.Wplus := by
  rw [Q.W_eq]
  exact Q.raw.W_subset_endpoints i

lemma CrowdedPath.disjoint_W_U0
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window) (i : ℕ) :
    Disjoint (Q.W i) S.U0 := by
  rw [Q.W_eq]
  exact Q.raw.disjoint_W_U0 i

lemma CrowdedPath.crowd_subset_matching
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) :
    Q.crowd i ⊆ S.matching :=
  Q.crowd_subset i hi

lemma CrowdedPath.crowd_pairwiseDisjoint
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) :
    (Q.crowd i : Set (Finset V)).PairwiseDisjoint id := by
  intro x hx y hy hxy
  exact S.matching_pairwiseDisjoint
    (Q.crowd_subset i hi hx) (Q.crowd_subset i hi hy) hxy

lemma CrowdedPath.crowd_uniform
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) {x : Finset V} (hx : x ∈ Q.crowd i) :
    x.card = S.k := by
  exact S.matching_uniform x (Q.crowd_subset i hi hx)

lemma CrowdedPath.crowd_away_structuralBase
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) {x : Finset V} (hx : x ∈ Q.crowd i) :
    Disjoint x (S.Wminus ∪ S.Wplus ∪ S.U0) := by
  exact S.matching_away x (Q.crowd_subset i hi hx)

lemma CrowdedPath.crowd_away_W_union_U0
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) {x : Finset V} (hx : x ∈ Q.crowd i) :
    Disjoint x (Q.W i ∪ S.U0) := by
  apply (Q.crowd_away_structuralBase hi hx).mono_right
  exact Finset.union_subset
    ((Q.W_subset_endpoints i).trans Finset.subset_union_left)
    Finset.subset_union_right

lemma CrowdedPath.crowd_away_W
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) {x : Finset V} (hx : x ∈ Q.crowd i) :
    Disjoint x (Q.W i) :=
  (Q.crowd_away_W_union_U0 hi hx).mono_right Finset.subset_union_left

lemma CrowdedPath.crowd_away_U0
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) {x : Finset V} (hx : x ∈ Q.crowd i) :
    Disjoint x S.U0 :=
  (Q.crowd_away_W_union_U0 hi hx).mono_right Finset.subset_union_right

lemma CrowdedPath.crowd_degree_U0
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) {x : Finset V} (hx : x ∈ Q.crowd i) :
    degreeInto G S.U0 x = S.d0 := by
  exact S.degree_U0 x (Q.crowd_subset i hi hx)

lemma CrowdedPath.crowd_diverse
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) {x y : Finset V}
    (hx : x ∈ Q.crowd i) (hy : y ∈ Q.crowd i) (hxy : x ≠ y) :
    aDiv * scale ≤ incidenceDiffMass G S.U0 x y := by
  exact S.diverse x (Q.crowd_subset i hi hx)
    y (Q.crowd_subset i hi hy) hxy

lemma CrowdedPath.crowd_degree_window
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) {x : Finset V} (hx : x ∈ Q.crowd i) :
    |(degreeInto G (Q.W i) x : ℤ) -
        degreeInto G (Q.W i) (Q.anchor i)| ≤ window := by
  exact Q.degree_window i hi x hx

lemma CrowdedPath.anchor_degree_U0
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) :
    degreeInto G S.U0 (Q.anchor i) = S.d0 := by
  exact S.degree_U0 (Q.anchor i) (Q.anchor_mem i hi)

lemma CrowdedPath.anchor_away_W_union_U0
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    {mu window : ℕ} (Q : CrowdedPath S mu window)
    {i : ℕ} (hi : i ≤ nW) :
    Disjoint (Q.anchor i) (Q.W i ∪ S.U0) := by
  apply (S.matching_away (Q.anchor i) (Q.anchor_mem i hi)).mono_right
  exact Finset.union_subset
    ((Q.W_subset_endpoints i).trans Finset.subset_union_left)
    Finset.subset_union_right

end

end OuterSwitchingPath
end Erdos636
