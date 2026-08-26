import ErdosProblems.Erdos556.CubeGeometry

/-!
# Admissible weights on cube profiles

The compatibility condition excludes a singleton intersection between
two profiles of positive weight. Positive edge profiles therefore form
a matching in the cube.
-/

namespace Erdos556

open Finset

structure IsCubeWeight (w : CubeProfile → ℝ) : Prop where
  nonneg : ∀ p, 0 ≤ w p
  sum_four : ∑ p, w p = 4
  vertex_zero : ∀ p, profileDimension p = 0 → w p = 0
  edge_le_one : ∀ p, profileDimension p = 1 → w p ≤ 1
  compatible : ∀ p q, 0 < w p → 0 < w q →
    (profileVertices p ∩ profileVertices q).card ≠ 1

def cubeOverlap (p q : CubeProfile) : ℝ :=
  if Disjoint (profileVertices p) (profileVertices q) then 0 else 1

def cubeEnergy (w : CubeProfile → ℝ) : ℝ :=
  (∑ p, ∑ q, cubeOverlap p q * w p * w q) - ∑ p, (profileDimension p : ℝ) * w p

def cubeGradient (w : CubeProfile → ℝ) (p : CubeProfile) : ℝ :=
  2 * (∑ q, cubeOverlap p q * w q) - profileDimension p

theorem cubeOverlap_symm (p q : CubeProfile) : cubeOverlap p q = cubeOverlap q p := by
  simp only [cubeOverlap, disjoint_comm]

theorem cubeOverlap_self (p : CubeProfile) : cubeOverlap p p = 1 := by
  have hcard : 0 < (profileVertices p).card := by rw [profileVertices_card]; positivity
  have hne : ¬ Disjoint (profileVertices p) (profileVertices p) := by
    simpa only [disjoint_self, Finset.bot_eq_empty, ← card_eq_zero] using Nat.ne_of_gt hcard
  simp only [cubeOverlap, if_neg hne]

theorem IsCubeWeight.le_four {w : CubeProfile → ℝ} (hw : IsCubeWeight w) (p : CubeProfile) :
    w p ≤ 4 := by
  calc
    w p ≤ ∑ q, w q := single_le_sum (fun q _ => hw.nonneg q) (mem_univ p)
    _ = 4 := hw.sum_four

theorem edge_profiles_packing_bound (E : Finset CubeProfile) (S : Finset CubeVertex)
    (hdim : ∀ p ∈ E, profileDimension p = 1)
    (hdisj : (E : Set CubeProfile).Pairwise (fun p q => Disjoint (profileVertices p) (profileVertices q)))
    (hsub : ∀ p ∈ E, profileVertices p ⊆ S) : 2 * E.card ≤ S.card := by
  have hsum : (∑ p ∈ E, (profileVertices p).card) = 2 * E.card := by
    calc
      (∑ p ∈ E, (profileVertices p).card) = ∑ _p ∈ E, 2 := by
        apply sum_congr rfl
        intro p hp
        rw [profileVertices_card, hdim p hp]
        norm_num
      _ = 2 * E.card := by simp [Nat.mul_comm]
  rw [← hsum, ← card_biUnion hdisj]
  apply card_le_card
  intro v hv
  obtain ⟨p, hp, hvp⟩ := mem_biUnion.mp hv
  exact hsub p hp hvp

open scoped Classical in
noncomputable def positiveEdgeProfiles (w : CubeProfile → ℝ) : Finset CubeProfile :=
  univ.filter (fun p => profileDimension p = 1 ∧ 0 < w p)

theorem IsCubeWeight.positive_edges_disjoint {w : CubeProfile → ℝ} (hw : IsCubeWeight w) :
    (positiveEdgeProfiles w : Set CubeProfile).Pairwise
      (fun p q => Disjoint (profileVertices p) (profileVertices q)) := by
  intro p hp q hq hpq
  obtain ⟨_, hpdim, hpw⟩ := mem_filter.mp hp
  obtain ⟨_, hqdim, hqw⟩ := mem_filter.mp hq
  exact distinct_compatible_edges_disjoint p q hpdim hqdim hpq (hw.compatible p q hpw hqw)

theorem IsCubeWeight.positive_edges_card_le_four {w : CubeProfile → ℝ} (hw : IsCubeWeight w) :
    (positiveEdgeProfiles w).card ≤ 4 := by
  have h := edge_profiles_packing_bound (positiveEdgeProfiles w) univ
    (fun p hp => (mem_filter.mp hp).2.1) hw.positive_edges_disjoint (fun _ _ => subset_univ _)
  have hcard : (univ : Finset CubeVertex).card = 8 := by decide
  rw [hcard] at h
  omega

#print axioms edge_profiles_packing_bound
#print axioms IsCubeWeight.positive_edges_card_le_four

end Erdos556
