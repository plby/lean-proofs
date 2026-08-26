import ErdosProblems.Erdos556.CubeQuadratic

/-!
# Energy on a matching of cube edges
-/

namespace Erdos556

open Finset

theorem cubeBilinear_eq_diagonal (x : CubeProfile → ℝ)
    (hzero : ∀ p q, p ≠ q → cubeOverlap p q * x p * x q = 0) :
    cubeBilinear x x = ∑ p, x p ^ 2 := by
  unfold cubeBilinear
  apply sum_congr rfl
  intro p _
  rw [sum_eq_single p]
  · rw [cubeOverlap_self]
    ring
  · intro q _ hqp
    exact hzero p q hqp.symm
  · intro hp
    exact (hp (mem_univ p)).elim

theorem cubeEnergy_of_edge_support (x : CubeProfile → ℝ) (S : Finset CubeProfile)
    (hsupport : ∀ p, p ∉ S → x p = 0)
    (hdim : ∀ p ∈ S, profileDimension p = 1)
    (hdisj : (S : Set CubeProfile).Pairwise (fun p q => Disjoint (profileVertices p) (profileVertices q))) :
    cubeEnergy x = (∑ p ∈ S, x p ^ 2) - ∑ p ∈ S, x p := by
  classical
  have hzero (p q : CubeProfile) (hpq : p ≠ q) : cubeOverlap p q * x p * x q = 0 := by
    by_cases hp : p ∈ S
    · by_cases hq : q ∈ S
      · simp only [cubeOverlap, if_pos (hdisj hp hq hpq), zero_mul]
      · rw [hsupport q hq, mul_zero]
    · rw [hsupport p hp, mul_zero, zero_mul]
  have hsq : (∑ p, x p ^ 2) = ∑ p ∈ S, x p ^ 2 := by
    symm
    apply sum_subset (subset_univ S)
    intro p _ hp
    rw [hsupport p hp]
    norm_num
  have hlin : cubeLinear x = ∑ p ∈ S, x p := by
    calc
      cubeLinear x = ∑ p ∈ S, (profileDimension p : ℝ) * x p := by
        symm
        apply sum_subset (subset_univ S)
        intro p _ hp
        rw [hsupport p hp, mul_zero]
      _ = ∑ p ∈ S, x p := by
        apply sum_congr rfl
        intro p hp
        rw [hdim p hp]
        norm_num
  rw [cubeEnergy_eq, cubeBilinear_eq_diagonal x hzero, hsq, hlin]

theorem cubeOverlap_wholeCube (p : CubeProfile) : cubeOverlap wholeCube p = 1 := by
  have hfull : profileVertices wholeCube = univ := by decide
  have hnon : (profileVertices p).Nonempty := by
    apply card_pos.mp
    rw [profileVertices_card]
    positivity
  have hnot : ¬ Disjoint (profileVertices wholeCube) (profileVertices p) := by
    intro hd
    obtain ⟨v, hv⟩ := hnon
    exact Finset.disjoint_left.mp hd (by rw [hfull]; exact mem_univ v) hv
  simp only [cubeOverlap, if_neg hnot]

theorem cubeGradient_wholeCube (x : CubeProfile → ℝ) :
    cubeGradient x wholeCube = 2 * (∑ p, x p) - 3 := by
  simp only [cubeGradient, cubeOverlap_wholeCube, one_mul, wholeCube_dimension, Nat.cast_ofNat]

#print axioms cubeEnergy_of_edge_support
#print axioms cubeGradient_wholeCube

end Erdos556
