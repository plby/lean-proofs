import ErdosProblems.Erdos88.GaussianVariancePartition

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal NNReal BigOperators

namespace Erdos88.GaussianQuadratic

theorem diagonalPartialSum_smallBall_le_of_relative_rankTwo_tail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (S : Finset ι)
    {rho : ℝ} (hrho : 0 < rho)
    (htail : ∀ T ⊆ S, T.card ≤ 2 →
      rho * (∑ i ∈ S, (lam i) ^ 2) ≤ ∑ i ∈ S \ T, (lam i) ^ 2)
    (hV : 0 < partialVariance a lam S)
    {eps : ℝ} (heps : 0 ≤ eps) (x : ℝ) :
    Erdos88.Esseen.smallBall
        ((Measure.pi fun _ : ι ↦ standardGaussian).map
          (diagonalPartialSum a lam S)) eps x ≤
      2 * (eps / Real.sqrt (partialVariance a lam S)) +
        (eps / Real.sqrt (partialVariance a lam S)) * threeSpectralMass /
          (2 * Real.pi * Real.sqrt (min rho 1 / 192)) := by
  classical
  rw [map_diagonalPartialSum_eq_diagonalCenteredLaw_subtype]
  let sigma := Real.sqrt (partialVariance a lam S)
  have hsigma : 0 < sigma := Real.sqrt_pos.2 hV
  let a' : S → ℝ := fun i ↦ a i / sigma
  let lam' : S → ℝ := fun i ↦ lam i / sigma
  have hsum : totalVariance a' lam' = 1 := by
    dsimp only [a', lam']
    rw [totalVariance_div, totalVariance_subtype_eq_partialVariance,
      Real.sq_sqrt hV.le, div_self (ne_of_gt hV)]
    exact hsigma.ne'
  have htail' : ∀ T : Finset S, T.card ≤ 2 →
      rho * (∑ i, (lam' i) ^ 2) ≤ ∑ i with i ∉ T, (lam' i) ^ 2 := by
    intro T hTcard
    let e : S ↪ ι := Function.Embedding.subtype fun i ↦ i ∈ S
    let U : Finset ι := T.map e
    have hUS : U ⊆ S := by
      intro i hi
      obtain ⟨j, hjT, rfl⟩ := Finset.mem_map.mp hi
      exact j.property
    have hUcard : U.card ≤ 2 := by
      simpa only [U, Finset.card_map] using hTcard
    have hraw := htail U hUS hUcard
    have hleft : (∑ i : S, (lam' i) ^ 2) =
        (∑ i ∈ S, (lam i) ^ 2) / sigma ^ 2 := by
      dsimp only [lam']
      simp_rw [div_pow]
      rw [← Finset.sum_div]
      exact congrArg (fun z : ℝ ↦ z / sigma ^ 2)
        (Finset.sum_subtype S (fun _ ↦ Iff.rfl) (fun i ↦ (lam i) ^ 2)).symm
    have hright : (∑ i : S with i ∉ T, (lam' i) ^ 2) =
        (∑ i ∈ S \ U, (lam i) ^ 2) / sigma ^ 2 := by
      dsimp only [lam']
      simp_rw [div_pow]
      rw [← Finset.sum_div]
      congr 1
      change (∑ i : S with i ∉ T, (lam (e i)) ^ 2) =
        ∑ i ∈ S \ U, (lam i) ^ 2
      rw [← Finset.sum_map (Finset.univ.filter fun i : S ↦ i ∉ T) e
        (fun i : ι ↦ (lam i) ^ 2)]
      congr 1
      ext i
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_sdiff, U, e]
      constructor
      · rintro ⟨j, hj, rfl⟩
        refine ⟨j.property, ?_⟩
        intro hU
        obtain ⟨k, hk, hkj⟩ := hU
        apply hj
        have : k = j := e.injective hkj
        simpa only [this] using hk
      · intro hi
        let j : S := ⟨i, hi.1⟩
        refine ⟨j, ?_, rfl⟩
        intro hj
        exact hi.2 ⟨j, hj, rfl⟩
    rw [hleft, hright]
    calc
      rho * ((∑ i ∈ S, (lam i) ^ 2) / sigma ^ 2) =
          (rho * (∑ i ∈ S, (lam i) ^ 2)) / sigma ^ 2 := by
        rw [mul_div_assoc]
      _ ≤ (∑ i ∈ S \ U, (lam i) ^ 2) / sigma ^ 2 :=
        (div_le_div_iff_of_pos_right (sq_pos_of_pos hsigma)).2 hraw
  have hnorm := smallBall_diagonalCenteredLaw_le_of_relative_rankTwo_tail
    a' lam' hsum hrho htail' (div_nonneg heps hsigma.le) (x / sigma)
  have hmap : diagonalCenteredLaw a' lam' =
      (diagonalCenteredLaw (fun i : S ↦ a i) (fun i : S ↦ lam i)).map
        (fun y ↦ y / sigma) := by
    exact diagonalCenteredLaw_div _ _ hsigma.ne'
  rw [hmap, smallBall_map_div_eq _ hsigma] at hnorm
  simpa only [sigma, mul_div_assoc] using hnorm

end Erdos88.GaussianQuadratic
