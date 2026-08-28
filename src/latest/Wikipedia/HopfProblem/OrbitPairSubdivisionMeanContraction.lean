import Wikipedia.HopfProblem.OrbitPairSubdivisionMeanGeometry

/-!
# Quantitative contraction between nested face means

For nested nonempty faces of at most `N + 1` vertices, their uniform means
are at distance at most `N / (N + 1)` times the original vertex diameter.
The ambient space is an arbitrary real normed space.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

variable {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem faceMean_union_dist_le (v : V → E) (A C : Finset V) [DecidableEq V]
    (hAC : Disjoint A C) (hA : A.Nonempty) (hC : C.Nonempty)
    (D : ℝ) (hv : ∀ i ∈ A ∪ C, ∀ j ∈ A ∪ C, dist (v i) (v j) ≤ D) :
    dist (faceMean v A) (faceMean v (A ∪ C)) ≤
      ((C.card : ℝ) / (A.card + C.card)) * D := by
  let a : ℝ := (A.card : ℝ) / (A.card + C.card)
  let b : ℝ := (C.card : ℝ) / (A.card + C.card)
  have hsum : (0 : ℝ) < A.card + C.card :=
    add_pos (Nat.cast_pos.mpr hA.card_pos) (Nat.cast_pos.mpr hC.card_pos)
  have hb : 0 ≤ b := div_nonneg (Nat.cast_nonneg _) hsum.le
  have hab : a + b = 1 := by
    dsimp [a, b]
    rw [← add_div, div_self (ne_of_gt hsum)]
  have hd : faceMean v A - faceMean v (A ∪ C) = b • (faceMean v A - faceMean v C) := by
    rw [faceMean_union v A C hAC hA hC]
    change faceMean v A - (a • faceMean v A + b • faceMean v C) = _
    rw [show a = 1 - b by linarith, sub_smul, one_smul, smul_sub]
    abel
  rw [dist_eq_norm, hd, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  apply mul_le_mul_of_nonneg_left _ hb
  rw [← dist_eq_norm]
  exact faceMeans_dist_le v A C (A ∪ C) hA hC Finset.subset_union_left
    Finset.subset_union_right D hv

theorem faceMean_ratio_le (A C : Finset V) (hA : A.Nonempty)
    (N : ℕ) (hcard : A.card + C.card ≤ N + 1) :
    ((C.card : ℝ) / (A.card + C.card)) ≤ (N : ℝ) / (N + 1) := by
  have ha : (1 : ℝ) ≤ A.card := by exact_mod_cast hA.card_pos
  have hc : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hcard' : (A.card : ℝ) + C.card ≤ N + 1 := by exact_mod_cast hcard
  have hsum : (0 : ℝ) < A.card + C.card := by linarith
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  apply (div_le_div_iff₀ hsum hNpos).mpr
  have hm : (N : ℝ) ≤ N * (A.card : ℝ) := by nlinarith
  nlinarith

theorem faceMeans_dist_le_mesh (v : V → E) (A B : Finset V)
    (hA : A.Nonempty) (hAB : A ⊆ B) (N : ℕ) (hcard : B.card ≤ N + 1)
    (D : ℝ) (hD : 0 ≤ D) (hv : ∀ i ∈ B, ∀ j ∈ B, dist (v i) (v j) ≤ D) :
    dist (faceMean v A) (faceMean v B) ≤ ((N : ℝ) / (N + 1)) * D := by
  classical
  by_cases he : A = B
  · subst B
    rw [dist_self]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by positivity)) hD
  · let C := B \ A
    have hC : C.Nonempty := Finset.sdiff_nonempty.mpr
      (fun hBA ↦ he (Finset.Subset.antisymm hAB hBA))
    have hAC : Disjoint A C := Finset.disjoint_left.mpr
      (fun i hi hiC ↦ (Finset.mem_sdiff.mp hiC).2 hi)
    have hu : A ∪ C = B := Finset.union_sdiff_of_subset hAB
    have hcard' : A.card + C.card ≤ N + 1 := by
      rw [← Finset.card_union_of_disjoint hAC, hu]
      exact hcard
    have hv' : ∀ i ∈ A ∪ C, ∀ j ∈ A ∪ C, dist (v i) (v j) ≤ D := hu ▸ hv
    have h := faceMean_union_dist_le v A C hAC hA hC D hv'
    rw [hu] at h
    exact h.trans (mul_le_mul_of_nonneg_right (faceMean_ratio_le A C hA N hcard') hD)

theorem meshRatio_nonneg (N : ℕ) : 0 ≤ (N : ℝ) / (N + 1) := by positivity

theorem meshRatio_lt_one (N : ℕ) : (N : ℝ) / (N + 1) < 1 := by
  apply (div_lt_one (by positivity : (0 : ℝ) < N + 1)).mpr
  linarith

end Wikipedia.HopfProblem.OrbitPair.Subdivision
