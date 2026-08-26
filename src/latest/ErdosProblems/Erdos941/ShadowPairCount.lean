import ErdosProblems.Erdos941.ProgressionPairCount

/-! # Counting sphere pairs satisfying the two shadowing congruences -/

namespace Erdos941

noncomputable def shadowPairs (n q : ℕ) : Finset (Triple × Triple) :=
  ((spherePoints n).product (spherePoints n)).filter fun p =>
    (q : ℤ) ∣ dot3 p.1 p.2 - n ∨ (q : ℤ) ∣ dot3 p.1 p.2 + n

theorem spherePairs_antidiagonal (n : ℕ) :
    spherePairs n (-(n : ℤ)) = (spherePoints n).image fun v => (v, -v) := by
  ext ⟨v, w⟩
  simp only [mem_spherePairs, Finset.mem_image, Prod.mk.injEq, mem_spherePoints]
  constructor
  · rintro ⟨hv, hw, he⟩
    have h := (dot3_eq_neg_norm_iff hv hw).mp he
    exact ⟨v, hv, rfl, by rw [h, neg_neg]⟩
  · rintro ⟨u, hu, rfl, rfl⟩
    have hneg : tripleNorm (-u) = n := by simpa [tripleNorm, norm3] using hu
    exact ⟨hu, hneg, (dot3_eq_neg_norm_iff hu hneg).mpr (by simp)⟩

theorem spherePairs_antidiagonal_card (n : ℕ) :
    (spherePairs n (-(n : ℤ))).card = sphereCount n := by
  rw [spherePairs_antidiagonal, Finset.card_image_iff.mpr]
  · rfl
  · intro v _ w _ h
    exact congrArg Prod.fst h

theorem shadowPairs_card_le (n q : ℕ) :
    (shadowPairs n q).card ≤ 2 * sphereCount n +
      (∑ e ∈ sphereResidueValues n q n, (spherePairs n e).card) +
      (∑ e ∈ sphereResidueValues n q (-(n : ℤ)), (spherePairs n e).card) := by
  classical
  let P := (sphereResidueValues n q n).biUnion (spherePairs n)
  let M := (sphereResidueValues n q (-(n : ℤ))).biUnion (spherePairs n)
  let D := spherePairs n n
  let A := spherePairs n (-(n : ℤ))
  have hsub : shadowPairs n q ⊆ (D ∪ A) ∪ (P ∪ M) := by
    rintro ⟨v, w⟩ hp
    obtain ⟨hvw, hc⟩ := Finset.mem_filter.mp hp
    obtain ⟨hv, hw⟩ := Finset.mem_product.mp hvw
    have hnv := mem_spherePoints.mp hv
    have hnw := mem_spherePoints.mp hw
    by_cases he : dot3 v w = n
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (mem_spherePairs.mpr ⟨hnv, hnw, he⟩))
    by_cases he' : dot3 v w = -(n : ℤ)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_spherePairs.mpr ⟨hnv, hnw, he'⟩))
    have hb := dot3_bounds hnv hnw
    dsimp only at hb
    have hI : dot3 v w ∈ Finset.Ioo (-(n : ℤ)) n := Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
    apply Finset.mem_union_right
    rcases hc with hc | hc
    · apply Finset.mem_union_left
      exact Finset.mem_biUnion.mpr ⟨dot3 v w, Finset.mem_filter.mpr ⟨hI, hc⟩,
        mem_spherePairs.mpr ⟨hnv, hnw, rfl⟩⟩
    · apply Finset.mem_union_right
      have hcm : (q : ℤ) ∣ dot3 v w - -(n : ℤ) := by simpa only [sub_neg_eq_add] using hc
      exact Finset.mem_biUnion.mpr ⟨dot3 v w, Finset.mem_filter.mpr ⟨hI, hcm⟩,
        mem_spherePairs.mpr ⟨hnv, hnw, rfl⟩⟩
  have hP : P.card ≤ ∑ e ∈ sphereResidueValues n q n, (spherePairs n e).card := Finset.card_biUnion_le
  have hM : M.card ≤ ∑ e ∈ sphereResidueValues n q (-(n : ℤ)),
      (spherePairs n e).card := Finset.card_biUnion_le
  have hD : D.card = sphereCount n := spherePairs_diagonal_card n
  have hA : A.card = sphereCount n := spherePairs_antidiagonal_card n
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (D ∪ A) (P ∪ M)
  have h3 := Finset.card_union_le D A
  have h4 := Finset.card_union_le P M
  omega

theorem exists_shadowPairs_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n q : ℕ, 0 < n → 0 < q → q.Coprime n →
      ((shadowPairs n q).card : ℝ) ≤
        2 * sphereCount n + K * ((n : ℝ) / q) * (n : ℝ) ^ ε := by
  obtain ⟨K, hK, hbound⟩ := exists_sum_sphere_residue_pairs_bound hε
  refine ⟨2 * K, by positivity, ?_⟩
  intro n q hn hq hcop
  have hcard : ((shadowPairs n q).card : ℝ) ≤ 2 * sphereCount n +
      (∑ e ∈ sphereResidueValues n q n, ((spherePairs n e).card : ℝ)) +
      (∑ e ∈ sphereResidueValues n q (-(n : ℤ)), ((spherePairs n e).card : ℝ)) := by
    exact_mod_cast shadowPairs_card_le n q
  have hplus := hbound n q n hn hq hcop (Or.inl rfl)
  have hminus := hbound n q (-(n : ℤ)) hn hq hcop (Or.inr rfl)
  nlinarith

theorem exists_three_power_shadowPairs_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n L : ℕ, n % 3 = 2 →
      ((shadowPairs n (3 ^ (2 * L))).card : ℝ) ≤
        2 * sphereCount n + K * ((n : ℝ) / 3 ^ (2 * L)) * (n : ℝ) ^ ε := by
  obtain ⟨K, hK, hbound⟩ := exists_shadowPairs_bound hε
  refine ⟨K, hK, ?_⟩
  intro n L hn
  have h3 : (3 : ℕ).Coprime n := (Nat.prime_three.coprime_iff_not_dvd).mpr (by
    intro h
    have := Nat.mod_eq_zero_of_dvd h
    omega)
  have h := hbound n (3 ^ (2 * L)) (by omega) (pow_pos (by decide) _) (h3.pow_left _)
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using h

end Erdos941
