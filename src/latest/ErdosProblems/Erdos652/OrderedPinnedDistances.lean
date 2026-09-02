import ErdosProblems.Erdos652.PinnedDistanceLowerBound
import ErdosProblems.Erdos652.LowPointsArithmetic

open scoped Real
noncomputable section

namespace Erdos652

open Classical in
/-- The number of distinct nonzero pinned distances determined by `p` in
the finite point set `S`.  If `p ∈ S`, erasing `p` is exactly the exclusion
`j ≠ i` in the statement of Problem 652. -/
def pinnedDistanceCount (p : Point) (S : Finset Point) : ℕ :=
  (distanceRadii p (S.erase p)).card

open Classical in
/-- Points whose pinned-distance count is below `C * sqrt |S|`. -/
def lowPinnedDistancePoints (S : Finset Point) (C : ℝ) : Finset Point :=
  S.filter fun p => (pinnedDistanceCount p S : ℝ) < C * Real.sqrt S.card

lemma distanceRadii_card_mono {p : Point} {A B : Finset Point} (hAB : A ⊆ B) :
    (distanceRadii p A).card ≤ (distanceRadii p B).card := by
  exact Finset.card_le_card (Finset.image_subset_image hAB)

/-- Quantifier form of the affirmative resolution of Problem 652.

For every fixed normalized distance bound `C`, once `k` is large enough,
no sufficiently large planar `n`-point set has `k` points with fewer than
`C * sqrt n` pinned distances.  The explicit sufficient size condition
`k^3 + k ≤ n` is stronger than “sufficiently large” and is the form needed
to invoke Mathialagan's bipartite estimate. -/
theorem eventually_few_lowPinnedDistancePoints :
    ∀ C : ℝ, 0 < C →
      ∃ K : ℕ, 8 ≤ K ∧
        ∀ k : ℕ, K ≤ k →
          ∀ n : ℕ, k ^ 3 + k ≤ n →
            ∀ S : Finset Point, S.card = n →
              (lowPinnedDistancePoints S C).card < k := by
  obtain ⟨ε, hε, hpinned⟩ := pinnedDistanceLowerBound
  intro C hC
  obtain ⟨K₀ : ℕ, hK₀⟩ := exists_nat_gt (2 * C ^ 2 / ε ^ 2)
  let K := max 8 K₀
  refine ⟨K, le_max_left _ _, ?_⟩
  intro k hK n hn S hSn
  have hk8 : 8 ≤ k := (le_max_left 8 K₀).trans hK
  have hkpos : 0 < k := lt_of_lt_of_le (by omega : 0 < 8) hk8
  have hkThreshold : 2 * C ^ 2 / ε ^ 2 < (k : ℝ) := by
    have hK₀k : K₀ ≤ k := (le_max_right 8 K₀).trans hK
    exact hK₀.trans_le (by exact_mod_cast hK₀k)
  by_contra hnot
  have hmany : k ≤ (lowPinnedDistancePoints S C).card := by omega
  obtain ⟨P, hPsub, hPcard⟩ := Finset.exists_subset_card_eq hmany
  let Q : Finset Point := S \ P
  have hPS : P ⊆ S := hPsub.trans (Finset.filter_subset _ _)
  have hPQ : Disjoint P Q := by
    exact Finset.disjoint_sdiff
  have hQcard : Q.card = n - k := by
    have hcard : Q.card + P.card = S.card := by
      simpa [Q] using Finset.card_sdiff_add_card_eq_card hPS
    rw [hSn, hPcard] at hcard
    omega
  have hkCubeQ : P.card ^ 3 ≤ Q.card := by
    rw [hPcard, hQcard]
    omega
  have hPnonempty : P.Nonempty := Finset.card_pos.mp (by omega)
  let values : Finset ℕ := P.image fun p => (distanceRadii p Q).card
  have hvalues : values.Nonempty := hPnonempty.image _
  let t : ℕ := values.max' hvalues
  have htUniform : ∀ p ∈ P, (distanceRadii p Q).card ≤ t := by
    intro p hp
    exact Finset.le_max' values _ (Finset.mem_image_of_mem _ hp)
  have htLow : (t : ℝ) < C * Real.sqrt n := by
    have htmem : t ∈ values := Finset.max'_mem values hvalues
    rcases Finset.mem_image.mp htmem with ⟨p, hp, hpt⟩
    have hpLow := (Finset.mem_filter.mp (hPsub hp)).2
    have hQerase : Q ⊆ S.erase p := by
      intro q hq
      have hqS : q ∈ S := (Finset.mem_sdiff.mp hq).1
      have hqP : q ∉ P := (Finset.mem_sdiff.mp hq).2
      exact Finset.mem_erase.mpr ⟨by
        intro hqp
        subst q
        exact hqP hp, hqS⟩
    have hcardMono := distanceRadii_card_mono (p := p) hQerase
    change (pinnedDistanceCount p S : ℝ) < C * Real.sqrt S.card at hpLow
    have htNat : t ≤ pinnedDistanceCount p S := by
      rw [← hpt]
      exact hcardMono
    rw [hSn] at hpLow
    exact (by exact_mod_cast htNat : (t : ℝ) ≤ pinnedDistanceCount p S) |>.trans_lt hpLow
  have hpinnedHere := hpinned P Q t hPQ (by simpa [hPcard] using hk8)
    hkCubeQ htUniform
  have hnpos : 0 < n := lt_of_lt_of_le hkpos (by omega)
  have hqHalfNat : n ≤ 2 * Q.card := by
    rw [hQcard]
    have hkCube : k ≤ k ^ 3 := Nat.le_pow (by norm_num)
    omega
  have hqHalf : (n : ℝ) / 2 ≤ (Q.card : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast (by simpa [Nat.mul_comm] using hqHalfNat)
  apply low_points_contradiction_arithmetic hε hC
    (by exact_mod_cast hkpos) (by exact_mod_cast hnpos) hqHalf hkThreshold
  · simpa [hPcard, hQcard] using hpinnedHere
  · simpa using htLow

end Erdos652
