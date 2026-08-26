import ErdosProblems.Erdos19.PairStarRemainder

/-! # Palette and vertex-cover estimates for the projective completion -/

namespace Erdos19

open Finset

theorem exists_small_completion_palettes (n : ℕ) (B : Finset (Fin n))
    (hB : B.card ≤ n / 128) :
    ∃ reserved palette : Finset (Fin n), reserved.card = n / 64 ∧
      Disjoint reserved B ∧ n - n / 16 ≤ palette.card ∧
      Disjoint palette B ∧ Disjoint palette reserved := by
  classical
  have hroom : n / 64 ≤ (univ \ B).card := by
    rw [card_sdiff_of_subset (subset_univ B), card_univ, Fintype.card_fin]
    have h64 := Nat.mul_div_le n 64
    have h128 := Nat.mul_div_le n 128
    omega
  obtain ⟨reserved, hreserved, hcard⟩ := exists_subset_card_eq hroom
  let palette := univ \ (B ∪ reserved)
  have hdisj : Disjoint reserved B :=
    disjoint_left.mpr (fun _ he hb ↦ (mem_sdiff.mp (hreserved he)).2 hb)
  refine ⟨reserved, palette, hcard, hdisj, ?_, ?_, ?_⟩
  · have hbig : (B ∪ reserved).card ≤ n / 16 := by
      have hsum := card_union_le B reserved
      have h64 := scaled_floor_le_div n 4 16 (by norm_num)
      have h128 := scaled_floor_le_div n 8 16 (by norm_num)
      norm_num only [Nat.reduceMul] at h64 h128
      omega
    dsimp only [palette]
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
    omega
  · exact disjoint_left.mpr (fun _ he hb ↦ (mem_sdiff.mp he).2 (mem_union_left _ hb))
  · exact disjoint_left.mpr (fun _ he hr ↦ (mem_sdiff.mp he).2 (mem_union_right _ hr))

theorem pair_star_completion_slack (n d u : ℕ) (hd : d ≤ n / 1024)
    (hu : u ≤ n / 1024) :
    (n / 256 + n / 1024) + 2 * d + 4 * u ≤ n / 64 := by
  have h256 := scaled_floor_le_div n 4 64 (by norm_num)
  have h1024 := scaled_floor_le_div n 16 64 (by norm_num)
  norm_num only [Nat.reduceMul] at h256 h1024
  omega

namespace SetHypergraph

theorem highPairVertices_small_of_low_incidence (n : ℕ) (hn : 0 < n)
    (H J : SetHypergraph (Fin n))
    (hpairs : ∀ e ∈ H, e.ncard = 2 → e ∈ J)
    (htotal : 65536 * (∑ e : J, e.1.ncard) ≤ n ^ 2) :
    (H.highPairVertices (n - 2 * (n / 8))).card ≤ n / 1024 := by
  let u := (H.highPairVertices (n - 2 * (n / 8))).card
  let T := ∑ e : J, e.1.ncard
  change 65536 * T ≤ n ^ 2 at htotal
  have hcount : u * (n - 2 * (n / 8) + 1) ≤ T :=
    H.highPairVertices_card_mul_le_incidence J _ hpairs
  have hk : n ≤ 2 * (n - 2 * (n / 8) + 1) := by
    have hq := Nat.mul_div_le n 8
    omega
  have hscaled := Nat.mul_le_mul_left u hk
  have hload : u * n ≤ 2 * T := by nlinarith only [hcount, hscaled]
  have hloadScale := Nat.mul_le_mul_left 32768 hload
  have hu : 32768 * u ≤ n := by
    apply Nat.le_of_mul_le_mul_left (c := n) _ hn
    nlinarith only [hloadScale, htotal]
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 1024)).mpr
  change u * 1024 ≤ n
  omega

#print axioms highPairVertices_small_of_low_incidence

end SetHypergraph

#print axioms exists_small_completion_palettes
#print axioms pair_star_completion_slack

end Erdos19
