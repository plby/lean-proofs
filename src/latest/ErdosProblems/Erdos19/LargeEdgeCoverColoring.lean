import ErdosProblems.Erdos19.LargeEdgeDichotomy
import ErdosProblems.Erdos19.CoreCoverColoring
import ErdosProblems.Erdos19.CoverPaletteBudget

/-! # Large-edge colorings with tunable coverage bounds

The saving branch retains half of its palette saving after coverage refinement.
In the projective branch the dense core excludes very large edges; its pair
coloring extends through the remainder with the same coverage bound.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

theorem eventually_large_edge_cover_dichotomy (t : ℕ) (ht : 1024 ≤ t) (B₀ : ℕ) :
    ∃ b r₀ N : ℕ, 8 * t ≤ b ∧ B₀ ≤ b ∧ 2 ≤ r₀ ∧
      ∀ n : ℕ, N ≤ n → ∀ H : SetHypergraph (Fin n), H.IsLinear →
        (∀ e : H, r₀ ≤ e.1.ncard) →
        (∃ color : H.EdgeColoring (Fin (n - n / (2 * b ^ 4))),
          H.IsCoverBoundedColoring color (16 * (n / t))) ∨
        (∃ color : H.EdgeColoring (Fin n),
          H.IsCoverBoundedColoring color (16 * (n / t)) ∧
          (∀ e : H, e.1.ncard < 8 * (n / t)) ∧
          ∃ W : Finset H, ∃ r : ℕ,
            projectiveScale n - projectiveScale n / t ≤ r ∧
            (∀ e ∈ W, r ≤ e.1.ncard ∧ e.1.ncard ≤ r + r / b) ∧
            (b - 10) * n ^ 2 ≤ b * (∑ e ∈ W, e.1.ncard * (e.1.ncard - 1))) := by
  obtain ⟨b, hbt, hbB₀, N₀, hbN, hN₀⟩ :=
    eventually_large_edge_saving_or_projective_core_parametric t ht B₀
  let r₀ := t ^ 2 * (2 * b ^ 4) + 1
  let N := max N₀ ((64 * t) * (64 * t) + 64 * t + 2)
  have htpos : 0 < t := by omega
  have hbpos : 0 < b := by omega
  have hb4pos : 0 < b ^ 4 := pow_pos hbpos _
  have ht2pos : 0 < t ^ 2 := pow_pos htpos _
  have hr₀ : 2 ≤ r₀ := by dsimp only [r₀]; nlinarith only [ht2pos, hb4pos]
  have hr₀b : b ^ 4 ≤ r₀ := by dsimp only [r₀]; nlinarith only [ht2pos, hb4pos]
  have htb : t ≤ b ^ 4 := by
    have hb : 1 ≤ b := hbpos
    have hpow : b ≤ b ^ 4 := by
      have h := Nat.pow_le_pow_left hb 3
      have hmul := Nat.mul_le_mul_left b h
      simpa only [one_pow, Nat.mul_one, ← pow_succ'] using hmul
    exact (show t ≤ b by omega).trans hpow
  refine ⟨b, r₀, N, hbt, hbB₀, hr₀, ?_⟩
  intro n hn H hlinear hmin
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnlarge : (64 * t) * (64 * t) + 64 * t + 2 ≤ n := (le_max_right _ _).trans hn
  have hkt := projectiveScale_ge_of_large_card (64 * t) n hnlarge
  have hnpos : 0 < n := hb4pos.trans_le (hbN.trans hn₀)
  have hmin' (e : H) : t ^ 2 * (2 * b ^ 4) + 1 ≤ e.1.ncard := hmin e
  rcases hN₀ n hn₀ H hlinear (fun e ↦ hr₀b.trans (hmin e)) with hcolor |
    ⟨S, W, r, hS, hWS, _, hdense, hpeel, hprojective, hminS, hmaxW, hvolume⟩
  · left
    exact H.exists_cover_bounded_coloring_of_saving hlinear n t (b ^ 4)
      (Fintype.card_fin n) hnpos htpos hb4pos hmin' hcolor
  · right
    have hk : n - n / t ≤ n - n / b ^ 4 :=
      Nat.sub_le_sub_left (Nat.div_le_div_left htb htpos) n
    have hcoremin : ∀ e ∈ S,
        projectiveScale n - projectiveScale n / t ≤ e.1.ncard :=
      fun e he ↦ hprojective.trans (hminS e he)
    have hbudget₀ := cover_extension_palette_budget n t (2 * b ^ 4) hnpos htpos (by omega)
    have hdiv : n / (2 * b ^ 4) ≤ n / b ^ 4 :=
      Nat.div_le_div_left (by omega) hb4pos
    have hbudget : n - n / b ^ 4 +
        n * (n - 1) / ((8 * (n / t) + 1) * (t ^ 2 * (2 * b ^ 4))) ≤ n := by
      have h := Nat.div_le_self n (b ^ 4)
      omega
    obtain ⟨color, hc⟩ := H.exists_cover_bounded_coloring_of_projective_core hlinear n t
      (n - n / b ^ 4) (t ^ 2 * (2 * b ^ 4)) (Fintype.card_fin n) ht hkt hk
      (by positivity) hmin' S hS hdense hpeel hcoremin hbudget
    have hmax := H.edge_size_lt_of_dense_projective_core hlinear n t (n - n / b ^ 4)
      (Fintype.card_fin n) ht hkt hk S hS hdense hcoremin
    exact ⟨color, hc, hmax, W, r, hprojective,
      fun e he ↦ ⟨hminS e (hWS he), hmaxW e he⟩, hvolume⟩

/-- Every prescribed fixed coverage fraction is achievable once the minimum
edge size and the vertex count are sufficiently large. Singleton color classes
are allowed for edges larger than the coverage bound. -/
theorem eventually_large_minimum_cover_coloring (t : ℕ) (ht : 1024 ≤ t) :
    ∃ r₀ N : ℕ, 2 ≤ r₀ ∧ ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → (∀ e : H, r₀ ≤ e.1.ncard) →
      ∃ color : H.EdgeColoring (Fin n),
        H.IsCoverBoundedColoring color (16 * (n / t)) := by
  obtain ⟨b, r₀, N, _, _, hr₀, hN⟩ := eventually_large_edge_cover_dichotomy t ht 0
  refine ⟨r₀, N, hr₀, ?_⟩
  intro n hn H hlinear hmin
  rcases hN n hn H hlinear hmin with ⟨color, hc⟩ | ⟨color, hc, _⟩
  · exact H.exists_cover_bounded_coloring_of_palette_card color _ _ hc
      (by simpa only [Fintype.card_fin] using Nat.sub_le n (n / (2 * b ^ 4)))
  · exact ⟨color, hc⟩

#print axioms eventually_large_edge_cover_dichotomy
#print axioms eventually_large_minimum_cover_coloring

end Erdos19.SetHypergraph
