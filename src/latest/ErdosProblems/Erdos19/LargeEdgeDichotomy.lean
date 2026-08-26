import ErdosProblems.Erdos19.LargeEdgeCore
import ErdosProblems.Erdos19.SubprojectiveWindow
import ErdosProblems.Erdos19.ProjectiveWindowGap
import ErdosProblems.Erdos19.HighVolumeWindow

/-! # A large-edge coloring saving or a projective core

A subprojective rank window receives a strict palette saving. Its complement
has small pair volume and is colored with a separate small palette.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

theorem eventually_large_edge_saving_or_projective_core_parametric
    (t : ℕ) (ht : 1024 ≤ t) (B₀ : ℕ) :
    ∃ b : ℕ, 8 * t ≤ b ∧ B₀ ≤ b ∧ ∃ N : ℕ, b ^ 4 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → (∀ e : H, b ^ 4 ≤ e.1.ncard) →
      H.EdgeColorable (n - n / b ^ 4) ∨
        ∃ S W : Finset H, ∃ r : ℕ,
          S.Nonempty ∧ W ⊆ S ∧ b ^ 4 ≤ r ∧
          IsDenseCore H.lineGraph S (n - n / b ^ 4) ∧
          IsPeelableOutside H.lineGraph univ S (n - n / b ^ 4) ∧
          projectiveScale n - projectiveScale n / t ≤ r ∧
          (∀ e ∈ S, r ≤ e.1.ncard) ∧ (∀ e ∈ W, e.1.ncard ≤ r + r / b) ∧
          (b - 10) * n ^ 2 ≤ b * (∑ e ∈ W, e.1.ncard * (e.1.ncard - 1)) := by
  classical
  obtain ⟨q, hq, N₀, _, hN₀⟩ := eventually_edgeColorable_of_subprojective_window (8 * t) (by omega)
  let s := 16 * q
  let C := 32 * s ^ 2 * (1 + 4 * s * (1 + 4 * s))
  let b := max (8 * t + B₀) (max (32 * q) (10 * C + 1))
  have hbt : 8 * t ≤ b := (Nat.le_add_right _ _).trans (le_max_left _ _)
  have hb8192 : 8192 ≤ b := by omega
  have hbB₀ : B₀ ≤ b := (Nat.le_add_left _ _).trans (le_max_left _ _)
  have hbq : 32 * q ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have hbC : 10 * C < b := lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_right _ _).trans (le_max_right _ _))
  have hb2 : b ≤ b ^ 2 := by nlinarith only [hb8192]
  have hb4 : b ^ 2 ≤ b ^ 4 := by nlinarith only [Nat.mul_le_mul hb2 hb2]
  have hbmin : 4 * s + 1 ≤ b ^ 4 := by
    dsimp only [s]
    nlinarith only [hb8192, hbq, hb4]
  have hbproj : 8 * t + 1 ≤ b ^ 4 := by nlinarith only [hbt, hb8192, hb4]
  have hs : 1 ≤ s := by dsimp only [s]; omega
  let N := max N₀ (max (b ^ 4) (max (5 * s) ((64 * t) * (64 * t) + 64 * t + 2)))
  refine ⟨b, hbt, hbB₀, N, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro n hn H hlinear hmin
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hnb : b ^ 4 ≤ n := ((le_max_left _ _).trans (le_max_right _ _)).trans hn
  have hns : 5 * s ≤ n := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hn
  have hnproj : (64 * t) * (64 * t) + 64 * t + 2 ≤ n :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hn
  have hkproj := projectiveScale_ge_of_large_card (64 * t) n hnproj
  have hcore := H.large_edge_colorable_or_concentrated_core hlinear b (by omega)
    (by simpa only [Fintype.card_fin] using hnb) hmin
  simp only [Fintype.card_fin] at hcore
  rcases hcore with hcolor | ⟨S, W, r, hS, hWS, hr, hdense, hpeel, hminS, hmaxW, hvolume⟩
  · exact Or.inl hcolor
  by_cases hprojective : projectiveScale n - projectiveScale n / t ≤ r
  · exact Or.inr ⟨S, W, r, hS, hWS, hr, hdense, hpeel, hprojective, hminS, hmaxW, hvolume⟩
  left
  let J := H.restrictEdges (W : Set H)
  have hJmin (e : J) : r ≤ e.1.ncard := by
    obtain ⟨f, hf, hfe⟩ := e.2
    rw [← hfe]
    exact hminS f (hWS hf)
  have hJmax (e : J) : e.1.ncard ≤ r + r / b := by
    obtain ⟨f, hf, hfe⟩ := e.2
    rw [← hfe]
    exact hmaxW f hf
  have hwidth : r + r / b ≤ r + r / (16 * q) :=
    Nat.add_le_add_left (Nat.div_le_div_left (show 16 * q ≤ b by omega) (by omega)) r
  have hgap := subprojective_window_gap_parametric n r b t ht hkproj hbt (Nat.lt_of_not_ge hprojective)
  have hJcolor := hN₀ n hn₀ J (H.restrictEdges_linear hlinear _) r (r + r / b)
    (by omega) (by omega) hJmin hJmax hwidth hgap
  have hfull := H.edgeColorable_of_high_volume_window hlinear W b s (n - n / (2 * q))
    (by omega) hs (by simpa only [Fintype.card_fin] using hns)
    (fun e ↦ hbmin.trans (hmin e)) hbC (by simpa only [Fintype.card_fin] using hvolume) hJcolor
  have hfull' : H.EdgeColorable ((n - n / (2 * q)) + 2 * n / (16 * q)) := by
    simpa only [Fintype.card_fin, s] using hfull
  have hsmall := hfull'.mono (high_volume_palette_saving n q hq)
  apply hsmall.mono
  apply Nat.sub_le_sub_left
  exact Nat.div_le_div_left (show 4 * q ≤ b ^ 4 by omega) (by omega)


/-- Fixed-gap version retained for the large-edge coloring theorem. -/
theorem eventually_large_edge_saving_or_projective_core (B₀ : ℕ) :
    ∃ b : ℕ, 8192 ≤ b ∧ B₀ ≤ b ∧ ∃ N : ℕ, b ^ 4 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ H : SetHypergraph (Fin n), H.IsLinear → (∀ e : H, b ^ 4 ≤ e.1.ncard) →
      H.EdgeColorable (n - n / b ^ 4) ∨
        ∃ S W : Finset H, ∃ r : ℕ,
          S.Nonempty ∧ W ⊆ S ∧ b ^ 4 ≤ r ∧
          IsDenseCore H.lineGraph S (n - n / b ^ 4) ∧
          IsPeelableOutside H.lineGraph univ S (n - n / b ^ 4) ∧
          projectiveScale n - projectiveScale n / 1024 ≤ r ∧
          (∀ e ∈ S, r ≤ e.1.ncard) ∧ (∀ e ∈ W, e.1.ncard ≤ r + r / b) ∧
          (b - 10) * n ^ 2 ≤ b * (∑ e ∈ W, e.1.ncard * (e.1.ncard - 1)) := by
  simpa only [Nat.reduceMul] using
    eventually_large_edge_saving_or_projective_core_parametric 1024 (by norm_num) B₀

#print axioms eventually_large_edge_saving_or_projective_core_parametric
#print axioms eventually_large_edge_saving_or_projective_core

end Erdos19.SetHypergraph
