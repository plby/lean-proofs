import ErdosProblems.Erdos19.DilutedTailBudget
import ErdosProblems.Erdos19.NonadjacentPairs

/-! # Coloring graphs with locally sparse neighborhoods

The proof uses one diluted random round, elementary deletion certificates,
finite bounded differences, and the finite product local lemma.
-/

namespace Erdos19

attribute [local instance] Classical.propDecidable

theorem eventually_colorable_of_nonadjacent_neighbor_pairs (h : ℕ) (hh : 1 ≤ h) :
    ∃ L : ℕ, 16 ≤ L ∧ ∃ N : ℕ, 2 * L ≤ N ∧ ∀ D : ℕ, N ≤ D →
      ∀ (V : Type*) [Fintype V], ∀ G : _root_.SimpleGraph V,
      (∀ v, (G.neighborSet v).ncard ≤ D) →
      (∀ v, D ^ 2 ≤ h * (nonadjacentNeighborPairGraph G v).edgeSet.ncard) →
      G.Colorable (D + 1 - D / L) := by
  classical
  let A := 10000 * h
  let L := 16 * h * A ^ 2
  have hA4 : 4 ≤ A := by dsimp only [A]; omega
  have hApos : 0 < A := by omega
  have hL16 : 16 ≤ L := by
    have h₁ : 16 ≤ 16 * h := by omega
    have h₂ : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ hApos
    exact (by simpa only [mul_one] using Nat.mul_le_mul h₁ h₂)
  have hLpos : 0 < L := by omega
  obtain ⟨N, hNL, hN⟩ := exists_diluted_tail_budget L hL16
  refine ⟨L, hL16, N, hNL, ?_⟩
  intro D hDN V _ G hdegree hpairs
  have hD₂ : 2 * L ≤ D := hNL.trans hDN
  have hDpos : 0 < D := by omega
  let t := D / L
  let k := D + 1 - t
  obtain ⟨ht2, hkpos, hkD, hDk, hambient, _⟩ := diluted_basic_parameters D L hL16 hD₂
  by_cases hsmall : Fintype.card V ≤ k
  · exact _root_.SimpleGraph.Colorable.mono hsmall G.colorable_of_fintype
  have hmin (v : V) : 2 ≤ (G.neighborSet v).ncard := by
    apply two_le_neighbor_ncard_of_nonadjacentPair G v
    have hp := hpairs v
    have hsq : 0 < D ^ 2 := by positivity
    have hprod : 0 < h * (nonadjacentNeighborPairGraph G v).edgeSet.ncard := hsq.trans_le hp
    exact Nat.pos_of_mul_pos_left hprod
  have hupper (v : V) : (nonadjacentNeighborPairGraph G v).edgeSet.ncard ≤ D ^ 2 :=
    (nonadjacentNeighborPairs_ncard_le_sq G v).trans (Nat.pow_le_pow_left (hdegree v) 2)
  have hA1024 : 1024 * h ≤ A := Nat.mul_le_mul_right h (by norm_num)
  have hmean (v : V) : 6 * A ^ 2 * k * t ≤ (nonadjacentNeighborPairGraph G v).edgeSet.ncard :=
    diluted_mean_parameter_bound h A D k t _ (by omega) hkD (Nat.mul_div_le D L) (hpairs v)
  have hdelete (v : V) : 8 * k * (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * D) ≤
      (t + 1) * (A * k) ^ 3 :=
    diluted_deletion_parameter_bound h A D k t _ hA1024 (hupper v) hDk
      (Nat.lt_mul_div_succ D hLpos).le
  have hpalette : 2 * D ≤ A * k := by
    calc
      2 * D ≤ 4 * k := by omega
      _ ≤ A * k := Nat.mul_le_mul_right k hA4
  apply colorable_of_diluted_tail_parameters G (A := A) (k := k) (Δ := D)
    (t := t) (a := 2 * t) (b := t) ⟨0, hApos⟩ hkpos hdegree hmin
    (by dsimp only [k]; omega) (by omega) hpalette (by omega) hdelete
    (t : ℝ) (by positivity)
  · intro v
    have hAR : (0 : ℝ) < A := by exact_mod_cast hApos
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    have hmeanR : (6 : ℝ) * A ^ 2 * k * t ≤
        (nonadjacentNeighborPairGraph G v).edgeSet.ncard := by exact_mod_cast hmean v
    apply (le_div_iff₀ (by positivity)).mpr
    push_cast
    nlinarith only [hmeanR]
  · intro v
    have hdcard : Fintype.card (G.neighborFinset v) = (G.neighborSet v).ncard := by
      simp only [Fintype.card_coe, G.card_neighborFinset_eq_degree,
        ← G.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard]
    rw [hdcard]
    have hden : (2 : ℝ) * (G.neighborSet v).ncard * (2 : ℝ) ^ 2 =
        8 * (G.neighborSet v).ncard := by ring
    rw [hden]
    exact hN D hDN _ (by have hv := hmin v; omega) (hdegree v)

#print axioms eventually_colorable_of_nonadjacent_neighbor_pairs

theorem eventually_colorable_with_fractional_saving (h : ℕ) (hh : 1 ≤ h) :
    ∃ q : ℕ, 0 < q ∧ ∃ N : ℕ, q ≤ N ∧ ∀ D : ℕ, N ≤ D →
      ∀ (V : Type*) [Fintype V], ∀ G : _root_.SimpleGraph V,
      (∀ v, (G.neighborSet v).ncard ≤ D) →
      (∀ v, D ^ 2 ≤ h * (nonadjacentNeighborPairGraph G v).edgeSet.ncard) →
      G.Colorable (D - D / q) := by
  obtain ⟨L, hL, N, hN, hcolor⟩ := eventually_colorable_of_nonadjacent_neighbor_pairs h hh
  refine ⟨2 * L, by omega, N, hN, ?_⟩
  intro D hD V _ G hdegree hpairs
  have ht : 2 ≤ D / L := (diluted_basic_parameters D L hL (hN.trans hD)).1
  have hdiv : D / (2 * L) = D / L / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm L 2]
  have hpalette : D + 1 - D / L ≤ D - D / (2 * L) := by
    rw [hdiv]
    have hle := Nat.div_le_self D L
    omega
  exact _root_.SimpleGraph.Colorable.mono hpalette (hcolor D hD V G hdegree hpairs)

#print axioms eventually_colorable_with_fractional_saving

end Erdos19
