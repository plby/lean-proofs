import ErdosProblems.Erdos1010.CrossTriangles
import ErdosProblems.Erdos1010.ImbalanceOne

/-! # The exact triangle supersaturation theorem for every even order -/

open Finset

namespace Erdos1010

open Bipartite

theorem even_triangles {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {r t : ℕ}
    (hn : Fintype.card V = 2 * r) (ht : t < r)
    (hm : G.edgeFinset.card = r ^ 2 + t) : r * t ≤ (G.cliqueFinset 3).card := by
  classical
  by_contra! hT
  have hTz : ((G.cliqueFinset 3).card : ℤ) < (r : ℤ) * t := by exact_mod_cast hT
  have hnz : (Fintype.card V : ℤ) = 2 * r := by exact_mod_cast hn
  have hmz : (G.edgeFinset.card : ℤ) = (r : ℤ) ^ 2 + t := by exact_mod_cast hm
  have htz : (t : ℤ) < r := by exact_mod_cast ht
  have hrpos : (0 : ℤ) < r := by omega
  obtain ⟨S, hmax, hsmall, hmin⟩ := exists_min_imbalance_maximum_cut G
  let s : ℤ := (r : ℤ) - S.card
  let HA := G.induce (S : Set V)
  let HB := G.induce ((Sᶜ : Finset V) : Set V)
  let M := missingCross G S
  let D : ℤ := M.card
  let x : ℤ := HA.edgeFinset.card
  let y : ℤ := HB.edgeFinset.card
  let C : ℤ := cutCharge HA HB M
  have hpart := card_add_card_compl S
  have hs : 0 ≤ s := by dsimp [s]; omega
  have hAcard : (S.card : ℤ) = r - s := by dsimp [s]; ring
  have hBcard : (Sᶜ.card : ℤ) = r + s := by dsimp [s]; omega
  have hproduct : (cutSize G S : ℤ) + D = ((r : ℤ) - s) * (r + s) := by
    have h : (cutSize G S : ℤ) + (missingCross G S).card = (S.card : ℤ) * Sᶜ.card := by
      exact_mod_cast cutSize_add_missingCross G S
    rw [hAcard, hBcard] at h
    exact h
  have hdefect := maximum_cut_defect_lt G S r t hrpos hnz hmz hmax hTz
  have hR : s ^ 2 + D < t := by nlinarith only [hproduct, hdefect]
  have hrCharge : D + s ^ 2 + 2 ≤ r := by omega
  have hedge : x + y + cutSize G S = (r : ℤ) ^ 2 + t := by
    have h : ((G.induce (S : Set V)).edgeFinset.card : ℤ) +
        (G.induce ((Sᶜ : Finset V) : Set V)).edgeFinset.card + cutSize G S = G.edgeFinset.card := by
      exact_mod_cast cut_induced_edge_partition G S
    rw [hmz] at h
    exact h
  have hsum : x + y = (t : ℤ) + (s ^ 2 + D) := by nlinarith only [hedge, hproduct]
  have hsumMul := congrArg (fun z : ℤ ↦ (r : ℤ) * z) hsum
  have hq : x + y ≤ (r : ℤ) + D + s ^ 2 - 1 := by omega
  have hcross : ((r : ℤ) + s) * x + ((r : ℤ) - s) * y ≤ (G.cliqueFinset 3).card + C := by
    have h := cross_triangle_lower_bound_induced G S
    rw [hAcard, hBcard] at h
    exact h
  have hcapA : ∀ a, (HA.degree a : ℤ) + leftDegree M a ≤ (r : ℤ) + s := by
    intro a
    have h : ((G.induce (S : Set V)).degree a : ℤ) + leftDegree (missingCross G S) a ≤ Sᶜ.card := by
      exact_mod_cast maximum_cut_left_cap G S hmax a
    rw [hBcard] at h
    exact h
  by_cases hs0 : s = 0
  · have hcapB : ∀ b, (HB.degree b : ℤ) + rightDegree M b ≤ (r : ℤ) := by
      intro b
      have h : ((G.induce ((Sᶜ : Finset V) : Set V)).degree b : ℤ) +
          rightDegree (missingCross G S) b ≤ S.card := by exact_mod_cast maximum_cut_right_cap G S hmax b
      rw [hAcard, hs0] at h
      simpa using h
    have hc := balanced_sparse_charge HA HB M r (by simpa [hs0] using hrCharge)
      (by simpa [hs0] using hq) (fun a ↦ by simpa [hs0] using hcapA a) hcapB
    change C ≤ (r : ℤ) * D at hc
    rw [hs0] at hcross hsumMul
    nlinarith only [hcross, hsumMul, hc, hTz]
  · have hs1 : 1 ≤ s := by omega
    have hgap : S.card + 2 ≤ Sᶜ.card := by omega
    have hcapB : ∀ b, (HB.degree b : ℤ) + rightDegree M b ≤ (r : ℤ) - s - 1 := by
      intro b
      have h : ((G.induce ((Sᶜ : Finset V) : Set V)).degree b : ℤ) +
          rightDegree (missingCross G S) b < S.card := by
        exact_mod_cast minimum_imbalance_right_cap G S hmax hmin hgap b
      rw [hAcard] at h
      dsimp [HB, M]
      omega
    have hc := unbalanced_sparse_charge HA HB M r s hs1 hrCharge hq hcapA hcapB
    change C + s * (y - x) ≤ (r : ℤ) * (D + s ^ 2) at hc
    nlinarith only [hcross, hsumMul, hc, hTz]

end Erdos1010
