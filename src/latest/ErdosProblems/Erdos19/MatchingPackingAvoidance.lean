import ErdosProblems.Erdos19.EventualPrescribedPacking
import ErdosProblems.Erdos19.ParityTargets
import ErdosProblems.Erdos19.MatchingFamilyDegrees

/-! # Dense matching packing avoiding prescribed covered sets -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem eventually_matching_packing_avoiding (zeta : ℝ) (hzeta : 0 < zeta) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : _root_.SimpleGraph (Fin n),
      (∀ v, (1 - delta) * n ≤ (G.degree v : ℝ)) →
      ∀ m : ℕ, (m : ℝ) ≤ (1 - zeta) * n →
      ∀ U : Set (Fin n), ∀ C : Fin m → Set (Fin n),
      (∀ i, C i ⊆ U) → (∀ i, m + (C i).ncard ≤ U.ncard) →
      (∀ i, ((C i).ncard : ℝ) ≤ delta * n) →
      (∀ v, ((∑ i : Fin m, (if v ∈ C i then 1 else 0) : ℕ) : ℝ) ≤ delta * n) →
      ∃ M : Fin m → G.Subgraph,
        (∀ i, (M i).IsMatching ∧ (M i).verts ⊆ (C i)ᶜ) ∧
        Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
        (∀ v, (∑ i : Fin m, if v ∈ (M i).verts then 0 else 1) ≤
          (∑ i : Fin m, if v ∈ C i then 1 else 0) + if v ∈ U then 1 else 0) := by
  classical
  obtain ⟨delta₀, hd₀, N₀, hN₀⟩ := eventually_prescribed_matching_packing_fin zeta hzeta
  let delta := delta₀ / 2
  have hd : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (1 / delta)
  refine ⟨delta, hd, max N₀ N₁, ?_⟩
  intro n hn G hG m hm U C hCU hroom hsmall habs
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hN₁n : (N₁ : ℝ) ≤ n := by exact_mod_cast (le_max_right N₀ N₁).trans hn
  have hunit : 1 ≤ delta * n := by
    have h : 1 / delta ≤ (n : ℝ) := (hN₁.trans_le hN₁n).le
    have h' := (div_le_iff₀ hd).mp h
    nlinarith only [h']
  have hrel : delta₀ * n = delta * n + delta * n := by dsimp only [delta]; ring
  have hG₀ : ∀ v, (1 - delta₀) * n ≤ (G.degree v : ℝ) := by
    intro v
    have hv := hG v
    have hdnonneg := mul_nonneg hd.le hnR
    nlinarith only [hv, hrel, hdnonneg]
  obtain ⟨A, hA, hAcnt⟩ := exists_even_targets_with_distinct_corrections U C hCU
    (fun i ↦ by simpa only [Fintype.card_fin] using hroom i)
  have hsmallA : ∀ i, ((A i)ᶜ.ncard : ℝ) ≤ delta₀ * n := by
    intro i
    have h : ((A i)ᶜ.ncard : ℝ) ≤ (C i).ncard + 1 := by exact_mod_cast (hA i).2.2.2
    have hs := hsmall i
    nlinarith only [h, hs, hunit, hrel]
  have habsA : ∀ v, ((∑ i : Fin m, (if v ∈ A i then 0 else 1) : ℕ) : ℝ) ≤ delta₀ * n := by
    intro v
    have hnat : (∑ i : Fin m, if v ∈ A i then 0 else 1) ≤
        (∑ i : Fin m, if v ∈ C i then 1 else 0) + 1 := by
      have h := hAcnt v
      split_ifs at h <;> omega
    have h : ((∑ i : Fin m, (if v ∈ A i then 0 else 1) : ℕ) : ℝ) ≤
        (∑ i : Fin m, (if v ∈ C i then 1 else 0) : ℕ) + 1 := by exact_mod_cast hnat
    have hv := habs v
    nlinarith only [h, hv, hunit, hrel]
  obtain ⟨M, hM, hdis⟩ := hN₀ n ((le_max_left _ _).trans hn) G hG₀ m hm A
    (fun i ↦ (hA i).1) hsmallA habsA
  refine ⟨M, fun i ↦ ⟨(hM i).1, (hM i).2 ▸ (hA i).2.1⟩, hdis, ?_⟩
  intro v
  simpa only [fun i ↦ (hM i).2] using hAcnt v

#print axioms eventually_matching_packing_avoiding

end Erdos19
