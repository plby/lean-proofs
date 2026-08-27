import Arxiv.Arxiv2411_18291.AsymptoticModularGenerators
import Arxiv.Arxiv2411_18291.TypicalDensityScales

/-!
# Existence of a sparse modular generating system

This constructs the graph as well as its generators, saturated cliques,
and good edges. The conclusion uses the observed graph density in its
clique main term and an eventual size threshold.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_exists_good_modular_generators (q r h N : ℕ)
    (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h) (hqr : r + 1 ≤ q)
    {α δ s t : ℝ} (hα : 0 ≤ α) (ht : 0 < t) (htδ : t < δ)
    (hs : s < 1) (hgap : s + 2 * t < α) (htyp : α * h + 2 * δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-δ)) h ∧
      |density K - (n : ℝ) ^ (-α)| ≤ (n : ℝ) ^ (-δ) * (n : ℝ) ^ (-α) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators (2 ^ q * (n : ℝ) ^ (-s)) ∧
        C.generators.card ≤ N * K.card ∧
        (C.saturated.card : ℝ) ≤ (n : ℝ) ^ (-t) * (cliqueFamily K q).card ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-t) * K.card ∧
        ∀ e ∈ C.good,
          |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
            cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
            (n : ℝ) ^ (-t) * cliqueMainTerm n (density K) q (r + 1) (r + 1) := by
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr)).trans hqh
  have hδ : 0 < δ := ht.trans htδ
  have hcount : α * q.choose (r + 1) + δ < 1 := by
    have hle := mul_le_mul_of_nonneg_left (show (q.choose (r + 1) : ℝ) ≤ h by
      exact_mod_cast hqh) hα
    linarith
  filter_upwards [eventually_exists_typicalGraph_density_scale r h hh hα hδ htyp,
    eventually_good_modular_generating_data q r h N hN hqh hqr
      (b := 1 / 2) (B := 2) (by norm_num) ht htδ hs hgap hcount] with n hKn hGn
  obtain ⟨K, hT, hd, hlo, hhi⟩ := hKn
  exact ⟨K, hT, hd, hGn K hT hlo hhi⟩

theorem eventually_exists_sparse_modular_generators (q r h N : ℕ)
    (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h) (hqr : r + 1 ≤ q)
    {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-α)| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-α) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators (2 ^ q * (n : ℝ) ^ (-(7 * α / 10))) ∧
        C.generators.card ≤ N * K.card ∧
        (C.saturated.card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * (cliqueFamily K q).card ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card ∧
        ∀ e ∈ C.good,
          |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
            cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
            (n : ℝ) ^ (-(α / 10)) * cliqueMainTerm n (density K) q (r + 1) (r + 1) := by
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr)).trans hqh
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hα1 : α ≤ 1 / 2 := by nlinarith
  exact eventually_exists_good_modular_generators q r h N hN hqh hqr hα.le
    (by positivity) (by linarith) (by linarith) (by linarith) (by linarith)

end Arxiv2411_18291
