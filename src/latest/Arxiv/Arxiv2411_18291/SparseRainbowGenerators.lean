import Arxiv.Arxiv2411_18291.TypicalRainbowExtensions
import Arxiv.Arxiv2411_18291.SparseModularGenerators
import Arxiv.Arxiv2411_18291.ColouredGenerators

/-!
# Sparse generators with simultaneous rainbow pattern extensions

The host, good edges, generators, and colour permutations are all constructed.
The fixed pattern can be a punctured clique or the nonroot part of an
exchange. Monochromatic unsaturated cliques are generated; generation of
every rainbow clique requires the further frame argument.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W]

theorem eventually_sparse_host_rainbow_extensions (F : Finset W) {r : ℕ}
    (E : Hypergraph W (r + 1)) (hroot : ∀ e ∈ E, ¬e.val ⊆ F) (h : ℕ)
    (hh : 1 ≤ h) (hEh : E.card ≤ h) {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 4) :
    ∃ L : ℕ, ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h →
      (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K →
      ∀ G : Hypergraph (Fin n) (r + 1), G ⊆ K →
      ((K \ G).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card →
      ∃ σ : Option (Fin L × E) → Equiv.Perm (Fin n), ∀ φ : F ↪ Fin n,
        (3 / 8 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) <
          (rainbowExtensions φ E σ G).card := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hα1 : α ≤ 1 / 4 := by nlinarith only [hhR, hαh, hα]
  have hE : α * E.card ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hEh) hα.le).trans hαh
  obtain ⟨L, hL⟩ := exists_trial_number F.card (by positivity : (0 : ℝ) < α / 100)
  refine ⟨L, eventually_many_rainbow_extensions F E hroot h L hh (b := 1 / 2)
    (α := α) (δ := 1 / 10) (τ := α / 10) (γ := α / 50) (χ := α / 25) (κ := α / 100)
    (by norm_num) (by positivity) (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) hL⟩

theorem eventually_exists_sparse_rainbow_generators (F : Finset W) {r : ℕ}
    (E : Hypergraph W (r + 1)) (hroot : ∀ e ∈ E, ¬e.val ⊆ F) (q h N : ℕ)
    (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h) (hqr : r + 1 ≤ q) (hEh : E.card ≤ h)
    {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 4) :
    ∃ L : ℕ, ∀ᶠ n : ℕ in atTop, ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-α)| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-α) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators (2 ^ q * (n : ℝ) ^ (-(7 * α / 10))) ∧
        C.generators.card ≤ N * K.card ∧
        (C.saturated.card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * (cliqueFamily K q).card ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card ∧
        (∀ e ∈ C.good,
          |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
            cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
            (n : ℝ) ^ (-(α / 10)) * cliqueMainTerm n (density K) q (r + 1) (r + 1)) ∧
        ∃ σ : Option (Fin L × E) → Equiv.Perm (Fin n),
          IsCliqueFamilyBounded r (permutedUnion σ C.generators)
            (((L * E.card + 1 : ℕ) : ℝ) * (2 ^ q * (n : ℝ) ^ (-(7 * α / 10)))) ∧
          (∀ Q ∈ permutedUnion σ ((cliqueFamily K q) \ C.saturated),
            modularCliqueVector N (r + 1) Q ∈ generatedSubgroup
              (modularCliqueVector N (r + 1)) (permutedUnion σ C.generators)) ∧
          ∀ φ : F ↪ Fin n,
            (3 / 8 : ℝ) * density C.good ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) <
              (rainbowExtensions φ E σ C.good).card := by
  classical
  have hh : 1 ≤ h := (Nat.succ_le_iff.mpr (Nat.choose_pos hqr)).trans hqh
  obtain ⟨L, hL⟩ := eventually_sparse_host_rainbow_extensions F E hroot h hh hEh hα hαh
  have hsmall := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨L, ?_⟩
  filter_upwards [eventually_exists_sparse_modular_generators q r h N hN hqh hqr hα
    (by linarith), hL, hsmall] with n hgen hcol hsn
  obtain ⟨K, hT, hd, C, hCb, hCs, hSat, hGood, hNear⟩ := hgen
  have hp0 := Real.rpow_nonneg (Nat.cast_nonneg n) (-α)
  have hlo := (abs_le.mp hd).1
  have hsmall' : (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 / 2 := hsn.le
  have hm := mul_le_mul_of_nonneg_right hsmall' hp0
  have hdlo : (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K := by
    linarith only [hlo, hm]
  obtain ⟨σ, hσ⟩ := hcol K hT hdlo C.good C.good_subset hGood
  refine ⟨K, hT, hd, C, hCb, hCs, hSat, hGood, hNear, σ, ?_, ?_, hσ⟩
  · simpa only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe] using hCb.permutedUnion σ
  · exact fun Q hQ => C.permuted_generates σ hQ

end Arxiv2411_18291
