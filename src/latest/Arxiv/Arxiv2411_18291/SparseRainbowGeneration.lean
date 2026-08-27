import Arxiv.Arxiv2411_18291.RainbowModularGeneration
import Arxiv.Arxiv2411_18291.SparseModularGenerators

/-!
# A constructed sparse family generating the original rainbow cliques

The host and modular generators are constructed before choosing the initial
colours. Adding finitely many permuted copies generates every rainbow
clique for those initial colours. The boundary bound loses only a fixed
factor, independent of the ambient size.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {J I V : Type*}

def augmentedPermutation (σ : J → Equiv.Perm V) (τ : I → Equiv.Perm V) :
    Option (J ⊕ I) → Equiv.Perm V :=
  fun i => i.elim (Equiv.refl V) (Sum.elim σ τ)

theorem permutedUnion_union_subset_augmented [Fintype J] [Fintype I]
    [DecidableEq V] (σ : J → Equiv.Perm V) (τ : I → Equiv.Perm V)
    {q : ℕ} (D : Finset (Block V q)) :
    permutedUnion σ D ∪ permutedUnion τ D ⊆ permutedUnion (augmentedPermutation σ τ) D := by
  intro Q hQ
  rcases mem_union.mp hQ with hσ | hτ
  · obtain ⟨j, P, hP, hPQ⟩ := (mem_permutedUnion σ D Q).mp hσ
    exact (mem_permutedUnion _ D Q).mpr ⟨some (Sum.inl j), P, hP, hPQ⟩
  · obtain ⟨i, P, hP, hPQ⟩ := (mem_permutedUnion τ D Q).mp hτ
    exact (mem_permutedUnion _ D Q).mpr ⟨some (Sum.inr i), P, hP, hPQ⟩

variable {W : Type*} [Fintype J] [Fintype W] [DecidableEq W] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)}

theorem eventually_exists_rainbow_generating_family (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (h N : ℕ) (hN : 0 < N) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h) {α : ℝ} (hα : 0 < α) (hαh : α * h ≤ 1 / 12) :
    ∃ L : ℕ, ∀ᶠ n : ℕ in atTop, ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K ∧
      |density K - (n : ℝ) ^ (-α)| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-α) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators (2 ^ q * (n : ℝ) ^ (-(7 * α / 10))) ∧
        ((K \ C.good).card : ℝ) ≤ (n : ℝ) ^ (-(α / 10)) * K.card ∧
        ∀ σ : J → Equiv.Perm (Fin n),
        ∃ ρ : Option (J ⊕ (Fin L × S.farCliques)) → Equiv.Perm (Fin n),
          IsCliqueFamilyBounded r (permutedUnion ρ C.generators)
            (((Fintype.card J + L * S.farCliques.card + 1 : ℕ) : ℝ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * α / 10)))) ∧
          (∀ Q ∈ permutedUnion σ C.generators, Q ∈ permutedUnion ρ C.generators) ∧
          ∀ Q : Block (Fin n) q,
            IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
            modularCliqueVector N (r + 1) Q ∈ generatedSubgroup
              (modularCliqueVector N (r + 1)) (permutedUnion ρ C.generators) := by
  classical
  obtain ⟨L, hL⟩ := eventually_sparse_host_rainbow_generation (J := J) (N := N)
    hA hqr h hqh hSh hα hαh
  have hsmall := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨L, ?_⟩
  filter_upwards [eventually_exists_sparse_modular_generators q r h N hN hqh hqr.le hα
    (by linarith only [hαh]), hL, hsmall] with n hgen hcol hsn
  obtain ⟨K, hT, hd, C, hCb, _, hsat, hgood, hcount⟩ := hgen
  have hp0 := Real.rpow_nonneg (Nat.cast_nonneg n) (-α)
  have hlo := (abs_le.mp hd).1
  have hs : (n : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 / 2 := hsn.le
  have hm := mul_le_mul_of_nonneg_right hs hp0
  have hdlo : (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K := by
    linarith only [hlo, hm]
  refine ⟨K, hT, hdlo, hd, C, hCb, hgood, fun σ => ?_⟩
  obtain ⟨τ, hτ⟩ := hcol K hT hdlo C hsat (fun e he => (hcount e he).le) σ
  let ρ := augmentedPermutation σ τ
  have hsub := permutedUnion_union_subset_augmented σ τ C.generators
  refine ⟨ρ, ?_, fun Q hQ => hsub (mem_union_left _ hQ), fun Q hQ => ?_⟩
  · simpa only [Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe] using hCb.permutedUnion ρ
  · exact generatedSubgroup_mono _ hsub (hτ Q hQ)

end Arxiv2411_18291
