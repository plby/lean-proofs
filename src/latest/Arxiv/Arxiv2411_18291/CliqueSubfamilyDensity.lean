import Arxiv.Arxiv2411_18291.AsymptoticCliqueCount
import Arxiv.Arxiv2411_18291.TypicalPermutationPairs
import Arxiv.Arxiv2411_18291.GoodSubgraphDensity

/-!
# Marginal density of an almost complete clique family

The lower clique count is normalized by the exact binomial denominator.
Removing a small fraction of cliques contributes only its relative loss
to the marginal probability used by the colour experiment.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem cliqueFamily_density_lower (K : Hypergraph V (r + 1)) (hqn : q ≤ Fintype.card V)
    {ε : ℝ} (hε : ε ≤ 1)
    (hcount : |((cliqueFamily K q).card : ℝ) -
      cliqueMainTerm (Fintype.card V) (density K) q (r + 1) 0| ≤
        ε * cliqueMainTerm (Fintype.card V) (density K) q (r + 1) 0) :
    (1 - ε) * density K ^ q.choose (r + 1) ≤ density (cliqueFamily K q) := by
  have hN : (0 : ℝ) < (Fintype.card V).choose q := by exact_mod_cast Nat.choose_pos hqn
  have hlow := (abs_le.mp hcount).1
  rw [cliqueMainTerm_small_root _ _ _ _ _ (Nat.succ_pos r), Nat.sub_zero] at hlow
  have hchoose : ((Fintype.card V).choose q : ℝ) ≤
      (Fintype.card V : ℝ) ^ q / q.factorial := Nat.choose_le_pow_div q (Fintype.card V)
  have hcoef : 0 ≤ (1 - ε) * density K ^ q.choose (r + 1) :=
    mul_nonneg (sub_nonneg.mpr hε) (pow_nonneg (density_nonneg K) _)
  change (1 - ε) * density K ^ q.choose (r + 1) ≤
    ((cliqueFamily K q).card : ℝ) / ((Fintype.card V).choose q : ℝ)
  rw [le_div_iff₀ hN]
  calc
    _ ≤ ((1 - ε) * density K ^ q.choose (r + 1)) *
        ((Fintype.card V : ℝ) ^ q / q.factorial) := mul_le_mul_of_nonneg_left hchoose hcoef
    _ ≤ _ := by nlinarith only [hlow]

theorem clique_subfamily_density_lower (K : Hypergraph V (r + 1))
    (D : Finset (Block V q)) (hD : D ⊆ cliqueFamily K q) (hqn : q ≤ Fintype.card V)
    {ε : ℝ} (hε1 : ε ≤ 1)
    (hcount : |((cliqueFamily K q).card : ℝ) -
      cliqueMainTerm (Fintype.card V) (density K) q (r + 1) 0| ≤
        ε * cliqueMainTerm (Fintype.card V) (density K) q (r + 1) 0)
    (hloss : (((cliqueFamily K q) \ D).card : ℝ) ≤ ε * (cliqueFamily K q).card) :
    (1 - 2 * ε) * density K ^ q.choose (r + 1) ≤ density D := by
  have hgood := (abs_le.mp (density_subgraph_error hD hloss)).1
  have hbase := cliqueFamily_density_lower K hqn hε1 hcount
  have hmul := mul_le_mul_of_nonneg_left hbase (sub_nonneg.mpr hε1)
  have hp := mul_nonneg (sq_nonneg ε) (pow_nonneg (density_nonneg K) (q.choose (r + 1)))
  nlinarith only [hgood, hmul, hp]

theorem eventually_cliqueFamily_relative_error (q r h : ℕ) (hqh : q.choose (r + 1) ≤ h)
    {b α δ κ : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hκδ : κ < δ)
    (hgap : α * q.choose (r + 1) + δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-δ)) h → b * (n : ℝ) ^ (-α) ≤ density K →
      |((cliqueFamily K q).card : ℝ) - cliqueMainTerm n (density K) q (r + 1) 0| ≤
        (n : ℝ) ^ (-κ) * cliqueMainTerm n (density K) q (r + 1) 0 := by
  filter_upwards [eventually_rootedClique_relative_error q r h hqh hb hδ hκδ hgap]
    with n hn
  intro K hT hd
  let E : Block (Fin n) 0 := ⟨∅, card_empty⟩
  have hE : cliqueEdges (r + 1) E ⊆ K := by
    rw [cliqueEdges_empty_of_small E (Nat.succ_pos r)]
    exact empty_subset K
  have hc := hn K hT hd 0 E (Nat.zero_le q)
  rw [rootedCliques_eq_filter_cliqueFamily K E hE] at hc
  simpa only [E, empty_subset, filter_true] using hc

end Arxiv2411_18291
