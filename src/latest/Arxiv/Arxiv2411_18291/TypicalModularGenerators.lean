import Arxiv.Arxiv2411_18291.ModularGeneratingData
import Arxiv.Arxiv2411_18291.CliqueCountEstimates

/-!
# Modular generators and a good subgraph inside a typical graph

Combine precise clique counts with bounded modular selection and removal
of heavy edges. This gives the complete finite construction behind
`lem:KSG`, with explicit numerical error and deletion bounds. Substitution
of the paper's polynomial thresholds is a separate asymptotic step.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r h : ℕ}

theorem exists_typical_modular_generating_data (N : ℕ) (hN : 0 < N)
    {K : Hypergraph V (r + 1)} {c η θ τ : ℝ}
    (hT : IsTypical K c h) (hqh : q.choose (r + 1) ≤ h) (hqr : r + 1 ≤ q)
    (hcη : c ≤ η) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hsize : (q : ℝ) ≤ (η - c) * (Fintype.card V * density K ^ q.choose (r + 1)))
    (cap : ℕ) (hcap : 0 < cap) (hτ : 0 < τ)
    (hθ : ((q - r : ℕ) : ℝ) * cap < θ * Fintype.card V) :
    let ε : ℝ := η * q * 2 ^ q
    let L : ℝ := (1 + ε) * cliqueMainTerm (Fintype.card V) (density K) q (r + 1) r
    let μ : ℝ := cliqueMainTerm (Fintype.card V) (density K) q (r + 1) (r + 1)
    ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
      IsCliqueFamilyBounded r C.generators θ ∧ C.generators.card ≤ N * K.card ∧
      (C.saturated.card : ℝ) ≤ (q.choose r * (N * K.card) : ℕ) * L / cap ∧
      ((K \ C.good).card : ℝ) ≤ (q.choose (r + 1) : ℝ) * C.saturated.card / τ ∧
      ∀ e ∈ C.good,
        |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| <
          ε * μ + τ := by
  dsimp only
  let ε : ℝ := η * q * 2 ^ q
  let L : ℝ := (1 + ε) * cliqueMainTerm (Fintype.card V) (density K) q (r + 1) r
  let μ : ℝ := cliqueMainTerm (Fintype.card V) (density K) q (r + 1) (r + 1)
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hL0 : 0 ≤ L := mul_nonneg (by linarith)
    (cliqueMainTerm_nonneg (Nat.cast_nonneg _) (density_nonneg K) q (r + 1) r)
  have hface (S : Block V r) :
      (((cliqueFamily K q).filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ L := by
    have he := (abs_le.mp (hT.cliqueFamily_small_root_relative hqh hcη hη hη1 hsize S
      (by omega) (Nat.lt_succ_self r))).2
    change _ ≤ ε * cliqueMainTerm (Fintype.card V) (density K) q (r + 1) r at he
    dsimp only [L]
    nlinarith
  have hedge (e : Block V (r + 1)) (he : e ∈ K) :
      |(((cliqueFamily K q).filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| ≤ ε * μ :=
    hT.cliqueFamily_edge_relative hqh hcη hη hη1 hsize hqr he
  obtain ⟨C, hload, hcard, hsat, hbad, hcount⟩ := exists_modular_generating_data N hN K
    (cliqueFamily K q) (fun _ hQ => (mem_filter.mp hQ).2) cap hcap hL0 hτ hface hedge
  exact ⟨C, cliqueFamilyBounded_of_face_load C.generators cap hload hθ,
    hcard, hsat, hbad, hcount⟩

end Arxiv2411_18291
