import Arxiv.Arxiv2411_18291.RainbowNearCandidates
import Arxiv.Arxiv2411_18291.TypicalCliqueColours
import Arxiv.Arxiv2411_18291.UniformColouredExtensions

/-!
# Monochromatic replacements for every original rainbow clique

One extra finite colour family makes all far cliques monochromatic in a
successful exchange embedding for every originally rainbow base. Near
cliques use the fixed original colours. Only the base is fixed in the
colour experiment; the entire eligible near frame contributes candidates.
-/

open Finset Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {J W : Type*} [Fintype J] [Fintype W] [DecidableEq W] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)}

theorem eventually_rainbow_exchange_replacements (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (h L : ℕ) (hqh : q.choose (r + 1) ≤ h)
    {b α δ τ γ χ κ : ℝ} (hb : 0 < b) (hα : 0 ≤ α)
    (hκ : 0 < κ) (hκγ : κ < γ) (hγχ : γ < χ) (hχδ : χ < δ)
    (hχ1 : χ < 1) (hχτ : χ < τ)
    (hnear : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) < 1)
    (hhost : α * q.choose (r + 1) + δ < 1)
    (hgap : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) * q.choose (r + 1) +
      2 * (α * q.choose (r + 1)) * S.farCliques.card + κ < 1)
    (hL : (q : ℝ) < κ * L) :
    ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-δ)) h → b * (n : ℝ) ^ (-α) ≤ density K →
      ∀ D : Finset (Block (Fin n) q), D ⊆ cliqueFamily K q →
      (((cliqueFamily K q) \ D).card : ℝ) ≤
        (n : ℝ) ^ (-τ) * (cliqueFamily K q).card →
      ∀ G : Hypergraph (Fin n) (r + 1),
      (∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-τ) * cliqueMainTerm n (density K) q (r + 1) (r + 1)) →
      ∀ σ : J → Equiv.Perm (Fin n),
      ∃ τ : Fin L × S.farCliques → Equiv.Perm (Fin n), ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding G) (cliqueEdges (r + 1) Q) →
        ∃ f : W ↪ Fin n, mapBlock f S.base = Q ∧
          ∀ P ∈ S.replacementCliques,
            mapBlock f P ∈ permutedUnion σ D ∪ permutedUnion τ D := by
  classical
  let c : ℝ := min (nearFrameDensityConstant b q (r + 1)) (3 / 4)
  have hc : 0 < c := lt_min (nearFrameDensityConstant_pos hb q (r + 1)) (by norm_num)
  have hb' : 0 < b ^ q.choose (r + 1) / 2 := by positivity
  have hroot : ∀ P ∈ (univ : Finset S.farCliques),
      (P.val.val ∩ S.base.val).card < r + 1 := fun P _ => S.far_inter_card_lt P.property
  have hgap' : α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) * q.choose (r + 1) +
      2 * (α * q.choose (r + 1)) * (univ : Finset S.farCliques).card + κ < 1 := by
    simpa only [card_univ, Fintype.card_coe] using hgap
  have hL' : (S.base.val.card : ℝ) < κ * L := by rw [S.base.property]; exact hL
  filter_upwards [eventually_rainbow_near_candidates (J := J) hA (Nat.succ_pos r) hqr hb hα
    (((hκ.trans hκγ).trans hγχ).trans hχτ) hnear,
    eventually_clique_colour_estimates q r h hqh hb (hκ.trans hκγ) hγχ hχδ hχ1 hχτ hhost,
    eventually_uniform_coloured_extensions S.base.val univ (fun P : S.farCliques => P.val)
      (r + 1) L hroot hb' hc hκ hκγ hgap' hL'] with n hN hDcol hcol
  intro K hT hd D hDK hloss G hcount σ
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  choose T hsize hnearT using hN K G D hd hcount σ
  have hsize' (φ : S.base.val ↪ Fin n) :
      (c * (n : ℝ) ^ (-(α * ((q.choose (r + 1) - 1 : ℕ) : ℝ) * q.choose (r + 1)))) *
        (n : ℝ) ^ (Fintype.card W - S.base.val.card) ≤ (T φ).card := by
    simpa only [c, S.base.property] using hsize φ
  have hprob := hDcol K hT hd D hDK hloss
  obtain ⟨ω, hω⟩ := hcol T D (density K ^ q.choose (r + 1))
    (pow_nonneg (density_nonneg K) _) hsize' hprob.1 hprob.2.1 hprob.2.2
  let τ (p : Fin L × S.farCliques) := ω p.1 p.2
  refine ⟨τ, fun Q hQ => ?_⟩
  let φ := edgeRootMap S.base Q
  have hQ' : IsRainbow (fun j => mapGraph (σ j).toEmbedding G)
      (cliqueEdges (r + 1) (rootImage φ S.base Subset.rfl)) := by
    simpa only [φ, rootImage_edgeRootMap] using hQ
  obtain ⟨j, hj⟩ := hω φ
  have hp0 := density_nonneg D
  have hpos : 0 < extensionColourCount φ univ (fun P : S.farCliques => P.val) (T φ) D
      (ω j) := (by positivity : (0 : ℝ) ≤
        ((T φ).card : ℝ) * density D ^ (univ : Finset S.farCliques).card / 2).trans_lt hj
  obtain ⟨f, hfT, hfcol⟩ :=
    (extensionColourCount_pos_iff univ (fun P : S.farCliques => P.val) (T φ) D (ω j)).mp hpos
  refine ⟨f.val, (f.map_rootBlock φ S.base Subset.rfl).trans
    (rootImage_edgeRootMap S.base Q), fun P hP => ?_⟩
  by_cases hPN : P ∈ S.nearCliques
  · exact mem_union_left _ (hnearT φ hQ' f hfT P hPN)
  · have hPF : P ∈ S.farCliques := mem_sdiff.mpr ⟨hP, hPN⟩
    exact mem_union_right _ (mapGraph_subset_permutedUnion τ D (j, ⟨P, hPF⟩)
      (hfcol ⟨P, hPF⟩ (mem_univ _)))

end Arxiv2411_18291
