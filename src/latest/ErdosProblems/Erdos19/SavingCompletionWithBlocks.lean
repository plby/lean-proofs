import ErdosProblems.Erdos19.BufferedReservoirUnion
import ErdosProblems.Erdos19.OutsideReservoirDegreeBounds
import ErdosProblems.Erdos19.RankSeparatedBufferedColoring
import ErdosProblems.Erdos19.SpecialPaletteInitialization
import ErdosProblems.Erdos19.SpecialPaletteBuffer
import ErdosProblems.Erdos19.MediumPaletteControl

/-! # Completing a saved palette from a balanced block partition

All coloring, matching, and completion steps are discharged here. The explicit
integer hypotheses describe the remaining parameter selection, rather than an
unproved coloring input.
-/

namespace Erdos19.SetHypergraph

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

theorem eventually_complete_saved_palette_with_blocks (r s t L : ℕ)
    (hr : 3 ≤ r) (hs : 2 ≤ s) (ht : 0 < t) (hL : 0 < L) :
    ∃ ell N : ℕ, 2 ≤ ell ∧ ∀ n : ℕ, N ≤ n →
      ∀ k : ℕ, 4 ≤ k → ∀ H : SetHypergraph (Fin n), H.IsLinear →
      (∀ e : H, 2 ≤ e.1.ncard) →
      ∀ m : ℕ, ∀ color : (H.rankAtLeast r).EdgeColoring (Fin m),
      ∀ S : Finset (Fin m), S.Nonempty → ∀ A d₀ dY d delta : ℕ,
      (H.rankAtLeast r).IsCoverBoundedColoring color A →
      (∀ a, a ∉ S → ((H.rankAtLeast r).coveredVertices {e | color e = a}).ncard ≤ A) →
      (∀ e : H.rankAtLeast r, color e ∉ S → ell * r ≤ e.1.ncard) →
      2 ≤ n / L → 8 * (n / L) < n / k →
      m + (n / k - 8 * (n / L)) = n → 2 * (S.card + n / k) ≤ n →
      4 * S.card ≤ d₀ → 4 * (S.card + n / s) ≤ dY →
      delta ≤ d₀ → d₀ < dY → d₀ + n / k + n / L ≤ d →
      9 * k * (n / L) + k ≤ delta →
      A + 2 * delta + 9 * (n / L) + 1 ≤ n / (16 * s * t) →
      ∀ Y : Set (Fin n), (∀ v ∈ Y, dY ≤ (H.twoGraph.neighborSet v)ᶜ.ncard) →
      2 * A ≤ Y.ncard + 1 → 2 * (d + S.card) + 1 ≤ Y.ncard →
      ∀ z : Fin n → Fin k,
      (∀ v, (H.twoGraph.neighborSet v).ncard ≤
        k * (((insideBlocks H.twoGraph z).neighborSet v).ncard + n / L)) →
      (∀ v, k * ((insideBlocks H.twoGraph z).neighborSet v).ncard ≤
        (H.twoGraph.neighborSet v).ncard + k * (n / L)) →
      (∀ a, n / t ≤ (Y.toFinset.filter fun v ↦ z v = a).card) → H.EdgeColorable n := by
  classical
  have heps : (0 : ℝ) < 1 / (2 * L) := by positivity
  obtain ⟨ell, N, hell, hcoloring⟩ := eventually_buffered_coloring_around_large_palette
    r s t (by omega) hs ht (1 / (2 * L)) heps
  refine ⟨ell, max N L, hell, ?_⟩
  intro n hn k hk H hlinear hmin m color S hS A d₀ dY d delta hbounded hold hlarge
    he hf hm hroom hsmall hYroom hdeltad hd₀Y hd hdelta hbufferRoom Y hY htrace hinit
    z hresLow hresUp hblocks
  let e := n / L
  let f := n / k
  let fresh := f - 8 * e
  let D := n - S.card - f + 2 * e
  let J := H.rankAtLeast r
  let R := insideBlocks H.twoGraph z
  let U₀ : Set (Fin n) := {v | (H.twoGraph.neighborSet v)ᶜ.ncard ≤ d₀}
  let U : Set (Fin n) := {v | (H.twoGraph.neighborSet v)ᶜ.ncard ≤ delta}
  have hsum (v : Fin n) : (H.twoGraph.neighborSet v).ncard +
      (H.twoGraph.neighborSet v)ᶜ.ncard = n := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      Set.ncard_add_ncard_compl (H.twoGraph.neighborSet v)
  have hUsub : U ⊆ U₀ := fun _ hv ↦ hv.trans hdeltad
  have hUY₀ : Disjoint U₀ Y := Set.disjoint_left.mpr (by
    intro v hv hvY
    have hy := hY v hvY
    change (H.twoGraph.neighborSet v)ᶜ.ncard ≤ d₀ at hv
    omega)
  have hUY : Disjoint U Y := hUY₀.mono_left hUsub
  have hJH : J ⊆ H := fun _ h ↦ h.1
  obtain ⟨bad, hbad, hbadBuffer⟩ := J.exists_exceptional_color_with_buffer
    (H.rankAtLeast_linear hlinear r) color A hbounded Y htrace S hS d hinit
  have hmissing₀ : ∀ u ∈ U₀, ((H.twoGraph \ R).neighborSet u)ᶜ.ncard ≤ d := by
    intro u hu
    have h := missing_neighbors_after_edge_use H.twoGraph R Set.univ u
    have huniv (T : Set (Fin n)) : Set.univ \ T = Tᶜ := by ext v; simp
    simp only [huniv] at h
    have hRupper := reservoir_degree_upper n k e _ _ (by omega)
      (by have := hsum u; omega) (hresUp u)
    change (H.twoGraph.neighborSet u)ᶜ.ncard ≤ d₀ at hu
    change (R.neighborSet u).ncard ≤ f + e at hRupper
    omega
  obtain ⟨J₀, c₀, hJJ₀, hJ₀H, hagree, hnonSpecial, hsame, hspecial, hload, Z,
    hindependent, hbadCover⟩ := H.exists_special_palette_initialization J hJH
      (fun e ↦ hr.trans e.2.2) m color S bad hbad R U₀ Y hUY₀ d hmissing₀ hbadBuffer
  let K := H.outsideReservoir J₀ R
  have hJ₀linear : J₀.IsLinear := fun {_} he {_} hf hne ↦ hlinear (hJ₀H he) (hJ₀H hf) hne
  have hKlinear : K.IsLinear := fun {_} he {_} hf hne ↦ hlinear he.1 hf.1 hne
  have hKmax : ∀ x : K, x.1.ncard ≤ r := by
    intro x
    by_contra hx
    exact x.2.2 (Or.inl (hJJ₀ ⟨x.2.1, by omega⟩))
  have hdeg := H.outsideReservoir_degree_bounds n k e d₀ dY (n / s) hk he J₀ hJ₀H
    hlinear hmin R (insideBlocks_le _ _) hresLow hload m c₀ S bad
    (fun v hv a ha hne ↦ hspecial a ha hne hv) (by omega) hsmall hYroom
  have hpal := saving_palette_arithmetic n S.card f e hroom (Nat.le_of_lt hf)
  dsimp only at hpal
  have hmEq : m = n - fresh := by dsimp only [fresh, f, e]; omega
  have hDlow : n ≤ 2 * D := hpal.2.2.2.1
  have hDhigh : D ≤ n := hpal.2.2.2.2.1
  have hp : m - S.card = D + 6 * e := by
    have h := hpal.2.2.2.2.2
    change n - fresh - S.card = D + 6 * e at h
    omega
  let palette : Finset (Fin m) := univ \ S
  have hpaletteCard : palette.card = m - S.card := by
    simp only [palette, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  have hpaletteSize : (1 + 1 / (2 * (L : ℝ))) * D ≤ palette.card := by
    rw [hpaletteCard, hp]
    exact saving_approximate_palette_slack n L D e hL hDhigh rfl ((le_max_right _ _).trans hn)
  have hactiveRank : ∀ x : J₀, c₀ x ∈ palette → ell * r ≤ x.1.ncard := by
    intro x hx
    have hnot : c₀ x ∉ S := (mem_sdiff.mp hx).2
    have hxJ := hnonSpecial x hnot
    have heq := hagree ⟨x.1, hxJ⟩ x.2
    exact hlarge ⟨x.1, hxJ⟩ (by simpa only [← heq] using hnot)
  let blocks : Fin k → Finset (Fin n) := fun a ↦ Y.toFinset.filter fun v ↦ z v = a
  have hblockDis : Pairwise fun i j ↦ Disjoint (blocks i) (blocks j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    exact hij ((mem_filter.mp hvi).2.symm.trans (mem_filter.mp hvj).2)
  obtain ⟨cK, hcross, hbuffer⟩ := hcoloring n ((le_max_left _ _).trans hn) J₀ K
    hJ₀linear hKlinear m c₀ palette hactiveRank hKmax D hDlow hDhigh hdeg.1
    (Fin k) blocks hblockDis hblocks
    (fun _ v hv ↦ hdeg.2 v (hY v (Set.mem_toFinset.mp (mem_filter.mp hv).1))) hpaletteSize
  have hfresh : 0 < fresh := by dsimp only [fresh, f, e]; omega
  have hanswer : H.EdgeColorable (m + fresh) := by
    apply H.edgeColorable_of_buffered_outside_reservoir J₀ hJ₀H hlinear hmin m fresh
      hfresh (by simpa only [Fintype.card_fin] using hm.symm) c₀ palette bad U Y Z hUY z
      cK hcross A delta 1 (delta + 9 * e) ?_ (fun _ hv ↦ hv) (fun v _ ↦ hload v)
      ?_ ?_ ?_ ?_ hindependent
    · intro a ha
      have hnot := (mem_sdiff.mp ha).2
      rw [hsame a hnot]
      exact hold a hnot
    · intro v hv
      apply reservoir_request_bound n k e delta _ _ m (by omega)
        (by have := hsum v; omega) (hresUp v) ?_ (Nat.le_of_lt hf) hm
      have := hsum v
      change (H.twoGraph.neighborSet v)ᶜ.ncard ≤ delta at hv
      omega
    · intro j a
      have hb := hbuffer j a
      have hset : ((Y ∩ {v | z v = j}) \ K.coveredVertices {x | cK x = a}).toFinset =
          blocks j \ (K.coveredVertices {x | cK x = a}).toFinset := by
        ext v
        simp only [Set.mem_toFinset, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_ofPred_eq,
          mem_sdiff, blocks, mem_filter]
      rw [Set.ncard_eq_toFinset_card', hset]
      exact (by dsimp only [e]; omega : A + delta + 1 + (delta + 9 * e) ≤ n / (16 * s * t)).trans hb
    · intro a ha v hv hex
      have haS : a ∈ S := by
        by_contra h
        exact ha (mem_sdiff.mpr ⟨mem_univ _, h⟩)
      rcases hex with hvZ | hne
      · by_cases hab : a = bad
        · subst a
          exact hbadCover v hvZ
        · exact hspecial a haS hab (hUsub hv)
      · exact hspecial a haS hne (hUsub hv)
    · intro v hv
      apply reservoir_outside_degree_bound n k e delta _ _ (by omega) (hresUp v)
        ?_ hdelta (Nat.le_of_lt hf)
      have := hsum v
      change ¬(H.twoGraph.neighborSet v)ᶜ.ncard ≤ delta at hv
      omega
  simpa only [show m + fresh = n from hm] using hanswer

#print axioms eventually_complete_saved_palette_with_blocks

end Erdos19.SetHypergraph
