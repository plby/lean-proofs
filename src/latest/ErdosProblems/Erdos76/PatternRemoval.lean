import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite
import Mathlib.Tactic
import ErdosProblems.Erdos76.FractionalBound

/-!
# Removing a fixed pattern of triangle edges

The auxiliary tripartite construction reduces a fixed edge-label pattern to
the triangle removal lemma already proved in Mathlib.
-/

open Finset Sum3 SimpleGraph
open SimpleGraph.TripartiteFromTriangles
open scoped BigOperators

namespace Erdos76.PatternRemoval

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

noncomputable local instance (t : Finset (V × V × V)) : DecidableRel (graph t).Adj :=
  Classical.decRel _

/-- Closure under taking the three pairwise projections. -/
def PairClosed (t : Finset (V × V × V)) : Prop :=
  ∀ a b c, (∃ c', (a, b, c') ∈ t) → (∃ b', (a, b', c) ∈ t) →
    (∃ a', (a', b, c) ∈ t) → (a, b, c) ∈ t

lemma cliqueFinset_eq_map {t : Finset (V × V × V)} (ht : PairClosed t) :
    (graph t).cliqueFinset 3 = t.map toTriangle := by
  ext S
  rw [mem_cliqueFinset_iff, mem_map]
  constructor
  · intro hS
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := is3Clique_iff.mp hS
    obtain ⟨a, b, c, heq, hab, hac, hbc⟩ := graph_triple hxy hxz hyz
    refine ⟨(a, b, c), ht a b c ?_ ?_ ?_, heq⟩
    · exact Graph.in₀₁_iff.mp hab
    · exact Graph.in₀₂_iff.mp hac
    · exact Graph.in₁₂_iff.mp hbc
  · rintro ⟨x, hx, rfl⟩
    exact toTriangle_is3Clique hx

lemma cliqueFinset_card {t : Finset (V × V × V)} (ht : PairClosed t) :
    ((graph t).cliqueFinset 3).card = t.card := by
  rw [cliqueFinset_eq_map ht, card_map]

def collapse : V ⊕ V ⊕ V → V := Sum.elim id (Sum.elim id id)

lemma triangle_hit_of_deleted_projection {t : Finset (V × V × V)}
    {H : SimpleGraph (V ⊕ V ⊕ V)} (hfree : H.CliqueFree 3)
    {a b c : V} (habc : (a, b, c) ∈ t) :
    s(a, b) ∈ ((graph t).edgeFinset \ H.edgeFinset).image (Sym2.map collapse) ∨
      s(a, c) ∈ ((graph t).edgeFinset \ H.edgeFinset).image (Sym2.map collapse) ∨
      s(b, c) ∈ ((graph t).edgeFinset \ H.edgeFinset).image (Sym2.map collapse) := by
  by_contra h
  push Not at h
  have hab : H.Adj (in₀ a) (in₁ b) := by
    by_contra hn
    apply h.1
    refine mem_image.mpr ⟨s(in₀ a, in₁ b), ?_, ?_⟩
    · rw [mem_sdiff, mem_edgeFinset, mem_edgeFinset, mem_edgeSet, mem_edgeSet]
      exact ⟨Graph.in₀₁_iff.mpr ⟨c, habc⟩, hn⟩
    · rfl
  have hac : H.Adj (in₀ a) (in₂ c) := by
    by_contra hn
    apply h.2.1
    refine mem_image.mpr ⟨s(in₀ a, in₂ c), ?_, ?_⟩
    · rw [mem_sdiff, mem_edgeFinset, mem_edgeFinset, mem_edgeSet, mem_edgeSet]
      exact ⟨Graph.in₀₂_iff.mpr ⟨b, habc⟩, hn⟩
    · rfl
  have hbc : H.Adj (in₁ b) (in₂ c) := by
    by_contra hn
    apply h.2.2
    refine mem_image.mpr ⟨s(in₁ b, in₂ c), ?_, ?_⟩
    · rw [mem_sdiff, mem_edgeFinset, mem_edgeFinset, mem_edgeSet, mem_edgeSet]
      exact ⟨Graph.in₁₂_iff.mpr ⟨a, habc⟩, hn⟩
    · rfl
  exact hfree {in₀ a, in₁ b, in₂ c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

lemma removal_canonical (G : SimpleGraph V) {ε : ℝ}
    (htri : ((G.cliqueFinset 3).card : ℝ) < triangleRemovalBound ε * (Fintype.card V : ℝ) ^ 3) :
    ∃ H ≤ G, ((NewProof.canonicalEdges G).card : ℝ) - (NewProof.canonicalEdges H).card <
      ε * (Fintype.card V : ℝ) ^ 2 ∧ H.CliqueFree 3 := by
  obtain ⟨H, hH, hdec, hsize, hfree⟩ := triangle_removal htri
  refine ⟨H, hH, ?_, hfree⟩
  simpa only [NewProof.edgeFinset_eq_canonical, Nat.cast_pow] using hsize

lemma projected_sdiff_card_le {W : Type*} [Fintype W] [DecidableEq W]
    (G H : SimpleGraph W) (hH : H ≤ G) (f : W → V) :
    (((G.edgeFinset \ H.edgeFinset).image (Sym2.map f)).card : ℝ) ≤
      ((NewProof.canonicalEdges G).card : ℝ) - (NewProof.canonicalEdges H).card := by
  have hcard := card_image_le (s := G.edgeFinset \ H.edgeFinset) (f := Sym2.map f)
  have hsub : H.edgeFinset ⊆ G.edgeFinset := edgeFinset_mono hH
  have hdiff : ((G.edgeFinset \ H.edgeFinset).card : ℝ) =
      (G.edgeFinset.card : ℝ) - H.edgeFinset.card := by
    rw [card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub)]
  have hcard' : (((G.edgeFinset \ H.edgeFinset).image (Sym2.map f)).card : ℝ) ≤
      (G.edgeFinset.card : ℝ) - H.edgeFinset.card := by
    rw [← hdiff]
    exact_mod_cast hcard
  simpa only [NewProof.edgeFinset_eq_canonical] using hcard'

/-- A pair-closed triple family of sufficiently small size can be hit by
deleting few original unordered pairs. -/
theorem exists_small_pair_cover {t : Finset (V × V × V)} (ht : PairClosed t)
    {ε : ℝ} (hε : 0 < ε)
    (hsmall : (t.card : ℝ) < triangleRemovalBound ε * (3 * (Fintype.card V : ℝ)) ^ 3) :
    ∃ E : Finset (Sym2 V), (E.card : ℝ) < 9 * ε * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ a b c, (a, b, c) ∈ t → s(a, b) ∈ E ∨ s(a, c) ∈ E ∨ s(b, c) ∈ E := by
  classical
  have hn : (Fintype.card (V ⊕ V ⊕ V) : ℝ) = 3 * (Fintype.card V : ℝ) := by
    simp only [Fintype.card_sum, Nat.cast_add]
    ring
  have htri : (((graph t).cliqueFinset 3).card : ℝ) <
      triangleRemovalBound ε * (Fintype.card (V ⊕ V ⊕ V) : ℝ) ^ 3 := by
    rw [cliqueFinset_card ht, hn]
    exact hsmall
  obtain ⟨H, hH, hsize, hfree⟩ := removal_canonical (graph t) htri
  let E := ((graph t).edgeFinset \ H.edgeFinset).image (Sym2.map collapse)
  refine ⟨E, ?_, fun a b c habc ↦ triangle_hit_of_deleted_projection hfree habc⟩
  have hcard' := projected_sdiff_card_le (graph t) H hH collapse
  have hsize' : ((NewProof.canonicalEdges (graph t)).card : ℝ) -
      (NewProof.canonicalEdges H).card <
      ε * (3 * (Fintype.card V : ℝ)) ^ 2 := by
    simpa only [hn] using hsize
  change (E.card : ℝ) ≤ _ at hcard'
  nlinarith

variable {K : Type*} [Fintype K] [DecidableEq K]

noncomputable def patternTriples (G : SimpleGraph V) (col : Sym2 V → K) (p : K × K × K) :
    Finset (V × V × V) :=
  univ.filter fun x ↦ G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2 ∧
    col s(x.1, x.2.1) = p.1 ∧ col s(x.1, x.2.2) = p.2.1 ∧ col s(x.2.1, x.2.2) = p.2.2

noncomputable def rejectedTriples (G : SimpleGraph V) (col : Sym2 V → K)
    (P : K × K × K → Prop) : Finset (V × V × V) :=
  univ.filter fun x ↦ G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2 ∧
    P (col s(x.1, x.2.1), col s(x.1, x.2.2), col s(x.2.1, x.2.2))

lemma patternTriples_pairClosed (G : SimpleGraph V) (col : Sym2 V → K) (p : K × K × K) :
    PairClosed (patternTriples G col p) := by
  intro a b c hab hac hbc
  rcases hab with ⟨c', hab⟩
  rcases hac with ⟨b', hac⟩
  rcases hbc with ⟨a', hbc⟩
  simp only [patternTriples, mem_filter, mem_univ, true_and] at hab hac hbc ⊢
  exact ⟨hab.1, hac.2.1, hbc.2.2.1, hab.2.2.2.1, hac.2.2.2.2.1, hbc.2.2.2.2.2⟩

lemma patternTriples_subset_rejected (G : SimpleGraph V) (col : Sym2 V → K)
    (P : K × K × K → Prop) {p : K × K × K} (hp : P p) :
    patternTriples G col p ⊆ rejectedTriples G col P := by
  intro x hx
  simp only [patternTriples, rejectedTriples, mem_filter, mem_univ, true_and] at hx ⊢
  refine ⟨hx.1, hx.2.1, hx.2.2.1, ?_⟩
  simpa only [hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2, Prod.eta] using hp

/-- A finite set of forbidden edge-label patterns can all be removed using
the ordinary uncoloured triangle removal theorem. -/
theorem exists_rejected_pair_cover (G : SimpleGraph V) (col : Sym2 V → K)
    (P : K × K × K → Prop) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ((rejectedTriples G col P).card : ℝ) <
      triangleRemovalBound ε * (3 * (Fintype.card V : ℝ)) ^ 3) :
    ∃ E : Finset (Sym2 V), (E.card : ℝ) ≤
      (Fintype.card K : ℝ) ^ 3 * 9 * ε * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ a b c, (a, b, c) ∈ rejectedTriples G col P →
        s(a, b) ∈ E ∨ s(a, c) ∈ E ∨ s(b, c) ∈ E := by
  classical
  have hex : ∀ p : K × K × K, ∃ E : Finset (Sym2 V),
      (E.card : ℝ) ≤ 9 * ε * (Fintype.card V : ℝ) ^ 2 ∧
      (P p → ∀ a b c, (a, b, c) ∈ patternTriples G col p →
        s(a, b) ∈ E ∨ s(a, c) ∈ E ∨ s(b, c) ∈ E) := by
    intro p
    by_cases hp : P p
    · have hcard : ((patternTriples G col p).card : ℝ) ≤ (rejectedTriples G col P).card := by
        exact_mod_cast card_le_card (patternTriples_subset_rejected G col P hp)
      have hsize := hcard.trans_lt hsmall
      obtain ⟨E, hE, hhit⟩ := exists_small_pair_cover (patternTriples_pairClosed G col p) hε hsize
      exact ⟨E, hE.le, fun _ ↦ hhit⟩
    · refine ⟨∅, ?_, fun h ↦ (hp h).elim⟩
      simp only [card_empty, Nat.cast_zero]
      positivity
  choose E hE using hex
  refine ⟨univ.biUnion E, ?_, ?_⟩
  · calc
      ((univ.biUnion E).card : ℝ) ≤ ∑ p, ((E p).card : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _p : K × K × K, 9 * ε * (Fintype.card V : ℝ) ^ 2 :=
        sum_le_sum (fun p _ ↦ (hE p).1)
      _ = (Fintype.card K : ℝ) ^ 3 * 9 * ε * (Fintype.card V : ℝ) ^ 2 := by
        simp only [sum_const, card_univ, Fintype.card_prod, Nat.cast_mul, nsmul_eq_mul]
        ring
  · intro a b c habc
    have h := habc
    simp only [rejectedTriples, mem_filter, mem_univ, true_and] at h
    let p := (col s(a, b), col s(a, c), col s(b, c))
    have hp : P p := h.2.2.2
    have hpat : (a, b, c) ∈ patternTriples G col p := by
      simp only [patternTriples, mem_filter, mem_univ, true_and, p, and_true]
      exact ⟨h.1, h.2.1, h.2.2.1⟩
    rcases (hE p).2 hp a b c hpat with hab | hac | hbc
    · exact Or.inl (mem_biUnion.mpr ⟨p, mem_univ _, hab⟩)
    · exact Or.inr (Or.inl (mem_biUnion.mpr ⟨p, mem_univ _, hac⟩))
    · exact Or.inr (Or.inr (mem_biUnion.mpr ⟨p, mem_univ _, hbc⟩))

end Erdos76.PatternRemoval
