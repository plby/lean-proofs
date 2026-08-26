import ErdosProblems.Erdos76.CoverQuantization

/-! Repairing fractional triangle covers with few deficient triangles. -/

open Finset SimpleGraph
open scoped BigOperators

namespace Erdos76.CoverRepair

variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

noncomputable def triangleCost (G : SimpleGraph V) (z : Sym2 V → ℝ) (t : Finset V) : ℝ :=
  ∑ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.sym2), z e

noncomputable def badTriangles (G : SimpleGraph V) (z : Sym2 V → ℝ) (α : ℝ) : Finset (Finset V) :=
  (G.cliqueFinset 3).filter (fun t ↦ triangleCost G z t < 1 - α)

noncomputable def badTriples (G : SimpleGraph V) (z : Sym2 V → ℝ) (α : ℝ) : Finset (V × V × V) :=
  univ.filter fun x ↦ G.Adj x.1 x.2.1 ∧ G.Adj x.1 x.2.2 ∧ G.Adj x.2.1 x.2.2 ∧
    z s(x.1, x.2.1) + z s(x.1, x.2.2) + z s(x.2.1, x.2.2) < 1 - α

lemma triangleCost_triple {G : SimpleGraph V} (z : Sym2 V → ℝ) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    triangleCost G z {a, b, c} = z s(a, b) + z s(a, c) + z s(b, c) := by
  rw [triangleCost, NewProof.triangle_edges_eq hab hac hbc]
  have h₁ : s(a, b) ≠ s(a, c) := fun h ↦ hbc.ne (Sym2.congr_right.mp h)
  have h₂ : s(a, b) ≠ s(b, c) := by
    simp only [ne_eq, Sym2.eq_iff]
    aesop
  have h₃ : s(a, c) ≠ s(b, c) := fun h ↦ hab.ne (Sym2.congr_left.mp h)
  simp [h₁, h₂, h₃, add_assoc]

lemma badTriples_card_le (G : SimpleGraph V) (z : Sym2 V → ℝ) (α : ℝ) :
    (badTriples G z α).card ≤ 27 * (badTriangles G z α).card := by
  have hsub : badTriples G z α ⊆
      (badTriangles G z α).biUnion (fun t ↦ t ×ˢ (t ×ˢ t)) := by
    rintro ⟨a, b, c⟩ h
    simp only [badTriples, mem_filter, mem_univ, true_and] at h
    refine mem_biUnion.mpr ⟨{a, b, c}, ?_, ?_⟩
    · rw [badTriangles, mem_filter, mem_cliqueFinset_iff]
      refine ⟨is3Clique_triple_iff.mpr ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
      rw [triangleCost_triple z h.1 h.2.1 h.2.2.1]
      exact h.2.2.2
    · simp
  calc
    _ ≤ ((badTriangles G z α).biUnion (fun t ↦ t ×ˢ (t ×ˢ t))).card := card_le_card hsub
    _ ≤ ∑ t ∈ badTriangles G z α, (t ×ˢ (t ×ˢ t)).card := card_biUnion_le
    _ = ∑ _t ∈ badTriangles G z α, 27 := by
      apply sum_congr rfl
      intro t ht
      have htcard := (mem_cliqueFinset_iff.mp (mem_filter.mp ht).1).card_eq
      simp [card_product, htcard]
    _ = 27 * (badTriangles G z α).card := by simp [mul_comm]

noncomputable def quantizedColor (q : ℕ) (z : Sym2 V → ℝ) : Sym2 V → Fin (q + 1) :=
  fun e ↦ CoverQuantization.label q (z e)

noncomputable def rejectedPattern (q : ℕ) (α : ℝ) (p : Fin (q + 1) × Fin (q + 1) × Fin (q + 1)) : Prop :=
  CoverQuantization.value p.1 + CoverQuantization.value p.2.1 +
    CoverQuantization.value p.2.2 < 1 - α

lemma rejected_subset_badTriples (G : SimpleGraph V) (z : Sym2 V → ℝ) {q : ℕ} (hq : 0 < q)
    {α : ℝ} (hα : 0 < α) :
    PatternRemoval.rejectedTriples G (quantizedColor q z) (rejectedPattern q α) ⊆
      badTriples G z α := by
  rintro ⟨a, b, c⟩ h
  simp only [PatternRemoval.rejectedTriples, badTriples, mem_filter, mem_univ, true_and] at h ⊢
  exact ⟨h.1, h.2.1, h.2.2.1, CoverQuantization.sum_lt_of_value_sum_lt hq hα h.2.2.2⟩

lemma badTriples_subset_rejected (G : SimpleGraph V) (z : Sym2 V → ℝ)
    (hz : ∀ e ∈ G.edgeFinset, 0 ≤ z e) {q : ℕ} (hq : 0 < q)
    {α : ℝ} (hstep : 3 / (q : ℝ) ≤ α / 2) :
    badTriples G z α ⊆
      PatternRemoval.rejectedTriples G (quantizedColor q z) (rejectedPattern q (α / 2)) := by
  rintro ⟨a, b, c⟩ h
  simp only [PatternRemoval.rejectedTriples, badTriples, mem_filter, mem_univ, true_and] at h ⊢
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  apply CoverQuantization.value_sum_lt_of_sum_lt hq _ _ _ hstep h.2.2.2
  · exact hz _ (mem_edgeFinset.mpr ((mem_edgeSet G).mpr h.1))
  · exact hz _ (mem_edgeFinset.mpr ((mem_edgeSet G).mpr h.2.1))
  · exact hz _ (mem_edgeFinset.mpr ((mem_edgeSet G).mpr h.2.2.1))

/-- Uniform removal of triangles with a fixed positive deficit in their
cover weight. The threshold depends only on the two error parameters. -/
theorem exists_uniform_defect_cover (α η : ℝ) (hα : 0 < α) (hη : 0 < η) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) (z : Sym2 W → ℝ),
      (∀ e ∈ G.edgeFinset, 0 ≤ z e) →
      ((badTriangles G z (α / 2)).card : ℝ) < θ * (Fintype.card W : ℝ) ^ 3 →
      ∃ E : Finset (Sym2 W), (E.card : ℝ) ≤ η * (Fintype.card W : ℝ) ^ 2 ∧
        ∀ t ∈ G.cliqueFinset 3, triangleCost G z t < 1 - α →
          ∃ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.sym2), e ∈ E := by
  classical
  obtain ⟨q, hq⟩ := exists_nat_gt (max 1 (6 / α))
  have hq₁ : (1 : ℝ) < q := (le_max_left _ _).trans_lt hq
  have hqpos : 0 < q := by exact_mod_cast (show (0 : ℝ) < q by linarith)
  have hstep : 3 / (q : ℝ) ≤ α / 2 := by
    have hqα : 6 / α < (q : ℝ) := (le_max_right _ _).trans_lt hq
    have hmul := (div_lt_iff₀ hα).mp hqα
    apply (div_le_iff₀ (by exact_mod_cast hqpos)).mpr
    nlinarith
  let σ : ℝ := η / (9 * ((q + 1 : ℕ) : ℝ) ^ 3)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  refine ⟨triangleRemovalBound σ, triangleRemovalBound_pos hσ, ?_⟩
  intro W _ _ G z hz hbad
  let col := quantizedColor q z
  let P := rejectedPattern q (α / 2)
  have hcard : ((PatternRemoval.rejectedTriples G col P).card : ℝ) ≤
      27 * (badTriangles G z (α / 2)).card := by
    exact_mod_cast (card_le_card (rejected_subset_badTriples G z hqpos (by positivity))).trans
      (badTriples_card_le G z (α / 2))
  have hsmall : ((PatternRemoval.rejectedTriples G col P).card : ℝ) <
      triangleRemovalBound σ * (3 * (Fintype.card W : ℝ)) ^ 3 := by
    have hmul := mul_lt_mul_of_pos_left hbad (by norm_num : (0 : ℝ) < 27)
    nlinarith
  obtain ⟨E, hE, hhit⟩ := PatternRemoval.exists_rejected_pair_cover G col P hσ hsmall
  refine ⟨E, ?_, ?_⟩
  · have hfactor : (Fintype.card (Fin (q + 1)) : ℝ) ^ 3 * 9 * σ = η := by
      simp only [Fintype.card_fin, σ]
      field_simp
    rwa [hfactor] at hE
  · intro t ht hcost
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := is3Clique_iff.mp (mem_cliqueFinset_iff.mp ht)
    have htriple : (a, b, c) ∈ badTriples G z α := by
      simp only [badTriples, mem_filter, mem_univ, true_and]
      exact ⟨hab, hac, hbc, by simpa only [triangleCost_triple z hab hac hbc] using hcost⟩
    have hreject := badTriples_subset_rejected G z hz hqpos hstep htriple
    rcases hhit a b c hreject with habE | hacE | hbcE
    · refine ⟨s(a, b), ?_, habE⟩
      rw [NewProof.triangle_edges_eq hab hac hbc]
      simp
    · refine ⟨s(a, c), ?_, hacE⟩
      rw [NewProof.triangle_edges_eq hab hac hbc]
      simp
    · refine ⟨s(b, c), ?_, hbcE⟩
      rw [NewProof.triangle_edges_eq hab hac hbc]
      simp

noncomputable def repairedWeight (z : Sym2 V → ℝ) (α : ℝ) (E : Finset (Sym2 V)) (e : Sym2 V) : ℝ :=
  z e / (1 - α) + if e ∈ E then 1 else 0

lemma repairedWeight_nonneg {G : SimpleGraph V} {z : Sym2 V → ℝ}
    (hz : ∀ e ∈ G.edgeFinset, 0 ≤ z e) {α : ℝ} (hα : α < 1) (E : Finset (Sym2 V)) :
    ∀ e ∈ G.edgeFinset, 0 ≤ repairedWeight z α E e := by
  intro e he
  have hd : 0 ≤ 1 - α := sub_nonneg.mpr hα.le
  have hdiv := div_nonneg (hz e he) hd
  unfold repairedWeight
  split_ifs <;> linarith

lemma repairedWeight_is_cover {G : SimpleGraph V} {z : Sym2 V → ℝ}
    (hz : ∀ e ∈ G.edgeFinset, 0 ≤ z e) {α : ℝ} (hα : α < 1) (E : Finset (Sym2 V))
    (hhit : ∀ t ∈ G.cliqueFinset 3, triangleCost G z t < 1 - α →
      ∃ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.sym2), e ∈ E) :
    LPDuality.IsFractionalEdgeCover G (repairedWeight z α E) := by
  have hd : 0 < 1 - α := sub_pos.mpr hα
  refine ⟨repairedWeight_nonneg hz hα E, ?_⟩
  intro t ht
  by_cases hex : ∃ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.sym2), e ∈ E
  · obtain ⟨e, he, heE⟩ := hex
    have hsingle := single_le_sum
      (fun f hf ↦ repairedWeight_nonneg hz hα E f (mem_filter.mp hf).1) he
    have hone : 1 ≤ repairedWeight z α E e := by
      have hnonneg := div_nonneg (hz e (mem_filter.mp he).1) hd.le
      simp only [repairedWeight, if_pos heE]
      linarith
    exact hone.trans hsingle
  · have hcost : 1 - α ≤ triangleCost G z t :=
      le_of_not_gt (fun h ↦ hex (hhit t ht h))
    have hzero : (∑ e ∈ G.edgeFinset.filter (fun e ↦ e ∈ t.sym2),
        if e ∈ E then (1 : ℝ) else 0) = 0 := by
      apply sum_eq_zero
      intro e he
      simp [show e ∉ E from fun h ↦ hex ⟨e, he, h⟩]
    simp only [repairedWeight, sum_add_distrib, ← sum_div, hzero, add_zero]
    exact (one_le_div hd).mpr hcost

lemma repairedWeight_sum_le {G : SimpleGraph V} (z : Sym2 V → ℝ) (α : ℝ)
    (E : Finset (Sym2 V)) :
    (∑ e ∈ G.edgeFinset, repairedWeight z α E e) ≤
      (∑ e ∈ G.edgeFinset, z e) / (1 - α) + E.card := by
  simp only [repairedWeight, sum_add_distrib, ← sum_div]
  apply add_le_add le_rfl
  have hsub : G.edgeFinset.filter (fun e ↦ e ∈ E) ⊆ E := fun e he ↦ (mem_filter.mp he).2
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast card_le_card hsub

/-- Sparse cover defects can be repaired at arbitrarily small quadratic cost,
uniformly in the graph and its number of vertices. -/
theorem exists_uniform_cover_repair (α η : ℝ) (hα : 0 < α) (hα₁ : α < 1) (hη : 0 < η) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (W : Type*) [Fintype W] [DecidableEq W]
      (G : SimpleGraph W) (z : Sym2 W → ℝ),
      (∀ e ∈ G.edgeFinset, 0 ≤ z e) →
      ((badTriangles G z (α / 2)).card : ℝ) < θ * (Fintype.card W : ℝ) ^ 3 →
      ∃ z' : Sym2 W → ℝ, LPDuality.IsFractionalEdgeCover G z' ∧
        (∑ e ∈ G.edgeFinset, z' e) ≤
          (∑ e ∈ G.edgeFinset, z e) / (1 - α) + η * (Fintype.card W : ℝ) ^ 2 := by
  obtain ⟨θ, hθ, hrem⟩ := exists_uniform_defect_cover α η hα hη
  refine ⟨θ, hθ, ?_⟩
  intro W _ _ G z hz hbad
  obtain ⟨E, hE, hhit⟩ := hrem W G z hz hbad
  refine ⟨repairedWeight z α E, repairedWeight_is_cover hz hα₁ E hhit, ?_⟩
  exact (repairedWeight_sum_le z α E).trans (add_le_add le_rfl hE)

end Erdos76.CoverRepair
