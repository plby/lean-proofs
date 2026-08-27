import ErdosProblems.Erdos4.FGKMTInitialEdgeGeometry
import ErdosProblems.Erdos4.FGKMTArithmeticIncidence
import ErdosProblems.Erdos4.TiltedCappedEdges

/-! Prime-clipped translated edges retain the unconditional Maynard incidences. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

variable {k Y : ℕ}

noncomputable def baseTargetEdgeLaw (h : Fin k → ℕ) (p : ℕ) (targets : Finset ℕ)
    (μ : FiniteLaw (TranslatedCenter Y)) : FiniteLaw (Finset targets) :=
  μ.map (fun n => initialTargetEdge h p Y targets n.val)

theorem baseTargetEdgeLaw_support (h : Fin k → ℕ) (p : ℕ) (targets : Finset ℕ)
    (μ : FiniteLaw (TranslatedCenter Y)) (E : Finset targets)
    (hE : 0 < (baseTargetEdgeLaw h p targets μ).weight E) :
    ∃ n : TranslatedCenter Y, 0 < μ.weight n ∧ initialTargetEdge h p Y targets n.val = E :=
  FiniteLaw.map_support μ _ E hE

theorem baseTargetEdgeLaw_card_le (h : Fin k → ℕ) (p : ℕ) (targets : Finset ℕ)
    (μ : FiniteLaw (TranslatedCenter Y)) (E : Finset targets)
    (hE : 0 < (baseTargetEdgeLaw h p targets μ).weight E) : E.card ≤ k := by
  obtain ⟨n, _, hn⟩ := baseTargetEdgeLaw_support h p targets μ E hE
  rw [← hn]
  exact initialTargetEdge_card_le h p Y targets n.val

theorem baseTargetEdgeLaw_residue (h : Fin k → ℕ) (p : ℕ) (targets : Finset ℕ)
    (μ : FiniteLaw (TranslatedCenter Y)) (E : Finset targets)
    (hE : 0 < (baseTargetEdgeLaw h p targets μ).weight E) :
    ∃ b : ZMod p, ∀ q ∈ E, (q.val : ZMod p) = b := by
  obtain ⟨n, _, hn⟩ := baseTargetEdgeLaw_support h p targets μ E hE
  exact ⟨(n.val : ZMod p) - (Y : ZMod p),
    fun q hq => initialTargetEdge_residue h p Y targets n.val q (hn ▸ hq)⟩

theorem baseTargetEdgeLaw_marginal_le (h : Fin k → ℕ) (hh : Function.Injective h)
    (targets : Finset ℕ) (μ : FiniteLaw (TranslatedCenter Y)) {p : ℕ}
    (hp : 0 < p) (hshift : ∀ i, h i * p ≤ Y) (q : targets)
    (hq0 : 1 ≤ q.val) (hqY : q.val ≤ Y) {α : ℝ} (hatom : ∀ n, μ.weight n ≤ α) :
    (baseTargetEdgeLaw h p targets μ).prob (fun E => q ∈ E) ≤ (k : ℝ) * α := by
  rw [baseTargetEdgeLaw, FiniteLaw.prob_map]
  have heq := μ.prob_congr_iff
    (fun n => q ∈ initialTargetEdge h p Y targets n.val)
    (fun n => q.val ∈ translatedEdge h p Y n.val) (fun n => by
      rw [mem_initialTargetEdge, mem_translatedEdge_iff_sites h p Y n.val hq0 hqY])
  rw [heq]
  exact translatedCenter_incidence_le h hh hp hq0 hqY hshift μ hatom

theorem baseTargetEdgeLaw_pair_source_unique (h : Fin k → ℕ) (hh : Function.Injective h)
    (targets : Finset ℕ) (μ μ' : FiniteLaw (TranslatedCenter Y))
    {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) (hbound : ∀ i, h i < p)
    (q r : targets) (hqr : q ≠ r)
    (hpair : 0 < (baseTargetEdgeLaw h p targets μ).prob (fun E => q ∈ E ∧ r ∈ E))
    (hpair' : 0 < (baseTargetEdgeLaw h p' targets μ').prob (fun E => q ∈ E ∧ r ∈ E)) : p = p' := by
  by_contra hne
  obtain ⟨E, he, hepos⟩ := FiniteLaw.exists_pos_of_prob_pos _ _ hpair
  obtain ⟨E', he', hepos'⟩ := FiniteLaw.exists_pos_of_prob_pos _ _ hpair'
  obtain ⟨n, _, hn⟩ := baseTargetEdgeLaw_support h p targets μ E hepos
  obtain ⟨n', _, hn'⟩ := baseTargetEdgeLaw_support h p' targets μ' E' hepos'
  let instPrime : Fact p.Prime := ⟨hp⟩
  have hsame := translatedSites_common_point_unique h hp hp' (Ne.symm hne)
    (natCast_shifts_injective h hh hbound)
    ((mem_initialTargetEdge h p Y targets n.val q).mp (hn ▸ he.1))
    ((mem_initialTargetEdge h p Y targets n.val r).mp (hn ▸ he.2))
    ((mem_initialTargetEdge h p' Y targets n'.val q).mp (hn' ▸ he'.1))
    ((mem_initialTargetEdge h p' Y targets n'.val r).mp (hn' ▸ he'.2))
  exact hqr (Subtype.ext (Nat.add_right_cancel hsame))

theorem baseTargetEdgeLaw_pair_sum_le (h : Fin k → ℕ) (hh : Function.Injective h)
    (sources targets : Finset ℕ) (μ : ℕ → FiniteLaw (TranslatedCenter Y))
    (hs : ∀ p ∈ sources, p.Prime ∧ ∀ i, h i < p) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmarg : ∀ p ∈ sources, ∀ q : targets, (baseTargetEdgeLaw h p targets (μ p)).prob (fun E => q ∈ E) ≤ δ)
    (q r : targets) (hqr : q ≠ r) :
    pairDegree (fun p : sources => baseTargetEdgeLaw h p.val targets (μ p.val)) q r ≤ δ := by
  apply sum_le_of_unique_positive _ hδ
  · intro p
    exact FiniteLaw.prob_nonneg _ _
  · intro p
    exact (FiniteLaw.prob_mono _ (fun E he => he.1)).trans (hmarg p p.property q)
  · intro p p' hp hp'
    apply Subtype.ext
    exact baseTargetEdgeLaw_pair_source_unique h hh targets (μ p) (μ p')
      (hs p p.property).1 (hs p' p'.property).1 (hs p p.property).2 q r hqr hp hp'

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ) [∀ l, Fact (ell₀ l).Prime] [∀ l, Fact (ell₁ l).Prime]

theorem rational_baseTarget_degree (b : ℝ) (R : ℕ) (h : Fin k → ℕ) (hY : 1 ≤ Y)
    (sources targets : Finset ℕ) (q : targets) (hq0 : 1 ≤ q.val) (hqY : q.val ≤ Y) :
    vertexDegree (fun p : sources => baseTargetEdgeLaw h p.val targets
      (rationalCenterLaw ell₀ ell₁ b R h hY p.val)) q =
      rationalSourceIncidence ell₀ ell₁ b R h hY sources (fun _ => 1) q.val := by
  unfold vertexDegree rationalSourceIncidence
  simp only [one_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [baseTargetEdgeLaw, FiniteLaw.prob_map, rationalBaseIncidence_eq_full ell₀ ell₁ b R h hY p q.val hq0 hqY]
  exact FiniteLaw.prob_congr_iff _ _ _ (fun n => mem_initialTargetEdge h p Y targets n.val q)

end Erdos4.Tilted
