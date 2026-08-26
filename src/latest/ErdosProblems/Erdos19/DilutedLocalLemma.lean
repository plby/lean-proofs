import ErdosProblems.Erdos19.DilutedTailBounds

/-! # From diluted color savings to a proper graph coloring -/

namespace Erdos19

attribute [local instance] Classical.propDecidable

def dilutedRetainedShortfall {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A k : ℕ} (active : Fin A) (t : ℕ) (v : V) :
    Set (V → Fin A × Fin k) :=
  {sample | (retainedCollisionColors G (dilutedSample active sample) v).ncard < t}

theorem dilutedRetainedShortfall_dependsOn {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A k t : ℕ} (active : Fin A) (v : V) :
    EventDependsOn (dilutedRetainedShortfall (k := k) G active t v) (twoStepSupport G v) := by
  intro sample sample' heq
  have hlift : ∀ x ∈ twoStepSupport G v,
      dilutedSample active sample x = dilutedSample active sample' x := by
    intro x hx
    simp only [dilutedSample, heq x hx]
  have hcert := hasRandomCollisionCertificate_iff_of_eqOn_twoStep
    (t := t) G (dilutedSample active sample) (dilutedSample active sample') v hlift
  have hleft := hasRandomCollisionCertificate_iff_le_retainedCollisionColors_ncard
    (t := t) G (dilutedSample active sample) v
  have hright := hasRandomCollisionCertificate_iff_le_retainedCollisionColors_ncard
    (t := t) G (dilutedSample active sample') v
  change (retainedCollisionColors G (dilutedSample active sample) v).ncard < t ↔
    (retainedCollisionColors G (dilutedSample active sample') v).ncard < t
  simp only [← not_le]
  exact not_congr (hleft.symm.trans (hcert.trans hright))

theorem colorable_of_diluted_shortfall_card_bound {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A k Δ t : ℕ} (active : Fin A) (hk : 0 < k)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ) (hgap : Δ + 1 - k ≤ t)
    (hshort : ∀ v, 4 * (Δ + 1) ^ 4 *
      (eventFinset (dilutedRetainedShortfall (k := k) G active t v)).card ≤
        Fintype.card (V → Fin A × Fin k)) : G.Colorable k := by
  classical
  letI : Nonempty (Fin A × Fin k) := ⟨(active, ⟨0, hk⟩)⟩
  let dep : V → V → Prop := fun v w ↦ ¬Disjoint (twoStepSupport G v) (twoStepSupport G w)
  have hdep (v : V) : ((Finset.univ : Finset V).filter (dep v)).card ≤ (Δ + 1) ^ 4 := by
    simpa only [dep, twoStepDependencyFinset] using twoStepDependencyFinset_card_le_pow_four G Δ hdegree v
  obtain ⟨sample, hs⟩ := exists_avoiding_of_local_product_events
    (fun v ↦ dilutedRetainedShortfall (k := k) G active t v) (twoStepSupport G) dep
    ((Δ + 1) ^ 4) (by positivity) hdep (dilutedRetainedShortfall_dependsOn G active)
    (fun h ↦ by simpa only [dep, not_not] using h) hshort
  apply SimpleGraph.colorable_of_no_localColoringBadEvents G hk hdegree hgap (dilutedSample active sample)
  intro v hv
  have hle : t ≤ (retainedCollisionColors G (dilutedSample active sample) v).ncard :=
    Nat.le_of_not_lt (hs v)
  exact hv.2 ((hasRandomCollisionCertificate_iff_le_retainedCollisionColors_ncard
    G (dilutedSample active sample) v).mpr hle)

theorem colorable_of_diluted_tail_parameters {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A k Δ t a b : ℕ} (active : Fin A) (hk : 0 < k)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hmin : ∀ v, 2 ≤ (G.neighborSet v).ncard)
    (hgap : Δ + 1 - k ≤ t) (hab : t + b ≤ a) (hpalette : 2 * Δ ≤ A * k)
    (hambient : 3 * (b + 1) ≤ Fintype.card V)
    (hdelete : ∀ v, 8 * k * (2 * (nonadjacentNeighborPairGraph G v).edgeSet.ncard * Δ) ≤
      (b + 1) * (A * k) ^ 3)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hmargin : ∀ v, (a : ℝ) + epsilon ≤
      ((nonadjacentNeighborPairGraph G v).edgeSet.ncard : ℝ) / (2 * (A : ℝ) ^ 2 * k))
    (hnumeric : ∀ v, ((4 * (Δ + 1) ^ 4 : ℕ) : ℝ) *
      (Real.exp (-epsilon ^ 2 / (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) +
        (1 / 2 : ℝ) ^ (b + 1)) ≤ 1) : G.Colorable k := by
  classical
  letI : Nonempty (Fin A × Fin k) := ⟨(active, ⟨0, hk⟩)⟩
  apply colorable_of_diluted_shortfall_card_bound G active hk hdegree hgap
  intro v
  let T := eventFinset {sample : V → Fin A × Fin k |
    (tentativeCollisionColors G (dilutedSample active sample) v).ncard < a}
  let S := eventFinset {sample : V → Fin A × Fin k |
    b < (spoiledCollisionColors G (dilutedSample active sample) v).ncard}
  let B := eventFinset (dilutedRetainedShortfall (k := k) G active t v)
  let q := Fintype.card (V → Fin A × Fin k)
  let L := 4 * (Δ + 1) ^ 4
  have hq : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hsub : B ⊆ T ∪ S := by
    intro sample hsample
    rw [Finset.mem_union, mem_eventFinset, mem_eventFinset]
    have hs' := (mem_eventFinset _ sample).mp hsample
    exact retainedCollisionShortfallEvent_subset_tentative_union_spoiled G hab v hs'
  have hcard : B.card ≤ T.card + S.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have htent := card_dilutedTentativeShortfall_ratio_le_exp G active v (active, ⟨0, hk⟩)
    a hk (hmin v) ((Nat.mul_le_mul_left 2 (hdegree v)).trans hpalette)
    epsilon hepsilon (hmargin v)
  have hspoil := card_dilutedSpoiledExcess_ratio_le_half_pow G active v b hk hdegree hambient (hdelete v)
  change (T.card : ℝ) / q ≤ _ at htent
  change (S.card : ℝ) / q ≤ _ at hspoil
  have hratio : (B.card : ℝ) / q ≤
      Real.exp (-epsilon ^ 2 / (2 * Fintype.card (G.neighborFinset v) * (2 : ℝ) ^ 2)) +
        (1 / 2 : ℝ) ^ (b + 1) := by
    have hc : (B.card : ℝ) ≤ T.card + S.card := by exact_mod_cast hcard
    exact (div_le_div_of_nonneg_right hc hq.le).trans (by
      rw [add_div]
      exact add_le_add htent hspoil)
  have hmul := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ L by positivity)
  have hbound : (L : ℝ) * B.card ≤ q := by
    have hnumeric' := hnumeric v
    change (L : ℝ) * _ ≤ 1 at hnumeric'
    have h : (L : ℝ) * B.card / q ≤ 1 := by
      rw [mul_div_assoc]
      exact hmul.trans hnumeric'
    exact (div_le_iff₀ hq).mp h |>.trans_eq (one_mul _)
  exact_mod_cast hbound

#print axioms colorable_of_diluted_tail_parameters

end Erdos19
