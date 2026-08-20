import ErdosProblems.Erdos746.BernoulliFinset
import ErdosProblems.Erdos746.BinomialLayers
import ErdosProblems.Erdos746.EdgeTail
import ErdosProblems.Erdos746.ExpansionRangeSums
import ErdosProblems.Erdos746.NeighborhoodCount

/-!
# The binomial and uniform expansion estimates

This file connects the finite Bernoulli edge-subset model to external
neighbourhoods of the corresponding graph and performs the complete
three-range union bound.
-/

open Filter
open scoped BigOperators Topology Sym2

namespace Erdos746

noncomputable section

attribute [local instance] Classical.propDecidable

namespace ExpansionProbability

/-- The possible edges from `S` to a fixed vertex `v`.  When `v` is in
`S` the bundle is empty; otherwise this is the complete cut from `S` to
the singleton `{v}`. -/
def neighborEdgeBundle {n : ℕ} (S : Finset (Fin n)) (v : Fin n) :
    Finset (Edge n) := by
  classical
  by_cases hv : v ∈ S
  · exact ∅
  · exact crossingEdges S {v} (Finset.disjoint_singleton_right.mpr hv)

@[simp] theorem mem_neighborEdgeBundle {n : ℕ} {S : Finset (Fin n)}
    {v : Fin n} {e : Edge n} (hv : v ∉ S) :
    e ∈ neighborEdgeBundle S v ↔
      ∃ u ∈ S, (e : Sym2 (Fin n)) = s(u, v) := by
  classical
  rw [neighborEdgeBundle, dif_neg hv]
  simpa using
    (mem_crossingEdges_iff (Finset.disjoint_singleton_right.mpr hv) e)

@[simp] theorem card_neighborEdgeBundle {n : ℕ} {S : Finset (Fin n)}
    {v : Fin n} (hv : v ∉ S) :
    (neighborEdgeBundle S v).card = S.card := by
  classical
  rw [neighborEdgeBundle, dif_neg hv,
    card_crossingEdges S {v} (Finset.disjoint_singleton_right.mpr hv)]
  simp

/-- The edge bundles belonging to distinct outside vertices are disjoint. -/
theorem pairwiseDisjoint_neighborEdgeBundle {n : ℕ} (S : Finset (Fin n)) :
    BernoulliFinset.PairwiseDisjointBundles (Finset.univ \ S)
      (neighborEdgeBundle S) := by
  classical
  intro v hv w hw hvw
  rw [Finset.disjoint_left]
  intro e hev hew
  have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
  have hwS : w ∉ S := (Finset.mem_sdiff.mp hw).2
  rw [mem_neighborEdgeBundle hvS] at hev
  rw [mem_neighborEdgeBundle hwS] at hew
  obtain ⟨u, huS, huv⟩ := hev
  obtain ⟨u', hu'S, hu'w⟩ := hew
  have hsym : s(u, v) = s(u', w) := huv.symm.trans hu'w
  rw [Sym2.eq_iff] at hsym
  rcases hsym with hsame | hswap
  · exact hvw (hsame.2)
  · exact hvS (hswap.2.symm ▸ hu'S)

/-- A bundle is occupied precisely when the corresponding outside vertex
belongs to the graph's external neighbourhood. -/
theorem nonempty_inter_neighborEdgeBundle_iff {n : ℕ}
    (A : Finset (Edge n)) (S : Finset (Fin n)) {v : Fin n} (hv : v ∉ S) :
    (A ∩ neighborEdgeBundle S v).Nonempty ↔
      ∃ u ∈ S, (graphOfEdges A).Adj u v := by
  classical
  constructor
  · rintro ⟨e, he⟩
    have heA := (Finset.mem_inter.mp he).1
    have heB := (mem_neighborEdgeBundle hv).mp (Finset.mem_inter.mp he).2
    obtain ⟨u, huS, heu⟩ := heB
    refine ⟨u, huS, ?_⟩
    rw [← SimpleGraph.mem_edgeSet, edgeSet_graphOfEdges]
    change s(u, v) ∈ A.map (edgeEmbedding n)
    rw [Finset.mem_map]
    exact ⟨e, heA, heu⟩
  · rintro ⟨u, huS, huv⟩
    rw [← SimpleGraph.mem_edgeSet, edgeSet_graphOfEdges] at huv
    change s(u, v) ∈ A.map (edgeEmbedding n) at huv
    rw [Finset.mem_map] at huv
    obtain ⟨e, heA, heu⟩ := huv
    refine ⟨e, Finset.mem_inter.mpr ⟨heA, ?_⟩⟩
    rw [mem_neighborEdgeBundle hv]
    exact ⟨u, huS, heu⟩

/-- The bundle occupancy set is definitionally the graph's external
neighbourhood.  This is the graph adapter for the exact binomial law. -/
theorem occupiedBundles_eq_outerNeighborFinset {n : ℕ}
    (A : Finset (Edge n)) (S : Finset (Fin n)) :
    BernoulliFinset.occupiedBundles (Finset.univ \ S)
        (neighborEdgeBundle S) A =
      (graphOfEdges A).outerNeighborFinset S := by
  classical
  ext v
  rw [BernoulliFinset.occupiedBundles, Finset.mem_filter,
    SimpleGraph.mem_outerNeighborFinset]
  constructor
  · rintro ⟨hv, hne⟩
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    exact ⟨hvS, (nonempty_inter_neighborEdgeBundle_iff A S hvS).mp hne⟩
  · rintro ⟨hvS, hne⟩
    exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvS⟩,
      (nonempty_inter_neighborEdgeBundle_iff A S hvS).mpr hne⟩

/-- All coordinates in a bundle belong to the complete edge universe. -/
theorem bundleUnion_subset_univ {n : ℕ} (S : Finset (Fin n)) :
    BernoulliFinset.bundleUnion (Finset.univ \ S)
        (neighborEdgeBundle S) ⊆ (Finset.univ : Finset (Edge n)) :=
  Finset.subset_univ _

/-- The two finite Bernoulli-mass definitions used by the layer coupling and
by the bundle calculation agree exactly. -/
theorem bernoulliEventMass_eq_eventMass {n : ℕ} (p : ℝ)
    (P : Finset (Edge n) → Prop) :
    bernoulliEventMass (Finset.univ : Finset (Edge n)) p P =
      BernoulliFinset.eventMass (Finset.univ : Finset (Edge n)) p P := by
  classical
  rfl

/-- **Exact fixed-set external-neighbour law in the finite edge model.**
For a fixed `S`, the number of external neighbours of `S` in the graph
obtained by choosing every edge independently with probability `p` has the
binomial distribution with `n-|S|` trials and success probability
`1-(1-p)^|S|`. -/
theorem bernoulli_fixed_outerNeighbor_card_eq {n : ℕ}
    (p : ℝ) (S : Finset (Fin n)) (r : ℕ) :
    bernoulliEventMass (Finset.univ : Finset (Edge n)) p
        (fun A ↦ ((graphOfEdges A).outerNeighborFinset S).card = r) =
      binomialTerm (n - S.card) (1 - (1 - p) ^ S.card) r := by
  classical
  let I : Finset (Fin n) := Finset.univ \ S
  let B : Fin n → Finset (Edge n) := neighborEdgeBundle S
  have hpair : BernoulliFinset.PairwiseDisjointBundles I B := by
    simpa [I, B] using pairwiseDisjoint_neighborEdgeBundle S
  have hcard : ∀ v ∈ I, (B v).card = S.card := by
    intro v hv
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    simpa [B] using card_neighborEdgeBundle hvS
  have hIcard : I.card = n - S.card := by
    simp [I, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  rw [bernoulliEventMass_eq_eventMass]
  have hevent :
      (fun A : Finset (Edge n) ↦
          ((graphOfEdges A).outerNeighborFinset S).card = r) =
        (fun A ↦ (BernoulliFinset.occupiedBundles I B A).card = r) := by
    funext A
    rw [show BernoulliFinset.occupiedBundles I B A =
        (graphOfEdges A).outerNeighborFinset S by
      simpa [I, B] using occupiedBundles_eq_outerNeighborFinset A S]
  rw [hevent]
  simpa [hIcard] using
    BernoulliFinset.eventMass_occupiedBundles_card_eq_of_subset
      (Finset.univ : Finset (Edge n)) I B (bundleUnion_subset_univ S)
      hpair hcard p r

/-- Exact strict lower-tail form of
`bernoulli_fixed_outerNeighbor_card_eq`. -/
theorem bernoulli_fixed_outerNeighbor_card_lt {n : ℕ}
    (p : ℝ) (S : Finset (Fin n)) (K : ℕ) :
    bernoulliEventMass (Finset.univ : Finset (Edge n)) p
        (fun A ↦ ((graphOfEdges A).outerNeighborFinset S).card < K) =
      binomialLowerTail (n - S.card) K
        (1 - (1 - p) ^ S.card) := by
  classical
  let I : Finset (Fin n) := Finset.univ \ S
  let B : Fin n → Finset (Edge n) := neighborEdgeBundle S
  have hpair : BernoulliFinset.PairwiseDisjointBundles I B := by
    simpa [I, B] using pairwiseDisjoint_neighborEdgeBundle S
  have hcard : ∀ v ∈ I, (B v).card = S.card := by
    intro v hv
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    simpa [B] using card_neighborEdgeBundle hvS
  have hIcard : I.card = n - S.card := by
    simp [I, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  rw [bernoulliEventMass_eq_eventMass]
  have hevent :
      (fun A : Finset (Edge n) ↦
          ((graphOfEdges A).outerNeighborFinset S).card < K) =
        (fun A ↦ (BernoulliFinset.occupiedBundles I B A).card < K) := by
    funext A
    rw [show BernoulliFinset.occupiedBundles I B A =
        (graphOfEdges A).outerNeighborFinset S by
      simpa [I, B] using occupiedBundles_eq_outerNeighborFinset A S]
  rw [hevent]
  simpa [hIcard] using
    BernoulliFinset.eventMass_occupiedBundles_card_lt_of_subset
      (Finset.univ : Finset (Edge n)) I B (bundleUnion_subset_univ S)
      hpair hcard p K

/-- Candidate vertex sets for the finite expansion union bound. -/
def expansionWitnesses (n k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ.powerset).filter fun S ↦ S.card ≤ k

/-- Failure of two-expansion is exactly the union of the fixed-set
lower-tail events over `expansionWitnesses`. -/
theorem not_isTwoExpanderUpTo_iff_exists_witness {n k : ℕ}
    (A : Finset (Edge n)) :
    ¬(graphOfEdges A).IsTwoExpanderUpTo k ↔
      ∃ S ∈ expansionWitnesses n k,
        ((graphOfEdges A).outerNeighborFinset S).card < 2 * S.card := by
  classical
  constructor
  · intro h
    rw [SimpleGraph.IsTwoExpanderUpTo] at h
    push Not at h
    obtain ⟨S, hSk, hbad⟩ := h
    exact ⟨S, by simp [expansionWitnesses, hSk], hbad⟩
  · rintro ⟨S, hS, hbad⟩ hExp
    have hSk : S.card ≤ k := by
      simpa [expansionWitnesses] using hS
    exact (Nat.not_le.mpr hbad) (hExp S hSk)

/-- The complete finite union bound, grouped by the cardinality of the bad
vertex set.  This theorem is the exact graph-level bridge used by all three
asymptotic ranges. -/
theorem binomial_twoExpanderFailure_le_size_sum
    (n k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hk : k ≤ n) :
    binomialGraphPropertyFailure n p
        (fun G ↦ G.IsTwoExpanderUpTo k) ≤
      ∑ s ∈ Finset.range (k + 1),
        (n.choose s : ℝ) *
          binomialLowerTail (n - s) (2 * s)
            (1 - (1 - p) ^ s) := by
  classical
  let U : Finset (Edge n) := Finset.univ
  let W := expansionWitnesses n k
  let bad : Finset (Fin n) → Finset (Edge n) → Prop :=
    fun S A ↦ ((graphOfEdges A).outerNeighborFinset S).card < 2 * S.card
  have hmass := BernoulliFinset.eventMass_exists_mem_le_sum
    U hp0 hp1 W bad
  have hleft :
      binomialGraphPropertyFailure n p
          (fun G ↦ G.IsTwoExpanderUpTo k) =
        BernoulliFinset.eventMass U p
          (fun A ↦ ∃ S ∈ W, bad S A) := by
    unfold binomialGraphPropertyFailure binomialGraphPropertyProbability
    rw [bernoulliEventMass_eq_eventMass]
    congr 1
    funext A
    exact propext (not_isTwoExpanderUpTo_iff_exists_witness A)
  rw [hleft]
  refine hmass.trans_eq ?_
  have hfixed : ∀ S ∈ W,
      BernoulliFinset.eventMass U p (bad S) =
        binomialLowerTail (n - S.card) (2 * S.card)
          (1 - (1 - p) ^ S.card) := by
    intro S hS
    rw [← bernoulliEventMass_eq_eventMass]
    exact bernoulli_fixed_outerNeighbor_card_lt p S (2 * S.card)
  calc
    (∑ S ∈ W, BernoulliFinset.eventMass U p (bad S)) =
        ∑ S ∈ W,
          binomialLowerTail (n - S.card) (2 * S.card)
            (1 - (1 - p) ^ S.card) := by
      apply Finset.sum_congr rfl
      exact hfixed
    _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          if S.card ≤ k then
            binomialLowerTail (n - S.card) (2 * S.card)
              (1 - (1 - p) ^ S.card)
          else 0 := by
      simp only [W, expansionWitnesses, Finset.sum_filter]
    _ = ∑ s ∈ Finset.range (n + 1),
          (n.choose s : ℝ) *
            (if s ≤ k then
              binomialLowerTail (n - s) (2 * s)
                (1 - (1 - p) ^ s)
            else 0) := by
      let f : ℕ → ℝ := fun s ↦
        if s ≤ k then
          binomialLowerTail (n - s) (2 * s) (1 - (1 - p) ^ s)
        else 0
      change (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset, f S.card) =
        ∑ s ∈ Finset.range (n + 1), (n.choose s : ℝ) * f s
      simpa [nsmul_eq_mul] using
        (Finset.sum_powerset_apply_card f
          (x := (Finset.univ : Finset (Fin n))))
    _ = ∑ s ∈ Finset.range (k + 1),
          (n.choose s : ℝ) *
            binomialLowerTail (n - s) (2 * s)
              (1 - (1 - p) ^ s) := by
      rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk))]
      · apply Finset.sum_congr rfl
        intro s hs
        have hsk : s ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hs)
        simp [hsk]
      · intro s hsn hsk
        have hnot : ¬s ≤ k := by
          intro hle
          exact hsk (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
        simp [hnot]

/-- In the binomial graph with edge density
`(1 + ρ / 2) log n / n`, two-expansion through sets of size `n / 4`
fails with probability tending to zero. -/
theorem tendsto_binomial_twoExpanderFailure_zero {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto
      (fun n : ℕ ↦ binomialGraphPropertyFailure n
        (clippedEdgeProbability (ρ / 2) n)
        (fun G ↦ G.IsTwoExpanderUpTo (n / 4)))
      atTop (nhds 0) := by
  let η : ℝ := ρ / 2
  let c : ℝ := 1 + η
  let δ : ℝ := min η 1
  have hη : 0 < η := by dsimp [η]; linarith
  have hc : 0 < c := by dsimp [c]; linarith
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hη zero_lt_one
  have hδ1 : δ ≤ 1 := by exact min_le_right _ _
  have hmargin : 1 + δ ≤ c := by
    dsimp [c, δ]
    linarith [min_le_left η 1]
  have hsum : Tendsto
      (fun n : ℕ ↦ ∑ s ∈ Finset.range (n / 4 + 1),
        expansionBinomialUnionTerm c n s) atTop (nhds 0) :=
    tendsto_totalExpansionBinomialUnionTerm_zero_general hc hδ hδ1 hmargin
  have hclip := eventually_clippedEdgeProbability_eq_raw hη
  have hupper : ∀ᶠ n : ℕ in atTop,
      binomialGraphPropertyFailure n (clippedEdgeProbability η n)
          (fun G ↦ G.IsTwoExpanderUpTo (n / 4)) ≤
        ∑ s ∈ Finset.range (n / 4 + 1),
          expansionBinomialUnionTerm c n s := by
    filter_upwards [hclip] with n hclipN
    have hbound := binomial_twoExpanderFailure_le_size_sum n (n / 4)
      (clippedEdgeProbability η n)
      (clippedEdgeProbability_nonneg η n)
      (clippedEdgeProbability_le_one η n) (Nat.div_le_self n 4)
    refine hbound.trans_eq ?_
    apply Finset.sum_congr rfl
    intro s hs
    unfold expansionBinomialUnionTerm rangeOneSuccess rangeOneProbability
    rw [hclipN]
    unfold rawEdgeProbability c
    ring
  have hnonneg : ∀ n : ℕ,
      0 ≤ binomialGraphPropertyFailure n (clippedEdgeProbability η n)
        (fun G ↦ G.IsTwoExpanderUpTo (n / 4)) := by
    intro n
    rw [binomialGraphPropertyFailure_eq_sum]
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg
      (binomialTerm_nonneg (clippedEdgeProbability_nonneg η n)
        (clippedEdgeProbability_le_one η n))
      (uniformProbability_nonneg _)
  apply squeeze_zero' (Eventually.of_forall hnonneg) hupper
  simpa [η, c] using hsum

/-- The base edge layer is eventually a valid layer of the complete graph. -/
theorem eventually_baseEdgeCount_le_edgeCount {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, baseEdgeCount η n ≤ edgeCount n := by
  let c : ℝ := 1 / 2 + η
  have hc : 0 < c := by dsimp [c]; linarith
  have hsmall := tendsto_log_div_nat.eventually
    (Iio_mem_nhds (show 0 < 1 / (4 * c) by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 2] with n hsmall hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hloglt : Real.log (n : ℝ) < (n : ℝ) / (4 * c) := by
    rw [div_lt_iff₀ hnpos] at hsmall
    simpa [div_eq_mul_inv, mul_comm] using hsmall
  have hhalf : (n : ℝ) / 2 ≤ (n - 1 : ℕ) := by
    have hnNat : n ≤ 2 * (n - 1) := by omega
    have hnReal : (n : ℝ) ≤ 2 * (n - 1 : ℕ) := by
      exact_mod_cast hnNat
    nlinarith
  have hlin : 2 * c * Real.log (n : ℝ) ≤ (n - 1 : ℕ) := by
    have h := mul_lt_mul_of_pos_left hloglt (show 0 < 2 * c by positivity)
    calc
      2 * c * Real.log (n : ℝ) ≤ (n : ℝ) / 2 := by
        apply le_of_lt
        calc
          2 * c * Real.log (n : ℝ) < 2 * c * ((n : ℝ) / (4 * c)) := h
          _ = (n : ℝ) / 2 := by field_simp [hc.ne']; ring
      _ ≤ (n - 1 : ℕ) := hhalf
  have hreal : c * (n : ℝ) * Real.log (n : ℝ) ≤ (edgeCount n : ℝ) := by
    rw [edgeCount, Nat.cast_choose_two]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    calc
      c * (n : ℝ) * Real.log (n : ℝ) =
          (n : ℝ) * (2 * c * Real.log (n : ℝ)) / 2 := by ring
      _ ≤ (n : ℝ) * (n - 1 : ℕ) / 2 := by gcongr
      _ = (n : ℝ) * ((n : ℝ) - 1) / 2 := by rw [hcast]
  apply Nat.ceil_le.mpr
  simpa [baseEdgeCount, c] using hreal

/-- Transfer an asymptotically vanishing binomial expansion failure to the
uniform base layer. -/
theorem tendsto_twoExpanderProbability_base_of_binomial
    {η : ℝ} (hη : 0 < η)
    (hbin : Tendsto
      (fun n : ℕ ↦ binomialGraphPropertyFailure n
        (clippedEdgeProbability η n)
        (fun G ↦ G.IsTwoExpanderUpTo (n / 4)))
      atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦ twoExpanderProbability n (baseEdgeCount η n) (n / 4))
      atTop (nhds 1) := by
  let bf : ℕ → ℝ := fun n ↦ binomialGraphPropertyFailure n
    (clippedEdgeProbability η n)
    (fun G ↦ G.IsTwoExpanderUpTo (n / 4))
  let uf : ℕ → ℝ := fun n ↦ graphPropertyFailure n (baseEdgeCount η n)
    (fun G ↦ G.IsTwoExpanderUpTo (n / 4))
  have hvalid := eventually_baseEdgeCount_le_edgeCount hη
  have htail := eventually_edgeCountUpperTail_le_half hη
  have hupper : ∀ᶠ n : ℕ in atTop, uf n ≤ 2 * bf n := by
    filter_upwards [hvalid, htail] with n hn htailn
    exact graphPropertyFailure_le_two_mul_binomialFailure
      (fun G : SimpleGraph (Fin n) ↦ G.IsTwoExpanderUpTo (n / 4))
      (fun _G _H hGH hG ↦ isTwoExpanderUpTo_mono hGH hG)
      (clippedEdgeProbability η n)
      (clippedEdgeProbability_nonneg η n)
      (clippedEdgeProbability_le_one η n) hn
      (by simpa [edgeCountUpperTail, baseEdgeCount, edgeCount] using htailn)
  have huf0 : Tendsto uf atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ uniformProbability_nonneg _
    · exact hupper
    · have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
        tendsto_const_nhds
      have hbf : Tendsto bf atTop (nhds 0) := by simpa [bf] using hbin
      simpa using htwo.mul hbf
  have hsuccess : ∀ᶠ n : ℕ in atTop,
      twoExpanderProbability n (baseEdgeCount η n) (n / 4) = 1 - uf n := by
    filter_upwards [hvalid] with n hn
    have hfail := graphPropertyFailure_eq_one_sub
      (fun G : SimpleGraph (Fin n) ↦ G.IsTwoExpanderUpTo (n / 4)) hn
    change graphPropertyProbability n (baseEdgeCount η n)
        (fun G ↦ G.IsTwoExpanderUpTo (n / 4)) =
      1 - graphPropertyProbability n (baseEdgeCount η n)
        (fun G ↦ ¬G.IsTwoExpanderUpTo (n / 4))
    linarith
  have hsub : Tendsto (fun n : ℕ ↦ (1 : ℝ) - uf n) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub huf0
  norm_num at hsub
  apply hsub.congr'
  filter_upwards [hsuccess] with n hn
  simpa [uf] using hn.symm

/-- The uniform graph at the Erdős--Rényi base threshold
`ceil ((1/2+ρ/2) n log n)` is a two-expander up to `n/4` with
probability tending to one. -/
theorem tendsto_twoExpanderProbability_base {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto
      (fun n : ℕ ↦
        twoExpanderProbability n (baseEdgeCount (ρ / 2) n) (n / 4))
      atTop (nhds 1) :=
  tendsto_twoExpanderProbability_base_of_binomial (by linarith : 0 < ρ / 2)
    (tendsto_binomial_twoExpanderFailure_zero hρ)

end ExpansionProbability

end

end Erdos746
