/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/

import ErdosProblems.Erdos182.LowerBridge
import ErdosProblems.Erdos182.LowerUnion
import ErdosProblems.Erdos182.LowerPackaging

/-!
# The Pyber--Rödl--Szemerédi lower construction

This file assembles the exact finite layered construction, its simultaneous
bad-event count, and isolated-vertex padding.  The resulting graph has exactly
`n` vertices, has order `n log log n` edges, and contains no regular subgraph
of any degree at least three.
-/

open Finset Fintype Filter

namespace Erdos182

open scoped BigOperators Classical

noncomputable section

/-- The sizes of the base layer and the `C-1` random later layers. -/
def prsShiftedLayerSizes (n : ℕ) :
    Option (Fin (prsLayerCount n - 1)) → ℕ
  | none => prsLayerSize n 0
  | some j => prsLayerSize n ((j : ℕ) + 1)

/-- The canonical inclusion of the dependent sum of later layers into all
layered vertices. -/
def laterVertexEmbedding {L : ℕ} (b : Option (Fin L) → ℕ) :
    (Σ j : Fin L, Fin (b (some j))) ↪ LayerVertex b where
  toFun x := ⟨some x.1, x.2⟩
  inj' := by
    rintro ⟨j, v⟩ ⟨k, w⟩ h
    cases h
    rfl

@[simp] lemma prsShiftedLayerSizes_none (n : ℕ) :
    prsShiftedLayerSizes n none = prsLayerSize n 0 := rfl

@[simp] lemma prsShiftedLayerSizes_some (n : ℕ)
    (j : Fin (prsLayerCount n - 1)) :
    prsShiftedLayerSizes n (some j) = prsLayerSize n ((j : ℕ) + 1) := rfl

/-- The dependent sum of the active layers has the expected cardinality. -/
lemma card_prsLayerVertex (n : ℕ) (hcount : 1 ≤ prsLayerCount n) :
    Fintype.card (LayerVertex (prsShiftedLayerSizes n)) =
      ∑ i ∈ Finset.range (prsLayerCount n), prsLayerSize n i := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fintype.sum_option]
  simp only [prsShiftedLayerSizes_none, prsShiftedLayerSizes_some]
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ prsLayerSize n (i + 1)) (prsLayerCount n - 1)]
  calc
    prsLayerSize n 0 +
          ∑ i ∈ Finset.range (prsLayerCount n - 1), prsLayerSize n (i + 1) =
        (∑ i ∈ Finset.range (prsLayerCount n - 1), prsLayerSize n (i + 1)) +
          prsLayerSize n 0 := Nat.add_comm _ _
    _ = ∑ i ∈ Finset.range (prsLayerCount n - 1 + 1), prsLayerSize n i :=
      (Finset.sum_range_succ' (fun i ↦ prsLayerSize n i)
        (prsLayerCount n - 1)).symm
    _ = ∑ i ∈ Finset.range (prsLayerCount n), prsLayerSize n i := by
      rw [Nat.sub_add_cancel hcount]

lemma card_laterLayerVertices {L : ℕ} (b : Option (Fin L) → ℕ) :
    (Finset.univ \ baseLayer b).card = ∑ j : Fin L, b (some j) := by
  classical
  let source : Finset (Σ j : Fin L, Fin (b (some j))) :=
    Finset.univ.sigma fun _ ↦ Finset.univ
  have heq : Finset.univ \ baseLayer b =
      source.map (laterVertexEmbedding b) := by
    ext v
    rcases v with ⟨_ | j, v⟩
    · constructor
      · simp [baseLayer]
      · intro h
        obtain ⟨x, _hx, hx⟩ := Finset.mem_map.mp h
        have := congrArg Sigma.fst hx
        simp [laterVertexEmbedding] at this
    · constructor
      · intro _
        apply Finset.mem_map.mpr
        exact ⟨⟨j, v⟩, by simp [source], rfl⟩
      · simp [baseLayer]
  rw [heq, Finset.card_map, Finset.card_sigma]
  simp [source]

lemma card_layerStrictTail_eq_sum {L : ℕ} (b : Option (Fin L) → ℕ)
    (i : Fin L) :
    (layerStrictTail b i).card = ∑ j : Fin L with i < j, b (some j) := by
  classical
  let source : Finset (Σ j : Fin L, Fin (b (some j))) :=
    (Finset.univ.filter fun j : Fin L ↦ i < j).sigma fun _ ↦ Finset.univ
  have heq : layerStrictTail b i =
      source.map (laterVertexEmbedding b) := by
    ext v
    rcases v with ⟨_ | j, v⟩
    · constructor
      · simp [layerStrictTail]
      · intro h
        obtain ⟨x, _hx, hx⟩ := Finset.mem_map.mp h
        have := congrArg Sigma.fst hx
        simp [laterVertexEmbedding] at this
    · constructor
      · intro h
        have hij : i < j := by simpa [layerStrictTail] using h
        apply Finset.mem_map.mpr
        exact ⟨⟨j, v⟩, by simp [source, hij], rfl⟩
      · intro h
        obtain ⟨⟨k, w⟩, hk, heq⟩ := Finset.mem_map.mp h
        have hkj : k = j := Option.some.inj (congrArg Sigma.fst heq)
        subst k
        simpa [layerStrictTail] using (by simpa [source] using hk : i < j)
  rw [heq, Finset.card_map, Finset.card_sigma]
  simp [source]

lemma card_prsLayerStrictTail (n : ℕ) (hcount : 2 ≤ prsLayerCount n)
    (i : Fin (prsLayerCount n - 1)) :
    (layerStrictTail (prsShiftedLayerSizes n) i).card =
      ∑ j ∈ Finset.Ico (i.val + 2) (prsLayerCount n), prsLayerSize n j := by
  rw [card_layerStrictTail_eq_sum]
  rw [Finset.sum_filter]
  simp only [prsShiftedLayerSizes_some]
  have hfin :
      (∑ a : Fin (prsLayerCount n - 1),
          if i < a then prsLayerSize n (a.val + 1) else 0) =
        ∑ a : Fin (prsLayerCount n - 1),
          if i.val < a.val then prsLayerSize n (a.val + 1) else 0 := by
    apply Finset.sum_congr rfl
    intro a _ha
    rfl
  rw [hfin]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ if i.val < j then prsLayerSize n (j + 1) else 0)
    (prsLayerCount n - 1)]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.range (prsLayerCount n - 1)).filter (fun j ↦ i.val < j) =
        Finset.Ico (i.val + 1) (prsLayerCount n - 1) := by
    ext j
    simp
    omega
  rw [hfilter, Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have hlen : prsLayerCount n - 1 - (i.val + 1) =
      prsLayerCount n - (i.val + 2) := by omega
  rw [hlen]
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  omega

lemma card_prsLaterLayerVertices (n : ℕ) :
    (Finset.univ \ baseLayer (prsShiftedLayerSizes n)).card =
      ∑ j ∈ Finset.Ico 1 (prsLayerCount n), prsLayerSize n j := by
  rw [card_laterLayerVertices]
  simp only [prsShiftedLayerSizes_some]
  rw [Fin.sum_univ_eq_sum_range
    (fun j ↦ prsLayerSize n (j + 1)) (prsLayerCount n - 1)]
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr
  · congr
  · intro j _hj
    congr 1
    omega

lemma prsLayerSize_antitone_below {n a z : ℕ}
    (hstep : ∀ i, i + 1 < prsLayerCount n →
      prsLayerSize n (i + 1) ≤ prsLayerSize n i)
    (haz : a ≤ z) (hz : z < prsLayerCount n) :
    prsLayerSize n z ≤ prsLayerSize n a := by
  induction z, haz using Nat.le_induction with
  | base => exact le_rfl
  | succ z haz ih =>
      exact (hstep z (by omega)).trans (ih (by omega))

lemma card_prefixCandidateCoordinateDemands_le_choose
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (i : Fin L) (r : ℕ) (S : Finset (LayerVertex b)) :
    (prefixCandidateCoordinateDemands default i r S).card ≤
      (S.card.choose 2).choose r := by
  classical
  by_cases hS : S ⊆ layerPrefix b i
  · simpa [prefixCandidateCoordinateDemands, hS] using
      card_candidateCoordinateDemands_le_choose default S r
  · simp [prefixCandidateCoordinateDemands, hS]

lemma coords_card_of_mem_prefixCandidateCoordinateDemands
    {L : ℕ} {b : Option (Fin L) → ℕ}
    (default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (i : Fin L) (r : ℕ) (S : Finset (LayerVertex b))
    {d : CoordinateDemand (LayerCoordinate b) (LaterLayerVertex b)}
    (hd : d ∈ prefixCandidateCoordinateDemands default i r S) :
    d.coords.card = r := by
  classical
  by_cases hS : S ⊆ layerPrefix b i
  · exact coords_card_of_mem_candidateCoordinateDemands default S r
      (by simpa [prefixCandidateCoordinateDemands, hS] using hd)
  · simp [prefixCandidateCoordinateDemands, hS] at hd

/-- Every coordinate occurring in a prefix demand targets a layer strictly
before the cutoff. -/
lemma layerAllowed_card_lower_of_mem_prefixCandidateCoordinateDemands
    {L B : ℕ} {b : Option (Fin L) → ℕ}
    (default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b))
    (i : Fin L) (r : ℕ) (S : Finset (LayerVertex b))
    (hmono : ∀ k : Fin L, k < i → B ≤ b (some k))
    {d : CoordinateDemand (LayerCoordinate b) (LaterLayerVertex b)}
    (hd : d ∈ prefixCandidateCoordinateDemands default i r S)
    {c : LayerCoordinate b} (hc : c ∈ d.coords) :
    B ≤ (layerAllowed b c).card := by
  classical
  by_cases hS : S ⊆ layerPrefix b i
  · have hd' : d ∈ candidateCoordinateDemands default S r := by
      simpa [prefixCandidateCoordinateDemands, hS] using hd
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hd'
    obtain ⟨hRpower, _hRcompat⟩ := Finset.mem_filter.mp hR
    obtain ⟨e, heR, hec⟩ := Finset.mem_image.mp hc
    have heCandidate : e ∈ candidateLayerDemands S :=
      (Finset.mem_powersetCard.mp hRpower).1 heR
    have heTarget : laterVertex e.1.2 e.2 ∈ S :=
      (mem_candidateLayerDemands.mp heCandidate).2
    have hePrefix := hS heTarget
    have hei : e.1.2 < i := by
      rw [mem_layerPrefix] at hePrefix
      rcases hePrefix with heNone | ⟨k, hk, hki⟩
      · simp [laterVertex] at heNone
      · have hke : k = e.1.2 := Option.some.inj (by
          simpa [laterVertex] using hk.symm)
        simpa [hke] using hki
    have hci : c.2 < i := by
      rw [← hec]
      exact hei
    simpa [card_layerAllowed] using hmono c.2 hci
  · simp [prefixCandidateCoordinateDemands, hS] at hd

/-- Choose the last scale whose layer is still at least `s/1000`.  The
geometric tail estimate then makes every strictly later layer negligible. -/
lemma exists_layerScale_of_tail
    {L : ℕ} (b : Option (Fin L) → ℕ) (hL : 0 < L) (s : ℕ) (hs : 0 < s)
    (hstart : s ≤ 1000 * b (some ⟨0, hL⟩))
    (htail : ∀ (i : Fin L) (hi : i.val + 1 < L),
      (layerStrictTail b i).card ≤
        2 * b (some ⟨i.val + 1, hi⟩)) :
    ∃ i : Fin L,
      s ≤ 1000 * b (some i) ∧ 500 * (layerStrictTail b i).card < s := by
  classical
  let P : ℕ → Prop := fun t ↦ ∃ ht : t < L,
    s ≤ 1000 * b (some ⟨t, ht⟩)
  let m := Nat.findGreatest P (L - 1)
  have hmle : m ≤ L - 1 := Nat.findGreatest_le _
  have hmL : m < L := by omega
  have hPm : P m := by
    apply Nat.findGreatest_spec (P := P) (Nat.zero_le _)
    exact ⟨hL, hstart⟩
  obtain ⟨_hmL', hmbound⟩ := hPm
  let i : Fin L := ⟨m, hmL⟩
  refine ⟨i, ?_, ?_⟩
  · exact hmbound
  · by_cases hnext : m + 1 < L
    · have hnot : ¬P (m + 1) := by
        intro hPnext
        have hle : m + 1 ≤ m := by
          apply Nat.le_findGreatest (P := P)
          · omega
          · exact hPnext
        omega
      have hsnext : 1000 * b (some ⟨m + 1, hnext⟩) < s := by
        by_contra hnlt
        apply hnot
        exact ⟨hnext, Nat.le_of_not_gt hnlt⟩
      have ht := htail i (by simpa [i] using hnext)
      have ht' : (layerStrictTail b i).card ≤
          2 * b (some ⟨m + 1, hnext⟩) := by
        simpa [i] using ht
      change 500 * (layerStrictTail b i).card < s
      omega
    · have hiLast : i.val = L - 1 := by
        dsimp [i]
        omega
      have htailEmpty : layerStrictTail b i = ∅ := by
        ext v
        constructor
        · intro hv
          have hv' : ∃ j : Fin L, v.1 = some j ∧ i < j := by
            simpa [layerStrictTail] using hv
          obtain ⟨j, _hj, hij⟩ := hv'
          have hjle : j.val ≤ L - 1 := by omega
          have hij' : i.val < j.val := hij
          omega
        · simp
      simp [htailEmpty, hs]

/-- Exact-order PRS witnesses, simultaneously avoiding every regular degree
at least three. -/
theorem prs_allDegreeWitness :
    ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n),
      (1 / 60 : ℝ) * (n : ℝ) * logLog n ≤ (G.edgeFinset.card : ℝ) ∧
        ∀ q : ℕ, 3 ≤ q → IsRegularSubgraphFree G q := by
  filter_upwards [eventually_two_le_prsLayerCount,
      eventually_prsLayerSize_bounds, eventually_prsLayer_sum_le,
      eventually_prsLayer_tail_le,
      eventually_four_thousand_mul_prsLayerSize_succ_le,
      eventually_prs_edge_count_lower, eventually_prs_error_lt_one,
      eventually_prs_badEvent_choose_bound] with
      n hcount hlayer hsum htail hseparate hedge herror honeEvent
  classical
  let b := prsShiftedLayerSizes n
  have hcard : Fintype.card (LayerVertex b) ≤ n := by
    rw [show Fintype.card (LayerVertex b) =
      Fintype.card (LayerVertex (prsShiftedLayerSizes n)) by rfl,
      card_prsLayerVertex n (by omega)]
    exact hsum
  have hlayerPos : ∀ i < prsLayerCount n, 0 < prsLayerSize n i :=
    fun i hi ↦ (hlayer i hi).1
  have hallowed : ∀ c : LayerCoordinate b, (layerAllowed b c).Nonempty := by
    intro c
    apply Finset.card_pos.mp
    rw [card_layerAllowed]
    change 0 < prsLayerSize n (c.2.val + 1)
    apply hlayerPos
    omega
  choose target htarget using hallowed
  let default : FiniteChoiceOutcome (LayerCoordinate b) (LaterLayerVertex b) :=
    fun c _hc ↦ target c
  have hdefault : default ∈ finiteChoiceSpace (layerAllowed b) := by
    rw [mem_finiteChoiceSpace]
    intro c
    exact htarget c
  have hstep : ∀ i, i + 1 < prsLayerCount n →
      prsLayerSize n (i + 1) ≤ prsLayerSize n i := by
    intro i hi
    have := hseparate i hi
    omega
  have hhalf : Real.exp (-(prsY n / 2)) ≤ (1 / 2 : ℝ) := by
    have hcountR : (2 : ℝ) ≤ prsLayerCount n := by exact_mod_cast hcount
    have hmul : 2 * 2 * Real.exp (-(prsY n / 2)) ≤
        2 * (prsLayerCount n : ℝ) * Real.exp (-(prsY n / 2)) := by
      gcongr
    linarith [Real.exp_pos (-(prsY n / 2))]
  obtain ⟨ω, hω, hAvoid⟩ :=
    exists_choice_avoiding_shifted_prs_demands n (layerAllowed b)
      (fun j z S ↦ prefixCandidateCoordinateDemands default j
        (prsBadEdgeCount (z.val + 1)) S) hcard hcount hlayerPos
      ⟨default, hdefault⟩ (by
        intro j z S hS
        have hScard := (Finset.mem_powersetCard.mp hS).2
        simpa [hScard] using
          card_prefixCandidateCoordinateDemands_le_choose default j
            (prsBadEdgeCount (z.val + 1)) S) (by
        intro j z S hS d hd
        have hScard := (Finset.mem_powersetCard.mp hS).2
        simpa [hScard] using
          coords_card_of_mem_prefixCandidateCoordinateDemands default j
            (prsBadEdgeCount (z.val + 1)) S hd) (by
        intro j z S _hS d hd c hc
        apply layerAllowed_card_lower_of_mem_prefixCandidateCoordinateDemands
          default j (prsBadEdgeCount (z.val + 1)) S (B := prsLayerSize n j.val)
          (fun k hk ↦ ?_) hd hc
        change prsLayerSize n j.val ≤ prsLayerSize n (k.val + 1)
        apply prsLayerSize_antitone_below hstep
        · omega
        · omega) honeEvent hhalf herror
  let choice := layeredChoiceOfOutcome ω hω
  let M := ∑ j ∈ Finset.Ico 1 (prsLayerCount n), prsLayerSize n j
  have hLaterCard : (Finset.univ \ baseLayer b).card ≤ M := by
    change (Finset.univ \ baseLayer (prsShiftedLayerSizes n)).card ≤ M
    rw [card_prsLaterLayerVertices]
  have hM : M ≤ 2 * prsLayerSize n 1 := by
    exact htail 0
  have hscale : ∀ s : ℕ, 0 < s → s ≤ 2 * M →
      ∃ i : Fin (prsLayerCount n - 1),
        s ≤ 1000 * b (some i) ∧
          500 * (layerStrictTail b i).card < s := by
    intro s hs hsM
    apply exists_layerScale_of_tail b (by omega) s hs
    · change s ≤ 1000 * prsLayerSize n 1
      omega
    · intro i hi
      change (layerStrictTail (prsShiftedLayerSizes n) i).card ≤
        2 * prsLayerSize n (i.val + 2)
      rw [card_prsLayerStrictTail n hcount i]
      exact htail (i.val + 1)
  have hdata : HasLayerLocalizationData (layeredGraph choice) :=
    layeredGraph_hasLayerLocalizationData_of_later_card choice hLaterCard hscale
  have hnotBad : ¬SparseEarlierSetBad b (layeredGraph choice) := by
    rintro ⟨i, hi⟩
    obtain ⟨x, hx, hxcut, hxmem⟩ :=
      mem_prsDemandUnion_of_sparseEarlierSetBadAt ω default hω i hi
    let z : Fin (prsBadCutoff n i) := ⟨x - 1, by
      rw [prsBadCutoff]
      change x - 1 < 1000 * b (some i)
      omega⟩
    have := hAvoid i z
    apply this
    simpa [z, Nat.sub_add_cancel hx] using hxmem
  have hthree : IsRegularSubgraphFree (layeredGraph choice) 3 := by
    intro hcontains
    exact hnotBad
      (sparseEarlierSetBad_of_containsThreeRegular_layered choice hdata hcontains)
  let G := paddedLayeredGraph choice hcard
  refine ⟨G, ?_, ?_⟩
  · calc
      (1 / 60 : ℝ) * (n : ℝ) * logLog n ≤
          (prsLayerSize n 0 * (prsLayerCount n - 1) : ℕ) := hedge
      _ = (G.edgeFinset.card : ℕ) := by
        rw [card_edgeFinset_paddedLayeredGraph]
        rfl
  · intro q hq
    intro hqcontains
    have hunpadded : ContainsRegularSubgraph (layeredGraph choice) q :=
      containsRegularSubgraph_of_contains_paddedLayeredGraph choice hcard
        (by omega) hqcontains
    exact (isRegularSubgraphFree_layered_of_three choice hthree hq) hunpadded

/-- The PRS construction gives the sharp-order lower half of the resolution
of Erdős Problem 182. -/
theorem prs_extremal_lower :
    ∃ c > 0, ∀ k : ℕ, 3 ≤ k →
      ∀ᶠ n : ℕ in atTop,
        c * ((n : ℝ) * logLog2 n) ≤ (regularExtremalNumber n k : ℝ) :=
  prs_extremal_lower_of_allDegreeWitness prs_allDegreeWitness

end

end Erdos182
