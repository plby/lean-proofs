/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RestrictedAbsorberBank
import ErdosProblems.Erdos207.LinearAvailabilitySchedule

/-!
# Initial pair availability outside the realizable absorber

For every pair, every initially illegal third vertex is either an absorber
neighbor of one endpoint or belongs to the finite support of the absorber
bank.  An order-four obstruction cannot occur because the induced forbidden
family retains only partial Steiner systems.
-/

namespace Erdos207

open Finset

noncomputable section

noncomputable def bankSupportThirdVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : TripleSystemOn V) {u v : V} (huv : u ≠ v) :
    Finset (ThirdVertex u v) := by
  classical
  exact univ.filter fun w ↦ w.1 ∈ verticesOn B

@[simp]
lemma mem_bankSupportThirdVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {B : TripleSystemOn V} {u v : V} {huv : u ≠ v}
    {w : ThirdVertex u v} :
    w ∈ bankSupportThirdVertices B huv ↔ w.1 ∈ verticesOn B := by
  classical
  simp [bankSupportThirdVertices]

lemma card_bankSupportThirdVertices_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {B : TripleSystemOn V} {u v : V} (huv : u ≠ v) :
    (bankSupportThirdVertices B huv).card ≤ (verticesOn B).card := by
  let e : ThirdVertex u v ↪ V := Function.Embedding.subtype _
  have hsub : (bankSupportThirdVertices B huv).map e ⊆ verticesOn B := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hx
    exact mem_bankSupportThirdVertices_iff.mp hw
  simpa using card_le_card hsub

/-- A singleton absorber-induced obstruction through any pair has its third
vertex in the bank support.  At order four this follows from packinghood:
an order-four configuration consists of two triples sharing a pair. -/
lemma singleton_absorberForbidden_third_mem_bankSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V}
    {B : TripleSystemOn V}
    {u v : V} (huv : u ≠ v)
    (w : ThirdVertex u v)
    (havoid : TriangleAvoidsGraph H (thirdVertexTriple huv w))
    (hcomplete : CompletesForbidden
      (absorberErdosForbiddenConfigurationsOn q B) ∅
      (thirdVertexTriple huv w)) :
    w.1 ∈ verticesOn B := by
  let T := thirdVertexTriple huv w
  obtain ⟨S, hSF, hTS, hSerase⟩ := hcomplete
  have hS : S = {T} := by
    ext U
    constructor
    · intro hUS
      by_cases hUT : U = T
      · simpa [hUT]
      · have hUerase : U ∈ S.erase T := mem_erase.mpr ⟨hUT, hUS⟩
        have : U ∈ (∅ : TripleSystemOn V) := hSerase hUerase
        simp at this
    · intro hU
      have hUT : U = T := by simpa only [mem_singleton] using hU
      subst U
      exact hTS
  subst S
  obtain ⟨_hne, r, hr4, hrq, E, hE, hEpacking, hEout⟩ :=
    mem_absorberErdosForbiddenConfigurationsOn_iff.mp hSF
  have hTdiff : T ∈ E \ B := by
    simpa only [hEout, mem_singleton]
  have hTE : T ∈ E := (mem_sdiff.mp hTdiff).1
  have hTnotB : T ∉ B := (mem_sdiff.mp hTdiff).2
  by_cases hr5 : 5 ≤ r
  · have hwE : w.1 ∈ verticesOn E :=
      mem_biUnion.mpr ⟨T, hTE, by
        exact third_mem_thirdVertexTriple huv w⟩
    have hthrough := IsErdosConfig.two_le_card_triplesThrough hE hr5 hwE
    have hTthrough : T ∈ triplesThrough E w.1 :=
      mem_filter.mpr ⟨hTE, third_mem_thirdVertexTriple huv w⟩
    obtain ⟨U, hUthrough, hUT⟩ :=
      Finset.exists_mem_ne (s := triplesThrough E w.1) (by omega) T
    have hUE : U ∈ E := (mem_filter.mp hUthrough).1
    have hwU : w.1 ∈ U.1 := (mem_filter.mp hUthrough).2
    have hUB : U ∈ B := by
      by_contra hUnotB
      have hUdiff : U ∈ E \ B := mem_sdiff.mpr ⟨hUE, hUnotB⟩
      have : U = T := by simpa only [hEout, mem_singleton] using hUdiff
      exact hUT this
    exact mem_biUnion.mpr ⟨U, hUB, hwU⟩
  · have hr : r = 4 := by omega
    have hconfig4 : IsConfigOn 4 2 E := by
      simpa [hr] using hE.1
    exact (hEpacking.no_four_config ⟨E, Subset.rfl, hconfig4⟩).elim

/-- Initially, every illegal third vertex is either
an absorber neighbor or lies in the bank support. -/
lemma initial_illegal_third_subset_edge_union_bankSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V}
    {B : TripleSystemOn V}
    {u v : V} (huv : u ≠ v) :
    (univ \ legalThirdVertices
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B) ∅ huv) ⊆
      absorberEdgeBlockedThirdVertices H huv ∪
        bankSupportThirdVertices B huv := by
  intro w hw
  have hnotLegal := (mem_sdiff.mp hw).2
  let T := thirdVertexTriple huv w
  by_cases hTA : T ∈ outsideAvailableTriangles H B
  · have hdata := mem_outsideAvailableTriangles_iff.mp hTA
    by_cases hcomplete : CompletesForbidden
        (absorberErdosForbiddenConfigurationsOn q B) ∅ T
    · apply mem_union.mpr
      right
      apply mem_bankSupportThirdVertices_iff.mpr
      exact singleton_absorberForbidden_third_mem_bankSupport
        huv w hdata.2 hcomplete
    · exfalso
      apply hnotLegal
      apply mem_legalThirdVertices_iff.mpr
      refine ⟨hTA, ?_⟩
      have hpacking : IsPackingOn (∅ : TripleSystemOn V) := by
        intro _ _ _ R hR
        simp at hR
      have havoid : AvoidsForbidden (∅ : TripleSystemOn V)
          (absorberErdosForbiddenConfigurationsOn q B) := by
        intro S hSF hSempty
        obtain ⟨U, hUS⟩ := absorberErdosForbidden_nonempty hSF
        simpa using hSempty hUS
      rw [isLegalExtension_iff hpacking havoid T]
      refine ⟨by simp [T], ?_, hcomplete⟩
      rw [coveredGraph_empty]
      intro a _ha b _hb _hab hadj
      exact hadj.elim
  · by_cases hTB : T ∈ B
    · apply mem_union.mpr
      right
      exact mem_bankSupportThirdVertices_iff.mpr
        (mem_biUnion.mpr ⟨T, hTB, third_mem_thirdVertexTriple huv w⟩)
    · apply mem_union.mpr
      left
      apply mem_absorberEdgeBlockedThirdVertices_iff.mpr
      intro havoids
      apply hTA
      exact mem_outsideAvailableTriangles_iff.mpr ⟨hTB, havoids⟩

/-- Exact initial cardinal accounting with no bank-cardinality loss. -/
theorem card_thirdVertex_le_initialLegal_add_supported_losses
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V}
    (hbank : BankPairsSupported H X B)
    {u v : V} (huv : u ≠ v) (huvH : ¬H.Adj u v) :
    Fintype.card (ThirdVertex u v) ≤
      (legalThirdVertices
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B) ∅ huv).card +
        (H.degree u + H.degree v + (verticesOn B).card) := by
  let L := legalThirdVertices
    (absorberErdosForbiddenConfigurationsOn q B)
    (outsideAvailableTriangles H B) ∅ huv
  let E := absorberEdgeBlockedThirdVertices H huv
  let K := bankSupportThirdVertices B huv
  have hcover : (univ : Finset (ThirdVertex u v)) ⊆ L ∪ (E ∪ K) := by
    intro w _hw
    by_cases hwL : w ∈ L
    · exact mem_union.mpr (Or.inl hwL)
    · apply mem_union.mpr
      right
      exact initial_illegal_third_subset_edge_union_bankSupport
        huv (mem_sdiff.mpr ⟨mem_univ w, hwL⟩)
  have hE := card_absorberEdgeBlockedThirdVertices_le_degree_add
    (H := H) huv huvH
  have hK := card_bankSupportThirdVertices_le (B := B) huv
  calc
    Fintype.card (ThirdVertex u v) =
        (univ : Finset (ThirdVertex u v)).card := by simp
    _ ≤ (L ∪ (E ∪ K)).card := card_le_card hcover
    _ ≤ L.card + (E ∪ K).card := card_union_le _ _
    _ ≤ L.card + (E.card + K.card) :=
      Nat.add_le_add_left (card_union_le E K) L.card
    _ ≤ L.card +
        ((H.degree u + H.degree v) + (verticesOn B).card) :=
      Nat.add_le_add_left (Nat.add_le_add hE hK) L.card
    _ = (legalThirdVertices
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B) ∅ huv).card +
          (H.degree u + H.degree v + (verticesOn B).card) := by
      rfl

/-- Legal third vertices inject into the initial available pair-star. -/
theorem card_initialLegalThirdVertices_le_pairStar
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V)
    {u v : V} (huv : u ≠ v) :
    (legalThirdVertices F A ∅ huv).card ≤
      (availableTrianglesContainingPair
        (absorberGreedyInitialState F A) {u, v}).card := by
  let e : ThirdVertex u v ↪ TripleOn V :=
    ⟨thirdVertexTriple huv, thirdVertexTriple_injective huv⟩
  have hsub : (legalThirdVertices F A ∅ huv).map e ⊆
      availableTrianglesContainingPair
        (absorberGreedyInitialState F A) {u, v} := by
    intro T hT
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hT
    have hw' := mem_legalThirdVertices_iff.mp hw
    apply mem_availableTrianglesContainingPair_iff.mpr
    constructor
    · exact mem_legalAvailable_iff.mpr hw'
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact left_mem_thirdVertexTriple huv w
      · exact right_mem_thirdVertexTriple huv w
  simpa using card_le_card hsub

/-- Initial available codegree outside `X²`, expressed directly in the
greedy state's pair-star language. -/
theorem card_sub_two_le_initialPairStar_add_supported_losses
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V}
    (hbank : BankPairsSupported H X B)
    {u v : V} (huv : u ≠ v) (huvH : ¬H.Adj u v) :
    Fintype.card V - 2 ≤
      (availableTrianglesContainingPair
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)) {u, v}).card +
        (H.degree u + H.degree v + (verticesOn B).card) := by
  rw [← card_thirdVertex huv]
  exact (card_thirdVertex_le_initialLegal_add_supported_losses
      hbank huv huvH).trans
    (Nat.add_le_add_right
      (card_initialLegalThirdVertices_le_pairStar
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B) huv) _)

theorem card_sub_two_le_initialPairStar_add_three_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    {q C : ℕ} {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V}
    (hbank : BankPairsSupported H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hsupport : (verticesOn B).card ≤ C)
    {u v : V} (huv : u ≠ v) (huvH : ¬H.Adj u v) :
    Fintype.card V - 2 ≤
      (availableTrianglesContainingPair
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)) {u, v}).card + 3 * C := by
  have hmain := card_sub_two_le_initialPairStar_add_supported_losses
    (q := q) hbank huv huvH
  have hu := hdegree u
  have hv := hdegree v
  omega

/-- An initially alive pair is outside the absorber graph; hence it satisfies
the uniform supported-loss lower bound. -/
theorem initialPairStar_lower_of_alive
    {V : Type*} [Fintype V] [DecidableEq V]
    {q C : ℕ} (hq : 4 ≤ q)
    {H : SimpleGraph V} [DecidableRel H.Adj]
    {X : Finset V} {B : TripleSystemOn V}
    (hA1 : HasHighGirthAbsorptionBank q H X B)
    (hXcard : 3 ≤ X.card)
    (hbank : BankPairsSupported H X B)
    (hdegree : ∀ x, H.degree x ≤ C)
    (hsupport : (verticesOn B).card ≤ C)
    (P : PairOn V)
    (hP : PairAlive P.1
      (absorberGreedyInitialState
        (absorberErdosForbiddenConfigurationsOn q B)
        (outsideAvailableTriangles H B))) :
    Fintype.card V - 2 ≤
      (availableTrianglesContainingPair
        (absorberGreedyInitialState
          (absorberErdosForbiddenConfigurationsOn q B)
          (outsideAvailableTriangles H B)) P.1).card + 3 * C := by
  obtain ⟨u, v, huv, hPuv⟩ := card_eq_two.mp P.2
  rw [hPuv] at hP ⊢
  have huvH : ¬H.Adj u v := by
    obtain ⟨T, hT⟩ := hP
    have hTdata := mem_availableTrianglesContainingPair_iff.mp hT
    have hTlegal := mem_legalAvailable_iff.mp hTdata.1
    have hTout := mem_outsideAvailableTriangles_iff.mp hTlegal.1
    exact hTout.2 u (hTdata.2 (by simp)) v (hTdata.2 (by simp)) huv
  exact card_sub_two_le_initialPairStar_add_three_mul
    hbank hdegree hsupport huv huvH

/-- Every initial available pair-codegree is at most the ambient order. -/
theorem initial_hasAvailablePairCutoff_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (A : TripleSystemOn V) :
    HasAvailablePairCutoff (Fintype.card V)
      (absorberGreedyInitialState F A) := by
  intro P hPcard
  let P₀ : PairOn V := ⟨P, hPcard⟩
  obtain ⟨u, v, huv, hPuv⟩ := card_eq_two.mp P₀.2
  change P = {u, v} at hPuv
  rw [hPuv]
  have hsub : availableTrianglesContainingPair
      (absorberGreedyInitialState F A) {u, v} ⊆
      universeTriplesThroughPair u v := by
    intro T hT
    have hpair := (mem_availableTrianglesContainingPair_iff.mp hT).2
    exact mem_universeTriplesThroughPair_iff.mpr
      ⟨hpair (by simp), hpair (by simp)⟩
  exact (card_le_card hsub).trans
    (card_universeTriplesThroughPair_le V huv)

end

end Erdos207
