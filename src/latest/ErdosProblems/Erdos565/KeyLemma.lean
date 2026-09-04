/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
import ErdosProblems.Erdos565.Events
import ErdosProblems.Erdos565.Localization
import ErdosProblems.Erdos565.MaximalSeed
import ErdosProblems.Erdos565.RandomGraph
import ErdosProblems.Erdos565.Chernoff
import ErdosProblems.Erdos565.KeyUnion
import ErdosProblems.Erdos565.KeyFiberCounting
import ErdosProblems.Erdos565.KeyStructure
import ErdosProblems.Erdos565.KeyFixedTuple
import ErdosProblems.Erdos565.Extension
import ErdosProblems.Erdos565.DeletedTarget
import ErdosProblems.Erdos565.Numeric

/-!
# The ACDFM key lemma

This file assembles the deterministic localization and maximal-seed steps,
the one-vertex extension estimate, concentration on independent stars, and
the final finite union bound.  All probabilities are represented as
cardinalities in the finite uniform space of labelled simple graphs.
-/

@[expose] public section

open scoped BigOperators SimpleGraph

namespace Erdos565
namespace KeyLemma

/-- The denominator of the Janson density
`p = 1 / (2^25 k^2 r^4)` used by Aragão--Campos--Dahia--Filipe--Marciano. -/
def keyDenominator (r k : ℕ) : ℕ := 2 ^ 25 * k ^ 2 * r ^ 4

/-- The integral saving retained by the finite cardinality version of the
key lemma.  It is the floor of `delta^2 N^2`, where `delta = r^-50`. -/
def keyExponent (r N : ℕ) : ℕ := N ^ 2 / r ^ 100

/-- The exact exceptional set in the ACDFM key lemma on an arbitrary finite
labelled vertex type.  This formulation is needed when the final descent is
applied to an induced subgraph whose vertex type is a subtype. -/
noncomputable def keyBadSetOn {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ}
    (k : ℕ) (targets : Events.TargetVector r order) :
    Finset (SimpleGraph V) := by
  classical
  exact Finset.univ.filter fun G ↦
    Events.BadForTargetsOn 1 (keyDenominator r k) targets G ∧
      Events.StrongInductionEventGlobalOn 1 (keyDenominator r k) 1 (r ^ 50)
        (8 * r) order G

/-- The labelled `Fin N` specialization of `keyBadSetOn`. -/
noncomputable def keyBadSet {r N : ℕ} {order : Fin r → ℕ}
    (k : ℕ) (targets : Events.TargetVector r order) :
    Finset (SimpleGraph (Fin N)) :=
  keyBadSetOn k targets

@[simp] theorem mem_keyBadSetOn {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ}
    {k : ℕ} {targets : Events.TargetVector r order}
    {G : SimpleGraph V} :
    G ∈ keyBadSetOn k targets ↔
      Events.BadForTargetsOn 1 (keyDenominator r k) targets G ∧
        Events.StrongInductionEventGlobalOn 1 (keyDenominator r k) 1 (r ^ 50)
          (8 * r) order G := by
  classical
  simp [keyBadSetOn]

@[simp] theorem mem_keyBadSet {r N : ℕ} {order : Fin r → ℕ}
    {k : ℕ} {targets : Events.TargetVector r order}
    {G : SimpleGraph (Fin N)} :
    G ∈ keyBadSet k targets ↔
      Events.BadForTargets 1 (keyDenominator r k) targets G ∧
        Events.StrongInductionEventGlobal 1 (keyDenominator r k) 1 (r ^ 50) (8 * r)
          order G := by
  classical
  simp [keyBadSet, keyBadSetOn, Events.BadForTargets,
    Events.StrongInductionEventGlobal]

lemma keyDenominator_pos {r k : ℕ} (hr : 0 < r) (hk : 0 < k) :
    0 < keyDenominator r k := by
  simp [keyDenominator, hr, hk]

lemma keyExponent_eq (r N : ℕ) :
    keyExponent r N = N * N / r ^ 100 := by
  simp [keyExponent, pow_two]

/-! ## Converting the Chernoff estimate to an exact cardinal inequality -/

/-- The real-valued graph Chernoff estimate implies the exact
denominator-cleared cardinal estimate used in the key lemma.  The deliberately
coarse hypothesis `64 * q ≤ |S| |U|` absorbs `2^q` into the exponential
tail without requiring an estimate for `log 2`. -/
theorem fewHighGraphs_card_mul_pow_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (U S : Finset V) (hUS : Disjoint U S) (q : ℕ)
    (hS : 2 ≤ S.card) (hU : 22 ≤ U.card)
    (hq : 64 * q ≤ S.card * U.card) :
    (Chernoff.fewHighGraphs U S hUS).card * 2 ^ q ≤
      Fintype.card (SimpleGraph V) := by
  have htail := Chernoff.fewHighGraphs_card_le_exp U S hUS hS hU
  have hqReal : (q : ℝ) ≤ (S.card : ℝ) * U.card / 64 := by
    have hq' : (64 : ℝ) * q ≤ (S.card : ℝ) * U.card := by
      exact_mod_cast hq
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hpow : (2 : ℝ) ^ q ≤
      Real.exp ((S.card : ℝ) * U.card / 64) := by
    calc
      (2 : ℝ) ^ q ≤ Real.exp 1 ^ q :=
        pow_le_pow_left₀ (by positivity) htwo q
      _ = Real.exp (q : ℝ) := by
        rw [← Real.exp_nat_mul]
        simp
      _ ≤ Real.exp ((S.card : ℝ) * U.card / 64) :=
        Real.exp_le_exp.mpr hqReal
  have hfactor :
      Real.exp (-((S.card : ℝ) * U.card) / 64) * (2 : ℝ) ^ q ≤ 1 := by
    calc
      Real.exp (-((S.card : ℝ) * U.card) / 64) * (2 : ℝ) ^ q ≤
          Real.exp (-((S.card : ℝ) * U.card) / 64) *
            Real.exp ((S.card : ℝ) * U.card / 64) := by
        gcongr
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
  have hreal :
      ((Chernoff.fewHighGraphs U S hUS).card : ℝ) * (2 : ℝ) ^ q ≤
        Fintype.card (SimpleGraph V) := by
    calc
      ((Chernoff.fewHighGraphs U S hUS).card : ℝ) * (2 : ℝ) ^ q ≤
          ((Fintype.card (SimpleGraph V) : ℝ) *
            Real.exp (-((S.card : ℝ) * U.card) / 64)) * (2 : ℝ) ^ q := by
        gcongr
      _ = (Fintype.card (SimpleGraph V) : ℝ) *
          (Real.exp (-((S.card : ℝ) * U.card) / 64) * (2 : ℝ) ^ q) := by
        ring
      _ ≤ (Fintype.card (SimpleGraph V) : ℝ) * 1 := by
        gcongr
      _ = Fintype.card (SimpleGraph V) := by ring
  exact_mod_cast hreal

/-! ## The dependent structural union bound -/

/-- The `KeyUnion` bookkeeping, specialized to the genuinely dependent
structural tuple whose color graphs live on the chosen seed subtype. -/
theorem dependent_key_union_bound
    {V Omega : Type*} [Fintype V] [DecidableEq V] [Fintype Omega]
    (r N D : ℕ) (Small : Finset V → Prop)
    (bad : KeyStructure.RestrictedStructure V r N Small → Omega → Prop)
    (K : ℕ) (hV : Fintype.card V = N)
    (hr : 1 ≤ r) (hND : N ≤ r * D)
    (hR : (N + 1) ^ r ≤ 2 ^ N)
    (hSmall : ∀ U : Finset V, Small U →
      r * U.card.choose 2 ≤ 4 * r * D)
    (hbad : ∀ s, (KeyUnion.badSet bad s).card ≤ K)
    (hfixed : K * 2 ^ (8 * r * D) ≤ Fintype.card Omega) :
    (KeyUnion.badUnion bad).card * 2 ^ D ≤ Fintype.card Omega := by
  have hstructures :
      Fintype.card (KeyStructure.RestrictedStructure V r N Small) ≤
        2 ^ (3 * N + 4 * r * D) :=
    KeyStructure.card_restrictedStructure_le_two_pow V r N D Small hV hR hSmall
  have hunion : (KeyUnion.badUnion bad).card ≤
      2 ^ (3 * N + 4 * r * D) * K :=
    (KeyUnion.card_badUnion_le bad K hbad).trans
      (Nat.mul_le_mul_right K hstructures)
  calc
    (KeyUnion.badUnion bad).card * 2 ^ D ≤
        (2 ^ (3 * N + 4 * r * D) * K) * 2 ^ D :=
      Nat.mul_le_mul_right (2 ^ D) hunion
    _ = K * 2 ^ (3 * N + 4 * r * D + D) := by
      rw [pow_add]
      ring
    _ ≤ K * 2 ^ (8 * r * D) := by
      exact Nat.mul_le_mul_left K
        (Nat.pow_le_pow_right (by decide : 0 < 2)
          (KeyUnion.structural_exponent_add_target_le hr hND))
    _ ≤ Fintype.card Omega := hfixed

/-! ## Pigeonholing a dense star into one color -/

/-- If the total degree of a star is more than one quarter of `u`, one of
`r` color-degrees is more than `u/(4r)`.  This denominator-cleared version
is exactly what the extension lemma consumes. -/
theorem exists_color_with_large_degree {r u : ℕ} (hr : 0 < r)
    (degree : Fin r → ℕ) (htotal : u < 4 * ∑ i, degree i) :
    ∃ i, u < 4 * r * degree i := by
  by_contra hnot
  push Not at hnot
  have hsum : 4 * r * (∑ i, degree i) ≤ r * u := by
    calc
      4 * r * (∑ i, degree i) = ∑ i, 4 * r * degree i := by
        simp [Finset.mul_sum]
      _ ≤ ∑ _i : Fin r, u := Finset.sum_le_sum fun i _ ↦ hnot i
      _ = r * u := by simp
  have hcancel : 4 * (∑ i, degree i) ≤ u := by
    have : r * (4 * ∑ i, degree i) ≤ r * u := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hsum
    exact Nat.le_of_mul_le_mul_left this hr
  omega

/-! ## One-vertex restrictions in ambient edge coordinates -/

section RootedRestriction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Identify `Option U` with the old vertices `U` and one new ambient
vertex `v`. -/
def rootedEmbeddingOn (v : V) (U : Finset V) (hv : v ∉ U) : Option ↑U ↪ V where
  toFun
    | none => v
    | some u => u.1
  inj' := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some y =>
            exfalso
            apply hv
            change v = y.1 at hxy
            rw [hxy]
            exact y.2
    | some x =>
        cases y with
        | none =>
            exfalso
            apply hv
            change x.1 = v at hxy
            rw [← hxy]
            exact x.2
        | some y => exact congrArg some (Subtype.ext hxy)

/-- Pull an ambient graph back to `U` together with the new root `v`. -/
def rootedRestrictionOn (G : SimpleGraph V) (v : V) (U : Finset V)
    (hv : v ∉ U) : SimpleGraph (Option ↑U) :=
  G.comap (rootedEmbeddingOn v U hv)

/-- The tautological induced embedding of a rooted restriction back into its
ambient graph. -/
def rootedGraphEmbeddingOn (G : SimpleGraph V) (v : V) (U : Finset V)
    (hv : v ∉ U) : rootedRestrictionOn G v U hv ↪g G where
  __ := rootedEmbeddingOn v U hv
  map_rel_iff' := Iff.rfl

@[simp] theorem range_rootedGraphEmbeddingOn
    (G : SimpleGraph V) (v : V) (U : Finset V) (hv : v ∉ U) :
    Finset.univ.map (rootedGraphEmbeddingOn G v U hv).toEmbedding = insert v U := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨a, rfl⟩
    cases a with
    | none => exact Or.inl rfl
    | some a => exact Or.inr a.2
  · rintro (rfl | hx)
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨x, hx⟩, rfl⟩

@[simp] theorem rootedRestrictionOn_adj_star
    (G : SimpleGraph V) (v : V) (U : Finset V) (hv : v ∉ U) (u : ↑U) :
    (rootedRestrictionOn G v U hv).Adj none (some u) ↔ G.Adj v u.1 := Iff.rfl

@[simp] theorem rootedRestrictionOn_adj_star_symm
    (G : SimpleGraph V) (v : V) (U : Finset V) (hv : v ∉ U) (u : ↑U) :
    (rootedRestrictionOn G v U hv).Adj (some u) none ↔ G.Adj u.1 v := Iff.rfl

@[simp] theorem oldPart_rootedRestrictionOn
    (G : SimpleGraph V) (v : V) (U : Finset V) (hv : v ∉ U) :
    Erdos565.oldPart (rootedRestrictionOn G v U hv) =
      G.induce (↑U : Set V) := by
  rfl

theorem rootedRestrictionOn_mono {G' G : SimpleGraph V} (h : G' ≤ G)
    (v : V) (U : Finset V) (hv : v ∉ U) :
    rootedRestrictionOn G' v U hv ≤ rootedRestrictionOn G v U hv := by
  intro x y hxy
  exact h hxy

@[simp] theorem labelGraph_pullback_rootedGraphEmbeddingOn
    {C : Type*} {G : SimpleGraph V} (coloring : G.EdgeLabeling C) (i : C)
    (v : V) (U : Finset V) (hv : v ∉ U) :
    (coloring.pullback (rootedGraphEmbeddingOn G v U hv).toHom).labelGraph i =
      rootedRestrictionOn (coloring.labelGraph i) v U hv := by
  ext x y
  change ((coloring.pullback (rootedGraphEmbeddingOn G v U hv).toHom).labelGraph i).Adj
      x y ↔ (coloring.labelGraph i).Adj
        (rootedEmbeddingOn v U hv x) (rootedEmbeddingOn v U hv y)
  rw [SimpleGraph.EdgeLabeling.labelGraph_adj,
    SimpleGraph.EdgeLabeling.labelGraph_adj]
  rfl

/-- The star of an ambient graph, seen as a subset of `U`, lifts to exactly
the restriction of its unordered-edge coordinate set to the star block. -/
theorem liftStar_graphStar_rootedRestrictionOn
    (G : SimpleGraph V) (v : V) (U : Finset V) (hv : v ∉ U) :
    KeyFixedTuple.liftStar v U hv
        (Extension.graphStar (rootedRestrictionOn G v U hv)) =
      RandomGraph.restrict (RandomGraph.starEdges v U hv)
        (RandomGraph.edgesOfGraph G) := by
  ext e
  constructor
  · intro he
    rw [KeyFixedTuple.liftStar, Finset.mem_map] at he
    obtain ⟨u, hu, rfl⟩ := he
    rw [RandomGraph.restrict, Finset.mem_inter]
    refine ⟨?_, ?_⟩
    · rw [RandomGraph.mem_edgesOfGraph]
      change s(v, u.1) ∈ G.edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact (Extension.mem_graphStar.mp hu).symm
    · rw [RandomGraph.mem_starEdges_iff]
      exact ⟨u.1, u.2, rfl⟩
  · intro he
    rw [RandomGraph.restrict, Finset.mem_inter] at he
    obtain ⟨heG, heStar⟩ := he
    obtain ⟨u, huU, heu⟩ := RandomGraph.mem_starEdges_iff.mp heStar
    let uU : ↑U := ⟨u, huU⟩
    have huG : (rootedRestrictionOn G v U hv).Adj (some uU) none := by
      rw [rootedRestrictionOn_adj_star_symm]
      have heG' : s(v, u) ∈ G.edgeSet := by
        simpa [heu] using (RandomGraph.mem_edgesOfGraph.mp heG)
      exact (G.mem_edgeSet.mp heG').symm
    rw [KeyFixedTuple.liftStar, Finset.mem_map]
    refine ⟨uU, Extension.mem_graphStar.mpr huG, ?_⟩
    apply Subtype.ext
    exact heu.symm

end RootedRestriction

/-! ## Relabelling copy hypergraphs onto finite induced vertex types -/

section InducedRelabelling

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem labelGraph_pullback_induce_eq_induce
    {C : Type*} {G : SimpleGraph V} (coloring : G.EdgeLabeling C) (i : C)
    (W : Finset V) :
    (coloring.pullback
      (SimpleGraph.Embedding.induce (G := G) (↑W : Set V)).toHom).labelGraph i =
      (coloring.labelGraph i).induce (↑W : Set V) := by
  ext x y
  change ((coloring.pullback
    (SimpleGraph.Embedding.induce (G := G) (↑W : Set V)).toHom).labelGraph i).Adj
      x y ↔ (coloring.labelGraph i).Adj x.1 y.1
  rw [SimpleGraph.EdgeLabeling.labelGraph_adj,
    SimpleGraph.EdgeLabeling.labelGraph_adj]
  rfl

/-- Jansonness of a globally restricted copy family is equivalent in the
direction needed here to Jansonness on the induced subtype. -/
theorem localCopy_isJanson_of_global_restrict
    {A C : Type*} [Fintype A] {G : SimpleGraph V}
    (target : SimpleGraph A) (coloring : G.EdgeLabeling C) (i : C)
    (W : Finset V) {p R : ℝ} (hp : 0 < p)
    (h : ((copyHypergraph target (coloring.labelGraph i) G).restrict W).IsJanson p R) :
    (copyHypergraph target ((coloring.labelGraph i).induce (↑W : Set V))
      (G.induce (↑W : Set V))).IsJanson p R := by
  classical
  let H := copyHypergraph target ((coloring.labelGraph i).induce (↑W : Set V))
    (G.induce (↑W : Set V))
  let f : (↑W : Set V) → V := fun x ↦ x.1
  have hmap : H.map f =
      (copyHypergraph target (coloring.labelGraph i) G).restrict W := by
    have h0 := map_copyHypergraph_pullback_induce_eq_restrict target G coloring i W
    rw [labelGraph_pullback_induce_eq_induce coloring i W] at h0
    simpa [H, f] using h0
  have hinj : Hypergraph.EdgewiseInjective H f := by
    intro E _hE x _hx y _hy hxy
    exact Subtype.ext hxy
  have hmapped : (H.map f).IsJanson p R := by
    rwa [hmap]
  exact Hypergraph.IsJanson.pullback hinj hp hmapped

/-- The copy family depends only on the isomorphism class of its target. -/
theorem copyHypergraph_eq_of_iso
    {A B : Type*} {F : SimpleGraph A} {F' : SimpleGraph B}
    (e : F ≃g F') (G' G : SimpleGraph V) :
    copyHypergraph F G' G = copyHypergraph F' G' G := by
  classical
  ext L
  rw [mem_copyHypergraph, mem_copyHypergraph]
  constructor
  · rintro ⟨⟨h⟩, hGG⟩
    exact ⟨⟨e.symm.trans h⟩, hGG⟩
  · rintro ⟨⟨h⟩, hGG⟩
    exact ⟨⟨e.trans h⟩, hGG⟩

theorem map_restrict_eq_restrict_map_of_injective
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (H : Hypergraph X) (W : Finset X) (f : X → Y)
    (hf : Function.Injective f) :
    (H.restrict W).map f = (H.map f).restrict (W.image f) := by
  classical
  ext E
  constructor
  · intro hE
    obtain ⟨D, hD, rfl⟩ := Hypergraph.mem_map.mp hE
    refine Hypergraph.mem_restrict.mpr
      ⟨Hypergraph.mem_map.mpr ⟨D, (Hypergraph.mem_restrict.mp hD).1, rfl⟩, ?_⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr
      ⟨x, (Hypergraph.mem_restrict.mp hD).2 hx, rfl⟩
  · intro hE
    obtain ⟨hEmap, hEW⟩ := Hypergraph.mem_restrict.mp hE
    obtain ⟨D, hDH, rfl⟩ := Hypergraph.mem_map.mp hEmap
    apply Hypergraph.mem_map.mpr
    refine ⟨D, Hypergraph.mem_restrict.mpr ⟨hDH, ?_⟩, rfl⟩
    intro x hx
    have hfx : f x ∈ W.image f := hEW (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hfx
    simpa [hf hyx] using hy

end InducedRelabelling

/-! ## Exact product count for transported one-vertex bad events -/

section StarProduct

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Inject a graph event into its unordered-edge-coordinate event. -/
theorem card_graphEvent_le_eventSamples
    (Q : SimpleGraph V → Prop) (P : Finset (RandomGraph.Edge V) → Prop)
    [DecidablePred Q] [DecidablePred P]
    (hQP : ∀ G, Q G → P (RandomGraph.edgesOfGraph G)) :
    ((Finset.univ : Finset (SimpleGraph V)).filter Q).card ≤
      (RandomGraph.eventSamples (RandomGraph.edgeUniverse V) P).card := by
  classical
  let badGraphs := (Finset.univ : Finset (SimpleGraph V)).filter Q
  have hinj : Function.Injective (RandomGraph.edgesOfGraph (V := V)) :=
    RandomGraph.edgeSetEquivGraph.symm.injective
  rw [← Finset.card_image_iff.mpr (fun G _ H _ h ↦ hinj h)]
  apply Finset.card_le_card
  intro S hS
  obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hS
  have hQ : Q G := (Finset.mem_filter.mp hG).2
  simp only [RandomGraph.eventSamples, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.subset_univ _, hQP G hQ⟩

/-- Multiplying the exact one-star extension estimates over a disjoint family
of roots gives the corresponding denominator-cleared graph-event estimate. -/
theorem card_uniform_bad_star_family_mul_pow_le
    (A U : Finset V) (hAU : Disjoint A U) (t : ℕ)
    (bad : A → Finset (Finset ↑U))
    (hbad : ∀ a, (bad a).card * 2 ^ t ≤ 2 ^ U.card) :
    (RandomGraph.eventSamples (RandomGraph.edgeUniverse V)
      (RandomGraph.supportedEvents Finset.univ
        (RandomGraph.indexedStarEdges A U hAU)
        (fun a S ↦ S ∈ KeyFixedTuple.liftedBadStars a.1 U
          (fun ha ↦ Finset.disjoint_left.mp hAU a.2 ha) (bad a)))).card *
        2 ^ (A.card * t) ≤ Fintype.card (SimpleGraph V) := by
  classical
  let P : A → Finset (RandomGraph.Edge V) → Prop := fun a S ↦
    S ∈ KeyFixedTuple.liftedBadStars a.1 U
      (fun ha ↦ Finset.disjoint_left.mp hAU a.2 ha) (bad a)
  have hformula := RandomGraph.card_uniform_star_family_event A U hAU P
  have hlocal : ∀ a : A,
      (RandomGraph.eventSamples (RandomGraph.indexedStarEdges A U hAU a)
        (P a)).card = (bad a).card := by
    intro a
    have heq : RandomGraph.eventSamples (RandomGraph.indexedStarEdges A U hAU a)
        (P a) = KeyFixedTuple.liftedBadStars a.1 U
          (fun ha ↦ Finset.disjoint_left.mp hAU a.2 ha) (bad a) := by
      ext S
      simp only [RandomGraph.eventSamples, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · exact fun h ↦ h.2
      · intro hS
        refine ⟨?_, hS⟩
        exact Finset.mem_powerset.mp (by
          simpa [RandomGraph.indexedStarEdges] using
            (KeyFixedTuple.liftedBadStars_subset_powerset _ _ _ (bad a) hS))
    rw [heq, KeyFixedTuple.card_liftedBadStars]
  have hprod : (∏ a : A, (bad a).card) * 2 ^ (A.card * t) ≤
      2 ^ (A.card * U.card) := by
    rw [show 2 ^ (A.card * t) = ∏ _a : A, 2 ^ t by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
      rw [← pow_mul, Nat.mul_comm]]
    rw [← Finset.prod_mul_distrib]
    calc
      ∏ a : A, ((bad a).card * 2 ^ t) ≤ ∏ _a : A, 2 ^ U.card := by
        exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
          (fun a _ ↦ hbad a)
      _ = 2 ^ (A.card * U.card) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
        rw [← pow_mul, Nat.mul_comm]
  have hcross : A.card * U.card ≤ (Fintype.card V).choose 2 := by
    rw [← RandomGraph.card_crossStarEdges A U hAU,
      ← RandomGraph.card_edgeUniverse (V := V)]
    exact Finset.card_le_card
      (RandomGraph.crossStarEdges_subset_edgeUniverse A U hAU)
  rw [hformula]
  simp_rw [hlocal]
  calc
    (2 ^ ((Fintype.card V).choose 2 - A.card * U.card) *
        ∏ a : A, (bad a).card) * 2 ^ (A.card * t) =
        2 ^ ((Fintype.card V).choose 2 - A.card * U.card) *
          ((∏ a : A, (bad a).card) * 2 ^ (A.card * t)) := by ring
    _ ≤ 2 ^ ((Fintype.card V).choose 2 - A.card * U.card) *
          2 ^ (A.card * U.card) := Nat.mul_le_mul_left _ hprod
    _ = 2 ^ (Fintype.card V).choose 2 := by
      rw [← pow_add, Nat.sub_add_cancel hcross]
    _ = Fintype.card (SimpleGraph V) :=
      (RandomGraph.card_simpleGraph (V := V)).symm

end StarProduct

/-- The sample space has exactly `2^(N choose 2)` labelled graphs. -/
theorem card_graph_sample_space (N : ℕ) :
    Fintype.card (SimpleGraph (Fin N)) = 2 ^ N.choose 2 := by
  simpa using (RandomGraph.card_simpleGraph (V := Fin N))

/-- Membership in the key exceptional set implies both constituent events. -/
theorem badForTargets_of_mem_keyBadSet {r N : ℕ} {order : Fin r → ℕ}
    {k : ℕ} {targets : Events.TargetVector r order}
    {G : SimpleGraph (Fin N)} (hG : G ∈ keyBadSet k targets) :
    Events.BadForTargets 1 (keyDenominator r k) targets G :=
  (mem_keyBadSet.mp hG).1

/-- Membership in the key exceptional set implies the strong induction
event with the exact ACDFM parameters. -/
theorem strongInductionEvent_of_mem_keyBadSet
    {r N : ℕ} {order : Fin r → ℕ}
    {k : ℕ} {targets : Events.TargetVector r order}
    {G : SimpleGraph (Fin N)} (hG : G ∈ keyBadSet k targets) :
    Events.StrongInductionEventGlobal 1 (keyDenominator r k) 1 (r ^ 50) (8 * r)
      order G :=
  (mem_keyBadSet.mp hG).2

/-- The key exceptional set is empty as soon as one target has at most one
vertex.  This closes the degenerate branch before localization. -/
theorem keyBadSetOn_eq_empty_of_order_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ} {k : ℕ}
    {targets : Events.TargetVector r order} (i : Fin r) (hi : order i ≤ 1) :
    keyBadSetOn (V := V) k targets = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro G hG
  exact Events.not_badForTargetsOn_of_target_order_le_one i hi
    (mem_keyBadSetOn.mp hG).1

theorem keyBadSetOn_card_mul_pow_le_of_order_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} {order : Fin r → ℕ} {k D : ℕ}
    {targets : Events.TargetVector r order} (i : Fin r) (hi : order i ≤ 1) :
    (keyBadSetOn (V := V) k targets).card * 2 ^ D ≤
      Fintype.card (SimpleGraph V) := by
  rw [keyBadSetOn_eq_empty_of_order_le_one i hi]
  simp

/-! ## The maximal seed, instantiated with copy hypergraphs -/

section Seed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The predicate supplied to the finite maximal-seed selector. -/
def CopyGood {r : ℕ} (copies : Fin r → Hypergraph V) (p : ℝ)
    (i : Fin r) (U : Finset V) (R : ℕ) : Prop :=
  ((copies i).restrict U).IsJanson p R

theorem copyGood_zero {r : ℕ} (copies : Fin r → Hypergraph V) (p : ℝ)
    (i : Fin r) (U : Finset V) : CopyGood copies p i U 0 := by
  simpa [CopyGood] using Hypergraph.IsJanson.radius_zero ((copies i).restrict U) p

theorem copyGood_mono {r : ℕ} (copies : Fin r → Hypergraph V) (p : ℝ)
    (i : Fin r) {U T : Finset V} {R : ℕ} (hUT : U ⊆ T)
    (h : CopyGood copies p i U R) : CopyGood copies p i T R := by
  exact Hypergraph.IsJanson.mono_edges
    (Hypergraph.restrict_mono_right (copies i) hUT) h

/-- An abstract localized non-Janson bound turns the finite maximizer into
the precise seed package used later.  Unlike `MaximalSeed.exists_result`,
the predicate here is already the actual copy-hypergraph Janson predicate;
only the numerical comparison between the localized radius and a candidate
radius is left to the caller. -/
theorem exists_copySeed {r N : ℕ} (copies : Fin r → Hypergraph V)
    (p localRadius : ℝ) (S : Finset V)
    (hp : 0 < p) (hlocalRadius : 0 ≤ localRadius)
    (hseed : seedThreshold r N ≤ S.card)
    (hlocal : ∀ i, ¬ ((copies i).restrict S).IsJanson p localRadius) :
    ∃ result : MaximalSeed.Result r N S (CopyGood copies p),
      ∀ i, (result.R i : ℝ) ≤ localRadius := by
  classical
  obtain ⟨result⟩ := MaximalSeed.exists_result r N S (CopyGood copies p)
    hseed
    (fun U _hUS _hcard i ↦ copyGood_zero copies p i U)
    (fun i U T R hUT hgood ↦ copyGood_mono copies p i hUT hgood)
  refine ⟨result, ?_⟩
  intro i
  by_contra hnot
  have hlt : localRadius < (result.R i : ℝ) := lt_of_not_ge hnot
  have hjU : ((copies i).restrict result.U).IsJanson p (result.R i : ℝ) :=
    result.candidate.2.2 i
  have hjS : ((copies i).restrict S).IsJanson p (result.R i : ℝ) :=
    Hypergraph.IsJanson.mono_edges
      (Hypergraph.restrict_mono_right (copies i) result.candidate.1) hjU
  exact hlocal i (Hypergraph.IsJanson.mono_params hjS hp (le_refl p)
    hlocalRadius hlt.le)

/-- Every maximal seed produced above is still non-Janson after adjoining
one outside vertex and increasing one radius by one. -/
theorem copySeed_extensionFailure {r N : ℕ}
    {copies : Fin r → Hypergraph V} {p : ℝ} {S : Finset V}
    (result : MaximalSeed.Result r N S (CopyGood copies p)) :
    ∀ v ∈ S \ result.U, ∀ i,
      ¬ ((copies i).restrict (insert v result.U)).IsJanson p (result.R i + 1) := by
  simpa [CopyGood, Nat.cast_add, Nat.cast_one] using result.extensionFailure

/-- Relabel the maximality failure on `insert v U` to the canonical
`Option U` one-vertex model used by the extension lemma. -/
theorem copySeed_extensionFailure_rooted
    {r N : ℕ} {order : Fin r → ℕ}
    {targets : Events.TargetVector r order} {G : SimpleGraph V}
    {coloring : G.EdgeLabeling (Fin r)} {p : ℝ} {S : Finset V}
    (result : MaximalSeed.Result r N S
      (CopyGood (fun i ↦ copyHypergraph (targets i)
        (Events.colorClassGraph coloring i) G) p))
    (hp : 0 < p) (v : V) (hv : v ∈ S \ result.U) (i : Fin r) :
    ¬ (copyHypergraph (targets i)
      (rootedRestrictionOn (Events.colorClassGraph coloring i) v result.U
        (Finset.mem_sdiff.mp hv).2)
      (rootedRestrictionOn G v result.U (Finset.mem_sdiff.mp hv).2)).IsJanson
        p (result.R i + 1) := by
  classical
  intro hrooted
  let hvU : v ∉ result.U := (Finset.mem_sdiff.mp hv).2
  let K := rootedRestrictionOn G v result.U hvU
  let e : K ↪g G := rootedGraphEmbeddingOn G v result.U hvU
  let H := copyHypergraph (targets i)
    (rootedRestrictionOn (Events.colorClassGraph coloring i) v result.U hvU) K
  have hmap : H.map (fun x ↦ e x) =
      (copyHypergraph (targets i) (Events.colorClassGraph coloring i) G).restrict
        (insert v result.U) := by
    have hmap0 := map_copyHypergraph_pullback_embedding_eq_restrict
      (targets i) K G coloring i e (insert v result.U)
        (range_rootedGraphEmbeddingOn G v result.U hvU)
    have hcolor : (coloring.pullback e.toHom).labelGraph i =
        rootedRestrictionOn (Events.colorClassGraph coloring i) v result.U hvU := by
      simpa [e, K, Events.colorClassGraph] using
        (labelGraph_pullback_rootedGraphEmbeddingOn coloring i v result.U hvU)
    rw [hcolor] at hmap0
    simpa [H, K] using hmap0
  have hmapJanson : (H.map (fun x ↦ e x)).IsJanson p (result.R i + 1) :=
    Extension.isJanson_map_of_injective H (fun x ↦ e x) e.injective hp (by
      simpa [H, K, hvU] using hrooted)
  apply copySeed_extensionFailure result v hv i
  rwa [← hmap]

/-- The localized radius is at most the source seed-radius bound on every
set at least as large as the rounded seed threshold. -/
theorem localJansonRadius_le_seedRatio {r k N u : ℕ}
    (hr : 2 ≤ r) (hk : 0 < k) (hu : seedThreshold r N ≤ u) :
    Localization.localJansonRadius r 1 (keyDenominator r k) N ≤
      Events.rationalParameter 1 (keyDenominator r k) * u / (512 * r) := by
  have hpden : 0 < keyDenominator r k := keyDenominator_pos (by omega) hk
  have hp : 0 < Events.rationalParameter 1 (keyDenominator r k) :=
    Events.rationalParameter_pos (by omega) hpden
  have hseed : N ≤ r ^ 50 * u :=
    (seedThreshold_lower hr).trans (Nat.mul_le_mul_left (r ^ 50) hu)
  have hseedReal : (N : ℝ) ≤ (r : ℝ) ^ 50 * u := by
    exact_mod_cast hseed
  rw [Localization.localJansonRadius, Events.jansonRadius]
  have hrReal : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hleftDen : 0 < (512 : ℝ) * (r : ℝ) ^ 51 := by positivity
  have hrightDen : 0 < (512 : ℝ) * r := by positivity
  rw [div_le_div_iff₀ hleftDen hrightDen]
  calc
    Events.rationalParameter 1 (keyDenominator r k) * N * (512 * r) ≤
        Events.rationalParameter 1 (keyDenominator r k) *
          ((r : ℝ) ^ 50 * u) * (512 * r) := by gcongr
    _ = (Events.rationalParameter 1 (keyDenominator r k) * u) *
          (512 * (r : ℝ) ^ 51) := by ring

/-- The complete localization-plus-maximal-seed step on `Fin N`.  There is
no abstract Janson hypothesis: the localized failures are obtained from the
actual bad-coloring event, and maximality itself forces every radius below
the localized threshold. -/
theorem exists_maximalCopySeed_of_bad
    {r k N : ℕ} {order : Fin r → ℕ}
    (targets : Events.TargetVector r order) (G : SimpleGraph (Fin N))
    (hr : 2 ≤ r) (hk : 0 < k)
    (hscale34 : 2 * r ^ 34 ≤ N) (hscale50 : 2 * r ^ 50 ≤ N)
    (hbad : Events.BadForTargets 1 (keyDenominator r k) targets G) :
    ∃ (coloring : G.EdgeLabeling (Fin r)) (S : Finset (Fin N))
        (result : MaximalSeed.Result r N S
          (CopyGood (fun i ↦ copyHypergraph (targets i)
            (Events.colorClassGraph coloring i) G)
            (Events.rationalParameter 1 (keyDenominator r k)))),
      sampleThreshold r N ≤ S.card ∧
      (∀ i, ¬ ((copyHypergraph (targets i)
        (Events.colorClassGraph coloring i) G).restrict S).IsJanson
          (Events.rationalParameter 1 (keyDenominator r k))
          (Localization.localJansonRadius r 1 (keyDenominator r k) N)) ∧
      (∀ i, (result.R i : ℝ) ≤
        Events.rationalParameter 1 (keyDenominator r k) * result.U.card /
          (512 * r)) ∧
      512 * (∑ i, result.R i) ≤ result.U.card ∧
      N ≤ r ^ 50 * result.U.card ∧
      511 * r ^ 50 * result.U.card ≤ 768 * N ∧
      r ^ 50 * result.U.card < 2 * N ∧
      4 * result.U.card ≤ S.card := by
  classical
  have hpDen : 0 < keyDenominator r k := keyDenominator_pos (by omega) hk
  obtain ⟨coloring, S, hsample, hlocal⟩ :=
    Localization.badForTargets_exists_localized_failure targets G hr
      (by omega) hpDen hscale34 hbad
  let copies : Fin r → Hypergraph (Fin N) := fun i ↦
    copyHypergraph (targets i) (Events.colorClassGraph coloring i) G
  let p : ℝ := Events.rationalParameter 1 (keyDenominator r k)
  let localRadius : ℝ := Localization.localJansonRadius r 1 (keyDenominator r k) N
  have hp : 0 < p := Events.rationalParameter_pos (by omega) hpDen
  have hlocal' : ∀ i, ¬ ((copies i).restrict S).IsJanson p localRadius := by
    simpa [copies, p, localRadius] using hlocal
  have hrpowPos : 0 < r ^ 34 := Nat.pow_pos (by omega)
  have hNpos : 0 < N := by omega
  have hlocalRadius : 0 ≤ localRadius :=
    (Localization.localJansonRadius_pos hr (by omega) hpDen hNpos).le
  obtain ⟨result, hresultRadius⟩ := exists_copySeed copies p localRadius S
    hp hlocalRadius ((seedThreshold_le_sampleThreshold hr).trans hsample) hlocal'
  have hratio : ∀ i, (result.R i : ℝ) ≤ p * result.U.card / (512 * r) := by
    intro i
    exact (hresultRadius i).trans (by
      simpa [p, localRadius] using
        (localJansonRadius_le_seedRatio (r := r) (k := k) (N := N)
          (u := result.U.card) hr hk
          (by
            rw [result.candidate.2.1]
            exact Nat.le_add_right _ _)))
  have hpOne : p ≤ 1 := by
    dsimp [p, Events.rationalParameter]
    rw [div_le_one (by exact_mod_cast hpDen)]
    exact_mod_cast (show 1 ≤ keyDenominator r k by omega)
  have haggregate : 512 * (∑ i, result.R i) ≤ result.U.card :=
    MaximalSeed.aggregate_radius_bound result.R (by omega) hpOne hratio
  have hbounds := MaximalSeed.result_card_bounds result hr hscale50 haggregate hsample
  refine ⟨coloring, S, result, hsample, hlocal, hratio, haggregate,
    hbounds.1, hbounds.2.1, hbounds.2.2.1, hbounds.2.2.2.2⟩

/-- Arbitrary-finite-vertex version of `exists_maximalCopySeed_of_bad`.
This is the form consumed after passing to an induced vertex subtype in the
minimal-state descent. -/
theorem exists_maximalCopySeedOn_of_bad
    {V : Type*} [Fintype V] [DecidableEq V]
    {r k : ℕ} {order : Fin r → ℕ}
    (targets : Events.TargetVector r order) (G : SimpleGraph V)
    (hr : 2 ≤ r) (hk : 0 < k)
    (hscale34 : 2 * r ^ 34 ≤ Fintype.card V)
    (hscale50 : 2 * r ^ 50 ≤ Fintype.card V)
    (hbad : Events.BadForTargetsOn 1 (keyDenominator r k) targets G) :
    ∃ (coloring : G.EdgeLabeling (Fin r)) (S : Finset V)
        (result : MaximalSeed.Result r (Fintype.card V) S
          (CopyGood (fun i ↦ copyHypergraph (targets i)
            (Events.colorClassGraph coloring i) G)
            (Events.rationalParameter 1 (keyDenominator r k)))),
      sampleThreshold r (Fintype.card V) ≤ S.card ∧
      (∀ i, ¬ ((copyHypergraph (targets i)
        (Events.colorClassGraph coloring i) G).restrict S).IsJanson
          (Events.rationalParameter 1 (keyDenominator r k))
          (Localization.localJansonRadius r 1 (keyDenominator r k)
            (Fintype.card V))) ∧
      (∀ i, (result.R i : ℝ) ≤
        Events.rationalParameter 1 (keyDenominator r k) * result.U.card /
          (512 * r)) ∧
      512 * (∑ i, result.R i) ≤ result.U.card ∧
      Fintype.card V ≤ r ^ 50 * result.U.card ∧
      511 * r ^ 50 * result.U.card ≤ 768 * Fintype.card V ∧
      r ^ 50 * result.U.card < 2 * Fintype.card V ∧
      4 * result.U.card ≤ S.card := by
  classical
  let N := Fintype.card V
  have hpDen : 0 < keyDenominator r k := keyDenominator_pos (by omega) hk
  obtain ⟨coloring, S, hsample, hlocal⟩ :=
    Localization.badForTargetsOn_exists_localized_failure targets G hr
      (by omega) hpDen hscale34 hbad
  let copies : Fin r → Hypergraph V := fun i ↦
    copyHypergraph (targets i) (Events.colorClassGraph coloring i) G
  let p : ℝ := Events.rationalParameter 1 (keyDenominator r k)
  let localRadius : ℝ := Localization.localJansonRadius r 1 (keyDenominator r k) N
  have hp : 0 < p := Events.rationalParameter_pos (by omega) hpDen
  have hlocal' : ∀ i, ¬ ((copies i).restrict S).IsJanson p localRadius := by
    simpa [copies, p, localRadius, N] using hlocal
  have hrpowPos : 0 < r ^ 34 := Nat.pow_pos (by omega)
  have hNpos : 0 < N := by
    dsimp [N]
    omega
  have hlocalRadius : 0 ≤ localRadius :=
    (Localization.localJansonRadius_pos hr (by omega) hpDen hNpos).le
  obtain ⟨result, hresultRadius⟩ := exists_copySeed copies p localRadius S
    hp hlocalRadius (by
      simpa [N] using (seedThreshold_le_sampleThreshold hr).trans hsample) hlocal'
  have hratio : ∀ i, (result.R i : ℝ) ≤ p * result.U.card / (512 * r) := by
    intro i
    exact (hresultRadius i).trans (by
      simpa [p, localRadius] using
        (localJansonRadius_le_seedRatio (r := r) (k := k) (N := N)
          (u := result.U.card) hr hk
          (by
            rw [result.candidate.2.1]
            exact Nat.le_add_right _ _)))
  have hpOne : p ≤ 1 := by
    dsimp [p, Events.rationalParameter]
    rw [div_le_one (by exact_mod_cast hpDen)]
    exact_mod_cast (show 1 ≤ keyDenominator r k by omega)
  have haggregate : 512 * (∑ i, result.R i) ≤ result.U.card :=
    MaximalSeed.aggregate_radius_bound result.R (by omega) hpOne hratio
  have hbounds := MaximalSeed.result_card_bounds result hr (by simpa [N] using hscale50)
    haggregate (by simpa [N] using hsample)
  refine ⟨coloring, S, result, hsample, hlocal, hratio, haggregate,
    by simpa [N] using hbounds.1, by simpa [N] using hbounds.2.1,
    by simpa [N] using hbounds.2.2.1, hbounds.2.2.2.2⟩

end Seed

/-! ## Fixed structural tuples covering the key exceptional event -/

section FixedTuples

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The upper seed-size estimate is the only restriction needed to count the
color graphs stored in a structural tuple. -/
def SeedSmall (r N : ℕ) (U : Finset V) : Prop :=
  r ^ 50 * U.card < 2 * N

/-- The exact event associated with one fixed structural tuple.  The global
coloring is quantified inside the fiber; it is never included in the outer
union bound. -/
def FixedSeedBad {r k N : ℕ} {order : Fin r → ℕ}
    (targets : Events.TargetVector r order)
    (sigma : KeyFixedTuple.Structure V r N (SeedSmall r N))
    (G : SimpleGraph V) : Prop :=
  ∃ coloring : G.EdgeLabeling (Fin r),
    KeyFixedTuple.Realizes sigma G coloring ∧
    sampleThreshold r N ≤ (KeyFixedTuple.vertexSet sigma).card ∧
    N ≤ r ^ 50 * (KeyFixedTuple.seedSet sigma).card ∧
    4 * (KeyFixedTuple.seedSet sigma).card ≤
      (KeyFixedTuple.vertexSet sigma).card ∧
    (∀ i, (copyHypergraph (targets i)
      (KeyFixedTuple.colorOnSeed sigma i)
      (KeyFixedTuple.ambientOnSeed sigma)).IsJanson
        (Events.rationalParameter 1 (keyDenominator r k))
        (KeyFixedTuple.radii sigma i)) ∧
    Events.StrongInductionEventGlobalOn 1 (keyDenominator r k) 1 (r ^ 50)
      (8 * r) order G ∧
    (∀ i, ¬ ((copyHypergraph (targets i)
      (Events.colorClassGraph coloring i) G).restrict
        (KeyFixedTuple.vertexSet sigma)).IsJanson
          (Events.rationalParameter 1 (keyDenominator r k))
          (Localization.localJansonRadius r 1 (keyDenominator r k) N)) ∧
    (∀ i, (KeyFixedTuple.radii sigma i : ℝ) ≤
      Events.rationalParameter 1 (keyDenominator r k) *
        (KeyFixedTuple.seedSet sigma).card / (512 * r)) ∧
    ∀ v, ∀ hv : v ∈ KeyFixedTuple.vertexSet sigma \ KeyFixedTuple.seedSet sigma, ∀ i,
      ¬ (copyHypergraph (targets i)
        (rootedRestrictionOn (Events.colorClassGraph coloring i) v
          (KeyFixedTuple.seedSet sigma) (Finset.mem_sdiff.mp hv).2)
        (rootedRestrictionOn G v (KeyFixedTuple.seedSet sigma)
          (Finset.mem_sdiff.mp hv).2)).IsJanson
          (Events.rationalParameter 1 (keyDenominator r k))
          (KeyFixedTuple.radii sigma i + 1)

/-- Localization and maximality place every graph in the key exceptional set
in one of the genuinely finite fixed-structural-tuple fibers. -/
theorem keyBadSetOn_subset_fixedSeedBadUnion
    {r k : ℕ} {order : Fin r → ℕ}
    (targets : Events.TargetVector r order)
    (hr : 2 ≤ r) (hk : 0 < k)
    (hscale34 : 2 * r ^ 34 ≤ Fintype.card V)
    (hscale50 : 2 * r ^ 50 ≤ Fintype.card V) :
    keyBadSetOn (V := V) k targets ⊆
      KeyUnion.badUnion (FixedSeedBad (V := V) (k := k)
        (N := Fintype.card V) targets) := by
  classical
  intro G hG
  have hbad := (mem_keyBadSetOn.mp hG).1
  have hstrong := (mem_keyBadSetOn.mp hG).2
  obtain ⟨coloring, S, result, hsample, hlocal, hratio, _haggregate,
      hUlower, _h511, hUupper, hfour⟩ :=
    exists_maximalCopySeedOn_of_bad targets G hr hk
      hscale34 hscale50 hbad
  have hSmall : SeedSmall r (Fintype.card V) result.U := by
    simpa [SeedSmall] using hUupper
  let sigma := KeyFixedTuple.ofSeed G coloring result
    (SeedSmall r (Fintype.card V)) hSmall rfl
  have hrealizes : KeyFixedTuple.Realizes sigma G coloring :=
    KeyFixedTuple.realizes_ofSeed G coloring result
      (SeedSmall r (Fintype.card V)) hSmall rfl
  rw [KeyUnion.badUnion, Finset.mem_biUnion]
  refine ⟨sigma, Finset.mem_univ _, ?_⟩
  rw [KeyUnion.badSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, coloring,
    hrealizes, ?_, ?_, ?_, ?_, hstrong, ?_, ?_, ?_⟩
  · change sampleThreshold r (Fintype.card V) ≤ S.card
    exact hsample
  · change Fintype.card V ≤ r ^ 50 * result.U.card
    exact hUlower
  · change 4 * result.U.card ≤ S.card
    exact hfour
  · intro i
    have hseed := localCopy_isJanson_of_global_restrict
      (p := Events.rationalParameter 1 (keyDenominator r k))
      (R := result.R i) (targets i) coloring i result.U
      (Events.rationalParameter_pos (by omega)
        (keyDenominator_pos (by omega) hk)) (by
          simpa [CopyGood] using result.candidate.2.2 i)
    have hamb := KeyFixedTuple.ambientOnSeed_eq_induce hrealizes
    change (copyHypergraph (targets i)
      (KeyFixedTuple.colorOnSeed sigma i)
      (KeyFixedTuple.ambientOnSeed sigma)).IsJanson
        (Events.rationalParameter 1 (keyDenominator r k)) (result.R i)
    rw [hrealizes.2.2 i, hamb]
    exact hseed
  · change ∀ i, ¬ ((copyHypergraph (targets i)
      (Events.colorClassGraph coloring i) G).restrict S).IsJanson
        (Events.rationalParameter 1 (keyDenominator r k))
        (Localization.localJansonRadius r 1 (keyDenominator r k)
          (Fintype.card V))
    exact hlocal
  · change ∀ i, (result.R i : ℝ) ≤
      Events.rationalParameter 1 (keyDenominator r k) * result.U.card / (512 * r)
    exact hratio
  · intro v hv i
    -- This is the injective relabelling of the global maximality failure to
    -- the canonical `Option U` one-vertex model.
    exact copySeed_extensionFailure_rooted result
      (Events.rationalParameter_pos (by omega)
        (keyDenominator_pos (by omega) hk)) v hv i

end FixedTuples

/-! ## Supersaturation supplied to the one-vertex extension lemma -/

section FixedSupersaturation

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem extensionP_eq_keyParameter (r k : ℕ) :
    Extension.extensionP r k =
      Events.rationalParameter 1 (keyDenominator r k) := by
  norm_num [Extension.extensionP, Events.rationalParameter, keyDenominator]

theorem fixedSeedBad_deleted_supersaturated
    {r k N : ℕ} {order : Fin r → ℕ}
    {targets : Events.TargetVector r order}
    {sigma : KeyFixedTuple.Structure V r N (SeedSmall r N)}
    {G : SimpleGraph V} (hV : Fintype.card V = N)
    (hbad : FixedSeedBad (k := k) targets sigma G)
    (hr : 2 ≤ r) (hk : 0 < k) (i : Fin r) (root : Fin (order i))
    (hi : 2 ≤ order i) :
    ∀ W : Finset ↑(KeyFixedTuple.seedSet sigma),
      (KeyFixedTuple.seedSet sigma).card ≤ 8 * r * W.card →
      ((copyHypergraph (deleteVertex (targets i) root)
        (KeyFixedTuple.colorOnSeed sigma i)
        (KeyFixedTuple.ambientOnSeed sigma)).restrict W).IsJanson
          (Extension.extensionP r k)
          (Extension.extensionR r k (KeyFixedTuple.seedSet sigma).card) := by
  classical
  rcases hbad with ⟨coloring, hreal, _hsample, hU, _hfour, _havail,
    hstrong, hlocal, hratio, _hfailure⟩
  intro W hUW
  let U := KeyFixedTuple.seedSet sigma
  let Wv : Finset V := W.image (fun u : ↑U ↦ u.1)
  have hWcard : Wv.card = W.card := by
    dsimp [Wv]
    exact Finset.card_image_iff.mpr fun x _ y _ h ↦ Subtype.ext h
  have hWvU : Wv ⊆ U := by
    intro x hx
    obtain ⟨u, _hu, rfl⟩ := Finset.mem_image.mp hx
    exact u.2
  have hWvS : Wv ⊆ KeyFixedTuple.vertexSet sigma :=
    hWvU.trans hreal.1
  have hpDen : 0 < keyDenominator r k := keyDenominator_pos (by omega) hk
  have hp : 0 < Events.rationalParameter 1 (keyDenominator r k) :=
    Events.rationalParameter_pos (by omega) hpDen
  have hsize : Events.MeetsDescendedSize 1 (r ^ 50) (8 * r) 1 N Wv.card := by
    unfold Events.MeetsDescendedSize
    simp only [pow_one, one_mul]
    rw [hWcard]
    calc
      N ≤ r ^ 50 * U.card := hU
      _ ≤ r ^ 50 * (8 * r * W.card) := Nat.mul_le_mul_left _ hUW
      _ = (8 * r * r ^ 50) * W.card := by ring
  have hlocalNonneg : 0 ≤
      Localization.localJansonRadius r 1 (keyDenominator r k) N := by
    unfold Localization.localJansonRadius Events.jansonRadius
    positivity
  have hlocalToW :
      Localization.localJansonRadius r 1 (keyDenominator r k) N ≤
        Events.jansonRadius 1 (keyDenominator r k) Wv.card := by
    calc
      Localization.localJansonRadius r 1 (keyDenominator r k) N ≤
          Events.rationalParameter 1 (keyDenominator r k) * U.card / (512 * r) :=
        by
          unfold Localization.localJansonRadius Events.jansonRadius
          rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 512 * r ^ 51)
            (by positivity : (0 : ℝ) < 512 * r)]
          have hUreal : (N : ℝ) ≤ (r : ℝ) ^ 50 * U.card := by
            exact_mod_cast hU
          calc
            Events.rationalParameter 1 (keyDenominator r k) * N * (512 * r) ≤
                Events.rationalParameter 1 (keyDenominator r k) *
                  ((r : ℝ) ^ 50 * U.card) * (512 * r) := by gcongr
            _ = Events.rationalParameter 1 (keyDenominator r k) * U.card *
                  (512 * r ^ 51) := by ring
      _ ≤ Events.rationalParameter 1 (keyDenominator r k) * W.card := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 512 * r)]
        have hUWreal : (U.card : ℝ) ≤ 8 * r * W.card := by exact_mod_cast hUW
        nlinarith [hp]
      _ = Events.jansonRadius 1 (keyDenominator r k) Wv.card := by
        rw [Events.jansonRadius, hWcard]
  have hglobal := DeletedTarget.deletedTarget_isJanson i root hi hstrong coloring
    hWvS (by simpa [hV] using hsize) (by simpa [hV] using hlocal) hp
      (by simpa [hV] using hlocalNonneg) (by simpa [hV] using hlocalToW)
  let H := copyHypergraph (DeletedTarget.deleteVertexFin (targets i) root)
    (KeyFixedTuple.colorOnSeed sigma i) (KeyFixedTuple.ambientOnSeed sigma)
  let f : ↑U → V := fun u ↦ u.1
  have hmapU : H.map f =
      (copyHypergraph (DeletedTarget.deleteVertexFin (targets i) root)
        (Events.colorClassGraph coloring i) G).restrict U := by
    have h0 := map_copyHypergraph_pullback_induce_eq_restrict
      (DeletedTarget.deleteVertexFin (targets i) root) G coloring i U
    rw [labelGraph_pullback_induce_eq_induce coloring i U] at h0
    have hamb := KeyFixedTuple.ambientOnSeed_eq_induce hreal
    have hcolorU : (Events.colorClassGraph coloring i).induce (↑U : Set V) =
        KeyFixedTuple.colorOnSeed sigma i := by
      change (coloring.labelGraph i).induce (↑U : Set V) =
        KeyFixedTuple.colorOnSeed sigma i
      simpa [U] using (hreal.2.2 i).symm
    have hcolorU' : (coloring.labelGraph i).induce (↑U : Set V) =
        KeyFixedTuple.colorOnSeed sigma i := hcolorU
    have hambU : G.induce (↑U : Set V) = KeyFixedTuple.ambientOnSeed sigma := by
      simpa [U] using hamb.symm
    rw [hcolorU', hambU] at h0
    simpa [H, f, U] using h0
  have hmapW : (H.restrict W).map f =
      (copyHypergraph (DeletedTarget.deleteVertexFin (targets i) root)
        (Events.colorClassGraph coloring i) G).restrict Wv := by
    calc
      (H.restrict W).map f = (H.map f).restrict (W.image f) :=
        map_restrict_eq_restrict_map_of_injective H W f
          (fun x y h ↦ Subtype.ext h)
      _ = ((copyHypergraph (DeletedTarget.deleteVertexFin (targets i) root)
          (Events.colorClassGraph coloring i) G).restrict U).restrict Wv := by
        rw [hmapU]
      _ = (copyHypergraph (DeletedTarget.deleteVertexFin (targets i) root)
          (Events.colorClassGraph coloring i) G).restrict Wv := by
        rw [Hypergraph.restrict_restrict]
        congr 2
        exact Finset.inter_eq_right.mpr hWvU
  have hinj : Hypergraph.EdgewiseInjective (H.restrict W) f := by
    intro E _hE x _hx y _hy hxy
    exact Subtype.ext hxy
  have hcanonicalW : (H.restrict W).IsJanson
      (Events.rationalParameter 1 (keyDenominator r k))
      (Events.jansonRadius 1 (keyDenominator r k) Wv.card) := by
    apply Hypergraph.IsJanson.pullback hinj hp
    rwa [hmapW]
  have hExtRadius : Extension.extensionR r k U.card ≤
      Events.jansonRadius 1 (keyDenominator r k) Wv.card := by
    rw [Extension.extensionR, extensionP_eq_keyParameter, Events.jansonRadius, hWcard]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 32 * r)]
    have hUWreal : (U.card : ℝ) ≤ 8 * r * W.card := by exact_mod_cast hUW
    nlinarith [hp]
  have hcanonical : (H.restrict W).IsJanson
      (Events.rationalParameter 1 (keyDenominator r k))
      (Extension.extensionR r k U.card) :=
    Hypergraph.IsJanson.mono_params hcanonicalW hp (le_refl _)
      (by
        unfold Extension.extensionR
        exact div_nonneg
          (mul_nonneg (by unfold Extension.extensionP; positivity) (Nat.cast_nonneg _))
          (by positivity)) hExtRadius
  obtain ⟨e⟩ := DeletedTarget.deleteVertex_iso_deleteVertexFin (targets i) root
  have htarget := copyHypergraph_eq_of_iso e
    (KeyFixedTuple.colorOnSeed sigma i) (KeyFixedTuple.ambientOnSeed sigma)
  rw [extensionP_eq_keyParameter]
  rw [htarget]
  exact hcanonical

end FixedSupersaturation

/-! ## The unconditional one-star estimate for a fixed tuple -/

section FixedExtension

variable {V : Type*} [Fintype V] [DecidableEq V]

def liftOldGraph {U : Type*} (H : SimpleGraph U) : SimpleGraph (Option U) :=
  H.map some

@[simp] theorem oldPart_liftOldGraph {U : Type*} (H : SimpleGraph U) :
    oldPart (liftOldGraph H) = H := by
  ext x y
  change (H.map (↑(⟨some, Option.some_injective U⟩ : U ↪ Option U))).Adj
      (some x) (some y) ↔ H.Adj x y
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp at ha hb
    subst a
    subst b
    exact hab
  · intro hxy
    exact ⟨x, y, hxy, rfl, rfl⟩

theorem seed_card_scale {r k t N u : ℕ}
    (hr : 2 ≤ r) (ht : 1 ≤ t)
    (hscale : r ^ (300 * (k + t)) ≤ N)
    (hU : N ≤ r ^ 50 * u) : r ^ (300 * k) ≤ u := by
  have hpow : r ^ (300 * k + 50) ≤ N := by
    exact (Nat.pow_le_pow_right (by omega)
      (by nlinarith : 300 * k + 50 ≤ 300 * (k + t))).trans hscale
  have hmul : r ^ 50 * r ^ (300 * k) ≤ r ^ 50 * u := by
    calc
      r ^ 50 * r ^ (300 * k) = r ^ (300 * k + 50) := by
        rw [pow_add]
        ring
      _ ≤ N := hpow
      _ ≤ r ^ 50 * u := hU
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos (by omega))

theorem seed_card_ge_22 {r k t N u : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) (ht : 1 ≤ t)
    (hscale : r ^ (300 * (k + t)) ≤ N)
    (hU : N ≤ r ^ 50 * u) : 22 ≤ u := by
  have hseed := seed_card_scale hr ht hscale hU
  calc
    22 ≤ 2 ^ 5 := by norm_num
    _ ≤ r ^ 5 := Numeric.two_pow_le_r_pow hr
    _ ≤ r ^ (300 * k) := by
      apply Nat.pow_le_pow_right (by omega)
      have := hk
      nlinarith
    _ ≤ u := hseed

theorem fixedSeedBad_extension_card
    {r k N : ℕ} {order : Fin r → ℕ}
    {targets : Events.TargetVector r order}
    {sigma : KeyFixedTuple.Structure V r N (SeedSmall r N)}
    {G : SimpleGraph V} (hV : Fintype.card V = N)
    (hbad : FixedSeedBad (k := k) targets sigma G)
    (hr : 2 ≤ r) (hk : 2 ≤ k) (horder : ∀ i, 2 ≤ order i)
    (hord : ∀ i, order i ≤ k)
    (hscale : r ^ (300 * (k + Events.totalOrder order)) ≤ N)
    (i : Fin r) :
    (Extension.graphExtensionBadStars (targets i)
      (KeyFixedTuple.colorOnSeed sigma i)
      (KeyFixedTuple.ambientOnSeed sigma)
      (Events.rationalParameter 1 (keyDenominator r k))
      (KeyFixedTuple.radii sigma i + 1)
      ((KeyFixedTuple.seedSet sigma).card ⌈/⌉ (4 * r))).card *
        2 ^ ((KeyFixedTuple.seedSet sigma).card / (32 * r)) ≤
      2 ^ (KeyFixedTuple.seedSet sigma).card := by
  classical
  have hbad' := hbad
  rcases hbad' with ⟨_coloring, _hreal, _hsample, hU, _hfour, havail,
    _hstrong, _hlocal, hratio, _hfailure⟩
  have hiorder := horder i
  have hik := hord i
  let root : Fin (order i) := ⟨0, by omega⟩
  let s := order i - 1
  have ht : 1 ≤ Events.totalOrder order := by
    have hi : order i ≤ ∑ j, order j :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    simpa [Events.totalOrder] using (show 1 ≤ ∑ j, order j from
      (show 1 ≤ order i by omega).trans hi)
  have hseedScale : r ^ (300 * k) ≤ (KeyFixedTuple.seedSet sigma).card :=
    seed_card_scale hr ht hscale hU
  have hseedPos : 0 < (KeyFixedTuple.seedSet sigma).card :=
    (Nat.pow_pos (by omega)).trans_le hseedScale
  let : Nonempty ↑(KeyFixedTuple.seedSet sigma) :=
    Fintype.card_pos_iff.mp (by simpa using hseedPos)
  have hspos : 1 ≤ s := by dsimp [s]; omega
  have hs : s + 1 ≤ k := by dsimp [s]; omega
  have htarget : Fintype.card (Fin (order i)) = s + 1 := by
    simp [s]
    omega
  have hR : (KeyFixedTuple.radii sigma i : ℝ) ≤
      Extension.extensionR r k (KeyFixedTuple.seedSet sigma).card / 16 := by
    calc
      (KeyFixedTuple.radii sigma i : ℝ) ≤
          Events.rationalParameter 1 (keyDenominator r k) *
            (KeyFixedTuple.seedSet sigma).card / (512 * r) := hratio i
      _ = Extension.extensionR r k (KeyFixedTuple.seedSet sigma).card / 16 := by
        rw [Extension.extensionR, extensionP_eq_keyParameter]
        ring
  have hseedScale' : r ^ (300 * k) ≤
      Fintype.card ↑(KeyFixedTuple.seedSet sigma) := by
    simpa using hseedScale
  have hR' : (KeyFixedTuple.radii sigma i : ℝ) ≤
      Extension.extensionR r k
        (Fintype.card ↑(KeyFixedTuple.seedSet sigma)) / 16 := by
    simpa using hR
  have h := Extension.strongExtensionLemma (targets i) root
    (liftOldGraph (KeyFixedTuple.colorOnSeed sigma i))
    (liftOldGraph (KeyFixedTuple.ambientOnSeed sigma)) r k s
    (KeyFixedTuple.radii sigma i) hr hk hspos hs htarget
    hseedScale'
    (by positivity) hR' (by
      simpa [extensionP_eq_keyParameter] using havail i)
    (by
      simpa only [Fintype.card_coe, oldPart_liftOldGraph] using
        (fixedSeedBad_deleted_supersaturated hV hbad
          hr (by omega) i root (horder i)))
  simpa [oldPart_liftOldGraph, extensionP_eq_keyParameter] using h

end FixedExtension

/-! ## Fixed-tuple event and its low/high-degree split -/

section FixedFiber

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem map_graphStar_rooted_color
    {r : ℕ} {G : SimpleGraph V} (coloring : G.EdgeLabeling (Fin r))
    (i : Fin r) (v : V) (U : Finset V) (hv : v ∉ U) :
    (Extension.graphStar
      (rootedRestrictionOn (Events.colorClassGraph coloring i) v U hv)).map
        ⟨Subtype.val, Subtype.val_injective⟩ =
      KeyFixedTuple.colorNeighbors coloring U v i := by
  classical
  ext u
  simp only [Finset.mem_map, Extension.mem_graphStar,
    KeyFixedTuple.colorNeighbors, Finset.mem_filter]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, by simpa [SimpleGraph.adj_comm] using hw⟩
  · rintro ⟨hu, huv⟩
    exact ⟨⟨u, hu⟩, by simpa [SimpleGraph.adj_comm] using huv, rfl⟩

abbrev StarIndex (r : ℕ) (T U : Finset V) :=
  Fin r × {A : Finset V //
    A ⊆ T ∧ Disjoint A U ∧ T.card < 4 * r * A.card}

noncomputable def fixedStarEvent
    {r k N : ℕ} {order : Fin r → ℕ}
    (targets : Events.TargetVector r order)
    (sigma : KeyFixedTuple.Structure V r N (SeedSmall r N))
    (T : Finset V)
    (x : StarIndex r T (KeyFixedTuple.seedSet sigma)) : Finset (SimpleGraph V) := by
  classical
  let A := x.2.1
  have hAU : Disjoint A (KeyFixedTuple.seedSet sigma) := x.2.2.2.1
  let bad := Extension.graphExtensionBadStars (targets x.1)
    (KeyFixedTuple.colorOnSeed sigma x.1)
    (KeyFixedTuple.ambientOnSeed sigma)
    (Events.rationalParameter 1 (keyDenominator r k))
    (KeyFixedTuple.radii sigma x.1 + 1)
    ((KeyFixedTuple.seedSet sigma).card ⌈/⌉ (4 * r))
  exact Finset.univ.filter fun G ↦
    RandomGraph.supportedEvents Finset.univ
      (RandomGraph.indexedStarEdges A (KeyFixedTuple.seedSet sigma) hAU)
      (fun a X ↦ X ∈ KeyFixedTuple.liftedBadStars a.1
        (KeyFixedTuple.seedSet sigma)
        (fun ha ↦ Finset.disjoint_left.mp hAU a.2 ha) bad)
      (RandomGraph.edgesOfGraph G)

theorem fixedStarEvent_card_mul_pow_le
    {r k N : ℕ} {order : Fin r → ℕ}
    {targets : Events.TargetVector r order}
    {sigma : KeyFixedTuple.Structure V r N (SeedSmall r N)}
    (hV : Fintype.card V = N)
    (hbad : ∃ G : SimpleGraph V, FixedSeedBad (k := k) targets sigma G)
    (hr : 2 ≤ r) (hk : 2 ≤ k) (horder : ∀ i, 2 ≤ order i)
    (hord : ∀ i, order i ≤ k)
    (hscale : r ^ (300 * (k + Events.totalOrder order)) ≤ N)
    (T : Finset V)
    (hS : N ≤ r ^ 34 * (KeyFixedTuple.vertexSet sigma).card)
    (hU : N ≤ r ^ 50 * (KeyFixedTuple.seedSet sigma).card)
    (hsum : T.card + (KeyFixedTuple.seedSet sigma).card =
      (KeyFixedTuple.vertexSet sigma).card)
    (hfour : 4 * (KeyFixedTuple.seedSet sigma).card ≤
      (KeyFixedTuple.vertexSet sigma).card)
    (x : StarIndex r T (KeyFixedTuple.seedSet sigma)) :
    (fixedStarEvent (k := k) targets sigma T x).card *
        2 ^ (2 * N + (8 * r * keyExponent r N + 1)) ≤
      Fintype.card (SimpleGraph V) := by
  classical
  let U := KeyFixedTuple.seedSet sigma
  let A := x.2.1
  have hAU : Disjoint A U := x.2.2.2.1
  let bad := Extension.graphExtensionBadStars (targets x.1)
    (KeyFixedTuple.colorOnSeed sigma x.1)
    (KeyFixedTuple.ambientOnSeed sigma)
    (Events.rationalParameter 1 (keyDenominator r k))
    (KeyFixedTuple.radii sigma x.1 + 1) (U.card ⌈/⌉ (4 * r))
  have hbadCard : bad.card * 2 ^ (U.card / (32 * r)) ≤ 2 ^ U.card := by
    obtain ⟨G, hG⟩ := hbad
    simpa [bad, U] using
      (fixedSeedBad_extension_card hV hG hr hk horder hord hscale x.1)
  have hsample := card_uniform_bad_star_family_mul_pow_le A U hAU
    (U.card / (32 * r)) (fun _ ↦ bad) (fun _ ↦ hbadCard)
  let P : Finset (RandomGraph.Edge V) → Prop :=
    RandomGraph.supportedEvents Finset.univ
      (RandomGraph.indexedStarEdges A U hAU)
      (fun a X ↦ X ∈ KeyFixedTuple.liftedBadStars a.1 U
        (fun ha ↦ Finset.disjoint_left.mp hAU a.2 ha) bad)
  have hgraph : (fixedStarEvent (k := k) targets sigma T x).card ≤
      (RandomGraph.eventSamples (RandomGraph.edgeUniverse V) P).card := by
    have hle := card_graphEvent_le_eventSamples
      (fun G : SimpleGraph V ↦ P (RandomGraph.edgesOfGraph G)) P
      (fun _ h ↦ h)
    simpa [fixedStarEvent, P, A, U, bad] using hle
  have hexp : 2 * N + 8 * r * keyExponent r N + 1 ≤
      A.card * (U.card / (32 * r)) := by
    simpa [keyExponent, A, U] using
      (Numeric.fixed_extension_exponent hr hk hscale hS hU hsum hfour
        x.2.2.2.2)
  calc
    (fixedStarEvent (k := k) targets sigma T x).card *
        2 ^ (2 * N + (8 * r * keyExponent r N + 1)) ≤
      (RandomGraph.eventSamples (RandomGraph.edgeUniverse V) P).card *
        2 ^ (2 * N + (8 * r * keyExponent r N + 1)) :=
      Nat.mul_le_mul_right _ hgraph
    _ ≤ (RandomGraph.eventSamples (RandomGraph.edgeUniverse V) P).card *
        2 ^ (A.card * (U.card / (32 * r))) := by
      exact Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by decide : 0 < 2) hexp)
    _ ≤ Fintype.card (SimpleGraph V) := by
      simpa [P, A, U, bad] using hsample

theorem fixedSeedBadSet_subset_low_union_high
    {r k N : ℕ} {order : Fin r → ℕ}
    {targets : Events.TargetVector r order}
    [DecidableEq (SimpleGraph V)]
    (sigma : KeyFixedTuple.Structure V r N (SeedSmall r N))
    (hr : 2 ≤ r) :
    KeyUnion.badSet (FixedSeedBad (k := k) targets) sigma ⊆
      Chernoff.fewHighGraphs (KeyFixedTuple.seedSet sigma)
          (KeyFixedTuple.vertexSet sigma \ KeyFixedTuple.seedSet sigma)
          Finset.disjoint_sdiff ∪
        Finset.univ.biUnion (fixedStarEvent (k := k) targets sigma
          (KeyFixedTuple.vertexSet sigma \ KeyFixedTuple.seedSet sigma)) := by
  classical
  let U := KeyFixedTuple.seedSet sigma
  let T := KeyFixedTuple.vertexSet sigma \ U
  have hUT : Disjoint U T := Finset.disjoint_sdiff
  intro G hG
  have hbadG : FixedSeedBad (k := k) targets sigma G :=
    (Finset.mem_filter.mp hG).2
  rcases hbadG with ⟨coloring, hreal, _hsample, _hU, _hfour, _havail,
    _hstrong, _hlocal, _hratio, hfailure⟩
  by_cases hfew : G ∈ Chernoff.fewHighGraphs U T hUT
  · exact Finset.mem_union_left _ hfew
  · apply Finset.mem_union_right
    have hhigh : T.card < 4 * (Chernoff.highDegreeVertices G U T).card := by
      rw [Chernoff.mem_fewHighGraphs_iff] at hfew
      omega
    have hdeg : ∀ v ∈ Chernoff.highDegreeVertices G U T,
        U.card < 4 * (KeyFixedTuple.ambientNeighbors G U v).card := by
      intro v hv
      have hv' := (Finset.mem_filter.mp hv).2
      simpa [Chernoff.highDegreeVertices, Chernoff.degreeInto,
        KeyFixedTuple.ambientNeighbors] using hv'
    obtain ⟨i, A, hAH, hHA, hcolor⟩ :=
      KeyFixedTuple.exists_common_highColor coloring U
        (Chernoff.highDegreeVertices G U T) (by omega) hdeg
    have hHT : Chernoff.highDegreeVertices G U T ⊆ T :=
      Finset.filter_subset _ _
    have hAT : A ⊆ T := hAH.trans hHT
    have hAU : Disjoint A U := (hUT.mono_right hAT).symm
    have hsize : T.card < 4 * r * A.card := by
      calc
        T.card < 4 * (Chernoff.highDegreeVertices G U T).card := hhigh
        _ ≤ 4 * (r * A.card) := Nat.mul_le_mul_left 4 hHA
        _ = 4 * r * A.card := by ring
    let x : StarIndex r T U := ⟨i, ⟨A, hAT, hAU, hsize⟩⟩
    rw [Finset.mem_biUnion]
    refine ⟨x, Finset.mem_univ _, ?_⟩
    rw [fixedStarEvent, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold RandomGraph.supportedEvents
    intro a _ha
    let haT : a.1 ∈ T := hAT a.2
    let haU : a.1 ∉ U := (Finset.mem_sdiff.mp haT).2
    let localAmbient := rootedRestrictionOn G a.1 U haU
    let localColor := rootedRestrictionOn
      (Events.colorClassGraph coloring i) a.1 U haU
    let B := Extension.graphStar localAmbient
    apply (KeyFixedTuple.mem_liftedBadStars_iff
      (v := a.1) (U := U) (hv := haU)).2
    refine ⟨B, ?_, ?_⟩
    · rw [Extension.mem_graphExtensionBadStars]
      refine ⟨Finset.subset_univ _, localColor, localAmbient, ?_, ?_, ?_, rfl, ?_, ?_⟩
      · exact rootedRestrictionOn_mono
          (SimpleGraph.EdgeLabeling.labelGraph_le coloring) a.1 U haU
      · rw [oldPart_rootedRestrictionOn]
        simpa [U] using (hreal.2.2 i).symm
      · rw [oldPart_rootedRestrictionOn]
        simpa [U] using (KeyFixedTuple.ambientOnSeed_eq_induce hreal).symm
      · apply (ceilDiv_le_iff_le_mul (by positivity : 0 < 4 * r)).2
        have hc := congrArg Finset.card
          (map_graphStar_rooted_color coloring i a.1 U haU)
        have hc' : (Extension.graphStar localColor).card =
            (KeyFixedTuple.colorNeighbors coloring U a.1 i).card := by
          simpa [localColor] using hc
        rw [hc']
        exact (hcolor a.1 a.2).le
      · simpa [localColor, localAmbient, U, T, haT, haU] using
          hfailure a.1 haT i
    · simpa [B, localAmbient, RandomGraph.indexedStarEdges] using
        (liftStar_graphStar_rootedRestrictionOn G a.1 U haU)

/-- The exact fixed-structural-tuple estimate used by the final dependent
union bound. -/
theorem fixedSeedBad_card_mul_pow_le
    {r k N : ℕ} {order : Fin r → ℕ}
    {targets : Events.TargetVector r order}
    (hV : Fintype.card V = N)
    (hr : 2 ≤ r) (hk : 2 ≤ k) (horder : ∀ i, 2 ≤ order i)
    (hord : ∀ i, order i ≤ k)
    (hscale : r ^ (300 * (k + Events.totalOrder order)) ≤ N)
    (sigma : KeyFixedTuple.Structure V r N (SeedSmall r N)) :
    (KeyUnion.badSet (FixedSeedBad (k := k) targets) sigma).card *
        2 ^ (8 * r * keyExponent r N) ≤ Fintype.card (SimpleGraph V) := by
  classical
  by_cases hB :
      (KeyUnion.badSet (FixedSeedBad (k := k) targets) sigma).Nonempty
  · obtain ⟨G₀, hG₀⟩ := hB
    have hbad₀ : FixedSeedBad (k := k) targets sigma G₀ := by
      simpa [KeyUnion.badSet] using hG₀
    have hbadWitness : ∃ G : SimpleGraph V,
        FixedSeedBad (k := k) targets sigma G := ⟨G₀, hbad₀⟩
    rcases hbad₀ with ⟨_coloring₀, hreal₀, hsample₀, hU₀, hfour₀,
      _havail₀, _hstrong₀, _hlocal₀, _hratio₀, _hfailure₀⟩
    let S := KeyFixedTuple.vertexSet sigma
    let U := KeyFixedTuple.seedSet sigma
    let T := S \ U
    let D := keyExponent r N
    have hUS : U ⊆ S := by simpa [U, S] using hreal₀.1
    have hUT : Disjoint U T := by
      simpa [T] using (Finset.disjoint_sdiff : Disjoint U (S \ U))
    have hsum : T.card + U.card = S.card := by
      simpa [T] using Finset.card_sdiff_add_card_eq_card hUS
    have hS : N ≤ r ^ 34 * S.card := by
      calc
        N ≤ r ^ 34 * sampleThreshold r N := sampleThreshold_lower hr
        _ ≤ r ^ 34 * S.card := by
          exact Nat.mul_le_mul_left _ (by simpa [S] using hsample₀)
    have hU : N ≤ r ^ 50 * U.card := by simpa [U] using hU₀
    have hfour : 4 * U.card ≤ S.card := by simpa [U, S] using hfour₀
    let i₀ : Fin r := ⟨0, by omega⟩
    have ht : 1 ≤ Events.totalOrder order := by
      have hi : order i₀ ≤ ∑ i, order i :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i₀)
      simpa [Events.totalOrder] using
        (show 1 ≤ ∑ i, order i from (by
          have hiorder := horder i₀
          omega))
    have hU22 : 22 ≤ U.card := by
      simpa [U] using seed_card_ge_22 hr hk ht hscale hU
    have hT2 : 2 ≤ T.card := by omega
    have hq : 64 * (8 * r * D + 1) ≤ T.card * U.card := by
      simpa [D, keyExponent] using
        (Numeric.fixed_chernoff_exponent hr hk hscale hS hU hsum hfour)
    have hlow :
        (Chernoff.fewHighGraphs U T hUT).card * 2 ^ (8 * r * D + 1) ≤
          Fintype.card (SimpleGraph V) :=
      fewHighGraphs_card_mul_pow_le U T hUT (8 * r * D + 1) hT2 hU22 hq
    have hrN : r ≤ N := by
      calc
        r = r ^ 1 := by simp
        _ ≤ r ^ (300 * (k + Events.totalOrder order)) := by
          apply Nat.pow_le_pow_right (by omega)
          nlinarith
        _ ≤ N := hscale
    have hrPow : r ≤ 2 ^ N := hrN.trans Nat.lt_two_pow_self.le
    have hsubtype :
        Fintype.card {A : Finset V //
          A ⊆ T ∧ Disjoint A U ∧ T.card < 4 * r * A.card} ≤ 2 ^ N := by
      calc
        Fintype.card {A : Finset V //
            A ⊆ T ∧ Disjoint A U ∧ T.card < 4 * r * A.card} ≤
            Fintype.card (Finset V) := Fintype.card_subtype_le _
        _ = 2 ^ N := by simp [Fintype.card_finset, hV]
    have hindex : Fintype.card (StarIndex r T U) ≤ 2 ^ (2 * N) := by
      calc
        Fintype.card (StarIndex r T U) =
            r * Fintype.card {A : Finset V //
              A ⊆ T ∧ Disjoint A U ∧ T.card < 4 * r * A.card} := by
          simp [StarIndex, Fintype.card_prod]
        _ ≤ 2 ^ N * 2 ^ N := Nat.mul_le_mul hrPow hsubtype
        _ = 2 ^ (2 * N) := by
          rw [← pow_add]
          congr 1
          omega
    have hhigh :
        (Finset.univ.biUnion
          (fixedStarEvent (k := k) targets sigma T)).card *
            2 ^ (8 * r * D + 1) ≤ Fintype.card (SimpleGraph V) := by
      apply KeyFiberCounting.card_biUnion_mul_pow_le
        (fixedStarEvent (k := k) targets sigma T) (2 * N) (8 * r * D + 1)
        hindex
      intro x
      simpa [D] using
        (fixedStarEvent_card_mul_pow_le hV hbadWitness hr hk horder hord
          hscale T hS hU hsum hfour x)
    have hunion := KeyFiberCounting.card_union_mul_pow_le
      (Chernoff.fewHighGraphs U T hUT)
      (Finset.univ.biUnion (fixedStarEvent (k := k) targets sigma T))
      (8 * r * D) hlow hhigh
    have hsubset :
        KeyUnion.badSet (FixedSeedBad (k := k) targets) sigma ⊆
          Chernoff.fewHighGraphs U T hUT ∪
            Finset.univ.biUnion
              (fixedStarEvent (k := k) targets sigma T) := by
      simpa [U, T, S] using
        (fixedSeedBadSet_subset_low_union_high sigma hr)
    calc
      (KeyUnion.badSet (FixedSeedBad (k := k) targets) sigma).card *
          2 ^ (8 * r * keyExponent r N) ≤
        (Chernoff.fewHighGraphs U T hUT ∪
          Finset.univ.biUnion
            (fixedStarEvent (k := k) targets sigma T)).card *
              2 ^ (8 * r * D) := by
        simpa [D] using Nat.mul_le_mul_right (2 ^ (8 * r * D))
          (Finset.card_le_card hsubset)
      _ ≤ Fintype.card (SimpleGraph V) := hunion
  · have hempty :
        KeyUnion.badSet (FixedSeedBad (k := k) targets) sigma = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hB
    simp [hempty]

end FixedFiber

/-! ## Deleted-target supersaturation -/

section DeletedTarget

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If the strong-induction event chooses an unchanged color, its Janson
witness contradicts the localized failure for that color.  Hence the winning
color must be the uniquely changed coordinate. -/
theorem changedColor_isJanson
    {r : ℕ} {order smaller : Fin r → ℕ}
    {pNum pDen deltaNum deltaDen shrinkDen : ℕ}
    {targets : Events.TargetVector r order}
    {smallerTargets : Events.TargetVector r smaller}
    {G : SimpleGraph V} {S W : Finset V} {i : Fin r}
    (hstrong : Events.StrongInductionEventGlobalOn pNum pDen deltaNum deltaDen
      shrinkDen order G)
    (hcoord : ∀ j, smaller j ≤ order j)
    (htotal : Events.totalOrder smaller < Events.totalOrder order)
    (hsize : Events.MeetsDescendedSize deltaNum deltaDen shrinkDen
      (Events.totalOrder order - Events.totalOrder smaller)
      (Fintype.card V) W.card)
    (coloring : G.EdgeLabeling (Fin r))
    (hWS : W ⊆ S)
    (hunchanged : ∀ j, j ≠ i →
      copyHypergraph (smallerTargets j) (Events.colorClassGraph coloring j) G =
        copyHypergraph (targets j) (Events.colorClassGraph coloring j) G)
    (hlocal : ∀ j,
      ¬ Hypergraph.IsJanson
        ((copyHypergraph (targets j) (Events.colorClassGraph coloring j) G).restrict S)
        (Events.rationalParameter pNum pDen)
        (Localization.localJansonRadius r pNum pDen (Fintype.card V)))
    (hp : 0 < Events.rationalParameter pNum pDen)
    (hlocalRadius : 0 ≤
      Localization.localJansonRadius r pNum pDen (Fintype.card V))
    (hradius : Localization.localJansonRadius r pNum pDen (Fintype.card V) ≤
      Events.jansonRadius pNum pDen W.card) :
    Hypergraph.IsJanson
      ((copyHypergraph (smallerTargets i) (Events.colorClassGraph coloring i) G).restrict W)
      (Events.rationalParameter pNum pDen)
      (Events.jansonRadius pNum pDen W.card) := by
  classical
  obtain ⟨j, hj⟩ := hstrong smaller hcoord htotal smallerTargets W hsize coloring
  by_cases hji : j = i
  · subst j
    exact hj
  · have hcopy := hunchanged j hji
    have hj' : Hypergraph.IsJanson
        ((copyHypergraph (targets j) (Events.colorClassGraph coloring j) G).restrict W)
        (Events.rationalParameter pNum pDen)
        (Events.jansonRadius pNum pDen W.card) := by
      rw [← hcopy]
      exact hj
    have hjS : Hypergraph.IsJanson
        ((copyHypergraph (targets j) (Events.colorClassGraph coloring j) G).restrict S)
        (Events.rationalParameter pNum pDen)
        (Events.jansonRadius pNum pDen W.card) :=
      Hypergraph.IsJanson.mono_edges
        (Hypergraph.restrict_mono_right _ hWS) hj'
    exact False.elim <| hlocal j <|
      Hypergraph.IsJanson.mono_params hjS hp (le_refl _)
        hlocalRadius hradius

end DeletedTarget

/-! ## The ACDFM key lemma -/

section FinalKeyLemma

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The nondegenerate form of the ACDFM key lemma.  All probabilistic,
localization, extension, and fixed-tuple estimates have been discharged in
the preceding lemmas; the proof here is the final structural union. -/
theorem acdfm_key_lemma_on_of_orders_ge_two
    {r k : ℕ} {order : Fin r → ℕ}
    (targets : Events.TargetVector r order)
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (horder : ∀ i, 2 ≤ order i)
    (hord : ∀ i, order i ≤ k)
    (hscale : r ^ (300 * (k + Events.totalOrder order)) ≤ Fintype.card V) :
    (keyBadSetOn (V := V) k targets).card *
        2 ^ keyExponent r (Fintype.card V) ≤
      Fintype.card (SimpleGraph V) := by
  classical
  have hscalePow (a : ℕ)
      (ha : a + 1 ≤ 300 * (k + Events.totalOrder order)) :
      2 * r ^ a ≤ Fintype.card V := by
    calc
      2 * r ^ a ≤ r * r ^ a := Nat.mul_le_mul_right _ hr
      _ = r ^ (a + 1) := by rw [pow_succ]; ring
      _ ≤ r ^ (300 * (k + Events.totalOrder order)) :=
        Nat.pow_le_pow_right (by omega) ha
      _ ≤ Fintype.card V := hscale
  have hscale34 : 2 * r ^ 34 ≤ Fintype.card V :=
    hscalePow 34 (by nlinarith)
  have hscale50 : 2 * r ^ 50 ≤ Fintype.card V :=
    hscalePow 50 (by nlinarith)
  have hcover : keyBadSetOn (V := V) k targets ⊆
      KeyUnion.badUnion (FixedSeedBad (V := V) (k := k)
        (N := Fintype.card V) targets) :=
    keyBadSetOn_subset_fixedSeedBadUnion targets hr (by omega)
      hscale34 hscale50
  have hND : Fintype.card V ≤
      r * keyExponent r (Fintype.card V) := by
    simpa [keyExponent] using
      (Numeric.le_r_mul_key_quotient hr hk hscale)
  have hR : (Fintype.card V + 1) ^ r ≤ 2 ^ Fintype.card V :=
    Numeric.radius_vector_count_le hr hk hscale
  have hSmall : ∀ U : Finset V, SeedSmall r (Fintype.card V) U →
      r * U.card.choose 2 ≤
        4 * r * keyExponent r (Fintype.card V) := by
    intro U hU
    simpa [keyExponent, SeedSmall] using
      (Numeric.choose_seed_le_four_key_quotient hr hk hscale hU)
  have hfixed : ∀ sigma : KeyStructure.RestrictedStructure V r
      (Fintype.card V) (SeedSmall r (Fintype.card V)),
      (KeyUnion.badSet
        (FixedSeedBad (V := V) (k := k) (N := Fintype.card V) targets)
        sigma).card *
          2 ^ (8 * r * keyExponent r (Fintype.card V)) ≤
        Fintype.card (SimpleGraph V) := by
    intro sigma
    exact fixedSeedBad_card_mul_pow_le rfl hr hk horder hord hscale sigma
  have hstructural := KeyFiberCounting.dependent_key_union_bound_scaled
    r (Fintype.card V) (keyExponent r (Fintype.card V))
    (SeedSmall r (Fintype.card V))
    (FixedSeedBad (V := V) (k := k) (N := Fintype.card V) targets)
    rfl (by omega) hND hR hSmall hfixed
  calc
    (keyBadSetOn (V := V) k targets).card *
        2 ^ keyExponent r (Fintype.card V) ≤
      (KeyUnion.badUnion
        (FixedSeedBad (V := V) (k := k) (N := Fintype.card V) targets)).card *
          2 ^ keyExponent r (Fintype.card V) :=
      Nat.mul_le_mul_right _ (Finset.card_le_card hcover)
    _ ≤ Fintype.card (SimpleGraph V) := hstructural

/-- **ACDFM key lemma (finite-host form).**  For every finite labelled host,
the set of graphs which are simultaneously Ramsey-bad for the target vector
and satisfy the strong induction event has the exact denominator-cleared
cardinality saving `2^(N^2/r^100)`. -/
theorem acdfm_key_lemma_on
    {r k : ℕ} {order : Fin r → ℕ}
    (targets : Events.TargetVector r order)
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hord : ∀ i, order i ≤ k)
    (hscale : r ^ (300 * (k + Events.totalOrder order)) ≤ Fintype.card V) :
    (keyBadSetOn (V := V) k targets).card *
        2 ^ keyExponent r (Fintype.card V) ≤
      Fintype.card (SimpleGraph V) := by
  classical
  by_cases hsmall : ∃ i, order i ≤ 1
  · obtain ⟨i, hi⟩ := hsmall
    exact keyBadSetOn_card_mul_pow_le_of_order_le_one
      (D := keyExponent r (Fintype.card V)) i hi
  · have horder : ∀ i, 2 ≤ order i := by
      intro i
      by_contra hi
      exact hsmall ⟨i, by omega⟩
    exact acdfm_key_lemma_on_of_orders_ge_two targets hr hk horder hord hscale

/-- The `Fin N` specialization of `acdfm_key_lemma_on`. -/
theorem acdfm_key_lemma
    {r k N : ℕ} {order : Fin r → ℕ}
    (targets : Events.TargetVector r order)
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (hord : ∀ i, order i ≤ k)
    (hscale : r ^ (300 * (k + Events.totalOrder order)) ≤ N) :
    (keyBadSet (N := N) k targets).card * 2 ^ keyExponent r N ≤
      Fintype.card (SimpleGraph (Fin N)) := by
  simpa [keyBadSet] using
    (acdfm_key_lemma_on (V := Fin N) targets hr hk hord (by simpa using hscale))

#print axioms acdfm_key_lemma_on

end FinalKeyLemma

end KeyLemma
end Erdos565
