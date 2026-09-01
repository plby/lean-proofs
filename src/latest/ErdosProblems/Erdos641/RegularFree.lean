/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos641.Construction

/-!
# Excluding 4-regular subgraphs from the JSS construction

The first half of the probabilistic argument counts dense vertex sets in
strict layer prefixes.  It reuses the generic coordinate-cylinder and PRS
analytic estimates from `Erdos182`.
-/

open Finset Fintype Filter
open scoped BigOperators

namespace Erdos641

open SimpleGraph
open Erdos182

noncomputable section

open Classical in
section

/-- A proposed edge, consisting of a coordinate and one possible value of
that coordinate. -/
@[ext]
structure JSSDemand (n : ℕ) where
  coord : JSSCoordinate n
  targetIndex : Fin (prsLayerSize n coord.targetLayer)
deriving DecidableEq, Fintype

/-- The target vertex of a proposed edge. -/
def jssDemandTarget {n : ℕ} (d : JSSDemand n) : JSSVertex n :=
  ⟨d.coord.targetLayer, d.targetIndex⟩

/-- The unordered edge represented by a demand. -/
def jssDemandEdge {n : ℕ} (d : JSSDemand n) : Sym2 (JSSVertex n) :=
  s(d.coord.source, jssDemandTarget d)

lemma jssDemandEdge_injective {n : ℕ} :
    Function.Injective (jssDemandEdge (n := n)) := by
  rintro ⟨dc, di⟩ ⟨ec, ei⟩ h
  rw [jssDemandEdge, jssDemandEdge, Sym2.eq_iff] at h
  rcases h with h | h
  · have hsrc : dc.source = ec.source := h.1
    have htgtLayer : dc.targetLayer = ec.targetLayer :=
      congrArg Sigma.fst h.2
    have hcoord : dc = ec := JSSCoordinate.ext hsrc htgtLayer
    subst ec
    have hindex : di = ei := by
      apply Fin.ext
      exact congrArg (fun z : JSSVertex n ↦ z.2.val) h.2
    subst ei
    rfl
  · have hdlt : dc.source.1 < dc.targetLayer := dc.isLt
    have helt : ec.source.1 < ec.targetLayer := ec.isLt
    have h1 : dc.source.1 = ec.targetLayer :=
      congrArg Sigma.fst h.1
    have h2 : dc.targetLayer = ec.source.1 :=
      congrArg Sigma.fst h.2
    have : dc.source.1 < dc.source.1 := by
      calc
        dc.source.1 < dc.targetLayer := hdlt
        _ = ec.source.1 := h2
        _ < ec.targetLayer := helt
        _ = dc.source.1 := h1.symm
    exact (lt_irrefl _ this).elim

lemma jssDemandEdge_mem_graph_iff {n : ℕ} (ω : JSSOutcome n)
    (hω : ω ∈ jssOutcomeSpace n) (d : JSSDemand n) :
    jssDemandEdge d ∈ (jssGraph ω hω).edgeFinset ↔
      ω d.coord (Finset.mem_univ _) = jssDemandTarget d := by
  classical
  rw [SimpleGraph.mem_edgeFinset]
  constructor
  · intro hd
    change (jssGraph ω hω).Adj d.coord.source (jssDemandTarget d) at hd
    rcases hd with ⟨c, hcs, hct⟩ | ⟨c, hct, hcs⟩
    · have hcsrc : c.source = d.coord.source := hcs
      have hclayer : c.targetLayer = d.coord.targetLayer := by
        have h := congrArg Sigma.fst hct
        change c.targetLayer = d.coord.targetLayer at h
        exact h
      have hc : c = d.coord := JSSCoordinate.ext hcsrc hclayer
      subst c
      rw [← jssTarget_eq_outcome ω hω]
      exact hct
    · have hcsource : c.source.1 = d.coord.targetLayer := by
        have h := congrArg Sigma.fst hct
        change c.source.1 = d.coord.targetLayer at h
        exact h
      have hctarget : c.targetLayer = d.coord.source.1 := by
        have h := congrArg Sigma.fst hcs
        change c.targetLayer = d.coord.source.1 at h
        exact h
      have hreverse : d.coord.targetLayer < d.coord.source.1 := by
        calc
          d.coord.targetLayer = c.source.1 := hcsource.symm
          _ < c.targetLayer := c.isLt
          _ = d.coord.source.1 := hctarget
      exact ((not_lt_of_ge (Nat.le_of_lt d.coord.isLt)) hreverse).elim
  · intro h
    change (jssGraph ω hω).Adj d.coord.source (jssDemandTarget d)
    have ht : jssTarget ω hω d.coord = jssDemandTarget d :=
      (jssTarget_eq_outcome ω hω d.coord).trans h
    exact Or.inl ⟨d.coord, rfl, ht⟩

/-- Potential edges with both endpoints in `S`. -/
def candidateJSSDemands {n : ℕ} (S : Finset (JSSVertex n)) :
    Finset (JSSDemand n) :=
  Finset.univ.filter fun d ↦
    d.coord.source ∈ S ∧ jssDemandTarget d ∈ S

@[simp] lemma mem_candidateJSSDemands {n : ℕ} {S : Finset (JSSVertex n)}
    {d : JSSDemand n} :
    d ∈ candidateJSSDemands S ↔
      d.coord.source ∈ S ∧ jssDemandTarget d ∈ S := by
  simp [candidateJSSDemands]

/-- A set of edge demands is compatible if no coordinate is assigned two
different targets. -/
def CompatibleJSSDemands {n : ℕ} (R : Finset (JSSDemand n)) : Prop :=
  Set.InjOn JSSDemand.coord (↑R : Set (JSSDemand n))

/-- Convert compatible proposed edges into a coordinate cylinder. -/
def coordinateDemandOfJSSDemands {n : ℕ} (default : JSSOutcome n)
    (R : Finset (JSSDemand n)) :
    CoordinateDemand (JSSCoordinate n) (JSSVertex n) where
  coords := R.image JSSDemand.coord
  value c := if h : ∃ d ∈ R, d.coord = c then
      jssDemandTarget (Classical.choose h)
    else default c (Finset.mem_univ c)

/-- Candidate demands actually selected by `ω`. -/
def realizedCandidateJSSDemands {n : ℕ} (ω : JSSOutcome n)
    (S : Finset (JSSVertex n)) : Finset (JSSDemand n) :=
  (candidateJSSDemands S).filter fun d ↦
    ω d.coord (Finset.mem_univ _) = jssDemandTarget d

@[simp] lemma mem_realizedCandidateJSSDemands {n : ℕ} {ω : JSSOutcome n}
    {S : Finset (JSSVertex n)} {d : JSSDemand n} :
    d ∈ realizedCandidateJSSDemands ω S ↔
      d ∈ candidateJSSDemands S ∧
        ω d.coord (Finset.mem_univ _) = jssDemandTarget d := by
  simp [realizedCandidateJSSDemands]

lemma compatible_of_subset_realizedJSSDemands {n : ℕ} {ω : JSSOutcome n}
    {S : Finset (JSSVertex n)} {R : Finset (JSSDemand n)}
    (hR : R ⊆ realizedCandidateJSSDemands ω S) :
    CompatibleJSSDemands R := by
  intro d hd e he hcoord
  have hd' := (mem_realizedCandidateJSSDemands.mp (hR hd)).2
  have he' := (mem_realizedCandidateJSSDemands.mp (hR he)).2
  rcases d with ⟨dc, di⟩
  rcases e with ⟨ec, ei⟩
  dsimp only at hcoord ⊢
  subst ec
  have ht : jssDemandTarget (⟨dc, di⟩ : JSSDemand n) =
      jssDemandTarget ⟨dc, ei⟩ := hd'.symm.trans he'
  have hi : di = ei := by
    apply Fin.ext
    exact congrArg (fun z : JSSVertex n ↦ z.2.val) ht
  subst ei
  rfl

lemma mem_coordinateDemand_outcomes_of_subset_realizedJSS
    {n : ℕ} (ω default : JSSOutcome n) (hω : ω ∈ jssOutcomeSpace n)
    {S : Finset (JSSVertex n)} {R : Finset (JSSDemand n)}
    (hR : R ⊆ realizedCandidateJSSDemands ω S) :
    ω ∈ (coordinateDemandOfJSSDemands default R).outcomes jssAllowed := by
  classical
  rw [CoordinateDemand.outcomes, mem_fixedChoiceSpace]
  constructor
  · intro c hc
    obtain ⟨d, hdR, hdc⟩ := Finset.mem_image.mp hc
    have hex : ∃ e ∈ R, e.coord = c := ⟨d, hdR, hdc⟩
    change ω c (Finset.mem_univ _) =
      (if h : ∃ e ∈ R, e.coord = c then
        jssDemandTarget (Classical.choose h) else default c (Finset.mem_univ _))
    rw [dif_pos hex]
    have heSpec := Classical.choose_spec hex
    have hcomp := compatible_of_subset_realizedJSSDemands hR
    have hed : Classical.choose hex = d :=
      hcomp heSpec.1 hdR (heSpec.2.trans hdc.symm)
    rw [hed, ← hdc]
    exact (mem_realizedCandidateJSSDemands.mp (hR hdR)).2
  · intro c _hc
    exact (mem_jssOutcomeSpace.mp hω) c

/-- Ambient edges of `G` internal to `S`. -/
def internalJSSEdges {n : ℕ} (G : SimpleGraph (JSSVertex n))
    (S : Finset (JSSVertex n)) : Finset (Sym2 (JSSVertex n)) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S

lemma card_internalJSSEdges {n : ℕ} (G : SimpleGraph (JSSVertex n))
    (S : Finset (JSSVertex n)) :
    (internalJSSEdges G S).card =
      (G.induce (S : Set (JSSVertex n))).edgeFinset.card := by
  classical
  simpa [internalJSSEdges] using G.card_filter_edgeFinset_toFinset_subset S

lemma image_realizedCandidateJSSDemands {n : ℕ} (ω : JSSOutcome n)
    (hω : ω ∈ jssOutcomeSpace n) (S : Finset (JSSVertex n)) :
    (realizedCandidateJSSDemands ω S).image jssDemandEdge =
      internalJSSEdges (jssGraph ω hω) S := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hdS, hdreal⟩ := mem_realizedCandidateJSSDemands.mp hd
    apply Finset.mem_filter.mpr
    constructor
    · rw [jssDemandEdge_mem_graph_iff]
      exact hdreal
    · intro z hz
      have hz' : z = d.coord.source ∨ z = jssDemandTarget d := by
        simpa [jssDemandEdge, Sym2.mem_toFinset] using hz
      rcases hz' with rfl | rfl
      · exact (mem_candidateJSSDemands.mp hdS).1
      · exact (mem_candidateJSSDemands.mp hdS).2
  · intro he
    obtain ⟨heG, heS⟩ := Finset.mem_filter.mp he
    rw [SimpleGraph.mem_edgeFinset] at heG
    refine Sym2.inductionOn e (fun a b heG heS ↦ ?_) heG heS
    change (jssGraph ω hω).Adj a b at heG
    rcases heG with ⟨c, hcs, hct⟩ | ⟨c, hct, hcs⟩
    · let d : JSSDemand n := ⟨c, jssTargetIndex ω hω c⟩
      apply Finset.mem_image.mpr
      refine ⟨d, ?_, ?_⟩
      · rw [mem_realizedCandidateJSSDemands]
        constructor
        · rw [mem_candidateJSSDemands]
          constructor
          · apply heS
            change c.source ∈ s(a, b).toFinset
            rw [hcs]
            simp
          · apply heS
            change jssTarget ω hω c ∈ s(a, b).toFinset
            rw [hct]
            simp
        · simp [d, jssDemandTarget]
      · change s(c.source, jssTarget ω hω c) = s(a, b)
        rw [hcs, hct]
    · let d : JSSDemand n := ⟨c, jssTargetIndex ω hω c⟩
      apply Finset.mem_image.mpr
      refine ⟨d, ?_, ?_⟩
      · rw [mem_realizedCandidateJSSDemands]
        constructor
        · rw [mem_candidateJSSDemands]
          constructor
          · apply heS
            change c.source ∈ s(a, b).toFinset
            rw [hct]
            simp
          · apply heS
            change jssTarget ω hω c ∈ s(a, b).toFinset
            rw [hcs]
            simp
        · simp [d, jssDemandTarget]
      · change s(c.source, jssTarget ω hω c) = s(a, b)
        rw [hct, hcs]
        exact Sym2.eq_swap

lemma card_realizedCandidateJSSDemands {n : ℕ} (ω : JSSOutcome n)
    (hω : ω ∈ jssOutcomeSpace n) (S : Finset (JSSVertex n)) :
    (realizedCandidateJSSDemands ω S).card =
      ((jssGraph ω hω).induce (S : Set (JSSVertex n))).edgeFinset.card := by
  classical
  rw [← card_internalJSSEdges, ← image_realizedCandidateJSSDemands ω hω S,
    Finset.card_image_of_injective _ jssDemandEdge_injective]

/-- All compatible `r`-edge prescriptions supported on `S`. -/
def candidateJSSCoordinateDemands {n : ℕ} (default : JSSOutcome n)
    (S : Finset (JSSVertex n)) (r : ℕ) :
    Finset (CoordinateDemand (JSSCoordinate n) (JSSVertex n)) :=
  (((candidateJSSDemands S).powersetCard r).filter CompatibleJSSDemands).image
    (coordinateDemandOfJSSDemands default)

/-- Vertices in layers strictly before `i`. -/
def jssPrefix (n : ℕ) (i : Fin (prsLayerCount n)) : Finset (JSSVertex n) :=
  Finset.univ.filter fun v ↦ v.1 < i

@[simp] lemma mem_jssPrefix {n : ℕ} {i : Fin (prsLayerCount n)}
    {v : JSSVertex n} : v ∈ jssPrefix n i ↔ v.1 < i := by
  simp [jssPrefix]

/-- Empty outside the prefix; this supplies the target-size denominator. -/
def prefixJSSCoordinateDemands {n : ℕ} (default : JSSOutcome n)
    (i : Fin (prsLayerCount n)) (r : ℕ) (S : Finset (JSSVertex n)) :
    Finset (CoordinateDemand (JSSCoordinate n) (JSSVertex n)) :=
  if S ⊆ jssPrefix n i then candidateJSSCoordinateDemands default S r else ∅

/-- A potential edge internal to `S`, as an edge of the complete graph on
the subtype `S`. -/
def candidateJSSDemandEdgeIn {n : ℕ} (S : Finset (JSSVertex n))
    (d : {d : JSSDemand n // d ∈ candidateJSSDemands S}) :
    (⊤ : SimpleGraph (S : Set (JSSVertex n))).edgeFinset := by
  let u : (S : Set (JSSVertex n)) :=
    ⟨d.1.coord.source, (mem_candidateJSSDemands.mp d.2).1⟩
  let v : (S : Set (JSSVertex n)) :=
    ⟨jssDemandTarget d.1, (mem_candidateJSSDemands.mp d.2).2⟩
  refine ⟨s(u, v), ?_⟩
  simp only [SimpleGraph.mem_edgeFinset]
  intro huv
  have hbad := congrArg (fun z : (S : Set (JSSVertex n)) ↦ z.1.1) huv
  exact (ne_of_lt d.1.coord.isLt) (by simpa [u, v, jssDemandTarget] using hbad)

lemma candidateJSSDemandEdgeIn_injective {n : ℕ}
    (S : Finset (JSSVertex n)) :
    Function.Injective (candidateJSSDemandEdgeIn S) := by
  intro d e hde
  apply Subtype.ext
  apply jssDemandEdge_injective
  have h := congrArg (fun z :
      (⊤ : SimpleGraph (S : Set (JSSVertex n))).edgeFinset ↦
        Sym2.map (Function.Embedding.subtype (fun x ↦ x ∈ S)) z.1) hde
  simpa [candidateJSSDemandEdgeIn, jssDemandEdge] using h

lemma card_candidateJSSDemands_le_choose {n : ℕ}
    (S : Finset (JSSVertex n)) :
    (candidateJSSDemands S).card ≤ S.card.choose 2 := by
  classical
  have hinj := Fintype.card_le_of_injective (candidateJSSDemandEdgeIn S)
    (candidateJSSDemandEdgeIn_injective S)
  calc
    (candidateJSSDemands S).card =
        Fintype.card {d // d ∈ candidateJSSDemands S} :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card
        ((⊤ : SimpleGraph (S : Set (JSSVertex n))).edgeFinset) := hinj
    _ = ((⊤ : SimpleGraph (S : Set (JSSVertex n))).edgeFinset).card :=
      Fintype.card_coe _
    _ ≤ (Fintype.card (S : Set (JSSVertex n))).choose 2 :=
      SimpleGraph.card_edgeFinset_le_card_choose_two
    _ = S.card.choose 2 := by simp

lemma card_candidateJSSCoordinateDemands_le_choose {n : ℕ}
    (default : JSSOutcome n) (S : Finset (JSSVertex n)) (r : ℕ) :
    (candidateJSSCoordinateDemands default S r).card ≤
      (S.card.choose 2).choose r := by
  classical
  calc
    (candidateJSSCoordinateDemands default S r).card ≤
        (((candidateJSSDemands S).powersetCard r).filter
          CompatibleJSSDemands).card := Finset.card_image_le
    _ ≤ ((candidateJSSDemands S).powersetCard r).card := Finset.card_filter_le _ _
    _ = (candidateJSSDemands S).card.choose r := Finset.card_powersetCard _ _
    _ ≤ (S.card.choose 2).choose r :=
      Nat.choose_le_choose r (card_candidateJSSDemands_le_choose S)

lemma coords_card_of_mem_candidateJSSCoordinateDemands {n : ℕ}
    (default : JSSOutcome n) (S : Finset (JSSVertex n)) (r : ℕ)
    {d : CoordinateDemand (JSSCoordinate n) (JSSVertex n)}
    (hd : d ∈ candidateJSSCoordinateDemands default S r) :
    d.coords.card = r := by
  classical
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hd
  obtain ⟨hRpowerset, hRcompatible⟩ := Finset.mem_filter.mp hR
  rw [coordinateDemandOfJSSDemands]
  have himage : (R.image JSSDemand.coord).card = R.card :=
    Finset.card_image_iff.mpr hRcompatible
  rw [himage]
  exact (Finset.mem_powersetCard.mp hRpowerset).2

lemma coords_card_of_mem_prefixJSSCoordinateDemands {n : ℕ}
    (default : JSSOutcome n) (i : Fin (prsLayerCount n))
    (S : Finset (JSSVertex n)) (r : ℕ)
    {d : CoordinateDemand (JSSCoordinate n) (JSSVertex n)}
    (hd : d ∈ prefixJSSCoordinateDemands default i r S) :
    d.coords.card = r := by
  classical
  by_cases hS : S ⊆ jssPrefix n i
  · exact coords_card_of_mem_candidateJSSCoordinateDemands default S r
      (by simpa [prefixJSSCoordinateDemands, hS] using hd)
  · simp [prefixJSSCoordinateDemands, hS] at hd

/-- Every target layer in a prefix demand has size at least the last layer
of that prefix. -/
lemma allowed_card_lower_of_mem_prefixJSSCoordinateDemands {n : ℕ}
    (default : JSSOutcome n) (i : Fin (prsLayerCount n))
    (S : Finset (JSSVertex n)) (r B : ℕ)
    (hmono : ∀ a, a < i → B ≤ prsLayerSize n a)
    {d : CoordinateDemand (JSSCoordinate n) (JSSVertex n)}
    (hd : d ∈ prefixJSSCoordinateDemands default i r S)
    {c : JSSCoordinate n} (hc : c ∈ d.coords) :
    B ≤ (jssAllowed c).card := by
  classical
  have hS : S ⊆ jssPrefix n i := by
    by_contra hnot
    simp [prefixJSSCoordinateDemands, hnot] at hd
  have hd' : d ∈ candidateJSSCoordinateDemands default S r := by
    simpa [prefixJSSCoordinateDemands, hS] using hd
  obtain ⟨R, hR, hRd⟩ := Finset.mem_image.mp hd'
  subst d
  change c ∈ R.image JSSDemand.coord at hc
  obtain ⟨e, heR, hec⟩ := Finset.mem_image.mp hc
  have heCandidate : e ∈ candidateJSSDemands S :=
    (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hR).1).1 heR
  have htS : jssDemandTarget e ∈ S :=
    (mem_candidateJSSDemands.mp heCandidate).2
  have htPrefix : (jssDemandTarget e).1 < i :=
    mem_jssPrefix.mp (hS htS)
  have htarget : c.targetLayer = e.coord.targetLayer := by
    rw [← hec]
  rw [card_jssAllowed, htarget]
  exact hmono e.coord.targetLayer (by simpa [jssDemandTarget] using htPrefix)

end

end

end Erdos641
