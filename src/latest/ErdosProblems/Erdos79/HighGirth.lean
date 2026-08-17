/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos79.Core
import ErdosProblems.Erdos79.Uniform
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Dense finite graphs of arbitrarily large girth

This file proves the elementary finite first-moment construction used in the proof of
Erdős Problem 79.  Edges of the complete graph on `Fin L` receive independent uniform labels
in `Fin L`, and precisely the labels below `24` are retained.  A finite averaging argument gives
an outcome with more retained edges than short cycles plus `6 * L`.  We then remove one edge from
every surviving short cycle, using `SimpleGraph.killCopies`.
-/

open scoped SimpleGraph
open Finset Function

noncomputable section

namespace Erdos79

private theorem card_cycleGraph_edges {l : ℕ} (hl : 3 ≤ l) :
    #(SimpleGraph.cycleGraph l).edgeFinset = l := by
  have hdeg : ∀ v : Fin l, (SimpleGraph.cycleGraph l).degree v = 2 := by
    obtain ⟨n, hn⟩ : ∃ n, l = n + 3 := ⟨l - 3, by omega⟩
    subst l
    exact fun v ↦ SimpleGraph.cycleGraph_degree_three_le (n := n) (v := v)
  have hsum := (SimpleGraph.cycleGraph l).sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hsum
  have : 2 * l = 2 * #(SimpleGraph.cycleGraph l).edgeFinset := by
    simpa [mul_comm] using hsum
  omega

private abbrev CompleteEdge (L : ℕ) := (⊤ : SimpleGraph (Fin L)).edgeSet

private abbrev EdgeOutcome (L : ℕ) := Uniform.Outcome (CompleteEdge L) L

/-- Retain precisely the complete-graph edges whose uniform label is below `24`. -/
private def sampledGraph {L : ℕ} (w : EdgeOutcome L) : SimpleGraph (Fin L) :=
  SimpleGraph.fromEdgeSet
    {e | ∃ he : e ∈ (⊤ : SimpleGraph (Fin L)).edgeSet, (w ⟨e, he⟩ : ℕ) < 24}

private theorem mem_sampledGraph_edgeSet {L : ℕ} {w : EdgeOutcome L} {e : Sym2 (Fin L)} :
    e ∈ (sampledGraph w).edgeSet ↔
      ∃ he : e ∈ (⊤ : SimpleGraph (Fin L)).edgeSet, (w ⟨e, he⟩ : ℕ) < 24 := by
  rw [sampledGraph, SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · exact fun he ↦ he.1
  · intro h
    exact ⟨h, by simpa using h.choose⟩

private theorem sampledGraph_adj_iff {L : ℕ} {w : EdgeOutcome L} {u v : Fin L} :
    (sampledGraph w).Adj u v ↔
      ∃ huv : u ≠ v, (w ⟨s(u, v), by simpa using huv⟩ : ℕ) < 24 := by
  rw [← SimpleGraph.mem_edgeSet, mem_sampledGraph_edgeSet]
  simp only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]

private noncomputable instance sampledGraph.edgeSetFintype {L : ℕ} (w : EdgeOutcome L) :
    Fintype (sampledGraph w).edgeSet := Fintype.ofFinite _

private theorem sampledGraph_edgeCard {L : ℕ} (w : EdgeOutcome L) :
    #(sampledGraph w).edgeFinset =
      #((Finset.univ : Finset (CompleteEdge L)).filter fun e ↦ (w e : ℕ) < 24) := by
  classical
  rw [SimpleGraph.edgeFinset_card]
  let f : (sampledGraph w).edgeSet →
      {e : CompleteEdge L // (w e : ℕ) < 24} := fun e ↦ by
    have he := mem_sampledGraph_edgeSet.mp e.2
    exact ⟨⟨e.1, he.choose⟩, he.choose_spec⟩
  have hf : Injective f := by
    intro e e' h
    apply Subtype.ext
    exact congrArg (fun x ↦ x.1.1) h
  have hsurj : Surjective f := by
    rintro ⟨⟨e, he⟩, hw⟩
    refine ⟨⟨e, mem_sampledGraph_edgeSet.mpr ⟨he, hw⟩⟩, ?_⟩
    rfl
  calc
    Fintype.card (sampledGraph w).edgeSet =
        Fintype.card {e : CompleteEdge L // (w e : ℕ) < 24} :=
      Fintype.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)
    _ = Fintype.card
        ↑((Finset.univ : Finset (CompleteEdge L)).filter fun e ↦ (w e : ℕ) < 24) := by
      apply Fintype.card_congr
      exact
        { toFun := fun e ↦ ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩⟩
          invFun := fun e ↦ ⟨e.1, (Finset.mem_filter.mp e.2).2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    _ = #((Finset.univ : Finset (CompleteEdge L)).filter fun e ↦ (w e : ℕ) < 24) :=
      Fintype.card_coe _

private def completeCycleCopy {l L : ℕ} (f : Fin l ↪ Fin L) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph l) (⊤ : SimpleGraph (Fin L)) where
  toHom :=
    { toFun := f
      map_rel' := fun hab ↦ by simpa using f.injective.ne hab.ne }
  injective' := f.injective

/-- The complete-graph edges which must be retained in order for `f` to give a labelled copy of
the `l`-cycle. -/
private def cycleSupport {l L : ℕ} (f : Fin l ↪ Fin L) : Finset (CompleteEdge L) :=
  Finset.univ.map (completeCycleCopy f).mapEdgeSet

private theorem card_cycleSupport {l L : ℕ} (hl : 3 ≤ l) (f : Fin l ↪ Fin L) :
    #(cycleSupport f) = l := by
  classical
  rw [cycleSupport, Finset.card_map, Finset.card_univ,
    SimpleGraph.card_edgeSet, card_cycleGraph_edges hl]

/-- Number of injective labelled `l`-cycles whose required edges all survive in the outcome. -/
private abbrev CycleCandidates {L : ℕ} (w : EdgeOutcome L) (l : ℕ) :=
  {f : Fin l ↪ Fin L // f ∈
    (Finset.univ.filter fun f ↦
      w ∈ Uniform.thresholdCylinder L 24 (cycleSupport f))}

private def cycleCandidateCount {L : ℕ} (w : EdgeOutcome L) (l : ℕ) : ℕ :=
  Nat.card (CycleCandidates w l)

private theorem copyEmbedding_mem_candidates {L l : ℕ} (w : EdgeOutcome L)
    (c : SimpleGraph.Copy (SimpleGraph.cycleGraph l) (sampledGraph w)) :
    c.toEmbedding ∈ (Finset.univ.filter fun f : Fin l ↪ Fin L ↦
      w ∈ Uniform.thresholdCylinder L 24 (cycleSupport f)) := by
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, Uniform.mem_thresholdCylinder.mpr ?_⟩
  intro e he
  rw [cycleSupport, Finset.mem_map] at he
  obtain ⟨e', -, rfl⟩ := he
  have hmem := c.toHom.map_mem_edgeSet e'.2
  have hlow := (mem_sampledGraph_edgeSet.mp hmem).choose_spec
  simpa [completeCycleCopy, SimpleGraph.Copy.mapEdgeSet,
    SimpleGraph.Hom.mapEdgeSet, SimpleGraph.Copy.toEmbedding] using hlow

private def copyToCandidate {L l : ℕ} (w : EdgeOutcome L) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph l) (sampledGraph w) →
      CycleCandidates w l :=
  fun c ↦ ⟨c.toEmbedding, copyEmbedding_mem_candidates w c⟩

private theorem copyToCandidate_injective {L l : ℕ} (w : EdgeOutcome L) :
    Injective (copyToCandidate (l := l) w) := by
  intro c c' h
  apply SimpleGraph.Copy.ext
  intro x
  exact congrArg (fun z ↦ z.1.1 x) h

private theorem labelledCopyCount_eq_natCard {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    G.labelledCopyCount H = Nat.card (SimpleGraph.Copy H G) := by
  classical
  unfold SimpleGraph.labelledCopyCount
  exact Nat.card_eq_fintype_card.symm

private theorem labelledCopyCount_cycle_le_candidateCount {L l : ℕ} (w : EdgeOutcome L) :
    (sampledGraph w).labelledCopyCount (SimpleGraph.cycleGraph l) ≤
      cycleCandidateCount w l := by
  rw [labelledCopyCount_eq_natCard]
  exact Nat.card_le_card_of_injective (copyToCandidate (l := l) w)
    (copyToCandidate_injective w)

private theorem edgeFinset_card_eq_natCard {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] : #G.edgeFinset = Nat.card G.edgeSet := by
  rw [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]

private theorem card_completeEdge (L : ℕ) :
    Fintype.card (CompleteEdge L) = L.choose 2 := by
  rw [← SimpleGraph.edgeFinset_card,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

private theorem sum_sampledGraph_edgeCard {L : ℕ} (hL : 24 ≤ L) :
    (∑ w : EdgeOutcome L, #(sampledGraph w).edgeFinset) =
      Fintype.card (CompleteEdge L) *
        (24 * L ^ (Fintype.card (CompleteEdge L) - 1)) := by
  classical
  let B : CompleteEdge L → Finset (EdgeOutcome L) := fun e ↦
    Uniform.thresholdCylinder L 24 {e}
  have hdouble := Uniform.sum_card_eq_sum_memberships B
  calc
    (∑ w : EdgeOutcome L, #(sampledGraph w).edgeFinset) =
        ∑ w : EdgeOutcome L,
          #((Finset.univ : Finset (CompleteEdge L)).filter fun e ↦ (w e : ℕ) < 24) := by
      apply Finset.sum_congr rfl
      intro w _
      exact sampledGraph_edgeCard w
    _ = ∑ w : EdgeOutcome L,
          #((Finset.univ : Finset (CompleteEdge L)).filter fun e ↦ w ∈ B e) := by
      apply Finset.sum_congr rfl
      intro w _
      apply congrArg Finset.card
      ext e
      simp [B, Uniform.mem_thresholdCylinder]
    _ = ∑ e : CompleteEdge L, #(B e) := hdouble.symm
    _ = Fintype.card (CompleteEdge L) *
        (24 * L ^ (Fintype.card (CompleteEdge L) - 1)) := by
      simp [B, Uniform.card_thresholdCylinder hL]

private theorem card_embedding_le_functions (l L : ℕ) :
    Fintype.card (Fin l ↪ Fin L) ≤ L ^ l := by
  classical
  have h := Fintype.card_le_of_injective
    (fun f : Fin l ↪ Fin L ↦ (f : Fin l → Fin L))
    (fun _ _ hff' ↦ DFunLike.coe_injective hff')
  simpa [Fintype.card_fun] using h

private theorem sum_cycleCandidateCount_le {L l : ℕ} (hL : 24 ≤ L) (hl : 3 ≤ l) :
    (∑ w : EdgeOutcome L, cycleCandidateCount w l) ≤
      24 ^ l * L ^ Fintype.card (CompleteEdge L) := by
  classical
  cases isEmpty_or_nonempty (Fin l ↪ Fin L) with
  | inl hempty => simp [cycleCandidateCount, CycleCandidates]
  | inr hnempty =>
      let B : (Fin l ↪ Fin L) → Finset (EdgeOutcome L) := fun f ↦
        Uniform.thresholdCylinder L 24 (cycleSupport f)
      have hdouble := Uniform.sum_card_eq_sum_memberships B
      let f₀ : Fin l ↪ Fin L := Classical.choice hnempty
      have hlM : l ≤ Fintype.card (CompleteEdge L) := by
        rw [← card_cycleSupport hl f₀]
        exact Finset.card_le_univ _
      calc
        (∑ w : EdgeOutcome L, cycleCandidateCount w l) =
            ∑ w : EdgeOutcome L,
              #((Finset.univ : Finset (Fin l ↪ Fin L)).filter fun f ↦ w ∈ B f) := by
          apply Finset.sum_congr rfl
          intro w _
          change Nat.card
              ↑((Finset.univ : Finset (Fin l ↪ Fin L)).filter fun f ↦ w ∈ B f) =
            #((Finset.univ : Finset (Fin l ↪ Fin L)).filter fun f ↦ w ∈ B f)
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
        _ = ∑ f : Fin l ↪ Fin L, #(B f) := hdouble.symm
        _ = Fintype.card (Fin l ↪ Fin L) *
            (24 ^ l * L ^ (Fintype.card (CompleteEdge L) - l)) := by
          simp [B, Uniform.card_thresholdCylinder hL, card_cycleSupport hl]
        _ ≤ L ^ l * (24 ^ l * L ^ (Fintype.card (CompleteEdge L) - l)) :=
          Nat.mul_le_mul_right _ (card_embedding_le_functions l L)
        _ = 24 ^ l * L ^ Fintype.card (CompleteEdge L) := by
          calc
            L ^ l * (24 ^ l * L ^ (Fintype.card (CompleteEdge L) - l)) =
                24 ^ l * (L ^ l * L ^ (Fintype.card (CompleteEdge L) - l)) := by
              ac_rfl
            _ = 24 ^ l * L ^ Fintype.card (CompleteEdge L) := by
              rw [← pow_add, Nat.add_sub_of_le hlM]

private def shortCycleBudget (g : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (g - 3), 24 ^ (i + 3)

private def shortCycleCount {L : ℕ} (w : EdgeOutcome L) (g : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (g - 3), cycleCandidateCount w (i + 3)

private theorem sum_shortCycleCount_le {L g : ℕ} (hL : 24 ≤ L) :
    (∑ w : EdgeOutcome L, shortCycleCount w g) ≤
      shortCycleBudget g * L ^ Fintype.card (CompleteEdge L) := by
  classical
  calc
    (∑ w : EdgeOutcome L, shortCycleCount w g) =
        ∑ i ∈ Finset.range (g - 3), ∑ w : EdgeOutcome L, cycleCandidateCount w (i + 3) := by
      simp only [shortCycleCount]
      rw [Finset.sum_comm]
    _ ≤ ∑ i ∈ Finset.range (g - 3),
        24 ^ (i + 3) * L ^ Fintype.card (CompleteEdge L) := by
      apply Finset.sum_le_sum
      intro i _
      exact sum_cycleCandidateCount_le hL (by omega)
    _ = shortCycleBudget g * L ^ Fintype.card (CompleteEdge L) := by
      simp [shortCycleBudget, Finset.sum_mul]

private theorem exists_goodSample (g : ℕ) :
    let B := shortCycleBudget g
    let L := B + 25
    ∃ w : EdgeOutcome L,
      shortCycleCount w g + 6 * L < #(sampledGraph w).edgeFinset := by
  classical
  dsimp only
  let B := shortCycleBudget g
  let L := B + 25
  let M := Fintype.card (CompleteEdge L)
  have hL : L = B + 25 := rfl
  have hL24 : 24 ≤ L := by omega
  have hMcard : M = L.choose 2 := card_completeEdge L
  have htwoM : 2 * M = L * (L - 1) := by
    rw [mul_comm, hMcard, Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self L)]
  have hMpos : 0 < M := by
    have hLpos : 0 < L * (L - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hpow : L ^ M = L ^ (M - 1) * L := by
    conv_lhs => rw [show M = (M - 1) + 1 by omega]
    exact pow_succ _ _
  have hcoef : B + 6 * L < 12 * (L - 1) := by
    omega
  have hfactor : 0 < L ^ (M - 1) * L :=
    Nat.mul_pos (pow_pos (by omega) (M - 1)) (by omega)
  have hmul := Nat.mul_lt_mul_of_pos_right hcoef hfactor
  have harith :
      B * L ^ M + (6 * L) * L ^ M < M * (24 * L ^ (M - 1)) := by
    calc
      B * L ^ M + (6 * L) * L ^ M =
          (B + 6 * L) * (L ^ (M - 1) * L) := by rw [hpow]; ring
      _ < 12 * (L - 1) * (L ^ (M - 1) * L) := hmul
      _ = 12 * (L * (L - 1)) * L ^ (M - 1) := by ring
      _ = 12 * (2 * M) * L ^ (M - 1) := by rw [← htwoM]
      _ = M * (24 * L ^ (M - 1)) := by ring
  have hedge := sum_sampledGraph_edgeCard hL24
  have hcycle := sum_shortCycleCount_le (g := g) hL24
  have hstrict :
      (∑ w : EdgeOutcome L, shortCycleCount w g) +
          ∑ _w : EdgeOutcome L, 6 * L <
        ∑ w : EdgeOutcome L, #(sampledGraph w).edgeFinset := by
    calc
      (∑ w : EdgeOutcome L, shortCycleCount w g) +
            ∑ _w : EdgeOutcome L, 6 * L ≤
          B * L ^ M + (6 * L) * L ^ M := by
        apply Nat.add_le_add hcycle
        simp [M, mul_comm, mul_assoc]
      _ < M * (24 * L ^ (M - 1)) := harith
      _ = ∑ w : EdgeOutcome L, #(sampledGraph w).edgeFinset := by
        simpa [M] using hedge.symm
  by_contra hnone
  push Not at hnone
  have hle :
      (∑ w : EdgeOutcome L, #(sampledGraph w).edgeFinset) ≤
        ∑ w : EdgeOutcome L, (shortCycleCount w g + 6 * L) :=
    Finset.sum_le_sum fun w _ ↦ hnone w
  rw [Finset.sum_add_distrib] at hle
  omega

private theorem labelledCopyCount_mono {V W : Type*} [Fintype V] [Fintype W]
    {G G' : SimpleGraph V} (h : G' ≤ G) (H : SimpleGraph W) :
    G'.labelledCopyCount H ≤ G.labelledCopyCount H := by
  classical
  unfold SimpleGraph.labelledCopyCount
  apply Fintype.card_le_of_injective
    (fun f : SimpleGraph.Copy H G' =>
      (SimpleGraph.Copy.ofLE G' G h).comp f)
  intro f f' hff'
  apply SimpleGraph.Copy.ext
  intro x
  have := DFunLike.congr_fun hff' x
  simpa using this

/-- Starting with `G`, successively remove one edge from every copy of the cycle graphs of
lengths `3, 4, ..., n + 2`. -/
private noncomputable def killShortCycles {V : Type*} (G : SimpleGraph V) :
    ℕ → SimpleGraph V
  | 0 => G
  | n + 1 => (killShortCycles G n).killCopies (SimpleGraph.cycleGraph (n + 3))

private theorem killShortCycles_le {V : Type*} (G : SimpleGraph V) (n : ℕ) :
    killShortCycles G n ≤ G := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact SimpleGraph.killCopies_le_left.trans ih

private noncomputable instance killShortCycles.edgeSetFintype {V : Type*}
    [Finite V] (G : SimpleGraph V) (n : ℕ) :
    Fintype (killShortCycles G n).edgeSet := Fintype.ofFinite _

private theorem free_mono_right {V W : Type*} {H : SimpleGraph W} {G G' : SimpleGraph V}
    (hfree : H.Free G) (hle : G' ≤ G) : H.Free G' := by
  intro hcopy
  exact hfree (hcopy.trans (SimpleGraph.IsContained.of_le hle))

private theorem killShortCycles_free {V : Type*} (G : SimpleGraph V) {i n : ℕ}
    (hi : i < n) :
    (SimpleGraph.cycleGraph (i + 3)).Free (killShortCycles G n) := by
  induction n with
  | zero => simp at hi
  | succ n ih =>
      by_cases hin : i = n
      · subst i
        exact SimpleGraph.free_killCopies (by
          intro hbot
          have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj
              ⟨0, by omega⟩ ⟨1, by omega⟩ := by
            simp [SimpleGraph.cycleGraph_adj']
          have : ¬ (SimpleGraph.cycleGraph (n + 3)).Adj
              ⟨0, by omega⟩ ⟨1, by omega⟩ := by simp [hbot]
          exact this hadj)
      · have hil : i < n := by omega
        exact free_mono_right (ih hil) SimpleGraph.killCopies_le_left

private theorem edgeCard_le_killShortCycles_add {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet] (n : ℕ) :
    #G.edgeFinset ≤ #(killShortCycles G n).edgeFinset +
      ∑ i ∈ Finset.range n, G.labelledCopyCount (SimpleGraph.cycleGraph (i + 3)) := by
  classical
  induction n with
  | zero =>
      rw [show Finset.range 0 = ∅ by rfl, Finset.sum_empty, add_zero]
      apply Nat.le_of_eq
      apply congrArg Finset.card
      ext e
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
      rfl
  | succ n ih =>
      let P := killShortCycles G n
      let C := SimpleGraph.cycleGraph (n + 3)
      have hkill : #P.edgeFinset ≤ #(P.killCopies C).edgeFinset + P.copyCount C :=
        SimpleGraph.le_card_edgeFinset_killCopies_add_copyCount
      have hcopy : P.copyCount C ≤ G.labelledCopyCount C :=
        (SimpleGraph.copyCount_le_labelledCopyCount).trans
          (labelledCopyCount_mono (killShortCycles_le G n) C)
      dsimp [P, C] at hkill hcopy
      have hsucc : #(killShortCycles G (n + 1)).edgeFinset =
          #((killShortCycles G n).killCopies
            (SimpleGraph.cycleGraph (n + 3))).edgeFinset := by
        apply congrArg Finset.card
        ext e
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset]
        rfl
      rw [hsucc, Finset.sum_range_succ]
      calc
        #G.edgeFinset ≤ #(killShortCycles G n).edgeFinset +
            ∑ i ∈ Finset.range n,
              G.labelledCopyCount (SimpleGraph.cycleGraph (i + 3)) := ih
        _ ≤ (#((killShortCycles G n).killCopies
              (SimpleGraph.cycleGraph (n + 3))).edgeFinset +
              (killShortCycles G n).copyCount (SimpleGraph.cycleGraph (n + 3))) +
            ∑ i ∈ Finset.range n,
              G.labelledCopyCount (SimpleGraph.cycleGraph (i + 3)) :=
          Nat.add_le_add_right hkill _
        _ ≤ (#((killShortCycles G n).killCopies
              (SimpleGraph.cycleGraph (n + 3))).edgeFinset +
              G.labelledCopyCount (SimpleGraph.cycleGraph (n + 3))) +
            ∑ i ∈ Finset.range n,
              G.labelledCopyCount (SimpleGraph.cycleGraph (i + 3)) := by omega
        _ = _ := by omega

private theorem egirth_killShortCycles {V : Type*} (G : SimpleGraph V) (g : ℕ) :
    (g : ℕ∞) ≤ (killShortCycles G (g - 3)).egirth := by
  rw [SimpleGraph.le_egirth]
  intro a w hw
  by_contra hnot
  have hwlt : w.length < g := by
    exact_mod_cast (not_le.mp hnot)
  have hthree : 3 ≤ w.length := hw.three_le_length
  have hi : w.length - 3 < g - 3 := by omega
  have hfree := killShortCycles_free G hi
  have hlen : w.length - 3 + 3 = w.length := by omega
  rw [hlen] at hfree
  apply hfree
  rw [SimpleGraph.cycleGraph_isContained_iff hthree]
  exact ⟨a, w, hw, rfl⟩

/-- For every prescribed lower bound on the girth, there is a finite graph with more than six
edges per vertex.  This is the dense high-girth input used in the resolution of Erdős Problem 79. -/
theorem exists_dense_highGirth (g : ℕ) :
    ∃ G : GraphCode,
      (g : ℕ∞) ≤ G.graph.egirth ∧ 6 * G.vertexCount < G.edgeCount := by
  classical
  let B := shortCycleBudget g
  let L := B + 25
  obtain ⟨w, hw⟩ := exists_goodSample g
  let Y := sampledGraph w
  let X := killShortCycles Y (g - 3)
  have hedge := edgeCard_le_killShortCycles_add Y (g - 3)
  have hcopies :
      (∑ i ∈ Finset.range (g - 3),
          Y.labelledCopyCount (SimpleGraph.cycleGraph (i + 3))) ≤
        shortCycleCount w g := by
    apply Finset.sum_le_sum
    intro i _
    exact labelledCopyCount_cycle_le_candidateCount w
  have hdense : 6 * L < #X.edgeFinset := by
    have hbound : #Y.edgeFinset ≤ #X.edgeFinset + shortCycleCount w g :=
      hedge.trans (Nat.add_le_add_left hcopies _)
    dsimp [Y] at hw hbound
    omega
  refine ⟨⟨L, X⟩, ?_, ?_⟩
  · exact egirth_killShortCycles Y g
  · have hnat : 6 * L < Nat.card X.edgeSet := by
      exact lt_of_lt_of_eq hdense (edgeFinset_card_eq_natCard X)
    change 6 * L < Nat.card X.edgeSet
    exact hnat

end Erdos79
