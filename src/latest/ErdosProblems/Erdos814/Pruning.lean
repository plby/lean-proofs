import ErdosProblems.Erdos814.Basic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith

/-!
# Erdős 814: the degree-`k` supply lemma

This file formalizes Lemma 2.2 of Sauermann's proof.  The graph is first replaced by an
edge-minimal spanning subgraph that still has minimum degree `k` and has acquired no new
degree-`k` vertices.  A finite red--blue construction then finds a large deletable red set.
-/

open scoped Sym2
open Finset SimpleGraph BigOperators

namespace Erdos814

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices of `A` having degree exactly `k` in `G[A]`. -/
def degreeEq (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) : Finset V :=
  A.filter fun v ↦ degreeOn G A v = k

@[simp] lemma mem_degreeEq {G : SimpleGraph V} [DecidableRel G.Adj]
    {A : Finset V} {k : ℕ} {v : V} :
    v ∈ degreeEq G A k ↔ v ∈ A ∧ degreeOn G A v = k := by
  simp [degreeEq]

private lemma degreeOn_deleteEdge_eq_of_ne
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {x y v : V} (hvx : v ≠ x) (hvy : v ≠ y) :
    degreeOn (G.deleteEdges ({s(x, y)} : Set (Sym2 V))) A v = degreeOn G A v := by
  unfold degreeOn
  congr 1
  ext z
  simp only [mem_inter, SimpleGraph.mem_neighborFinset, deleteEdges_adj,
    Set.mem_singleton_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨hvz, _⟩, hzA⟩
    exact ⟨hvz, hzA⟩
  · rintro ⟨hvz, hzA⟩
    refine ⟨⟨hvz, ?_⟩, hzA⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hvx h1
    · exact hvy h1

private lemma degreeOn_deleteEdge_add_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {x y : V} (hxy : G.Adj x y) (hyA : y ∈ A) :
    degreeOn (G.deleteEdges ({s(x, y)} : Set (Sym2 V))) A x + 1 = degreeOn G A x := by
  unfold degreeOn
  let D := (G.deleteEdges ({s(x, y)} : Set (Sym2 V))).neighborFinset x ∩ A
  have hyold : y ∈ G.neighborFinset x ∩ A := by simp [hxy, hyA]
  have hyD : y ∉ D := by simp [D]
  have hdecomp : insert y D = G.neighborFinset x ∩ A := by
    ext z
    simp only [mem_insert, mem_inter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro (rfl | hz)
      · exact ⟨hxy, hyA⟩
      · have hle : G.deleteEdges ({s(x, y)} : Set (Sym2 V)) ≤ G :=
          SimpleGraph.deleteEdges_le _
        exact ⟨by
          apply hle
          simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hz).1,
          (mem_inter.mp hz).2⟩
    · rintro ⟨hxz, hzA⟩
      by_cases hzy : z = y
      · exact Or.inl hzy
      · exact Or.inr <| by
          refine mem_inter.mpr ⟨?_, hzA⟩
          simp only [SimpleGraph.mem_neighborFinset, deleteEdges_adj,
            Set.mem_singleton_iff, Sym2.eq_iff]
          refine ⟨hxz, ?_⟩
          rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact hzy h
          · subst y
            exact hxy.ne rfl
  rw [← hdecomp, card_insert_of_notMem hyD]

private lemma degreeOn_deleteEdge_add_one_right
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    {x y : V} (hxy : G.Adj x y) (hxA : x ∈ A) :
    degreeOn (G.deleteEdges ({s(x, y)} : Set (Sym2 V))) A y + 1 = degreeOn G A y := by
  simpa [Sym2.eq_swap] using
    (degreeOn_deleteEdge_add_one G A hxy.symm hxA)

/-- The edges lost by deleting a single vertex are counted by its restricted degree. -/
lemma incidentCount_singleton (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {v : V} (hv : v ∈ A) :
    incidentCount G A {v} = degreeOn G A v := by
  unfold incidentCount incidentEdges degreeOn
  let f : V → Sym2 V := fun w ↦ s(v, w)
  have hfmem (w : V) (hw : w ∈ G.neighborFinset v ∩ A) :
      f w ∈ edgeOn G A \ edgeOn G (A \ {v}) := by
    rcases mem_inter.mp hw with ⟨hvw, hwA⟩
    have hvw' : G.Adj v w := by simpa [SimpleGraph.mem_neighborFinset] using hvw
    refine mem_sdiff.mpr ⟨?_, ?_⟩
    · refine mem_edgeOn.mpr ⟨by simpa [f] using hvw', ?_⟩
      simpa only [f, Sym2.toFinset_mk_eq, insert_subset_iff,
        singleton_subset_iff] using And.intro hv hwA
    · intro hret
      have hvret : v ∈ A \ {v} := (mem_edgeOn.mp hret).2 (by simp [f])
      simpa using hvret
  symm
  refine Finset.card_bij (fun w hw ↦ f w) ?_ ?_ ?_
  · intro w hw
    exact hfmem w hw
  · intro w₁ hw₁ w₂ _ heq
    rcases (Sym2.eq_iff.mp heq) with h | h
    · exact h.2
    · have hvw₁ : v ≠ w₁ := by
        have hadj : G.Adj v w₁ := by
          simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hw₁).1
        exact hadj.ne
      exact (hvw₁ h.2.symm).elim
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [mem_sdiff, mem_edgeOn, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, Sym2.toFinset_mk_eq, insert_subset_iff,
        singleton_subset_iff, mem_sdiff, mem_singleton] at he
      rcases he with ⟨⟨hxy, hxA, hyA⟩, hnot⟩
      have hvxy : x = v ∨ y = v := by
        by_contra h
        push_neg at h
        exact hnot ⟨hxy, ⟨hxA, h.1⟩, hyA, h.2⟩
      rcases hvxy with rfl | rfl
      · refine ⟨y, mem_inter.mpr ⟨?_, hyA⟩, ?_⟩
        · simpa [SimpleGraph.mem_neighborFinset] using hxy
        · rfl
      · refine ⟨x, mem_inter.mpr ⟨?_, hxA⟩, ?_⟩
        · simpa [SimpleGraph.mem_neighborFinset] using hxy.symm
        · simp [f, Sym2.eq_swap]

/-- An incident edge is charged to one of its endpoints. -/
lemma incidentCount_le_sum_degreeOn (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) {X : Finset V} (hXA : X ⊆ A) :
    incidentCount G A X ≤ ∑ v ∈ X, degreeOn G A v := by
  induction X using Finset.induction_on with
  | empty => simp
  | @insert v X hvX ih =>
      have hvA : v ∈ A := hXA (mem_insert_self v X)
      have hsub : X ⊆ A := fun x hx ↦ hXA (mem_insert_of_mem hx)
      calc
        incidentCount G A (insert v X) = incidentCount G A ({v} ∪ X) := by
          rw [singleton_union]
        _ ≤ incidentCount G A {v} + incidentCount G A X :=
          incidentCount_union_le G A {v} X
        _ ≤ degreeOn G A v + ∑ x ∈ X, degreeOn G A x := by
          rw [incidentCount_singleton G A hvA]
          exact Nat.add_le_add_left (ih hsub) _
        _ = ∑ x ∈ insert v X, degreeOn G A x := by simp [hvX]

private def SparseCandidate (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (H : SimpleGraph V) : Prop := by
  exact H ≤ G ∧ ∃ _hdec : DecidableRel H.Adj,
    HasMinDegreeOn H A k ∧
      ∀ v ∈ A, degreeOn H A v = k → degreeOn G A v = k

private lemma exists_sparse_candidate
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ)
    (hmin : HasMinDegreeOn G A k) :
    ∃ H : SimpleGraph V, SparseCandidate G A k H ∧
      ∀ H', SparseCandidate G A k H' → H' ≤ H → H ≤ H' := by
  classical
  let candidates := (Finset.univ : Finset (SimpleGraph V)).filter (SparseCandidate G A k)
  have hG : G ∈ candidates := by
    simp only [candidates, mem_filter, mem_univ, true_and]
    exact ⟨le_rfl, inferInstance, hmin, fun _ _ h ↦ h⟩
  obtain ⟨H, hHmin⟩ := candidates.exists_minimal ⟨G, hG⟩
  refine ⟨H, ?_, ?_⟩
  · exact (mem_filter.mp hHmin.1).2
  · intro H' hH' hle
    exact hHmin.2 (mem_filter.mpr ⟨mem_univ _, hH'⟩) hle

private lemma sparse_edge_bound
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ)
    (hmin : HasMinDegreeOn G A k) :
    ∃ H : SimpleGraph V, ∃ _hdec : DecidableRel H.Adj,
      H ≤ G ∧ HasMinDegreeOn H A k ∧
      (∀ v ∈ A, degreeOn H A v = k → degreeOn G A v = k) ∧
      edgeCount H A ≤ (k + 1) * A.card := by
  classical
  obtain ⟨H, hcandidate, hminimal⟩ := exists_sparse_candidate G A k hmin
  have hcandidate' : H ≤ G ∧ ∃ _hdec : DecidableRel H.Adj,
      HasMinDegreeOn H A k ∧
        ∀ v ∈ A, degreeOn H A v = k → degreeOn G A v = k := by
    simpa [SparseCandidate] using hcandidate
  rcases hcandidate' with ⟨hHG, hdecH, hHmin, hlow⟩
  let : DecidableRel H.Adj := hdecH
  have hnoHigh : ∀ {x y}, x ∈ A → y ∈ A → H.Adj x y →
      k + 2 ≤ degreeOn H A x → k + 2 ≤ degreeOn H A y → False := by
    intro x y hxA hyA hxy hdx hdy
    let H' := H.deleteEdges ({s(x, y)} : Set (Sym2 V))
    have hH'leH : H' ≤ H := SimpleGraph.deleteEdges_le _
    have hH'min : HasMinDegreeOn H' A k := by
      refine ⟨hHmin.1, ?_⟩
      intro v hvA
      by_cases hvx : v = x
      · subst v
        have heq : degreeOn H' A x + 1 = degreeOn H A x := by
          simpa [H'] using degreeOn_deleteEdge_add_one H A hxy hyA
        change k ≤ degreeOn H' A x
        omega
      · by_cases hvy : v = y
        · subst v
          have heq : degreeOn H' A y + 1 = degreeOn H A y := by
            simpa [H'] using degreeOn_deleteEdge_add_one_right H A hxy hxA
          change k ≤ degreeOn H' A y
          omega
        · change k ≤ degreeOn H' A v
          rw [degreeOn_deleteEdge_eq_of_ne H A hvx hvy]
          exact hHmin.2 v hvA
    have hH'low : ∀ v ∈ A, degreeOn H' A v = k → degreeOn G A v = k := by
      intro v hvA hvdeg
      apply hlow v hvA
      by_cases hvx : v = x
      · subst v
        have heq : degreeOn H' A x + 1 = degreeOn H A x := by
          simpa [H'] using degreeOn_deleteEdge_add_one H A hxy hyA
        change degreeOn H' A x = k at hvdeg
        omega
      · by_cases hvy : v = y
        · subst v
          have heq : degreeOn H' A y + 1 = degreeOn H A y := by
            simpa [H'] using degreeOn_deleteEdge_add_one_right H A hxy hxA
          change degreeOn H' A y = k at hvdeg
          omega
        · change degreeOn H A v = k
          rw [← degreeOn_deleteEdge_eq_of_ne H A hvx hvy]
          exact hvdeg
    have hH'candidate : SparseCandidate G A k H' := by
      change H' ≤ G ∧ ∃ _hdec : DecidableRel H'.Adj,
        HasMinDegreeOn H' A k ∧ _
      exact ⟨hH'leH.trans hHG, inferInstance, hH'min, hH'low⟩
    have hback : H ≤ H' := hminimal H' hH'candidate hH'leH
    have : H'.Adj x y := hback hxy
    simpa [H'] using this
  let L := A.filter fun v ↦ degreeOn H A v ≤ k + 1
  have hLA : L ⊆ A := filter_subset _ _
  have hremain : edgeCount H (A \ L) = 0 := by
    rw [edgeCount, card_eq_zero]
    ext e
    constructor
    · intro he
      induction e using Sym2.inductionOn with
      | _ x y =>
        have hem := mem_edgeOn.mp he
        simp only [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff,
          mem_sdiff] at hem
        rcases hem with ⟨hxy, ⟨hxA, hxL⟩, hyA, hyL⟩
        have hxyAdj : H.Adj x y := by
          simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hxy
        have hxhigh : k + 2 ≤ degreeOn H A x := by
          have hkx := hHmin.2 x hxA
          have : ¬ degreeOn H A x ≤ k + 1 := by simpa [L, hxA] using hxL
          omega
        have hyhigh : k + 2 ≤ degreeOn H A y := by
          have hky := hHmin.2 y hyA
          have : ¬ degreeOn H A y ≤ k + 1 := by simpa [L, hyA] using hyL
          omega
        exact (hnoHigh hxA hyA hxyAdj hxhigh hyhigh).elim
    · simp
  have hincident : incidentCount H A L = edgeCount H A := by
    have hsplit := edgeCount_sdiff_add_incidentCount H A L
    rw [hremain, zero_add] at hsplit
    exact hsplit
  have hedge : edgeCount H A ≤ (k + 1) * A.card := by
    calc
      edgeCount H A = incidentCount H A L := hincident.symm
      _ ≤ ∑ v ∈ L, degreeOn H A v := incidentCount_le_sum_degreeOn H A hLA
      _ ≤ ∑ _v ∈ L, (k + 1) := by
        apply sum_le_sum
        intro v hv
        exact (mem_filter.mp hv).2
      _ = (k + 1) * L.card := by simp [Nat.mul_comm]
      _ ≤ (k + 1) * A.card := Nat.mul_le_mul_left _ (card_le_card hLA)
  exact ⟨H, inferInstance, hHG, hHmin, hlow, hedge⟩

private lemma degreeOn_mono_graph
    {H G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (A : Finset V) (v : V) :
    degreeOn H A v ≤ degreeOn G A v := by
  unfold degreeOn
  apply card_le_card
  intro x hx
  refine mem_inter.mpr ⟨?_, (mem_inter.mp hx).2⟩
  have hxAdj : H.Adj v x := by
    simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hx).1
  simpa [SimpleGraph.mem_neighborFinset] using hHG hxAdj

/-- A red set and its blue protection set.  The numerical budget is exactly the
one used in Sauermann's greedy coloring argument. -/
private def ProtectedPair (H : SimpleGraph V) [DecidableRel H.Adj]
    (A T : Finset V) (k : ℕ) (R B : Finset V) : Prop :=
  R ⊆ T ∧ B ⊆ A ∧ Disjoint R B ∧
    (∀ v ∈ A, (∃ r ∈ R, H.Adj r v) → k ≤ degreeOn H B v) ∧
    B.card ≤ (9 * k ^ 2 - 1) * R.card

private lemma protectedPair_empty
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A T : Finset V) (k : ℕ) : ProtectedPair H A T k ∅ ∅ := by
  simp [ProtectedPair, HasMinDegreeOn, degreeOn]

private lemma ProtectedPair.extend
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A T : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hmin : HasMinDegreeOn H A k)
    {R B : Finset V} (hpair : ProtectedPair H A T k R B)
    {w : V} (hwT : w ∈ T) (hwRB : w ∉ R ∪ B)
    (hwA : w ∈ A)
    (hwlow : degreeOn H A w < 9 * k)
    (hwaway : ∀ v ∈ A, H.Adj w v → degreeOn H A v ≠ k) :
    ∃ B', ProtectedPair H A T k (insert w R) B' := by
  classical
  rcases hpair with ⟨hRT, hBA, hdisj, hprotect, hbudget⟩
  have hwR : w ∉ R := fun hw ↦ hwRB (mem_union_left B hw)
  have hwB : w ∉ B := fun hw ↦ hwRB (mem_union_right R hw)
  let Nw : Finset V := H.neighborFinset w ∩ A
  have havail (v : ↑Nw) (hred : ¬ ∃ r ∈ R, H.Adj r (v : V)) :
      k ≤ ((H.neighborFinset (v : V) ∩ A).erase w).card := by
    have hwv : H.Adj w (v : V) := by
      simpa [Nw, SimpleGraph.mem_neighborFinset] using (mem_inter.mp v.property).1
    have hvA : (v : V) ∈ A := (mem_inter.mp v.property).2
    have hdeg : k ≤ degreeOn H A (v : V) := hmin.2 v hvA
    have hne : degreeOn H A (v : V) ≠ k := hwaway v hvA hwv
    have hsucc : k + 1 ≤ degreeOn H A (v : V) := by omega
    have hwmem : w ∈ H.neighborFinset (v : V) ∩ A := by
      refine mem_inter.mpr ⟨?_, hwA⟩
      simpa [SimpleGraph.mem_neighborFinset] using hwv.symm
    rw [card_erase_of_mem hwmem]
    change k ≤ degreeOn H A (v : V) - 1
    omega
  let C : ↑Nw → Finset V := fun v ↦
    if hred : ∃ r ∈ R, H.Adj r (v : V) then ∅
    else Classical.choose (Finset.exists_subset_card_eq (havail v hred))
  have hC_empty (v : ↑Nw) (hred : ∃ r ∈ R, H.Adj r (v : V)) : C v = ∅ := by
    simp [C, hred]
  have hC_subset (v : ↑Nw) (hred : ¬ ∃ r ∈ R, H.Adj r (v : V)) :
      C v ⊆ (H.neighborFinset (v : V) ∩ A).erase w := by
    simpa [C, hred] using
      (Classical.choose_spec (Finset.exists_subset_card_eq (havail v hred))).1
  have hC_card (v : ↑Nw) (hred : ¬ ∃ r ∈ R, H.Adj r (v : V)) :
      (C v).card = k := by
    simpa [C, hred] using
      (Classical.choose_spec (Finset.exists_subset_card_eq (havail v hred))).2
  have hC_card_le (v : ↑Nw) : (C v).card ≤ k := by
    by_cases hred : ∃ r ∈ R, H.Adj r (v : V)
    · simp [hC_empty v hred]
    · exact (hC_card v hred).le
  have hC_away (v : ↑Nw) {x : V} (hxC : x ∈ C v) : x ∉ insert w R := by
    by_cases hred : ∃ r ∈ R, H.Adj r (v : V)
    · rw [hC_empty v hred] at hxC
      simp at hxC
    · have hxAvail := hC_subset v hred hxC
      have hxw : x ≠ w := (mem_erase.mp hxAvail).1
      have hxNbr : x ∈ H.neighborFinset (v : V) :=
        (mem_inter.mp (mem_erase.mp hxAvail).2).1
      intro hxIns
      rcases mem_insert.mp hxIns with rfl | hxR
      · exact hxw rfl
      · apply hred
        refine ⟨x, hxR, ?_⟩
        have hvx : H.Adj (v : V) x := by
          simpa [SimpleGraph.mem_neighborFinset] using hxNbr
        exact hvx.symm
  let New : Finset V := Nw.attach.biUnion C
  let B' : Finset V := B ∪ New
  refine ⟨B', ?_⟩
  unfold ProtectedPair
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases mem_insert.mp hx with rfl | hxR
    · exact hwT
    · exact hRT hxR
  · intro x hx
    rcases mem_union.mp hx with hxB | hxNew
    · exact hBA hxB
    · obtain ⟨v, hvAttach, hxC⟩ := mem_biUnion.mp hxNew
      by_cases hred : ∃ r ∈ R, H.Adj r (v : V)
      · rw [hC_empty v hred] at hxC
        simp at hxC
      · exact (mem_inter.mp (mem_erase.mp (hC_subset v hred hxC)).2).2
  · rw [Finset.disjoint_left]
    intro x hxIns hxB'
    rcases mem_union.mp hxB' with hxB | hxNew
    · rcases mem_insert.mp hxIns with rfl | hxR
      · exact hwB hxB
      · exact (Finset.disjoint_left.mp hdisj hxR hxB)
    · obtain ⟨v, hvAttach, hxC⟩ := mem_biUnion.mp hxNew
      exact hC_away v hxC hxIns
  · intro v hvA hredNew
    by_cases hredOld : ∃ r ∈ R, H.Adj r v
    · exact (hprotect v hvA hredOld).trans
        (degreeOn_mono H (show B ⊆ B' by intro x hx; exact mem_union_left _ hx) v)
    · obtain ⟨r, hrIns, hrv⟩ := hredNew
      have hrw : r = w := (mem_insert.mp hrIns).resolve_right
        (fun hrR ↦ hredOld ⟨r, hrR, hrv⟩)
      subst r
      have hvNw : v ∈ Nw := by
        exact mem_inter.mpr ⟨by simpa [SimpleGraph.mem_neighborFinset] using hrv, hvA⟩
      let vv : ↑Nw := ⟨v, hvNw⟩
      have hCsub := hC_subset vv hredOld
      have hCdeg : (C vv).card = k := hC_card vv hredOld
      rw [← hCdeg]
      apply card_le_card
      intro x hxC
      refine mem_inter.mpr ⟨?_, ?_⟩
      · exact (mem_inter.mp (mem_erase.mp (hCsub hxC)).2).1
      · exact mem_union_right B (mem_biUnion.mpr ⟨vv, mem_attach _ _, hxC⟩)
  · have hNewCard : New.card ≤ Nw.card * k := by
      calc
        New.card ≤ ∑ v ∈ Nw.attach, (C v).card := Finset.card_biUnion_le
        _ ≤ ∑ _v ∈ Nw.attach, k := by
          apply sum_le_sum
          intro v hv
          exact hC_card_le v
        _ = Nw.card * k := by simp
    have hstep : Nw.card * k ≤ 9 * k ^ 2 - 1 := by
      have hn : Nw.card = degreeOn H A w := by rfl
      rw [hn]
      have hdeg : degreeOn H A w ≤ 9 * k - 1 := by omega
      have hmul := Nat.mul_le_mul_right k hdeg
      have hnum : (9 * k - 1) * k ≤ 9 * k ^ 2 - 1 := by
        rw [Nat.sub_mul]
        simp only [one_mul]
        have heq : 9 * k * k = 9 * k ^ 2 := by ring
        rw [heq]
        exact Nat.sub_le_sub_left (by omega) _
      exact hmul.trans hnum
    calc
      B'.card ≤ B.card + New.card := card_union_le _ _
      _ ≤ (9 * k ^ 2 - 1) * R.card + (9 * k ^ 2 - 1) :=
        Nat.add_le_add hbudget (hNewCard.trans hstep)
      _ = (9 * k ^ 2 - 1) * (insert w R).card := by simp [hwR, Nat.mul_add]

private lemma exists_covering_protectedPair
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A T : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hmin : HasMinDegreeOn H A k)
    (hTA : T ⊆ A)
    (hgood : ∀ w ∈ T,
      degreeOn H A w < 9 * k ∧
      ∀ v ∈ A, H.Adj w v → degreeOn H A v ≠ k) :
    ∃ R B, ProtectedPair H A T k R B ∧ T ⊆ R ∪ B := by
  classical
  let candidates := T.powerset.filter fun R ↦ ∃ B, ProtectedPair H A T k R B
  have hempty : ∅ ∈ candidates := by
    simp only [candidates, mem_filter, mem_powerset, empty_subset, true_and]
    exact ⟨∅, protectedPair_empty H A T k⟩
  obtain ⟨R, hRmax⟩ := candidates.exists_maximal ⟨∅, hempty⟩
  rcases mem_filter.mp hRmax.1 with ⟨hRpow, B, hpair⟩
  refine ⟨R, B, hpair, ?_⟩
  intro w hwT
  by_contra hwRB
  have hwNot : w ∉ R ∪ B := hwRB
  obtain ⟨B', hpair'⟩ := ProtectedPair.extend H A T k hk hmin hpair hwT hwNot
    (hTA hwT) (hgood w hwT).1 (hgood w hwT).2
  have hInsCand : insert w R ∈ candidates := by
    refine mem_filter.mpr ⟨?_, B', hpair'⟩
    exact mem_powerset.mpr (insert_subset hwT (mem_powerset.mp hRpow))
  have hback : insert w R ⊆ R := hRmax.2 hInsCand (subset_insert w R)
  have hwR : w ∉ R := fun hw ↦ hwNot (mem_union_left B hw)
  exact hwR (hback (mem_insert_self w R))

private lemma sparse_degreeKSupply
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (A : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hmin : HasMinDegreeOn H A k)
    (hedge : edgeCount H A ≤ (k + 1) * A.card)
    (hFew : 3 * k * (degreeEq H A k).card ≤ A.card) :
    ∃ W : Finset V, W ⊆ A ∧ HasMinDegreeOn H W k ∧
      27 * k ^ 2 * W.card ≤ (27 * k ^ 2 - 1) * A.card := by
  classical
  let D := degreeEq H A k
  let T₁ := D.biUnion fun v ↦ H.neighborFinset v ∩ A
  let T₂ := A.filter fun v ↦ 9 * k ≤ degreeOn H A v
  let U := T₁ ∪ T₂
  let T := A \ U
  have hDdeg : ∀ v ∈ D, degreeOn H A v = k := by
    intro v hv
    exact (mem_degreeEq.mp (show v ∈ degreeEq H A k by simpa [D] using hv)).2
  have hT₁A : T₁ ⊆ A := by
    intro x hx
    obtain ⟨v, hvD, hxN⟩ := mem_biUnion.mp hx
    exact (mem_inter.mp hxN).2
  have hT₁card : T₁.card ≤ k * D.card := by
    calc
      T₁.card ≤ ∑ v ∈ D, (H.neighborFinset v ∩ A).card :=
        Finset.card_biUnion_le
      _ = ∑ _v ∈ D, k := by
        apply sum_congr rfl
        intro v hv
        exact hDdeg v hv
      _ = k * D.card := by simp [Nat.mul_comm]
  have hT₁third : 3 * T₁.card ≤ A.card := by
    calc
      3 * T₁.card ≤ 3 * (k * D.card) := Nat.mul_le_mul_left 3 hT₁card
      _ = 3 * k * (degreeEq H A k).card := by simp [D, Nat.mul_assoc]
      _ ≤ A.card := hFew
  have hT₂A : T₂ ⊆ A := filter_subset _ _
  have hHighSum : 9 * k * T₂.card ≤ ∑ v ∈ T₂, degreeOn H A v := by
    calc
      9 * k * T₂.card = ∑ _v ∈ T₂, 9 * k := by
        simp
        ring
      _ ≤ ∑ v ∈ T₂, degreeOn H A v := by
        apply sum_le_sum
        intro v hv
        exact (mem_filter.mp hv).2
  have hHighTotal : 9 * k * T₂.card ≤ ∑ v ∈ A, degreeOn H A v := by
    exact hHighSum.trans (sum_le_sum_of_subset_of_nonneg hT₂A (by simp))
  have hTotal : (∑ v ∈ A, degreeOn H A v) ≤ 3 * k * A.card := by
    calc
      (∑ v ∈ A, degreeOn H A v) = 2 * edgeCount H A :=
        sum_degreeOn_eq_twice_edgeCount H A
      _ ≤ 2 * ((k + 1) * A.card) := Nat.mul_le_mul_left 2 hedge
      _ ≤ (3 * k) * A.card := by
        have hcoef : 2 * (k + 1) ≤ 3 * k := by omega
        simpa [Nat.mul_assoc] using Nat.mul_le_mul_right A.card hcoef
      _ = 3 * k * A.card := by simp [Nat.mul_assoc]
  have hT₂third : 3 * T₂.card ≤ A.card := by
    apply Nat.le_of_mul_le_mul_left (c := 3 * k) ?_ (by omega)
    calc
      (3 * k) * (3 * T₂.card) = 9 * k * T₂.card := by ring
      _ ≤ 3 * k * A.card := hHighTotal.trans hTotal
      _ = (3 * k) * A.card := by ring
  have hUA : U ⊆ A := union_subset hT₁A hT₂A
  have hUbound : 3 * U.card ≤ 2 * A.card := by
    calc
      3 * U.card ≤ 3 * (T₁.card + T₂.card) :=
        Nat.mul_le_mul_left 3 (card_union_le T₁ T₂)
      _ = 3 * T₁.card + 3 * T₂.card := by ring
      _ ≤ A.card + A.card := Nat.add_le_add hT₁third hT₂third
      _ = 2 * A.card := by omega
  have hTA : T ⊆ A := sdiff_subset
  have hsplitT : T.card + U.card = A.card := by
    have := Nat.sub_add_cancel (card_le_card hUA)
    simpa [T, card_sdiff_of_subset hUA] using this
  have hTthird : A.card ≤ 3 * T.card := by omega
  have hgood : ∀ w ∈ T,
      degreeOn H A w < 9 * k ∧
      ∀ v ∈ A, H.Adj w v → degreeOn H A v ≠ k := by
    intro w hwT
    have hwA : w ∈ A := hTA hwT
    have hwU : w ∉ U := (mem_sdiff.mp hwT).2
    have hwT₂ : w ∉ T₂ := fun hw ↦ hwU (mem_union_right T₁ hw)
    constructor
    · have hnot : ¬ 9 * k ≤ degreeOn H A w := by
        simpa [T₂, hwA] using hwT₂
      omega
    · intro v hvA hwv heq
      have hvD : v ∈ D := by
        simpa [D, mem_degreeEq, hvA, heq]
      have hwT₁ : w ∈ T₁ := by
        apply mem_biUnion.mpr
        refine ⟨v, hvD, mem_inter.mpr ⟨?_, hwA⟩⟩
        simpa [SimpleGraph.mem_neighborFinset] using hwv.symm
      exact hwU (mem_union_left T₂ hwT₁)
  obtain ⟨R, B, hpair, hcover⟩ :=
    exists_covering_protectedPair H A T k hk hmin hTA hgood
  rcases hpair with ⟨hRT, hBA, hdisj, hprotect, hbudget⟩
  have hTRB : T.card ≤ R.card + B.card := by
    calc
      T.card ≤ (R ∪ B).card := card_le_card hcover
      _ ≤ R.card + B.card := card_union_le R B
  have hqpos : 0 < 9 * k ^ 2 := by positivity
  have hTred : T.card ≤ 9 * k ^ 2 * R.card := by
    calc
      T.card ≤ R.card + B.card := hTRB
      _ ≤ R.card + (9 * k ^ 2 - 1) * R.card := Nat.add_le_add_left hbudget _
      _ = 9 * k ^ 2 * R.card := by
        have : 9 * k ^ 2 - 1 + 1 = 9 * k ^ 2 := by omega
        calc
          R.card + (9 * k ^ 2 - 1) * R.card =
              (1 + (9 * k ^ 2 - 1)) * R.card := by ring
          _ = 9 * k ^ 2 * R.card := by rw [Nat.add_comm 1, this]
  have hAR : A.card ≤ 27 * k ^ 2 * R.card := by
    calc
      A.card ≤ 3 * T.card := hTthird
      _ ≤ 3 * (9 * k ^ 2 * R.card) := Nat.mul_le_mul_left 3 hTred
      _ = 27 * k ^ 2 * R.card := by ring
  have hRA : R ⊆ A := hRT.trans hTA
  let W := A \ R
  have hBW : B ⊆ W := by
    intro b hb
    refine mem_sdiff.mpr ⟨hBA hb, ?_⟩
    intro hbR
    exact Finset.disjoint_left.mp hdisj hbR hb
  have hWnonempty : W.Nonempty := by
    by_cases hRne : R.Nonempty
    · obtain ⟨r, hrR⟩ := hRne
      have hrA : r ∈ A := hRA hrR
      have hrpos : 0 < degreeOn H A r := lt_of_lt_of_le (by omega) (hmin.2 r hrA)
      obtain ⟨v, hvNbr⟩ := card_pos.mp hrpos
      have hrv : H.Adj r v := by
        simpa [degreeOn, SimpleGraph.mem_neighborFinset] using (mem_inter.mp hvNbr).1
      have hvA : v ∈ A := (mem_inter.mp hvNbr).2
      have hBpos : 0 < degreeOn H B v :=
        lt_of_lt_of_le (by omega) (hprotect v hvA ⟨r, hrR, hrv⟩)
      obtain ⟨b, hbNbr⟩ := card_pos.mp hBpos
      exact ⟨b, hBW (mem_inter.mp hbNbr).2⟩
    · have hRempty : R = ∅ := not_nonempty_iff_eq_empty.mp hRne
      simpa [W, hRempty] using hmin.1
  have hWmin : HasMinDegreeOn H W k := by
    refine ⟨hWnonempty, ?_⟩
    intro v hvW
    have hvA : v ∈ A := (mem_sdiff.mp hvW).1
    by_cases hred : ∃ r ∈ R, H.Adj r v
    · exact (hprotect v hvA hred).trans (degreeOn_mono H hBW v)
    · exact (hmin.2 v hvA).trans <| by
        unfold degreeOn
        apply card_le_card
        intro x hx
        refine mem_inter.mpr ⟨(mem_inter.mp hx).1, mem_sdiff.mpr ⟨(mem_inter.mp hx).2, ?_⟩⟩
        intro hxR
        apply hred
        refine ⟨x, hxR, ?_⟩
        have hvx : H.Adj v x := by
          simpa [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hx).1
        exact hvx.symm
  have hsplitR : W.card + R.card = A.card := by
    have := Nat.sub_add_cancel (card_le_card hRA)
    simpa [W, card_sdiff_of_subset hRA] using this
  have hshrink : 27 * k ^ 2 * W.card ≤ (27 * k ^ 2 - 1) * A.card := by
    have hadd : 27 * k ^ 2 * W.card + A.card ≤ 27 * k ^ 2 * A.card := by
      calc
        27 * k ^ 2 * W.card + A.card ≤
            27 * k ^ 2 * W.card + 27 * k ^ 2 * R.card :=
          Nat.add_le_add_left hAR _
        _ = 27 * k ^ 2 * A.card := by rw [← hsplitR]; ring
    have hsub : 27 * k ^ 2 * W.card ≤ 27 * k ^ 2 * A.card - A.card :=
      Nat.le_sub_of_add_le hadd
    simpa [Nat.sub_mul] using hsub
  exact ⟨W, sdiff_subset, hWmin, hshrink⟩

/-- Sauermann's degree-`k` supply lemma (Lemma 2.2), in the fixed-ambient
form used by the rest of the formalization. -/
theorem degreeKSupply
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hmin : HasMinDegreeOn G A k)
    (hFew : 3 * k * (degreeEq G A k).card ≤ A.card) :
    ∃ W : Finset V, W ⊆ A ∧ HasMinDegreeOn G W k ∧
      27 * k ^ 2 * W.card ≤ (27 * k ^ 2 - 1) * A.card := by
  classical
  obtain ⟨H, hdecH, hHG, hHmin, hlow, hedge⟩ := sparse_edge_bound G A k hmin
  let : DecidableRel H.Adj := hdecH
  have hdegSub : degreeEq H A k ⊆ degreeEq G A k := by
    intro v hv
    rcases mem_degreeEq.mp hv with ⟨hvA, hvdeg⟩
    exact mem_degreeEq.mpr ⟨hvA, hlow v hvA hvdeg⟩
  have hFewH : 3 * k * (degreeEq H A k).card ≤ A.card := by
    exact (Nat.mul_le_mul_left (3 * k) (card_le_card hdegSub)).trans hFew
  obtain ⟨W, hWA, hWmin, hshrink⟩ :=
    sparse_degreeKSupply H A k hk hHmin hedge hFewH
  refine ⟨W, hWA, ⟨hWmin.1, ?_⟩, hshrink⟩
  intro v hvW
  exact (hWmin.2 v hvW).trans (degreeOn_mono_graph hHG W v)

/-- Contrapositive form used in a minimal counterexample: if none of the
cores furnished by `degreeKSupply` is allowed, degree-`k` vertices have total
mass at least `|A| / (3k)`. -/
theorem many_degree_eq_k_of_counterexample
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (k : ℕ) (hk : 2 ≤ k)
    (hmin : HasMinDegreeOn G A k)
    (hno : ¬ ∃ W : Finset V, W ⊆ A ∧ HasMinDegreeOn G W k ∧
      27 * k ^ 2 * W.card ≤ (27 * k ^ 2 - 1) * A.card) :
    A.card ≤ 3 * k * (degreeEq G A k).card := by
  by_contra hmany
  have hFew : 3 * k * (degreeEq G A k).card ≤ A.card := by omega
  exact hno (degreeKSupply G A k hk hmin hFew)

end Erdos814
