import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-!
# Prüfer decoding for labelled trees

The decoder is defined on an ambient ordered finite type.  Removing a label
from the active vertex set leaves it isolated in the ambient graph, so the
recursive construction does not change its vertex type.
-/

namespace Erdos745.Prufer

noncomputable section

variable {V : Type*} [LinearOrder V] [Fintype V]

attribute [local instance] Classical.propDecidable

/-- All endpoints of graph edges belong to the active label set. -/
def SupportedOn (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ ⦃u v⦄, G.Adj u v → u ∈ S ∧ v ∈ S

theorem degree_eq_zero_of_supported {G : SimpleGraph V} {S : Finset V}
    (hG : SupportedOn G S) {v : V} (hv : v ∉ S) : G.degree v = 0 := by
  classical
  rw [SimpleGraph.degree_eq_zero_iff_notMem_support]
  rintro ⟨w, hvw⟩
  exact hv (hG hvw).1

/-- The complete graph on the active labels, with all other labels isolated. -/
def completeOn (S : Finset V) : SimpleGraph V where
  Adj u v := u ∈ S ∧ v ∈ S ∧ u ≠ v
  symm := ⟨fun _ _ h ↦ ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.2.2 rfl⟩

theorem completeOn_supported (S : Finset V) : SupportedOn (completeOn S) S := by
  intro u v h
  exact ⟨h.1, h.2.1⟩

theorem completeOn_pair (a b : V) :
    completeOn {a, b} = SimpleGraph.edge a b := by
  ext u v
  simp only [completeOn, SimpleGraph.edge_adj, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hu | hu, hv | hv, huv⟩
    · exact False.elim (huv (hu.trans hv.symm))
    · exact ⟨Or.inl ⟨hu, hv⟩, huv⟩
    · exact ⟨Or.inr ⟨hu, hv⟩, huv⟩
    · exact False.elim (huv (hu.trans hv.symm))
  · rintro ⟨⟨hu, hv⟩ | ⟨hu, hv⟩, huv⟩
    · exact ⟨Or.inl hu, Or.inr hv, huv⟩
    · exact ⟨Or.inr hu, Or.inl hv, huv⟩

theorem isAcyclic_edge (a b : V) : (SimpleGraph.edge a b).IsAcyclic := by
  by_cases hab : a = b
  · subst b
    simpa using (SimpleGraph.isAcyclic_bot (V := V))
  · have hreach : ¬ (⊥ : SimpleGraph V).Reachable a b := by
      simpa only [SimpleGraph.reachable_bot] using hab
    simpa using SimpleGraph.IsAcyclic.sup_edge_of_not_reachable hreach
      (SimpleGraph.isAcyclic_bot (V := V))

theorem completeOn_acyclic {S : Finset V} (hS : S.card = 2) :
    (completeOn S).IsAcyclic := by
  obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.mp hS
  rw [completeOn_pair]
  exact isAcyclic_edge a b

/-- Labels still available but absent from the remaining Prüfer word. -/
def missingLabels (S : Finset V) (L : List V) : Finset V := S \ L.toFinset

theorem missingLabels_nonempty {S : Finset V} {L : List V}
    (hlen : L.length < S.card) : (missingLabels S L).Nonempty := by
  by_contra h
  have hempty : missingLabels S L = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hsub : S ⊆ L.toFinset := Finset.sdiff_eq_empty_iff_subset.mp hempty
  have hcard := (Finset.card_le_card hsub).trans L.toFinset_card_le
  omega

def missingLabel (S : Finset V) (L : List V) (h : (missingLabels S L).Nonempty) : V :=
  (missingLabels S L).min' h

theorem missingLabel_mem {S : Finset V} {L : List V}
    (h : (missingLabels S L).Nonempty) : missingLabel S L h ∈ S :=
  (Finset.mem_sdiff.mp ((missingLabels S L).min'_mem h)).1

theorem missingLabel_not_mem {S : Finset V} {L : List V}
    (h : (missingLabels S L).Nonempty) : missingLabel S L h ∉ L := by
  have hnot := (Finset.mem_sdiff.mp ((missingLabels S L).min'_mem h)).2
  simpa only [missingLabel, List.mem_toFinset] using hnot

theorem missingLabel_le {S : Finset V} {L : List V}
    (h : (missingLabels S L).Nonempty) {v : V} (hv : v ∈ S) (hvL : v ∉ L) :
    missingLabel S L h ≤ v := by
  exact (missingLabels S L).min'_le v
    (Finset.mem_sdiff.mpr ⟨hv, by simpa only [List.mem_toFinset] using hvL⟩)

/-- The standard Prüfer decoder.  Invalid inputs are totalized by the empty
graph; all counting theorems will impose the exact length and membership conditions. -/
def decode (S : Finset V) : List V → SimpleGraph V
  | [] => completeOn S
  | a :: L =>
      if h : (missingLabels S (a :: L)).Nonempty then
        let v := missingLabel S (a :: L) h
        decode (S.erase v) L ⊔ SimpleGraph.edge v a
      else ⊥

theorem decode_supported (S : Finset V) (L : List V)
    (hL : ∀ v ∈ L, v ∈ S) : SupportedOn (decode S L) S := by
  induction L generalizing S with
  | nil => exact completeOn_supported S
  | cons a L ih =>
    unfold decode
    split_ifs with hm
    · let v := missingLabel S (a :: L) hm
      have hvS : v ∈ S := missingLabel_mem hm
      have hvL : v ∉ a :: L := missingLabel_not_mem hm
      have htail : ∀ u ∈ L, u ∈ S.erase v := by
        intro u hu
        exact Finset.mem_erase.mpr
          ⟨fun huv ↦ hvL (by simp [← huv, hu]), hL u (by simp [hu])⟩
      have hsup := ih (S.erase v) htail
      intro u w huw
      rcases huw with huw | huw
      · exact ⟨Finset.mem_of_mem_erase (hsup huw).1,
          Finset.mem_of_mem_erase (hsup huw).2⟩
      · rw [SimpleGraph.edge_adj] at huw
        have haS : a ∈ S := hL a (by simp)
        rcases huw.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨hvS, haS⟩
        · exact ⟨haS, hvS⟩
    · intro u w huw
      exact False.elim huw

theorem decode_acyclic (S : Finset V) (L : List V)
    (hlen : S.card = L.length + 2) (hL : ∀ v ∈ L, v ∈ S) :
    (decode S L).IsAcyclic := by
  induction L generalizing S with
  | nil => exact completeOn_acyclic (by simpa using hlen)
  | cons a L ih =>
    have hm : (missingLabels S (a :: L)).Nonempty :=
      missingLabels_nonempty (by simp only [List.length_cons] at hlen ⊢; omega)
    let v := missingLabel S (a :: L) hm
    have hvS : v ∈ S := missingLabel_mem hm
    have hvL : v ∉ a :: L := missingLabel_not_mem hm
    have hva : v ≠ a := fun h ↦ hvL (by simp [h])
    have htail : ∀ u ∈ L, u ∈ S.erase v := by
      intro u hu
      exact Finset.mem_erase.mpr
        ⟨fun huv ↦ hvL (by simp [← huv, hu]), hL u (by simp [hu])⟩
    have hsize : (S.erase v).card = L.length + 2 := by
      rw [Finset.card_erase_of_mem hvS]
      simp only [List.length_cons] at hlen
      omega
    have hacyc := ih (S.erase v) hsize htail
    have hzero : (decode (S.erase v) L).degree v = 0 :=
      degree_eq_zero_of_supported (decode_supported _ _ htail) (Finset.notMem_erase _ _)
    have hreach : ¬ (decode (S.erase v) L).Reachable v a :=
      SimpleGraph.not_reachable_of_left_degree_zero hva hzero
    rw [decode, dif_pos hm]
    exact hacyc.sup_edge_of_not_reachable hreach

/-- Ambient reachability between all active labels. -/
def ConnectedOn (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, G.Reachable u v

theorem decode_connectedOn (S : Finset V) (L : List V)
    (hlen : S.card = L.length + 2) (hL : ∀ v ∈ L, v ∈ S) :
    ConnectedOn (decode S L) S := by
  induction L generalizing S with
  | nil =>
    intro u hu v hv
    by_cases huv : u = v
    · subst v
      exact .rfl
    · exact (show (completeOn S).Adj u v from ⟨hu, hv, huv⟩).reachable
  | cons a L ih =>
    have hm : (missingLabels S (a :: L)).Nonempty :=
      missingLabels_nonempty (by simp only [List.length_cons] at hlen ⊢; omega)
    let w := missingLabel S (a :: L) hm
    have hwS : w ∈ S := missingLabel_mem hm
    have hwL : w ∉ a :: L := missingLabel_not_mem hm
    have hwa : w ≠ a := fun h ↦ hwL (by simp [h])
    have haS : a ∈ S := hL a (by simp)
    have htail : ∀ u ∈ L, u ∈ S.erase w := by
      intro u hu
      exact Finset.mem_erase.mpr
        ⟨fun huw ↦ hwL (by simp [← huw, hu]), hL u (by simp [hu])⟩
    have hsize : (S.erase w).card = L.length + 2 := by
      rw [Finset.card_erase_of_mem hwS]
      simp only [List.length_cons] at hlen
      omega
    have hc := ih (S.erase w) hsize htail
    have ha : a ∈ S.erase w := Finset.mem_erase.mpr ⟨hwa.symm, haS⟩
    rw [decode, dif_pos hm]
    have hedge : (decode (S.erase w) L ⊔ SimpleGraph.edge w a).Reachable w a := by
      apply SimpleGraph.Adj.reachable
      apply Or.inr
      rw [SimpleGraph.edge_adj]
      exact ⟨Or.inl ⟨rfl, rfl⟩, hwa⟩
    intro u hu v hv
    by_cases huw : u = w
    · subst u
      by_cases hvw : v = w
      · subst v
        exact .rfl
      · exact hedge.trans ((hc a ha v (Finset.mem_erase.mpr ⟨hvw, hv⟩)).mono le_sup_left)
    · have hu' : u ∈ S.erase w := Finset.mem_erase.mpr ⟨huw, hu⟩
      by_cases hvw : v = w
      · subst v
        exact ((hc u hu' a ha).mono le_sup_left).trans hedge.symm
      · exact (hc u hu' v (Finset.mem_erase.mpr ⟨hvw, hv⟩)).mono le_sup_left

theorem walk_support_subset {G : SimpleGraph V} {S : Finset V}
    (hG : SupportedOn G S) {u v : V} (p : G.Walk u v) (hu : u ∈ S) :
    ∀ w ∈ p.support, w ∈ S := by
  induction p with
  | nil => simpa using hu
  | @cons u w v huw p ih =>
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hu
    · exact ih (hG huw).2 x hx

theorem connected_induce_of_supported {G : SimpleGraph V} {S : Finset V}
    (hG : SupportedOn G S) (hc : ConnectedOn G S) (hne : S.Nonempty) :
    (G.induce (S : Set V)).Connected := by
  let : Nonempty (S : Set V) := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨p⟩ := hc u.val u.property v.val v.property
  exact ⟨p.induce (S : Set V) (walk_support_subset hG p u.property)⟩

/-- A valid Prüfer word always decodes to a tree on precisely the active labels. -/
theorem decode_isTree_induce (S : Finset V) (L : List V)
    (hlen : S.card = L.length + 2) (hL : ∀ v ∈ L, v ∈ S) :
    ((decode S L).induce (S : Set V)).IsTree := by
  refine ⟨connected_induce_of_supported (decode_supported S L hL)
    (decode_connectedOn S L hlen hL) ?_, (decode_acyclic S L hlen hL).induce _⟩
  exact Finset.card_pos.mp (by omega)

theorem neighborFinset_completeOn {S : Finset V} {u : V} (hu : u ∈ S) :
    (completeOn S).neighborFinset u = S.erase u := by
  ext v
  rw [SimpleGraph.mem_neighborFinset]
  change (u ∈ S ∧ v ∈ S ∧ u ≠ v) ↔ v ∈ S.erase u
  simp [hu, ne_comm, and_comm]

theorem degree_completeOn {S : Finset V} {u : V} (hu : u ∈ S) :
    (completeOn S).degree u = S.card - 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_completeOn hu]
  exact Finset.card_erase_of_mem hu

theorem neighborFinset_edge (a b u : V) (hab : a ≠ b) :
    (SimpleGraph.edge a b).neighborFinset u =
      if u = a then {b} else if u = b then {a} else ∅ := by
  ext v
  by_cases hua : u = a <;> by_cases hub : u = b <;>
    simp [SimpleGraph.mem_neighborFinset, SimpleGraph.edge_adj, hua, hub, hab,
      eq_comm] <;> aesop

theorem degree_edge (a b u : V) (hab : a ≠ b) :
    (SimpleGraph.edge a b).degree u =
      if u = a then 1 else if u = b then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_edge a b u hab]
  split_ifs <;> simp

theorem degree_sup_edge_of_isolated (G : SimpleGraph V) (a b u : V)
    (ha : G.degree a = 0) :
    (G ⊔ SimpleGraph.edge a b).degree u =
      G.degree u + (SimpleGraph.edge a b).degree u := by
  have hiso (v : V) : ¬G.Adj a v := by
    intro hav
    have hp : 0 < G.degree a := (G.degree_pos_iff_exists_adj a).mpr ⟨v, hav⟩
    omega
  have hdis : Disjoint (G.neighborFinset u) ((SimpleGraph.edge a b).neighborFinset u) := by
    rw [Finset.disjoint_left]
    intro v hGu he
    rw [SimpleGraph.mem_neighborFinset] at hGu he
    rw [SimpleGraph.edge_adj] at he
    rcases he.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hiso _ hGu
    · exact hiso _ hGu.symm
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_sup,
    Finset.card_union_of_disjoint hdis]
  simp only [SimpleGraph.card_neighborFinset_eq_degree]

theorem degree_decode (S : Finset V) (L : List V)
    (hlen : S.card = L.length + 2) (hL : ∀ v ∈ L, v ∈ S)
    {u : V} (hu : u ∈ S) :
    (decode S L).degree u = L.count u + 1 := by
  induction L generalizing S with
  | nil =>
    rw [decode, degree_completeOn hu]
    simp only [List.length_nil] at hlen
    simp [hlen]
  | cons a L ih =>
    have hm : (missingLabels S (a :: L)).Nonempty :=
      missingLabels_nonempty (by simp only [List.length_cons] at hlen ⊢; omega)
    let v := missingLabel S (a :: L) hm
    have hvS : v ∈ S := missingLabel_mem hm
    have hvL : v ∉ a :: L := missingLabel_not_mem hm
    have hva : v ≠ a := fun h ↦ hvL (by simp [h])
    have htail : ∀ w ∈ L, w ∈ S.erase v := by
      intro w hw
      exact Finset.mem_erase.mpr
        ⟨fun hwv ↦ hvL (by simp [← hwv, hw]), hL w (by simp [hw])⟩
    have hsize : (S.erase v).card = L.length + 2 := by
      rw [Finset.card_erase_of_mem hvS]
      simp only [List.length_cons] at hlen
      omega
    have hzero : (decode (S.erase v) L).degree v = 0 :=
      degree_eq_zero_of_supported (decode_supported _ _ htail) (Finset.notMem_erase _ _)
    rw [decode, dif_pos hm]
    dsimp only
    have hadd := degree_sup_edge_of_isolated (decode (S.erase v) L) v a u hzero
    have hsum : (decode (S.erase v) L).degree u + (SimpleGraph.edge v a).degree u =
        (a :: L).count u + 1 := by
      rw [degree_edge v a u hva]
      by_cases huv : u = v
      · subst u
        rw [hzero]
        rw [List.count_eq_zero.mpr hvL]
        simp
      · rw [if_neg huv, ih (S.erase v) hsize htail (Finset.mem_erase.mpr ⟨huv, hu⟩)]
        by_cases hua : u = a
        · subst u
          simp
        · simp [hua, Ne.symm hua]
    simpa only [← SimpleGraph.card_neighborSet_eq_degree,
      Fintype.card_eq_nat_card] using hadd.trans hsum

/-- The missing letters are precisely the leaves of the decoded tree. -/
theorem missingLabels_eq_leaves (S : Finset V) (L : List V)
    (hlen : S.card = L.length + 2) (hL : ∀ v ∈ L, v ∈ S) :
    missingLabels S L = S.filter (fun u ↦ Nat.card ((decode S L).neighborSet u) = 1) := by
  ext u
  by_cases hu : u ∈ S
  · have hd := degree_decode S L hlen hL hu
    rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hd
    simp only [missingLabels, Finset.mem_sdiff, List.mem_toFinset,
      Finset.mem_filter, hu, true_and]
    rw [hd]
    constructor
    · intro h
      rw [List.count_eq_zero.mpr h]
    · intro h
      exact List.count_eq_zero.mp (by omega)
  · simp [missingLabels, hu]

theorem decode_adj_leaf_iff (S : Finset V) (a : V) (L : List V)
    (hm : (missingLabels S (a :: L)).Nonempty) (hL : ∀ v ∈ a :: L, v ∈ S)
    (u : V) :
    (decode S (a :: L)).Adj (missingLabel S (a :: L) hm) u ↔ u = a := by
  let v := missingLabel S (a :: L) hm
  have hvL : v ∉ a :: L := missingLabel_not_mem hm
  have hva : v ≠ a := fun h ↦ hvL (by simp [h])
  have htail : ∀ w ∈ L, w ∈ S.erase v := by
    intro w hw
    exact Finset.mem_erase.mpr
      ⟨fun hwv ↦ hvL (by simp [← hwv, hw]), hL w (by simp [hw])⟩
  have hnot : ¬ (decode (S.erase v) L).Adj v u := by
    intro h
    exact (Finset.notMem_erase v S) (decode_supported _ _ htail h).1
  rw [decode, dif_pos hm]
  change (decode (S.erase v) L).Adj v u ∨ (SimpleGraph.edge v a).Adj v u ↔ u = a
  simp [hnot, SimpleGraph.edge_adj, hva, eq_comm]
  intro hau huv
  exact hva (huv.symm.trans hau.symm)

/-- Adding the same isolated leaf is injective on graphs supported away from it. -/
theorem sup_edge_left_cancel {S : Finset V} {v a : V} {G H : SimpleGraph V}
    (hG : SupportedOn G (S.erase v)) (hH : SupportedOn H (S.erase v))
    (heq : G ⊔ SimpleGraph.edge v a = H ⊔ SimpleGraph.edge v a) : G = H := by
  ext u w
  have hnotG : G.Adj u w → ¬ (SimpleGraph.edge v a).Adj u w := by
    intro huw he
    have hu := (Finset.mem_erase.mp (hG huw).1).1
    have hw := (Finset.mem_erase.mp (hG huw).2).1
    rw [SimpleGraph.edge_adj] at he
    rcases he.1 with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact hu rfl
    · exact hw rfl
  have hnotH : H.Adj u w → ¬ (SimpleGraph.edge v a).Adj u w := by
    intro huw he
    have hu := (Finset.mem_erase.mp (hH huw).1).1
    have hw := (Finset.mem_erase.mp (hH huw).2).1
    rw [SimpleGraph.edge_adj] at he
    rcases he.1 with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact hu rfl
    · exact hw rfl
  have he : G.Adj u w ∨ (SimpleGraph.edge v a).Adj u w ↔
      H.Adj u w ∨ (SimpleGraph.edge v a).Adj u w := by
    exact congrArg (fun J : SimpleGraph V ↦ J.Adj u w) heq |>.to_iff
  tauto

/-- The standard Prüfer decoder is injective on valid words. -/
theorem decode_injective (S : Finset V) (L M : List V)
    (hLlen : S.card = L.length + 2) (hMlen : S.card = M.length + 2)
    (hL : ∀ v ∈ L, v ∈ S) (hM : ∀ v ∈ M, v ∈ S)
    (heq : decode S L = decode S M) : L = M := by
  induction L generalizing S M with
  | nil =>
    have : M.length = 0 := by simp only [List.length_nil] at hLlen; omega
    exact (List.length_eq_zero_iff.mp this).symm
  | cons a L ih =>
    cases M with
    | nil => simp only [List.length_cons, List.length_nil] at hLlen hMlen; omega
    | cons b M =>
      have hmL : (missingLabels S (a :: L)).Nonempty :=
        missingLabels_nonempty (by simp only [List.length_cons] at hLlen ⊢; omega)
      have hmM : (missingLabels S (b :: M)).Nonempty :=
        missingLabels_nonempty (by simp only [List.length_cons] at hMlen ⊢; omega)
      have hmiss : missingLabels S (a :: L) = missingLabels S (b :: M) := by
        rw [missingLabels_eq_leaves S (a :: L) hLlen hL,
          missingLabels_eq_leaves S (b :: M) hMlen hM, heq]
      let v := missingLabel S (a :: L) hmL
      have hvM : v = missingLabel S (b :: M) hmM := by
        dsimp [v, missingLabel]
        congr 1
      have hab : a = b := by
        have ha : (decode S (a :: L)).Adj v a :=
          (decode_adj_leaf_iff S a L hmL hL a).mpr rfl
        rw [heq, hvM] at ha
        exact (decode_adj_leaf_iff S b M hmM hM a).mp ha
      subst b
      have hvS : v ∈ S := missingLabel_mem hmL
      have hvL : v ∉ a :: L := missingLabel_not_mem hmL
      have hvM' : v ∉ a :: M := by rw [hvM]; exact missingLabel_not_mem hmM
      have htailL : ∀ w ∈ L, w ∈ S.erase v := by
        intro w hw
        exact Finset.mem_erase.mpr
          ⟨fun hwv ↦ hvL (by simp [← hwv, hw]), hL w (by simp [hw])⟩
      have htailM : ∀ w ∈ M, w ∈ S.erase v := by
        intro w hw
        exact Finset.mem_erase.mpr
          ⟨fun hwv ↦ hvM' (by simp [← hwv, hw]), hM w (by simp [hw])⟩
      have heq' : decode (S.erase v) L = decode (S.erase v) M := by
        apply sup_edge_left_cancel (a := a)
          (decode_supported _ _ htailL) (decode_supported _ _ htailM)
        rw [decode, dif_pos hmL, decode, dif_pos hmM] at heq
        simpa only [← hvM] using heq
      have hsizeL : (S.erase v).card = L.length + 2 := by
        rw [Finset.card_erase_of_mem hvS]
        simp only [List.length_cons] at hLlen
        omega
      have hsizeM : (S.erase v).card = M.length + 2 := by
        rw [Finset.card_erase_of_mem hvS]
        simp only [List.length_cons] at hMlen
        omega
      exact congrArg (List.cons a) (ih (S.erase v) M hsizeL hsizeM htailL htailM heq')

/-- A function-valued Prüfer word, decoded as a graph on all `n` labels. -/
def decodeWord {n : ℕ} (f : Fin (n - 2) → Fin n) : SimpleGraph (Fin n) :=
  decode Finset.univ (List.ofFn f)

theorem decodeWord_isTree {n : ℕ} (hn : 2 ≤ n) (f : Fin (n - 2) → Fin n) :
    (decodeWord f).IsTree := by
  have h := decode_isTree_induce (Finset.univ : Finset (Fin n)) (List.ofFn f)
    (by simp; omega) (by simp)
  rw [Finset.coe_univ] at h
  exact (SimpleGraph.induceUnivIso (decodeWord f)).isTree_iff.mp h

theorem decodeWord_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (decodeWord : (Fin (n - 2) → Fin n) → SimpleGraph (Fin n)) := by
  intro f g hfg
  apply List.ofFn_injective
  exact decode_injective Finset.univ (List.ofFn f) (List.ofFn g)
    (by simp; omega) (by simp; omega) (by simp) (by simp) hfg

/-- The tree-counting lower bound furnished by the injective Prüfer construction.
Surjectivity is not needed for the critical lower-tail argument. -/
theorem pow_le_card_trees {n : ℕ} (hn : 2 ≤ n) :
    n ^ (n - 2) ≤ Fintype.card {G : SimpleGraph (Fin n) // G.IsTree} := by
  let f : (Fin (n - 2) → Fin n) → {G : SimpleGraph (Fin n) // G.IsTree} :=
    fun w ↦ ⟨decodeWord w, decodeWord_isTree hn w⟩
  have hf : Function.Injective f := fun w z hwz ↦
    decodeWord_injective hn (congrArg Subtype.val hwz)
  simpa using Fintype.card_le_of_injective f hf

end

end Erdos745.Prufer
