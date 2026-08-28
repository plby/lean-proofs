import ErdosProblems.Erdos577.FirstPawModel
import ErdosProblems.Erdos577.PawEncoding
import ErdosProblems.Erdos577.QuadModel

/-! Exact cyclic labels, normalized paw rows, and positive obstruction transport. -/

namespace Erdos577.FirstPaw

open Finset Function
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def normalizedPaw (p : Paw G) (swap : Bool) : Paw G := if swap then p.swapNoncentral else p

lemma normalizedPaw_support (p : Paw G) (swap : Bool) :
    (normalizedPaw p swap).support = p.support := by
  cases swap <;> simp [normalizedPaw, Paw.swapNoncentral_support]

lemma normalizedPaw_triangle (p : Paw G) (swap : Bool) :
    (normalizedPaw p swap).triangle = p.triangle := by
  cases swap <;> simp [normalizedPaw, Paw.swapNoncentral_triangle]

omit [DecidableEq V] in
lemma normalizedPaw_leaf (p : Paw G) (swap : Bool) :
    (normalizedPaw p swap).leaf = p.leaf := by cases swap <;> rfl

omit [DecidableEq V] in
lemma normalizedPaw_center (p : Paw G) (swap : Bool) :
    (normalizedPaw p swap).center = p.center := by cases swap <;> rfl

variable [DecidableRel G.Adj]

def orderedQuad (q : Quadrilateral G) (cols : Fin 4 ↪ Fin 4)
    (hc : CycleOrder (Unattached.diagonal q) cols) : Quadrilateral G :=
  Quadrilateral.ofEdges (cols.trans q.toEmbedding)
    (fun i ↦ (q.model_adj_iff (cols i) (cols (i + 1))).mp (hc i))

omit [DecidableEq V] in
@[simp] lemma orderedQuad_apply (q : Quadrilateral G) (cols : Fin 4 ↪ Fin 4)
    (hc : CycleOrder (Unattached.diagonal q) cols) (i : Fin 4) :
    orderedQuad q cols hc i = q (cols i) := rfl

lemma orderedQuad_support (q : Quadrilateral G) (cols : Fin 4 ↪ Fin 4)
    (hc : CycleOrder (Unattached.diagonal q) cols) :
    (orderedQuad q cols hc).support = q.support := by
  apply eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨i, rfl⟩ := ((orderedQuad q cols hc).mem_support v).mp hv
    exact (q.mem_support _).mpr ⟨cols i, rfl⟩
  · simp only [Quadrilateral.card_support, le_refl]

omit [DecidableEq V] in
lemma quadAdj_ordered_iff (q : Quadrilateral G) (cols : Fin 4 ↪ Fin 4)
    (hc : CycleOrder (Unattached.diagonal q) cols) (i j : Fin 4) :
    quadAdj (Unattached.diagonal q) cols i j ↔
      G.Adj (orderedQuad q cols hc i) (orderedQuad q cols hc j) :=
  q.model_adj_iff (cols i) (cols j)

lemma Positive.transport (p : Paw G) (q : Quadrilateral G) (hd : Disjoint p.support q.support)
    (h : Positive (Unattached.diagonal q) (PawEncoding.encoded p q).val) :
    LocalFactor G (p.support ∪ q.support) ∨
      StrictImprovement G (p.support ∪ q.support) (edgeCount G q.support) ∨
      TwoEdgeReduction G (p.support ∪ q.support) (edgeCount G q.support + 2) := by
  rcases h with h | h | h
  · left
    have hg := h.image (PawEncoding.modelCopy p q hd)
    rw [PawEncoding.modelCopy_image] at hg
    exact hg
  · right
    left
    have hg := h.image (PawEncoding.modelCopy p q hd)
    rw [PawEncoding.modelCopy_image, Unattached.oldEdges_diagonal] at hg
    exact hg
  · right
    right
    have hg := h.image (PawEncoding.modelCopy p q hd)
    rw [PawEncoding.modelCopy_image, Unattached.oldEdges_diagonal] at hg
    exact hg

omit [DecidableEq V] in
lemma bit_encoded (p : Paw G) (q : Quadrilateral G) (swap : Bool) (cols : Fin 4 ↪ Fin 4)
    (hc : CycleOrder (Unattached.diagonal q) cols) (i j : Fin 4) :
    bit (PawEncoding.encoded p q).val swap cols i j =
      decide (G.Adj ((normalizedPaw p swap).vertices i) (orderedQuad q cols hc j)) := by
  rw [bit, PawEncoding.encoded_bit]
  cases swap <;> rfl

lemma rowCount_encoded (p : Paw G) (q : Quadrilateral G) (swap : Bool) (cols : Fin 4 ↪ Fin 4)
    (hc : CycleOrder (Unattached.diagonal q) cols) (i : Fin 4) :
    rowCount (PawEncoding.encoded p q).val swap cols i =
      degreeIn G ((normalizedPaw p swap).vertices i) q.support := by
  let q' := orderedQuad q cols hc
  have hinj : Injective (q' : Fin 4 → V) := q'.injective
  have he := degreeIn_image G ((normalizedPaw p swap).vertices i) univ q' hinj
  change degreeIn G ((normalizedPaw p swap).vertices i) q'.support = _ at he
  have hcount : rowCount (PawEncoding.encoded p q).val swap cols i =
      degreeIn G ((normalizedPaw p swap).vertices i) q'.support := by
    rw [he, rowCount]
    apply sum_congr rfl
    intro j _
    rw [bit_encoded p q swap cols hc]
    change (decide (G.Adj ((normalizedPaw p swap).vertices i) (q' j))).toNat =
      if G.Adj ((normalizedPaw p swap).vertices i) (q' j) then 1 else 0
    by_cases h : G.Adj ((normalizedPaw p swap).vertices i) (q' j) <;>
      simp only [h, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, if_true, if_false]
  simpa only [q', orderedQuad_support] using hcount

omit [DecidableEq V] in
lemma ExactRows.transport (p : Paw G) (q : Quadrilateral G) (swap : Bool)
    (cols : Fin 4 ↪ Fin 4) (hc : CycleOrder (Unattached.diagonal q) cols) (rows : Fin 4 → ℕ)
    (h : ExactRows (PawEncoding.encoded p q).val swap cols rows) (i j : Fin 4) :
    G.Adj ((normalizedPaw p swap).vertices i) (orderedQuad q cols hc j) ↔
      (rows i).testBit j.val = true := by
  have he := h i j
  rw [bit_encoded p q swap cols hc] at he
  exact ⟨fun h ↦ by rw [← he]; exact decide_eq_true h,
    fun h ↦ of_decide_eq_true (he.trans h)⟩

omit [DecidableEq V] in
lemma OnlyFirst.transport (q : Quadrilateral G) (cols : Fin 4 ↪ Fin 4)
    (hc : CycleOrder (Unattached.diagonal q) cols) (h : OnlyFirst (Unattached.diagonal q) cols) :
    G.Adj (orderedQuad q cols hc 0) (orderedQuad q cols hc 2) ∧
      ¬G.Adj (orderedQuad q cols hc 1) (orderedQuad q cols hc 3) :=
  ⟨(quadAdj_ordered_iff q cols hc 0 2).mp h.1,
    fun he ↦ h.2 ((quadAdj_ordered_iff q cols hc 1 3).mpr he)⟩

variable [Fintype V]

lemma positive_excluded {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {b : Finset V} (hb : b ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = b) :
    ¬Positive (Unattached.diagonal q) (PawEncoding.encoded p q).val := by
  intro hpos
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    apply disjoint_left.mpr
    intro v hv hvb
    exact (mem_sdiff.mp (c.complementPartition.block_subset hb hvb)).2 hv
  have hout := hpos.transport p q hd
  rw [hp, hq] at hout
  rcases hout with hf | hg | hg
  · exact c.no_local_factor hcard hn hb hf
  · exact hc.no_strict_improvement hb hg
  · exact hc.no_two_edge_gain hcard hdeg hn hb hg

end Erdos577.FirstPaw
