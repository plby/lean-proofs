/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.RootedModels

/-!
# Forward-saturated separators pointing to a bramble haven

Finite maximization and the checked rooted-model transport implement the
extremal step of the Leaf--Seymour tree construction. A saturated separator
has a connected right exclusive side, and every boundary vertex has a
neighbor there. Inserting a vertex from this region preserves forward
minimality at the next order.
-/

namespace Erdos73
open Erdos73Infrastructure.SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
variable {β : Finset (Finset V)} {q : ℕ}

lemma IsVertexSeparation.insert_left {A B : Finset V}
    (hAB : IsVertexSeparation G A B) {u : V} (hu : u ∈ B) :
    IsVertexSeparation G (insert u A) B := by
  constructor
  · ext v
    have hv := hAB.mem_left_or_right v
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_univ, iff_true]
    tauto
  · intro a b ha haB hb hbA hab
    have haA : a ∈ A := (Finset.mem_insert.mp ha).resolve_left (fun heq ↦ haB (heq ▸ hu))
    exact hAB.2 haA haB hb (fun h ↦ hbA (Finset.mem_insert_of_mem h)) hab

namespace BrambleHaven

def PointsTo (h : BrambleHaven G β q) (A B : Finset V) : Prop :=
  ∃ hsmall : (A ∩ B).card < q, h.region ⟨A ∩ B, hsmall⟩ ⊆ B

lemma pointsTo_exclusive (h : BrambleHaven G β q) {A B : Finset V}
    {hsmall : (A ∩ B).card < q} (hB : h.region ⟨A ∩ B, hsmall⟩ ⊆ B) :
    h.region ⟨A ∩ B, hsmall⟩ ⊆ B \ A := by
  intro v hv
  refine Finset.mem_sdiff.mpr ⟨hB hv, ?_⟩
  intro hvA
  exact Finset.disjoint_left.mp (h.avoids ⟨A ∩ B, hsmall⟩) hv
    (Finset.mem_inter.mpr ⟨hvA, hB hv⟩)

lemma pointsTo_of_touches_right (h : BrambleHaven G β q) {A B T : Finset V}
    (hsep : IsVertexSeparation G A B) (hsmall : (A ∩ B).card < q)
    (hT : T ⊆ B \ A) (htouch : FinsetTouches G (h.region ⟨A ∩ B, hsmall⟩) T) :
    h.PointsTo A B := by
  refine ⟨hsmall, ?_⟩
  rcases connected_finset_subset_side_of_disjoint_separator hsep
    (h.connected ⟨A ∩ B, hsmall⟩) (h.avoids ⟨A ∩ B, hsmall⟩) with hA | hB
  · exact (not_finsetTouches_of_separation_sides hsep hA hT htouch).elim
  · exact hB.trans Finset.sdiff_subset

lemma pointsTo_of_forward (h : BrambleHaven G β q) {A B C D : Finset V}
    (hAB : IsVertexSeparation G A B) (hAC : A ⊆ C) (hDB : D ⊆ B)
    (hCD : h.PointsTo C D) (hsmall : (A ∩ B).card < q) : h.PointsTo A B := by
  obtain ⟨hsmallCD, hregion⟩ := hCD
  have hright : h.region ⟨C ∩ D, hsmallCD⟩ ⊆ B \ A := by
    intro v hv
    have hv' := Finset.mem_sdiff.mp (h.pointsTo_exclusive hregion hv)
    exact Finset.mem_sdiff.mpr ⟨hDB hv'.1, fun ha ↦ hv'.2 (hAC ha)⟩
  exact h.pointsTo_of_touches_right hAB hsmall hright
    (h.touches ⟨A ∩ B, hsmall⟩ ⟨C ∩ D, hsmallCD⟩)

/-- No forward separation pointing to the haven has smaller order. -/
def ForwardMinimal (h : BrambleHaven G β q) (A B : Finset V) : Prop :=
  ∀ C D : Finset V, IsVertexSeparation G C D → A ⊆ C → D ⊆ B →
    h.PointsTo C D → (A ∩ B).card ≤ (C ∩ D).card

/-- No distinct forward separation pointing to the haven has at most this order. -/
def ForwardSaturated (h : BrambleHaven G β q) (A B : Finset V) : Prop :=
  ∀ C D : Finset V, IsVertexSeparation G C D → A ⊆ C → D ⊆ B →
    h.PointsTo C D → (C ∩ D).card ≤ (A ∩ B).card → C = A ∧ D = B

theorem exists_forwardSaturated (h : BrambleHaven G β q) {A B : Finset V}
    (hAB : IsVertexSeparation G A B) (hpoint : h.PointsTo A B)
    (hmin : h.ForwardMinimal A B) :
    ∃ C D : Finset V, IsVertexSeparation G C D ∧ A ⊆ C ∧ D ⊆ B ∧
      (C ∩ D).card = (A ∩ B).card ∧ h.PointsTo C D ∧ h.ForwardSaturated C D := by
  let candidates : Finset (Finset V × Finset V) := Finset.univ.filter fun p ↦
    IsVertexSeparation G p.1 p.2 ∧ A ⊆ p.1 ∧ p.2 ⊆ B ∧
      (p.1 ∩ p.2).card = (A ∩ B).card ∧ h.PointsTo p.1 p.2
  have hmem (C D : Finset V) : (C, D) ∈ candidates ↔
      IsVertexSeparation G C D ∧ A ⊆ C ∧ D ⊆ B ∧
        (C ∩ D).card = (A ∩ B).card ∧ h.PointsTo C D := by
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
  obtain ⟨⟨C, D⟩, hCD, hmax⟩ := candidates.exists_max_image
    (fun p ↦ p.1.card + (Finset.univ \ p.2).card)
    ⟨(A, B), (hmem A B).mpr ⟨hAB, fun _ ↦ id, fun _ ↦ id, rfl, hpoint⟩⟩
  obtain ⟨hsep, hAC, hDB, hcard, hpoints⟩ := (hmem C D).mp hCD
  refine ⟨C, D, hsep, hAC, hDB, hcard, hpoints, ?_⟩
  intro E F hEF hCE hFD hEFpoint hEFcard
  have hcardEF : (E ∩ F).card = (A ∩ B).card := by
    apply le_antisymm (hEFcard.trans hcard.le)
    exact hmin E F hEF (hAC.trans hCE) (hFD.trans hDB) hEFpoint
  have hmaxEF := hmax (E, F) ((hmem E F).mpr
    ⟨hEF, hAC.trans hCE, hFD.trans hDB, hcardEF, hEFpoint⟩)
  change E.card + (Finset.univ \ F).card ≤ C.card + (Finset.univ \ D).card at hmaxEF
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ F),
    Finset.card_sdiff_of_subset (Finset.subset_univ D)] at hmaxEF
  have hCEcard := Finset.card_le_card hCE
  have hFDcard := Finset.card_le_card hFD
  have hFuniv := Finset.card_le_card (Finset.subset_univ F)
  have hDuniv := Finset.card_le_card (Finset.subset_univ D)
  exact ⟨(Finset.eq_of_subset_of_card_le hCE (by omega)).symm,
    Finset.eq_of_subset_of_card_le hFD (by omega)⟩

theorem exists_saturated_rootedModel (h : BrambleHaven G β q) {A B : Finset V}
    {I : Type*} {H : SimpleGraph I} (M : LeftRootedModel H G A B)
    (hAB : IsVertexSeparation G A B) (hpoint : h.PointsTo A B)
    (hmin : h.ForwardMinimal A B) :
    ∃ C D : Finset V, IsVertexSeparation G C D ∧ A ⊆ C ∧ D ⊆ B ∧
      (C ∩ D).card = (A ∩ B).card ∧ h.PointsTo C D ∧ h.ForwardSaturated C D ∧
      Nonempty (LeftRootedModel H G C D) := by
  obtain ⟨C, D, hCD, hAC, hDB, hcard, hpoints, hsat⟩ :=
    h.exists_forwardSaturated hAB hpoint hmin
  refine ⟨C, D, hCD, hAC, hDB, hcard, hpoints, hsat,
    M.exists_transport_of_nested hAB hCD hAC hDB rfl hcard ?_⟩
  intro E F hEF hAE hEC hDF hFB
  by_contra hlt
  have hlt' := Nat.lt_of_not_ge hlt
  obtain ⟨hsmallAB, _⟩ := hpoint
  have hpointsEF := h.pointsTo_of_forward hEF hEC hDF hpoints (hlt'.trans hsmallAB)
  exact hlt (hmin E F hEF hAE hFB hpointsEF)

lemma right_eq_region_of_saturated (h : BrambleHaven G β q) {A B : Finset V}
    (hpoint : h.PointsTo A B) (hsat : h.ForwardSaturated A B)
    (hsmall : (A ∩ B).card < q) : B \ A = h.region ⟨A ∩ B, hsmall⟩ := by
  obtain ⟨_, hregB⟩ := hpoint
  let R := h.region ⟨A ∩ B, hsmall⟩
  let S := A ∩ B
  have hR : R ⊆ B \ A := h.pointsTo_exclusive hregB
  have hdisj : Disjoint R S := h.avoids ⟨A ∩ B, hsmall⟩
  have hboundary : externalNeighborhood G R ⊆ S := h.boundary ⟨A ∩ B, hsmall⟩
  have hsep : IsVertexSeparation G (Finset.univ \ R) (R ∪ S) := by
    constructor
    · ext v
      by_cases hvR : v ∈ R <;> simp [hvR]
    · intro a b ha haRS hb hbR hab
      have hb : b ∈ R := by
        simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] using hbR
      have haN : a ∈ externalNeighborhood G R :=
        (mem_externalNeighborhood G R a).mpr ⟨(Finset.mem_sdiff.mp ha).2, b, hb, hab⟩
      exact haRS (Finset.mem_union.mpr (Or.inr (hboundary haN)))
  have hinter : (Finset.univ \ R) ∩ (R ∪ S) = S := by
    ext v
    have hnot : v ∈ S → v ∉ R := fun hvS hvR ↦ Finset.disjoint_left.mp hdisj hvR hvS
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_union]
    tauto
  have hpoint' : h.PointsTo (Finset.univ \ R) (R ∪ S) := by
    refine ⟨by simpa only [hinter] using hsmall, ?_⟩
    have hid : (⟨(Finset.univ \ R) ∩ (R ∪ S), by simpa only [hinter] using hsmall⟩ :
        {X : Finset V // X.card < q}) = ⟨A ∩ B, hsmall⟩ := Subtype.ext hinter
    rw [hid]
    exact Finset.subset_union_left
  obtain ⟨heqA, heqB⟩ := hsat (Finset.univ \ R) (R ∪ S) hsep
    (by
      intro v hvA
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,
        fun hvR ↦ (Finset.mem_sdiff.mp (hR hvR)).2 hvA⟩)
    (by
      intro v hv
      rcases Finset.mem_union.mp hv with hvR | hvS
      · exact (Finset.mem_sdiff.mp (hR hvR)).1
      · exact (Finset.mem_inter.mp hvS).2)
    hpoint' (by rw [hinter])
  change B \ A = R
  rw [← heqA, ← heqB]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and, not_not]
  tauto

lemma saturated_right_properties (h : BrambleHaven G β q) {A B : Finset V}
    (hAB : IsVertexSeparation G A B) (hpoint : h.PointsTo A B)
    (hsat : h.ForwardSaturated A B) :
    (G.induce ((B \ A : Finset V) : Set V)).Connected ∧
      ∀ v ∈ A ∩ B, ∃ u ∈ B \ A, G.Adj v u := by
  obtain ⟨hsmall, hreg⟩ := hpoint
  have heq := h.right_eq_region_of_saturated ⟨hsmall, hreg⟩ hsat hsmall
  refine ⟨by rw [heq]; exact h.connected _, ?_⟩
  intro v hv
  by_contra hnone
  have hvA := (Finset.mem_inter.mp hv).1
  have hvB := (Finset.mem_inter.mp hv).2
  have hsep : IsVertexSeparation G A (B.erase v) := by
    constructor
    · ext x
      have hx := hAB.mem_left_or_right x
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_univ, iff_true]
      by_cases hxx : x = v
      · exact Or.inl (hxx ▸ hvA)
      · tauto
    · intro a b ha haB hb hbA hab
      by_cases hav : a = v
      · exact hnone ⟨b, Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hb).2, hbA⟩, hav ▸ hab⟩
      · exact hAB.2 ha (fun haB' ↦ haB (Finset.mem_erase.mpr ⟨hav, haB'⟩))
          (Finset.mem_erase.mp hb).2 hbA hab
  have hinter : A ∩ B.erase v = (A ∩ B).erase v := by ext x; simp; tauto
  have hcard : (A ∩ B.erase v).card < (A ∩ B).card := by
    rw [hinter, Finset.card_erase_of_mem hv]
    exact Nat.sub_one_lt (Finset.card_pos.mpr ⟨v, hv⟩).ne'
  have hright : h.region ⟨A ∩ B, hsmall⟩ ⊆ B.erase v \ A := by
    intro x hx
    have hx' : x ∈ B \ A := by rw [heq]; exact hx
    have hxB := (Finset.mem_sdiff.mp hx').1
    have hxA := (Finset.mem_sdiff.mp hx').2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr
      ⟨fun hxx ↦ hxA (hxx ▸ hvA), hxB⟩, hxA⟩
  have hpoint' := h.pointsTo_of_touches_right hsep (hcard.trans hsmall) hright
    (h.touches ⟨A ∩ B.erase v, hcard.trans hsmall⟩ ⟨A ∩ B, hsmall⟩)
  have heqB := (hsat A (B.erase v) hsep (fun _ ↦ id) (Finset.erase_subset v B)
    hpoint' hcard.le).2
  have hvErase : v ∈ B.erase v := by rw [heqB]; exact hvB
  exact (Finset.mem_erase.mp hvErase).1 rfl

lemma pointsTo_insert_left (h : BrambleHaven G β q) {A B : Finset V} {u : V}
    (hpoint : h.PointsTo A B)
    (hsmall : (insert u A ∩ B).card < q) : h.PointsTo (insert u A) B := by
  obtain ⟨hABsmall, hreg⟩ := hpoint
  refine ⟨hsmall, (h.antitone ⟨A ∩ B, hABsmall⟩ ⟨insert u A ∩ B, hsmall⟩
    (Finset.inter_subset_inter (Finset.subset_insert u A) (fun _ ↦ id))).trans hreg⟩

lemma saturated_insert_left_minimal (h : BrambleHaven G β q) {A B : Finset V} {u : V}
    (hsat : h.ForwardSaturated A B) (hu : u ∈ B \ A) :
    h.ForwardMinimal (insert u A) B := by
  intro C D hCD hAC hDB hpoint
  by_contra hnot
  have hcard : (insert u A ∩ B).card = (A ∩ B).card + 1 := by
    rw [Finset.insert_inter_of_mem (Finset.mem_sdiff.mp hu).1,
      Finset.card_insert_of_notMem (fun hv ↦ (Finset.mem_sdiff.mp hu).2
        (Finset.mem_inter.mp hv).1)]
  have hle : (C ∩ D).card ≤ (A ∩ B).card := by omega
  have hCA := (hsat C D hCD ((Finset.subset_insert u A).trans hAC) hDB hpoint hle).1
  exact (Finset.mem_sdiff.mp hu).2 (hCA ▸ hAC (Finset.mem_insert_self u A))

lemma forwardSaturated_minimal (h : BrambleHaven G β q) {A B : Finset V}
    (hsat : h.ForwardSaturated A B) : h.ForwardMinimal A B := by
  intro C D hCD hAC hDB hpoint
  by_contra hnot
  obtain ⟨rfl, rfl⟩ := hsat C D hCD hAC hDB hpoint (Nat.le_of_lt (Nat.lt_of_not_ge hnot))
  exact hnot le_rfl

end BrambleHaven
end
end Erdos73

#print axioms Erdos73.BrambleHaven.exists_saturated_rootedModel
