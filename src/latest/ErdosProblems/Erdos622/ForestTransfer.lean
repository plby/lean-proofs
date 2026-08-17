/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.GoodCut

/-!
# Transferring linear forests across a balancing move

In the almost-bipartite argument a small set of vertices is moved from one
side of a cut to the other in order to balance the two sides.  A linear
forest supported on the enlarged side is converted back to a forest on the
original side by deleting every edge incident with a moved vertex.  Since a
linear forest has maximum degree two, at most twice the number of moved
vertices is lost.

This file states the argument for arbitrary finite vertex sets.  In the
sampled application, `T` is the finset of sampled moved vertices, whose
cardinality is `(S ∩ T_ambient).card`.  The generic formulation avoids any
dependence on the particular subtype presentation used for induced samples.
-/

open scoped SimpleGraph

namespace Erdos622
namespace ForestTransfer

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edges of `F` incident with at least one vertex of `T`. -/
noncomputable def incidentEdges (F : SimpleGraph V) (T : Finset V) :
    Finset (Sym2 V) :=
  T.biUnion fun v => F.incidenceFinset v

/-- Delete every edge incident with a vertex of `T`. -/
noncomputable def eraseIncident (F : SimpleGraph V) (T : Finset V) :
    SimpleGraph V :=
  F.deleteEdges (incidentEdges F T : Set (Sym2 V))

theorem incidentEdges_subset_edgeFinset (F : SimpleGraph V) (T : Finset V) :
    incidentEdges F T ⊆ F.edgeFinset := by
  classical
  intro e he
  obtain ⟨v, hvT, hev⟩ := Finset.mem_biUnion.mp he
  exact F.incidenceFinset_subset v hev

@[simp]
theorem edgeSet_eraseIncident (F : SimpleGraph V) (T : Finset V) :
    (eraseIncident F T).edgeSet =
      F.edgeSet \ (incidentEdges F T : Set (Sym2 V)) := by
  classical
  exact SimpleGraph.edgeSet_deleteEdges _

theorem eraseIncident_le (F : SimpleGraph V) (T : Finset V) :
    eraseIncident F T ≤ F := by
  classical
  exact SimpleGraph.deleteEdges_le _

/-- No vertex of `T` remains in the support after all incident edges are
deleted.  The stronger conclusion also records that no new support was
created. -/
theorem support_eraseIncident_subset_sdiff (F : SimpleGraph V) (T : Finset V) :
    (eraseIncident F T).support ⊆ F.support \ (T : Set V) := by
  classical
  intro v hv
  refine ⟨SimpleGraph.support_mono (eraseIncident_le F T) hv, ?_⟩
  intro hvT
  obtain ⟨w, hvw⟩ := (SimpleGraph.mem_support (eraseIncident F T)).mp hv
  have hvw' : F.Adj v w ∧
      s(v, w) ∉ (incidentEdges F T : Set (Sym2 V)) := by
    exact SimpleGraph.deleteEdges_adj.mp hvw
  have hnot : s(v, w) ∉ (incidentEdges F T : Finset (Sym2 V)) := by
    simpa using hvw'.2
  apply hnot
  exact Finset.mem_biUnion.mpr
    ⟨v, hvT, (F.mem_incidenceFinset v s(v, w)).mpr
      ((F.mem_incidenceSet v w).mpr hvw'.1)⟩

/-- The number of edges incident with `T` is at most the sum of the degrees
over `T`. -/
theorem card_incidentEdges_le_sum_degree (F : SimpleGraph V) (T : Finset V) :
    (incidentEdges F T).card ≤ ∑ v ∈ T, F.degree v := by
  classical
  calc
    (incidentEdges F T).card
        ≤ ∑ v ∈ T, (F.incidenceFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ T, F.degree v := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact F.card_incidenceFinset_eq_degree v

/-- A maximum-degree-two graph has at most two deleted incidences per moved
vertex. -/
theorem card_incidentEdges_le_two_mul (F : SimpleGraph V) (T : Finset V)
    (hdegree : ∀ v, F.degree v ≤ 2) :
    (incidentEdges F T).card ≤ 2 * T.card := by
  classical
  calc
    (incidentEdges F T).card ≤ ∑ v ∈ T, F.degree v :=
      card_incidentEdges_le_sum_degree F T
    _ ≤ ∑ _v ∈ T, 2 := Finset.sum_le_sum fun v _hv => hdegree v
    _ = 2 * T.card := by simp [Nat.mul_comm]

/-- The exact edge loss is the cardinality of the deleted incident-edge
union.  Edge sets and `Set.ncard` are used here to avoid dependence on a
particular `Fintype edgeSet` instance. -/
theorem edgeLoss_eraseIncident_eq (F : SimpleGraph V) (T : Finset V) :
    F.edgeSet.ncard - (eraseIncident F T).edgeSet.ncard =
      (incidentEdges F T).card := by
  classical
  have hsub : (incidentEdges F T : Set (Sym2 V)) ⊆ F.edgeSet := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mp
      (incidentEdges_subset_edgeFinset F T (by simpa using he))
  rw [edgeSet_eraseIncident]
  have hsum := Set.ncard_sdiff_add_ncard_of_subset hsub
  rw [Set.ncard_coe_finset] at hsum
  omega

/-- Deleting all edges incident with `T` from a linear forest loses at most
`2 * T.card` edges. -/
theorem edgeLoss_eraseIncident_le (F : SimpleGraph V) (T : Finset V)
    (hF : LinearForest F) :
    F.edgeSet.ncard - (eraseIncident F T).edgeSet.ncard ≤ 2 * T.card := by
  rw [edgeLoss_eraseIncident_eq]
  exact card_incidentEdges_le_two_mul F T hF.2

/-- Direct witness form of the transfer lemma.  If the old support is
contained in `X ∪ T`, erasing incidences of `T` leaves a linear forest
supported on `X`, with at most two lost edges per moved vertex. -/
theorem LinearForest.exists_transfer {F : SimpleGraph V} {X T : Finset V}
    (hF : LinearForest F) (hsupport : F.support ⊆ ((X ∪ T : Finset V) : Set V)) :
    ∃ H : SimpleGraph V,
      H ≤ F ∧ LinearForest H ∧ H.support ⊆ (X : Set V) ∧
        F.edgeSet.ncard - H.edgeSet.ncard ≤ 2 * T.card := by
  refine ⟨eraseIncident F T, eraseIncident_le F T,
    hF.anti (eraseIncident_le F T), ?_, edgeLoss_eraseIncident_le F T hF⟩
  intro v hv
  have hv' := support_eraseIncident_subset_sdiff F T hv
  have hvXT : v ∈ X ∪ T := by
    simpa using hsupport hv'.1
  rw [Finset.mem_union] at hvXT
  rcases hvXT with hvX | hvT
  · exact hvX
  · exact False.elim (hv'.2 hvT)

/-- Property-level form used in the good-cut count.  A witness supported in
`Z ⊆ X ∪ T` transfers to `X`, after reducing the guaranteed edge count
by at most `2 * T.card`. -/
theorem ContainsLinearForestWith.transfer_moved
    {G : SimpleGraph V} {X T Z : Finset V} {r : ℕ}
    (h : ContainsLinearForestWith G Z r) (hZ : Z ⊆ X ∪ T) :
    ContainsLinearForestWith G X (r - 2 * T.card) := by
  obtain ⟨F, hFG, hlin, hsupp, hr⟩ := h
  have hZset : (Z : Set V) ⊆ ((X ∪ T : Finset V) : Set V) := by
    intro v hv
    have hvZ : v ∈ Z := by simpa using hv
    have hvXT : v ∈ X ∪ T := hZ hvZ
    exact hvXT
  obtain ⟨H, hHF, hHlin, hHsupp, hloss⟩ :=
    LinearForest.exists_transfer hlin (X := X) (T := T)
      (hsupp.trans hZset)
  refine ⟨H, hHF.trans hFG, hHlin, hHsupp, ?_⟩
  have hFcard : F.edgeSet.ncard = F.edgeFinset.card := by
    rw [← F.coe_edgeFinset, Set.ncard_coe_finset]
  have hHcard : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [← H.coe_edgeFinset, Set.ncard_coe_finset]
  rw [hFcard, hHcard] at hloss
  omega

/-- Convenient special case when the enlarged support set is literally
`X ∪ T`. -/
theorem ContainsLinearForestWith.transfer_union
    {G : SimpleGraph V} {X T : Finset V} {r : ℕ}
    (h : ContainsLinearForestWith G (X ∪ T) r) :
    ContainsLinearForestWith G X (r - 2 * T.card) :=
  ContainsLinearForestWith.transfer_moved h Finset.Subset.rfl

/-- Safe transfer on the side that shrinks: support in `A \ T` is already
support in `A`, with no edge loss. -/
theorem ContainsLinearForestWith.transfer_sdiff
    {G : SimpleGraph V} {A T : Finset V} {r : ℕ}
    (h : ContainsLinearForestWith G (A \ T) r) :
    ContainsLinearForestWith G A r :=
  ContainsLinearForestWith.mono_vertexSet h Finset.sdiff_subset

/-- Equality-oriented form of the safe shrinking-side transfer. -/
theorem ContainsLinearForestWith.transfer_left
    {G : SimpleGraph V} {A A₀ T : Finset V} {r : ℕ}
    (hA₀ : A₀ = A \ T) (h : ContainsLinearForestWith G A₀ r) :
    ContainsLinearForestWith G A r := by
  subst A₀
  exact ContainsLinearForestWith.transfer_sdiff h

/-- Equality-oriented form of the enlarged-side transfer. -/
theorem ContainsLinearForestWith.transfer_right
    {G : SimpleGraph V} {B B₀ T : Finset V} {r : ℕ}
    (hB₀ : B₀ = B ∪ T) (h : ContainsLinearForestWith G B₀ r) :
    ContainsLinearForestWith G B (r - 2 * T.card) := by
  subst B₀
  exact ContainsLinearForestWith.transfer_union h

/-! ## Sampled-cut interface -/

/-- The vertices of an ambient finset that survive in a sample, regarded as
vertices of the induced graph on that sample.  This is deliberately the
same expression as `restrictedPart` in the almost-bipartite assembly; that
module can bridge the two definitions by simplification without creating an
import cycle. -/
def sampledPart (S A : Finset V) : Finset (S : Set V) :=
  S.attach.filter fun v => v.1 ∈ A

omit [Fintype V] in
@[simp] theorem mem_sampledPart {S A : Finset V} {v : (S : Set V)} :
    v ∈ sampledPart S A ↔ v.1 ∈ A := by
  simp [sampledPart]

omit [Fintype V] in
theorem sampledPart_mono {S A B : Finset V} (hAB : A ⊆ B) :
    sampledPart S A ⊆ sampledPart S B := by
  intro v hv
  exact mem_sampledPart.mpr (hAB (mem_sampledPart.mp hv))

omit [Fintype V] in
theorem sampledPart_union (S A B : Finset V) :
    sampledPart S (A ∪ B) = sampledPart S A ∪ sampledPart S B := by
  ext v
  simp only [mem_sampledPart, Finset.mem_union]

omit [Fintype V] in
/-- Cardinality of the sampled copy of an ambient finset. -/
theorem card_sampledPart (S A : Finset V) :
    (sampledPart S A).card = (S ∩ A).card := by
  classical
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    exact Finset.mem_inter.mpr ⟨x.property, mem_sampledPart.mp hx⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro y hy
    exact ⟨⟨y, (Finset.mem_inter.mp hy).1⟩,
      mem_sampledPart.mpr (Finset.mem_inter.mp hy).2, rfl⟩

/-- Safe sampled transfer on the side changed from `A` to `A \ T`.
No edges are lost. -/
theorem ContainsLinearForestWith.transfer_sampled_left
    {S A A₀ T : Finset V} {G : SimpleGraph (S : Set V)} {r : ℕ}
    (hA₀ : A₀ = A \ T)
    (h : ContainsLinearForestWith G (sampledPart S A₀) r) :
    ContainsLinearForestWith G (sampledPart S A) r := by
  apply ContainsLinearForestWith.mono_vertexSet h
  apply sampledPart_mono
  rw [hA₀]
  exact Finset.sdiff_subset

/-- Sampled transfer on the side changed from `B` to `B ∪ T`.  All
edges incident with sampled moved vertices are deleted; the resulting
forest is supported on the original sampled side and loses at most
`2 * (S ∩ T).card` edges. -/
theorem ContainsLinearForestWith.transfer_sampled_right
    {S B B₀ T : Finset V} {G : SimpleGraph (S : Set V)} {r : ℕ}
    (hB₀ : B₀ = B ∪ T)
    (h : ContainsLinearForestWith G (sampledPart S B₀) r) :
    ContainsLinearForestWith G (sampledPart S B)
      (r - 2 * (S ∩ T).card) := by
  have htransfer : ContainsLinearForestWith G (sampledPart S B)
      (r - 2 * (sampledPart S T).card) := by
    apply ContainsLinearForestWith.transfer_moved h
    rw [hB₀, sampledPart_union]
  rw [card_sampledPart] at htransfer
  exact htransfer

/-- Full balancing-context form.  The hypotheses record
`T ⊆ A`, `A₀ = A \ T`, and `B₀ = B ∪ T`; the right-side forest
transfer only needs the last identity, while the first two are retained in
the interface to match the structural decomposition that produces the cut. -/
theorem ContainsLinearForestWith.transfer_sampled_balancing_right
    {S A B T A₀ B₀ : Finset V} {G : SimpleGraph (S : Set V)} {r : ℕ}
    (_hTA : T ⊆ A) (_hA₀ : A₀ = A \ T) (hB₀ : B₀ = B ∪ T)
    (h : ContainsLinearForestWith G (sampledPart S B₀) r) :
    ContainsLinearForestWith G (sampledPart S B)
      (r - 2 * (S ∩ T).card) :=
  ContainsLinearForestWith.transfer_sampled_right hB₀ h

end ForestTransfer
end Erdos622
