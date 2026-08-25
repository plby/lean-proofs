/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.FiniteBernoulliLocality
import ErdosProblems.Erdos76.Kahn

/-!
# Local dependency geometry for the Pippenger--Spencer nibble

This file is a downstream combinatorial layer.  It constructs finite balls
in the conflict graph of an indexed hypergraph, bounds their sizes from
uniformity and maximum vertex degree, and packages the radius-one influence
sets used by batched residual-degree events.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Edges conflicting with `e`. -/
def conflictNeighborhood (H : FiniteHypergraph V E) (e : E) : Finset E :=
  (Finset.univ : Finset E).filter fun f ↦ H.Conflicts e f

/-- The closed neighborhood of an edge in the conflict graph. -/
def closedConflictNeighborhood (H : FiniteHypergraph V E) (e : E) : Finset E :=
  insert e (H.conflictNeighborhood e)

/-- One closed-neighborhood expansion of an edge family. -/
def conflictExpand (H : FiniteHypergraph V E) (S : Finset E) : Finset E :=
  S.biUnion H.closedConflictNeighborhood

/-- The radius-`r` closed ball about one edge in the conflict graph. -/
def conflictBall (H : FiniteHypergraph V E) : ℕ → E → Finset E
  | 0, e => {e}
  | r + 1, e => H.conflictExpand (H.conflictBall r e)

/-- Edges incident with a vertex. -/
def incidentEdges (H : FiniteHypergraph V E) (v : V) : Finset E :=
  (Finset.univ : Finset E).filter fun e ↦ v ∈ H.support e

/-- The union of radius-`r` edge balls centred at edges through `v`. -/
def vertexConflictBall (H : FiniteHypergraph V E) (r : ℕ) (v : V) : Finset E :=
  (H.incidentEdges v).biUnion (H.conflictBall r)

/-- The radius-one influence set for a residual-degree event at `v`. -/
def vertexInfluenceEdges (H : FiniteHypergraph V E) (v : V) : Finset E :=
  H.vertexConflictBall 1 v

/-- Vertices touched by edges in the radius-`r` conflict ball about `v`. -/
def vertexConflictBallVertices (H : FiniteHypergraph V E) (r : ℕ) (v : V) : Finset V :=
  (H.vertexConflictBall r v).biUnion H.support

@[simp] lemma mem_conflictNeighborhood (H : FiniteHypergraph V E) (e f : E) :
    f ∈ H.conflictNeighborhood e ↔ H.Conflicts e f := by
  simp [conflictNeighborhood]

@[simp] lemma card_conflictNeighborhood (H : FiniteHypergraph V E) (e : E) :
    (H.conflictNeighborhood e).card = H.conflictDegree e := rfl

@[simp] lemma mem_closedConflictNeighborhood (H : FiniteHypergraph V E) (e f : E) :
    f ∈ H.closedConflictNeighborhood e ↔ f = e ∨ H.Conflicts e f := by
  simp [closedConflictNeighborhood]

lemma mem_closedConflictNeighborhood_comm (H : FiniteHypergraph V E) (e f : E) :
    f ∈ H.closedConflictNeighborhood e ↔ e ∈ H.closedConflictNeighborhood f := by
  simp only [mem_closedConflictNeighborhood]
  constructor
  · rintro (rfl | hef)
    · exact Or.inl rfl
    · exact Or.inr hef.symm
  · rintro (rfl | hfe)
    · exact Or.inl rfl
    · exact Or.inr hfe.symm

@[simp] lemma mem_conflictExpand (H : FiniteHypergraph V E) (S : Finset E) (f : E) :
    f ∈ H.conflictExpand S ↔
      ∃ e ∈ S, f ∈ H.closedConflictNeighborhood e := by
  simp [conflictExpand]

@[simp] lemma conflictBall_zero (H : FiniteHypergraph V E) (e : E) :
    H.conflictBall 0 e = {e} := rfl

@[simp] lemma conflictBall_succ (H : FiniteHypergraph V E) (r : ℕ) (e : E) :
    H.conflictBall (r + 1) e = H.conflictExpand (H.conflictBall r e) := rfl

lemma mem_conflictBall_self (H : FiniteHypergraph V E) (r : ℕ) (e : E) :
    e ∈ H.conflictBall r e := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [conflictBall_succ, mem_conflictExpand]
      exact ⟨e, ih, by simp⟩

lemma conflictBall_mono_radius (H : FiniteHypergraph V E) (r : ℕ) (e : E) :
    H.conflictBall r e ⊆ H.conflictBall (r + 1) e := by
  intro f hf
  rw [conflictBall_succ, mem_conflictExpand]
  exact ⟨f, hf, by simp⟩

lemma conflictBall_of_mem_closed {H : FiniteHypergraph V E} {e f : E}
    (hef : f ∈ H.closedConflictNeighborhood e) (r : ℕ) :
    H.conflictBall r f ⊆ H.conflictBall (r + 1) e := by
  induction r with
  | zero =>
      intro x hx
      simp only [conflictBall_zero, mem_singleton] at hx
      subst x
      rw [conflictBall_succ, mem_conflictExpand]
      exact ⟨e, by simp, hef⟩
  | succ r ih =>
      intro x hx
      rw [conflictBall_succ, mem_conflictExpand] at hx ⊢
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨y, ih hy, hxy⟩

lemma mem_conflictBall_comm (H : FiniteHypergraph V E) (r : ℕ) (e f : E) :
    f ∈ H.conflictBall r e ↔ e ∈ H.conflictBall r f := by
  induction r generalizing e f with
  | zero => simp [eq_comm]
  | succ r ih =>
      constructor
      · intro hf
        rw [conflictBall_succ, mem_conflictExpand] at hf
        obtain ⟨g, hg, hfg⟩ := hf
        exact H.conflictBall_of_mem_closed
          ((H.mem_closedConflictNeighborhood_comm g f).mp hfg) r
          ((ih e g).mp hg)
      · intro he
        rw [conflictBall_succ, mem_conflictExpand] at he
        obtain ⟨g, hg, heg⟩ := he
        exact H.conflictBall_of_mem_closed
          ((H.mem_closedConflictNeighborhood_comm g e).mp heg) r
          ((ih f g).mp hg)

lemma conflictBall_comp {H : FiniteHypergraph V E} {e f : E} {r : ℕ}
    (hef : f ∈ H.conflictBall r e) (s : ℕ) :
    H.conflictBall s f ⊆ H.conflictBall (r + s) e := by
  induction s with
  | zero =>
      intro x hx
      simp only [conflictBall_zero, mem_singleton] at hx
      subst x
      simpa using hef
  | succ s ih =>
      intro x hx
      rw [conflictBall_succ, mem_conflictExpand] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      rw [show r + (s + 1) = (r + s) + 1 by omega, conflictBall_succ,
        mem_conflictExpand]
      exact ⟨y, ih hy, hxy⟩

@[simp] lemma mem_incidentEdges (H : FiniteHypergraph V E) (v : V) (e : E) :
    e ∈ H.incidentEdges v ↔ v ∈ H.support e := by
  simp [incidentEdges]

@[simp] lemma card_incidentEdges (H : FiniteHypergraph V E) (v : V) :
    (H.incidentEdges v).card = H.edgeDegree v := rfl

@[simp] lemma mem_vertexConflictBall (H : FiniteHypergraph V E)
    (r : ℕ) (v : V) (f : E) :
    f ∈ H.vertexConflictBall r v ↔
      ∃ e, v ∈ H.support e ∧ f ∈ H.conflictBall r e := by
  simp [vertexConflictBall]

lemma mem_vertexInfluenceEdges_iff (H : FiniteHypergraph V E) (v : V) (f : E) :
    f ∈ H.vertexInfluenceEdges v ↔
      ∃ e, v ∈ H.support e ∧ (f = e ∨ H.Conflicts e f) := by
  simp [vertexInfluenceEdges, mem_vertexConflictBall, conflictBall]

lemma incidentEdges_subset_vertexInfluenceEdges (H : FiniteHypergraph V E) (v : V) :
    H.incidentEdges v ⊆ H.vertexInfluenceEdges v := by
  intro e he
  rw [mem_vertexInfluenceEdges_iff]
  exact ⟨e, (H.mem_incidentEdges v e).mp he, Or.inl rfl⟩

lemma closedConflictNeighborhood_card_le {H : FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (e : E) :
    (H.closedConflictNeighborhood e).card ≤ k * D + 1 := by
  calc
    (H.closedConflictNeighborhood e).card ≤ (H.conflictNeighborhood e).card + 1 :=
      card_insert_le e (H.conflictNeighborhood e)
    _ = H.conflictDegree e + 1 := by rw [card_conflictNeighborhood]
    _ ≤ k * D + 1 := Nat.add_le_add_right
      (H.conflictDegree_le_uniform_mul hunif hdeg e) 1

lemma conflictExpand_card_le {H : FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (S : Finset E) :
    (H.conflictExpand S).card ≤ S.card * (k * D + 1) := by
  calc
    (H.conflictExpand S).card ≤
        ∑ e ∈ S, (H.closedConflictNeighborhood e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ S, (k * D + 1) := by
      exact sum_le_sum fun e _ ↦ H.closedConflictNeighborhood_card_le hunif hdeg e
    _ = S.card * (k * D + 1) := by simp

lemma conflictBall_card_le {H : FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) (r : ℕ) (e : E) :
    (H.conflictBall r e).card ≤ (k * D + 1) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [conflictBall_succ, pow_succ]
      exact (H.conflictExpand_card_le hunif hdeg _).trans
        (Nat.mul_le_mul_right (k * D + 1) ih)

lemma vertexConflictBall_card_le {H : FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {v : V} (hv : v ∈ H.vertexSet) (r : ℕ) :
    (H.vertexConflictBall r v).card ≤ D * (k * D + 1) ^ r := by
  calc
    (H.vertexConflictBall r v).card ≤
        ∑ e ∈ H.incidentEdges v, (H.conflictBall r e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ H.incidentEdges v, (k * D + 1) ^ r := by
      exact sum_le_sum fun e _ ↦ H.conflictBall_card_le hunif hdeg r e
    _ = (H.incidentEdges v).card * (k * D + 1) ^ r := by simp
    _ ≤ D * (k * D + 1) ^ r :=
      Nat.mul_le_mul_right _ (by simpa using hdeg v hv)

lemma vertexConflictBallVertices_card_le {H : FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {v : V} (hv : v ∈ H.vertexSet) (r : ℕ) :
    (H.vertexConflictBallVertices r v).card ≤
      (D * (k * D + 1) ^ r) * k := by
  calc
    (H.vertexConflictBallVertices r v).card ≤
        ∑ e ∈ H.vertexConflictBall r v, (H.support e).card := card_biUnion_le
    _ = ∑ _e ∈ H.vertexConflictBall r v, k := by
      apply sum_congr rfl
      intro e _
      exact hunif e
    _ = (H.vertexConflictBall r v).card * k := by simp
    _ ≤ (D * (k * D + 1) ^ r) * k :=
      Nat.mul_le_mul_right k (H.vertexConflictBall_card_le hunif hdeg hv r)

/-- If two vertex-centred radius-`r` edge balls overlap, then the second
vertex is touched by the radius-`2r` ball about the first. -/
lemma mem_vertexConflictBallVertices_of_overlap
    (H : FiniteHypergraph V E) (r : ℕ) (v w : V)
    (hoverlap : ¬ Disjoint (H.vertexConflictBall r v) (H.vertexConflictBall r w)) :
    w ∈ H.vertexConflictBallVertices (r + r) v := by
  obtain ⟨x, hxv, hxw⟩ := not_disjoint_iff.mp hoverlap
  rw [mem_vertexConflictBall] at hxv hxw
  obtain ⟨e, hve, hxe⟩ := hxv
  obtain ⟨f, hwf, hxf⟩ := hxw
  rw [vertexConflictBallVertices, mem_biUnion]
  refine ⟨f, ?_, hwf⟩
  rw [mem_vertexConflictBall]
  refine ⟨e, hve, ?_⟩
  exact H.conflictBall_comp hxe r ((H.mem_conflictBall_comm r f x).mp hxf)

/-- Read one trial from a flattened family of Bernoulli coordinates. -/
def batchAt {J : Type*} [Fintype J] (Z : Finset (J × E)) (j : J) : Finset E :=
  (Finset.univ : Finset E).filter fun e ↦ (j, e) ∈ Z

/-- All flattened coordinates which can affect the residual degree at `v`. -/
def batchVertexInfluenceSupport {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (v : V) : Finset (J × E) :=
  (Finset.univ : Finset J).product (H.vertexInfluenceEdges v)

@[simp] lemma mem_batchAt {J : Type*} [Fintype J]
    (Z : Finset (J × E)) (j : J) (e : E) :
    e ∈ batchAt Z j ↔ (j, e) ∈ Z := by
  simp [batchAt]

@[simp] lemma mem_batchVertexInfluenceSupport {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (v : V) (z : J × E) :
    z ∈ H.batchVertexInfluenceSupport v ↔ z.2 ∈ H.vertexInfluenceEdges v := by
  simp [batchVertexInfluenceSupport]

lemma batchVertexInfluenceSupport_card_le
    {J : Type*} [Fintype J] {H : FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {v : V} (hv : v ∈ H.vertexSet) :
    (H.batchVertexInfluenceSupport (J := J) v).card ≤
      Fintype.card J * (D * (k * D + 1)) := by
  change (((Finset.univ : Finset J) ×ˢ H.vertexInfluenceEdges v).card ≤ _)
  rw [card_product, card_univ]
  exact Nat.mul_le_mul_left _ (by
    simpa [vertexInfluenceEdges] using H.vertexConflictBall_card_le hunif hdeg hv 1)

/-- Vertex dependency graph obtained by intersecting radius-one influence
edge sets. -/
def vertexInfluenceDependency (H : FiniteHypergraph V E)
    (v : ↥H.vertexSet) : Finset ↥H.vertexSet :=
  (Finset.univ : Finset ↥H.vertexSet).filter fun w ↦
    v ≠ w ∧ ¬ Disjoint (H.vertexInfluenceEdges v.1) (H.vertexInfluenceEdges w.1)

@[simp] lemma mem_vertexInfluenceDependency (H : FiniteHypergraph V E)
    (v w : ↥H.vertexSet) :
    w ∈ H.vertexInfluenceDependency v ↔
      v ≠ w ∧ ¬ Disjoint (H.vertexInfluenceEdges v.1) (H.vertexInfluenceEdges w.1) := by
  simp [vertexInfluenceDependency]

lemma vertexInfluenceDependency_card_le
    {H : FiniteHypergraph V E} {k D : ℕ}
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (v : ↥H.vertexSet) :
    (H.vertexInfluenceDependency v).card ≤
      (D * (k * D + 1) ^ 2) * k := by
  let imageVertices : Finset V :=
    (H.vertexInfluenceDependency v).image Subtype.val
  have hcard : imageVertices.card = (H.vertexInfluenceDependency v).card := by
    exact card_image_of_injective _ Subtype.val_injective
  have hsub : imageVertices ⊆ H.vertexConflictBallVertices 2 v.1 := by
    intro w hw
    obtain ⟨w', hwDep, rfl⟩ := mem_image.mp hw
    have hoverlap := (H.mem_vertexInfluenceDependency v w').mp hwDep |>.2
    simpa [vertexInfluenceEdges] using
      H.mem_vertexConflictBallVertices_of_overlap 1 v.1 w'.1 hoverlap
  rw [← hcard]
  exact (card_le_card hsub).trans
    (H.vertexConflictBallVertices_card_le hunif hdeg v.2 2)

lemma batchInfluence_contains_overlaps {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) :
    FiniteNibble.ContainsSupportOverlaps
      (fun v : ↥H.vertexSet ↦ H.batchVertexInfluenceSupport (J := J) v.1)
      H.vertexInfluenceDependency := by
  intro v w hvw hoverlap
  rw [H.mem_vertexInfluenceDependency]
  refine ⟨hvw, ?_⟩
  obtain ⟨z, hzv, hzw⟩ := not_disjoint_iff.mp hoverlap
  rw [H.mem_batchVertexInfluenceSupport] at hzv hzw
  exact not_disjoint_iff.mpr ⟨z.2, hzv, hzw⟩

/-- Accepted edges, expressed directly on flattened batch coordinates. -/
def flattenedBatchAcceptedEdges {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (Z : Finset (J × E)) : Finset E :=
  (Finset.univ : Finset J).biUnion fun j ↦ H.isolatedSample (batchAt Z j)

/-- Residual degree expressed directly on flattened batch coordinates.  This
is definitionally the same finite calculation as `batchResidualDegree` after
unflattening the batch. -/
def flattenedBatchResidualDegree {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (Z : Finset (J × E)) (v : V) : ℕ :=
  ((Finset.univ : Finset E) \ H.flattenedBatchAcceptedEdges Z).filter
    (fun e ↦ v ∈ H.support e) |>.card

@[simp] lemma mem_flattenedBatchAcceptedEdges {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (Z : Finset (J × E)) (e : E) :
    e ∈ H.flattenedBatchAcceptedEdges Z ↔
      ∃ j : J, e ∈ H.isolatedSample (batchAt Z j) := by
  simp [flattenedBatchAcceptedEdges]

lemma mem_iff_of_agreesOn {J : Type*} [Fintype J]
    {R Z T : Finset (J × E)} (hZT : FiniteNibble.AgreesOn R Z T)
    {z : J × E} (hz : z ∈ R) :
    z ∈ Z ↔ z ∈ T := by
  unfold FiniteNibble.AgreesOn at hZT
  have hmem := congrArg (fun S : Finset (J × E) ↦ z ∈ S) hZT
  have hmem' : (z ∈ Z) = (z ∈ T) := by
    simpa only [mem_inter, hz, and_true] using hmem
  exact eq_iff_iff.mp hmem'

/-- For an edge through `v`, isolated acceptance in one trial is determined
by the radius-one influence coordinates at `v`. -/
lemma isolatedSample_mem_iff_of_agreesOn_batchVertexInfluence
    {J : Type*} [Fintype J] (H : FiniteHypergraph V E)
    {v : V} {Z T : Finset (J × E)}
    (hZT : FiniteNibble.AgreesOn (H.batchVertexInfluenceSupport v) Z T)
    (j : J) {e : E} (hve : v ∈ H.support e) :
    e ∈ H.isolatedSample (batchAt Z j) ↔
      e ∈ H.isolatedSample (batchAt T j) := by
  have relevant (f : E) (hef : f = e ∨ H.Conflicts e f) :
      (j, f) ∈ H.batchVertexInfluenceSupport v := by
    rw [H.mem_batchVertexInfluenceSupport, H.mem_vertexInfluenceEdges_iff]
    exact ⟨e, hve, hef⟩
  have transfer (f : E) (hef : f = e ∨ H.Conflicts e f) :
      f ∈ batchAt Z j ↔ f ∈ batchAt T j := by
    simp only [mem_batchAt]
    exact mem_iff_of_agreesOn hZT (relevant f hef)
  constructor
  · intro heZ
    have heZ' := mem_filter.mp heZ
    apply mem_filter.mpr
    refine ⟨(transfer e (Or.inl rfl)).mp heZ'.1, ?_⟩
    intro f hfT hef
    by_cases hdisj : Disjoint (H.support e) (H.support f)
    · exact hdisj
    · have hconf : H.Conflicts e f := ⟨hef, hdisj⟩
      exact heZ'.2 f ((transfer f (Or.inr hconf)).mpr hfT) hef
  · intro heT
    have heT' := mem_filter.mp heT
    apply mem_filter.mpr
    refine ⟨(transfer e (Or.inl rfl)).mpr heT'.1, ?_⟩
    intro f hfZ hef
    by_cases hdisj : Disjoint (H.support e) (H.support f)
    · exact hdisj
    · have hconf : H.Conflicts e f := ⟨hef, hdisj⟩
      exact heT'.2 f ((transfer f (Or.inr hconf)).mp hfZ) hef

lemma flattenedBatchAcceptedEdges_mem_iff_of_agreesOn
    {J : Type*} [Fintype J] (H : FiniteHypergraph V E)
    {v : V} {Z T : Finset (J × E)}
    (hZT : FiniteNibble.AgreesOn (H.batchVertexInfluenceSupport v) Z T)
    {e : E} (hve : v ∈ H.support e) :
    e ∈ H.flattenedBatchAcceptedEdges Z ↔
      e ∈ H.flattenedBatchAcceptedEdges T := by
  simp only [mem_flattenedBatchAcceptedEdges]
  constructor
  · rintro ⟨j, heZ⟩
    exact ⟨j, (H.isolatedSample_mem_iff_of_agreesOn_batchVertexInfluence hZT j hve).mp heZ⟩
  · rintro ⟨j, heT⟩
    exact ⟨j, (H.isolatedSample_mem_iff_of_agreesOn_batchVertexInfluence hZT j hve).mpr heT⟩

/-- Agreement on the influence coordinates preserves the residual degree. -/
lemma flattenedBatchResidualDegree_eq_of_agreesOn
    {J : Type*} [Fintype J] (H : FiniteHypergraph V E)
    {v : V} {Z T : Finset (J × E)}
    (hZT : FiniteNibble.AgreesOn (H.batchVertexInfluenceSupport v) Z T) :
    H.flattenedBatchResidualDegree Z v = H.flattenedBatchResidualDegree T v := by
  apply congrArg card
  ext e
  simp only [flattenedBatchResidualDegree, mem_filter, mem_sdiff, mem_univ, true_and]
  by_cases hve : v ∈ H.support e
  · simp only [hve, and_true]
    exact not_congr (H.flattenedBatchAcceptedEdges_mem_iff_of_agreesOn hZT hve)
  · simp [hve]

/-- Any predicate of the residual degree is a local event on the flattened
radius-one influence support. -/
theorem eventDependsOn_flattenedBatchResidualDegree
    {J : Type*} [Fintype J] (H : FiniteHypergraph V E) (v : V)
    (P : ℕ → Prop) :
    FiniteNibble.EventDependsOn (H.batchVertexInfluenceSupport v)
      (fun Z : Finset (J × E) ↦ P (H.flattenedBatchResidualDegree Z v)) := by
  intro Z T hZT
  change P (H.flattenedBatchResidualDegree Z v) ↔
    P (H.flattenedBatchResidualDegree T v)
  rw [H.flattenedBatchResidualDegree_eq_of_agreesOn hZT]

/-- Upper residual-degree bad event used in the outer local-lemma batch. -/
def flattenedResidualDegreeBad {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (threshold : ↥H.vertexSet → ℕ)
    (v : ↥H.vertexSet) (Z : Finset (J × E)) : Prop :=
  threshold v ≤ H.flattenedBatchResidualDegree Z v.1

lemma flattenedResidualDegreeBad_eventDependsOn
    {J : Type*} [Fintype J] (H : FiniteHypergraph V E)
    (threshold : ↥H.vertexSet → ℕ) (v : ↥H.vertexSet) :
    FiniteNibble.EventDependsOn (H.batchVertexInfluenceSupport v.1)
      (H.flattenedResidualDegreeBad (J := J) threshold v) := by
  exact H.eventDependsOn_flattenedBatchResidualDegree v.1
    (fun d ↦ threshold v ≤ d)

/-- Exact outside-neighborhood independence for all upper residual-degree
bad events in a flattened Bernoulli batch. -/
theorem flattenedResidualDegreeBad_independentOutside
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (prob : J × E → ℝ)
    (threshold : ↥H.vertexSet → ℕ) :
    FiniteLocalLemma.IndependentOutside
      (fun Z : Finset (J × E) ↦ FiniteNibble.bernoulliMass Finset.univ prob Z)
      (H.flattenedResidualDegreeBad threshold) H.vertexInfluenceDependency := by
  apply FiniteNibble.independentOutside_of_eventDependsOn prob
    (fun v : ↥H.vertexSet ↦ H.batchVertexInfluenceSupport v.1)
    (H.flattenedResidualDegreeBad threshold) H.vertexInfluenceDependency
  · exact H.flattenedResidualDegreeBad_eventDependsOn (J := J) threshold
  · exact H.batchInfluence_contains_overlaps (J := J)

/-- `HasLocalBound` package for residual-degree bad events.  The only
probabilistic input left to the caller is the uniform marginal tail bound. -/
theorem flattenedResidualDegreeBad_hasLocalBound
    {J : Type*} [Fintype J]
    (H : FiniteHypergraph V E) (prob : J × E → ℝ)
    (hprob0 : ∀ z, 0 ≤ prob z) (hprob1 : ∀ z, prob z ≤ 1)
    (threshold : ↥H.vertexSet → ℕ) {bound : ℝ}
    (hmarginal : ∀ v, FiniteLocalLemma.eventMass
      (fun Z : Finset (J × E) ↦ FiniteNibble.bernoulliMass Finset.univ prob Z)
      (H.flattenedResidualDegreeBad threshold v) ≤ bound) :
    FiniteLocalLemma.HasLocalBound
      (fun Z : Finset (J × E) ↦ FiniteNibble.bernoulliMass Finset.univ prob Z)
      (H.flattenedResidualDegreeBad threshold) H.vertexInfluenceDependency bound := by
  apply FiniteNibble.hasLocalBound_of_eventDependsOn prob hprob0 hprob1
    (fun v : ↥H.vertexSet ↦ H.batchVertexInfluenceSupport v.1)
    (H.flattenedResidualDegreeBad threshold) H.vertexInfluenceDependency
  · exact H.flattenedResidualDegreeBad_eventDependsOn (J := J) threshold
  · exact H.batchInfluence_contains_overlaps (J := J)
  · exact hmarginal

end FiniteHypergraph

end

end Erdos76
