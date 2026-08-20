/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.LiftedCyclicSkeletonIncidence

/-!
# Owner-preserving realization of sign-vector edges

The cardinality construction in `LiftedCyclicSkeletonIncidence` is deliberately global and hence
does not remember the supporting arrangement line of an edge.  Here the cardinal equivalences are
chosen separately in every owner fiber.  Consequently the resulting equivalence from projective
strict sign edges to cyclic skeleton edges preserves the line label, as does its spherical lift.
In particular, both endpoints assigned to a strict edge lie on that edge's supporting line.
-/

open Classical
noncomputable section

namespace Erdos735.SignVector

open ChartOrder

universe u v

variable {I : Type u} [Fintype I] [DecidableEq I]
variable {V : Type v} [Fintype V] [DecidableEq V]

@[simp] theorem normalizeProjectiveEdge_support
    (pick : OtherLineChoice I) (n : I → Vec3) (e : StrictEdge n) :
    (normalizeProjectiveEdge pick n e).1.1.1 = e.1.1 := by
  unfold normalizeProjectiveEdge
  split <;> rfl

@[simp] theorem strictEdgeEquivProjectiveTimesBool_support
    (pick : OtherLineChoice I) (n : I → Vec3) (e : StrictEdge n) :
    ((strictEdgeEquivProjectiveTimesBool pick n e).1).1.1.1 = e.1.1 := by
  exact normalizeProjectiveEdge_support pick n e

abbrev StrictEdgeOn (n : I → Vec3) (i : I) :=
  {e : StrictEdge n // e.1.1 = i}

abbrev ProjectiveStrictEdgeOn (pick : OtherLineChoice I) (n : I → Vec3) (i : I) :=
  {e : ProjectiveStrictEdge pick n // e.1.1.1 = i}

abbrev RestrictedPatternOn (n : I → Vec3) (i : I) :=
  {s : {j : I // j ≠ i} → Bool //
    RestrictedRealizable (otherNormals n i) (n i) s}

noncomputable def strictEdgeOnEquivRestrictedPatternOn
    (n : I → Vec3) (i : I) :
    StrictEdgeOn n i ≃ RestrictedPatternOn n i where
  toFun e := by
    rcases e with ⟨⟨⟨k, s⟩, hs⟩, hk⟩
    change k = i at hk
    subst k
    exact ⟨s, hs⟩
  invFun s := ⟨⟨⟨i, s.1⟩, s.2⟩, rfl⟩
  left_inv e := by
    rcases e with ⟨⟨⟨k, s⟩, hs⟩, hk⟩
    change k = i at hk
    subst k
    rfl
  right_inv s := rfl

theorem card_restrictedPatternOn (n : I → Vec3) (i : I) :
    Fintype.card (RestrictedPatternOn n i) =
      restrictedFaceCount (otherNormals n i) (n i) := by
  rw [Fintype.card_subtype]
  unfold restrictedFaceCount restrictedFacePatterns
  apply congrArg Finset.card
  ext s
  simp

noncomputable def strictEdgeOnEquivProjectiveOnTimesBool
    (pick : OtherLineChoice I) (n : I → Vec3) (i : I) :
    StrictEdgeOn n i ≃ ProjectiveStrictEdgeOn pick n i × Bool where
  toFun e :=
    let eb := strictEdgeEquivProjectiveTimesBool pick n e.1
    (⟨eb.1, by
      exact (strictEdgeEquivProjectiveTimesBool_support pick n e.1).trans e.2⟩, eb.2)
  invFun eb :=
    let e := (strictEdgeEquivProjectiveTimesBool pick n).symm (eb.1.1, eb.2)
    ⟨e, by
      have h := strictEdgeEquivProjectiveTimesBool_support pick n e
      have hap := (strictEdgeEquivProjectiveTimesBool pick n).apply_symm_apply
        (eb.1.1, eb.2)
      have hproj : (strictEdgeEquivProjectiveTimesBool pick n e).1 = eb.1.1 :=
        congrArg Prod.fst hap
      exact h.symm.trans ((congrArg (fun p : ProjectiveStrictEdge pick n ↦ p.1.1.1)
        hproj).trans eb.1.2)⟩
  left_inv e := by
    apply Subtype.ext
    exact (strictEdgeEquivProjectiveTimesBool pick n).symm_apply_apply e.1
  right_inv eb := by
    rcases eb with ⟨e, b⟩
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst ((strictEdgeEquivProjectiveTimesBool pick n).apply_symm_apply (e.1, b))
    · change ((strictEdgeEquivProjectiveTimesBool pick n)
          ((strictEdgeEquivProjectiveTimesBool pick n).symm (e.1, b))).2 = b
      exact congrArg Prod.snd
        ((strictEdgeEquivProjectiveTimesBool pick n).apply_symm_apply (e.1, b))

theorem card_projectiveStrictEdgeOn
    (pick : OtherLineChoice I) (n : I → Vec3) (i : I) :
    2 * Fintype.card (ProjectiveStrictEdgeOn pick n i) =
      restrictedFaceCount (otherNormals n i) (n i) := by
  have hstrict : Fintype.card (StrictEdgeOn n i) =
      restrictedFaceCount (otherNormals n i) (n i) := by
    rw [Fintype.card_congr (strictEdgeOnEquivRestrictedPatternOn n i),
      card_restrictedPatternOn]
  have hpair : Fintype.card (StrictEdgeOn n i) =
      2 * Fintype.card (ProjectiveStrictEdgeOn pick n i) := by
    rw [Fintype.card_congr (strictEdgeOnEquivProjectiveOnTimesBool pick n i),
      Fintype.card_prod, Fintype.card_bool]
    omega
  omega

theorem card_projectiveStrictEdgeOn_eq_verticesOn
    (pick : OtherLineChoice I) (n : I → Vec3)
    (vertices : Finset V) (onLine : V → I → Prop) [DecidableRel onLine]
    (hrestricted : ∀ i,
      restrictedFaceCount (otherNormals n i) (n i) =
        2 * (verticesOn vertices onLine i).card)
    (i : I) :
    Fintype.card (ProjectiveStrictEdgeOn pick n i) =
      Fintype.card {v // v ∈ verticesOn vertices onLine i} := by
  rw [Fintype.card_coe]
  have hp := card_projectiveStrictEdgeOn pick n i
  have hr := hrestricted i
  omega

noncomputable def ownerPreservingProjectiveEdgeEquiv
    (pick : OtherLineChoice I) (n : I → Vec3)
    (vertices : Finset V) (onLine : V → I → Prop) [DecidableRel onLine]
    (hrestricted : ∀ i,
      restrictedFaceCount (otherNormals n i) (n i) =
        2 * (verticesOn vertices onLine i).card) :
    ProjectiveStrictEdge pick n ≃ CyclicSkeletonEdge vertices onLine :=
  (Equiv.sigmaFiberEquiv
      (fun e : ProjectiveStrictEdge pick n ↦ e.1.1.1)).symm |>.trans
    (Equiv.sigmaCongrRight fun i ↦
      Fintype.equivOfCardEq
        (card_projectiveStrictEdgeOn_eq_verticesOn
          pick n vertices onLine hrestricted i))

@[simp] theorem ownerPreservingProjectiveEdgeEquiv_line
    (pick : OtherLineChoice I) (n : I → Vec3)
    (vertices : Finset V) (onLine : V → I → Prop) [DecidableRel onLine]
    (hrestricted : ∀ i,
      restrictedFaceCount (otherNormals n i) (n i) =
        2 * (verticesOn vertices onLine i).card)
    (e : ProjectiveStrictEdge pick n) :
    cyclicEdgeLine (ownerPreservingProjectiveEdgeEquiv
      pick n vertices onLine hrestricted e) = e.1.1.1 := by
  rfl

noncomputable def ownerPreservingStrictEdgeEquivLiftedCyclic
    (pick : OtherLineChoice I) (n : I → Vec3)
    (vertices : Finset V) (onLine : V → I → Prop) [DecidableRel onLine]
    (hrestricted : ∀ i,
      restrictedFaceCount (otherNormals n i) (n i) =
        2 * (verticesOn vertices onLine i).card) :
    StrictEdge n ≃ LiftedCyclicSkeletonEdge vertices onLine :=
  strictEdgeEquivLiftedCyclic pick n
    (ownerPreservingProjectiveEdgeEquiv pick n vertices onLine hrestricted)

@[simp] theorem ownerPreservingStrictEdgeEquivLiftedCyclic_line
    (pick : OtherLineChoice I) (n : I → Vec3)
    (vertices : Finset V) (onLine : V → I → Prop) [DecidableRel onLine]
    (hrestricted : ∀ i,
      restrictedFaceCount (otherNormals n i) (n i) =
        2 * (verticesOn vertices onLine i).card)
    (e : StrictEdge n) :
    cyclicEdgeLine ((ownerPreservingStrictEdgeEquivLiftedCyclic
      pick n vertices onLine hrestricted e).1) = e.1.1 := by
  change cyclicEdgeLine (ownerPreservingProjectiveEdgeEquiv pick n vertices onLine
    hrestricted (normalizeProjectiveEdge pick n e)) = e.1.1
  rw [ownerPreservingProjectiveEdgeEquiv_line, normalizeProjectiveEdge_support]

namespace LiftedCyclicEdgeRealization

noncomputable def ofRestrictedFaceCountsOwnerPreserving
    {n : I → Vec3} {onLine : V → I → Prop} [DecidableRel onLine]
    (pick : OtherLineChoice I)
    (vertices : Finset V) (coord : V → ℝ)
    (all_vertices : vertices = Finset.univ)
    (coord_injective : Set.InjOn coord (vertices : Set V))
    (two_vertices_on_line : ∀ i, 2 ≤ (verticesOn vertices onLine i).card)
    (hrestricted : ∀ i,
      restrictedFaceCount (otherNormals n i) (n i) =
        2 * (verticesOn vertices onLine i).card)
    (multiplicity_two_le : ∀ v, 2 ≤ lineMultiplicity onLine v) :
    LiftedCyclicEdgeRealization n onLine :=
  ofProjective pick vertices coord all_vertices coord_injective two_vertices_on_line
    (ownerPreservingProjectiveEdgeEquiv pick n vertices onLine hrestricted)
    multiplicity_two_le

theorem edgeVertex_on_support
    {n : I → Vec3} {onLine : V → I → Prop} [DecidableRel onLine]
    (pick : OtherLineChoice I)
    (vertices : Finset V) (coord : V → ℝ)
    (all_vertices : vertices = Finset.univ)
    (coord_injective : Set.InjOn coord (vertices : Set V))
    (two_vertices_on_line : ∀ i, 2 ≤ (verticesOn vertices onLine i).card)
    (hrestricted : ∀ i,
      restrictedFaceCount (otherNormals n i) (n i) =
        2 * (verticesOn vertices onLine i).card)
    (multiplicity_two_le : ∀ v, 2 ≤ lineMultiplicity onLine v)
    (e : StrictEdge n) (v : V × Bool)
    (hv : v ∈ (ofRestrictedFaceCountsOwnerPreserving pick vertices coord
      all_vertices coord_injective two_vertices_on_line hrestricted
      multiplicity_two_le).edgeVertices e) :
    onLine v.1 e.1.1 := by
  let X := ofRestrictedFaceCountsOwnerPreserving pick vertices coord
    all_vertices coord_injective two_vertices_on_line hrestricted
    multiplicity_two_le
  change v ∈ liftedCyclicEdgeVertices vertices onLine coord (fun _ ↦ false)
    (ownerPreservingStrictEdgeEquivLiftedCyclic
      pick n vertices onLine hrestricted e) at hv
  rw [liftedCyclicEdgeVertices] at hv
  rcases Finset.mem_insert.mp hv with hstart | hfinish
  · have hv1 : v.1 = cyclicEdgeStart
        ((ownerPreservingStrictEdgeEquivLiftedCyclic
          pick n vertices onLine hrestricted e).1) := by
      simpa only using congrArg Prod.fst hstart
    rw [hv1]
    have hinc := cyclicEdgeStart_incident vertices onLine
      ((ownerPreservingStrictEdgeEquivLiftedCyclic
        pick n vertices onLine hrestricted e).1)
    rw [ownerPreservingStrictEdgeEquivLiftedCyclic_line] at hinc
    exact hinc
  · have hv1 : v.1 = cyclicEdgeFinish vertices onLine coord
        ((ownerPreservingStrictEdgeEquivLiftedCyclic
          pick n vertices onLine hrestricted e).1) := by
      simpa only using congrArg Prod.fst (Finset.mem_singleton.mp hfinish)
    rw [hv1]
    have hinc := cyclicEdgeFinish_incident vertices onLine coord
      ((ownerPreservingStrictEdgeEquivLiftedCyclic
        pick n vertices onLine hrestricted e).1)
    rw [ownerPreservingStrictEdgeEquivLiftedCyclic_line] at hinc
    exact hinc

end LiftedCyclicEdgeRealization
end Erdos735.SignVector
