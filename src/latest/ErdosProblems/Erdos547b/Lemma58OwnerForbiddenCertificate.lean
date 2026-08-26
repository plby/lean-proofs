/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OwnerForbidden

/-!
# Certified owner-specific target cleaning in Zhao Lemma 5.8

`Lemma58OwnerForbidden` embeds an owner batch after deleting a prescribed
bad set from the two current matching endpoints.  Its basic output forgets
that deletion when it widens the local embedding back to the original live
sets.  For reconnecting the edges deleted by Zhao's forest partition we
also need the corresponding certificate: every embedded branch vertex
avoids the bad set belonging to its literal owner and physical side.

This file retains exactly that certificate through the existing chosen-
orientation owner recursion.  It adds no embedding-valued premise: the
local input remains the source/host `OwnerLocalStepData` consumed by the
already checked threshold and Appendix constructors.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58OwnerForbiddenCertificate

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58DynamicBatchAppend
open Erdos547b.ZhaoLemma58ChosenOwnerBatches
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58OwnerForbidden
open Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest

universe v

/-- A chosen partial embedding together with the literal bad-set avoidance
certificate for every already processed source component. -/
structure CertifiedChosenPartialEmbedding
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (available : Fin 2 → Finset B)
    (owner : Fin b → Fin r)
    (bad : Fin r → Fin 2 → Finset B)
    (selected : Finset (Fin b)) where
  chosen : ChosenPartialDynamicEmbedding
    F G externalParent available selected
  avoids : ∀ i (hi : i ∈ selected) a,
    chosen.state.forestCopy.componentCopy i hi a ∉
      bad (owner i)
        (chosen.orient i
          ((F.isTree i).coloringTwoOfVert (F.root i) a))

/-- The empty owner prefix has the certified empty realization. -/
noncomputable def emptyCertified
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (available : Fin 2 → Finset B)
    (owner : Fin b → Fin r)
    (bad : Fin r → Fin 2 → Finset B) :
    CertifiedChosenPartialEmbedding F G externalParent available owner bad ∅ where
  chosen := {
    orient := fun _ ↦ Equiv.refl _
    state := emptyPartial F G externalParent (fun _ ↦ Equiv.refl _)
      available
  }
  avoids := by
    intro i hi
    have : False := by simpa using hi
    exact False.elim this

/-- `appendChosen` uses the old component copy literally on the first
selected family. -/
theorem appendChosen_componentCopy_left
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (s t : Finset (Fin b)) (hst : Disjoint s t)
    (E₁ : ChosenPartialDynamicEmbedding
      F G externalParent available s)
    (E₂ : ChosenPartialDynamicEmbedding F G externalParent
      (fun c ↦ available c \ E₁.used c) t)
    (i : Fin b) (hi : i ∈ s ∪ t) (his : i ∈ s)
    (a : Fin (F.size i)) :
    (appendChosen F G externalParent whole available havailable
        hwholeDisjoint s t hst E₁ E₂).state.forestCopy.componentCopy
          i hi a = E₁.state.forestCopy.componentCopy i his a := by
  simp [appendChosen, appendPartial, reorientPartial, his]

/-- `appendChosen` uses the new component copy literally on the second
selected family. -/
theorem appendChosen_componentCopy_right
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (s t : Finset (Fin b)) (hst : Disjoint s t)
    (E₁ : ChosenPartialDynamicEmbedding
      F G externalParent available s)
    (E₂ : ChosenPartialDynamicEmbedding F G externalParent
      (fun c ↦ available c \ E₁.used c) t)
    (i : Fin b) (hi : i ∈ s ∪ t) (his : i ∉ s) (hit : i ∈ t)
    (a : Fin (F.size i)) :
    (appendChosen F G externalParent whole available havailable
        hwholeDisjoint s t hst E₁ E₂).state.forestCopy.componentCopy
          i hi a = E₂.state.forestCopy.componentCopy i hit a := by
  simp [appendChosen, appendPartial, reorientPartial, his]

/-- Orientations of an appended state agree with the first state on its
selected source indices. -/
theorem appendChosen_orient_left
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (s t : Finset (Fin b)) (hst : Disjoint s t)
    (E₁ : ChosenPartialDynamicEmbedding
      F G externalParent available s)
    (E₂ : ChosenPartialDynamicEmbedding F G externalParent
      (fun c ↦ available c \ E₁.used c) t)
    (i : Fin b) (his : i ∈ s) :
    (appendChosen F G externalParent whole available havailable
      hwholeDisjoint s t hst E₁ E₂).orient i = E₁.orient i := by
  simp [appendChosen, pasteOrient, his]

/-- Orientations of an appended state agree with the second state on its
selected source indices. -/
theorem appendChosen_orient_right
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (s t : Finset (Fin b)) (hst : Disjoint s t)
    (E₁ : ChosenPartialDynamicEmbedding
      F G externalParent available s)
    (E₂ : ChosenPartialDynamicEmbedding F G externalParent
      (fun c ↦ available c \ E₁.used c) t)
    (i : Fin b) (hit : i ∈ t) :
    (appendChosen F G externalParent whole available havailable
      hwholeDisjoint s t hst E₁ E₂).orient i = E₂.orient i := by
  have his : i ∉ s := by
    intro his
    exact Finset.disjoint_left.mp hst his hit
  simp [appendChosen, pasteOrient, his]

/-- Append two certified disjoint owner families. -/
noncomputable def appendCertified
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (owner : Fin b → Fin r) (bad : Fin r → Fin 2 → Finset B)
    (s t : Finset (Fin b)) (hst : Disjoint s t)
    (E₁ : CertifiedChosenPartialEmbedding
      F G externalParent available owner bad s)
    (E₂ : CertifiedChosenPartialEmbedding F G externalParent
      (fun c ↦ available c \ E₁.chosen.used c) owner bad t) :
    CertifiedChosenPartialEmbedding F G externalParent available owner bad
      (s ∪ t) where
  chosen := appendChosen F G externalParent whole available havailable
    hwholeDisjoint s t hst E₁.chosen E₂.chosen
  avoids := by
    intro i hi a
    by_cases his : i ∈ s
    · rw [appendChosen_componentCopy_left F G externalParent whole available
          havailable hwholeDisjoint s t hst E₁.chosen E₂.chosen i hi his a,
        appendChosen_orient_left F G externalParent whole available havailable
          hwholeDisjoint s t hst E₁.chosen E₂.chosen i his]
      exact E₁.avoids i his a
    · have hit : i ∈ t := (Finset.mem_union.mp hi).resolve_left his
      rw [appendChosen_componentCopy_right F G externalParent whole available
          havailable hwholeDisjoint s t hst E₁.chosen E₂.chosen i hi his
          hit a,
        appendChosen_orient_right F G externalParent whole available havailable
          hwholeDisjoint s t hst E₁.chosen E₂.chosen i hit]
      exact E₂.avoids i hit a

/-- Full-family dynamic embedding retaining owner-specific bad-set
avoidance on every branch vertex. -/
structure CertifiedOwnerDynamicEmbedding
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B)
    (externalParent : Fin b → B)
    (available : Fin 2 → Finset B)
    (owner : Fin b → Fin r)
    (bad : Fin r → Fin 2 → Finset B) where
  orient : Fin b → Fin 2 ≃ Fin 2
  embedding : DynamicAttachedForestEmbedding
    F G externalParent orient available
  avoids : ∀ i a,
    embedding.embedding.copy i a ∉
      bad (owner i)
        (orient i ((F.isTree i).coloringTwoOfVert (F.root i) a))

/-- Owner-recursive Lemma 5.8 with dynamically chosen orientations,
owner-specific target cleaning, and the retained avoidance certificate.
The local premise is still only concrete source/live-host data. -/
theorem exists_certifiedDynamicEmbedding_of_ownerLocalStepsWithForbidden
    {b r : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (owner : Fin b → Fin r) (rho density : ℝ)
    (bad : Fin r → Fin 2 → Finset B)
    (hdata : ∀ n (hn : n < r)
      (Eprefix : ChosenPartialDynamicEmbedding F G externalParent available
        (ownerPrefix Finset.univ owner n)),
      Nonempty (OwnerLocalStepData
        (selectedForest F (ownerBatch Finset.univ owner ⟨n, hn⟩)) G
        (fun k ↦ externalParent
          (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
            (ownerBatch Finset.univ owner ⟨n, hn⟩) k))
        whole
        (ownerCleanedLive (fun c ↦ available c \ Eprefix.used c)
          (bad ⟨n, hn⟩)) rho density)) :
    Nonempty (CertifiedOwnerDynamicEmbedding
      F G externalParent available owner bad) := by
  classical
  have hbuild : ∀ n, n ≤ r →
      Nonempty (CertifiedChosenPartialEmbedding F G externalParent available
        owner bad (ownerPrefix Finset.univ owner n)) := by
    intro n hnr
    induction n with
    | zero =>
        rw [ownerPrefix_zero]
        exact ⟨emptyCertified F G externalParent available owner bad⟩
    | succ n ih =>
        have hn : n < r := Nat.lt_of_succ_le hnr
        obtain ⟨Eprefix⟩ := ih (Nat.le_of_lt hn)
        obtain ⟨D⟩ := hdata n hn Eprefix.chosen
        obtain ⟨localOrient, ⟨Eraw⟩⟩ := D.realize
          (selectedForest F (ownerBatch Finset.univ owner ⟨n, hn⟩)) G
          (fun k ↦ externalParent
            (Erdos547b.ZhaoClaim616SourceBridge.OrderedBranchForest.selectedEquiv
              (ownerBatch Finset.univ owner ⟨n, hn⟩) k))
          whole
          (ownerCleanedLive (fun c ↦ available c \ Eprefix.chosen.used c)
            (bad ⟨n, hn⟩)) rho density
        let Cbatch := chosenPartialOfSelectedForest F G externalParent
          (ownerCleanedLive
            (fun c ↦ available c \ Eprefix.chosen.used c) (bad ⟨n, hn⟩))
          (ownerBatch Finset.univ owner ⟨n, hn⟩) localOrient Eraw
        let Cwide : ChosenPartialDynamicEmbedding F G externalParent
            (fun c ↦ available c \ Eprefix.chosen.used c)
            (ownerBatch Finset.univ owner ⟨n, hn⟩) := {
          orient := Cbatch.orient
          state := {
            forestCopy := Cbatch.state.forestCopy
            attach := Cbatch.state.attach
            map_side := by
              intro i hi a
              exact (Finset.mem_sdiff.mp (Cbatch.state.map_side i hi a)).1
          }
        }
        let Ebatch : CertifiedChosenPartialEmbedding F G externalParent
            (fun c ↦ available c \ Eprefix.chosen.used c) owner bad
            (ownerBatch Finset.univ owner ⟨n, hn⟩) := {
          chosen := Cwide
          avoids := by
            intro i hi a
            have howner : owner i = ⟨n, hn⟩ :=
              (Finset.mem_filter.mp hi).2
            have hm := Cbatch.state.map_side i hi a
            have hnot := (Finset.mem_sdiff.mp hm).2
            rw [howner]
            exact hnot
        }
        let Eunion := appendCertified F G externalParent whole available
          havailable hwholeDisjoint owner bad
          (ownerPrefix Finset.univ owner n)
          (ownerBatch Finset.univ owner ⟨n, hn⟩)
          (ownerPrefix_disjoint_ownerBatch Finset.univ owner n hn)
          Eprefix Ebatch
        rw [ownerPrefix_succ Finset.univ owner n hn] at Eunion
        exact ⟨Eunion⟩
  obtain ⟨E⟩ := hbuild r le_rfl
  rw [ownerPrefix_all Finset.univ owner] at E
  let full := E.chosen.state.toDynamic F G externalParent E.chosen.orient
    available
  refine ⟨{
    orient := E.chosen.orient
    embedding := full
    avoids := ?_
  }⟩
  intro i a
  exact E.avoids i (Finset.mem_univ i) a

end Erdos547b.ZhaoLemma58OwnerForbiddenCertificate

#print axioms Erdos547b.ZhaoLemma58OwnerForbiddenCertificate.exists_certifiedDynamicEmbedding_of_ownerLocalStepsWithForbidden
