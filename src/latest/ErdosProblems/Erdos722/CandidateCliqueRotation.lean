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
import ErdosProblems.Erdos722.CliqueRotationAsymptotic
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Clique rotations over a restricted rooted candidate family

In Lemma 6.3(iv) of Keevash's short proof, the candidate embeddings are not
all embeddings extending the base clique.  They are the large subfamily for
which every distinguished special clique has already been sent to a
monochromatic unsaturated clique.  The remaining exchange cliques are then
handled by fresh independent rotations.

This file isolates the finite second-moment statement for precisely that
situation.  The only new ingredient compared with
`card_rootedRotationFailures_paley_scaled` is that `candidates` is an
arbitrary finite subfamily of the rooted embeddings.  Consequently all
geometric intersection statements are recovered from the supplied rooted
request, while the exceptional-pair count is inherited by restriction from
the ambient rooted family.
-/

namespace Erdos722.CandidateCliqueRotation

open Finset Filter
open Erdos722.Typicality
open Erdos722.Rotations
open Erdos722.RootedEmbedding
open Erdos722.CliqueRotationAsymptotic

noncomputable section

/-- Candidates which fail general position with one fixed rooted
embedding.  Naming the classical filter keeps theorem statements free of
extra decidability parameters. -/
noncomputable def outsideMeetingCandidates
    {v n : ℕ} (root : Finset (Fin v))
    (embeddings : Finset (Fin v ↪ Fin n)) (φ : Fin v ↪ Fin n) :
    Finset (Fin v ↪ Fin n) := by
  classical
  exact embeddings.filter fun ψ ↦ ¬RootedOutsideDisjoint root φ ψ

/-- Restricting the ambient rooted family cannot create more exceptional
partners. -/
theorem card_outsideMeetingCandidates_le
    {v n : ℕ} {root : Finset (Fin v)}
    {request : RootRequest v n root}
    {embeddings : Finset (Fin v ↪ Fin n)}
    (hrooted : ∀ φ ∈ embeddings, ExtendsRequest root request φ)
    (φ : Fin v ↪ Fin n) :
    (outsideMeetingCandidates root embeddings φ).card ≤
      (v - root.card) ^ 2 * n ^ (v - (root.card + 1)) := by
  classical
  apply (Finset.card_le_card ?_).trans
    (card_rootedExceptionalPartners_le root request φ)
  intro ψ hψ
  have hdata : ψ ∈ embeddings ∧ ¬RootedOutsideDisjoint root φ ψ := by
    simpa [outsideMeetingCandidates] using hψ
  change ψ ∈ (rootedEmbeddings root request).filter
    (fun ψ ↦ ¬RootedOutsideDisjoint root φ ψ)
  exact Finset.mem_filter.mpr
    ⟨mem_rootedEmbeddings.mpr (hrooted ψ hdata.1), hdata.2⟩

/-- A Paley--Zygmund zero-count bound for an arbitrary nonempty subfamily of
rooted embeddings.  `hcorr` is the normalized pair correlation for two
general-position candidates and `hexception` pays for candidates meeting
outside the root. -/
theorem candidateRotationFailures_paley_of_correlation
    {v n m q r R : ℕ} {root : Finset (Fin v)}
    {request : RootRequest v n root}
    {U : Finset (Finset (Fin n))}
    {embeddings : Finset (Fin v ↪ Fin n)}
    (hU : ∀ Q ∈ U, Q.card = q)
    {blocks : Fin m → Finset (Fin v)}
    (hblocks : ∀ i, (blocks i).card = q)
    (hproper : ∀ i, (blocks i ∩ root).card < r)
    (hUpos : 0 < U.card)
    (hcandidates : 0 < embeddings.card)
    (hrooted : ∀ φ ∈ embeddings, ExtendsRequest root request φ)
    {L : ℕ}
    (hexceptional : ∀ φ ∈ embeddings,
      (outsideMeetingCandidates root embeddings φ).card ≤ L)
    (hR : 0 < R)
    (hcorr : ∀ φ ∈ embeddings, ∀ ψ ∈ embeddings,
      RootedOutsideDisjoint root φ ψ →
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          (rootedRotationSuccess U blocks φ ∩
            rootedRotationSuccess U blocks ψ).card ≤
        (R - 1) * (rootedRotationSuccess U blocks φ).card *
          (rootedRotationSuccess U blocks ψ).card)
    (hexception : ∀ φ ∈ embeddings,
      Fintype.card (Fin m → Equiv.Perm (Fin n)) * L ≤
        embeddings.card * (rootedRotationSuccess U blocks φ).card) :
    R * ((rotationSamples n m).filter fun σ ↦
      Erdos722.Probability.finiteSuccessCount embeddings
        (rootedRotationSuccess U blocks) σ = 0).card ≤
      (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  classical
  obtain ⟨φ₀, hφ₀⟩ := Finset.card_pos.mp hcandidates
  let A := (rootedRotationSuccess U blocks φ₀).card
  let G := (R - 1) * A ^ 2 /
    Fintype.card (Fin m → Equiv.Perm (Fin n))
  have hsamplePos : 0 < Fintype.card (Fin m → Equiv.Perm (Fin n)) :=
    Fintype.card_pos
  have hApos : 0 < A := by
    dsimp [A]
    exact Erdos722.RotationAsymptotic.rootedRotationSuccess_card_pos
      hU hUpos hblocks φ₀
  have hcard : ∀ φ ∈ embeddings,
      (rootedRotationSuccess U blocks φ).card = A := by
    intro φ hφ
    exact card_rootedRotationSuccess_eq hU hblocks φ φ₀
  have hgood : ∀ φ ∈ embeddings, ∀ ψ ∈ embeddings,
      RootedOutsideDisjoint root φ ψ →
      (rootedRotationSuccess U blocks φ ∩
        rootedRotationSuccess U blocks ψ).card ≤ G := by
    intro φ hφ ψ hψ hdisj
    have h := hcorr φ hφ ψ hψ hdisj
    rw [hcard φ hφ, hcard ψ hψ] at h
    dsimp [G]
    exact (Nat.le_div_iff_mul_le hsamplePos).2 (by
      simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h)
  apply Erdos722.Probability.card_samples_with_no_success_paley_scaled_of_pair_bounds
    embeddings (rootedRotationSuccess U blocks)
      (RootedOutsideDisjoint root) A G L R hR hcandidates hApos hcard
      hgood hexceptional
  have hseparate :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) * G ≤
        (R - 1) * A ^ 2 := by
    dsimp [G]
    exact Nat.mul_div_le _ _
  have hexception₀ := hexception φ₀ hφ₀
  have hmoment := Erdos722.Probability.pairMomentRatio_of_separate_bounds
    (S := Fintype.card (Fin m → Equiv.Perm (Fin n)))
    (C := embeddings.card) (A := A) (G := G) (L := L)
    (Cg := R - 1) (Ce := 1) hseparate (by
      simpa [A, hcard φ₀ hφ₀, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hexception₀)
  have hRdecomp : R - 1 + 1 = R := Nat.sub_add_cancel (by omega)
  simpa [hRdecomp] using hmoment

/-- The preceding theorem with the correlation discharged by the standard
proper-root clique-pair estimate. -/
theorem candidateRotationFailures_paley
    {v n m q r c : ℕ} {root : Finset (Fin v)}
    {request : RootRequest v n root}
    {U : Finset (Finset (Fin n))}
    {embeddings : Finset (Fin v ↪ Fin n)}
    (hU : ∀ Q ∈ U, Q.card = q)
    (hpair : ∀ j < r,
      (orderedIntersectionPairs U j).card * Nat.choose n q ^ 2 ≤
        c * U.card ^ 2 *
          (orderedIntersectionPairs (uniformEdges n q) j).card)
    {blocks : Fin m → Finset (Fin v)}
    (hblocks : ∀ i, (blocks i).card = q)
    (hproper : ∀ i, (blocks i ∩ root).card < r)
    (hUpos : 0 < U.card)
    (hcandidates : 0 < embeddings.card)
    (hrooted : ∀ φ ∈ embeddings, ExtendsRequest root request φ)
    {L : ℕ}
    (hexceptional : ∀ φ ∈ embeddings,
      (outsideMeetingCandidates root embeddings φ).card ≤ L)
    (hexception : ∀ φ ∈ embeddings,
      Fintype.card (Fin m → Equiv.Perm (Fin n)) * L ≤
        embeddings.card * (rootedRotationSuccess U blocks φ).card) :
    let R := c ^ m + 2
    R * ((rotationSamples n m).filter fun σ ↦
      Erdos722.Probability.finiteSuccessCount embeddings
        (rootedRotationSuccess U blocks) σ = 0).card ≤
      (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  let R := c ^ m + 2
  have hR : 0 < R := by positivity
  apply candidateRotationFailures_paley_of_correlation hU hblocks hproper
    hUpos hcandidates hrooted hexceptional hR
  · intro φ hφ ψ hψ hdisj
    have hcorr := rootedUnsaturatedRotationSuccess_inter_ratio
      hU hpair hblocks hproper (hrooted φ hφ) (hrooted ψ hψ) hdisj
    have hc : c ^ m ≤ R - 1 := by dsimp [R]; omega
    exact hcorr.trans (by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_right
        ((rootedRotationSuccess U blocks φ).card *
          (rootedRotationSuccess U blocks ψ).card) hc)
  · exact hexception

/-- Amplify a uniform restricted-candidate failure bound over an arbitrary
finite task family.  The conclusion retains membership in the task's
candidate family, which is the information needed to recover the already
fixed special monochromatic cliques. -/
theorem exists_amplified_candidateRotationCover_of_scaled_bad
    {Task : Type*} [DecidableEq Task]
    {v n m R g : ℕ}
    (tasks : Finset Task)
    (embeddings : Task → Finset (Fin v ↪ Fin n))
    (U : Finset (Finset (Fin n)))
    (blocks : Fin m → Finset (Fin v))
    (hR : 0 < R)
    (hbad : ∀ task ∈ tasks,
      R * ((rotationSamples n m).filter fun σ ↦
        Erdos722.Probability.finiteSuccessCount (embeddings task)
          (rootedRotationSuccess U blocks) σ = 0).card ≤
        (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)))
    (hunion : tasks.card * (R - 1) ^ g < R ^ g) :
    ∃ choice : Fin g → (Fin m → Equiv.Perm (Fin n)),
      ∀ task ∈ tasks, ∃ t : Fin g, ∃ φ ∈ embeddings task,
        ∀ i, rotateEdge (choice t i).symm (mapEdge φ (blocks i)) ∈ U := by
  classical
  let Sample := Fin m → Equiv.Perm (Fin n)
  let bad : Task → Finset Sample := fun task ↦
    (rotationSamples n m).filter fun σ ↦
      Erdos722.Probability.finiteSuccessCount (embeddings task)
        (rootedRotationSuccess U blocks) σ = 0
  have hbad' : ∀ task ∈ tasks,
      R * (bad task).card ≤ (R - 1) * Fintype.card Sample := by
    intro task htask
    simpa [bad, Sample] using hbad task htask
  obtain ⟨choice, hchoice⟩ :=
    Erdos722.Probability.exists_amplified_cover_of_scaled_bad
      tasks bad R (R - 1) g hR hbad' (by
        simpa [Sample] using hunion)
  refine ⟨choice, ?_⟩
  intro task htask
  obtain ⟨t, ht⟩ := hchoice task htask
  have hnonzero :
      Erdos722.Probability.finiteSuccessCount (embeddings task)
        (rootedRotationSuccess U blocks) (choice t) ≠ 0 := by
    intro hzero
    apply ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩
  have hpositive := Nat.pos_of_ne_zero hnonzero
  change 0 < ((embeddings task).filter fun φ ↦
      choice t ∈ rootedRotationSuccess U blocks φ).card at hpositive
  obtain ⟨φ, hφ⟩ := Finset.card_pos.mp hpositive
  have hφdata := Finset.mem_filter.mp hφ
  exact ⟨t, φ, hφdata.1, mem_rootedRotationSuccess.mp hφdata.2⟩

end

end Erdos722.CandidateCliqueRotation
