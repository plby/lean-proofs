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
import ErdosProblems.Erdos722.RotationAsymptotic
import ErdosProblems.Erdos722.CoverClique
import Mathlib

/-!
# Abundant rooted rotation covers

The zero-success Paley--Zygmund estimate used for qualitative focusing also
gives a constant-factor lower bound on the number of successful rooted
embeddings.  This file records the division-free finite form needed for the
simultaneous reserve-focusing cover.
-/

namespace Erdos722.RotationAbundance

open Finset
open Erdos722.Probability
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.IntegralGenerators
open Erdos722.Prune
open Erdos722.Rotations
open Erdos722.RotationAsymptotic
open Erdos722.GeneratorAsymptotic
open Erdos722.CoverClique
open Erdos722.Asymptotics

noncomputable section

/-- A division-free half-mean Paley--Zygmund inequality.  If the normalized
second moment is at most `R`, then at least a `1/(4R)` fraction of the sample
space has success count at least half its mean. -/
theorem card_samples_with_small_success_paley_scaled
    {Candidate Sample : Type*} [Fintype Sample] [Nonempty Sample]
    [DecidableEq Candidate] [DecidableEq Sample]
    (candidates : Finset Candidate) (success : Candidate → Finset Sample)
    (R Q : ℕ) (hR : 0 < R)
    (hT : 0 < ∑ c ∈ candidates, (success c).card)
    (hQ : ∑ c ∈ candidates, ∑ d ∈ candidates,
        (success c ∩ success d).card ≤ Q)
    (hratio :
      Fintype.card Sample * Q ≤
        R * (∑ c ∈ candidates, (success c).card) ^ 2) :
    (4 * R) * ((Finset.univ : Finset Sample).filter fun ω ↦
        2 * Fintype.card Sample *
            finiteSuccessCount candidates success ω <
          ∑ c ∈ candidates, (success c).card).card ≤
      (4 * R - 1) * Fintype.card Sample := by
  classical
  let samples := (Finset.univ : Finset Sample)
  let X := finiteSuccessCount candidates success
  let T := ∑ c ∈ candidates, (success c).card
  let S := Fintype.card Sample
  let bad := samples.filter fun ω ↦ 2 * S * X ω < T
  let good := samples.filter fun ω ↦ T ≤ 2 * S * X ω
  have hS : 0 < S := Fintype.card_pos
  have hfirst : ∑ ω ∈ samples, X ω = T := by
    rw [sum_finiteSuccessCount]
    simp [samples, T, X]
  have hpartitionSum :
      (∑ ω ∈ bad, X ω) + ∑ ω ∈ good, X ω = T := by
    have hsplit := Finset.sum_filter_add_sum_filter_not samples
      (fun ω ↦ 2 * S * X ω < T) X
    have hnot : samples.filter (fun ω ↦ ¬ 2 * S * X ω < T) = good := by
      ext ω
      simp [good]
    rw [hnot] at hsplit
    exact hsplit.trans hfirst
  have hbadTerm : ∀ ω ∈ bad, 2 * S * X ω < T := by
    intro ω hω
    exact (Finset.mem_filter.mp hω).2
  have hbadSum : 2 * (∑ ω ∈ bad, X ω) < T := by
    by_cases hbadNonempty : bad.Nonempty
    · have hsum : ∑ ω ∈ bad, 2 * S * X ω < ∑ _ω ∈ bad, T := by
        exact Finset.sum_lt_sum_of_nonempty hbadNonempty hbadTerm
      have hbadCard : bad.card ≤ S := by
        change bad.card ≤ S
        calc
          bad.card ≤ samples.card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ = S := by simp [samples, S]
      have hscaled : S * (2 * (∑ ω ∈ bad, X ω)) < S * T := by
        calc
          S * (2 * (∑ ω ∈ bad, X ω)) =
              ∑ ω ∈ bad, 2 * S * X ω := by
                rw [← Finset.mul_sum]
                ring
          _ < ∑ _ω ∈ bad, T := hsum
          _ = bad.card * T := by simp
          _ ≤ S * T := Nat.mul_le_mul_right T hbadCard
      exact (Nat.mul_lt_mul_left hS).mp (by
        simpa [Nat.mul_assoc] using hscaled)
    · have hbadEq : bad = ∅ := Finset.not_nonempty_iff_eq_empty.mp hbadNonempty
      simpa [hbadEq, T] using hT
  have hhalf : T ≤ 2 * (∑ ω ∈ good, X ω) := by
    omega
  have hsecondGood : ∑ ω ∈ good, (X ω) ^ 2 ≤ Q := by
    calc
      (∑ ω ∈ good, (X ω) ^ 2) ≤
          ∑ ω ∈ samples, (X ω) ^ 2 :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ∑ c ∈ candidates, ∑ d ∈ candidates,
          (success c ∩ success d).card := by
        rw [sum_finiteSuccessCount_sq]
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro d hd
        congr 1
        ext ω
        simp [samples]
      _ ≤ Q := hQ
  have hcauchy :
      (∑ ω ∈ good, X ω) ^ 2 ≤ good.card * Q := by
    calc
      (∑ ω ∈ good, X ω) ^ 2 ≤
          good.card * ∑ ω ∈ good, (X ω) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ ≤ good.card * Q := Nat.mul_le_mul_left _ hsecondGood
  have hTsq : T ^ 2 ≤ 4 * good.card * Q := by
    calc
      T ^ 2 ≤ (2 * (∑ ω ∈ good, X ω)) ^ 2 :=
        Nat.pow_le_pow_left hhalf _
      _ = 4 * (∑ ω ∈ good, X ω) ^ 2 := by ring
      _ ≤ 4 * (good.card * Q) := Nat.mul_le_mul_left _ hcauchy
      _ = 4 * good.card * Q := by ring
  have hQpos : 0 < Q := by
    by_contra hQzero
    have hQeq : Q = 0 := Nat.eq_zero_of_not_pos hQzero
    rw [hQeq] at hTsq
    have hTpos : 0 < T := by simpa [T] using hT
    have : 0 < T ^ 2 := pow_pos hTpos _
    omega
  have hgoodScaled : S ≤ 4 * R * good.card := by
    apply Nat.le_of_mul_le_mul_right (c := Q) ?_ hQpos
    calc
      S * Q ≤ R * T ^ 2 := by simpa [S, T] using hratio
      _ ≤ R * (4 * good.card * Q) := Nat.mul_le_mul_left _ hTsq
      _ = (4 * R * good.card) * Q := by ring
  have hpartition : bad.card + good.card = S := by
    have hcard := Finset.card_filter_add_card_filter_not
      (s := samples) (p := fun ω ↦ 2 * S * X ω < T)
    have hnot : samples.filter (fun ω ↦ ¬ 2 * S * X ω < T) = good := by
      ext ω
      simp [good]
    rw [hnot] at hcard
    simpa [samples, S] using hcard
  have hplus : (4 * R) * bad.card + S ≤ (4 * R) * S := by
    calc
      (4 * R) * bad.card + S ≤
          (4 * R) * bad.card + (4 * R) * good.card :=
        Nat.add_le_add_left hgoodScaled _
      _ = (4 * R) * S := by rw [← Nat.mul_add, hpartition]
  have hfourR : 0 < 4 * R := by positivity
  have hdecomp : 4 * R - 1 + 1 = 4 * R := Nat.sub_add_cancel hfourR
  have hgoal : (4 * R) * bad.card ≤ (4 * R - 1) * S := by
    apply Nat.le_of_add_le_add_right (b := S)
    calc
      (4 * R) * bad.card + S ≤ (4 * R) * S := hplus
      _ = (4 * R - 1 + 1) * S :=
        congrArg (fun t ↦ t * S) hdecomp.symm
      _ = (4 * R - 1) * S + S := by rw [Nat.add_mul, one_mul]
  simpa [bad, X, T, samples, S] using hgoal

/-- Pair-correlation specialization of the half-mean inequality. -/
theorem card_samples_with_small_success_paley_scaled_of_pair_bounds
    {Candidate Sample : Type*} [Fintype Sample] [Nonempty Sample]
    [DecidableEq Candidate] [DecidableEq Sample]
    (candidates : Finset Candidate) (success : Candidate → Finset Sample)
    (good : Candidate → Candidate → Prop) [DecidableRel good]
    (A G L R : ℕ) (hR : 0 < R)
    (hcandidates : 0 < candidates.card) (hApos : 0 < A)
    (hcard : ∀ c ∈ candidates, (success c).card = A)
    (hgood : ∀ c ∈ candidates, ∀ d ∈ candidates, good c d →
      (success c ∩ success d).card ≤ G)
    (hexceptional : ∀ c ∈ candidates,
      (candidates.filter fun d ↦ ¬good c d).card ≤ L)
    (hratio :
      Fintype.card Sample *
          (candidates.card ^ 2 * G + candidates.card * L * A) ≤
        R * (candidates.card * A) ^ 2) :
    (4 * R) * ((Finset.univ : Finset Sample).filter fun ω ↦
        2 * Fintype.card Sample *
            finiteSuccessCount candidates success ω <
          candidates.card * A).card ≤
      (4 * R - 1) * Fintype.card Sample := by
  classical
  let Q := candidates.card ^ 2 * G + candidates.card * L * A
  have hinterAny : ∀ c ∈ candidates, ∀ d ∈ candidates,
      (success c ∩ success d).card ≤ A := by
    intro c hc d hd
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq
      (hcard c hc)
  have hinner : ∀ c ∈ candidates,
      (∑ d ∈ candidates, (success c ∩ success d).card) ≤
        candidates.card * G + L * A := by
    intro c hc
    let goodSet := candidates.filter fun d ↦ good c d
    let badSet := candidates.filter fun d ↦ ¬good c d
    rw [show (∑ d ∈ candidates, (success c ∩ success d).card) =
        (∑ d ∈ goodSet, (success c ∩ success d).card) +
          ∑ d ∈ badSet, (success c ∩ success d).card by
      simpa [goodSet, badSet] using
        (Finset.sum_filter_add_sum_filter_not candidates
          (fun d ↦ good c d)
          (fun d ↦ (success c ∩ success d).card)).symm]
    apply Nat.add_le_add
    · calc
        (∑ d ∈ goodSet, (success c ∩ success d).card) ≤
            ∑ _d ∈ goodSet, G := by
          apply Finset.sum_le_sum
          intro d hd
          have hddata := Finset.mem_filter.mp hd
          exact hgood c hc d hddata.1 hddata.2
        _ = goodSet.card * G := by simp
        _ ≤ candidates.card * G :=
          Nat.mul_le_mul_right G
            (Finset.card_le_card (Finset.filter_subset _ _))
    · calc
        (∑ d ∈ badSet, (success c ∩ success d).card) ≤
            ∑ _d ∈ badSet, A := by
          apply Finset.sum_le_sum
          intro d hd
          exact hinterAny c hc d (Finset.mem_filter.mp hd).1
        _ = badSet.card * A := by simp
        _ ≤ L * A := Nat.mul_le_mul_right A (by
          simpa [badSet] using hexceptional c hc)
  have hQ : ∑ c ∈ candidates, ∑ d ∈ candidates,
      (success c ∩ success d).card ≤ Q := by
    calc
      (∑ c ∈ candidates, ∑ d ∈ candidates,
          (success c ∩ success d).card) ≤
          ∑ _c ∈ candidates, (candidates.card * G + L * A) := by
        apply Finset.sum_le_sum
        intro c hc
        exact hinner c hc
      _ = Q := by simp [Q, pow_two]; ring
  have hT : ∑ c ∈ candidates, (success c).card =
      candidates.card * A := by
    calc
      (∑ c ∈ candidates, (success c).card) =
          ∑ _c ∈ candidates, A := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hcard c hc
      _ = candidates.card * A := by simp
  have hbase := card_samples_with_small_success_paley_scaled
    candidates success R Q hR (by rw [hT]; positivity) hQ (by
      simpa [Q, hT] using hratio)
  simpa [hT] using hbase

/-- Half-mean abundance for rooted rotation samples, under the same
general-position pair estimate used by the qualitative cover. -/
theorem card_rootedRotationSmall_paley_scaled
    {v n m r R : ℕ} {root : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    {φ₀ φ₁ : Fin v ↪ Fin n}
    (hφ₀ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₀)
    (hφ₁ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₁)
    (hdisj : RootedOutsideDisjoint root φ₀ φ₁)
    (hApos : 0 < (rootedRotationSuccess K edges φ₀).card)
    (hR : 0 < R)
    (hratio :
      let candidates :=
        Erdos722.RootedEmbedding.rootedEmbeddings root request
      let A := (rootedRotationSuccess K edges φ₀).card
      let G := (rootedRotationSuccess K edges φ₀ ∩
        rootedRotationSuccess K edges φ₁).card
      let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          (candidates.card ^ 2 * G + candidates.card * L * A) ≤
        R * (candidates.card * A) ^ 2) :
    let candidates := Erdos722.RootedEmbedding.rootedEmbeddings root request
    let success := rootedRotationSuccess K edges
    let A := (success φ₀).card
    (4 * R) * ((rotationSamples n m).filter fun σ ↦
      2 * Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          Erdos722.Probability.finiteSuccessCount candidates success σ <
        candidates.card * A).card ≤
      (4 * R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  classical
  let candidates := Erdos722.RootedEmbedding.rootedEmbeddings root request
  let success := rootedRotationSuccess K edges
  let good : (Fin v ↪ Fin n) → (Fin v ↪ Fin n) → Prop :=
    fun φ ψ ↦ RootedOutsideDisjoint root φ ψ
  let A := (success φ₀).card
  let G := (success φ₀ ∩ success φ₁).card
  let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
  have hφ₀mem : φ₀ ∈ candidates :=
    Erdos722.RootedEmbedding.mem_rootedEmbeddings.mpr hφ₀
  have hcandidates : 0 < candidates.card :=
    Finset.card_pos.mpr ⟨φ₀, hφ₀mem⟩
  have hcard : ∀ φ ∈ candidates, (success φ).card = A := by
    intro φ hφ
    exact card_rootedRotationSuccess_eq hK hedges φ φ₀
  have hgood : ∀ φ ∈ candidates, ∀ ψ ∈ candidates, good φ ψ →
      (success φ ∩ success ψ).card ≤ G := by
    intro φ hφ ψ hψ hφψ
    have hextφ := Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hφ
    have hextψ := Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hψ
    exact Nat.le_of_eq
      (card_rootedRotationSuccess_inter_eq_of_outsideDisjoint
        hK hedges hextφ hextψ hφ₀ hφ₁ hφψ hdisj)
  have hexceptional : ∀ φ ∈ candidates,
      (candidates.filter fun ψ ↦ ¬good φ ψ).card ≤ L := by
    intro φ hφ
    simpa [candidates, good, L, rootedExceptionalPartners] using
      card_rootedExceptionalPartners_le root request φ
  have hbound :=
    card_samples_with_small_success_paley_scaled_of_pair_bounds
      candidates success good A G L R hR hcandidates hApos hcard hgood
        hexceptional (by
          simpa [candidates, success, A, G, L] using hratio)
  simpa [rotationSamples, candidates, success, A] using hbound

/-- A constant pair ratio and the one-power exceptional-partner bound give
half-mean abundance for one rooted request. -/
theorem rootedRotationSmall_paley_of_correlation
    {v n m r c : ℕ} {root : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    {φ₀ φ₁ : Fin v ↪ Fin n}
    (hφ₀ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₀)
    (hφ₁ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₁)
    (hdisj : RootedOutsideDisjoint root φ₀ φ₁)
    (hApos : 0 < (rootedRotationSuccess K edges φ₀).card)
    (hcorr :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          (rootedRotationSuccess K edges φ₀ ∩
            rootedRotationSuccess K edges φ₁).card ≤
        c ^ m * (rootedRotationSuccess K edges φ₀).card *
          (rootedRotationSuccess K edges φ₁).card)
    (hexception :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) ≤
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          (rootedRotationSuccess K edges φ₀).card) :
    let R := c ^ m + 1
    let candidates := Erdos722.RootedEmbedding.rootedEmbeddings root request
    let success := rootedRotationSuccess K edges
    let A := (success φ₀).card
    (4 * R) * ((rotationSamples n m).filter fun σ ↦
      2 * Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          Erdos722.Probability.finiteSuccessCount candidates success σ <
        candidates.card * A).card ≤
      (4 * R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  let candidates := Erdos722.RootedEmbedding.rootedEmbeddings root request
  let A := (rootedRotationSuccess K edges φ₀).card
  let G := (rootedRotationSuccess K edges φ₀ ∩
    rootedRotationSuccess K edges φ₁).card
  let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
  let S := Fintype.card (Fin m → Equiv.Perm (Fin n))
  have hAeq : (rootedRotationSuccess K edges φ₁).card = A :=
    card_rootedRotationSuccess_eq hK hedges φ₁ φ₀
  have hcorr' : S * G ≤ c ^ m * A ^ 2 := by
    simpa [S, G, A, hAeq, pow_two, Nat.mul_assoc] using hcorr
  have hexception' : S * L ≤ candidates.card * A := by
    simpa [S, L, candidates, A] using hexception
  have hratio :
      S * (candidates.card ^ 2 * G + candidates.card * L * A) ≤
        (c ^ m + 1) * (candidates.card * A) ^ 2 := by
    calc
      S * (candidates.card ^ 2 * G + candidates.card * L * A) =
          candidates.card ^ 2 * (S * G) +
            candidates.card * A * (S * L) := by ring
      _ ≤ candidates.card ^ 2 * (c ^ m * A ^ 2) +
            candidates.card * A * (candidates.card * A) := by gcongr
      _ = (c ^ m + 1) * (candidates.card * A) ^ 2 := by ring
  apply card_rootedRotationSmall_paley_scaled hK hedges
    hφ₀ hφ₁ hdisj hApos (by positivity)
  simpa [candidates, A, G, L, S] using hratio

/-- The half-mean threshold can be written without the stabilizer-sized
single-candidate success count. -/
lemma rootedRotation_small_iff_normalized
    {v n m r C X : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    (φ : Fin v ↪ Fin n) :
    let S := Fintype.card (Fin m → Equiv.Perm (Fin n))
    let A := (rootedRotationSuccess K edges φ).card
    let U := Nat.choose n r
    2 * S * X < C * A ↔
      2 * X * U ^ m < C * K.card ^ m := by
  dsimp only
  let S := Fintype.card (Fin m → Equiv.Perm (Fin n))
  let A := (rootedRotationSuccess K edges φ).card
  let U := Nat.choose n r
  have htargets : ∀ i,
      (Erdos722.RootedEmbedding.mapEdge φ (edges i)).card = r := by
    intro i
    exact (Erdos722.RootedEmbedding.card_mapEdge φ (edges i)).trans
      (hedges i)
  have hsuccess : A * U ^ m = K.card ^ m * S := by
    simpa [A, U, S, rootedRotationSuccess, mappedTargets,
      Fintype.card_fun] using
      (card_rainbowHitSamples_mul_choose_pow hK htargets)
  have hS : 0 < S := Fintype.card_pos
  have hU : 0 < U ^ m := by
    by_cases hm : m = 0
    · simp [hm]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let i : Fin m := ⟨0, hmpos⟩
      have hrn : r ≤ n := by
        calc
          r = (edges i).card := (hedges i).symm
          _ = (Erdos722.RootedEmbedding.mapEdge φ (edges i)).card :=
            (Erdos722.RootedEmbedding.card_mapEdge φ _).symm
          _ ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = n := by simp
      exact pow_pos (Nat.choose_pos hrn) m
  constructor
  · intro h
    have hmul := (Nat.mul_lt_mul_right hU).mpr h
    have hscaled : S * (2 * X * U ^ m) < S * (C * K.card ^ m) := by
      calc
        S * (2 * X * U ^ m) = (2 * S * X) * U ^ m := by ring
        _ < (C * A) * U ^ m := hmul
        _ = S * (C * K.card ^ m) := by rw [mul_assoc, hsuccess]; ring
    exact (Nat.mul_lt_mul_left hS).mp hscaled
  · intro h
    have hmul := (Nat.mul_lt_mul_left hS).mpr h
    have hscaled : U ^ m * (2 * S * X) < U ^ m * (C * A) := by
      calc
        U ^ m * (2 * S * X) = S * (2 * X * U ^ m) := by ring
        _ < S * (C * K.card ^ m) := hmul
        _ = C * (K.card ^ m * S) := by ring
        _ = C * (A * U ^ m) := by rw [hsuccess]
        _ = U ^ m * (C * A) := by ring
    exact (Nat.mul_lt_mul_left hU).mp hscaled

/-- Normalized form of `rootedRotationSmall_paley_of_correlation`; its bad
event no longer mentions a request-dependent reference embedding. -/
theorem rootedRotationSmall_normalized_paley_of_correlation
    {v n m r c : ℕ} {root : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    {φ₀ φ₁ : Fin v ↪ Fin n}
    (hφ₀ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₀)
    (hφ₁ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₁)
    (hdisj : RootedOutsideDisjoint root φ₀ φ₁)
    (hApos : 0 < (rootedRotationSuccess K edges φ₀).card)
    (hcorr :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          (rootedRotationSuccess K edges φ₀ ∩
            rootedRotationSuccess K edges φ₁).card ≤
        c ^ m * (rootedRotationSuccess K edges φ₀).card *
          (rootedRotationSuccess K edges φ₁).card)
    (hexception :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) ≤
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          (rootedRotationSuccess K edges φ₀).card) :
    let R := 4 * (c ^ m + 1)
    let candidates := Erdos722.RootedEmbedding.rootedEmbeddings root request
    let success := rootedRotationSuccess K edges
    R * ((rotationSamples n m).filter fun σ ↦
      2 * Erdos722.Probability.finiteSuccessCount candidates success σ *
          Nat.choose n r ^ m <
        candidates.card * K.card ^ m).card ≤
      (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  classical
  let candidates := Erdos722.RootedEmbedding.rootedEmbeddings root request
  let success := rootedRotationSuccess K edges
  let A := (success φ₀).card
  let R₀ := c ^ m + 1
  have hbase := rootedRotationSmall_paley_of_correlation hK hedges
    hφ₀ hφ₁ hdisj hApos hcorr hexception
  have hfilter :
      (rotationSamples n m).filter (fun σ ↦
        2 * Fintype.card (Fin m → Equiv.Perm (Fin n)) *
            Erdos722.Probability.finiteSuccessCount candidates success σ <
          candidates.card * A) =
      (rotationSamples n m).filter (fun σ ↦
        2 * Erdos722.Probability.finiteSuccessCount candidates success σ *
            Nat.choose n r ^ m <
          candidates.card * K.card ^ m) := by
    ext σ
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ ↦
      rootedRotation_small_iff_normalized hK hedges φ₀)
  dsimp only at hbase ⊢
  rw [hfilter] at hbase
  simpa [R₀, candidates, success, A] using hbase

/-- The pruned generator has a uniform constant-fraction family of
half-mean rotation samples for every rooted request. -/
theorem eventually_prunedGenerator_rootedRotation_abundant_failure
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    {v m : ℕ} (root : Finset (Fin v)) (hroot : root.card < v)
    (hmd : m < d) (edges : Fin m → Finset (Fin v))
    (hedges : ∀ i, (edges i).card = r)
    (hproper : ∀ i, (edges i ∩ root).card < r) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (hn : 0 < n)
        (ω : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r ω →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
        let R := 4 * (rotationPairConstant r ^ m + 1)
        let candidates :=
          Erdos722.RootedEmbedding.rootedEmbeddings root request
        let success := rootedRotationSuccess D.Kstar edges
        R * ((rotationSamples n m).filter fun σ ↦
          2 * Erdos722.Probability.finiteSuccessCount candidates success σ *
              Nat.choose n r ^ m <
            candidates.card * D.Kstar.card ^ m).card ≤
          (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  have hd : 1 < d := by
    have hchoose : 0 < Nat.choose q r := Nat.choose_pos hrq.le
    omega
  have hpair := eventually_prunedGenerator_pair_ratio N q r d hr hrq hqd
  have hexpected := eventually_rooted_expected_lower root hroot
    (by omega : 0 < r) hd hmd
  have hexceptional :=
    eventually_rootedExceptionalPartners_lt_rootedEmbeddings root hroot
  have hdegree := eventually_rpow_div_sixteen_le_generatorDegreeLower hd
  filter_upwards [hpair, hexpected, hexceptional, hdegree,
      Filter.eventually_ge_atTop (max (2 * v) r)] with
      n hpair hexpected hexceptional hdegree hnlarge
  intro hn ω D htyp hDK hmass request
  have hnTwoV : 2 * v ≤ n := (le_max_left _ _).trans hnlarge
  have hnr : r ≤ n := (le_max_right _ _).trans hnlarge
  have hDuniform : ∀ e ∈ D.Kstar, e.card = r := by
    intro e he
    exact D.uniform e (D.Kstar_subset he)
  have hpairD : ∀ j < r,
      (orderedIntersectionPairs D.Kstar j).card * Nat.choose n r ^ 2 ≤
        rotationPairConstant r * D.Kstar.card ^ 2 *
          (orderedIntersectionPairs (uniformEdges n r) j).card :=
    hpair hn ω D htyp hDK hmass
  have hdegreePos : 0 < generatorDegreeLower d n := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hstrict : (0 : ℝ) <
        (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 16 := by
      positivity
    have : (0 : ℝ) < generatorDegreeLower d n :=
      hstrict.trans_le hdegree
    exact_mod_cast this
  have huniformPos : 0 < (uniformEdges n (r - 1)).card := by
    simpa [uniformEdges] using Nat.choose_pos (by omega : r - 1 ≤ n)
  have hKstarPos : 0 < D.Kstar.card := by
    have hleft : 0 <
        (uniformEdges n (r - 1)).card * generatorDegreeLower d n :=
      Nat.mul_pos huniformPos hdegreePos
    have hright : 0 < 2 * D.Kstar.card * Nat.choose r (r - 1) :=
      hleft.trans_le hmass
    have htwoK : 0 < 2 * D.Kstar.card :=
      Nat.pos_of_mul_pos_right hright
    exact Nat.pos_of_mul_pos_left htwoK
  have hcandidates : 0 <
      (Erdos722.RootedEmbedding.rootedEmbeddings root request).card := by
    have hdesc : 0 < (n - root.card).descFactorial
        (v - root.card) := Nat.descFactorial_pos.mpr (by omega)
    exact hdesc.trans_le
      (Erdos722.RootedEmbedding.descFactorial_le_card_rootedEmbeddings
        root request)
  obtain ⟨φ₀, φ₁, hφ₀, hφ₁, hdisj⟩ :=
    exists_rootedOutsideDisjoint_of_exceptional_lt root request hcandidates
      (hexceptional request)
  have hApos : 0 < (rootedRotationSuccess D.Kstar edges φ₀).card :=
    rootedRotationSuccess_card_pos hDuniform hKstarPos hedges φ₀
  have hcorr :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          (rootedRotationSuccess D.Kstar edges φ₀ ∩
            rootedRotationSuccess D.Kstar edges φ₁).card ≤
        rotationPairConstant r ^ m *
          (rootedRotationSuccess D.Kstar edges φ₀).card *
          (rootedRotationSuccess D.Kstar edges φ₁).card :=
    rootedRotationSuccess_inter_ratio hDuniform hpairD hedges hproper
      hφ₀ hφ₁ hdisj
  have hexpectedD :
      ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) *
          Nat.choose n r ^ m ≤
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          D.Kstar.card ^ m := by
    apply hexpected D.Kstar
    simpa [uniformEdges] using hmass
  have hexception :
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          ((v - root.card) ^ 2 * n ^ (v - (root.card + 1))) ≤
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          (rootedRotationSuccess D.Kstar edges φ₀).card :=
    rootedRotation_exceptional_of_expected_lower request hDuniform hedges
      φ₀ hexpectedD
  simpa using rootedRotationSmall_normalized_paley_of_correlation
    hDuniform hedges hφ₀ hφ₁ hdisj hApos hcorr hexception

/-- Amplify a uniform half-mean failure estimate over all root requests. -/
theorem exists_amplified_rootedRotationAbundantCover_of_scaled_bad
    {v n m r R g : ℕ} {root : Finset (Fin v)}
    (K : Finset (Finset (Fin n)))
    (edges : Fin m → Finset (Fin v))
    (hR : 0 < R)
    (hbad : ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
      R * ((rotationSamples n m).filter fun σ ↦
        2 * Erdos722.Probability.finiteSuccessCount
              (Erdos722.RootedEmbedding.rootedEmbeddings root request)
              (rootedRotationSuccess K edges) σ *
            Nat.choose n r ^ m <
          (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
            K.card ^ m).card ≤
        (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)))
    (hunion :
      Nat.card (Erdos722.RootedEmbedding.RootRequest v n root) *
          (R - 1) ^ g < R ^ g) :
    ∃ choice : Fin g → (Fin m → Equiv.Perm (Fin n)),
      ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
        ∃ t : Fin g,
          (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
              K.card ^ m ≤
            2 * Erdos722.Probability.finiteSuccessCount
                (Erdos722.RootedEmbedding.rootedEmbeddings root request)
                (rootedRotationSuccess K edges) (choice t) *
              Nat.choose n r ^ m := by
  classical
  let Task := Erdos722.RootedEmbedding.RootRequest v n root
  let Sample := Fin m → Equiv.Perm (Fin n)
  letI : Fintype Task := Fintype.ofInjective
    Erdos722.RootedEmbedding.RootRequest.map (by
      intro a b hab
      cases a with
      | mk amap ainj =>
        cases b with
        | mk bmap binj =>
          simp only [Erdos722.RootedEmbedding.RootRequest.map] at hab
          cases hab
          rfl)
  let tasks : Finset Task := Finset.univ
  let bad : Task → Finset Sample := fun request ↦
    (rotationSamples n m).filter fun σ ↦
      2 * Erdos722.Probability.finiteSuccessCount
            (Erdos722.RootedEmbedding.rootedEmbeddings root request)
            (rootedRotationSuccess K edges) σ *
          Nat.choose n r ^ m <
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
          K.card ^ m
  have hbad' : ∀ request ∈ tasks,
      R * (bad request).card ≤
        (R - 1) * Fintype.card Sample := by
    intro request hrequest
    simpa [bad, Sample] using hbad request
  obtain ⟨choice, hchoice⟩ :=
    Erdos722.Probability.exists_amplified_cover_of_scaled_bad
      tasks bad R (R - 1) g hR hbad' (by
        simpa [tasks, Task] using hunion)
  refine ⟨choice, ?_⟩
  intro request
  obtain ⟨t, ht⟩ := hchoice request (Finset.mem_univ _)
  refine ⟨t, Nat.le_of_not_gt ?_⟩
  intro hlt
  apply ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩

/-- Amplified abundant form: one deterministic family of rotation groups
gives a half-expected number of successful embeddings for every request. -/
theorem eventually_exists_prunedGenerator_rootedRotationAbundantCover
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    {v m : ℕ} (root : Finset (Fin v)) (hroot : root.card < v)
    (hmd : m < d) (edges : Fin m → Finset (Fin v))
    (hedges : ∀ i, (edges i).card = r)
    (hproper : ∀ i, (edges i ∩ root).card < r) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (hn : 0 < n)
        (ω : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r ω →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∃ choice : Fin (generatorEdgeCap d n) →
          (Fin m → Equiv.Perm (Fin n)),
        ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
          ∃ t : Fin (generatorEdgeCap d n),
            (Erdos722.RootedEmbedding.rootedEmbeddings root request).card *
                D.Kstar.card ^ m ≤
              2 * Erdos722.Probability.finiteSuccessCount
                  (Erdos722.RootedEmbedding.rootedEmbeddings root request)
                  (rootedRotationSuccess D.Kstar edges) (choice t) *
                Nat.choose n r ^ m := by
  let R := 4 * (rotationPairConstant r ^ m + 1)
  have hR : 1 < R := by
    dsimp [R]
    have hc : 0 < rotationPairConstant r :=
      rotationPairConstant_pos (by omega)
    have : 0 < rotationPairConstant r ^ m := pow_pos hc _
    omega
  have hfailure :=
    eventually_prunedGenerator_rootedRotation_abundant_failure
      N q r d hr hrq hqd root hroot hmd edges hedges hproper
  have hunion := eventually_rotation_amplification_union_bound v d R
    (by have := (Nat.choose_pos hrq.le).trans hqd; omega) hR
  filter_upwards [hfailure, hunion] with n hfailure hunion
  intro hn ω D htyp hDK hmass
  apply exists_amplified_rootedRotationAbundantCover_of_scaled_bad
    (r := r) (R := R) (g := generatorEdgeCap d n)
    D.Kstar edges (by omega)
  · intro request
    simpa [R] using hfailure hn ω D htyp hDK hmass request
  · exact hunion root

/-- Forgetting the labels of injective `q`-vertex embeddings loses at most
`q^q` possibilities per image set. -/
theorem card_embeddings_le_image_range_mul_pow
    {q n : ℕ} (s : Finset (Fin q ↪ Fin n)) :
    s.card ≤
      (s.image fun φ ↦ Erdos722.RootedEmbedding.mapEdge φ Finset.univ).card *
        q ^ q := by
  classical
  let range : (Fin q ↪ Fin n) → Finset (Fin n) := fun φ ↦
    Erdos722.RootedEmbedding.mapEdge φ Finset.univ
  have hfiber : ∀ B ∈ s.image range,
      (s.filter fun φ ↦ range φ = B).card ≤ q ^ q := by
    intro B hB
    obtain ⟨φ₀, hφ₀s, hφ₀B⟩ := Finset.mem_image.mp hB
    have hBcard : B.card = q := by
      rw [← hφ₀B]
      simp [range, Erdos722.RootedEmbedding.mapEdge]
    let fiber := s.filter fun φ ↦ range φ = B
    let code : ↑fiber → (Fin q → ↑B) := fun z x ↦ ⟨z.1 x, by
      have hzEq : range z.1 = B := (Finset.mem_filter.mp z.2).2
      rw [← hzEq]
      dsimp [range, Erdos722.RootedEmbedding.mapEdge]
      apply Finset.mem_map.mpr
      exact ⟨x, Finset.mem_univ _, rfl⟩⟩
    have hcode : Function.Injective code := by
      intro a b hab
      apply Subtype.ext
      apply Function.Embedding.ext
      intro x
      exact congrArg Subtype.val (congrFun hab x)
    calc
      (s.filter fun φ ↦ range φ = B).card = Fintype.card ↑fiber := by
        change fiber.card = Fintype.card ↑fiber
        exact (Fintype.card_coe fiber).symm
      _ ≤ Fintype.card (Fin q → ↑B) :=
        Fintype.card_le_of_injective code hcode
      _ = B.card ^ q := by simp
      _ = q ^ q := by rw [hBcard]
  rw [Finset.card_eq_sum_card_image range s]
  calc
    (∑ B ∈ s.image range, (s.filter fun φ ↦ range φ = B).card) ≤
        ∑ _B ∈ s.image range, q ^ q := by
      apply Finset.sum_le_sum
      intro B hB
      exact hfiber B hB
    _ = (s.image range).card * q ^ q := by simp
    _ = (s.image (fun φ ↦
        Erdos722.RootedEmbedding.mapEdge φ Finset.univ)).card * q ^ q :=
      rfl

/-- The union of all coordinate hosts in a finite family of rotation
groups. -/
def rotationUnionHost
    {n m g : ℕ} (K : Finset (Finset (Fin n)))
    (choice : Fin g → Fin m → Equiv.Perm (Fin n)) :
    Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin g)).biUnion fun t ↦
    (Finset.univ : Finset (Fin m)).biUnion fun i ↦
      rotateFamily (choice t i) K

/-- The successful rooted embeddings for one fixed rotation sample. -/
def successfulRootedEmbeddings
    {v n m : ℕ} (root : Finset (Fin v))
    (request : Erdos722.RootedEmbedding.RootRequest v n root)
    (K : Finset (Finset (Fin n)))
    (edges : Fin m → Finset (Fin v))
    (σ : Fin m → Equiv.Perm (Fin n)) : Finset (Fin v ↪ Fin n) :=
  (Erdos722.RootedEmbedding.rootedEmbeddings root request).filter fun φ ↦
    σ ∈ rootedRotationSuccess K edges φ

@[simp] lemma card_successfulRootedEmbeddings
    {v n m : ℕ} (root : Finset (Fin v))
    (request : Erdos722.RootedEmbedding.RootRequest v n root)
    (K : Finset (Finset (Fin n)))
    (edges : Fin m → Finset (Fin v))
    (σ : Fin m → Equiv.Perm (Fin n)) :
    (successfulRootedEmbeddings root request K edges σ).card =
      Erdos722.Probability.finiteSuccessCount
        (Erdos722.RootedEmbedding.rootedEmbeddings root request)
        (rootedRotationSuccess K edges) σ := rfl

/-- Successful labelled copies of the rooted complete clique forget to
genuine reserve candidates in the union of the corresponding rotated
coordinate hosts. -/
theorem successful_coverPattern_ranges_subset_reserveCandidates
    {n q r g : ℕ} (hrq : r ≤ q)
    (K : Finset (Finset (Fin n)))
    (choice : Fin g →
      Fin (coverPattern q r).freeEdges.card → Equiv.Perm (Fin n))
    (request : Erdos722.RootedEmbedding.RootRequest q n (coverRoot q r))
    (e : Finset (Fin n))
    (hrequest : Erdos722.RootedEmbedding.requestImage
      (coverRoot q r) request = e)
    (t : Fin g) :
    (successfulRootedEmbeddings (coverRoot q r) request K
        (fun i ↦ (coverPattern q r).freeEdges.equivFin.symm i)
        (choice t)).image (fun φ ↦
          Erdos722.RootedEmbedding.mapEdge φ Finset.univ) ⊆
      reserveCandidates n q r (rotationUnionHost K choice) e := by
  classical
  intro B hB
  obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hB
  have hφdata := Finset.mem_filter.mp hφ
  have hext := Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hφdata.1
  have hsuccess := mem_rootedRotationSuccess.mp hφdata.2
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply mem_uniformEdges.mpr
    simp [Erdos722.RootedEmbedding.mapEdge]
  · have hrootMap : Erdos722.RootedEmbedding.mapEdge φ (coverRoot q r) = e :=
      (Erdos722.RootedEmbedding.mapEdge_root_eq_requestImage_of_extends
        (coverRoot q r) request φ hext).trans hrequest
    rw [← hrootMap]
    exact Finset.map_subset_map.mpr (Finset.subset_univ _)
  · rw [← imageFreeEdges_coverPattern_eq_spill hrq request e
      (Erdos722.RootedEmbedding.mapEdge φ Finset.univ) φ hext hrequest rfl]
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
    let i : Fin (coverPattern q r).freeEdges.card :=
      (coverPattern q r).freeEdges.equivFin ⟨a₀, ha₀⟩
    have hi : rotateEdge (choice t i).symm
        (Erdos722.RootedEmbedding.mapEdge φ a₀) ∈ K := by
      have := hsuccess i
      simpa [i] using this
    apply Finset.mem_biUnion.mpr
    refine ⟨t, Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    exact mem_rotateFamily.mpr hi

/-- Successful labelled rooted clique embeddings whose non-root edges avoid
the already chosen reserve.  These are precisely the copies which can be
used for the separated reserve-focusing cover. -/
def cleanSuccessfulRootedEmbeddings
    {n q r g : ℕ}
    (K reserve : Finset (Finset (Fin n)))
    (choice : Fin g →
      Fin (coverPattern q r).freeEdges.card → Equiv.Perm (Fin n))
    (request : Erdos722.RootedEmbedding.RootRequest q n (coverRoot q r))
    (t : Fin g) : Finset (Fin q ↪ Fin n) :=
  successfulRootedEmbeddings (coverRoot q r) request K
      (fun i ↦ (coverPattern q r).freeEdges.equivFin.symm i)
      (choice t) \
    Erdos722.RootedEmbedding.embeddingsMeeting
      (coverPattern q r) request reserve

/-- After deleting the successful embeddings which meet the old reserve,
forgetting labels lands in the genuine candidate family supported on the
rotated host with the old reserve removed. -/
theorem cleanSuccessful_coverPattern_ranges_subset_reserveCandidates
    {n q r g : ℕ} (hrq : r ≤ q)
    (K reserve : Finset (Finset (Fin n)))
    (choice : Fin g →
      Fin (coverPattern q r).freeEdges.card → Equiv.Perm (Fin n))
    (request : Erdos722.RootedEmbedding.RootRequest q n (coverRoot q r))
    (e : Finset (Fin n))
    (hrequest : Erdos722.RootedEmbedding.requestImage
      (coverRoot q r) request = e)
    (t : Fin g) :
    (cleanSuccessfulRootedEmbeddings K reserve choice request t).image
        (fun φ ↦ Erdos722.RootedEmbedding.mapEdge φ Finset.univ) ⊆
      reserveCandidates n q r (rotationUnionHost K choice \ reserve) e := by
  classical
  intro B hB
  obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.mp hB
  have hclean := Finset.mem_sdiff.mp hφ
  have hcandidate := successful_coverPattern_ranges_subset_reserveCandidates
    hrq K choice request e hrequest t
      (Finset.mem_image.mpr ⟨φ, hclean.1, rfl⟩)
  have hcData := Finset.mem_filter.mp hcandidate
  apply Finset.mem_filter.mpr
  refine ⟨hcData.1, hcData.2.1, ?_⟩
  intro a ha
  have hnotMeeting :=
    (Erdos722.RootedEmbedding.mem_embeddingsMeeting.not.mp hclean.2)
  have hsuccessData := Finset.mem_filter.mp hclean.1
  have hext := Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hsuccessData.1
  have hspillEq := imageFreeEdges_coverPattern_eq_spill hrq request e
    (Erdos722.RootedEmbedding.mapEdge φ Finset.univ) φ hext hrequest rfl
  have haImage : a ∈ Erdos722.RootedEmbedding.imageFreeEdges
      (coverPattern q r) φ := by
    rw [hspillEq]
    exact ha
  have haUnion : a ∈ rotationUnionHost K choice := hcData.2.2 ha
  have haNotReserve : a ∉ reserve := by
    intro haReserve
    exact hnotMeeting ⟨hext, by
      rw [Finset.not_disjoint_iff]
      exact ⟨a, haImage, haReserve⟩⟩
  exact Finset.mem_sdiff.mpr ⟨haUnion, haNotReserve⟩

/-- An abundant rooted rotation family gives the power-cleared candidate
bound whenever its density loss is strictly smaller than the requested
loss.  This is the scalar bridge from half-mean rotation abundance to the
reserve-cover interface. -/
theorem eventually_candidate_power_of_abundant_rotations
    {q r d m Dloss Kloss F : ℕ}
    (hr : 0 < r) (hrq : r < q) (hd : 1 < d)
    (hF : 0 < F)
    (hcross : Dloss * m < d * Kloss)
    (hKloss : Kloss ≤ Dloss * (q - r)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (K : Finset (Finset (Fin n)))
        (request : Erdos722.RootedEmbedding.RootRequest q n (coverRoot q r))
        (candidateCount : ℕ),
      (Nat.choose n (r - 1) * generatorDegreeLower d n ≤
        2 * K.card * Nat.choose r (r - 1)) →
      ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).card * K.card ^ m ≤
        F * candidateCount * Nat.choose n r ^ m) →
      n ^ (Dloss * (q - r) - Kloss) ≤ candidateCount ^ Dloss := by
  let s := q - r
  let a : ℝ := ((d - 1 : ℕ) : ℝ) / d
  let b : ℝ := (r - 1 : ℕ) + a
  let lowerExp : ℝ := (s : ℕ) + b * m
  let targetExp : ℝ :=
    (Dloss * s - Kloss : ℕ) + Dloss * (r * m)
  let raisedLowerExp : ℝ := Dloss * lowerExp
  let Cchoose : ℕ := 2 ^ (r - 1) * Nat.factorial (r - 1)
  let Cedge : ℕ := 32 * r * Cchoose
  let Ctotal : ℝ :=
    (((2 : ℝ) ^ s * (Cedge : ℝ) ^ m) * F) ^ Dloss
  have hs : 0 < s := by dsimp [s]; omega
  have hDpos : 0 < Dloss := by
    by_contra hzero
    have : Dloss = 0 := Nat.eq_zero_of_not_pos hzero
    subst Dloss
    have hKzero : Kloss = 0 := by simpa using hKloss
    subst Kloss
    simp at hcross
  have hCchoose : 0 < Cchoose := by positivity
  have hCedge : 0 < Cedge := by
    dsimp [Cedge]
    positivity
  have hgap : targetExp < raisedLowerExp := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hcrossR : (Dloss : ℝ) * m < d * Kloss := by
      exact_mod_cast hcross
    have hKlossLe : Kloss ≤ Dloss * s := by simpa [s] using hKloss
    dsimp [targetExp, raisedLowerExp, lowerExp, b, a, s]
    rw [Nat.cast_sub hKlossLe]
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    rw [Nat.cast_sub (by omega : 1 ≤ r)]
    push_cast
    field_simp
    nlinarith
  have hdom := eventually_const_mul_rpow_le_rpow hgap
    (show 0 ≤ Ctotal by positivity)
  have hdegreeLower :=
    eventually_rpow_div_sixteen_le_generatorDegreeLower hd
  filter_upwards [hdom, hdegreeLower,
      Filter.eventually_ge_atTop (max (2 * q) (4 * r))] with
      n hdom hdegreeLower hnlarge
  intro K request candidateCount hmass habundant
  have hnTwoQ : 2 * q ≤ n := (le_max_left _ _).trans hnlarge
  have hnFourR : 4 * r ≤ n := (le_max_right _ _).trans hnlarge
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hrootCard : (coverRoot q r).card = r := card_coverRoot hrq.le
  have hbaseline :=
    Erdos722.LocalDecoderAsymptotic.descFactorial_sub_cast_lower
      (n := n) (r := r) (s := s) (by
        have hrs : r + s = q := by dsimp [s]; omega
        simpa [hrs] using hnTwoQ)
  have hcandidate : (n : ℝ) ^ s / (2 : ℝ) ^ s ≤
      (Erdos722.RootedEmbedding.rootedEmbeddings
        (coverRoot q r) request).card := by
    have hdesc :=
      Erdos722.RootedEmbedding.descFactorial_le_card_rootedEmbeddings
        (coverRoot q r) request
    rw [hrootCard] at hdesc
    exact hbaseline.trans (by exact_mod_cast hdesc)
  have hchooseNat :=
    Erdos722.BinomialBounds.pow_le_factorial_mul_choose_sub
      n 0 (r - 1) (by omega : 2 * (0 + (r - 1)) ≤ n)
  have hchoose : (n : ℝ) ^ (r - 1) / Cchoose ≤
      Nat.choose n (r - 1) := by
    have hreal : (n : ℝ) ^ (r - 1) ≤
        (Cchoose : ℝ) * Nat.choose n (r - 1) := by
      exact_mod_cast (by simpa [Cchoose] using hchooseNat)
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < Cchoose)).2 (by
      simpa [mul_comm] using hreal)
  have hmassR :
      (Nat.choose n (r - 1) : ℝ) * generatorDegreeLower d n ≤
        2 * (K.card : ℝ) * r := by
    have hchooseR : Nat.choose r (r - 1) = r := by
      rw [← Nat.choose_symm (by omega : r - 1 ≤ r)]
      simp [show r - (r - 1) = 1 by omega]
    rw [hchooseR] at hmass
    exact_mod_cast hmass
  have hedge : (n : ℝ) ^ b / Cedge ≤ K.card := by
    have hpow : (n : ℝ) ^ b =
        (n : ℝ) ^ (r - 1) * (n : ℝ) ^ a := by
      rw [show b = (r - 1 : ℕ) + a by rfl, Real.rpow_add hnR,
        Real.rpow_natCast]
    have hprod :
        ((n : ℝ) ^ (r - 1) / Cchoose) *
            ((n : ℝ) ^ a / 16) ≤
          (Nat.choose n (r - 1) : ℝ) *
            generatorDegreeLower d n := by gcongr
    calc
      (n : ℝ) ^ b / Cedge =
          (((n : ℝ) ^ (r - 1) / Cchoose) *
            ((n : ℝ) ^ a / 16)) / (2 * r) := by
        rw [hpow]
        dsimp [Cedge]
        push_cast
        field_simp
        <;> ring
      _ ≤ ((Nat.choose n (r - 1) : ℝ) *
            generatorDegreeLower d n) / (2 * r) := by gcongr
      _ ≤ K.card := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * r)).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmassR
  have hlower :
      (n : ℝ) ^ lowerExp /
          ((2 : ℝ) ^ s * (Cedge : ℝ) ^ m) ≤
        ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).card : ℝ) *
          (K.card : ℝ) ^ m := by
    calc
      (n : ℝ) ^ lowerExp /
          ((2 : ℝ) ^ s * (Cedge : ℝ) ^ m) =
        ((n : ℝ) ^ s / (2 : ℝ) ^ s) *
          (((n : ℝ) ^ b / Cedge) ^ m) := by
        rw [show lowerExp = (s : ℕ) + b * m by rfl,
          Real.rpow_add hnR, Real.rpow_natCast,
          Real.rpow_mul hnR.le]
        rw [Real.rpow_natCast, div_pow]
        ring
      _ ≤ ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).card : ℝ) *
          (K.card : ℝ) ^ m := by gcongr
  have habundantR :
      ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).card : ℝ) *
          (K.card : ℝ) ^ m ≤
        F * candidateCount * (Nat.choose n r : ℝ) ^ m := by
    exact_mod_cast habundant
  have hchooseUpper : (Nat.choose n r : ℝ) ^ m ≤
      ((n : ℝ) ^ r) ^ m := by
    gcongr
    exact_mod_cast Nat.choose_le_pow n r
  let Cbase : ℝ := (2 : ℝ) ^ s * (Cedge : ℝ) ^ m
  have hbasePos : 0 < Cbase := by positivity
  have hraw : (n : ℝ) ^ lowerExp ≤
      (Cbase * F) * candidateCount * (n : ℝ) ^ (r * m) := by
    have hmul := mul_le_mul_of_nonneg_left
      (hlower.trans (habundantR.trans (by
        gcongr))) hbasePos.le
    calc
      (n : ℝ) ^ lowerExp =
          Cbase * ((n : ℝ) ^ lowerExp / Cbase) := by field_simp
      _ ≤ Cbase * (F * candidateCount *
          (Nat.choose n r : ℝ) ^ m) := hmul
      _ ≤ Cbase * (F * candidateCount * (((n : ℝ) ^ r) ^ m)) := by
        gcongr
      _ = (Cbase * F) * candidateCount * (n : ℝ) ^ (r * m) := by
        rw [← pow_mul]
        ring
  have hraised : (n : ℝ) ^ raisedLowerExp ≤
      (Cbase * F) ^ Dloss * candidateCount ^ Dloss *
        (n : ℝ) ^ (Dloss * (r * m)) := by
    have hp := pow_le_pow_left₀ (by positivity) hraw Dloss
    calc
      (n : ℝ) ^ raisedLowerExp = ((n : ℝ) ^ lowerExp) ^ Dloss := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hnR.le]
        congr 1
        dsimp [raisedLowerExp]
        ring
      _ ≤ (((Cbase * F) * candidateCount *
          (n : ℝ) ^ (r * m)) ^ Dloss) := hp
      _ = (Cbase * F) ^ Dloss * candidateCount ^ Dloss *
          (n : ℝ) ^ (Dloss * (r * m)) := by
        rw [mul_pow, mul_pow]
        rw [← pow_mul]
        ring
  have hCtotal : Ctotal = (Cbase * F) ^ Dloss := by rfl
  have hchain :
      Ctotal * (n : ℝ) ^ targetExp ≤
        Ctotal * candidateCount ^ Dloss *
          (n : ℝ) ^ (Dloss * (r * m)) :=
    hdom.trans (by simpa [hCtotal] using hraised)
  have htargetPow : (n : ℝ) ^ targetExp =
      (n : ℝ) ^ (Dloss * s - Kloss) *
        (n : ℝ) ^ (Dloss * (r * m)) := by
    have hexp : targetExp =
        ((Dloss * s - Kloss : ℕ) : ℝ) +
          ((Dloss * (r * m) : ℕ) : ℝ) := by
      dsimp [targetExp]
      push_cast
      ring
    rw [hexp, Real.rpow_add hnR, Real.rpow_natCast, Real.rpow_natCast]
  have hpositive : 0 < Ctotal *
      (n : ℝ) ^ (Dloss * (r * m)) := by
    have hCtotalPos : 0 < Ctotal := by
      dsimp [Ctotal]
      positivity
    positivity
  have hcancel : (n : ℝ) ^ (Dloss * s - Kloss) ≤
      (candidateCount : ℝ) ^ Dloss := by
    apply (mul_le_mul_iff_of_pos_left hpositive).mp
    calc
      (Ctotal * (n : ℝ) ^ (Dloss * (r * m))) *
          (n : ℝ) ^ (Dloss * s - Kloss) =
        Ctotal * (n : ℝ) ^ targetExp := by rw [htargetPow]; ring
      _ ≤ Ctotal * candidateCount ^ Dloss *
          (n : ℝ) ^ (Dloss * (r * m)) := hchain
      _ = (Ctotal * (n : ℝ) ^ (Dloss * (r * m))) *
          (candidateCount : ℝ) ^ Dloss := by push_cast; ring
  dsimp [s] at hcancel
  exact_mod_cast hcancel

/-- A bounded set of forbidden ground vertices contains only a lower-order
fraction of an abundant rooted clique sample.  The estimate is deliberately
stated before selecting a particular rotation group: it will be applied to
the one group supplied by the amplified abundance cover. -/
theorem eventually_outsideRootTouch_lt_of_abundant_rotations
    {q r d m C : ℕ}
    (hr : 0 < r) (hrq : r < q) (hd : 1 < d)
    (hcross : 2 * m < d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (K : Finset (Finset (Fin n)))
        (request : Erdos722.RootedEmbedding.RootRequest q n (coverRoot q r))
        (successCount : ℕ) (J : Finset (Fin n)),
      (Nat.choose n (r - 1) * generatorDegreeLower d n ≤
        2 * K.card * Nat.choose r (r - 1)) →
      ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).card * K.card ^ m ≤
        2 * successCount * Nat.choose n r ^ m) →
      J.card ≤ C →
      ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).filter fun phi ↦
        Erdos722.RootedEmbedding.outsideRootTouchHit
          (coverRoot q r) J [] phi).card < successCount := by
  let s := q - r
  let A := s * C
  have hpower := eventually_candidate_power_of_abundant_rotations
    (q := q) (r := r) (d := d) (m := m)
    (Dloss := 2) (Kloss := 1) (F := 2)
    hr hrq hd (by positivity) (by simpa using hcross) (by omega)
  filter_upwards [hpower,
      Filter.eventually_gt_atTop (A ^ 2)] with n hpower hn
  intro K request successCount J hmass habundant hJ
  have hrootCard : (coverRoot q r).card = r := card_coverRoot hrq.le
  have hbad :=
    Erdos722.RootedEmbedding.card_rootedEmbeddings_outsideRootTouches_le
      (coverRoot q r) request J
  rw [hrootCard] at hbad
  have hbadBound :
      ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).filter fun phi ↦
        Erdos722.RootedEmbedding.outsideRootTouchHit
          (coverRoot q r) J [] phi).card ≤ A * n ^ (s - 1) := by
    calc
      _ ≤ (q - r) * J.card * n ^ (q - (r + 1)) := hbad
      _ ≤ (q - r) * C * n ^ (q - (r + 1)) := by gcongr
      _ = A * n ^ (s - 1) := by
        dsimp [A, s]
        congr 1
  have hbadPower :
      ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).filter fun phi ↦
        Erdos722.RootedEmbedding.outsideRootTouchHit
          (coverRoot q r) J [] phi).card ^ 2 <
        n ^ (2 * s - 1) := by
    calc
      _ ≤ (A * n ^ (s - 1)) ^ 2 := Nat.pow_le_pow_left hbadBound 2
      _ = A ^ 2 * n ^ (2 * (s - 1)) := by
        rw [mul_pow, ← pow_mul]
        congr 2
        omega
      _ < n * n ^ (2 * (s - 1)) :=
        Nat.mul_lt_mul_of_pos_right hn (pow_pos (by omega) _)
      _ = n ^ (2 * s - 1) := by
        have hs : 0 < s := by dsimp [s]; omega
        rw [Nat.mul_comm, ← pow_succ]
        congr 1
        omega
  have hsuccessPower : n ^ (2 * s - 1) ≤ successCount ^ 2 := by
    simpa [s] using hpower K request successCount hmass habundant
  have hpowLt :
      ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).filter fun phi ↦
        Erdos722.RootedEmbedding.outsideRootTouchHit
          (coverRoot q r) J [] phi).card ^ 2 < successCount ^ 2 :=
    hbadPower.trans_le hsuccessPower
  exact (Nat.pow_lt_pow_iff_left (by omega : 2 ≠ 0)).mp hpowLt

/-- The amplified rooted rotation cover can be chosen so that, after a
request is fixed, every bounded forbidden vertex set admits a successful
copy whose non-root vertices avoid it.  The same rotation group works for
all forbidden sets attached to that request because its successful sample
is larger than each corresponding one-power-loss bad set. -/
theorem eventually_exists_prunedGenerator_rootedRotationAvoidingCover
    (N q r d C : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    {m : ℕ} (hcross : 2 * m < d) (edges : Fin m → Finset (Fin q))
    (hedges : ∀ i, (edges i).card = r)
    (hproper : ∀ i, (edges i ∩ coverRoot q r).card < r) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (hn : 0 < n)
        (omega : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omega ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omega <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r omega →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∃ choice : Fin (generatorEdgeCap d n) →
          (Fin m → Equiv.Perm (Fin n)),
        ∀ request : Erdos722.RootedEmbedding.RootRequest q n (coverRoot q r),
          ∀ J : Finset (Fin n), J.card ≤ C →
            ∃ (t : Fin (generatorEdgeCap d n))
              (phi : Fin q ↪ Fin n),
              phi ∈ successfulRootedEmbeddings (coverRoot q r) request D.Kstar
                edges (choice t) ∧
              ¬ Erdos722.RootedEmbedding.OutsideRootTouches
                (coverRoot q r) J phi := by
  have hcover := eventually_exists_prunedGenerator_rootedRotationAbundantCover
    N q r d hr hrq hqd (coverRoot q r) (by
      rw [card_coverRoot hrq.le]
      exact hrq) (by omega) edges hedges hproper
  have hchooseOne : 1 < Nat.choose q r := by
    have hpos : 0 < Nat.choose q r := Nat.choose_pos hrq.le
    have hne : Nat.choose q r ≠ 1 := by
      intro heq
      rcases Nat.choose_eq_one_iff.mp heq with hrzero | hqr
      · omega
      · omega
    omega
  have havoid := eventually_outsideRootTouch_lt_of_abundant_rotations
    (q := q) (r := r) (d := d) (m := m) (C := C)
    (by omega) hrq (hchooseOne.trans hqd) hcross
  filter_upwards [hcover, havoid] with n hcover havoid
  intro hn omega D htyp hDK hmass
  obtain ⟨choice, hchoice⟩ := hcover hn omega D htyp hDK hmass
  refine ⟨choice, ?_⟩
  intro request J hJ
  obtain ⟨t, ht⟩ := hchoice request
  let S := successfulRootedEmbeddings
    (coverRoot q r) request D.Kstar edges (choice t)
  let bad := (Erdos722.RootedEmbedding.rootedEmbeddings
    (coverRoot q r) request).filter fun phi ↦
      Erdos722.RootedEmbedding.outsideRootTouchHit
        (coverRoot q r) J [] phi
  have hlt : bad.card < S.card := by
    apply havoid D.Kstar request S.card J (by
      simpa [uniformEdges] using hmass)
    · simpa [S, card_successfulRootedEmbeddings] using ht
    · exact hJ
  have hexists : ∃ phi ∈ S,
      ¬ Erdos722.RootedEmbedding.OutsideRootTouches
        (coverRoot q r) J phi := by
    by_contra hnone
    push_neg at hnone
    have hsub : S ⊆ bad := by
      intro phi hphi
      have hSdata := Finset.mem_filter.mp hphi
      apply Finset.mem_filter.mpr
      refine ⟨hSdata.1, ?_⟩
      exact (Erdos722.RootedEmbedding.outsideRootTouchHit_eq_true_iff
        (coverRoot q r) J [] phi).mpr (hnone phi hphi)
    exact (Nat.not_le_of_lt hlt) (Finset.card_le_card hsub)
  obtain ⟨phi, hphi, hphiAvoid⟩ := hexists
  exact ⟨t, phi, by simpa [S] using hphi, hphiAvoid⟩

/-- A reserve with codimension-one degree `O(n^(1-1/rho))` destroys only
lower-order many rooted clique embeddings.  Consequently an abundant
rotation sample retains at least half of its successful embeddings after
all copies meeting the old reserve are deleted. -/
theorem eventually_twice_meeting_le_of_abundant_rotations
    {q r d m rho F Cdeg : ℕ}
    (hr : 0 < r) (hrq : r < q) (hd : 1 < d)
    (hrho : 0 < rho) (hF : 0 < F)
    (hcross : (2 * rho) * m < d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (K reserve : Finset (Finset (Fin n)))
        (request : Erdos722.RootedEmbedding.RootRequest q n (coverRoot q r))
        (successCount D : ℕ),
      (Nat.choose n (r - 1) * generatorDegreeLower d n ≤
        2 * K.card * Nat.choose r (r - 1)) →
      ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).card * K.card ^ m ≤
        F * successCount * Nat.choose n r ^ m) →
      (∀ g ∈ reserve, g.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        Reserve.localDegree reserve J ≤ D) →
      D ^ rho ≤ Cdeg ^ rho * n ^ (rho - 1) →
      2 * (Erdos722.RootedEmbedding.embeddingsMeeting
          (coverPattern q r) request reserve).card ≤ successCount := by
  let s := q - r
  let M := coverMeetingConstant q r
  let C := 2 * M * Cdeg
  have hs : 0 < s := by dsimp [s]; omega
  have hstrong := eventually_candidate_power_of_abundant_rotations
    (q := q) (r := r) (d := d) (m := m)
    (Dloss := 2 * rho) (Kloss := 1) (F := F)
    hr hrq hd hF (by simpa using hcross) (by
      exact Nat.mul_pos (by positivity : 0 < 2 * rho) (by omega))
  filter_upwards [hstrong,
      Filter.eventually_ge_atTop (max 1 (C ^ (2 * rho)))] with
      n hstrong hn
  intro K reserve request successCount D hmass habundant
    huniform hmax hDpow
  have hnpos : 0 < n := (le_max_left _ _).trans hn
  have hCpow : C ^ (2 * rho) ≤ n := (le_max_right _ _).trans hn
  have hsuccessPower :
      n ^ ((2 * rho) * s - 1) ≤ successCount ^ (2 * rho) := by
    simpa [s] using hstrong K request successCount hmass habundant
  have hmeeting :
      (Erdos722.RootedEmbedding.embeddingsMeeting
        (coverPattern q r) request reserve).card ≤
        M * D * n ^ (s - 1) := by
    have hraw := Erdos722.RootedEmbedding.card_embeddingsMeeting_le_of_codimOne
      (coverPattern q r) request reserve huniform D hmax
    change (Erdos722.RootedEmbedding.embeddingsMeeting
      (coverPattern q r) request reserve).card ≤
        Erdos722.RootedEmbedding.codimOneMeetingBound
          (coverPattern q r) n D at hraw
    exact hraw.trans (by
      simpa [M, s] using codimOneMeetingBound_coverPattern_le hr hrq n D)
  let bad := (Erdos722.RootedEmbedding.embeddingsMeeting
    (coverPattern q r) request reserve).card
  have hbadPower : (2 * bad) ^ (2 * rho) ≤
      C ^ (2 * rho) * n ^ ((2 * rho) * s - 2) := by
    have hpow := Nat.pow_le_pow_left hmeeting (2 * rho)
    have hDpowTwo := Nat.pow_le_pow_left hDpow 2
    calc
      (2 * bad) ^ (2 * rho) =
          2 ^ (2 * rho) * bad ^ (2 * rho) := by rw [mul_pow]
      _ ≤ 2 ^ (2 * rho) * (M * D * n ^ (s - 1)) ^ (2 * rho) :=
        Nat.mul_le_mul_left _ hpow
      _ = (2 * M) ^ (2 * rho) * (D ^ rho) ^ 2 *
          n ^ ((s - 1) * (2 * rho)) := by
        rw [mul_pow, mul_pow, pow_mul, ← pow_mul]
        ring
      _ ≤ (2 * M) ^ (2 * rho) *
          (Cdeg ^ rho * n ^ (rho - 1)) ^ 2 *
            n ^ ((s - 1) * (2 * rho)) := by
        exact Nat.mul_le_mul_right _
          (Nat.mul_le_mul_left _ hDpowTwo)
      _ = C ^ (2 * rho) * n ^ ((2 * rho) * s - 2) := by
        have hexp : (rho - 1) * 2 + (s - 1) * (2 * rho) =
            (2 * rho) * s - 2 := by
          rw [Nat.sub_mul, Nat.sub_mul]
          have htwoRho : 2 ≤ 2 * rho := by nlinarith
          have htwoRhoS : 2 * rho ≤ 2 * rho * s := by
            calc
              2 * rho = 2 * rho * 1 := by ring
              _ ≤ 2 * rho * s := by gcongr; omega
          have hcomm : s * (2 * rho) = 2 * rho * s := by ring
          rw [hcomm]
          omega
        have hCdegPow : (Cdeg ^ rho) ^ 2 = Cdeg ^ (2 * rho) := by
          calc
            (Cdeg ^ rho) ^ 2 = Cdeg ^ (rho * 2) :=
              (pow_mul Cdeg rho 2).symm
            _ = Cdeg ^ (2 * rho) := by congr 1; omega
        have hnPow : (n ^ (rho - 1)) ^ 2 = n ^ ((rho - 1) * 2) :=
          (pow_mul n (rho - 1) 2).symm
        calc
          (2 * M) ^ (2 * rho) *
                (Cdeg ^ rho * n ^ (rho - 1)) ^ 2 *
              n ^ ((s - 1) * (2 * rho)) =
            (2 * M) ^ (2 * rho) * Cdeg ^ (2 * rho) *
              (n ^ ((rho - 1) * 2) *
                n ^ ((s - 1) * (2 * rho))) := by
              rw [mul_pow (Cdeg ^ rho) (n ^ (rho - 1)) 2,
                hCdegPow, hnPow]
              ring
          _ = (2 * M) ^ (2 * rho) * Cdeg ^ (2 * rho) *
              n ^ ((2 * rho) * s - 2) := by
                rw [← pow_add, hexp]
          _ = C ^ (2 * rho) * n ^ ((2 * rho) * s - 2) := by
                dsimp [C]
                rw [mul_pow]
                ring
  have hbadPower' : (2 * bad) ^ (2 * rho) ≤
      n ^ ((2 * rho) * s - 1) := by
    calc
      (2 * bad) ^ (2 * rho) ≤
          C ^ (2 * rho) * n ^ ((2 * rho) * s - 2) := hbadPower
      _ ≤ n * n ^ ((2 * rho) * s - 2) :=
        Nat.mul_le_mul_right _ hCpow
      _ = n ^ ((2 * rho) * s - 1) := by
        have hexp : (2 * rho) * s - 2 + 1 =
            (2 * rho) * s - 1 := by
          have hprod : 2 ≤ 2 * rho * s := by
            calc
              2 = 2 * 1 * 1 := by ring
              _ ≤ 2 * rho * s := by gcongr <;> omega
          omega
        rw [Nat.mul_comm, ← pow_succ, hexp]
  have hfinalPower : (2 * bad) ^ (2 * rho) ≤
      successCount ^ (2 * rho) := hbadPower'.trans hsuccessPower
  have hexp : 2 * rho ≠ 0 := by omega
  have hfinal := (Nat.pow_le_pow_iff_left hexp).mp hfinalPower
  simpa [bad] using hfinal

/-- The complete quantitative bridge used for reserve focusing.  A
half-mean abundant rotation group is cleaned of copies meeting the old
reserve, labels are forgotten with loss at most `q^q`, and the resulting
actual blocks satisfy the requested power-cleared candidate estimate. -/
theorem eventually_clean_candidate_power_of_abundant_rotations
    {q r d m rho Dloss Kloss Cdeg : ℕ}
    (hr : 0 < r) (hrq : r < q) (hd : 1 < d)
    (hrho : 0 < rho)
    (hcrossStrong : (2 * rho) * m < d)
    (hcrossFinal : Dloss * m < d * Kloss)
    (hKloss : Kloss ≤ Dloss * (q - r)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (g : ℕ) (K reserve : Finset (Finset (Fin n)))
        (choice : Fin g →
          Fin (coverPattern q r).freeEdges.card → Equiv.Perm (Fin n))
        (request : Erdos722.RootedEmbedding.RootRequest q n (coverRoot q r))
        (e : Finset (Fin n)) (t : Fin g) (D : ℕ),
      (Nat.choose n (r - 1) * generatorDegreeLower d n ≤
        2 * K.card * Nat.choose r (r - 1)) →
      ((Erdos722.RootedEmbedding.rootedEmbeddings
          (coverRoot q r) request).card * K.card ^ m ≤
        2 * (successfulRootedEmbeddings (coverRoot q r) request K
          (fun i ↦ (coverPattern q r).freeEdges.equivFin.symm i)
          (choice t)).card * Nat.choose n r ^ m) →
      (∀ a ∈ reserve, a.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        Reserve.localDegree reserve J ≤ D) →
      D ^ rho ≤ Cdeg ^ rho * n ^ (rho - 1) →
      Erdos722.RootedEmbedding.requestImage
        (coverRoot q r) request = e →
      n ^ (Dloss * (q - r) - Kloss) ≤
        (reserveCandidates n q r
          (rotationUnionHost K choice \ reserve) e).card ^ Dloss := by
  let Ffinal := 4 * q ^ q
  have hmeeting := eventually_twice_meeting_le_of_abundant_rotations
    (q := q) (r := r) (d := d) (m := m) (rho := rho)
    (F := 2) (Cdeg := Cdeg) hr hrq hd hrho (by positivity) hcrossStrong
  have hfinal := eventually_candidate_power_of_abundant_rotations
    (q := q) (r := r) (d := d) (m := m)
    (Dloss := Dloss) (Kloss := Kloss) (F := Ffinal)
    hr hrq hd (by
      have hq : 0 < q := hr.trans hrq
      dsimp [Ffinal]
      positivity) hcrossFinal hKloss
  filter_upwards [hmeeting, hfinal] with n hmeeting hfinal
  intro g K reserve choice request e t D hmass habundant
    huniform hmax hDpow hrequest
  let S := successfulRootedEmbeddings (coverRoot q r) request K
    (fun i ↦ (coverPattern q r).freeEdges.equivFin.symm i) (choice t)
  let bad := Erdos722.RootedEmbedding.embeddingsMeeting
    (coverPattern q r) request reserve
  let clean := cleanSuccessfulRootedEmbeddings K reserve choice request t
  let ranges := clean.image fun φ ↦
    Erdos722.RootedEmbedding.mapEdge φ Finset.univ
  let candidates := reserveCandidates n q r
    (rotationUnionHost K choice \ reserve) e
  have htwiceBad : 2 * bad.card ≤ S.card := by
    simpa [S, bad] using hmeeting K reserve request S.card D hmass
      (by simpa [S] using habundant) huniform hmax hDpow
  have hsplit := Finset.card_sdiff_add_card_inter S bad
  have hinter : (S ∩ bad).card ≤ bad.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hSdecomp : S.card ≤ clean.card + bad.card := by
    have : S.card ≤ (S \ bad).card + bad.card := by omega
    simpa [clean, cleanSuccessfulRootedEmbeddings, S, bad] using this
  have hbadClean : bad.card ≤ clean.card := by omega
  have hSclean : S.card ≤ 2 * clean.card := by omega
  have hforget := card_embeddings_le_image_range_mul_pow clean
  have hrangesSubset : ranges ⊆ candidates := by
    simpa [ranges, clean, candidates] using
      cleanSuccessful_coverPattern_ranges_subset_reserveCandidates
        hrq.le K reserve choice request e hrequest t
  have hrangesCard : ranges.card ≤ candidates.card :=
    Finset.card_le_card hrangesSubset
  have hcleanCandidate : clean.card ≤ candidates.card * q ^ q :=
    hforget.trans (Nat.mul_le_mul_right _ hrangesCard)
  have hScandidate : S.card ≤ 2 * (q ^ q) * candidates.card := by
    calc
      S.card ≤ 2 * clean.card := hSclean
      _ ≤ 2 * (candidates.card * q ^ q) :=
        Nat.mul_le_mul_left _ hcleanCandidate
      _ = 2 * (q ^ q) * candidates.card := by ring
  apply hfinal K request candidates.card hmass
  calc
    (Erdos722.RootedEmbedding.rootedEmbeddings
        (coverRoot q r) request).card * K.card ^ m ≤
      2 * S.card * Nat.choose n r ^ m := by simpa [S] using habundant
    _ ≤ Ffinal * candidates.card * Nat.choose n r ^ m := by
      have htwo := Nat.mul_le_mul_left 2 hScandidate
      calc
        2 * S.card * Nat.choose n r ^ m ≤
            2 * (2 * q ^ q * candidates.card) * Nat.choose n r ^ m :=
          Nat.mul_le_mul_right _ htwo
        _ = Ffinal * candidates.card * Nat.choose n r ^ m := by
          dsimp [Ffinal]
          ring
    _ = Ffinal * candidates.card * Nat.choose n r ^ m := rfl

end

end Erdos722.RotationAbundance
