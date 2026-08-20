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
import ErdosProblems.Erdos722.NibbleProcess
import ErdosProblems.Erdos722.Counting
import Mathlib

/-!
# Exact counters for the clique-removal process

All quantities in the differential-equation analysis are finite cardinalities.
This file records their exact updates and the double counts used to compute
conditional expectations.
-/

namespace Erdos722.NibbleCounters

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.AdaptiveChernoff

noncomputable section

variable {n q r : ℕ}

/-- The residual host after a history. -/
def residualHost (host : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  host \ usedEdges r history

/-- Available-clique degree of a residual host edge. -/
def availableDegree (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e : Finset (Fin n)) : ℕ :=
  ((availableCliques H r history).filter fun Q ↦ e ∈ blockEdges r Q).card

/-- Residual degree of a lower face. -/
def residualFaceDegree (host : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (f : Finset (Fin n)) : ℕ :=
  Erdos722.Reserve.localDegree (residualHost host r history) f

/-- In an `r`-uniform host, a fixed `(r-1)`-face has at most one extension
for each ground vertex. -/
lemma residualFaceDegree_le_n
    {host : Finset (Finset (Fin n))}
    (hr : 0 < r)
    (hhost : host ⊆ Erdos722.Typicality.uniformEdges n r)
    (history : List (Finset (Fin n)))
    {f : Finset (Fin n)} (hf : f.card = r - 1) :
    residualFaceDegree host r history f ≤ n := by
  unfold residualFaceDegree Erdos722.Reserve.localDegree
  have hsub :
      (residualHost host r history).filter (fun e ↦ f ⊆ e) ⊆
        (Erdos722.Typicality.uniformEdges n r).filter (fun e ↦ f ⊆ e) := by
    intro e he
    have hm := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr
      ⟨hhost (Finset.mem_sdiff.mp hm.1).1, hm.2⟩
  calc
    ((residualHost host r history).filter (fun e ↦ f ⊆ e)).card ≤
        ((Erdos722.Typicality.uniformEdges n r).filter (fun e ↦ f ⊆ e)).card :=
      Finset.card_le_card hsub
    _ = Nat.choose (n - f.card) (r - f.card) := by
      rw [Erdos722.Typicality.uniformEdges,
        Finset.card_filter_powersetCard_subset f Finset.univ r
        (Finset.subset_univ f) (by omega)]
      simp
    _ ≤ n := by
      rw [hf]
      have hone : r - (r - 1) = 1 := by omega
      rw [hone, Nat.choose_one_right]
      omega

/-- Available cliques removed when the next block is selected. -/
def deletedCliques (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (Q : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  availableCliques H r history \ availableCliques H r (history ++ [Q])

/-- Available cliques through `e` removed by the next selection. -/
def deletedAtEdge (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e Q : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  (deletedCliques H r history Q).filter fun P ↦ e ∈ blockEdges r P

/-- Residual edges through `f` removed by the next selection. -/
def faceLoss (r : ℕ) (Q f : Finset (Fin n)) : ℕ :=
  ((blockEdges r Q).filter fun e ↦ f ⊆ e).card

lemma availableCliques_append_subset (H : Finset (Finset (Fin n)))
    (r : ℕ) (history : List (Finset (Fin n))) (Q : Finset (Fin n)) :
    availableCliques H r (history ++ [Q]) ⊆ availableCliques H r history := by
  intro P hP
  have hm := mem_availableCliques.mp hP
  apply mem_availableCliques.mpr
  refine ⟨hm.1, hm.2.mono_right ?_⟩
  intro e he
  rw [usedEdges_append_single]
  exact Finset.mem_union_left _ he

lemma availableCliques_sdiff_deleted
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (Q : Finset (Fin n)) :
    availableCliques H r history \ deletedCliques H r history Q =
      availableCliques H r (history ++ [Q]) := by
  ext P
  simp only [deletedCliques, Finset.mem_sdiff]
  have hsub := availableCliques_append_subset H r history Q
  constructor
  · rintro ⟨hPold, hnot⟩
    by_contra hPnew
    exact hnot ⟨hPold, hPnew⟩
  · intro hPnew
    exact ⟨hsub hPnew, fun hdel ↦ hdel.2 hPnew⟩

lemma card_availableCliques_update
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (Q : Finset (Fin n)) :
    (availableCliques H r (history ++ [Q])).card =
      (availableCliques H r history).card -
        (deletedCliques H r history Q).card := by
  have hsub := availableCliques_append_subset H r history Q
  unfold deletedCliques
  rw [Finset.card_sdiff_of_subset hsub]
  exact (Nat.sub_sub_self (Finset.card_le_card hsub)).symm

lemma availableDegree_update
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e Q : Finset (Fin n)) :
    availableDegree H r (history ++ [Q]) e =
      availableDegree H r history e -
        (deletedAtEdge H r history e Q).card := by
  let old := (availableCliques H r history).filter
    (fun P ↦ e ∈ blockEdges r P)
  let new := (availableCliques H r (history ++ [Q])).filter
    (fun P ↦ e ∈ blockEdges r P)
  have hsub : new ⊆ old := Finset.filter_subset_filter _
    (availableCliques_append_subset H r history Q)
  have hdeleted : deletedAtEdge H r history e Q = old \ new := by
    ext P
    simp only [deletedAtEdge, deletedCliques, old, new,
      Finset.mem_filter, Finset.mem_sdiff]
    aesop
  rw [hdeleted]
  change new.card = old.card - (old \ new).card
  rw [Finset.card_sdiff_of_subset hsub]
  exact (Nat.sub_sub_self (Finset.card_le_card hsub)).symm

lemma card_deletedAtEdge_le_availableDegree
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n))) (e Q : Finset (Fin n)) :
    (deletedAtEdge H r history e Q).card ≤
      availableDegree H r history e := by
  apply Finset.card_le_card
  intro P hP
  have hm := Finset.mem_filter.mp hP
  exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hm.1).1, hm.2⟩

lemma residualHost_update (host : Finset (Finset (Fin n)))
    (r : ℕ) (history : List (Finset (Fin n))) (Q : Finset (Fin n)) :
    residualHost host r (history ++ [Q]) =
      residualHost host r history \ blockEdges r Q := by
  ext e
  simp [residualHost, usedEdges_append_single]
  aesop

lemma blockEdges_subset_residual_of_available
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    {history : List (Finset (Fin n))} {Q : Finset (Fin n)}
    (hQ : Q ∈ availableCliques H r history) :
    blockEdges r Q ⊆ residualHost host r history := by
  have hm := mem_availableCliques.mp hQ
  intro e he
  exact Finset.mem_sdiff.mpr
    ⟨hH Q hm.1 he, Finset.disjoint_left.mp hm.2 he⟩

/-- A legal selected `q`-clique removes exactly `choose q r` residual
edges. -/
lemma card_residualHost_update
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    {history : List (Finset (Fin n))} {Q : Finset (Fin n)}
    (hQ : Q ∈ availableCliques H r history) :
    (residualHost host r (history ++ [Q])).card =
      (residualHost host r history).card - Nat.choose q r := by
  rw [residualHost_update]
  have hsub := blockEdges_subset_residual_of_available
    (fun P hP ↦ (hH P hP).2) hQ
  rw [Finset.card_sdiff_of_subset hsub]
  simp [blockEdges,
    (hH Q (availableCliques_subset H r history hQ)).1]

/-- Iterating the preceding identity along a legal path gives an exact
deterministic formula for the residual host size. -/
lemma card_residualHost_append_path
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    {history path : List (Finset (Fin n))}
    (hpath : FollowsAvailable H r history path) :
    (residualHost host r (history ++ path)).card =
      (residualHost host r history).card - path.length * Nat.choose q r := by
  induction path generalizing history with
  | nil => simp
  | cons Q rest ih =>
      have hhead : Q ∈ availableCliques H r history := hpath.1
      have htail := ih (history := history ++ [Q]) hpath.2
      rw [List.length_cons]
      calc
        (residualHost host r (history ++ Q :: rest)).card =
            (residualHost host r ((history ++ [Q]) ++ rest)).card := by
              simp [List.append_assoc]
        _ = (residualHost host r (history ++ [Q])).card -
              rest.length * Nat.choose q r := htail
        _ = ((residualHost host r history).card - Nat.choose q r) -
              rest.length * Nat.choose q r := by
                rw [card_residualHost_update hH hhead]
        _ = (residualHost host r history).card -
              (rest.length + 1) * Nat.choose q r := by
                rw [Nat.sub_sub]
                congr 1
                ring

lemma residualFaceDegree_update
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    {history : List (Finset (Fin n))} {Q f : Finset (Fin n)}
    (hQ : Q ∈ availableCliques H r history) :
    residualFaceDegree host r (history ++ [Q]) f =
      residualFaceDegree host r history f - faceLoss r Q f := by
  unfold residualFaceDegree faceLoss Erdos722.Reserve.localDegree
  rw [residualHost_update]
  have hsub := blockEdges_subset_residual_of_available hH hQ
  have hfilter :
      (blockEdges r Q).filter (fun e ↦ f ⊆ e) ⊆
        (residualHost host r history).filter (fun e ↦ f ⊆ e) :=
    Finset.filter_subset_filter _ hsub
  rw [← Finset.card_sdiff_of_subset hfilter]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  aesop

lemma faceLoss_le_residualFaceDegree
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    {history : List (Finset (Fin n))} {Q f : Finset (Fin n)}
    (hQ : Q ∈ availableCliques H r history) :
    faceLoss r Q f ≤ residualFaceDegree host r history f := by
  unfold faceLoss residualFaceDegree Erdos722.Reserve.localDegree
  exact Finset.card_le_card (Finset.filter_subset_filter _
    (blockEdges_subset_residual_of_available hH hQ))

lemma faceLoss_le_card_blockEdges (r : ℕ) (Q f : Finset (Fin n)) :
    faceLoss r Q f ≤ (blockEdges r Q).card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma card_blockEdges (Q : Finset (Fin n)) :
    (blockEdges r Q).card = Nat.choose Q.card r := by
  simp [blockEdges]

lemma faceLoss_le_choose (Q f : Finset (Fin n)) (hQcard : Q.card = q) :
    faceLoss r Q f ≤ Nat.choose q r := by
  simpa [card_blockEdges, hQcard] using faceLoss_le_card_blockEdges r Q f

lemma faceLoss_eq_zero_of_not_subset {Q f : Finset (Fin n)}
    (hnot : ¬ f ⊆ Q) : faceLoss r Q f = 0 := by
  rw [faceLoss, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have hm := Finset.mem_filter.mp he
  exact hnot (hm.2.trans (Finset.mem_powersetCard.mp hm.1).1)

/-- Exact value `q-r+1` for the number of edges of a `q`-clique extending
an `(r-1)`-face contained in it. -/
lemma faceLoss_eq
    {Q f : Finset (Fin n)} (hQcard : Q.card = q)
    (hfcard : f.card = r - 1) (hfQ : f ⊆ Q)
    (hr : 0 < r) (hrq : r ≤ q) :
    faceLoss r Q f = q - r + 1 := by
  unfold faceLoss blockEdges
  rw [Finset.card_filter_powersetCard_subset f Q r hfQ (by omega)]
  rw [hQcard, hfcard]
  have hone : r - (r - 1) = 1 := by omega
  rw [hone, Nat.choose_one_right]
  omega

/-- Sum of available edge-degrees equals clique size times the number of
available cliques. -/
lemma sum_availableDegree
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host) :
    ∀ history,
      ∑ e ∈ residualHost host r history, availableDegree H r history e =
        Nat.choose q r * (availableCliques H r history).card := by
  intro history
  let A := availableCliques H r history
  calc
    (∑ e ∈ residualHost host r history, availableDegree H r history e) =
        ∑ e ∈ residualHost host r history,
          ∑ Q ∈ A, if e ∈ blockEdges r Q then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      unfold availableDegree
      rw [Finset.card_filter]
    _ = ∑ Q ∈ A, ∑ e ∈ residualHost host r history,
          if e ∈ blockEdges r Q then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ Q ∈ A, Nat.choose q r := by
      apply Finset.sum_congr rfl
      intro Q hQ
      have hQavail : Q ∈ availableCliques H r history := hQ
      have hQH : Q ∈ H := availableCliques_subset H r history hQ
      have hsub := blockEdges_subset_residual_of_available
        (fun P hP ↦ (hH P hP).2) hQavail
      have heq :
          (residualHost host r history).filter (fun e ↦ e ∈ blockEdges r Q) =
            blockEdges r Q := by
        ext e
        simp only [Finset.mem_filter]
        constructor
        · exact fun he ↦ he.2
        · exact fun he ↦ ⟨hsub he, he⟩
      rw [← Finset.card_filter, heq, card_blockEdges, (hH Q hQH).1]
    _ = _ := by simp [A, Nat.mul_comm]

/-- Uniform lower edge-degree bounds give a lower bound for the number of
available cliques, without introducing a separate clique-count counter. -/
lemma card_residual_mul_degreeLower_le
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (history : List (Finset (Fin n))) (L : ℕ)
    (hlower : ∀ e ∈ residualHost host r history,
      L ≤ availableDegree H r history e) :
    (residualHost host r history).card * L ≤
      Nat.choose q r * (availableCliques H r history).card := by
  calc
    (residualHost host r history).card * L =
        ∑ _e ∈ residualHost host r history, L := by simp
    _ ≤ ∑ e ∈ residualHost host r history,
        availableDegree H r history e := by
          exact Finset.sum_le_sum fun e he ↦ hlower e he
    _ = Nat.choose q r * (availableCliques H r history).card :=
      sum_availableDegree hH history

/-- Uniform upper edge-degree bounds give the matching upper bound for the
number of available cliques. -/
lemma choose_mul_card_available_le_residual_mul_degreeUpper
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (history : List (Finset (Fin n))) (U : ℕ)
    (hupper : ∀ e ∈ residualHost host r history,
      availableDegree H r history e ≤ U) :
    Nat.choose q r * (availableCliques H r history).card ≤
      (residualHost host r history).card * U := by
  rw [← sum_availableDegree hH history]
  calc
    (∑ e ∈ residualHost host r history,
        availableDegree H r history e) ≤
        ∑ _e ∈ residualHost host r history, U := by
          exact Finset.sum_le_sum fun e he ↦ hupper e he
    _ = (residualHost host r history).card * U := by simp

/-- Exact conditional mean of one face loss under uniform selection. -/
lemma sum_uniformStep_mul_faceLoss
    (H : Finset (Finset (Fin n))) (r : ℕ)
    (history : List (Finset (Fin n)))
    (hne : (availableCliques H r history).Nonempty)
    (f : Finset (Fin n)) :
    (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q * faceLoss r Q f) =
      (∑ Q ∈ availableCliques H r history, faceLoss r Q f : ℝ) /
        (availableCliques H r history).card := by
  have hcard : ((availableCliques H r history).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  rw [div_eq_mul_inv]
  calc
    (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q * faceLoss r Q f) =
        ∑ Q ∈ availableCliques H r history,
          ((availableCliques H r history).card : ℝ)⁻¹ * faceLoss r Q f := by
      calc
        _ = ∑ Q : Finset (Fin n), if Q ∈ availableCliques H r history then
              ((availableCliques H r history).card : ℝ)⁻¹ * faceLoss r Q f
            else 0 := by
          apply Finset.sum_congr rfl
          intro Q _hQ
          by_cases hQa : Q ∈ availableCliques H r history <;>
            simp [uniformStep, hQa]
        _ = _ := by
          rw [← Finset.sum_filter]
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = (∑ Q ∈ availableCliques H r history, faceLoss r Q f : ℝ) *
          ((availableCliques H r history).card : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro Q _hQ
      ring

/-- Double-count the selected clique/edge incidences through one face. -/
lemma sum_faceLoss_eq_sum_availableDegree
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    (history : List (Finset (Fin n))) (f : Finset (Fin n)) :
    (∑ Q ∈ availableCliques H r history, faceLoss r Q f) =
      ∑ e ∈ (residualHost host r history).filter (fun e ↦ f ⊆ e),
        availableDegree H r history e := by
  calc
    (∑ Q ∈ availableCliques H r history, faceLoss r Q f) =
        ∑ Q ∈ availableCliques H r history,
          ∑ e ∈ residualHost host r history,
            if f ⊆ e ∧ e ∈ blockEdges r Q then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      have hsub := blockEdges_subset_residual_of_available hH hQ
      unfold faceLoss
      rw [Finset.card_filter]
      calc
        (∑ e ∈ blockEdges r Q, if f ⊆ e then 1 else 0) =
            ∑ e ∈ blockEdges r Q,
              if e ∈ blockEdges r Q then (if f ⊆ e then 1 else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro e he
          simp [he]
        _ =
            ∑ e ∈ residualHost host r history,
              if e ∈ blockEdges r Q then (if f ⊆ e then 1 else 0) else 0 := by
          apply Finset.sum_subset hsub
          intro e he _heQ
          simp only [_heQ, if_false]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro e _he
          by_cases hf : f ⊆ e <;> by_cases heQ : e ∈ blockEdges r Q <;>
            simp [hf, heQ]
    _ = ∑ e ∈ residualHost host r history,
          ∑ Q ∈ availableCliques H r history,
            if f ⊆ e ∧ e ∈ blockEdges r Q then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ (residualHost host r history).filter (fun e ↦ f ⊆ e),
          availableDegree H r history e := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hf : f ⊆ e
      · simp only [hf, true_and, if_true]
        unfold availableDegree
        rw [Finset.card_filter]
      · simp [hf]

/-- The face-loss numerator is at most the current residual face degree
times a uniform upper available-degree bound. -/
lemma sum_faceLoss_le_faceDegree_mul_degreeUpper
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    (history : List (Finset (Fin n))) (f : Finset (Fin n)) (U : ℕ)
    (hupper : ∀ e ∈ residualHost host r history,
      availableDegree H r history e ≤ U) :
    (∑ Q ∈ availableCliques H r history, faceLoss r Q f) ≤
      residualFaceDegree host r history f * U := by
  rw [sum_faceLoss_eq_sum_availableDegree hH]
  calc
    (∑ e ∈ (residualHost host r history).filter (fun e ↦ f ⊆ e),
        availableDegree H r history e) ≤
        ∑ _e ∈ (residualHost host r history).filter (fun e ↦ f ⊆ e), U := by
          apply Finset.sum_le_sum
          intro e he
          exact hupper e (Finset.mem_filter.mp he).1
    _ = residualFaceDegree host r history f * U := by
      simp [residualFaceDegree, Erdos722.Reserve.localDegree]

/-- Uniform lower edge-degree bounds give the matching lower bound for the
face-loss numerator. -/
lemma faceDegree_mul_degreeLower_le_sum_faceLoss
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, blockEdges r Q ⊆ host)
    (history : List (Finset (Fin n))) (f : Finset (Fin n)) (L : ℕ)
    (hlower : ∀ e ∈ residualHost host r history,
      L ≤ availableDegree H r history e) :
    residualFaceDegree host r history f * L ≤
      ∑ Q ∈ availableCliques H r history, faceLoss r Q f := by
  rw [sum_faceLoss_eq_sum_availableDegree hH]
  calc
    residualFaceDegree host r history f * L =
        ∑ _e ∈ (residualHost host r history).filter (fun e ↦ f ⊆ e), L := by
          simp [residualFaceDegree, Erdos722.Reserve.localDegree]
    _ ≤ ∑ e ∈ (residualHost host r history).filter (fun e ↦ f ⊆ e),
        availableDegree H r history e := by
          apply Finset.sum_le_sum
          intro e he
          exact hlower e (Finset.mem_filter.mp he).1

end

end Erdos722.NibbleCounters
