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

import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic

/-!
# Erdős Problem 1031

Prömel and Rödl proved that every graph with no clique or independent set
of order `C log n` contains every graph of order `c(C) log n` as an induced
subgraph.  Taking the target to be a cycle gives the requested induced,
nonempty, noncomplete regular subgraph.

The detailed mathematical proof and the declaration-level Leanization plan
are in `tex/1031.tex`.
-/

open Fintype
open scoped Classical SimpleGraph

namespace Erdos1031

open SimpleGraph

/-- The order of a largest trivial (complete or empty) induced subgraph. -/
noncomputable def homNum {V : Type*} (G : SimpleGraph V) : ℕ :=
  max G.cliqueNum G.indepNum

/-- `G` contains every graph on exactly `k` labelled vertices as an induced
subgraph.  Exact-order universality is all that is needed for Problem 1031. -/
def IsInducedUniversalAt {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ H : SimpleGraph (Fin k), H ⊴ G

/-- The number of edges in the subgraph induced on a finite vertex set.  `Nat.card`
keeps this definition independent of a chosen decidability instance for adjacency. -/
noncomputable def edgeCountOn {V : Type*} [Finite V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce (S : Set V)).edgeSet

/-- The induced graph on `S` has edge density at most `ε`, with the usual
normalization `2e/(|S|(|S|-1))`. -/
def IsSparseOn {V : Type*} [Finite V]
    (G : SimpleGraph V) (ε : ℝ) (S : Finset V) : Prop :=
  2 * (edgeCountOn G S : ℝ) ≤ ε * S.card * (S.card - 1)

/-- The induced graph on `S` has edge density at least `1-ε`. -/
def IsDenseOn {V : Type*} [Finite V]
    (G : SimpleGraph V) (ε : ℝ) (S : Finset V) : Prop :=
  IsSparseOn Gᶜ ε S

@[simp] lemma homNum_compl {V : Type*} (G : SimpleGraph V) :
    homNum Gᶜ = homNum G := by
  simp [homNum, max_comm]

@[simp] lemma isSparseOn_compl {V : Type*} [Finite V]
    (G : SimpleGraph V) (ε : ℝ) (S : Finset V) :
    IsSparseOn Gᶜ ε S ↔ IsDenseOn G ε S := by
  rfl

@[simp] lemma isDenseOn_compl {V : Type*} [Finite V]
    (G : SimpleGraph V) (ε : ℝ) (S : Finset V) :
    IsDenseOn Gᶜ ε S ↔ IsSparseOn G ε S := by
  simp [IsDenseOn]

lemma indepNum_induce_le {V : Type*} [Finite V]
    (G : SimpleGraph V) (S : Set V) :
    (G.induce S).indepNum ≤ G.indepNum := by
  have hcompl : (G.induce S)ᶜ = Gᶜ.induce S := by
    ext x y
    simp [SimpleGraph.compl_adj, Subtype.ext_iff]
  calc
    (G.induce S).indepNum = (G.induce S)ᶜ.cliqueNum := by simp
    _ = (Gᶜ.induce S).cliqueNum := by rw [hcompl]
    _ ≤ Gᶜ.cliqueNum := Gᶜ.cliqueNum_induce_le S
    _ = G.indepNum := by simp

lemma homNum_induce_le {V : Type*} [Finite V]
    (G : SimpleGraph V) (S : Set V) :
    homNum (G.induce S) ≤ homNum G := by
  exact max_le_max (G.cliqueNum_induce_le S) (indepNum_induce_le G S)

lemma edgeCountOn_eq_card_edgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) [DecidableRel G.Adj] :
    edgeCountOn G S = (G.induce (S : Set V)).edgeFinset.card := by
  rw [edgeCountOn, Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

/-! ## A finite asymmetric Ramsey bound -/

/-- The Erdős--Szekeres binomial upper bound for the two-colour Ramsey
number, indexed so that zero-size requests cause no special obligations. -/
def ramseyBound (a b : ℕ) : ℕ :=
  Nat.choose (a + b - 2) (a - 1)

lemma ramseyBound_step (a b : ℕ) :
    ramseyBound (a + 2) (b + 2) =
      ramseyBound (a + 1) (b + 2) + ramseyBound (a + 2) (b + 1) := by
  simp only [ramseyBound]
  have h₁ : a + 2 + (b + 2) - 2 = a + b + 2 := by omega
  have h₂ : a + 1 + (b + 2) - 2 = a + b + 1 := by omega
  have h₃ : a + 2 + (b + 1) - 2 = a + b + 1 := by omega
  have h₄ : a + 2 - 1 = a + 1 := by omega
  have h₅ : a + 1 - 1 = a := by omega
  rw [h₁, h₂, h₃, h₄, h₅]
  simpa [Nat.add_assoc] using Nat.choose_succ_succ (a + b + 1) a

lemma ramseyBound_one_left (b : ℕ) : ramseyBound 1 b = 1 := by
  simp [ramseyBound]

lemma ramseyBound_one_right (a : ℕ) (_ha : 1 ≤ a) : ramseyBound a 1 = 1 := by
  simp [ramseyBound, Nat.choose_self]

lemma ramseyBound_pos {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 < ramseyBound a b := by
  rw [ramseyBound]
  exact Nat.choose_pos (by omega)

lemma ramseyBound_comm {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ramseyBound a b = ramseyBound b a := by
  rw [ramseyBound, ramseyBound]
  have hab : a + b - 2 = (a - 1) + (b - 1) := by omega
  have hba : b + a - 2 = (a - 1) + (b - 1) := by omega
  rw [hab, hba]
  exact Nat.choose_symm_add

lemma ramseyBound_recurrence {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ramseyBound a b = ramseyBound (a - 1) b + ramseyBound a (b - 1) := by
  obtain ⟨a', ha'⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  subst a
  subst b
  simpa using ramseyBound_step a' b'

/-- Finset form of the asymmetric Erdős--Szekeres Ramsey bound. -/
theorem exists_clique_or_indep_of_ramseyBound_le
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcard : ramseyBound a b ≤ S.card) :
    (∃ T : Finset V, T ⊆ S ∧ G.IsNClique a T) ∨
      ∃ T : Finset V, T ⊆ S ∧ G.IsNIndepSet b T := by
  classical
  induction hsum : a + b using Nat.strong_induction_on generalizing a b S with
  | h n ih =>
      obtain ⟨v, hv⟩ : ∃ v, v ∈ S := by
        exact S.card_pos.mp ((ramseyBound_pos ha hb).trans_le hcard)
      by_cases ha1 : a = 1
      · subst a
        exact Or.inl ⟨{v}, by simpa using hv, by simp⟩
      by_cases hb1 : b = 1
      · subst b
        exact Or.inr ⟨{v}, by simpa using hv,
          ⟨by simp [SimpleGraph.isIndepSet_iff], by simp⟩⟩
      have ha2 : 2 ≤ a := by omega
      have hb2 : 2 ≤ b := by omega
      let R : Finset V := S.erase v
      let N : Finset V := R.filter (G.Adj v)
      let M : Finset V := R.filter (fun w ↦ ¬G.Adj v w)
      have hNM : N.card + M.card = R.card := by
        simpa [N, M] using R.card_filter_add_card_filter_not (G.Adj v)
      have hR : R.card + 1 = S.card := by
        rw [show R.card = S.card - 1 by simp [R, Finset.card_erase_of_mem hv]]
        have : 0 < S.card := Finset.card_pos.mpr ⟨v, hv⟩
        omega
      have hrec := ramseyBound_recurrence ha2 hb2
      by_cases hNcard : ramseyBound (a - 1) b ≤ N.card
      · have hsmall : a - 1 + b < n := by omega
        have hNsub : N ⊆ S := by
          intro x hx
          exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx).1
        rcases ih (a - 1 + b) hsmall N (a - 1) b (by omega) hb
            hNcard rfl with hcl | hind
        · obtain ⟨T, hTN, hTcl⟩ := hcl
          refine Or.inl ⟨insert v T, ?_, ?_⟩
          · exact Finset.insert_subset hv (hTN.trans hNsub)
          · have hadj : ∀ x ∈ T, G.Adj v x := by
              intro x hx
              exact (Finset.mem_filter.mp (hTN hx)).2
            simpa [Nat.sub_add_cancel ha] using hTcl.insert hadj
        · obtain ⟨T, hTN, hTind⟩ := hind
          exact Or.inr ⟨T, hTN.trans hNsub, hTind⟩
      · have hMcard : ramseyBound a (b - 1) ≤ M.card := by
          have hp₁ := ramseyBound_pos (by omega : 1 ≤ a - 1) hb
          have hp₂ := ramseyBound_pos ha (by omega : 1 ≤ b - 1)
          omega
        have hsmall : a + (b - 1) < n := by omega
        have hMsub : M ⊆ S := by
          intro x hx
          exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hx).1
        rcases ih (a + (b - 1)) hsmall M a (b - 1) ha (by omega)
            hMcard rfl with hcl | hind
        · obtain ⟨T, hTM, hTcl⟩ := hcl
          exact Or.inl ⟨T, hTM.trans hMsub, hTcl⟩
        · obtain ⟨T, hTM, hTind⟩ := hind
          refine Or.inr ⟨insert v T, ?_, ?_⟩
          · exact Finset.insert_subset hv (hTM.trans hMsub)
          · have hnonadj : ∀ x ∈ T, Gᶜ.Adj v x := by
              intro x hx
              have hxM := Finset.mem_filter.mp (hTM hx)
              rw [SimpleGraph.compl_adj]
              exact ⟨(Finset.mem_erase.mp hxM.1).1.symm, hxM.2⟩
            have hclcompl : Gᶜ.IsNClique (b - 1) T := by simpa using hTind
            simpa [Nat.sub_add_cancel hb] using hclcompl.insert hnonadj

/-- Numerical consequence of the asymmetric Ramsey bound, stated directly
in terms of clique and independence numbers. -/
lemma ramseyBound_le_card_imp_le_homNum
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcard : ramseyBound a b ≤ S.card) :
    a ≤ homNum G ∨ b ≤ homNum G := by
  rcases exists_clique_or_indep_of_ramseyBound_le G S a b ha hb hcard with h | h
  · obtain ⟨T, _, hT⟩ := h
    exact Or.inl <| (hT.card_eq ▸ hT.isClique.card_le_cliqueNum).trans (Nat.le_max_left ..)
  · obtain ⟨T, _, hT⟩ := h
    exact Or.inr <| (hT.card_eq ▸ hT.isIndepSet.card_le_indepNum).trans (Nat.le_max_right ..)

/-! ## The fixed-density Erdős--Hajnal pair lemma -/

/-- Across an ordered pair `(A,B)`, every vertex of `A` sees fewer than
one quarter of `B`.  The division-free form is convenient for finite
cardinality estimates. -/
def IsRecipSparsePair {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : ℕ) (A B : Finset V) : Prop :=
  ∀ x ∈ A, r * (B.filter (G.Adj x)).card < B.card

/-- Across an ordered pair `(A,B)`, every vertex of `A` misses fewer than
one quarter of `B`. -/
def IsRecipDensePair {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : ℕ) (A B : Finset V) : Prop :=
  ∀ x ∈ A, r * (B.filter (fun y ↦ ¬G.Adj x y)).card < B.card

/-- A large quarter-sparse or quarter-dense ordered pair inside `S`. -/
def HasRecipPair {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r : ℕ) (S : Finset V) (q : ℕ) : Prop :=
  ∃ A B : Finset V,
    A ⊆ S ∧ B ⊆ S ∧ Disjoint A B ∧ q ≤ A.card ∧ q ≤ B.card ∧
      (IsRecipSparsePair G r A B ∨ IsRecipDensePair G r A B)

/-- If no large sparse/dense pair exists, one can choose the next vertex
of a greedy induced embedding while retaining at least a quarter of every
later candidate set. -/
lemma exists_good_candidate_of_not_hasRecipPair
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {r k q : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (S : Finset V) (H : SimpleGraph (Fin k))
    (W : Fin k → Finset V) (hWS : ∀ j, W j ⊆ S)
    (hWdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    {i : Fin k} (hWi : k * q ≤ (W i).card)
    (hWq : ∀ j, i < j → q ≤ (W j).card)
    (hno : ¬HasRecipPair G r S q) :
    ∃ x ∈ W i, ∀ j : Fin k, i < j →
      if H.Adj i j then
        (W j).card ≤ r * ((W j).filter (G.Adj x)).card
      else
        (W j).card ≤ r * ((W j).filter (fun y ↦ ¬G.Adj x y)).card := by
  classical
  by_contra! hbad
  let badIndex (x : V) : Fin k :=
    if hx : x ∈ W i then Classical.choose (hbad x hx) else ⟨0, hk⟩
  have badIndex_spec {x : V} (hx : x ∈ W i) :
      i < badIndex x ∧
        (if H.Adj i (badIndex x) then
          r * ((W (badIndex x)).filter (G.Adj x)).card < (W (badIndex x)).card
        else
          r * ((W (badIndex x)).filter (fun y ↦ ¬G.Adj x y)).card <
            (W (badIndex x)).card) := by
    have hs := Classical.choose_spec (hbad x hx)
    simp only [badIndex, hx, ↓reduceDIte] at hs ⊢
    refine ⟨hs.1, ?_⟩
    by_cases hadj : H.Adj i (Classical.choose (hbad x hx))
    · simp [hadj] at hs ⊢
      omega
    · simp [hadj] at hs ⊢
      omega
  obtain ⟨j, -, hjcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := W i) (t := Finset.univ) (f := badIndex) (n := q)
      (by simp) ⟨⟨0, hk⟩, by simp⟩ (by simpa using hWi)
  let A : Finset V := (W i).filter (fun x ↦ badIndex x = j)
  have hAcard : q ≤ A.card := by simpa [A] using hjcard
  have hijlt : i < j := by
    obtain ⟨x, hxA⟩ := Finset.card_pos.mp (lt_of_lt_of_le hq hAcard)
    have hxWi := (Finset.mem_filter.mp hxA).1
    have hxj := (Finset.mem_filter.mp hxA).2
    have hijlt := (badIndex_spec hxWi).1
    rw [hxj] at hijlt
    exact hijlt
  have hij : i ≠ j := ne_of_lt hijlt
  have hAsub : A ⊆ S := (Finset.filter_subset _ _).trans (hWS i)
  have hAB : Disjoint A (W j) :=
    Finset.disjoint_of_subset_left (Finset.filter_subset _ _) (hWdisj i j hij)
  apply hno
  refine ⟨A, W j, hAsub, hWS j, hAB, hAcard, hWq j hijlt, ?_⟩
  by_cases hadj : H.Adj i j
  · left
    intro x hx
    have hxWi : x ∈ W i := (Finset.mem_filter.mp hx).1
    have hxj : badIndex x = j := (Finset.mem_filter.mp hx).2
    simpa [IsRecipSparsePair, hxj, hadj] using (badIndex_spec hxWi).2
  · right
    intro x hx
    have hxWi : x ∈ W i := (Finset.mem_filter.mp hx).1
    have hxj : badIndex x = j := (Finset.mem_filter.mp hx).2
    simpa [IsRecipDensePair, hxj, hadj] using (badIndex_spec hxWi).2

/-- Candidates for the next vertices in the greedy induced embedding. -/
noncomputable def greedyCandidates
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {k : ℕ} (H : SimpleGraph (Fin k)) (blocks : Fin k → Finset V)
    {i : ℕ} (hi : i ≤ k) (f : Fin i ↪ V) (j : Fin k) : Finset V :=
  (blocks j).filter fun x ↦
    ∀ r : Fin i, G.Adj (f r) x ↔ H.Adj (Fin.castLE hi r) j

@[simp] lemma mem_greedyCandidates
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {k : ℕ} (H : SimpleGraph (Fin k)) (blocks : Fin k → Finset V)
    {i : ℕ} (hi : i ≤ k) (f : Fin i ↪ V) (j : Fin k) (x : V) :
    x ∈ greedyCandidates G H blocks hi f j ↔
      x ∈ blocks j ∧
        ∀ r : Fin i, G.Adj (f r) x ↔ H.Adj (Fin.castLE hi r) j := by
  simp [greedyCandidates]

lemma recip_power_step {r k i q old new : ℕ} (hr : 1 ≤ r) (hi : i < k)
    (hlower : k * r ^ (k - i) * q ≤ old) (hrecip : old ≤ r * new) :
    k * r ^ (k - (i + 1)) * q ≤ new := by
  have hsub : k - i = (k - (i + 1)) + 1 := by omega
  have hmul :
      r * (k * r ^ (k - (i + 1)) * q) ≤ r * new := by
    calc
      r * (k * r ^ (k - (i + 1)) * q) = k * r ^ (k - i) * q := by
        rw [hsub, pow_succ]
        ac_rfl
      _ ≤ old := hlower
      _ ≤ r * new := hrecip
  exact Nat.le_of_mul_le_mul_left hmul (by omega)

/-- The greedy construction of an induced embedding, stated with its
candidate-set invariant. -/
lemma exists_partial_induced_embedding_of_not_hasRecipPair
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {r k q : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (S : Finset V) (H : SimpleGraph (Fin k))
    (blocks : Fin k → Finset V)
    (hblocksS : ∀ j, blocks j ⊆ S)
    (hblocksDisj : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j))
    (hblocksCard : ∀ j, k * r ^ k * q ≤ (blocks j).card)
    (hno : ¬HasRecipPair G r S q)
    {i : ℕ} (hi : i ≤ k) :
    ∃ f : Fin i ↪ V,
      (∀ r : Fin i, f r ∈ blocks (Fin.castLE hi r)) ∧
      (∀ r s : Fin i,
        G.Adj (f r) (f s) ↔ H.Adj (Fin.castLE hi r) (Fin.castLE hi s)) ∧
      ∀ j : Fin k, i ≤ j.val →
        k * r ^ (k - i) * q ≤ (greedyCandidates G H blocks hi f j).card := by
  classical
  induction i with
  | zero =>
      let f : Fin 0 ↪ V := ⟨Fin.elim0, fun a ↦ Fin.elim0 a⟩
      refine ⟨f, by simp, by simp, ?_⟩
      intro j _
      simpa [greedyCandidates, f] using hblocksCard j
  | succ i ih =>
      have hi0 : i ≤ k := by omega
      have hik : i < k := by omega
      obtain ⟨f, hfblocks, hfadj, hlarge⟩ := ih hi0
      let ii : Fin k := ⟨i, hik⟩
      let W : Fin k → Finset V := greedyCandidates G H blocks hi0 f
      have hWS : ∀ j, W j ⊆ S := by
        intro j
        exact (Finset.filter_subset _ _).trans (hblocksS j)
      have hWdisj : ∀ a b, a ≠ b → Disjoint (W a) (W b) := by
        intro a b hab
        exact (hblocksDisj a b hab).mono (Finset.filter_subset _ _)
          (Finset.filter_subset _ _)
      have hWiLarge : k * q ≤ (W ii).card := by
        have h := hlarge ii (by simp [ii])
        have hp : 1 ≤ r ^ (k - i) := one_le_pow₀ hr
        have hsmall : k * q ≤ k * r ^ (k - i) * q := by
          calc
            k * q = k * (1 * q) := by simp
            _ ≤ k * (r ^ (k - i) * q) :=
              Nat.mul_le_mul_left k (Nat.mul_le_mul_right q hp)
            _ = k * r ^ (k - i) * q := by simp [Nat.mul_assoc]
        exact hsmall.trans (by simpa [W] using h)
      have hWq : ∀ j, ii < j → q ≤ (W j).card := by
        intro j hij
        have h := hlarge j (by exact Nat.le_of_lt hij)
        have hp : 1 ≤ r ^ (k - i) := one_le_pow₀ hr
        have hkq : q ≤ k * q := by simpa using Nat.mul_le_mul_right q hk
        have hsmall : k * q ≤ k * r ^ (k - i) * q := by
          calc
            k * q = k * (1 * q) := by simp
            _ ≤ k * (r ^ (k - i) * q) :=
              Nat.mul_le_mul_left k (Nat.mul_le_mul_right q hp)
            _ = k * r ^ (k - i) * q := by simp [Nat.mul_assoc]
        exact hkq.trans (hsmall.trans (by simpa [W] using h))
      obtain ⟨x, hxW, hgood⟩ :=
        exists_good_candidate_of_not_hasRecipPair G hr hk hq S H W hWS hWdisj
          hWiLarge hWq hno
      have hxblock : x ∈ blocks ii := (mem_greedyCandidates ..).mp hxW |>.1
      have hxrel : ∀ r : Fin i,
          G.Adj (f r) x ↔ H.Adj (Fin.castLE hi0 r) ii :=
        (mem_greedyCandidates ..).mp hxW |>.2
      have hxrange : x ∉ Set.range f := by
        rintro ⟨r, hr⟩
        have hdisj := hblocksDisj (Fin.castLE hi0 r) ii (by
          intro heq
          have := congrArg Fin.val heq
          simp [ii] at this
          omega)
        exact (Finset.disjoint_left.mp hdisj) (hfblocks r) (hr ▸ hxblock)
      let f' : Fin (i + 1) ↪ V := Fin.Embedding.snoc f hxrange
      have hcastLast : Fin.castLE hi (Fin.last i) = ii := by
        apply Fin.ext
        simp [ii]
      have hcastSucc (r : Fin i) :
          Fin.castLE hi r.castSucc = Fin.castLE hi0 r := by
        apply Fin.ext
        simp
      have hf'blocks : ∀ r : Fin (i + 1), f' r ∈ blocks (Fin.castLE hi r) := by
        intro r
        refine Fin.lastCases ?_ (fun s ↦ ?_) r
        · rw [hcastLast]
          simpa [f'] using hxblock
        · rw [hcastSucc]
          simpa [f'] using hfblocks s
      have hf'adj : ∀ r s : Fin (i + 1),
          G.Adj (f' r) (f' s) ↔ H.Adj (Fin.castLE hi r) (Fin.castLE hi s) := by
        intro r s
        refine Fin.lastCases ?_ (fun r₀ ↦ ?_) r
        · refine Fin.lastCases ?_ (fun s₀ ↦ ?_) s
          · simp
          · rw [hcastLast, hcastSucc]
            simpa [f', SimpleGraph.adj_comm] using hxrel s₀
        · refine Fin.lastCases ?_ (fun s₀ ↦ ?_) s
          · rw [hcastSucc, hcastLast]
            simpa [f'] using hxrel r₀
          · rw [hcastSucc, hcastSucc]
            simpa [f'] using hfadj r₀ s₀
      refine ⟨f', hf'blocks, hf'adj, ?_⟩
      intro j hij
      have hiij : ii < j := by
        change i < j.val
        omega
      have hold := hlarge j (by omega)
      have hqtr := hgood j hiij
      have hcand :
          greedyCandidates G H blocks hi f' j =
            if H.Adj ii j then (W j).filter (G.Adj x)
            else (W j).filter (fun y ↦ ¬G.Adj x y) := by
        ext y
        constructor
        · intro hy
          have hy' := (mem_greedyCandidates G H blocks hi f' j y).mp hy
          have holdrel : ∀ r : Fin i,
              G.Adj (f r) y ↔ H.Adj (Fin.castLE hi0 r) j := by
            intro r
            simpa [f', hcastSucc r] using hy'.2 r.castSucc
          have hyW : y ∈ W j :=
            (mem_greedyCandidates G H blocks hi0 f j y).mpr ⟨hy'.1, holdrel⟩
          have hlast := hy'.2 (Fin.last i)
          by_cases hadj : H.Adj ii j
          · rw [if_pos hadj, Finset.mem_filter]
            exact ⟨hyW, by simpa [f', hcastLast, hadj] using hlast⟩
          · rw [if_neg hadj, Finset.mem_filter]
            exact ⟨hyW, by simpa [f', hcastLast, hadj] using hlast⟩
        · intro hy
          by_cases hadj : H.Adj ii j
          · rw [if_pos hadj, Finset.mem_filter] at hy
            have hyW := (mem_greedyCandidates G H blocks hi0 f j y).mp hy.1
            apply (mem_greedyCandidates G H blocks hi f' j y).mpr
            refine ⟨hyW.1, ?_⟩
            intro r
            refine Fin.lastCases ?_ (fun r₀ ↦ ?_) r
            · simpa [f', hcastLast, hadj] using hy.2
            · simpa [f', hcastSucc r₀] using hyW.2 r₀
          · rw [if_neg hadj, Finset.mem_filter] at hy
            have hyW := (mem_greedyCandidates G H blocks hi0 f j y).mp hy.1
            apply (mem_greedyCandidates G H blocks hi f' j y).mpr
            refine ⟨hyW.1, ?_⟩
            intro r
            refine Fin.lastCases ?_ (fun r₀ ↦ ?_) r
            · simpa [f', hcastLast, hadj] using hy.2
            · simpa [f', hcastSucc r₀] using hyW.2 r₀
      apply recip_power_step hr hik hold
      rw [hcand]
      by_cases hadj : H.Adj ii j <;> simpa [hadj] using hqtr

/-- The rounded Erdős--Hajnal sparse/dense pair lemma at density `1/4`.
The deliberately generous factor `k² 4^k` eliminates all floors from the
greedy proof. -/
theorem hasRecipPair_of_induced_free
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {r k q : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (S : Finset V) (H : SimpleGraph (Fin k))
    (hfree : ¬H ⊴ G)
    (hcard : k * (k * r ^ k * q) ≤ S.card) :
    HasRecipPair G r S q := by
  classical
  by_contra hno
  let m : ℕ := k * r ^ k * q
  have hdomain : Fintype.card (Fin k × Fin m) ≤ S.card := by
    simpa [m, Nat.mul_assoc] using hcard
  obtain ⟨e : (Fin k × Fin m) ↪ V, heS⟩ :=
    Function.Embedding.exists_of_card_le_finset hdomain
  let eblock (i : Fin k) : Fin m ↪ V :=
    { toFun := fun r ↦ e (i, r)
      inj' := by
        intro r s hrs
        exact congrArg Prod.snd (e.injective hrs) }
  let blocks (i : Fin k) : Finset V := Finset.univ.map (eblock i)
  have hblocksS : ∀ i, blocks i ⊆ S := by
    intro i x hx
    obtain ⟨r, -, rfl⟩ := Finset.mem_map.mp hx
    exact heS ⟨(i, r), rfl⟩
  have hblocksDisj : ∀ i j, i ≠ j → Disjoint (blocks i) (blocks j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    obtain ⟨r, -, hr⟩ := Finset.mem_map.mp hxi
    obtain ⟨s, -, hs⟩ := Finset.mem_map.mp hxj
    apply hij
    have hp : (i, r) = (j, s) := e.injective (hr.trans hs.symm)
    exact congrArg Prod.fst hp
  have hblocksCard : ∀ i, k * r ^ k * q ≤ (blocks i).card := by
    intro i
    simp [blocks, m]
  obtain ⟨f, -, hfadj, -⟩ :=
    exists_partial_induced_embedding_of_not_hasRecipPair G hr hk hq S H blocks
      hblocksS hblocksDisj hblocksCard hno (i := k) le_rfl
  apply hfree
  let ge : H ↪g G :=
    { toFun := f
      inj' := f.injective
      map_rel_iff' := by
        intro r s
        simpa using hfadj r s }
  exact ge.isIndContained

/-! ## From sparse pairs to a sparse induced subgraph -/

/-- Edges of `G` whose two endpoints lie in `S`. -/
noncomputable def edgesInside {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S

lemma card_edgesInside {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    (edgesInside G S).card = edgeCountOn G S := by
  rw [edgeCountOn_eq_card_edgeFinset]
  simpa [edgesInside] using G.card_filter_edgeFinset_toFinset_subset S

/-- Edges induced by a disjoint union are internal to one side or cross
between the two sides. -/
lemma card_edgesInside_union_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (C D : Finset V) (hCD : Disjoint C D) :
    (edgesInside G (C ∪ D)).card ≤ (G.interedges C D).card +
      (edgesInside G C ∪ edgesInside G D).card := by
  classical
  let X := G.edgeFinset.filter fun e ↦
    ∃ x ∈ C, ∃ y ∈ D, e = s(x, y)
  have hX : X.card ≤ (G.interedges C D).card := by
    choose x hxC y hyD heq using fun e : X ↦ (Finset.mem_filter.mp e.2).2
    let target : X → G.interedges C D := fun e ↦
      ⟨(x e, y e), G.mk_mem_interedges_iff.mpr
        ⟨hxC e, hyD e, by
          have heG := (Finset.mem_filter.mp e.2).1
          rw [SimpleGraph.mem_edgeFinset] at heG
          simpa [heq e] using heG⟩⟩
    have hinj : Function.Injective target := by
      intro e f hef
      apply Subtype.ext
      have hxy : x e = x f := congrArg (fun p : G.interedges C D ↦ p.1.1) hef
      have huv : y e = y f := congrArg (fun p : G.interedges C D ↦ p.1.2) hef
      exact (heq e).trans (by simpa [hxy, huv] using (heq f).symm)
    simpa using Fintype.card_le_of_injective target hinj
  have hcover : edgesInside G (C ∪ D) ⊆
      X ∪ (edgesInside G C ∪ edgesInside G D) := by
    intro e he
    have he' := Finset.mem_filter.mp he
    obtain ⟨a, b⟩ := e
    have hab : a ∈ C ∪ D ∧ b ∈ C ∪ D := by
      simpa [Sym2.toFinset_mk_eq, Finset.insert_subset_iff] using he'.2
    rcases Finset.mem_union.mp hab.1 with haC | haD <;>
      rcases Finset.mem_union.mp hab.2 with hbC | hbD
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨he'.1, by simpa [Sym2.toFinset_mk_eq,
          Finset.insert_subset_iff] using And.intro haC hbC⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he'.1,
        ⟨a, haC, b, hbD, rfl⟩⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he'.1,
        ⟨b, hbC, a, haD, Sym2.eq_swap⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨he'.1, by simpa [Sym2.toFinset_mk_eq,
          Finset.insert_subset_iff] using And.intro haD hbD⟩))
  calc
    (edgesInside G (C ∪ D)).card ≤
        (X ∪ (edgesInside G C ∪ edgesInside G D)).card := Finset.card_le_card hcover
    _ ≤ X.card + (edgesInside G C ∪ edgesInside G D).card := Finset.card_union_le _ _
    _ ≤ (G.interedges C D).card + (edgesInside G C ∪ edgesInside G D).card :=
      Nat.add_le_add_right hX _

lemma edgeCountOn_union_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (C D : Finset V) (hCD : Disjoint C D) :
    edgeCountOn G (C ∪ D) ≤ edgeCountOn G C + edgeCountOn G D +
      (G.interedges C D).card := by
  rw [← card_edgesInside G, ← card_edgesInside G, ← card_edgesInside G]
  have h := card_edgesInside_union_le G C D hCD
  have hu := Finset.card_union_le (edgesInside G C) (edgesInside G D)
  omega

/-- Number of neighbours of `x` in a prescribed finite set. -/
noncomputable def degreeInto {V : Type*} [Fintype V] (G : SimpleGraph V)
    (x : V) (S : Finset V) : ℕ :=
  (S.filter (G.Adj x)).card

lemma card_interedges_eq_sum_degreeInto
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (G.interedges A B).card = ∑ x ∈ A, degreeInto G x B := by
  rw [G.interedges_def, Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x _
  rw [degreeInto, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro y _
  rw [show (x, y).1 = x from rfl, show (x, y).2 = y from rfl]
  by_cases hxy : G.Adj x y <;> simp [hxy]

lemma recipSparsePair_interedges
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} {A B : Finset V} (hA : A.Nonempty)
    (h : IsRecipSparsePair G r A B) :
    r * (G.interedges A B).card < A.card * B.card := by
  rw [card_interedges_eq_sum_degreeInto]
  rw [Finset.mul_sum]
  calc
    ∑ x ∈ A, r * degreeInto G x B < ∑ _x ∈ A, B.card := by
      exact Finset.sum_lt_sum_of_nonempty hA fun x hx ↦ h x hx
    _ = A.card * B.card := by simp

/-- Elementary Markov thinning.  A sparse cut from `U` to a set with at
least `2q` vertices contains a `q`-set whose total cross-edge count is at
most twice the average bound. -/
lemma exists_subset_card_eq_recip_interedges_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {r q : ℕ} {U B : Finset V} (hU : U.Nonempty)
    (havg : r * (G.interedges U B).card < U.card * B.card)
    (hB : 2 * q ≤ B.card) :
    ∃ B' : Finset V, B' ⊆ B ∧ B'.card = q ∧
      r * (G.interedges U B').card ≤ 2 * U.card * q := by
  classical
  letI : Std.Symm G.Adj := G.symm
  let good : Finset V := B.filter fun b ↦ r * degreeInto G b U ≤ 2 * U.card
  have hgood : q ≤ good.card := by
    by_contra hsmall
    have hgoodlt : good.card < q := Nat.lt_of_not_ge hsmall
    let bad : Finset V := B.filter fun b ↦ 2 * U.card < r * degreeInto G b U
    have hpart : good.card + bad.card = B.card := by
      dsimp [good, bad]
      simpa only [not_le] using
        B.card_filter_add_card_filter_not
          (fun b ↦ r * degreeInto G b U ≤ 2 * U.card)
    have hbad : bad.Nonempty := by
      exact Finset.card_pos.mp (by omega)
    have hsumlt : bad.card * (2 * U.card) <
        r * ∑ b ∈ bad, degreeInto G b U := by
      calc
        bad.card * (2 * U.card) = ∑ _b ∈ bad, 2 * U.card := by simp
        _ < ∑ b ∈ bad, r * degreeInto G b U :=
          Finset.sum_lt_sum_of_nonempty hbad fun b hb ↦
            (Finset.mem_filter.mp hb).2
        _ = r * ∑ b ∈ bad, degreeInto G b U := by rw [Finset.mul_sum]
    have hbsub : bad ⊆ B := Finset.filter_subset _ _
    have hsumle : ∑ b ∈ bad, degreeInto G b U ≤
        ∑ b ∈ B, degreeInto G b U :=
      Finset.sum_le_sum_of_subset_of_nonneg hbsub (fun _ _ _ ↦ by omega)
    have hcomm : (G.interedges B U).card = (G.interedges U B).card :=
      Rel.card_interedges_comm (r := G.Adj) B U
    have htotal : ∑ b ∈ B, degreeInto G b U = (G.interedges U B).card := by
      rw [← card_interedges_eq_sum_degreeInto, hcomm]
    have hUpos : 0 < U.card := Finset.card_pos.mpr hU
    have h₁ : (bad.card : ℝ) * (2 * U.card) <
        r * ∑ b ∈ bad, degreeInto G b U := by exact_mod_cast hsumlt
    have h₂ : (∑ b ∈ bad, degreeInto G b U : ℝ) ≤
        ∑ b ∈ B, degreeInto G b U := by exact_mod_cast hsumle
    have h₃ : (r : ℝ) * (G.interedges U B).card < U.card * B.card := by
      exact_mod_cast havg
    have h₄ : (good.card : ℝ) + bad.card = B.card := by exact_mod_cast hpart
    have h₅ : (good.card : ℝ) < q := by exact_mod_cast hgoodlt
    have h₆ : (2 : ℝ) * q ≤ B.card := by exact_mod_cast hB
    have h₇ : (0 : ℝ) < U.card := by exact_mod_cast hUpos
    rw [htotal] at h₂
    nlinarith
  obtain ⟨B', hB'good, hB'card⟩ := Finset.exists_subset_card_eq hgood
  refine ⟨B', hB'good.trans (Finset.filter_subset _ _), hB'card, ?_⟩
  rw [show (G.interedges U B').card = (G.interedges B' U).card from
    Rel.card_interedges_comm (r := G.Adj) U B']
  rw [card_interedges_eq_sum_degreeInto, Finset.mul_sum]
  calc
    ∑ b ∈ B', r * degreeInto G b U ≤ ∑ _b ∈ B', 2 * U.card := by
      apply Finset.sum_le_sum
      intro b hb
      exact (Finset.mem_filter.mp (hB'good hb)).2
    _ = 2 * U.card * q := by simp [hB'card, Nat.mul_comm]

/-- A union of `a` equal blocks, with an explicit upper bound on its
internal edge count.  The slack term `a²q²/r` is chosen to make the
one-block extension recurrence purely polynomial. -/
def HasSparseBlockWitness {V : Type*} [Fintype V] (G : SimpleGraph V)
    (r a q : ℕ) (S : Finset V) : Prop :=
  ∃ U : Finset V, U ⊆ S ∧ U.card = a * q ∧
    r * edgeCountOn G U ≤ r * a * Nat.choose q 2 + a ^ 2 * q ^ 2

lemma HasSparseBlockWitness.mono
    {V : Type*} [Fintype V] {G : SimpleGraph V} {r a q : ℕ}
    {S T : Finset V} (h : HasSparseBlockWitness G r a q S) (hST : S ⊆ T) :
    HasSparseBlockWitness G r a q T := by
  obtain ⟨U, hUS, hcard, hedge⟩ := h
  exact ⟨U, hUS.trans hST, hcard, hedge⟩

lemma edgeCountOn_le_choose_card
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    edgeCountOn G S ≤ Nat.choose S.card 2 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  rw [edgeCountOn_eq_card_edgeFinset]
  simpa using (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two

lemma isRecipSparsePair_compl_of_dense
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {r : ℕ}
    {A B : Finset V} (hAB : Disjoint A B)
    (h : IsRecipDensePair G r A B) :
    IsRecipSparsePair Gᶜ r A B := by
  letI : DecidableEq V := Classical.decEq V
  intro x hx
  have hx' := h x hx
  convert hx' using 1
  apply congrArg (fun n : ℕ ↦ r * n)
  apply congrArg Finset.card
  ext y
  by_cases hy : y ∈ B
  · have hxy : x ≠ y := hAB.forall_ne_finset hx hy
    simp [SimpleGraph.compl_adj, hy, hxy]
  · simp [hy]

/-- Append one block across a sparse pair.  Markov thinning supplies an
exactly `q`-vertex piece of the right side, and the edge recurrence is
absorbed by the square slack in `HasSparseBlockWitness`. -/
lemma HasSparseBlockWitness.succ_of_sparsePair
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {r a q : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a) (hq : 1 ≤ q)
    {A B : Finset V} (hW : HasSparseBlockWitness G r a q A)
    (hpair : IsRecipSparsePair G r A B) (hAB : Disjoint A B)
    (hBcard : 2 * q ≤ B.card) :
    HasSparseBlockWitness G r (a + 1) q (A ∪ B) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨U, hUA, hUcard, hUedge⟩ := hW
  have hUne : U.Nonempty := by
    exact Finset.card_pos.mp (by rw [hUcard]; positivity)
  have hpairU : IsRecipSparsePair G r U B := fun x hx ↦ hpair x (hUA hx)
  have havg := recipSparsePair_interedges G hUne hpairU
  obtain ⟨B', hB'B, hB'card, hcross⟩ :=
    exists_subset_card_eq_recip_interedges_le G hUne havg hBcard
  have hUB' : Disjoint U B' := hAB.mono hUA hB'B
  refine ⟨U ∪ B', ?_, ?_, ?_⟩
  · exact Finset.union_subset (hUA.trans (Finset.subset_union_left))
      (hB'B.trans (Finset.subset_union_right))
  · rw [Finset.card_union_of_disjoint hUB', hUcard, hB'card]
    ring
  · have hdecomp := edgeCountOn_union_le G U B' hUB'
    have hB'edge : edgeCountOn G B' ≤ Nat.choose q 2 := by
      simpa [hB'card] using edgeCountOn_le_choose_card G B'
    have hcast :
        (r * edgeCountOn G (U ∪ B') : ℝ) ≤
          r * (a + 1) * Nat.choose q 2 + (a + 1) ^ 2 * q ^ 2 := by
      have hd : (r : ℝ) * edgeCountOn G (U ∪ B') ≤
          r * edgeCountOn G U + r * edgeCountOn G B' +
            r * (G.interedges U B').card := by
        have hdnat := Nat.mul_le_mul_left r hdecomp
        have hdnat' : r * edgeCountOn G (U ∪ B') ≤
            r * edgeCountOn G U + r * edgeCountOn G B' +
              r * (G.interedges U B').card := by
          calc
            r * edgeCountOn G (U ∪ B') ≤
                r * (edgeCountOn G U + edgeCountOn G B' +
                  (G.interedges U B').card) := hdnat
            _ = _ := by ring
        exact_mod_cast hdnat'
      have hu : (r : ℝ) * edgeCountOn G U ≤
          r * a * Nat.choose q 2 + a ^ 2 * q ^ 2 := by exact_mod_cast hUedge
      have hb : (r : ℝ) * edgeCountOn G B' ≤ r * Nat.choose q 2 := by
        exact_mod_cast Nat.mul_le_mul_left r hB'edge
      have hc : (r : ℝ) * (G.interedges U B').card ≤ 2 * a * q ^ 2 := by
        rw [hUcard] at hcross
        have hcNat : r * (G.interedges U B').card ≤ 2 * a * q ^ 2 := by
          calc
            _ ≤ 2 * (a * q) * q := hcross
            _ = _ := by ring
        exact_mod_cast hcNat
      nlinarith [sq_nonneg ((a : ℝ) + 1)]
    exact_mod_cast hcast

lemma hasSparseBlockWitness_one
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {r q : ℕ} (S : Finset V) (hqS : q ≤ S.card) :
    HasSparseBlockWitness G r 1 q S := by
  classical
  obtain ⟨U, hUS, hUcard⟩ := Finset.exists_subset_card_eq hqS
  refine ⟨U, hUS, by simpa using hUcard, ?_⟩
  have hedge := edgeCountOn_le_choose_card G U
  rw [hUcard] at hedge
  have hmul := Nat.mul_le_mul_left r hedge
  calc
    r * edgeCountOn G U ≤ r * Nat.choose q 2 := hmul
    _ ≤ r * Nat.choose q 2 + q ^ 2 := by omega
    _ = r * 1 * Nat.choose q 2 + 1 ^ 2 * q ^ 2 := by ring

/-- The loss in one application of the rounded induced-free pair lemma. -/
def pairFactor (r k : ℕ) : ℕ := k * (k * r ^ k)

lemma pairFactor_pos {r k : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) :
    0 < pairFactor r k := by
  exact Nat.mul_pos hk (Nat.mul_pos hk (pow_pos (by omega) _))

/-- Iterating the induced-free pair lemma produces either `a` sparse
blocks in `G` or `b` sparse blocks in its complement.  The exponent is
linear in `a+b` and in the order `k` of the omitted induced graph. -/
theorem sparse_or_compl_sparse_blocks_of_induced_free
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {r k q a b : ℕ} (hr : 1 ≤ r) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (H : SimpleGraph (Fin k)) (hfree : ¬H ⊴ G)
    (S : Finset V)
    (hcard : pairFactor r k ^ (a + b - 2) * (2 * q) ≤ S.card) :
    HasSparseBlockWitness G r a q S ∨
      HasSparseBlockWitness Gᶜ r b q S := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  induction hsum : a + b using Nat.strong_induction_on generalizing a b S with
  | h n ih =>
      by_cases ha1 : a = 1
      · subst a
        exact Or.inl (hasSparseBlockWitness_one G S (by
          have hDpos := pairFactor_pos hr hk
          have hD : 1 ≤ pairFactor r k := by omega
          have hp : 1 ≤ pairFactor r k ^ (1 + b - 2) := one_le_pow₀ hD
          have : q ≤ pairFactor r k ^ (1 + b - 2) * (2 * q) := by
            have hq2 : q ≤ 2 * q := by omega
            exact hq2.trans (by simpa using Nat.mul_le_mul_right (2 * q) hp)
          exact this.trans hcard))
      by_cases hb1 : b = 1
      · subst b
        exact Or.inr (hasSparseBlockWitness_one Gᶜ S (by
          have hDpos := pairFactor_pos hr hk
          have hD : 1 ≤ pairFactor r k := by omega
          have hp : 1 ≤ pairFactor r k ^ (a + 1 - 2) := one_le_pow₀ hD
          have : q ≤ pairFactor r k ^ (a + 1 - 2) * (2 * q) := by
            have hq2 : q ≤ 2 * q := by omega
            exact hq2.trans (by simpa using Nat.mul_le_mul_right (2 * q) hp)
          exact this.trans hcard))
      have ha2 : 2 ≤ a := by omega
      have hb2 : 2 ≤ b := by omega
      let childQ : ℕ := pairFactor r k ^ (a + b - 3) * (2 * q)
      have hchildQ : 1 ≤ childQ := by
        dsimp [childQ]
        have hDpos := pairFactor_pos hr hk
        have hD : 1 ≤ pairFactor r k := by omega
        have hp : 1 ≤ pairFactor r k ^ (a + b - 3) := one_le_pow₀ hD
        have h2q : 1 ≤ 2 * q := by omega
        exact Nat.mul_pos hp h2q
      have hpairCard : k * (k * r ^ k * childQ) ≤ S.card := by
        calc
          k * (k * r ^ k * childQ) =
              pairFactor r k ^ (a + b - 2) * (2 * q) := by
            have he : a + b - 2 = (a + b - 3) + 1 := by omega
            rw [he, pow_succ]
            simp only [childQ, pairFactor]
            ring
          _ ≤ S.card := hcard
      obtain ⟨A, B, hAS, hBS, hAB, hAcard, hBcard, hpair⟩ :=
        hasRecipPair_of_induced_free G hr hk hchildQ S H hfree hpairCard
      have hchild_ge : 2 * q ≤ childQ := by
        dsimp [childQ]
        have hDpos := pairFactor_pos hr hk
        have hD : 1 ≤ pairFactor r k := by omega
        have hp : 1 ≤ pairFactor r k ^ (a + b - 3) := one_le_pow₀ hD
        simpa using Nat.mul_le_mul_right (2 * q) hp
      rcases hpair with hsparse | hdense
      · have hsmall : a - 1 + b < n := by omega
        have hArec : pairFactor r k ^ ((a - 1) + b - 2) * (2 * q) ≤ A.card := by
          calc
            pairFactor r k ^ ((a - 1) + b - 2) * (2 * q) = childQ := by
              dsimp [childQ]
              congr 2 <;> omega
            _ ≤ A.card := hAcard
        rcases ih (a - 1 + b) hsmall (a := a - 1) (b := b)
            (by omega) hb A hArec rfl with hAW | hAcW
        · left
          have hext := hAW.succ_of_sparsePair G hr (by omega) hq hsparse hAB
            (hchild_ge.trans hBcard)
          simpa [Nat.sub_add_cancel ha] using
            hext.mono (Finset.union_subset hAS hBS)
        · exact Or.inr (hAcW.mono hAS)
      · have hsmall : a + (b - 1) < n := by omega
        have hArec : pairFactor r k ^ (a + (b - 1) - 2) * (2 * q) ≤ A.card := by
          calc
            pairFactor r k ^ (a + (b - 1) - 2) * (2 * q) = childQ := by
              dsimp [childQ]
              congr 2 <;> omega
            _ ≤ A.card := hAcard
        rcases ih (a + (b - 1)) hsmall (a := a) (b := b - 1)
            ha (by omega) A hArec rfl with hAW | hAcW
        · exact Or.inl (hAW.mono hAS)
        · right
          have hcompPair : IsRecipSparsePair Gᶜ r A B :=
            isRecipSparsePair_compl_of_dense G hAB hdense
          have hext := hAcW.succ_of_sparsePair Gᶜ hr (by omega) hq hcompPair hAB
            (hchild_ge.trans hBcard)
          simpa [Nat.sub_add_cancel hb] using
            hext.mono (Finset.union_subset hAS hBS)

/-! ## A finite sparse-graph Ramsey estimate -/

/-- The possible small neighborhoods in a finite set. -/
def smallSubsets {V : Type*} [DecidableEq V]
    (X : Finset V) (w : ℕ) : Finset (Finset V) :=
  X.powerset.filter fun T ↦ T.card ≤ X.card / w

/-- A weighted form of the binomial theorem, indexed by subsets. -/
lemma sum_powerset_pow_card_sub {V : Type*} [DecidableEq V]
    (X : Finset V) (w : ℕ) :
    ∑ T ∈ X.powerset, w ^ (X.card - T.card) = (w + 1) ^ X.card := by
  calc
    ∑ T ∈ X.powerset, w ^ (X.card - T.card) =
        ∑ m ∈ Finset.range (X.card + 1),
          X.card.choose m * w ^ (X.card - m) := by
      convert
        (Finset.sum_powerset_apply_card (α := ℕ)
          (fun m ↦ w ^ (X.card - m)) (x := X)) using 1 <;>
        simp [nsmul_eq_mul]
    _ = (w + 1) ^ X.card := by
      simpa [mul_comm, add_comm] using (add_pow 1 w X.card).symm

/-- The weighted binomial argument bounds all subsets of relative size at
most `1 / w` without introducing division into the conclusion. -/
lemma card_smallSubsets_mul_pow_le {V : Type*} [DecidableEq V]
    (X : Finset V) {w : ℕ} (hw : 1 ≤ w) :
    (smallSubsets X w).card * w ^ (X.card - X.card / w) ≤
      (w + 1) ^ X.card := by
  classical
  calc
    (smallSubsets X w).card * w ^ (X.card - X.card / w) =
        ∑ _T ∈ smallSubsets X w, w ^ (X.card - X.card / w) := by simp
    _ ≤ ∑ T ∈ smallSubsets X w, w ^ (X.card - T.card) := by
      gcongr with T hT
      have hcard : T.card ≤ X.card / w := (Finset.mem_filter.mp hT).2
      omega
    _ ≤ ∑ T ∈ X.powerset, w ^ (X.card - T.card) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun T hT ↦ (Finset.mem_filter.mp hT).1)
        (fun _ _ _ ↦ Nat.zero_le _)
    _ = (w + 1) ^ X.card := sum_powerset_pow_card_sub X w

/-- Deleting the vertices of large degree from a graph with few edges
leaves at least three quarters of the vertices.  The multiplicative
form avoids every rounding issue. -/
lemma exists_large_lowDegreeSet
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {D : ℕ} (hV : 0 < Fintype.card V)
    (hedges : 8 * D * G.edgeFinset.card ≤ Fintype.card V ^ 2) :
    ∃ L : Finset V,
      3 * Fintype.card V ≤ 4 * L.card ∧
      ∀ v ∈ L, D * G.degree v < Fintype.card V := by
  classical
  let high : Finset V := Finset.univ.filter fun v ↦
    Fintype.card V ≤ D * G.degree v
  let L : Finset V := Finset.univ.filter fun v ↦
    D * G.degree v < Fintype.card V
  have hsumLow : high.card * Fintype.card V ≤
      D * ∑ v ∈ high, G.degree v := by
    calc
      high.card * Fintype.card V =
          ∑ _v ∈ high, Fintype.card V := by simp
      _ ≤ ∑ v ∈ high, D * G.degree v := by
        gcongr with v hv
        exact (Finset.mem_filter.mp hv).2
      _ = D * ∑ v ∈ high, G.degree v := by rw [Finset.mul_sum]
  have hsumAll : ∑ v ∈ high, G.degree v ≤ ∑ v : V, G.degree v := by
    simpa using
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)
  have hhighMul : 4 * high.card * Fintype.card V ≤
      Fintype.card V * Fintype.card V := by
    calc
      4 * high.card * Fintype.card V =
          4 * (high.card * Fintype.card V) := by ring
      _ ≤ 4 * (D * ∑ v ∈ high, G.degree v) :=
        Nat.mul_le_mul_left 4 hsumLow
      _ ≤ 4 * (D * ∑ v : V, G.degree v) := by
        gcongr
      _ = 8 * D * G.edgeFinset.card := by
        rw [G.sum_degrees_eq_twice_card_edges]
        ring
      _ ≤ Fintype.card V ^ 2 := hedges
      _ = Fintype.card V * Fintype.card V := by ring
  have hhigh : 4 * high.card ≤ Fintype.card V := by
    exact Nat.le_of_mul_le_mul_right (by simpa [mul_assoc] using hhighMul) hV
  have hpart : high.card + L.card = Fintype.card V := by
    dsimp [high, L]
    simpa only [not_le, Finset.card_univ] using
      (Finset.univ.card_filter_add_card_filter_not
        (fun v : V ↦ Fintype.card V ≤ D * G.degree v))
  refine ⟨L, by omega, ?_⟩
  intro v hv
  exact (Finset.mem_filter.mp hv).2

/-- The combinatorial core of the Erdős--Szemerédi sparse-graph
estimate.  The last hypothesis is precisely the finite entropy/Ramsey
inequality needed by the neighborhood-pattern pigeonhole argument. -/
lemma homNum_ge_of_maxDegree
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {N w K : ℕ} (hw : 1 ≤ w) (hK : 1 ≤ K)
    (hsize : 8 * K ≤ N)
    (hV : 3 * N ≤ 4 * Fintype.card V)
    (hdegree : ∀ v : V, 100 * w * G.degree v < N)
    (hnum : ∀ x < K,
      4 * ramseyBound (x / w + 1) K * (w + 1) ^ x ≤
        N * w ^ (x - x / w)) :
    K ≤ homNum G := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : Std.Symm G.Adj := G.symm
  by_contra hnot
  have hhom : homNum G < K := Nat.lt_of_not_ge hnot
  obtain ⟨X, hXmax⟩ := G.maximumIndepSet_exists
  let x := X.card
  have hxhom : x ≤ homNum G := by
    calc
      x = G.indepNum := G.maximumIndepSet_card_eq_indepNum X hXmax
      _ ≤ homNum G := le_max_right _ _
  have hxK : x < K := hxhom.trans_lt hhom
  have hxpos : 0 < x := by
    by_contra hx0
    have hVpos : 0 < Fintype.card V := by omega
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp hVpos
    have hsingle : G.IsIndepSet ({v} : Finset V) := by
      simp [SimpleGraph.isIndepSet_iff]
    have := hXmax.maximum {v} hsingle
    have hXempty : X = ∅ := Finset.card_eq_zero.mp (by simpa [x] using hx0)
    exact (by simpa [hXempty] using this)
  let Y : Finset V := Finset.univ \ X
  have hXY : X.card + Y.card = Fintype.card V := by
    dsimp [Y]
    rw [Finset.card_sdiff, Finset.card_univ]
    simp only [Finset.inter_eq_left.mpr (Finset.subset_univ X)]
    omega
  have hY : 2 * N ≤ 4 * Y.card := by omega
  let s : ℕ := x / w + 1
  let bad : Finset V := Y.filter fun v ↦ s ≤ degreeInto G v X
  have hsumCross : 100 * w * ∑ v ∈ Y, degreeInto G v X < x * N := by
    have hcomm : (G.interedges Y X).card = (G.interedges X Y).card :=
      Rel.card_interedges_comm (r := G.Adj) Y X
    have hdegSum : 100 * w * ∑ v ∈ X, G.degree v < x * N := by
      rw [Finset.mul_sum]
      calc
        ∑ v ∈ X, 100 * w * G.degree v < ∑ _v ∈ X, N := by
          exact Finset.sum_lt_sum_of_nonempty
            (Finset.card_pos.mp hxpos) fun v _ ↦ hdegree v
        _ = x * N := by simp [x]
    calc
      100 * w * ∑ v ∈ Y, degreeInto G v X =
          100 * w * (G.interedges Y X).card := by
        rw [card_interedges_eq_sum_degreeInto]
      _ = 100 * w * (G.interedges X Y).card := by rw [hcomm]
      _ = 100 * w * ∑ v ∈ X, degreeInto G v Y := by
        rw [card_interedges_eq_sum_degreeInto]
      _ ≤ 100 * w * ∑ v ∈ X, G.degree v := by
        gcongr with v hv
        dsimp [degreeInto]
        exact Finset.card_le_card (by
          intro z hz
          simpa using (Finset.mem_filter.mp hz).2)
      _ < x * N := hdegSum
  have hbadDegree : bad.card * s ≤ ∑ v ∈ Y, degreeInto G v X := by
    calc
      bad.card * s = ∑ _v ∈ bad, s := by simp
      _ ≤ ∑ v ∈ bad, degreeInto G v X := by
        gcongr with v hv
        exact (Finset.mem_filter.mp hv).2
      _ ≤ ∑ v ∈ Y, degreeInto G v X :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun _ _ _ ↦ Nat.zero_le _)
  have hsx : x < w * s := by
    dsimp [s]
    exact Nat.lt_mul_div_succ x (by omega)
  have hbad : 4 * bad.card ≤ N := by
    by_cases hb0 : bad.card = 0
    · omega
    have hbadlt : 100 * bad.card * x < x * N := by
      calc
        100 * bad.card * x < 100 * bad.card * (w * s) := by
          exact Nat.mul_lt_mul_of_pos_left hsx (by omega)
        _ = bad.card * s * (100 * w) := by ring
        _ ≤ (∑ v ∈ Y, degreeInto G v X) * (100 * w) := by
          gcongr
        _ = 100 * w * ∑ v ∈ Y, degreeInto G v X := by ring
        _ < x * N := hsumCross
    have hbad100 : 100 * bad.card < N := by
      exact Nat.lt_of_mul_lt_mul_left (by simpa [mul_comm] using hbadlt)
    omega
  let Z : Finset V := Y \ bad
  have hbadY : bad ⊆ Y := Finset.filter_subset _ _
  have hYZ : bad.card + Z.card = Y.card := by
    dsimp [Z]
    rw [Finset.card_sdiff]
    simp only [Finset.inter_eq_left.mpr hbadY]
    omega
  have hZ : N ≤ 4 * Z.card := by omega
  let pattern : V → Finset V := fun v ↦ X.filter (G.Adj v)
  have hpatternSmall : ∀ v ∈ Z, pattern v ∈ smallSubsets X w := by
    intro v hv
    have hvY : v ∈ Y := (Finset.mem_sdiff.mp hv).1
    have hvbad : v ∉ bad := (Finset.mem_sdiff.mp hv).2
    have hdeglt : degreeInto G v X < s := by
      by_contra h
      exact hvbad (Finset.mem_filter.mpr ⟨hvY, by omega⟩)
    change X.filter (G.Adj v) ∈
      X.powerset.filter (fun T ↦ T.card ≤ X.card / w)
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    simpa [pattern, degreeInto, s] using Nat.le_of_lt_succ hdeglt
  have hsmallCard :
      (smallSubsets X w).card * w ^ (x - x / w) ≤ (w + 1) ^ x := by
    simpa [x] using card_smallSubsets_mul_pow_le X hw
  have hRamseySmall :
      (smallSubsets X w).card * ramseyBound s K ≤ Z.card := by
    have hp : 0 < w ^ (x - x / w) := pow_pos (by omega) _
    have hmul :
        4 * ((smallSubsets X w).card * ramseyBound s K) *
            w ^ (x - x / w) ≤
          N * w ^ (x - x / w) := by
      calc
        4 * ((smallSubsets X w).card * ramseyBound s K) *
              w ^ (x - x / w) =
            4 * ramseyBound s K *
              ((smallSubsets X w).card * w ^ (x - x / w)) := by ring
        _ ≤ 4 * ramseyBound s K * (w + 1) ^ x := by gcongr
        _ ≤ N * w ^ (x - x / w) := by
          simpa [s] using hnum x hxK
    have hcancel :
        4 * ((smallSubsets X w).card * ramseyBound s K) ≤ N :=
      Nat.le_of_mul_le_mul_right (by simpa [mul_assoc] using hmul) hp
    omega
  have hsmallNonempty : (smallSubsets X w).Nonempty := by
    have hZpos : 0 < Z.card := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hZpos
    exact ⟨pattern v, hpatternSmall v hv⟩
  obtain ⟨S, hSsmall, hfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := Z) (t := smallSubsets X w) (f := pattern)
      hpatternSmall hsmallNonempty hRamseySmall
  let W : Finset V := Z.filter fun v ↦ pattern v = S
  have hWcard : ramseyBound s K ≤ W.card := by
    simpa [W] using hfiber
  have hspos : 1 ≤ s := by simp [s]
  have hWcard' : ramseyBound K s ≤ W.card := by
    rwa [ramseyBound_comm hK hspos]
  rcases exists_clique_or_indep_of_ramseyBound_le G W K s hK hspos hWcard' with
      hclique | hindep
  · obtain ⟨T, _hTW, hTc⟩ := hclique
    have hKT : K ≤ G.cliqueNum := by
      rw [← hTc.card_eq]
      exact hTc.isClique.card_le_cliqueNum
    exact (not_lt_of_ge (hKT.trans (le_max_left _ _))) hhom
  · obtain ⟨T, hTW, hTi⟩ := hindep
    have hTsubZ : T ⊆ Z := hTW.trans (Finset.filter_subset _ _)
    have hTS : ∀ v ∈ T, pattern v = S := by
      intro v hv
      exact (Finset.mem_filter.mp (hTW hv)).2
    have hSX : S ⊆ X := by
      exact Finset.mem_powerset.mp (Finset.mem_filter.mp hSsmall).1
    have hScard : S.card ≤ x / w :=
      (Finset.mem_filter.mp hSsmall).2
    have hdisj : Disjoint (X \ S) T := by
      rw [Finset.disjoint_left]
      intro v hvX hvT
      have hvY : v ∈ Y := (Finset.mem_sdiff.mp (hTsubZ hvT)).1
      exact (Finset.mem_sdiff.mp hvY).2 (Finset.mem_sdiff.mp hvX).1
    have hUnionIndep : G.IsIndepSet ((X \ S) ∪ T) := by
      intro a ha b hb hab
      have ha' : (a ∈ X ∧ a ∉ S) ∨ a ∈ T := by
        simpa only [Set.mem_union, Set.mem_sdiff, Finset.mem_coe] using ha
      have hb' : (b ∈ X ∧ b ∉ S) ∨ b ∈ T := by
        simpa only [Set.mem_union, Set.mem_sdiff, Finset.mem_coe] using hb
      rcases ha' with haX | haT
      · rcases hb' with hbX | hbT
        · exact hXmax.isIndepSet haX.1 hbX.1 hab
        · intro habAdj
          have hpat := hTS b hbT
          have haMem : a ∈ pattern b := by
            exact Finset.mem_filter.mpr
              ⟨haX.1, habAdj.symm⟩
          exact haX.2 (hpat ▸ haMem)
      · rcases hb' with hbX | hbT
        · intro habAdj
          have hpat := hTS a haT
          have hbMem : b ∈ pattern a := by
            exact Finset.mem_filter.mpr ⟨hbX.1, habAdj⟩
          exact hbX.2 (hpat ▸ hbMem)
        · exact hTi.isIndepSet haT hbT hab
    have hUnionCard : X.card < ((X \ S) ∪ T).card := by
      rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_sdiff, Finset.inter_eq_left.mpr hSX, hTi.card_eq]
      dsimp [s]
      omega
    have hUnionIndep' : G.IsIndepSet (↑((X \ S) ∪ T) : Set V) := by
      simpa only [Finset.coe_union, Finset.coe_sdiff] using hUnionIndep
    exact (not_le_of_gt hUnionCard (hXmax.maximum _ hUnionIndep')).elim

/-- Sparse graphs have large homogeneous sets, in a fully explicit finite
form.  The numerical hypothesis is separated so that later applications
can choose any convenient fixed entropy base. -/
theorem homNum_ge_of_sparse
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {w K : ℕ} (hw : 1 ≤ w) (hK : 1 ≤ K)
    (hsize : 8 * K ≤ Fintype.card V)
    (hedges : 800 * w * G.edgeFinset.card ≤ Fintype.card V ^ 2)
    (hnum : ∀ x < K,
      4 * ramseyBound (x / w + 1) K * (w + 1) ^ x ≤
        Fintype.card V * w ^ (x - x / w)) :
    K ≤ homNum G := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hVpos : 0 < Fintype.card V := by omega
  obtain ⟨L, hLcard, hLdegree⟩ :=
    exists_large_lowDegreeSet G hVpos (D := 100 * w) (by
      calc
        8 * (100 * w) * G.edgeFinset.card =
            800 * w * G.edgeFinset.card := by ring
        _ ≤ Fintype.card V ^ 2 := hedges)
  let F : SimpleGraph L := G.induce (L : Set V)
  have hFdegree : ∀ v : L, 100 * w * F.degree v < Fintype.card V := by
    intro v
    have hdegLe : F.degree v ≤ G.degree v := by
      rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
      let f : F.neighborSet v → G.neighborSet (v : V) := fun z ↦
        ⟨z.val.val, z.property⟩
      exact Fintype.card_le_of_injective f (by
        intro a b hab
        have hv : a.val.val = b.val.val :=
          congrArg (fun z : G.neighborSet (v : V) ↦ z.val) hab
        exact Subtype.ext (Subtype.ext hv))
    exact lt_of_le_of_lt (Nat.mul_le_mul_left (100 * w) hdegLe)
      (hLdegree v v.property)
  have hFK : K ≤ homNum F := by
    apply homNum_ge_of_maxDegree F hw hK hsize
    · simpa [F] using hLcard
    · exact hFdegree
    · exact hnum
  exact hFK.trans (homNum_induce_le G (L : Set V))

/-- A single binomial summand is bounded by the whole binomial sum. -/
lemma choose_mul_pow_card_sub_le_add_pow
    {w n j : ℕ} (hj : j ≤ n) :
    n.choose j * w ^ (n - j) ≤ (w + 1) ^ n := by
  rw [show (w + 1) ^ n = (1 + w) ^ n by rw [add_comm], add_pow]
  have hjmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  calc
    n.choose j * w ^ (n - j) =
        1 ^ j * w ^ (n - j) * n.choose j := by simp [mul_comm]
    _ ≤ ∑ m ∈ Finset.range (n + 1),
        1 ^ m * w ^ (n - m) * n.choose m := by
      exact Finset.single_le_sum (f := fun m ↦
          1 ^ m * w ^ (n - m) * n.choose m)
        (fun _ _ ↦ Nat.zero_le _) hjmem

/-- If `(1+1/w)^w ≤ 3`, then the same estimate holds for every
smaller exponent.  It is stated over naturals after clearing powers of
`w`, which is exactly the form used below. -/
lemma add_one_pow_le_three_mul_pow
    {w r : ℕ} (hw : 1 ≤ w) (hr : r ≤ w)
    (hbin : (w + 1) ^ w ≤ 3 * w ^ w) :
    (w + 1) ^ r ≤ 3 * w ^ r := by
  have hp : 0 < w ^ (w - r) := pow_pos (by omega) _
  have hmul : (w + 1) ^ r * w ^ (w - r) ≤
      (3 * w ^ r) * w ^ (w - r) := by
    calc
      (w + 1) ^ r * w ^ (w - r) ≤
          (w + 1) ^ r * (w + 1) ^ (w - r) := by
        gcongr
        omega
      _ = (w + 1) ^ w := by rw [← pow_add]; congr; omega
      _ ≤ 3 * w ^ w := hbin
      _ = (3 * w ^ r) * w ^ (w - r) := by
        symm
        calc
          (3 * w ^ r) * w ^ (w - r) =
              3 * (w ^ r * w ^ (w - r)) := by ring
          _ = 3 * w ^ (r + (w - r)) := by rw [pow_add]
          _ = 3 * w ^ w := by congr; omega
  exact Nat.le_of_mul_le_mul_right hmul hp

/-- The entropy factor for a set of size `x < w*t`. -/
lemma add_one_pow_entropy_bound
    {w t x : ℕ} (hw : 1 ≤ w) (hx : x < w * t)
    (hbin : (w + 1) ^ w ≤ 3 * w ^ w) :
    (w + 1) ^ x ≤ (3 * w) ^ t * w ^ (x - x / w) := by
  let q := x / w
  let r := x % w
  have hq : q < t := by
    dsimp [q]
    exact Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hx)
  have hr : r < w := by
    dsimp [r]
    exact Nat.mod_lt _ (by omega)
  have hxqr : x = q * w + r := by
    dsimp [q, r]
    simpa [mul_comm] using (Nat.div_add_mod x w).symm
  have hblock : (w + 1) ^ (q * w) ≤ (3 * w ^ w) ^ q := by
    rw [show q * w = w * q by ring, pow_mul]
    exact pow_le_pow_left' hbin q
  have hrem := add_one_pow_le_three_mul_pow hw hr.le hbin
  have hmain : (w + 1) ^ x ≤ 3 ^ (q + 1) * w ^ x := by
    rw [hxqr, pow_add]
    calc
      (w + 1) ^ (q * w) * (w + 1) ^ r ≤
          (3 * w ^ w) ^ q * (3 * w ^ r) := by gcongr
      _ = 3 ^ (q + 1) * w ^ (q * w + r) := by
        rw [mul_pow, pow_add]
        ring
  have hqt : q + 1 ≤ t := by omega
  have hqle : q ≤ x := by
    dsimp [q]
    exact Nat.div_le_self _ _
  have hpowx : w ^ x = w ^ q * w ^ (x - q) := by
    rw [← pow_add]
    congr
    omega
  have h3pow : 3 ^ (q + 1) ≤ 3 ^ t :=
    pow_le_pow_right₀ (by omega) hqt
  have hwpow : w ^ q ≤ w ^ t :=
    pow_le_pow_right₀ hw (by omega)
  calc
    (w + 1) ^ x ≤ 3 ^ (q + 1) * w ^ x := hmain
    _ = (3 ^ (q + 1) * w ^ q) * w ^ (x - q) := by
      rw [hpowx]
      ring
    _ ≤ (3 ^ t * w ^ t) * w ^ (x - q) := by
      gcongr
    _ = (3 * w) ^ t * w ^ (x - x / w) := by
      dsimp [q]
      rw [mul_pow]

/-- The asymmetric Ramsey number needed by the neighborhood-pattern
argument has the same entropy scale. -/
lemma ramseyBound_entropy_bound
    {w t s : ℕ} (hw : 1 ≤ w) (ht : 1 ≤ t)
    (hs : 1 ≤ s) (hst : s ≤ t)
    (hbin : (w + 1) ^ w ≤ 3 * w ^ w) :
    ramseyBound s (w * t) ≤ w * (3 * (w + 1)) ^ t := by
  have hK : 1 ≤ w * t := Nat.mul_pos hw ht
  have hj : s - 1 ≤ s + w * t - 2 := by omega
  have hterm := choose_mul_pow_card_sub_le_add_pow (w := w) hj
  have hsub : s + w * t - 2 - (s - 1) = w * t - 1 := by omega
  have hnle : s + w * t - 2 ≤ (w + 1) * t := by
    rw [show (w + 1) * t = w * t + t by ring]
    omega
  have haddpow : (w + 1) ^ (s + w * t - 2) ≤
      (3 * (w + 1)) ^ t * w ^ (w * t) := by
    calc
      (w + 1) ^ (s + w * t - 2) ≤ (w + 1) ^ ((w + 1) * t) :=
        pow_le_pow_right₀ (by omega) hnle
      _ = ((w + 1) ^ w) ^ t * (w + 1) ^ t := by
        rw [show (w + 1) * t = w * t + t by ring, pow_add, pow_mul]
      _ ≤ (3 * w ^ w) ^ t * (w + 1) ^ t := by gcongr
      _ = (3 * (w + 1)) ^ t * w ^ (w * t) := by
        rw [mul_pow, mul_pow, pow_mul]
        ring
  have hp : 0 < w ^ (w * t - 1) := pow_pos (by omega) _
  have hmul : ramseyBound s (w * t) * w ^ (w * t - 1) ≤
      (w * (3 * (w + 1)) ^ t) * w ^ (w * t - 1) := by
    calc
      ramseyBound s (w * t) * w ^ (w * t - 1) ≤
          (w + 1) ^ (s + w * t - 2) := by
        simpa [ramseyBound, hsub, mul_comm] using hterm
      _ ≤ (3 * (w + 1)) ^ t * w ^ (w * t) := haddpow
      _ = (w * (3 * (w + 1)) ^ t) * w ^ (w * t - 1) := by
        have hpowsucc : w ^ (w * t) = w ^ (w * t - 1) * w := by
          calc
            w ^ (w * t) = w ^ ((w * t - 1) + 1) := by congr; omega
            _ = w ^ (w * t - 1) * w := by rw [pow_succ]
        rw [hpowsucc]
        ring
  exact Nat.le_of_mul_le_mul_right hmul hp

/-- A convenient packaged sparse-graph estimate. -/
theorem homNum_ge_of_sparse_power
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {w t : ℕ} (hw : 1 ≤ w) (ht : 1 ≤ t)
    (hbin : (w + 1) ^ w ≤ 3 * w ^ w)
    (hsize : 8 * (w * t) ≤ Fintype.card V)
    (hbase : 4 * w * (9 * w * (w + 1)) ^ t ≤ Fintype.card V)
    (hedges : 800 * w * G.edgeFinset.card ≤ Fintype.card V ^ 2) :
    w * t ≤ homNum G := by
  apply homNum_ge_of_sparse G hw (Nat.mul_pos hw ht) hsize hedges
  intro x hx
  let s := x / w + 1
  have hs : 1 ≤ s := by simp [s]
  have hst : s ≤ t := by
    dsimp [s]
    have hdiv : x / w < t :=
      Nat.div_lt_of_lt_mul (by simpa [mul_comm] using hx)
    omega
  have hR := ramseyBound_entropy_bound hw ht hs hst hbin
  have hP := add_one_pow_entropy_bound hw hx hbin
  calc
    4 * ramseyBound (x / w + 1) (w * t) * (w + 1) ^ x ≤
        4 * (w * (3 * (w + 1)) ^ t) *
          ((3 * w) ^ t * w ^ (x - x / w)) := by
      dsimp [s] at hR
      gcongr
    _ = (4 * w * (9 * w * (w + 1)) ^ t) *
          w ^ (x - x / w) := by
      calc
        4 * (w * (3 * (w + 1)) ^ t) *
              ((3 * w) ^ t * w ^ (x - x / w)) =
            4 * w * (((3 * (w + 1)) ^ t * (3 * w) ^ t) *
              w ^ (x - x / w)) := by ring
        _ = (4 * w * (9 * w * (w + 1)) ^ t) *
              w ^ (x - x / w) := by
          rw [← mul_pow]
          ring
    _ ≤ Fintype.card V * w ^ (x - x / w) := by gcongr

lemma fixed_entropy_binomial :
    (1024 + 1 : ℕ) ^ 1024 ≤ 3 * 1024 ^ 1024 := by
  have hunit : (1 + (1024 : ℝ)⁻¹) ^ 1024 ≤ Real.exp 1 :=
    Real.one_add_inv_pow_le_exp
  have hthree : (1 + (1024 : ℝ)⁻¹) ^ 1024 ≤ 3 :=
    hunit.trans Real.exp_one_lt_three.le
  have hmul := mul_le_mul_of_nonneg_left hthree
    (show 0 ≤ (1024 : ℝ) ^ 1024 by positivity)
  have heq : (1025 : ℝ) ^ 1024 =
      1024 ^ 1024 * (1 + (1024 : ℝ)⁻¹) ^ 1024 := by
    rw [show (1025 : ℝ) = 1024 * (1 + (1024 : ℝ)⁻¹) by norm_num,
      mul_pow]
  have hreal : (1025 : ℝ) ^ 1024 ≤ 3 * 1024 ^ 1024 := by
    rw [heq]
    simpa [mul_comm] using hmul
  exact_mod_cast hreal

/-- Fixed constants used in the final quantitative argument. -/
def entropyBase : ℕ := 9 * 1024 * (1024 + 1)

def sparseScale : ℕ := 1600 * 1024

def blockExponent : ℕ := 2 * sparseScale - 2

def universalDivisor : ℕ := 184 * blockExponent

lemma entropyBase_ge_two : 2 ≤ entropyBase := by norm_num [entropyBase]

lemma entropyBase_le_two_pow : entropyBase ≤ 2 ^ 24 := by
  norm_num [entropyBase]

lemma sparseScale_le_two_pow : sparseScale ≤ 2 ^ 21 := by
  norm_num [sparseScale]

lemma universalDivisor_pos : 0 < universalDivisor := by
  norm_num [universalDivisor, blockExponent, sparseScale]

lemma pairFactor_fixed_le_two_pow {k : ℕ} :
    pairFactor sparseScale k ≤ 2 ^ (23 * k) := by
  have hk : k ≤ 2 ^ k := k.lt_two_pow_self.le
  have hr : sparseScale ^ k ≤ (2 ^ 21) ^ k :=
    pow_le_pow_left' sparseScale_le_two_pow k
  calc
    pairFactor sparseScale k = k * (k * sparseScale ^ k) := rfl
    _ ≤ 2 ^ k * (2 ^ k * (2 ^ 21) ^ k) := by gcongr
    _ = 2 ^ (23 * k) := by
      rw [pow_mul]
      rw [← mul_pow, ← mul_pow]
      norm_num

/-- A block witness with the fixed parameters already forces the large
homogeneous set that will contradict the Ramsey hypothesis. -/
theorem homNum_of_fixed_sparseBlockWitness
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    {t : ℕ} (ht : 1 ≤ t) {S : Finset V}
    (hW : HasSparseBlockWitness G sparseScale sparseScale (entropyBase ^ t) S) :
    1024 * t ≤ homNum G := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨U, _hUS, hUcard, hUedges⟩ := hW
  let F : SimpleGraph U := G.induce (U : Set V)
  have htq : t ≤ entropyBase ^ t := by
    exact t.lt_two_pow_self.le.trans
      (pow_le_pow_left' entropyBase_ge_two t)
  have hFcard : Fintype.card U = sparseScale * entropyBase ^ t := by
    simpa using hUcard
  have hsize : 8 * (1024 * t) ≤ Fintype.card U := by
    rw [hFcard]
    calc
      8 * (1024 * t) ≤ 8 * (1024 * entropyBase ^ t) := by gcongr
      _ = (8 * 1024) * entropyBase ^ t := by ring
      _ ≤ sparseScale * entropyBase ^ t :=
        Nat.mul_le_mul_right (entropyBase ^ t) (by norm_num [sparseScale])
  have hbase : 4 * 1024 * entropyBase ^ t ≤ Fintype.card U := by
    rw [hFcard]
    dsimp [sparseScale]
    gcongr
    norm_num
  have hFedge : F.edgeFinset.card = edgeCountOn G U := by
    simpa [F] using (edgeCountOn_eq_card_edgeFinset G U).symm
  have hchoose : Nat.choose (entropyBase ^ t) 2 ≤ (entropyBase ^ t) ^ 2 :=
    Nat.choose_le_pow _ _
  have hedges : 800 * 1024 * F.edgeFinset.card ≤ Fintype.card U ^ 2 := by
    rw [hFedge, hFcard]
    have hscale : 0 < sparseScale := by norm_num [sparseScale]
    refine Nat.le_of_mul_le_mul_left ?_ hscale
    calc
      sparseScale * (800 * 1024 * edgeCountOn G U) =
          800 * 1024 * (sparseScale * edgeCountOn G U) := by ring
      _ ≤ 800 * 1024 *
          (sparseScale * sparseScale * Nat.choose (entropyBase ^ t) 2 +
            sparseScale ^ 2 * (entropyBase ^ t) ^ 2) := by
        gcongr
      _ ≤ 800 * 1024 *
          (sparseScale * sparseScale * (entropyBase ^ t) ^ 2 +
            sparseScale ^ 2 * (entropyBase ^ t) ^ 2) := by
        gcongr
      _ = sparseScale * (sparseScale * entropyBase ^ t) ^ 2 := by
        dsimp [sparseScale]
        ring
  have hFhom : 1024 * t ≤ homNum F := by
    apply homNum_ge_of_sparse_power F (w := 1024) (t := t)
    · norm_num
    · exact ht
    · exact fixed_entropy_binomial
    · exact hsize
    · simpa [entropyBase] using hbase
    · exact hedges
  exact hFhom.trans (homNum_induce_le G (U : Set V))

/-- With the fixed constants, absence of one `k`-vertex induced graph
would force a homogeneous set of order `1024 * floor(log₂ n / 64)`. -/
theorem inducedUniversalAt_of_homNum_lt
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hlog : universalDivisor ≤ Nat.log 2 (Fintype.card V))
    (hhom : homNum G < 1024 * (Nat.log 2 (Fintype.card V) / 64)) :
    IsInducedUniversalAt G
      (Nat.log 2 (Fintype.card V) / universalDivisor) := by
  classical
  let L := Nat.log 2 (Fintype.card V)
  let k := L / universalDivisor
  let t := L / 64
  let q := entropyBase ^ t
  have hLpos : 0 < L := by
    exact lt_of_lt_of_le universalDivisor_pos hlog
  have hVne : Fintype.card V ≠ 0 := by
    intro hzero
    simp [L, hzero] at hLpos
  have hk : 1 ≤ k := by
    dsimp [k]
    rw [Nat.le_div_iff_mul_le universalDivisor_pos]
    simpa using hlog
  have ht : 1 ≤ t := by
    dsimp [t]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 64)]
    exact (by norm_num [universalDivisor, blockExponent, sparseScale] :
      64 ≤ universalDivisor).trans hlog
  have hkLoss : universalDivisor * k ≤ L := by
    dsimp [k]
    exact Nat.mul_div_le L universalDivisor
  have htLoss : 64 * t ≤ L := by
    dsimp [t]
    exact Nat.mul_div_le L 64
  have hexponent : 23 * k * blockExponent ≤ L / 8 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 8)]
    calc
      (23 * k * blockExponent) * 8 = universalDivisor * k := by
        dsimp [universalDivisor]
        ring
      _ ≤ L := hkLoss
  have hDpow : pairFactor sparseScale k ^ blockExponent ≤ 2 ^ (L / 8) := by
    calc
      pairFactor sparseScale k ^ blockExponent ≤
          (2 ^ (23 * k)) ^ blockExponent :=
        pow_le_pow_left' pairFactor_fixed_le_two_pow blockExponent
      _ = 2 ^ (23 * k * blockExponent) :=
        (pow_mul 2 (23 * k) blockExponent).symm
      _ ≤ 2 ^ (L / 8) := pow_le_pow_right₀ (by omega) hexponent
  have hqpow : q ≤ 2 ^ (L / 2) := by
    have h24 : 24 * t ≤ L / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
      calc
        (24 * t) * 2 ≤ 64 * t := by omega
        _ ≤ L := htLoss
    calc
      q = entropyBase ^ t := rfl
      _ ≤ (2 ^ 24) ^ t := pow_le_pow_left' entropyBase_le_two_pow t
      _ = 2 ^ (24 * t) := by rw [pow_mul]
      _ ≤ 2 ^ (L / 2) := pow_le_pow_right₀ (by omega) h24
  have hL8 : 8 ≤ L :=
    (by norm_num [universalDivisor, blockExponent, sparseScale] :
      8 ≤ universalDivisor).trans hlog
  have htotalExponent : L / 8 + (1 + L / 2) ≤ L := by omega
  have hcard : pairFactor sparseScale k ^ blockExponent * (2 * q) ≤
      Fintype.card V := by
    calc
      pairFactor sparseScale k ^ blockExponent * (2 * q) ≤
          2 ^ (L / 8) * (2 * 2 ^ (L / 2)) := by gcongr
      _ = 2 ^ (L / 8 + (1 + L / 2)) := by
        change 2 ^ (L / 8) * (2 ^ 1 * 2 ^ (L / 2)) = _
        rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ L := pow_le_pow_right₀ (by omega) htotalExponent
      _ ≤ Fintype.card V := Nat.pow_log_le_self 2 hVne
  have hentropy : 0 < entropyBase := by norm_num [entropyBase]
  have hqpos : 0 < q := by
    dsimp [q]
    exact pow_pos hentropy t
  intro H
  by_contra hfree
  have hblocks := sparse_or_compl_sparse_blocks_of_induced_free
    G (r := sparseScale) (k := k) (q := q)
      (a := sparseScale) (b := sparseScale)
      (by norm_num [sparseScale]) hk
      hqpos
      (by norm_num [sparseScale]) (by norm_num [sparseScale])
      H hfree Finset.univ (by
        simpa [blockExponent, two_mul] using hcard)
  rcases hblocks with hGsparse | hGcsparse
  · have hlarge := homNum_of_fixed_sparseBlockWitness G ht hGsparse
    exact (not_lt_of_ge hlarge) (by simpa [t, L] using hhom)
  · have hlarge := homNum_of_fixed_sparseBlockWitness Gᶜ ht hGcsparse
    rw [homNum_compl] at hlarge
    exact (not_lt_of_ge hlarge) (by simpa [t, L] using hhom)

/-- Comparison between the natural logarithm and the binary integer
logarithm.  The deliberately weak constant `1` keeps all rounding on the
integer side of the final proof. -/
lemma real_log_nat_lt_succ_log_two {n : ℕ} (hn : n ≠ 0) :
    Real.log (n : ℝ) < (Nat.log 2 n + 1 : ℕ) := by
  have hnat : n < 2 ^ (Nat.log 2 n + 1) := by
    simpa [Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self Nat.one_lt_two n)
  have hcast : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast hnat
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog := Real.log_lt_log hnpos hcast
  rw [Real.log_pow] at hlog
  have hlogtwo : Real.log 2 < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hsuccpos : (0 : ℝ) < (Nat.log 2 n + 1 : ℕ) := by positivity
  exact hlog.trans (by
    have := mul_lt_mul_of_pos_left hlogtwo hsuccpos
    simpa [mul_one] using this)

/-- An induced regular subgraph with enough vertices whose degree excludes
both the empty and complete cases. -/
def HasLargeInducedNontrivialRegular {V : Type*} [Fintype V]
    (G : SimpleGraph V) (L : ℝ) : Prop :=
  ∃ (S : Set V) (d : ℕ),
    L ≤ (Fintype.card S : ℝ) ∧
    0 < d ∧ d + 1 < Fintype.card S ∧
    (G.induce S).IsRegularOfDegree d

/-- Graph isomorphisms preserve regularity and its degree. -/
lemma Iso.isRegularOfDegree_iff {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (d : ℕ) :
    G.IsRegularOfDegree d ↔ H.IsRegularOfDegree d := by
  constructor
  · intro h w
    rw [← e.apply_symm_apply w]
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      ← Nat.card_congr (e.mapNeighborSet (e.symm w)), Nat.card_eq_fintype_card,
      card_neighborSet_eq_degree]
    simpa using h (e.symm w)
  · intro h v
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      Nat.card_congr (e.mapNeighborSet v), Nat.card_eq_fintype_card,
      card_neighborSet_eq_degree]
    exact h (e v)

/-- A cycle with at least three vertices is `2`-regular. -/
lemma cycleGraph_isRegularOfDegree_two {m : ℕ} (hm : 3 ≤ m) :
    (cycleGraph m).IsRegularOfDegree 2 := by
  obtain ⟨q, hq⟩ : ∃ q, m = q + 3 := ⟨m - 3, by omega⟩
  subst m
  exact fun _ ↦ cycleGraph_degree_three_le

/-- Exact-order induced universality supplies a nontrivial regular induced
subgraph whenever the universal order is at least four and large enough. -/
theorem hasLargeInducedNontrivialRegular_of_universalAt
    {V : Type*} [Fintype V] (G : SimpleGraph V) {L : ℝ} {m : ℕ}
    (hmL : L ≤ (m : ℝ)) (hm4 : 4 ≤ m) (hU : IsInducedUniversalAt G m) :
    HasLargeInducedNontrivialRegular G L := by
  classical
  have hcycle : cycleGraph m ⊴ G := hU (cycleGraph m)
  obtain ⟨S, ⟨e⟩⟩ := isIndContained_iff_exists_iso_induce.mp hcycle
  have hcard : Fintype.card S = m := by
    simpa using e.card_eq.symm
  refine ⟨S, 2, ?_, by omega, ?_, ?_⟩
  · simpa [hcard] using hmL
  · omega
  · intro w
    rw [← e.apply_symm_apply w]
    rw [← card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card,
      ← Nat.card_congr (e.mapNeighborSet (e.symm w)), Nat.card_eq_fintype_card,
      card_neighborSet_eq_degree]
    simpa using
      (cycleGraph_isRegularOfDegree_two (m := m) (by omega) (e.symm w))

/-- **Erdős Problem 1031 (Prömel--Rödl).**  For all sufficiently
large orders, every graph with no complete or empty induced subgraph of
order `10 log n` has an induced nonempty, noncomplete regular subgraph
of order at least a fixed positive multiple of `log n`.

Here `homNum` is the maximum of the clique and independence numbers, so
the strict hypothesis is exactly the assertion that there is no trivial
induced subgraph on at least `10 log n` vertices. -/
theorem erdos_1031 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
        Fintype.card V = n →
        (homNum G : ℝ) < 10 * Real.log n →
        HasLargeInducedNontrivialRegular G (c * Real.log n) := by
  let c : ℝ := (2 * (universalDivisor : ℝ))⁻¹
  let n₀ : ℕ := 2 ^ (4 * universalDivisor)
  refine ⟨c, ?_, n₀, ?_⟩
  · dsimp [c]
    apply inv_pos.mpr
    exact mul_pos (by norm_num) (by exact_mod_cast universalDivisor_pos)
  intro n hn V instV G hVcard hRamsey
  let L := Nat.log 2 n
  let m := L / universalDivisor
  have hn0 : n ≠ 0 := by
    have hn0pos : 0 < n₀ := by
      dsimp [n₀]
      positivity
    omega
  have hfourLog : 4 * universalDivisor ≤ L := by
    dsimp [L]
    apply Nat.le_log_of_pow_le Nat.one_lt_two
    simpa [n₀] using hn
  have hlog : universalDivisor ≤ L := by
    exact (by
      have hpos := universalDivisor_pos
      omega)
  have hm4 : 4 ≤ m := by
    dsimp [m]
    rw [Nat.le_div_iff_mul_le universalDivisor_pos]
    simpa [mul_comm] using hfourLog
  have hlogReal := real_log_nat_lt_succ_log_two hn0
  have hfloor : 10 * (L + 1) ≤ 1024 * (L / 64) := by
    have hlower : 64 * (L / 64) ≤ L := Nat.mul_div_le L 64
    have hupper : L < 64 * (L / 64 + 1) :=
      Nat.lt_mul_div_succ L (by norm_num)
    have hLlarge : 200 ≤ L :=
      (by norm_num [universalDivisor, blockExponent, sparseScale] :
        200 ≤ universalDivisor).trans hlog
    omega
  have hhomNat : homNum G < 1024 * (L / 64) := by
    have hreal : (homNum G : ℝ) < ((1024 * (L / 64) : ℕ) : ℝ) := by
      calc
        (homNum G : ℝ) < 10 * Real.log n := hRamsey
        _ < 10 * ((L + 1 : ℕ) : ℝ) := by nlinarith [hlogReal]
        _ ≤ ((1024 * (L / 64) : ℕ) : ℝ) := by exact_mod_cast hfloor
    exact_mod_cast hreal
  have hU : IsInducedUniversalAt G m := by
    have hU' := inducedUniversalAt_of_homNum_lt G (by
      simpa [hVcard, L] using hlog) (by
      simpa [hVcard, L] using hhomNat)
    simpa [m, L, hVcard] using hU'
  have hmLoss : universalDivisor * m ≤ L := by
    dsimp [m]
    exact Nat.mul_div_le L universalDivisor
  have hmUpper : L + 1 ≤ 2 * universalDivisor * m := by
    have hnext : L < universalDivisor * (m + 1) := by
      dsimp [m]
      exact Nat.lt_mul_div_succ L universalDivisor_pos
    have hCm : universalDivisor ≤ universalDivisor * m := by
      simpa using Nat.mul_le_mul_left universalDivisor (show 1 ≤ m by omega)
    calc
      L + 1 ≤ universalDivisor * (m + 1) := by omega
      _ = universalDivisor * m + universalDivisor := by ring
      _ ≤ universalDivisor * m + universalDivisor * m := by gcongr
      _ = 2 * universalDivisor * m := by ring
  have hmReal : c * Real.log n ≤ (m : ℝ) := by
    have hlogLe : Real.log n ≤ ((2 * universalDivisor * m : ℕ) : ℝ) := by
      exact hlogReal.le.trans (by exact_mod_cast hmUpper)
    have hden : (0 : ℝ) < 2 * universalDivisor := by
      exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) universalDivisor_pos
    have hmulReal : Real.log n ≤ (m : ℝ) * (2 * universalDivisor) := by
      calc
        Real.log n ≤ ((2 * universalDivisor * m : ℕ) : ℝ) := hlogLe
        _ = (m : ℝ) * (2 * universalDivisor) := by
          push_cast
          ring
    have hdiv := (div_le_iff₀ hden).2 hmulReal
    simpa [c, div_eq_inv_mul, mul_comm] using hdiv
  exact hasLargeInducedNontrivialRegular_of_universalAt G hmReal hm4 hU

#print axioms erdos_1031

end Erdos1031
