/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 777.
https://www.erdosproblems.com/forum/thread/777

Informal authors:
- Noga Alon
- Péter Frankl
- Shagnik Das
- Roman Glebov
- Benny Sudakov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos777.md
-/
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
import Mathlib

/-!
# Erdős Problem 777

This file formalizes the three-part resolution of the Daykin--Erdős problem
on comparable pairs in a family of subsets of `[n]`.

* the first question is affirmative;
* the proposed constant-density bound in the second question is false;
* the third question is affirmative.

The mathematical proof and the detailed map to the declarations below are in
`tex/777.tex`.
-/

open scoped BigOperators NNReal

namespace Erdos777

noncomputable section

/-- The comparability graph of a finite family of finite sets.  Vertices are
members of the family, and adjacency is strict containment in either
direction. -/
def comparableGraph {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : SimpleGraph {A // A ∈ 𝓕} where
  Adj A B := A.1 < B.1 ∨ B.1 < A.1
  symm := ⟨by intro A B; tauto⟩
  loopless := ⟨by intro A h; exact (lt_irrefl A.1) (h.elim id id)⟩

instance comparableGraph_instDecidableRel {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : DecidableRel (comparableGraph 𝓕).Adj :=
  fun _ _ ↦ Classical.propDecidable _

@[simp] theorem comparableGraph_adj {α : Type*} [DecidableEq α]
    {𝓕 : Finset (Finset α)} {A B : {S // S ∈ 𝓕}} :
    (comparableGraph 𝓕).Adj A B ↔ A.1 < B.1 ∨ B.1 < A.1 :=
  Iff.rfl

/-- The number of unordered strict comparable pairs in `𝓕`. -/
def comparableEdges {α : Type*} [Fintype α] [DecidableEq α]
    (𝓕 : Finset (Finset α)) : ℕ :=
  (comparableGraph 𝓕).edgeFinset.card

/-- Strictly oriented containment pairs.  Every unoriented edge of the
comparability graph has a unique orientation of this form. -/
def strictContainments {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) : ℕ :=
  (Finset.univ.filter fun p : {A // A ∈ 𝓕} × {B // B ∈ 𝓕} ↦ p.1.1 < p.2.1).card

/-- Counting a comparable edge after orienting it from the smaller set to the
larger set does not change its cardinality. -/
lemma comparableEdges_eq_strictContainments {α : Type*} [Fintype α] [DecidableEq α]
    (𝓕 : Finset (Finset α)) : comparableEdges 𝓕 = strictContainments 𝓕 := by
  let V := {A // A ∈ 𝓕}
  let G : SimpleGraph V := comparableGraph 𝓕
  let L : Finset (V × V) := Finset.univ.filter fun p ↦ p.1.1 < p.2.1
  let R : Finset (V × V) := Finset.univ.filter fun p ↦ p.2.1 < p.1.1
  have hLR : L.card = R.card := by
    let e : V × V ≃ V × V := Equiv.prodComm V V
    have himage : L.map e.toEmbedding = R := by
      ext p
      rcases p with ⟨A, B⟩
      simp [L, R, e]
    rw [← himage, Finset.card_map]
  have hdisj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro p hpL hpR
    have h₁ : p.1.1 < p.2.1 := (Finset.mem_filter.mp hpL).2
    have h₂ : p.2.1 < p.1.1 := (Finset.mem_filter.mp hpR).2
    exact lt_asymm h₁ h₂
  have hunion : Finset.univ.filter (fun p : V × V ↦ G.Adj p.1 p.2) = L ∪ R := by
    ext p
    simp [G, L, R, comparableGraph]
  have htwice := G.two_mul_card_edgeFinset
  have hcard : 2 * G.edgeFinset.card = 2 * L.card := by
    rw [htwice, hunion, Finset.card_union_of_disjoint hdisj, ← hLR]
    omega
  have heq : G.edgeFinset.card = L.card := by omega
  simpa [comparableEdges, strictContainments, G, L] using heq

/-! ## The counterexample for the second question -/

/-- Three tagged blocks of respective sizes `r`, `r`, and `1`.  The final
point separates the lower and upper halves of the construction. -/
abbrev CounterGround (r : ℕ) := Fin r ⊕ (Fin r ⊕ Fin 1)

def lowerSet (r : ℕ) (p : Fin r × Finset (Fin r)) : Finset (CounterGround r) :=
  p.2.disjSum (({p.1} : Finset (Fin r)).disjSum (∅ : Finset (Fin 1)))

def upperSet (r : ℕ) (p : Fin r × Finset (Fin r)) : Finset (CounterGround r) :=
  ((Finset.univ : Finset (Fin r)).erase p.1).disjSum (p.2.disjSum {0})

lemma lowerSet_injective (r : ℕ) : Function.Injective (lowerSet r) := by
  rintro ⟨x, A⟩ ⟨x', A'⟩ h
  simp only [lowerSet, Finset.disjSum_inj] at h
  have hA : A = A' := h.1
  have hx : ({x} : Finset (Fin r)) = {x'} := h.2.1
  have : x = x' := by simpa using hx
  subst x'
  simp_all

lemma upperSet_injective (r : ℕ) : Function.Injective (upperSet r) := by
  rintro ⟨y, B⟩ ⟨y', B'⟩ h
  simp only [upperSet, Finset.disjSum_inj] at h
  obtain ⟨hy, hB, -⟩ := h
  have : y = y' := (Finset.erase_inj Finset.univ (Finset.mem_univ y)).mp hy
  subst y'
  simp_all

def lowerEmbedding (r : ℕ) : (Fin r × Finset (Fin r)) ↪ Finset (CounterGround r) :=
  ⟨lowerSet r, lowerSet_injective r⟩

def upperEmbedding (r : ℕ) : (Fin r × Finset (Fin r)) ↪ Finset (CounterGround r) :=
  ⟨upperSet r, upperSet_injective r⟩

def lowerFamily (r : ℕ) : Finset (Finset (CounterGround r)) :=
  Finset.univ.map (lowerEmbedding r)

def upperFamily (r : ℕ) : Finset (Finset (CounterGround r)) :=
  Finset.univ.map (upperEmbedding r)

lemma lower_upper_disjoint (r : ℕ) : Disjoint (lowerFamily r) (upperFamily r) := by
  rw [Finset.disjoint_left]
  intro S hS hS'
  simp only [lowerFamily, upperFamily, Finset.mem_map] at hS hS'
  obtain ⟨⟨x, A⟩, -, rfl⟩ := hS
  obtain ⟨⟨y, B⟩, -, hEq⟩ := hS'
  have hm₀ : (Sum.inr (Sum.inr (0 : Fin 1)) : CounterGround r) ∉ lowerSet r (x, A) := by
    simp [lowerSet]
  have hm₁ : (Sum.inr (Sum.inr (0 : Fin 1)) : CounterGround r) ∈ upperSet r (y, B) := by
    simp [upperSet]
  change upperSet r (y, B) = lowerSet r (x, A) at hEq
  have hmem := congrArg
    (fun T : Finset (CounterGround r) ↦
      (Sum.inr (Sum.inr (0 : Fin 1)) : CounterGround r) ∈ T) hEq
  exact hm₀ (hmem.mp hm₁)

def counterGroundEquiv (r : ℕ) : CounterGround r ≃ Fin (r + (r + 1)) :=
  (Equiv.sumCongr (Equiv.refl (Fin r)) finSumFinEquiv).trans finSumFinEquiv

def counterFamilySum (r : ℕ) : Finset (Finset (CounterGround r)) :=
  lowerFamily r ∪ upperFamily r

def counterFamily (r : ℕ) : Finset (Finset (Fin (r + (r + 1)))) :=
  (counterFamilySum r).map (Finset.mapEmbedding (counterGroundEquiv r).toEmbedding).toEmbedding

lemma card_lowerFamily (r : ℕ) : (lowerFamily r).card = r * 2 ^ r := by
  simp [lowerFamily, Fintype.card_prod, Fintype.card_finset]

lemma card_upperFamily (r : ℕ) : (upperFamily r).card = r * 2 ^ r := by
  simp [upperFamily, Fintype.card_prod, Fintype.card_finset]

lemma card_counterFamily (r : ℕ) : (counterFamily r).card = 2 * r * 2 ^ r := by
  rw [counterFamily, Finset.card_map, counterFamilySum,
    Finset.card_union_of_disjoint (lower_upper_disjoint r),
    card_lowerFamily, card_upperFamily]
  ring

/-- The choices which produce certified lower-to-upper containments. -/
abbrev CounterQuad (r : ℕ) :=
  Σ x : Fin r, Σ y : Fin r,
    Finset {z : Fin r // z ≠ y} × Finset {z : Fin r // z ≠ x}

def forgetNe {r : ℕ} {x : Fin r} (A : Finset {z : Fin r // z ≠ x}) : Finset (Fin r) :=
  A.map (Function.Embedding.subtype _)

@[simp] lemma mem_forgetNe {r : ℕ} {x z : Fin r}
    {A : Finset {z : Fin r // z ≠ x}} :
    z ∈ forgetNe A ↔ ∃ h : z ≠ x, (⟨z, h⟩ : {z // z ≠ x}) ∈ A := by
  simp [forgetNe]

lemma forgetNe_injective {r : ℕ} {x : Fin r} :
    Function.Injective (forgetNe (r := r) (x := x)) :=
  Finset.map_injective (Function.Embedding.subtype _)

def quadLower {r : ℕ} (q : CounterQuad r) : Finset (CounterGround r) :=
  lowerSet r (q.1, forgetNe q.2.2.1)

def quadUpper {r : ℕ} (q : CounterQuad r) : Finset (CounterGround r) :=
  upperSet r (q.2.1, insert q.1 (forgetNe q.2.2.2))

lemma quadLower_ssubset_quadUpper {r : ℕ} (q : CounterQuad r) :
    quadLower q ⊂ quadUpper q := by
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · unfold quadLower quadUpper lowerSet upperSet
    apply Finset.disjSum_mono
    · intro z hz
      rcases mem_forgetNe.mp hz with ⟨hz_ne, -⟩
      simp [hz_ne]
    · apply Finset.disjSum_mono
      · simp
      · simp
  · intro hEq
    have hm₀ : (Sum.inr (Sum.inr (0 : Fin 1)) : CounterGround r) ∉ quadLower q := by
      simp [quadLower, lowerSet]
    have hm₁ : (Sum.inr (Sum.inr (0 : Fin 1)) : CounterGround r) ∈ quadUpper q := by
      simp [quadUpper, upperSet]
    exact hm₀ (hEq ▸ hm₁)

lemma card_fin_ne (r : ℕ) (x : Fin r) :
    Fintype.card {z : Fin r // z ≠ x} = r - 1 := by
  rw [Fintype.card_subtype_compl (fun z : Fin r ↦ z = x)]
  simp

lemma card_counterQuad (r : ℕ) :
    Fintype.card (CounterQuad r) = r ^ 2 * 2 ^ (2 * (r - 1)) := by
  simp only [CounterQuad, Fintype.card_sigma, Fintype.card_prod, Fintype.card_finset,
    card_fin_ne, Finset.sum_const_nat]
  simp [Finset.card_univ]
  ring

lemma quad_pair_injective (r : ℕ) :
    Function.Injective (fun q : CounterQuad r ↦ (quadLower q, quadUpper q)) := by
  rintro ⟨x, y, A, B⟩ ⟨x', y', A', B'⟩ h
  change (lowerSet r (x, forgetNe A), upperSet r (y, insert x (forgetNe B))) =
    (lowerSet r (x', forgetNe A'), upperSet r (y', insert x' (forgetNe B'))) at h
  have hl : lowerSet r (x, forgetNe A) = lowerSet r (x', forgetNe A') :=
    congrArg Prod.fst h
  have hl' := lowerSet_injective r hl
  have hx : x = x' := congrArg Prod.fst hl'
  subst x'
  have hu : upperSet r (y, insert x (forgetNe B)) =
      upperSet r (y', insert x (forgetNe B')) := congrArg Prod.snd h
  have hu' := upperSet_injective r hu
  have hy : y = y' := congrArg Prod.fst hu'
  subst y'
  have hAmap : forgetNe A = forgetNe A' := congrArg Prod.snd hl'
  have hA : A = A' := forgetNe_injective hAmap
  subst A'
  have hBins : insert x (forgetNe B) = insert x (forgetNe B') := congrArg Prod.snd hu'
  have hxB : x ∉ forgetNe B := by simp [mem_forgetNe]
  have hxB' : x ∉ forgetNe B' := by simp [mem_forgetNe]
  have hBmap : forgetNe B = forgetNe B' := by
    have := congrArg (fun S : Finset (Fin r) ↦ S.erase x) hBins
    simpa [Finset.erase_insert hxB, Finset.erase_insert hxB'] using this
  have hB : B = B' := forgetNe_injective hBmap
  subst B'
  rfl

lemma quadLower_mem_lowerFamily {r : ℕ} (q : CounterQuad r) :
    quadLower q ∈ lowerFamily r := by
  apply Finset.mem_map.mpr
  exact ⟨(q.1, forgetNe q.2.2.1), Finset.mem_univ _, rfl⟩

lemma quadUpper_mem_upperFamily {r : ℕ} (q : CounterQuad r) :
    quadUpper q ∈ upperFamily r := by
  apply Finset.mem_map.mpr
  exact ⟨(q.2.1, insert q.1 (forgetNe q.2.2.2)), Finset.mem_univ _, rfl⟩

lemma counterQuad_le_edges (r : ℕ) :
    r ^ 2 * 2 ^ (2 * (r - 1)) ≤ comparableEdges (counterFamily r) := by
  rw [comparableEdges_eq_strictContainments, ← card_counterQuad]
  let e : CounterGround r ↪ Fin (r + (r + 1)) := (counterGroundEquiv r).toEmbedding
  let V := {A // A ∈ counterFamily r}
  let target := {p : V × V // p.1.1 < p.2.1}
  let f : CounterQuad r → target := fun q ↦
    ⟨(⟨(quadLower q).map e, by
          simp only [counterFamily, Finset.mem_map]
          exact ⟨quadLower q, by
            exact Finset.mem_union_left _ (quadLower_mem_lowerFamily q), rfl⟩⟩,
       ⟨(quadUpper q).map e, by
          simp only [counterFamily, Finset.mem_map]
          exact ⟨quadUpper q, by
            exact Finset.mem_union_right _ (quadUpper_mem_upperFamily q), rfl⟩⟩),
      Finset.map_ssubset_map.mpr (quadLower_ssubset_quadUpper q)⟩
  have hf : Function.Injective f := by
    intro q q' h
    have hpair : ((quadLower q).map e, (quadUpper q).map e) =
        ((quadLower q').map e, (quadUpper q').map e) := by
      exact congrArg (fun z : target ↦ (z.1.1.1, z.1.2.1)) h
    have hl : quadLower q = quadLower q' := Finset.map_injective e (congrArg Prod.fst hpair)
    have hu : quadUpper q = quadUpper q' := Finset.map_injective e (congrArg Prod.snd hpair)
    exact quad_pair_injective r (Prod.ext hl hu)
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [strictContainments, target, V, Fintype.card_subtype] using hcard

lemma counterFamily_density {r : ℕ} (hr : 1 ≤ r) :
    (1 / 16 : ℝ) * ((counterFamily r).card : ℝ) ^ 2 ≤
      comparableEdges (counterFamily r) := by
  have he := counterQuad_le_edges r
  have hpow : 16 * (r ^ 2 * 2 ^ (2 * (r - 1))) = (2 * r * 2 ^ r) ^ 2 := by
    have hexp : 2 * (r - 1) + 4 = 2 * r + 2 := by omega
    calc
      16 * (r ^ 2 * 2 ^ (2 * (r - 1))) =
          r ^ 2 * (2 ^ (2 * (r - 1)) * 2 ^ 4) := by norm_num; ring
      _ = r ^ 2 * 2 ^ (2 * (r - 1) + 4) := by rw [pow_add]
      _ = r ^ 2 * 2 ^ (2 * r + 2) := by rw [hexp]
      _ = (2 * r * 2 ^ r) ^ 2 := by
        rw [pow_add]
        norm_num
        rw [show 2 * r = r * 2 by omega, pow_mul]
        ring
  have hpow' : (1 / 16 : ℝ) * ((2 * r * 2 ^ r : ℕ) : ℝ) ^ 2 =
      (r ^ 2 * 2 ^ (2 * (r - 1)) : ℕ) := by
    have hpowR : (16 : ℝ) * (r ^ 2 * 2 ^ (2 * (r - 1)) : ℕ) =
        ((2 * r * 2 ^ r : ℕ) : ℝ) ^ 2 := by exact_mod_cast hpow
    linarith
  rw [card_counterFamily, hpow']
  exact_mod_cast he

/-- The affirmative answer to the first question in Problem 777. -/
def FirstQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ 𝓕 : Finset (Finset (Fin n)),
      (𝓕.card : ℝ) ≤ (2 - ε) * (2 : ℝ) ^ ((n : ℝ) / 2) →
      comparableEdges 𝓕 < 2 ^ n

/-- The uniform `O_c(2^{n/2})` assertion proposed in the second question. -/
def SecondQuestion : Prop :=
  ∀ c : ℝ, 0 < c →
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ 𝓕 : Finset (Finset (Fin n)),
      c * (𝓕.card : ℝ) ^ 2 ≤ comparableEdges 𝓕 →
      (𝓕.card : ℝ) ≤ C * (2 : ℝ) ^ ((n : ℝ) / 2)

theorem secondQuestion_false : ¬ SecondQuestion := by
  intro h
  obtain ⟨C, hC, hbound⟩ := h (1 / 16) (by norm_num)
  obtain ⟨r, hrC⟩ := exists_nat_gt C
  let R : ℕ := max r 2
  have hRr : r ≤ R := Nat.le_max_left _ _
  have hR2 : 2 ≤ R := Nat.le_max_right _ _
  have hRC : C < R := hrC.trans_le (by exact_mod_cast hRr)
  have hdense : (1 / 16 : ℝ) * ((counterFamily R).card : ℝ) ^ 2 ≤
      comparableEdges (counterFamily R) := counterFamily_density (by omega)
  have hb := hbound (R + (R + 1)) (counterFamily R) hdense
  have hexp : ((R + (R + 1) : ℕ) : ℝ) / 2 ≤ (R + 1 : ℕ) := by
    norm_num
    linarith
  have hq : (2 : ℝ) ^ (((R + (R + 1) : ℕ) : ℝ) / 2) ≤
      (2 : ℝ) ^ (R + 1 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  rw [card_counterFamily] at hb
  have hCnonneg : 0 ≤ C := hC.le
  have hb' : ((2 * R * 2 ^ R : ℕ) : ℝ) ≤ C * (2 : ℝ) ^ (R + 1 : ℕ) :=
    hb.trans (mul_le_mul_of_nonneg_left hq hCnonneg)
  rw [pow_succ] at hb'
  have hpowpos : (0 : ℝ) < (2 : ℕ) ^ R := by positivity
  have hRCast : C < (R : ℝ) := by exact_mod_cast hRC
  norm_num [Nat.cast_mul, Nat.cast_pow] at hb'
  have hmul := mul_lt_mul_of_pos_right hRCast hpowpos
  ring_nf at hb' hmul
  linarith

/-! ## A finite-moment estimate for containments -/

/-- Forget the membership certificates in a tuple of members of `S`. -/
def tupleSubtypeEmbedding {β : Type*} [DecidableEq β]
    (S : Finset β) (t : ℕ) : (Fin t → {x // x ∈ S}) ↪ (Fin t → β) where
  toFun f i := (f i).1
  inj' := by
    intro f g h
    funext i
    apply Subtype.ext
    exact congrFun h i

/-- The finite set of `t`-tuples with every coordinate in `S`. -/
def tuplesFrom {β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset β) (t : ℕ) : Finset (Fin t → β) :=
  Finset.univ.map (tupleSubtypeEmbedding S t)

@[simp] lemma mem_tuplesFrom {β : Type*} [Fintype β] [DecidableEq β]
    {S : Finset β} {t : ℕ} {f : Fin t → β} :
    f ∈ tuplesFrom S t ↔ ∀ i, f i ∈ S := by
  constructor
  · intro hf i
    rw [tuplesFrom, Finset.mem_map] at hf
    obtain ⟨g, -, rfl⟩ := hf
    exact (g i).2
  · intro hf
    rw [tuplesFrom, Finset.mem_map]
    let g : Fin t → {x // x ∈ S} := fun i ↦ ⟨f i, hf i⟩
    exact ⟨g, Finset.mem_univ _, by funext i; rfl⟩

@[simp] lemma card_tuplesFrom {β : Type*} [Fintype β] [DecidableEq β]
    (S : Finset β) (t : ℕ) : (tuplesFrom S t).card = S.card ^ t := by
  simp [tuplesFrom, Fintype.card_coe]

/-- Union of the coordinates of a tuple of sets. -/
def tupleUnion {α : Type*} [DecidableEq α] {t : ℕ}
    (f : Fin t → Finset α) : Finset α :=
  Finset.univ.biUnion f

lemma tuple_subset_union {α : Type*} [DecidableEq α] {t : ℕ}
    (f : Fin t → Finset α) (i : Fin t) : f i ⊆ tupleUnion f :=
  Finset.subset_biUnion_of_mem f (Finset.mem_univ i)

/-- A set `B` together with a `t`-tuple of members of `𝓕` lying below it. -/
def momentPairs {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    Finset (Σ _B : Finset (Fin n), Fin t → Finset (Fin n)) :=
  𝓕.sigma fun B ↦ tuplesFrom (𝓕.filter fun A ↦ A ⊆ B) t

@[simp] lemma mem_momentPairs {n t : ℕ} {𝓕 : Finset (Finset (Fin n))}
    {q : Σ _B : Finset (Fin n), Fin t → Finset (Fin n)} :
    q ∈ momentPairs 𝓕 t ↔ q.1 ∈ 𝓕 ∧ ∀ i, q.2 i ∈ 𝓕 ∧ q.2 i ⊆ q.1 := by
  simp [momentPairs]

lemma card_momentPairs {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (momentPairs 𝓕 t).card =
      ∑ B ∈ 𝓕, (𝓕.filter fun A ↦ A ⊆ B).card ^ t := by
  simp [momentPairs, Finset.card_sigma]

/-- The total number of non-strict ordered containments in `𝓕`. -/
def containmentCount {n : ℕ} (𝓕 : Finset (Finset (Fin n))) : ℕ :=
  ∑ B ∈ 𝓕, (𝓕.filter fun A ↦ A ⊆ B).card

lemma strictContainments_le_containmentCount {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) :
    strictContainments 𝓕 ≤ containmentCount 𝓕 := by
  let V := {A // A ∈ 𝓕}
  let s : Finset (V × V) := Finset.univ.filter fun p ↦ p.1.1 < p.2.1
  let t : Finset (Σ _B : Finset (Fin n), Finset (Fin n)) :=
    𝓕.sigma fun B ↦ 𝓕.filter fun A ↦ A ⊆ B
  let f : V × V → (Σ _B : Finset (Fin n), Finset (Fin n)) :=
    fun p ↦ ⟨p.2.1, p.1.1⟩
  have hmap : Set.MapsTo f (s : Set (V × V)) (t : Set _) := by
    intro p hp
    have hp' : p.1.1 < p.2.1 := (Finset.mem_filter.mp hp).2
    change (⟨p.2.1, p.1.1⟩ : Σ _B : Finset (Fin n), Finset (Fin n)) ∈
      𝓕.sigma (fun B ↦ 𝓕.filter fun A ↦ A ⊆ B)
    exact Finset.mem_sigma.mpr
      ⟨p.2.2, Finset.mem_filter.mpr ⟨p.1.2, hp'.le⟩⟩
  have hinj : Set.InjOn f (s : Set (V × V)) := by
    intro p _ q _ h
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg (fun z ↦ z.2) h
    · apply Subtype.ext
      exact congrArg (fun z ↦ z.1) h
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  simpa [strictContainments, containmentCount, s, t, Finset.card_sigma] using hcard

lemma containmentCount_moment {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    {t : ℕ} (ht : 1 ≤ t) :
    containmentCount 𝓕 ^ t ≤ 𝓕.card ^ (t - 1) * (momentPairs 𝓕 t).card := by
  have hj := pow_sum_le_card_mul_sum_pow
    (s := 𝓕) (f := fun B ↦ ((𝓕.filter fun A ↦ A ⊆ B).card : ℝ))
    (fun _ _ ↦ by positivity) (t - 1)
  have ht' : t - 1 + 1 = t := by omega
  rw [ht'] at hj
  have hcard := congrArg (fun z : ℕ ↦ (z : ℝ)) (card_momentPairs 𝓕 t)
  norm_num [Nat.cast_sum, Nat.cast_pow] at hcard
  rw [← hcard] at hj
  have hj' : ((containmentCount 𝓕 ^ t : ℕ) : ℝ) ≤
      ((𝓕.card ^ (t - 1) * (momentPairs 𝓕 t).card : ℕ) : ℝ) := by
    simpa [containmentCount, Nat.cast_sum, Nat.cast_pow, Nat.cast_mul] using hj
  exact_mod_cast hj'

lemma tupleUnion_subset {α : Type*} [DecidableEq α] {t : ℕ}
    {f : Fin t → Finset α} {B : Finset α} (h : ∀ i, f i ⊆ B) :
    tupleUnion f ⊆ B := by
  intro z hz
  rw [tupleUnion, Finset.mem_biUnion] at hz
  obtain ⟨i, -, hzi⟩ := hz
  exact h i hzi

def smallMoments {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :=
  (momentPairs 𝓕 t).filter fun q ↦ (tupleUnion q.2).card ≤ n / 2

def smallCodes {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    Finset (Σ _U : Finset (Fin n), (Fin t → Finset (Fin n)) × Finset (Fin n)) :=
  (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 2).sigma fun U ↦
    (tuplesFrom U.powerset t).product 𝓕

def toSmallCode {n t : ℕ} :
    (Σ _B : Finset (Fin n), Fin t → Finset (Fin n)) →
      (Σ _U : Finset (Fin n), (Fin t → Finset (Fin n)) × Finset (Fin n)) :=
  fun q ↦ ⟨tupleUnion q.2, (q.2, q.1)⟩

lemma card_smallMoments_le_codes {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (smallMoments 𝓕 t).card ≤ (smallCodes 𝓕 t).card := by
  apply Finset.card_le_card_of_injOn toSmallCode
  · intro q hq
    have hq' := (Finset.mem_filter.mp hq)
    have hm := mem_momentPairs.mp hq'.1
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq'.2⟩
    · apply Finset.mem_product.mpr
      constructor
      · rw [mem_tuplesFrom]
        intro i
        exact Finset.mem_powerset.mpr (tuple_subset_union q.2 i)
      · exact hm.1
  · intro q _ q' _ h
    rcases q with ⟨B, f⟩
    rcases q' with ⟨B', f'⟩
    have hp : (f, B) = (f', B') := congrArg Sigma.snd h
    have hf : f = f' := congrArg Prod.fst hp
    have hB : B = B' := congrArg Prod.snd hp
    subst f'
    subst B'
    rfl

lemma card_smallCodes_le {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (smallCodes 𝓕 t).card ≤ 2 ^ n * ((2 ^ (n / 2)) ^ t * 𝓕.card) := by
  rw [smallCodes, Finset.card_sigma]
  calc
    (∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 2),
        ((tuplesFrom U.powerset t).product 𝓕).card) =
        ∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 2),
          (2 ^ U.card) ^ t * 𝓕.card := by
            apply Finset.sum_congr rfl
            intro U _
            simp
    _ ≤ ∑ _U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 2),
          (2 ^ (n / 2)) ^ t * 𝓕.card := by
            apply Finset.sum_le_sum
            intro U hU
            have hcard := (Finset.mem_filter.mp hU).2
            exact Nat.mul_le_mul_right _
              (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by omega) hcard) t)
    _ = (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 2).card *
          ((2 ^ (n / 2)) ^ t * 𝓕.card) := by simp
    _ ≤ 2 ^ n * ((2 ^ (n / 2)) ^ t * 𝓕.card) := by
      gcongr
      calc
        (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 2).card ≤
            (Finset.univ : Finset (Finset (Fin n))).card := Finset.card_filter_le _ _
        _ = 2 ^ n := by simp

def largeMoments {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :=
  (momentPairs 𝓕 t).filter fun q ↦ ¬(tupleUnion q.2).card ≤ n / 2

def largeCodes {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    Finset (Σ _f : Fin t → Finset (Fin n), Finset (Fin n)) :=
  ((tuplesFrom 𝓕 t).filter fun f ↦ ¬(tupleUnion f).card ≤ n / 2).sigma fun f ↦
    ((Finset.univ : Finset (Fin n)) \ tupleUnion f).powerset

def toLargeCode {n t : ℕ} :
    (Σ _B : Finset (Fin n), Fin t → Finset (Fin n)) →
      (Σ _f : Fin t → Finset (Fin n), Finset (Fin n)) :=
  fun q ↦ ⟨q.2, q.1 \ tupleUnion q.2⟩

lemma card_largeMoments_le_codes {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (largeMoments 𝓕 t).card ≤ (largeCodes 𝓕 t).card := by
  apply Finset.card_le_card_of_injOn toLargeCode
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hm := mem_momentPairs.mp hq'.1
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨mem_tuplesFrom.mpr (fun i ↦ (hm.2 i).1), hq'.2⟩
    · apply Finset.mem_powerset.mpr
      exact Finset.sdiff_subset_sdiff_left _ (Finset.subset_univ _)
  · intro q hq q' hq' h
    rcases q with ⟨B, f⟩
    rcases q' with ⟨B', f'⟩
    have hfun : f = f' := congrArg Sigma.fst h
    subst f'
    have hdiff : B \ tupleUnion f = B' \ tupleUnion f := congrArg Sigma.snd h
    have hm := mem_momentPairs.mp (Finset.mem_filter.mp hq).1
    have hm' := mem_momentPairs.mp (Finset.mem_filter.mp hq').1
    have hu : tupleUnion f ⊆ B := tupleUnion_subset (fun i ↦ (hm.2 i).2)
    have hu' : tupleUnion f ⊆ B' := tupleUnion_subset (fun i ↦ (hm'.2 i).2)
    have hB : B = B' := by
      ext z
      by_cases hz : z ∈ tupleUnion f
      · exact iff_of_true (hu hz) (hu' hz)
      · have hd := Finset.ext_iff.mp hdiff z
        simpa [hz] using hd
    subst B'
    rfl

lemma card_largeCodes_le {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (largeCodes 𝓕 t).card ≤ 𝓕.card ^ t * 2 ^ (n / 2) := by
  rw [largeCodes, Finset.card_sigma]
  calc
    (∑ f ∈ (tuplesFrom 𝓕 t).filter fun f ↦ ¬(tupleUnion f).card ≤ n / 2,
        (((Finset.univ : Finset (Fin n)) \ tupleUnion f).powerset).card) ≤
        ∑ _f ∈ (tuplesFrom 𝓕 t).filter fun f ↦ ¬(tupleUnion f).card ≤ n / 2,
          2 ^ (n / 2) := by
            apply Finset.sum_le_sum
            intro f hf
            rw [Finset.card_powerset]
            have hlarge := (Finset.mem_filter.mp hf).2
            apply Nat.pow_le_pow_right (by omega)
            have hu : (tupleUnion f).card ≤ n := by
              simpa using Finset.card_le_card (Finset.subset_univ (tupleUnion f))
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
              Fintype.card_fin]
            omega
    _ = ((tuplesFrom 𝓕 t).filter fun f ↦ ¬(tupleUnion f).card ≤ n / 2).card *
          2 ^ (n / 2) := by simp
    _ ≤ 𝓕.card ^ t * 2 ^ (n / 2) := by
      gcongr
      exact (Finset.card_filter_le _ _).trans_eq (card_tuplesFrom 𝓕 t)

lemma card_momentPairs_le {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (momentPairs 𝓕 t).card ≤
      2 ^ n * ((2 ^ (n / 2)) ^ t * 𝓕.card) + 𝓕.card ^ t * 2 ^ (n / 2) := by
  have hpart : (momentPairs 𝓕 t).card =
      (smallMoments 𝓕 t).card + (largeMoments 𝓕 t).card := by
    rw [smallMoments, largeMoments, ← Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter_not (momentPairs 𝓕 t) (momentPairs 𝓕 t) _),
      Finset.filter_union_filter_not_eq]
  rw [hpart]
  exact Nat.add_le_add
    ((card_smallMoments_le_codes 𝓕 t).trans (card_smallCodes_le 𝓕 t))
    ((card_largeMoments_le_codes 𝓕 t).trans (card_largeCodes_le 𝓕 t))

lemma comparableEdges_pow_le {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    {t : ℕ} (ht : 1 ≤ t) :
    comparableEdges 𝓕 ^ t ≤
      𝓕.card ^ t * 2 ^ n * (2 ^ (n / 2)) ^ t +
        𝓕.card ^ (2 * t - 1) * 2 ^ (n / 2) := by
  have hec : comparableEdges 𝓕 ≤ containmentCount 𝓕 :=
    (comparableEdges_eq_strictContainments 𝓕).le.trans
      (strictContainments_le_containmentCount 𝓕)
  calc
    comparableEdges 𝓕 ^ t ≤ containmentCount 𝓕 ^ t := Nat.pow_le_pow_left hec t
    _ ≤ 𝓕.card ^ (t - 1) * (momentPairs 𝓕 t).card := containmentCount_moment 𝓕 ht
    _ ≤ 𝓕.card ^ (t - 1) *
        (2 ^ n * ((2 ^ (n / 2)) ^ t * 𝓕.card) +
          𝓕.card ^ t * 2 ^ (n / 2)) :=
      Nat.mul_le_mul_left _ (card_momentPairs_le 𝓕 t)
    _ = 𝓕.card ^ t * 2 ^ n * (2 ^ (n / 2)) ^ t +
        𝓕.card ^ (2 * t - 1) * 2 ^ (n / 2) := by
      rw [mul_add]
      calc
        𝓕.card ^ (t - 1) * (2 ^ n * ((2 ^ (n / 2)) ^ t * 𝓕.card)) +
            𝓕.card ^ (t - 1) * (𝓕.card ^ t * 2 ^ (n / 2)) =
            (𝓕.card ^ (t - 1) * 𝓕.card) * 2 ^ n * (2 ^ (n / 2)) ^ t +
              (𝓕.card ^ (t - 1) * 𝓕.card ^ t) * 2 ^ (n / 2) := by ring
        _ = _ := by
          rw [← pow_succ, show t - 1 + 1 = t by omega,
            ← pow_add, show t - 1 + t = 2 * t - 1 by omega]

lemma exists_power_parameters (b : ℝ) (hb : 2 < b) :
    ∃ t : ℕ, ∃ δ : ℝ, 4 ≤ t ∧ 0 < δ ∧ 2 * (t : ℝ) * δ < 1 ∧
      (2 : ℝ) ^ ((t : ℝ) + 2) < b ^ ((t : ℝ) * (1 - 2 * δ)) ∧
      (2 : ℝ) < b ^ (1 - 2 * (t : ℝ) * δ) := by
  let L : ℝ := Real.log b
  let l : ℝ := Real.log 2
  have hl : 0 < l := Real.log_pos (by norm_num)
  have hL : 0 < L := Real.log_pos (by linarith)
  have hlL : l < L := by
    dsimp [l, L]
    exact Real.log_lt_log (by norm_num) hb
  have hd : 0 < L - l := sub_pos.mpr hlL
  obtain ⟨r, hr⟩ := exists_nat_gt (2 * l / (L - l))
  let t : ℕ := max r 4
  have htr : r ≤ t := Nat.le_max_left _ _
  have ht4 : 4 ≤ t := Nat.le_max_right _ _
  have htpos : (0 : ℝ) < t := by positivity
  have htg : 2 * l < (t : ℝ) * (L - l) := by
    have hr' : 2 * l / (L - l) < (t : ℝ) := hr.trans_le (by exact_mod_cast htr)
    rw [div_lt_iff₀ hd] at hr'
    linarith
  let g₁ : ℝ := (t : ℝ) * L - ((t : ℝ) + 2) * l
  let g₂ : ℝ := L - l
  have hg₁ : 0 < g₁ := by dsimp [g₁]; nlinarith
  have hg₂ : 0 < g₂ := by simpa [g₂] using hd
  let δ : ℝ := min g₁ g₂ / (8 * (t : ℝ) * L)
  have hden : 0 < 8 * (t : ℝ) * L := by positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (lt_min hg₁ hg₂) hden
  have hmin₁ : min g₁ g₂ ≤ g₁ := min_le_left _ _
  have hmin₂ : min g₁ g₂ ≤ g₂ := min_le_right _ _
  have hminL : min g₁ g₂ < L := hmin₂.trans_lt (by dsimp [g₂]; linarith)
  have htwodelta : 2 * (t : ℝ) * δ < 1 := by
    dsimp [δ]
    rw [div_eq_mul_inv]
    have hLi : 0 < L⁻¹ := inv_pos.mpr hL
    field_simp
    nlinarith
  have hgap₁ : ((t : ℝ) + 2) * l < (t : ℝ) * (1 - 2 * δ) * L := by
    have hsmall : 2 * (t : ℝ) * δ * L ≤ g₁ / 4 := by
      dsimp [δ]
      field_simp
      nlinarith
    dsimp [g₁] at hsmall ⊢
    nlinarith
  have hgap₂ : l < (1 - 2 * (t : ℝ) * δ) * L := by
    have hsmall : 2 * (t : ℝ) * δ * L ≤ g₂ / 4 := by
      dsimp [δ]
      field_simp
      nlinarith
    dsimp [g₂] at hsmall
    nlinarith
  refine ⟨t, δ, ht4, hδ, htwodelta, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by linarith),
      Real.exp_lt_exp]
    dsimp [l, L] at hgap₁ ⊢
    nlinarith
  · calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ < Real.exp (Real.log b * (1 - 2 * (t : ℝ) * δ)) := by
        rw [Real.exp_lt_exp]
        dsimp [l, L] at hgap₂
        nlinarith
      _ = b ^ (1 - 2 * (t : ℝ) * δ) :=
        (Real.rpow_def_of_pos (by linarith) _).symm

lemma nat_half_cast_le (n : ℕ) : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
  have h : (n / 2) * 2 ≤ n := Nat.div_mul_le_self n 2
  have h' : (((n / 2) * 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  norm_num [Nat.cast_mul] at h'
  linarith

lemma first_moment_factor_bound {b δ : ℝ} {t n m : ℕ}
    (hb : 0 < b) (hδ : 0 ≤ (t : ℝ) * (1 - 2 * δ))
    (hbase : (2 : ℝ) ^ ((t : ℝ) + 2) ≤ b ^ ((t : ℝ) * (1 - 2 * δ)))
    (hm : b ^ ((n : ℝ) / 2) ≤ (m : ℝ)) :
    (2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2)) ^ t ≤
      (m : ℝ) ^ ((t : ℝ) * (1 - 2 * δ)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
  have he : (n : ℝ) + ((n / 2 : ℕ) : ℝ) * (t : ℝ) ≤
      ((t : ℝ) + 2) * ((n : ℝ) / 2) := by
    have hh := nat_half_cast_le n
    nlinarith
  calc
    (2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2)) ^ t =
        (2 : ℝ) ^ ((n : ℝ) + ((n / 2 : ℕ) : ℝ) * (t : ℝ)) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_mul (by positivity),
        Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (((t : ℝ) + 2) * ((n : ℝ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = ((2 : ℝ) ^ ((t : ℝ) + 2)) ^ ((n : ℝ) / 2) :=
      Real.rpow_mul (by positivity) _ _
    _ ≤ (b ^ ((t : ℝ) * (1 - 2 * δ))) ^ ((n : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hbase hn
    _ = b ^ (((t : ℝ) * (1 - 2 * δ)) * ((n : ℝ) / 2)) :=
      (Real.rpow_mul hb.le _ _).symm
    _ = (b ^ ((n : ℝ) / 2)) ^ ((t : ℝ) * (1 - 2 * δ)) := by
      rw [← Real.rpow_mul (y := (n : ℝ) / 2)
        (z := (t : ℝ) * (1 - 2 * δ)) hb.le]
      congr 1 <;> ring
    _ ≤ (m : ℝ) ^ ((t : ℝ) * (1 - 2 * δ)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hb.le _) hm hδ

lemma second_moment_factor_bound {b δ : ℝ} {t n m : ℕ}
    (hb : 0 < b) (hδ : 0 ≤ 1 - 2 * (t : ℝ) * δ)
    (hbase : (2 : ℝ) ≤ b ^ (1 - 2 * (t : ℝ) * δ))
    (hm : b ^ ((n : ℝ) / 2) ≤ (m : ℝ)) :
    (2 : ℝ) ^ (n / 2) ≤ (m : ℝ) ^ (1 - 2 * (t : ℝ) * δ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
  have hh := nat_half_cast_le n
  calc
    (2 : ℝ) ^ (n / 2) = (2 : ℝ) ^ ((n / 2 : ℕ) : ℝ) :=
      (Real.rpow_natCast 2 (n / 2)).symm
    _ ≤ (2 : ℝ) ^ ((n : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hh
    _ ≤ (b ^ (1 - 2 * (t : ℝ) * δ)) ^ ((n : ℝ) / 2) :=
      Real.rpow_le_rpow (by positivity) hbase hn
    _ = b ^ ((1 - 2 * (t : ℝ) * δ) * ((n : ℝ) / 2)) :=
      (Real.rpow_mul hb.le _ _).symm
    _ = (b ^ ((n : ℝ) / 2)) ^ (1 - 2 * (t : ℝ) * δ) := by
      rw [← Real.rpow_mul (y := (n : ℝ) / 2)
        (z := 1 - 2 * (t : ℝ) * δ) hb.le]
      congr 1 <;> ring
    _ ≤ (m : ℝ) ^ (1 - 2 * (t : ℝ) * δ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hb.le _) hm hδ

lemma edge_power_saving_of_factors {b δ : ℝ} {t n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (ht : 1 ≤ t) (hb : 0 < b)
    (hδ₁ : 0 ≤ (t : ℝ) * (1 - 2 * δ))
    (hδ₂ : 0 ≤ 1 - 2 * (t : ℝ) * δ)
    (hbase₁ : (2 : ℝ) ^ ((t : ℝ) + 2) ≤ b ^ ((t : ℝ) * (1 - 2 * δ)))
    (hbase₂ : (2 : ℝ) ≤ b ^ (1 - 2 * (t : ℝ) * δ))
    (hm : b ^ ((n : ℝ) / 2) ≤ (𝓕.card : ℝ))
    (habsorb : (2 : ℝ) ≤ (𝓕.card : ℝ) ^ ((t : ℝ) * δ)) :
    (comparableEdges 𝓕 : ℝ) ≤ (𝓕.card : ℝ) ^ (2 - δ) := by
  have hmpos : (0 : ℝ) < 𝓕.card :=
    (Real.rpow_pos_of_pos hb _).trans_le hm
  have hf₁ := first_moment_factor_bound hb hδ₁ hbase₁ hm
  have hf₂ := second_moment_factor_bound hb hδ₂ hbase₂ hm
  have hmomentNat := comparableEdges_pow_le 𝓕 ht
  have hmoment : ((comparableEdges 𝓕 : ℕ) : ℝ) ^ t ≤
      (𝓕.card : ℝ) ^ t * (2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2)) ^ t +
        (𝓕.card : ℝ) ^ (2 * t - 1) * (2 : ℝ) ^ (n / 2) := by
    exact_mod_cast hmomentNat
  let P : ℝ := (𝓕.card : ℝ) ^ ((t : ℝ) * (2 - 2 * δ))
  have hterm₁ : (𝓕.card : ℝ) ^ t *
      ((2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2)) ^ t) ≤ P := by
    calc
      (𝓕.card : ℝ) ^ t * ((2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2)) ^ t) ≤
          (𝓕.card : ℝ) ^ t * (𝓕.card : ℝ) ^ ((t : ℝ) * (1 - 2 * δ)) :=
        mul_le_mul_of_nonneg_left hf₁ (by positivity)
      _ = P := by
        dsimp [P]
        rw [← Real.rpow_natCast, ← Real.rpow_add hmpos]
        congr 1
        ring
  have hterm₂ : (𝓕.card : ℝ) ^ (2 * t - 1) * (2 : ℝ) ^ (n / 2) ≤ P := by
    calc
      (𝓕.card : ℝ) ^ (2 * t - 1) * (2 : ℝ) ^ (n / 2) ≤
          (𝓕.card : ℝ) ^ (2 * t - 1) *
            (𝓕.card : ℝ) ^ (1 - 2 * (t : ℝ) * δ) :=
        mul_le_mul_of_nonneg_left hf₂ (by positivity)
      _ = P := by
        dsimp [P]
        rw [← Real.rpow_natCast, ← Real.rpow_add hmpos]
        congr 1
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * t)]
        push_cast
        ring
  have hsum : ((comparableEdges 𝓕 : ℕ) : ℝ) ^ t ≤ 2 * P := by
    calc
      ((comparableEdges 𝓕 : ℕ) : ℝ) ^ t ≤
          (𝓕.card : ℝ) ^ t *
              ((2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 2)) ^ t) +
            (𝓕.card : ℝ) ^ (2 * t - 1) * (2 : ℝ) ^ (n / 2) := by
        simpa only [mul_assoc] using hmoment
      _ ≤ P + P := add_le_add hterm₁ hterm₂
      _ = 2 * P := by ring
  have habs : 2 * P ≤ (𝓕.card : ℝ) ^ ((t : ℝ) * (2 - δ)) := by
    calc
      2 * P ≤ (𝓕.card : ℝ) ^ ((t : ℝ) * δ) * P :=
        mul_le_mul_of_nonneg_right habsorb (by positivity)
      _ = (𝓕.card : ℝ) ^ ((t : ℝ) * (2 - δ)) := by
        dsimp [P]
        rw [← Real.rpow_add hmpos]
        congr 1
        ring
  by_contra hnot
  have hlt : (𝓕.card : ℝ) ^ (2 - δ) < (comparableEdges 𝓕 : ℝ) := lt_of_not_ge hnot
  have htpos : (0 : ℝ) < t := by positivity
  have hpw := Real.rpow_lt_rpow (Real.rpow_nonneg hmpos.le _) hlt htpos
  have hpw' : (𝓕.card : ℝ) ^ ((t : ℝ) * (2 - δ)) <
      ((comparableEdges 𝓕 : ℕ) : ℝ) ^ t := by
    calc
      (𝓕.card : ℝ) ^ ((t : ℝ) * (2 - δ)) =
          ((𝓕.card : ℝ) ^ (2 - δ)) ^ (t : ℝ) := by
        rw [← Real.rpow_mul hmpos.le]
        congr 1
        ring
      _ < ((comparableEdges 𝓕 : ℕ) : ℝ) ^ (t : ℝ) := hpw
      _ = ((comparableEdges 𝓕 : ℕ) : ℝ) ^ t := Real.rpow_natCast _ _
  exact (not_lt_of_ge (hsum.trans habs)) hpw'

lemma comparableEdges_lt_half_square {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (hm : 0 < 𝓕.card) :
    (comparableEdges 𝓕 : ℝ) < (𝓕.card : ℝ) ^ 2 / 2 := by
  have hedge := (comparableGraph 𝓕).card_edgeFinset_le_card_choose_two
  have hediv : comparableEdges 𝓕 ≤ 𝓕.card * (𝓕.card - 1) / 2 := by
    simpa [comparableEdges, Fintype.card_coe, Nat.choose_two_right] using hedge
  have hemul : comparableEdges 𝓕 * 2 ≤ 𝓕.card * (𝓕.card - 1) :=
    (Nat.le_div_iff_mul_le (by omega)).mp hediv
  have hemulR : (comparableEdges 𝓕 : ℝ) * 2 ≤
      (𝓕.card : ℝ) * (𝓕.card - 1) := by
    have h' : ((comparableEdges 𝓕 * 2 : ℕ) : ℝ) ≤
        ((𝓕.card * (𝓕.card - 1) : ℕ) : ℝ) := by exact_mod_cast hemul
    norm_num [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 𝓕.card)] at h' ⊢
    exact h'
  have hmR : (0 : ℝ) < 𝓕.card := by exact_mod_cast hm
  nlinarith

lemma small_dimension_power_bound {δ : ℝ} {N n : ℕ}
    (hδ : 0 < δ) (hδN : δ * (N : ℝ) ≤ 1) (hn : n < N)
    (𝓕 : Finset (Finset (Fin n))) :
    (comparableEdges 𝓕 : ℝ) ≤ (𝓕.card : ℝ) ^ (2 - δ) := by
  by_cases hm0 : 𝓕.card = 0
  · have hF : 𝓕 = ∅ := Finset.card_eq_zero.mp hm0
    subst 𝓕
    have hedge := (comparableGraph (∅ : Finset (Finset (Fin n)))).card_edgeFinset_le_card_choose_two
    have he : comparableEdges (∅ : Finset (Finset (Fin n))) = 0 := by
      rw [comparableEdges]
      apply Nat.eq_zero_of_le_zero
      simpa [Fintype.card_coe] using hedge
    rw [he]
    norm_num only [Finset.card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by norm_num) (2 - δ)
  have hm : 0 < 𝓕.card := Nat.pos_of_ne_zero hm0
  have hedge := comparableEdges_lt_half_square 𝓕 hm
  have hmcard : 𝓕.card ≤ 2 ^ n := by
    calc
      𝓕.card ≤ (Finset.univ : Finset (Finset (Fin n))).card := Finset.card_le_univ _
      _ = 2 ^ n := by simp
  have hnN : n ≤ N := by omega
  have hmN : (𝓕.card : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast hmcard.trans (Nat.pow_le_pow_right (by omega) hnN)
  have hmnonneg : (0 : ℝ) ≤ 𝓕.card := by positivity
  have hmdelta : (𝓕.card : ℝ) ^ δ ≤ 2 := by
    calc
      (𝓕.card : ℝ) ^ δ ≤ ((2 : ℝ) ^ N) ^ δ :=
        Real.rpow_le_rpow hmnonneg hmN hδ.le
      _ = (2 : ℝ) ^ ((N : ℝ) * δ) := by
        rw [← Real.rpow_natCast]
        exact (Real.rpow_mul (by positivity) _ _).symm
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ = 2 := by norm_num
  have hmpos : (0 : ℝ) < 𝓕.card := by exact_mod_cast hm
  have hhalf : (𝓕.card : ℝ) ^ 2 / 2 ≤ (𝓕.card : ℝ) ^ (2 - δ) := by
    have hid : (𝓕.card : ℝ) ^ (2 : ℝ) =
        (𝓕.card : ℝ) ^ (2 - δ) * (𝓕.card : ℝ) ^ δ := by
      rw [← Real.rpow_add hmpos]
      congr 1
      ring
    rw [Real.rpow_two] at hid
    have hp := Real.rpow_pos_of_pos hmpos (2 - δ)
    nlinarith
  exact (hedge.trans_le hhalf).le

/-- The affirmative answer to the third question in Problem 777. -/
def ThirdQuestion : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, ∀ 𝓕 : Finset (Finset (Fin n)),
      (𝓕.card : ℝ) ^ (2 - δ) < comparableEdges 𝓕 →
      (𝓕.card : ℝ) < (2 + ε) ^ ((n : ℝ) / 2)

theorem thirdQuestion_true : ThirdQuestion := by
  intro ε hε
  let b : ℝ := 2 + ε
  have hb2 : 2 < b := by dsimp [b]; linarith
  have hb0 : 0 < b := by linarith
  obtain ⟨t, δ, ht4, hδ, htwo, hbase₁, hbase₂⟩ := exists_power_parameters b hb2
  let x : ℝ := 2 / ((t : ℝ) * δ)
  let N : ℕ := ⌈x⌉₊
  have htpos : (0 : ℝ) < t := by positivity
  have htdpos : 0 < (t : ℝ) * δ := mul_pos htpos hδ
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hNlow : x ≤ (N : ℝ) := by
    dsimp [N]
    exact Nat.le_ceil x
  have hNhigh : (N : ℝ) < x + 1 := by
    dsimp [N]
    exact Nat.ceil_lt_add_one hxpos.le
  have hsmall : 2 / (t : ℝ) + δ < 1 := by
    have ht4R : (4 : ℝ) ≤ t := by exact_mod_cast ht4
    have h' : 2 / (t : ℝ) < 1 - δ := by
      rw [div_lt_iff₀ htpos]
      nlinarith
    linarith
  have hδN : δ * (N : ℝ) ≤ 1 := by
    have hmul := mul_lt_mul_of_pos_left hNhigh hδ
    dsimp [x] at hmul
    have hcalc : δ * (2 / ((t : ℝ) * δ) + 1) = 2 / (t : ℝ) + δ := by
      field_simp
    rw [hcalc] at hmul
    exact (hmul.trans hsmall).le
  have ht1 : 1 ≤ t := by omega
  have hδ₂ : 0 ≤ 1 - 2 * (t : ℝ) * δ := by linarith
  have hδ₁ : 0 ≤ (t : ℝ) * (1 - 2 * δ) := by
    have ht1R : (1 : ℝ) ≤ t := by exact_mod_cast ht1
    have : 2 * δ ≤ 2 * (t : ℝ) * δ := by nlinarith
    exact mul_nonneg htpos.le (by linarith)
  refine ⟨δ, hδ, fun n 𝓕 hbad ↦ ?_⟩
  by_contra hnot
  have hm : b ^ ((n : ℝ) / 2) ≤ (𝓕.card : ℝ) := le_of_not_gt hnot
  by_cases hn : n < N
  · have hs := small_dimension_power_bound hδ hδN hn 𝓕
    exact (not_lt_of_ge hs) hbad
  · have hNn : N ≤ n := le_of_not_gt hn
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hNn
    have hexp : (1 : ℝ) ≤ ((n : ℝ) / 2) * ((t : ℝ) * δ) := by
      have hxle : 2 / ((t : ℝ) * δ) ≤ (n : ℝ) := by
        exact hNlow.trans hnR
      rw [div_le_iff₀ htdpos] at hxle
      nlinarith
    have h2m : (2 : ℝ) ^ ((n : ℝ) / 2) ≤ (𝓕.card : ℝ) := by
      exact (Real.rpow_le_rpow (by norm_num) hb2.le (by positivity)).trans hm
    have habsorb : (2 : ℝ) ≤ (𝓕.card : ℝ) ^ ((t : ℝ) * δ) := by
      calc
        (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ (((n : ℝ) / 2) * ((t : ℝ) * δ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = ((2 : ℝ) ^ ((n : ℝ) / 2)) ^ ((t : ℝ) * δ) :=
          Real.rpow_mul (by norm_num) _ _
        _ ≤ (𝓕.card : ℝ) ^ ((t : ℝ) * δ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h2m
            (mul_nonneg htpos.le hδ.le)
    have hs := edge_power_saving_of_factors 𝓕 ht1 hb0 hδ₁ hδ₂
      hbase₁.le hbase₂.le hm habsorb
    exact (not_lt_of_ge hs) hbad

/-! ## Vanishing triangle density at the square-root threshold -/

def triangleMoments {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    Finset (Σ _B : Finset (Fin n),
      (Fin t → Finset (Fin n)) × (Fin t → Finset (Fin n))) :=
  𝓕.sigma fun B ↦
    (tuplesFrom (𝓕.filter fun A ↦ A ⊆ B) t).product
      (tuplesFrom (𝓕.filter fun C ↦ B ⊆ C) t)

@[simp] lemma mem_triangleMoments {n t : ℕ} {𝓕 : Finset (Finset (Fin n))}
    {q : Σ _B : Finset (Fin n),
      (Fin t → Finset (Fin n)) × (Fin t → Finset (Fin n))} :
    q ∈ triangleMoments 𝓕 t ↔
      q.1 ∈ 𝓕 ∧ (∀ i, q.2.1 i ∈ 𝓕 ∧ q.2.1 i ⊆ q.1) ∧
        (∀ i, q.2.2 i ∈ 𝓕 ∧ q.1 ⊆ q.2.2 i) := by
  simp [triangleMoments]

lemma card_triangleMoments {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (triangleMoments 𝓕 t).card =
      ∑ B ∈ 𝓕, ((𝓕.filter fun A ↦ A ⊆ B).card *
        (𝓕.filter fun C ↦ B ⊆ C).card) ^ t := by
  simp [triangleMoments, Finset.card_sigma, mul_pow]

lemma clique_has_oriented_chain {n : ℕ} {𝓕 : Finset (Finset (Fin n))}
    {s : Finset {A // A ∈ 𝓕}} (hs : (comparableGraph 𝓕).IsNClique 3 s) :
    ∃ A B C : {A // A ∈ 𝓕}, A.1 < B.1 ∧ B.1 < C.1 ∧ s = {A, B, C} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ :=
    (SimpleGraph.is3Clique_iff.mp hs)
  simp only [comparableGraph_adj] at hxy hxz hyz
  rcases hxy with hxy | hyx
  · rcases hyz with hyz | hzy
    · exact ⟨x, y, z, hxy, hyz, hs⟩
    · rcases hxz with hxz | hzx
      · exact ⟨x, z, y, hxz, hzy, by
          simpa [Finset.ext_iff, or_comm, or_left_comm, or_assoc] using hs⟩
      · exact ⟨z, x, y, hzx, hxy, by
          simpa [Finset.ext_iff, or_comm, or_left_comm, or_assoc] using hs⟩
  · rcases hyz with hyz | hzy
    · rcases hxz with hxz | hzx
      · exact ⟨y, x, z, hyx, hxz, by
          simpa [Finset.ext_iff, or_comm, or_left_comm, or_assoc] using hs⟩
      · exact ⟨y, z, x, hyz, hzx, by
          simpa [Finset.ext_iff, or_comm, or_left_comm, or_assoc] using hs⟩
    · exact ⟨z, y, x, hzy, hyx, by
        simpa [Finset.ext_iff, or_comm, or_left_comm, or_assoc] using hs⟩

noncomputable def triangleChainChoice {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (s : (comparableGraph 𝓕).cliqueFinset 3) :
    {A // A ∈ 𝓕} × {A // A ∈ 𝓕} × {A // A ∈ 𝓕} :=
  let h := clique_has_oriented_chain (SimpleGraph.mem_cliqueFinset_iff.mp s.2)
  (h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose)

lemma triangleChainChoice_spec {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (s : (comparableGraph 𝓕).cliqueFinset 3) :
    (triangleChainChoice 𝓕 s).1.1 < (triangleChainChoice 𝓕 s).2.1.1 ∧
      (triangleChainChoice 𝓕 s).2.1.1 < (triangleChainChoice 𝓕 s).2.2.1 ∧
      s.1 = {(triangleChainChoice 𝓕 s).1,
        (triangleChainChoice 𝓕 s).2.1, (triangleChainChoice 𝓕 s).2.2} := by
  dsimp [triangleChainChoice]
  exact (clique_has_oriented_chain
    (SimpleGraph.mem_cliqueFinset_iff.mp s.2)).choose_spec.choose_spec.choose_spec

lemma triangleChainChoice_injective {n : ℕ} (𝓕 : Finset (Finset (Fin n))) :
    Function.Injective (triangleChainChoice 𝓕) := by
  intro s s' h
  apply Subtype.ext
  have hs := (triangleChainChoice_spec 𝓕 s).2.2
  have hs' := (triangleChainChoice_spec 𝓕 s').2.2
  rw [hs, hs', h]

lemma cliqueFinset_le_triangleMoments_one {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) :
    ((comparableGraph 𝓕).cliqueFinset 3).card ≤ (triangleMoments 𝓕 1).card := by
  let f : (comparableGraph 𝓕).cliqueFinset 3 →
      (Σ _B : Finset (Fin n),
        (Fin 1 → Finset (Fin n)) × (Fin 1 → Finset (Fin n))) := fun s ↦
    ⟨(triangleChainChoice 𝓕 s).2.1.1,
      ((fun _ ↦ (triangleChainChoice 𝓕 s).1.1),
        (fun _ ↦ (triangleChainChoice 𝓕 s).2.2.1))⟩
  have hmap : Set.MapsTo f Set.univ (triangleMoments 𝓕 1 : Set _) := by
    intro s _
    change f s ∈ triangleMoments 𝓕 1
    rw [mem_triangleMoments]
    have hs := triangleChainChoice_spec 𝓕 s
    exact ⟨(triangleChainChoice 𝓕 s).2.1.2,
      (fun _ ↦ ⟨(triangleChainChoice 𝓕 s).1.2, hs.1.le⟩),
      (fun _ ↦ ⟨(triangleChainChoice 𝓕 s).2.2.2, hs.2.1.le⟩)⟩
  have hinj : Function.Injective f := by
    intro s s' h
    apply triangleChainChoice_injective 𝓕
    have hB : (triangleChainChoice 𝓕 s).2.1 =
        (triangleChainChoice 𝓕 s').2.1 := Subtype.ext (congrArg Sigma.fst h)
    have hp := congrArg Sigma.snd h
    have hA : (triangleChainChoice 𝓕 s).1 =
        (triangleChainChoice 𝓕 s').1 := by
      apply Subtype.ext
      exact congrFun (congrArg Prod.fst hp) 0
    have hC : (triangleChainChoice 𝓕 s).2.2 =
        (triangleChainChoice 𝓕 s').2.2 := by
      apply Subtype.ext
      exact congrFun (congrArg Prod.snd hp) 0
    exact Prod.ext hA (Prod.ext hB hC)
  let f' : (comparableGraph 𝓕).cliqueFinset 3 → (triangleMoments 𝓕 1) :=
    fun s ↦ ⟨f s, hmap (Set.mem_univ s)⟩
  have hf' : Function.Injective f' := by
    intro s s' h
    exact hinj (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f' hf'
  rw [Fintype.card_coe, Fintype.card_coe] at hc
  exact hc

def tupleOutside {n t : ℕ} (g : Fin t → Finset (Fin n)) : Finset (Fin n) :=
  tupleUnion fun i ↦ (Finset.univ : Finset (Fin n)) \ g i

def middleRegion {n t : ℕ} (f g : Fin t → Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)) \ (tupleUnion f ∪ tupleOutside g)

lemma union_disjoint_outside {n t : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    {q : Σ _B : Finset (Fin n),
      (Fin t → Finset (Fin n)) × (Fin t → Finset (Fin n))}
    (hq : q ∈ triangleMoments 𝓕 t) :
    Disjoint (tupleUnion q.2.1) (tupleOutside q.2.2) := by
  rw [Finset.disjoint_left]
  intro z hzU hzW
  rw [tupleUnion, Finset.mem_biUnion] at hzU
  rw [tupleOutside, tupleUnion, Finset.mem_biUnion] at hzW
  obtain ⟨i, -, hzi⟩ := hzU
  obtain ⟨j, -, hzj⟩ := hzW
  have hm := mem_triangleMoments.mp hq
  have hzB := (hm.2.1 i).2 hzi
  have hzC := (hm.2.2 j).2 hzB
  exact (Finset.mem_sdiff.mp hzj).2 hzC

lemma middleRegion_card_le {n t : ℕ}
    {𝓕 : Finset (Finset (Fin n))}
    {q : Σ _B : Finset (Fin n),
      (Fin t → Finset (Fin n)) × (Fin t → Finset (Fin n))}
    (hq : q ∈ triangleMoments 𝓕 t)
    (hU : ¬(tupleUnion q.2.1).card ≤ n / 3)
    (hW : ¬(tupleOutside q.2.2).card ≤ n / 3) :
    (middleRegion q.2.1 q.2.2).card ≤ n / 3 := by
  have hd := union_disjoint_outside hq
  have hsub : tupleUnion q.2.1 ∪ tupleOutside q.2.2 ⊆
      (Finset.univ : Finset (Fin n)) := Finset.subset_univ _
  rw [middleRegion, Finset.card_sdiff_of_subset hsub, Finset.card_univ,
    Fintype.card_fin, Finset.card_union_of_disjoint hd]
  omega

def triSmallU {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :=
  (triangleMoments 𝓕 t).filter fun q ↦ (tupleUnion q.2.1).card ≤ n / 3

def triNotU {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :=
  (triangleMoments 𝓕 t).filter fun q ↦ ¬(tupleUnion q.2.1).card ≤ n / 3

def triSmallW {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :=
  (triNotU 𝓕 t).filter fun q ↦ (tupleOutside q.2.2).card ≤ n / 3

def triSmallM {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :=
  (triNotU 𝓕 t).filter fun q ↦ ¬(tupleOutside q.2.2).card ≤ n / 3

lemma card_triangleMoments_partition {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (triangleMoments 𝓕 t).card =
      (triSmallU 𝓕 t).card + (triSmallW 𝓕 t).card + (triSmallM 𝓕 t).card := by
  have h₁ : (triangleMoments 𝓕 t).card =
      (triSmallU 𝓕 t).card + (triNotU 𝓕 t).card := by
    rw [triSmallU, triNotU, ← Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter_not (triangleMoments 𝓕 t) (triangleMoments 𝓕 t) _),
      Finset.filter_union_filter_not_eq]
  have h₂ : (triNotU 𝓕 t).card =
      (triSmallW 𝓕 t).card + (triSmallM 𝓕 t).card := by
    rw [triSmallW, triSmallM, ← Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter_not (triNotU 𝓕 t) (triNotU 𝓕 t) _),
      Finset.filter_union_filter_not_eq]
  omega

def triUCodes {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    Finset (Σ _U : Finset (Fin n),
      (Fin t → Finset (Fin n)) ×
        (Finset (Fin n) × (Fin t → Finset (Fin n)))) :=
  (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 3).sigma fun U ↦
    (tuplesFrom U.powerset t).product (𝓕.product (tuplesFrom 𝓕 t))

def toTriUCode {n t : ℕ} :
    (Σ _B : Finset (Fin n),
      (Fin t → Finset (Fin n)) × (Fin t → Finset (Fin n))) →
    (Σ _U : Finset (Fin n),
      (Fin t → Finset (Fin n)) ×
        (Finset (Fin n) × (Fin t → Finset (Fin n)))) :=
  fun q ↦ ⟨tupleUnion q.2.1, (q.2.1, (q.1, q.2.2))⟩

lemma card_triSmallU_le_codes {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (triSmallU 𝓕 t).card ≤ (triUCodes 𝓕 t).card := by
  apply Finset.card_le_card_of_injOn toTriUCode
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hm := mem_triangleMoments.mp hq'.1
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq'.2⟩, ?_⟩
    apply Finset.mem_product.mpr
    refine ⟨mem_tuplesFrom.mpr (fun i ↦
      Finset.mem_powerset.mpr (tuple_subset_union q.2.1 i)), ?_⟩
    exact Finset.mem_product.mpr
      ⟨hm.1, mem_tuplesFrom.mpr (fun i ↦ (hm.2.2 i).1)⟩
  · intro q _ q' _ h
    rcases q with ⟨B, f, g⟩
    rcases q' with ⟨B', f', g'⟩
    have hp : (f, (B, g)) = (f', (B', g')) := congrArg Sigma.snd h
    have hf : f = f' := congrArg Prod.fst hp
    have hBg : (B, g) = (B', g') := congrArg Prod.snd hp
    subst f'
    cases hBg
    rfl

lemma card_triUCodes_le {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (triUCodes 𝓕 t).card ≤
      2 ^ n * ((2 ^ (n / 3)) ^ t * 𝓕.card ^ (t + 1)) := by
  rw [triUCodes, Finset.card_sigma]
  calc
    (∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 3),
        ((tuplesFrom U.powerset t).product (𝓕.product (tuplesFrom 𝓕 t))).card) =
      ∑ U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 3),
        (2 ^ U.card) ^ t * 𝓕.card ^ (t + 1) := by
          apply Finset.sum_congr rfl
          intro U _
          simp [pow_succ']
    _ ≤ ∑ _U ∈ (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 3),
        (2 ^ (n / 3)) ^ t * 𝓕.card ^ (t + 1) := by
          apply Finset.sum_le_sum
          intro U hU
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
            (Nat.pow_le_pow_right (by omega) (Finset.mem_filter.mp hU).2) t)
    _ = (Finset.univ.filter fun U : Finset (Fin n) ↦ U.card ≤ n / 3).card *
        ((2 ^ (n / 3)) ^ t * 𝓕.card ^ (t + 1)) := by simp
    _ ≤ 2 ^ n * ((2 ^ (n / 3)) ^ t * 𝓕.card ^ (t + 1)) := by
      gcongr
      exact (Finset.card_filter_le _ _).trans_eq (by simp)

def complementTuple {n t : ℕ} (g : Fin t → Finset (Fin n)) :
    Fin t → Finset (Fin n) :=
  fun i ↦ (Finset.univ : Finset (Fin n)) \ g i

lemma complementTuple_injective {n t : ℕ} :
    Function.Injective (complementTuple (n := n) (t := t)) := by
  intro g g' h
  funext i
  have hi := congrFun h i
  ext z
  have hz := Finset.ext_iff.mp hi z
  simp only [complementTuple, Finset.mem_sdiff, Finset.mem_univ, true_and] at hz
  tauto

def triWCodes {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    Finset (Σ _W : Finset (Fin n),
      (Fin t → Finset (Fin n)) ×
        (Finset (Fin n) × (Fin t → Finset (Fin n)))) :=
  (Finset.univ.filter fun W : Finset (Fin n) ↦ W.card ≤ n / 3).sigma fun W ↦
    (tuplesFrom W.powerset t).product (𝓕.product (tuplesFrom 𝓕 t))

def toTriWCode {n t : ℕ} :
    (Σ _B : Finset (Fin n),
      (Fin t → Finset (Fin n)) × (Fin t → Finset (Fin n))) →
    (Σ _W : Finset (Fin n),
      (Fin t → Finset (Fin n)) ×
        (Finset (Fin n) × (Fin t → Finset (Fin n)))) :=
  fun q ↦ ⟨tupleOutside q.2.2, (complementTuple q.2.2, (q.1, q.2.1))⟩

lemma card_triSmallW_le_codes {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (triSmallW 𝓕 t).card ≤ (triWCodes 𝓕 t).card := by
  apply Finset.card_le_card_of_injOn toTriWCode
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hm := mem_triangleMoments.mp (Finset.mem_filter.mp hq'.1).1
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq'.2⟩, ?_⟩
    apply Finset.mem_product.mpr
    refine ⟨mem_tuplesFrom.mpr (fun i ↦ Finset.mem_powerset.mpr ?_), ?_⟩
    · exact tuple_subset_union (complementTuple q.2.2) i
    · exact Finset.mem_product.mpr
        ⟨hm.1, mem_tuplesFrom.mpr (fun i ↦ (hm.2.1 i).1)⟩
  · intro q _ q' _ h
    rcases q with ⟨B, f, g⟩
    rcases q' with ⟨B', f', g'⟩
    have hp : (complementTuple g, (B, f)) =
        (complementTuple g', (B', f')) := congrArg Sigma.snd h
    have hg : g = g' := complementTuple_injective (congrArg Prod.fst hp)
    have hBf : (B, f) = (B', f') := congrArg Prod.snd hp
    subst g'
    cases hBf
    rfl

lemma card_triWCodes_le {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (triWCodes 𝓕 t).card ≤
      2 ^ n * ((2 ^ (n / 3)) ^ t * 𝓕.card ^ (t + 1)) := by
  rw [triWCodes, Finset.card_sigma]
  calc
    (∑ W ∈ (Finset.univ.filter fun W : Finset (Fin n) ↦ W.card ≤ n / 3),
        ((tuplesFrom W.powerset t).product (𝓕.product (tuplesFrom 𝓕 t))).card) =
      ∑ W ∈ (Finset.univ.filter fun W : Finset (Fin n) ↦ W.card ≤ n / 3),
        (2 ^ W.card) ^ t * 𝓕.card ^ (t + 1) := by
          apply Finset.sum_congr rfl
          intro W _
          simp [pow_succ']
    _ ≤ ∑ _W ∈ (Finset.univ.filter fun W : Finset (Fin n) ↦ W.card ≤ n / 3),
        (2 ^ (n / 3)) ^ t * 𝓕.card ^ (t + 1) := by
          apply Finset.sum_le_sum
          intro W hW
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left
            (Nat.pow_le_pow_right (by omega) (Finset.mem_filter.mp hW).2) t)
    _ = (Finset.univ.filter fun W : Finset (Fin n) ↦ W.card ≤ n / 3).card *
        ((2 ^ (n / 3)) ^ t * 𝓕.card ^ (t + 1)) := by simp
    _ ≤ 2 ^ n * ((2 ^ (n / 3)) ^ t * 𝓕.card ^ (t + 1)) := by
      gcongr
      exact (Finset.card_filter_le _ _).trans_eq (by simp)

def triMCodes {n : ℕ} (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    Finset (Σ _p : (Fin t → Finset (Fin n)) × (Fin t → Finset (Fin n)),
      Finset (Fin n)) :=
  (((tuplesFrom 𝓕 t).product (tuplesFrom 𝓕 t)).filter fun p ↦
    (middleRegion p.1 p.2).card ≤ n / 3).sigma fun p ↦
      (middleRegion p.1 p.2).powerset

def toTriMCode {n t : ℕ} :
    (Σ _B : Finset (Fin n),
      (Fin t → Finset (Fin n)) × (Fin t → Finset (Fin n))) →
    (Σ _p : (Fin t → Finset (Fin n)) × (Fin t → Finset (Fin n)),
      Finset (Fin n)) :=
  fun q ↦ ⟨q.2, q.1 \ tupleUnion q.2.1⟩

lemma card_triSmallM_le_codes {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (triSmallM 𝓕 t).card ≤ (triMCodes 𝓕 t).card := by
  apply Finset.card_le_card_of_injOn toTriMCode
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hnotU := Finset.mem_filter.mp hq'.1
    have hm := mem_triangleMoments.mp hnotU.1
    apply Finset.mem_sigma.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨mem_tuplesFrom.mpr (fun i ↦ (hm.2.1 i).1),
          mem_tuplesFrom.mpr (fun i ↦ (hm.2.2 i).1)⟩, ?_⟩
      exact middleRegion_card_le hnotU.1 hnotU.2 hq'.2
    · apply Finset.mem_powerset.mpr
      intro z hz
      have hz' := Finset.mem_sdiff.mp hz
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.mem_union]
      push Not
      refine ⟨hz'.2, ?_⟩
      intro hzW
      rw [tupleOutside, tupleUnion, Finset.mem_biUnion] at hzW
      obtain ⟨j, -, hzj⟩ := hzW
      exact (Finset.mem_sdiff.mp hzj).2 ((hm.2.2 j).2 hz'.1)
  · intro q hq q' hq' h
    rcases q with ⟨B, f, g⟩
    rcases q' with ⟨B', f', g'⟩
    have hp : (f, g) = (f', g') := congrArg Sigma.fst h
    cases hp
    have hd : B \ tupleUnion f = B' \ tupleUnion f := congrArg Sigma.snd h
    have hm := mem_triangleMoments.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    have hm' := mem_triangleMoments.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq').1).1
    have hu : tupleUnion f ⊆ B := tupleUnion_subset (fun i ↦ (hm.2.1 i).2)
    have hu' : tupleUnion f ⊆ B' := tupleUnion_subset (fun i ↦ (hm'.2.1 i).2)
    have hB : B = B' := by
      ext z
      by_cases hz : z ∈ tupleUnion f
      · exact iff_of_true (hu hz) (hu' hz)
      · have hdz := Finset.ext_iff.mp hd z
        simpa [hz] using hdz
    subst B'
    rfl

lemma card_triMCodes_le {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (triMCodes 𝓕 t).card ≤ 𝓕.card ^ (2 * t) * 2 ^ (n / 3) := by
  rw [triMCodes, Finset.card_sigma]
  calc
    (∑ p ∈ ((tuplesFrom 𝓕 t).product (tuplesFrom 𝓕 t)).filter fun p ↦
        (middleRegion p.1 p.2).card ≤ n / 3,
      ((middleRegion p.1 p.2).powerset).card) ≤
      ∑ _p ∈ ((tuplesFrom 𝓕 t).product (tuplesFrom 𝓕 t)).filter fun p ↦
        (middleRegion p.1 p.2).card ≤ n / 3, 2 ^ (n / 3) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.card_powerset]
          exact Nat.pow_le_pow_right (by omega) (Finset.mem_filter.mp hp).2
    _ = (((tuplesFrom 𝓕 t).product (tuplesFrom 𝓕 t)).filter fun p ↦
        (middleRegion p.1 p.2).card ≤ n / 3).card * 2 ^ (n / 3) := by simp
    _ ≤ 𝓕.card ^ (2 * t) * 2 ^ (n / 3) := by
      gcongr
      calc
        (((tuplesFrom 𝓕 t).product (tuplesFrom 𝓕 t)).filter fun p ↦
            (middleRegion p.1 p.2).card ≤ n / 3).card ≤
            ((tuplesFrom 𝓕 t).product (tuplesFrom 𝓕 t)).card := Finset.card_filter_le _ _
        _ = 𝓕.card ^ (2 * t) := by
          simp [pow_mul, pow_two, mul_pow]

/-- The three-region encoding bound for the `t`-th moment of two-sided
containment degrees. -/
lemma card_triangleMoments_le {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (t : ℕ) :
    (triangleMoments 𝓕 t).card ≤
      2 * (2 ^ n * ((2 ^ (n / 3)) ^ t * 𝓕.card ^ (t + 1))) +
        𝓕.card ^ (2 * t) * 2 ^ (n / 3) := by
  rw [card_triangleMoments_partition]
  have hU := (card_triSmallU_le_codes 𝓕 t).trans (card_triUCodes_le 𝓕 t)
  have hW := (card_triSmallW_le_codes 𝓕 t).trans (card_triWCodes_le 𝓕 t)
  have hM := (card_triSmallM_le_codes 𝓕 t).trans (card_triMCodes_le 𝓕 t)
  omega

/-- Sum, over possible middle sets, of the product of the lower and upper
non-strict containment degrees. -/
def chainMiddleCount {n : ℕ} (𝓕 : Finset (Finset (Fin n))) : ℕ :=
  ∑ B ∈ 𝓕, (𝓕.filter fun A ↦ A ⊆ B).card *
    (𝓕.filter fun C ↦ B ⊆ C).card

lemma card_triangleMoments_one {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) :
    (triangleMoments 𝓕 1).card = chainMiddleCount 𝓕 := by
  rw [card_triangleMoments]
  simp [chainMiddleCount]

/-- Power-mean converts the first two-sided chain count to its `t`-th
moment. -/
lemma chainMiddleCount_moment {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    {t : ℕ} (ht : 1 ≤ t) :
    chainMiddleCount 𝓕 ^ t ≤
      𝓕.card ^ (t - 1) * (triangleMoments 𝓕 t).card := by
  have hj := pow_sum_le_card_mul_sum_pow
    (s := 𝓕)
    (f := fun B ↦ (((𝓕.filter fun A ↦ A ⊆ B).card *
      (𝓕.filter fun C ↦ B ⊆ C).card : ℕ) : ℝ))
    (fun _ _ ↦ by positivity) (t - 1)
  have ht' : t - 1 + 1 = t := by omega
  rw [ht'] at hj
  norm_num [Nat.cast_mul] at hj
  have hcard := congrArg (fun z : ℕ ↦ (z : ℝ)) (card_triangleMoments 𝓕 t)
  norm_num [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul] at hcard
  rw [← hcard] at hj
  have hj' : ((chainMiddleCount 𝓕 ^ t : ℕ) : ℝ) ≤
      ((𝓕.card ^ (t - 1) * (triangleMoments 𝓕 t).card : ℕ) : ℝ) := by
    simpa [chainMiddleCount, Nat.cast_sum, Nat.cast_pow, Nat.cast_mul] using hj
  exact_mod_cast hj'

lemma cliqueFinset_le_chainMiddleCount {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) :
    ((comparableGraph 𝓕).cliqueFinset 3).card ≤ chainMiddleCount 𝓕 := by
  exact (cliqueFinset_le_triangleMoments_one 𝓕).trans_eq
    (card_triangleMoments_one 𝓕)

/-- A completely finite quantitative form of vanishing triangle density.
The exponents are chosen so that both summands save an exponential factor
once `|𝓕| ≥ 2^(n/2)`. -/
lemma clique_pow_twelve_le {n : ℕ} (𝓕 : Finset (Finset (Fin n))) :
    ((comparableGraph 𝓕).cliqueFinset 3).card ^ 12 ≤
      2 * (𝓕.card ^ 24 * (2 ^ n * (2 ^ (n / 3)) ^ 12)) +
        𝓕.card ^ 35 * 2 ^ (n / 3) := by
  calc
    ((comparableGraph 𝓕).cliqueFinset 3).card ^ 12 ≤
        chainMiddleCount 𝓕 ^ 12 :=
      Nat.pow_le_pow_left (cliqueFinset_le_chainMiddleCount 𝓕) 12
    _ ≤ 𝓕.card ^ 11 * (triangleMoments 𝓕 12).card := by
      simpa using chainMiddleCount_moment 𝓕 (t := 12) (by omega)
    _ ≤ 𝓕.card ^ 11 *
        (2 * (2 ^ n * ((2 ^ (n / 3)) ^ 12 * 𝓕.card ^ 13)) +
          𝓕.card ^ 24 * 2 ^ (n / 3)) :=
      Nat.mul_le_mul_left _ (by simpa using card_triangleMoments_le 𝓕 12)
    _ = 2 * (𝓕.card ^ 24 * (2 ^ n * (2 ^ (n / 3)) ^ 12)) +
        𝓕.card ^ 35 * 2 ^ (n / 3) := by ring

/-- The exact yes/no resolution of all three questions. -/
def Resolution : Prop := FirstQuestion ∧ ¬ SecondQuestion ∧ ThirdQuestion

/-- The `k = 2` sparse-clique statement of Alon--Das--Glebov--Sudakov,
in exactly the quantitative form needed for the first question. -/
def ComparableTrianglesVanish : Prop :=
  ∀ γ : ℝ, 0 < γ →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ 𝓕 : Finset (Finset (Fin n)),
      (2 : ℝ) ^ ((n : ℝ) / 2) ≤ 𝓕.card →
      ((comparableGraph 𝓕).cliqueFinset 3).card < γ * (𝓕.card : ℝ) ^ 3

/-- The real square of `2^(n/2)` is `2^n`. -/
lemma rpow_half_sq (n : ℕ) :
    ((2 : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ n := by
  calc
    ((2 : ℝ) ^ ((n : ℝ) / 2)) ^ (2 : ℕ) =
        ((2 : ℝ) ^ ((n : ℝ) / 2)) ^ (2 : ℝ) :=
      (Real.rpow_natCast ((2 : ℝ) ^ ((n : ℝ) / 2)) 2).symm
    _ = (2 : ℝ) ^ (((n : ℝ) / 2) * 2) :=
      (Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2) ((n : ℝ) / 2) 2).symm
    _ = (2 : ℝ) ^ (n : ℝ) := by congr 1 <;> ring
    _ = (2 : ℝ) ^ (n : ℕ) := Real.rpow_natCast 2 n

lemma nat_third_cast_le (n : ℕ) : ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by
  have h : (n / 3) * 3 ≤ n := Nat.div_mul_le_self n 3
  have h' : (((n / 3) * 3 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  norm_num [Nat.cast_mul] at h'
  linarith

/-- The finite twelfth-moment bound, normalized by `|𝓕|^36`. -/
lemma clique_pow_twelve_normalized {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (hlarge : (2 : ℝ) ^ ((n : ℝ) / 2) ≤ 𝓕.card) :
    (((comparableGraph 𝓕).cliqueFinset 3).card : ℝ) ^ 12 ≤
      (𝓕.card : ℝ) ^ 36 *
        (2 * ((1 / 2 : ℝ) ^ n) + ((2 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n) := by
  have hnat := clique_pow_twelve_le 𝓕
  have hnatR : ((((comparableGraph 𝓕).cliqueFinset 3).card ^ 12 : ℕ) : ℝ) ≤
      ((2 * (𝓕.card ^ 24 * (2 ^ n * (2 ^ (n / 3)) ^ 12)) +
        𝓕.card ^ 35 * 2 ^ (n / 3) : ℕ) : ℝ) := by exact_mod_cast hnat
  norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at hnatR
  have hm0 : (0 : ℝ) < 𝓕.card := by
    have hq : 0 < (2 : ℝ) ^ ((n : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact hq.trans_le hlarge
  have htwo : (2 : ℝ) ^ n ≤ (𝓕.card : ℝ) ^ 2 := by
    rw [← rpow_half_sq n]
    gcongr
  have ha12 : ((2 : ℝ) ^ (n / 3 : ℕ)) ^ 12 ≤ ((2 : ℝ) ^ n) ^ 4 := by
    norm_num [← pow_mul]
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2)
      (by omega : (n / 3) * 12 ≤ n * 4)
  have hP6 : ((2 : ℝ) ^ n) ^ 6 ≤ (𝓕.card : ℝ) ^ 12 := by
    calc
      ((2 : ℝ) ^ n) ^ 6 ≤ ((𝓕.card : ℝ) ^ 2) ^ 6 := by gcongr
      _ = (𝓕.card : ℝ) ^ 12 := by ring
  have hhalfprod : (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) = 1 := by
    rw [← mul_pow]
    norm_num
  have hidentity : ((2 : ℝ) ^ n) * ((2 : ℝ) ^ n) ^ 4 =
      ((2 : ℝ) ^ n) ^ 6 * ((1 / 2 : ℝ) ^ n) := by
    calc
      (2 : ℝ) ^ n * ((2 : ℝ) ^ n) ^ 4 = ((2 : ℝ) ^ n) ^ 5 := by ring
      _ = ((2 : ℝ) ^ n) ^ 5 *
          ((2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n)) := by
        rw [hhalfprod]
        ring
      _ = ((2 : ℝ) ^ n) ^ 6 * ((1 / 2 : ℝ) ^ n) := by
        rw [pow_succ]
        ring
  have hfirst :
      2 * ((𝓕.card : ℝ) ^ 24 *
        ((2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 3 : ℕ)) ^ 12)) ≤
        (𝓕.card : ℝ) ^ 36 * (2 * ((1 / 2 : ℝ) ^ n)) := by
    calc
      2 * ((𝓕.card : ℝ) ^ 24 *
          ((2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 3 : ℕ)) ^ 12)) ≤
          2 * ((𝓕.card : ℝ) ^ 24 *
            ((2 : ℝ) ^ n * ((2 : ℝ) ^ n) ^ 4)) := by gcongr
      _ = 2 * ((𝓕.card : ℝ) ^ 24 *
          (((2 : ℝ) ^ n) ^ 6 * ((1 / 2 : ℝ) ^ n))) := by rw [hidentity]
      _ ≤ 2 * ((𝓕.card : ℝ) ^ 24 *
          ((𝓕.card : ℝ) ^ 12 * ((1 / 2 : ℝ) ^ n))) := by gcongr
      _ = (𝓕.card : ℝ) ^ 36 * (2 * ((1 / 2 : ℝ) ^ n)) := by ring
  have hthird : (2 : ℝ) ^ (n / 3 : ℕ) ≤
      (2 : ℝ) ^ ((n : ℝ) / 2) *
        ((2 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n := by
    calc
      (2 : ℝ) ^ (n / 3 : ℕ) = (2 : ℝ) ^ (((n / 3 : ℕ) : ℝ)) :=
        (Real.rpow_natCast 2 (n / 3)).symm
      _ ≤ (2 : ℝ) ^ ((n : ℝ) / 3) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (nat_third_cast_le n)
      _ = (2 : ℝ) ^ ((n : ℝ) / 2) *
          ((2 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num)]
        congr 1
        ring
  have hmiddle : (𝓕.card : ℝ) ^ 35 * (2 : ℝ) ^ (n / 3 : ℕ) ≤
      (𝓕.card : ℝ) ^ 36 * ((2 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n := by
    calc
      (𝓕.card : ℝ) ^ 35 * (2 : ℝ) ^ (n / 3 : ℕ) ≤
          (𝓕.card : ℝ) ^ 35 *
            ((2 : ℝ) ^ ((n : ℝ) / 2) *
              ((2 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n) := by gcongr
      _ ≤ (𝓕.card : ℝ) ^ 35 *
            ((𝓕.card : ℝ) * ((2 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n) := by gcongr
      _ = (𝓕.card : ℝ) ^ 36 *
          ((2 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n := by ring
  calc
    (((comparableGraph 𝓕).cliqueFinset 3).card : ℝ) ^ 12 ≤
        2 * ((𝓕.card : ℝ) ^ 24 *
          ((2 : ℝ) ^ n * ((2 : ℝ) ^ (n / 3 : ℕ)) ^ 12)) +
          (𝓕.card : ℝ) ^ 35 * (2 : ℝ) ^ (n / 3 : ℕ) := hnatR
    _ ≤ (𝓕.card : ℝ) ^ 36 * (2 * ((1 / 2 : ℝ) ^ n)) +
          (𝓕.card : ℝ) ^ 36 *
            ((2 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n := add_le_add hfirst hmiddle
    _ = _ := by ring

lemma triangleCoefficient_eventually {γ : ℝ} (hγ : 0 < γ) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      2 * ((1 / 2 : ℝ) ^ n) +
        ((2 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n < γ ^ 12 := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-(1 : ℝ) / 6) :=
    Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-(1 : ℝ) / 6) < 1 := by
    rw [← Real.rpow_zero 2]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hhalf := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hr := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hsum : Filter.Tendsto
      (fun n : ℕ ↦ 2 * ((1 / 2 : ℝ) ^ n) +
        ((2 : ℝ) ^ (-(1 : ℝ) / 6)) ^ n)
      Filter.atTop (nhds 0) := by
    convert (hhalf.const_mul 2).add hr using 1 <;> simp
  exact Filter.eventually_atTop.mp
    (hsum.eventually_lt tendsto_const_nhds (by positivity))

/-- Comparable triangles have density tending to zero at and above the
square-root threshold.  This is the set-system input needed by triangle
removal. -/
theorem comparableTrianglesVanish_true : ComparableTrianglesVanish := by
  intro γ hγ
  obtain ⟨n₀, hn₀⟩ := triangleCoefficient_eventually hγ
  refine ⟨n₀, fun n hn 𝓕 hlarge ↦ ?_⟩
  have hnorm := clique_pow_twelve_normalized 𝓕 hlarge
  have hcoeff := hn₀ n hn
  have hm0 : (0 : ℝ) < 𝓕.card := by
    exact (Real.rpow_pos_of_pos (by norm_num) _).trans_le hlarge
  have hstrict : (((comparableGraph 𝓕).cliqueFinset 3).card : ℝ) ^ 12 <
      (𝓕.card : ℝ) ^ 36 * γ ^ 12 := by
    exact hnorm.trans_lt (mul_lt_mul_of_pos_left hcoeff (by positivity))
  have heq : (𝓕.card : ℝ) ^ 36 * γ ^ 12 =
      (γ * (𝓕.card : ℝ) ^ 3) ^ 12 := by ring
  rw [heq] at hstrict
  by_contra hnot
  have hle : γ * (𝓕.card : ℝ) ^ 3 ≤
      (((comparableGraph 𝓕).cliqueFinset 3).card : ℝ) := le_of_not_gt hnot
  have hp : (γ * (𝓕.card : ℝ) ^ 3) ^ 12 ≤
      (((comparableGraph 𝓕).cliqueFinset 3).card : ℝ) ^ 12 := by gcongr
  exact (not_lt_of_ge hp) hstrict

/-- Mantel's inequality in a form independent of the parity of the vertex
count. -/
lemma four_mul_edges_le_sq_of_triangleFree
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) :
    4 * G.edgeFinset.card ≤ Fintype.card V ^ 2 := by
  have h := hG.card_edgeFinset_le (r := 2)
  simp only [Nat.reduceSub, Nat.mul_one, Nat.reduceMul,
    Nat.choose_eq_zero_of_lt (Nat.mod_lt _ (by omega : 0 < 2))] at h
  calc
    4 * G.edgeFinset.card ≤ 4 * ((Fintype.card V ^ 2 - (Fintype.card V % 2) ^ 2) / 4) :=
      Nat.mul_le_mul_left 4 h
    _ ≤ Fintype.card V ^ 2 - (Fintype.card V % 2) ^ 2 := Nat.mul_div_le _ _
    _ ≤ Fintype.card V ^ 2 := Nat.sub_le _ _

/-- The graph-theoretic deduction of the first answer from the sparse-triangle
theorem.  The only deep set-system input is isolated in
`ComparableTrianglesVanish`; triangle removal and Mantel are supplied by
Mathlib. -/
theorem firstQuestion_of_comparableTrianglesVanish
    (htri : ComparableTrianglesVanish) : FirstQuestion := by
  intro ε hε
  by_cases hε₂ : 2 ≤ ε
  · refine ⟨0, fun n _ 𝓕 hm ↦ ?_⟩
    have hcard : 𝓕.card = 0 := by
      have hpow : 0 < (2 : ℝ) ^ ((n : ℝ) / 2) := by positivity
      have : (𝓕.card : ℝ) ≤ 0 := hm.trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) hpow.le)
      exact_mod_cast (Nat.eq_zero_of_le_zero (by exact_mod_cast this))
    have hF : 𝓕 = ∅ := Finset.card_eq_zero.mp hcard
    have hedge := (comparableGraph 𝓕).card_edgeFinset_le_card_choose_two
    have hedge0 : comparableEdges 𝓕 = 0 := by
      rw [comparableEdges]
      apply Nat.eq_zero_of_le_zero
      simpa [Fintype.card_coe, hcard] using hedge
    simp [hedge0]
  · have hεlt : ε < 2 := lt_of_not_ge hε₂
    let a : ℝ := 2 - ε
    have ha : 0 < a := by dsimp [a]; linarith
    have ha2 : a < 2 := by dsimp [a]; linarith
    let β : ℝ := (a⁻¹ ^ 2 - (1 / 4 : ℝ)) / 2
    have hβ : 0 < β := by
      dsimp [β]
      have hainv : (1 / 4 : ℝ) < a⁻¹ ^ 2 := by
        rw [inv_pow]
        rw [inv_eq_one_div]
        rw [lt_div_iff₀ (sq_pos_of_pos ha)]
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos (sub_pos.mpr ha2)]
      linarith
    have hcoef : (1 / 4 + β) * a ^ 2 < 1 := by
      have ha0 : a ≠ 0 := ne_of_gt ha
      dsimp [β]
      field_simp
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos (sub_pos.mpr ha2)]
    have hrb : 0 < SimpleGraph.triangleRemovalBound β :=
      SimpleGraph.triangleRemovalBound_pos hβ
    obtain ⟨n₀, hn₀⟩ := htri (SimpleGraph.triangleRemovalBound β) hrb
    refine ⟨n₀, fun n hn 𝓕 hm ↦ ?_⟩
    let q : ℝ := (2 : ℝ) ^ ((n : ℝ) / 2)
    have hq : 0 < q := by dsimp [q]; positivity
    have hqsq : q ^ 2 = (2 : ℝ) ^ n := rpow_half_sq n
    by_cases hsmall : (𝓕.card : ℝ) < q
    · have hedge := (comparableGraph 𝓕).card_edgeFinset_le_card_choose_two
      have hedge' : (comparableEdges 𝓕 : ℝ) ≤ (𝓕.card : ℝ) ^ 2 / 2 := by
        have hediv : (comparableGraph 𝓕).edgeFinset.card ≤ 𝓕.card * (𝓕.card - 1) / 2 := by
          simpa [Fintype.card_coe, Nat.choose_two_right] using hedge
        have he2 : (comparableGraph 𝓕).edgeFinset.card * 2 ≤ 𝓕.card ^ 2 := by
          calc
            (comparableGraph 𝓕).edgeFinset.card * 2 ≤ 𝓕.card * (𝓕.card - 1) :=
              (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hediv
            _ ≤ 𝓕.card * 𝓕.card := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
            _ = 𝓕.card ^ 2 := by ring
        rw [comparableEdges]
        have he2' : ((comparableGraph 𝓕).edgeFinset.card : ℝ) * 2 ≤
            (𝓕.card : ℝ) ^ 2 := by exact_mod_cast he2
        linarith
      have : (comparableEdges 𝓕 : ℝ) < (2 : ℝ) ^ n := by
        rw [← hqsq]
        nlinarith [sq_pos_of_pos hq, sq_nonneg ((𝓕.card : ℝ) - q)]
      exact_mod_cast this
    · have hlarge : q ≤ (𝓕.card : ℝ) := le_of_not_gt hsmall
      have ht := hn₀ n hn 𝓕 hlarge
      have ht' : ((comparableGraph 𝓕).cliqueFinset 3).card <
          SimpleGraph.triangleRemovalBound β *
            (Fintype.card {A // A ∈ 𝓕} : ℝ) ^ 3 := by
        simpa using ht
      obtain ⟨G', hG'le, _inst, hdiff, hfree⟩ := SimpleGraph.triangle_removal ht'
      have hmantel := four_mul_edges_le_sq_of_triangleFree hfree
      have hmantel' : 4 * (G'.edgeFinset.card : ℝ) ≤ (𝓕.card : ℝ) ^ 2 := by
        have hmantel0 : 4 * G'.edgeFinset.card ≤ 𝓕.card ^ 2 := by
          simpa only [Fintype.card_coe] using hmantel
        exact_mod_cast hmantel0
      have hdiff' : (comparableEdges 𝓕 : ℝ) - (G'.edgeFinset.card : ℝ) <
          β * (𝓕.card : ℝ) ^ 2 := by
        simpa [comparableEdges] using hdiff
      have hedgecoef : (comparableEdges 𝓕 : ℝ) < (1 / 4 + β) * (𝓕.card : ℝ) ^ 2 := by
        nlinarith
      have hm' : (𝓕.card : ℝ) ≤ a * q := by simpa [a, q] using hm
      have hm_sq : (𝓕.card : ℝ) ^ 2 ≤ a ^ 2 * q ^ 2 := by
        nlinarith [sq_nonneg ((𝓕.card : ℝ) - a * q)]
      have : (comparableEdges 𝓕 : ℝ) < (2 : ℝ) ^ n := by
        rw [← hqsq]
        nlinarith [mul_nonneg (by positivity : 0 ≤ (1 / 4 + β))
          (sub_nonneg.mpr hm_sq), sq_pos_of_pos hq]
      exact_mod_cast this

/-- The first Daykin--Erdős question has an affirmative answer. -/
theorem firstQuestion_true : FirstQuestion :=
  firstQuestion_of_comparableTrianglesVanish comparableTrianglesVanish_true

/-- Complete resolution of Erdős Problem 777: yes, no, yes. -/
theorem erdos777 : Resolution :=
  ⟨firstQuestion_true, secondQuestion_false, thirdQuestion_true⟩

#print axioms erdos777

end

end Erdos777
