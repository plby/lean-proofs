/-
Vendored from danlyng/Econlib (Apache-2.0), retrieved 2026-08-16.
Upstream path: Econlib source: CubicalSperner.lean
-/
/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import ErdosProblems.Erdos909.External.Econlib.FreudenthalTriangulation
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic

/-!
# Cubical Sperner's lemma

Sperner's lemma for the Freudenthal triangulation of the grid `[0,p]^n`. Under a Sperner-proper
coloring, the number of fully colored simplices is odd; in particular at least one exists. The
fully-colored count and the parity of rainbow boundary faces are tracked through the induction on
dimension.

## Main definitions

* `ValidSimplex` — a `KuhnSimplex` satisfying the validity predicate, as a subtype.
* `childEmbed`, `childColoring` — the embedding and coloring used to descend to the boundary face.

## Main statements

* `cubicalSperner` — the number of fully colored simplices is odd.
* `weakerCubicalSperner` — at least one fully colored simplex exists.
* `vertex_close` — vertices of a valid simplex differ by at most `1` in each coordinate.

## Tags

sperner's lemma, freudenthal triangulation, rainbow face, parity, double counting
-/

@[expose] public section

open KuhnSimplex

/-! ### Valid simplices as a subtype -/

/-- A valid Kuhn simplex: `base(j) + 1 ≤ p` for all `j`. -/
abbrev ValidSimplex (n p : ℕ) := { S : KuhnSimplex n p // S.isValid }

noncomputable instance instFintypeValidSimplex (n p : ℕ) :
    Fintype (ValidSimplex n p) :=
  Fintype.subtype (Finset.univ.filter KuhnSimplex.isValid) (by simp)

/-! ### Rainbow face counting -/

section RainbowFaces

variable {n p : ℕ} (SC : SpernerColoring n p)

/-- A rainbow face is a pair (S, k) where S is a valid simplex and face k is rainbow. It's a
boundary face if faceAdj returns none. -/
def isRainbowBoundaryFace (Sk : ValidSimplex n p × Fin (n + 1)) : Prop :=
  Sk.1.val.isRainbowFace Sk.1.property SC.color Sk.2 ∧ Sk.1.val.faceAdj Sk.2 = none

/-- A rainbow interior face is a pair (S, k) with rainbow face k and faceAdj giving some S'. -/
def isRainbowInteriorFace (Sk : ValidSimplex n p × Fin (n + 1)) : Prop :=
  Sk.1.val.isRainbowFace Sk.1.property SC.color Sk.2 ∧ Sk.1.val.faceAdj Sk.2 ≠ none

open Classical in
/-- The number of rainbow faces of a valid simplex S (counting face indices). -/
noncomputable def rainbowFaceCount (S : ValidSimplex n p) : ℕ :=
  Finset.card (Finset.univ.filter (fun k : Fin (n + 1) =>
    decide (S.val.isRainbowFace S.property SC.color k) = true))

open Classical in
/-- Fully colored ↔ odd number of rainbow faces. -/
lemma rainbowFaceCount_odd_iff (S : ValidSimplex n p) :
    Odd (rainbowFaceCount SC S) ↔ S.val.fullyColored S.property SC.color := by
  unfold rainbowFaceCount
  constructor
  · -- Odd rainbow count → fully colored
    intro hodd
    by_contra hnfc
    have h := S.val.not_fullyColored_rainbow_zero_or_two S.property SC.color hnfc
    rcases h with h0 | ⟨k₁, k₂, hne, hk₁, hk₂, huniq⟩
    · -- 0 rainbow faces: count = 0, not odd
      have : (Finset.univ.filter (fun k : Fin (n + 1) =>
          decide (S.val.isRainbowFace S.property SC.color k) = true)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _; simp [h0 k]
      rw [this] at hodd; exact (Nat.not_odd_zero) hodd
    · -- 2 rainbow faces: count = 2, not odd
      have : (Finset.univ.filter (fun k : Fin (n + 1) =>
          decide (S.val.isRainbowFace S.property SC.color k) = true)).card = 2 := by
        rw [Finset.card_eq_two]
        exact ⟨k₁, k₂, hne, by
          ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_insert, Finset.mem_singleton, decide_eq_true_eq]
          exact ⟨fun hk => huniq k hk, fun h => h.elim (· ▸ hk₁) (· ▸ hk₂)⟩⟩
      rw [this] at hodd; exact (by decide : ¬ Odd 2) hodd
  · -- Fully colored → odd rainbow count (= 1)
    intro hfc
    obtain ⟨k₀, hk₀, huniq⟩ := S.val.fullyColored_rainbow_count S.property SC.color hfc
    have : (Finset.univ.filter (fun k : Fin (n + 1) =>
        decide (S.val.isRainbowFace S.property SC.color k) = true)).card = 1 := by
      rw [Finset.card_eq_one]
      exact ⟨k₀, by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, decide_eq_true_eq]
        exact ⟨fun hk => huniq k hk, fun h => h ▸ hk₀⟩⟩
    rw [this]; exact odd_one

end RainbowFaces

/-! ### Induction step: Boundary faces reduce to lower dimension -/

section Induction

/-- Embedding of the n-dimensional grid into the (n+1)-dimensional grid boundary where the last
coordinate equals p. -/
def childEmbed (n p : ℕ) (v : Fin n → Fin (p + 1)) : Fin (n + 1) → Fin (p + 1) :=
  fun i => if h : i.val < n then v ⟨i.val, h⟩ else Fin.last p

/-- Restrict a Sperner coloring on dimension n+1 to the "last coordinate = p" face, producing a
Sperner coloring on dimension n. -/
noncomputable def childColoring {n p : ℕ}
    (SC : SpernerColoring (n + 1) p) : SpernerColoring n p where
  color v :=
    let c := SC.color (childEmbed n p v)
    ⟨c.val, by
      have h_last : (childEmbed n p v) ⟨n, by omega⟩ = Fin.last p := by
        simp [childEmbed]
      have h_le := (SC.proper (childEmbed n p v) ⟨n, by omega⟩).2 h_last
      omega⟩
  proper v k := by
    constructor
    · intro hv0 heq
      have hcv : (SC.color (childEmbed n p v)).val = k.val := by
        have := congr_arg Fin.val heq; simpa using this
      have h_embed : (childEmbed n p v) k.castSucc = 0 := by
        simp [childEmbed, hv0]
      have h_ne := (SC.proper (childEmbed n p v) k.castSucc).1 h_embed
      apply h_ne; ext; simp only [Fin.castSucc]; exact hcv
    · intro hvp
      have h_embed : (childEmbed n p v) k.castSucc = Fin.last p := by
        simp [childEmbed, hvp]
      exact (SC.proper (childEmbed n p v) k.castSucc).2 h_embed

end Induction

/-! ### Main theorems -/

/-- #{a | Odd f(a)} has the same parity as Σ f(a). Each even f(a) contributes 0 mod 2; each odd
contributes 1. -/
private lemma odd_card_odd_iff_odd_sum {α : Type*} [Fintype α]
    (f : α → ℕ) :
    Odd (Finset.univ.filter (fun a => Odd (f a))).card ↔ Odd (∑ a : α, f a) := by
  rw [← ZMod.natCast_eq_one_iff_odd, ← ZMod.natCast_eq_one_iff_odd, Nat.cast_sum]
  suffices h : ∀ x : α, (f x : ZMod 2) = if Odd (f x) then 1 else 0 by
    simp_rw [h, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  intro x
  rcases Nat.even_or_odd (f x) with he | ho
  · rw [if_neg (by rwa [Nat.not_odd_iff_even]), ZMod.natCast_eq_zero_iff_even.mpr he]
  · rw [if_pos ho, ZMod.natCast_eq_one_iff_odd.mpr ho]

/-! ### Parity lemma: Interior rainbow faces pair up -/

open Classical in
/-- The set of all rainbow face pairs (S, k) for valid simplices S. -/
private noncomputable def allRainbowPairs (n p : ℕ) (SC : SpernerColoring n p) :
    Finset (ValidSimplex n p × Fin (n + 1)) :=
  Finset.univ.filter (fun Sk : ValidSimplex n p × Fin (n + 1) =>
    decide (Sk.1.val.isRainbowFace Sk.1.property SC.color Sk.2) = true)

open Classical in
/-- The total rainbow face count equals the cardinality of rainbow face pairs. This is a standard
reindexing: Σ_S card(filter_k) = card(Σ_S filter_k). -/
private lemma sum_rainbowFaceCount_eq_card (n p : ℕ) (SC : SpernerColoring n p) :
    ∑ S : ValidSimplex n p, rainbowFaceCount SC S =
    (allRainbowPairs n p SC).card := by
  -- Reindexing: Σ_S #{k | rainbow(S,k)} = #{(S,k) | rainbow(S,k)}.
  -- Fibers over Prod.fst partition the product filter.
  unfold allRainbowPairs rainbowFaceCount
  set P := fun (Sk : ValidSimplex n p × Fin (n + 1)) =>
    decide (Sk.1.val.isRainbowFace Sk.1.property SC.color Sk.2) = true
  -- Each summand = #{(S,k) ∈ univ.filter P | fst = S}
  have hsummand : ∀ S : ValidSimplex n p,
    (Finset.univ.filter (fun k => decide (S.val.isRainbowFace S.property SC.color k) = true)).card =
    ((Finset.univ.filter P).filter (fun Sk => Sk.1 = S)).card := by
      intro S
      apply Finset.card_nbij' (fun k => (S, k)) (fun Sk => Sk.2)
      · -- MapsTo forward: k ∈ filter → (S,k) ∈ filter P ∩ {fst = S}
        intro k hk
        rw [Finset.mem_coe] at hk
        have hk' := (Finset.mem_filter.mp hk).2
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩, rfl⟩
      · -- MapsTo backward: (S',k) ∈ filter P with S'=S → k ∈ filter
        intro ⟨S', k⟩ hSk
        have hSk' := Finset.mem_filter.mp hSk
        have hSk1 := (Finset.mem_filter.mp hSk'.1).2
        have hSk2 : S' = S := hSk'.2
        subst hSk2
        rw [Finset.mem_coe]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSk1⟩
      · -- LeftInvOn
        intro k _; rfl
      · -- RightInvOn
        intro ⟨S', k⟩ hSk
        have hSk' := Finset.mem_filter.mp hSk
        have hSk2 : S' = S := hSk'.2
        subst hSk2; rfl
  simp_rw [hsummand]
  -- Now Σ_S #{Sk ∈ filter P univ | Sk.1 = S} = #(filter P univ)
  -- This is sum_card_fiberwise_eq_card_filter with g = Prod.fst, applied to all of univ
  have key := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ.filter P) Finset.univ
    (fun Sk : ValidSimplex n p × Fin (n + 1) => Sk.1)
  simp only [Finset.mem_univ, Finset.filter_true_of_mem (fun _ _ => trivial)] at key
  exact key

/-- The boundary rainbow face pairs: (S, k) where face k is rainbow and on the boundary. -/
private noncomputable def boundaryRainbowPairs (n p : ℕ) (SC : SpernerColoring n p) :
    Finset (ValidSimplex n p × Fin (n + 1)) :=
  (allRainbowPairs n p SC).filter (fun Sk => Sk.1.val.faceAdj Sk.2 = none)

/-- The interior rainbow face pairs: (S, k) where face k is rainbow and interior. -/
private noncomputable def interiorRainbowPairs (n p : ℕ) (SC : SpernerColoring n p) :
    Finset (ValidSimplex n p × Fin (n + 1)) :=
  (allRainbowPairs n p SC).filter (fun Sk => Sk.1.val.faceAdj Sk.2 ≠ none)

/-- Interior rainbow face pairs have even cardinality. The face involution pairs them up: (S, k) ↦
(S', k') via faceAdj. -/
private lemma even_card_of_fpf_invol {α : Type*}
    {s : Finset α} (f : α → α) (hf_mem : ∀ a ∈ s, f a ∈ s)
    (hf_inv : ∀ a ∈ s, f (f a) = a) (hf_ne : ∀ a ∈ s, f a ≠ a) :
    Even s.card := by
  have h : ∑ a ∈ s, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => f a)
      (fun a _ => show (1 : ZMod 2) + 1 = 0 by decide)
      (fun a ha _ => hf_ne a ha)
      (fun a ha => hf_mem a ha)
      (fun a ha => hf_inv a ha)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rwa [← ZMod.natCast_eq_zero_iff_even]

open Classical in
private lemma interior_rainbow_even (n p : ℕ) (SC : SpernerColoring n p) :
    Even (interiorRainbowPairs n p SC).card := by
  -- Define the face involution on ValidSimplex × Fin (n+1):
  -- For (⟨S, hv⟩, k) with faceAdj k = some S', map to (⟨S', hv'⟩, k')
  -- where (k', hk', _) := faceAdj_shared_vertices.
  -- When faceAdj k = none, map to self (these aren't in the interior set anyway).
  let invol : ValidSimplex n p × Fin (n + 1) → ValidSimplex n p × Fin (n + 1) :=
    fun ⟨⟨S, hv⟩, k⟩ =>
      match h : S.faceAdj k with
      | none => (⟨S, hv⟩, k)
      | some S' =>
        have hv' : S'.isValid := S.faceAdj_preserves_valid hv k h
        let k' := (S.faceAdj_shared_vertices hv k h hv').choose
        (⟨S', hv'⟩, k')
  -- Helper: characterize invol's behavior when faceAdj k = some S'
  have invol_some : ∀ (S : KuhnSimplex n p) (hv : S.isValid) (k : Fin (n + 1))
      (S' : KuhnSimplex n p) (hS' : S.faceAdj k = some S'),
      ∃ k', invol (⟨S, hv⟩, k) = (⟨S', S.faceAdj_preserves_valid hv k hS'⟩, k') ∧
        S'.faceAdj k' = some S ∧
        ∀ i : Fin (n + 1), i ≠ k →
          ∃ j : Fin (n + 1), j ≠ k' ∧
            S.vertex hv i = S'.vertex (S.faceAdj_preserves_valid hv k hS') j := by
    intro S hv k S' hS'
    simp only [invol]
    split
    next heq =>
      -- faceAdj k = none contradicts hS'
      exact absurd (hS' ▸ heq) (Option.some_ne_none _)
    next S'' heq =>
      -- faceAdj k = some S'', and we know faceAdj k = some S', so S'' = S'
      have hS''_eq : S'' = S' := Option.some_inj.mp (heq ▸ hS')
      subst hS''_eq
      set hv' := S.faceAdj_preserves_valid hv k heq
      set spec := S.faceAdj_shared_vertices hv k heq hv'
      exact ⟨spec.choose, by congr 1, spec.choose_spec⟩
  apply even_card_of_fpf_invol invol
  · -- invol maps interiorRainbowPairs to itself
    intro ⟨⟨S, hv⟩, k⟩ hmem
    simp only [interiorRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, ne_eq] at hmem
    obtain ⟨hrainbow, hinterior⟩ := hmem
    obtain ⟨S', hS'⟩ := Option.ne_none_iff_exists'.mp hinterior
    obtain ⟨k', hinvol_eq, hk'_adj, hk'_verts⟩ := invol_some S hv k S' hS'
    rw [hinvol_eq]
    simp only [interiorRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, ne_eq]
    constructor
    · -- S' is rainbow at face k': shared vertices carry the same colors
      rw [decide_eq_true_eq]
      intro color
      have hrainbow' := decide_eq_true_eq.mp hrainbow
      obtain ⟨i, hi_ne, hi_color⟩ := hrainbow' color
      obtain ⟨j, hj_ne, hj_eq⟩ := hk'_verts i hi_ne
      exact ⟨j, hj_ne, by rw [← hj_eq]; exact hi_color⟩
    · -- S'.faceAdj k' ≠ none: S'.faceAdj k' = some S
      rw [hk'_adj]; exact Option.some_ne_none S
  · -- invol is an involution on interiorRainbowPairs
    intro ⟨⟨S, hv⟩, k⟩ hmem
    simp only [interiorRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, ne_eq] at hmem
    obtain ⟨_, hinterior⟩ := hmem
    obtain ⟨S', hS'⟩ := Option.ne_none_iff_exists'.mp hinterior
    obtain ⟨k', hinvol_eq, hk'_adj, hk'_verts⟩ := invol_some S hv k S' hS'
    -- invol(⟨S,hv⟩, k) = (⟨S', hv'⟩, k'), so invol(invol(⟨S,hv⟩, k)) = invol(⟨S', hv'⟩, k')
    rw [hinvol_eq]
    -- Now apply invol_some to S' at k' with S'.faceAdj k' = some S
    set hv' := S.faceAdj_preserves_valid hv k hS'
    obtain ⟨k'', hinvol_eq', hk''_adj, _⟩ := invol_some S' hv' k' S hk'_adj
    rw [hinvol_eq']
    -- Now: (⟨S, S'.faceAdj_preserves_valid hv' k' hk'_adj⟩, k'') = (⟨S, hv⟩, k)
    -- First component: S matches, and hv is proof-irrelevant in the subtype
    -- Second component: k'' = k, which follows from faceAdj injectivity
    -- The first component is easy (proof irrelevance for isValid)
    -- congr 1 solves the subtype component (proof irrelevance), leaving k'' = k
    -- Both k and k'' satisfy S.faceAdj _ = some S', so k'' = k by injectivity
    congr 1
    exact S.faceAdj_injective k'' k hk''_adj hS'
  · -- invol has no fixed points on interiorRainbowPairs
    intro ⟨⟨S, hv⟩, k⟩ hmem
    simp only [interiorRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, ne_eq] at hmem
    obtain ⟨_, hinterior⟩ := hmem
    obtain ⟨S', hS'⟩ := Option.ne_none_iff_exists'.mp hinterior
    obtain ⟨k', hinvol_eq, _, _⟩ := invol_some S hv k S' hS'
    -- S' ≠ S by faceAdj_ne
    have hne : S' ≠ S := S.faceAdj_ne k hS'
    rw [hinvol_eq]
    intro heq
    exact hne (congr_arg Subtype.val (Prod.mk.inj heq).1)

/-- The parity of total rainbow faces equals the parity of boundary rainbow faces. -/
private lemma total_parity_eq_boundary (n p : ℕ) (SC : SpernerColoring n p) :
    Odd (allRainbowPairs n p SC).card ↔
    Odd (boundaryRainbowPairs n p SC).card := by
  -- allRainbow = boundary ∪ interior (disjoint partition)
  have hdisj : Disjoint (boundaryRainbowPairs n p SC) (interiorRainbowPairs n p SC) :=
    Finset.disjoint_filter.mpr fun _ _ h => not_not.mpr h
  have hunion : allRainbowPairs n p SC =
      boundaryRainbowPairs n p SC ∪ interiorRainbowPairs n p SC := by
    unfold boundaryRainbowPairs interiorRainbowPairs
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro h; exact (_root_.em _).elim (fun hb => Or.inl ⟨h, hb⟩) (fun hb => Or.inr ⟨h, hb⟩)
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  rw [hunion, Finset.card_union_of_disjoint hdisj]
  obtain ⟨m, hm⟩ := interior_rainbow_even n p SC
  constructor
  · intro ⟨k, hk⟩; exact ⟨k - m, by omega⟩
  · intro ⟨k, hk⟩; exact ⟨k + m, by omega⟩

/-- In dimension 0, the sum of rainbow face counts is odd. There is exactly one simplex (trivially
valid) and its single face is rainbow. -/
private lemma base_case_zero (p : ℕ) (SC : SpernerColoring 0 p) (_hp : 0 < p) :
    Odd (∑ S : ValidSimplex 0 p, rainbowFaceCount SC S) := by
  -- In dimension 0, Fin 0 is empty, so KuhnSimplex 0 p has exactly one element
  -- (unique base : Fin 0 → Fin (p+1) and unique perm : Equiv.Perm (Fin 0)).
  -- isValid is vacuously true. isRainbowFace asks ∀ color : Fin 0, which is vacuous.
  -- So rainbowFaceCount = 1 (the single face k=0 is rainbow), and the sum = 1 = odd.
  -- The unique simplex
  have hUniq : ∀ (S : KuhnSimplex 0 p), S = ⟨Fin.elim0, Equiv.refl _⟩ := by
    intro S; cases S; congr
    · exact funext (fun i => Fin.elim0 i)
    · exact Equiv.ext (fun i => Fin.elim0 i)
  -- Every simplex is valid (vacuously)
  have hValid : ∀ (S : KuhnSimplex 0 p), S.isValid := by
    intro S j; exact Fin.elim0 j
  -- There is exactly one valid simplex
  have hCard : Fintype.card (ValidSimplex 0 p) = 1 := by
    rw [← Finset.card_univ, Finset.card_eq_one]
    use ⟨⟨Fin.elim0, Equiv.refl _⟩, hValid _⟩
    ext ⟨S, hv⟩
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subtype.ext (hUniq S)
  -- Rainbow face count is 1 for any valid simplex (the only face k=0 is vacuously rainbow)
  have hCount : ∀ (S : ValidSimplex 0 p), rainbowFaceCount SC S = 1 := by
    intro ⟨S, hv⟩
    unfold rainbowFaceCount
    rw [Finset.card_eq_one]
    use ⟨0, by omega⟩
    ext ⟨k, hk⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      decide_eq_true_eq]
    constructor
    · intro _; ext; omega
    · intro heq
      have : k = 0 := by have := congr_arg Fin.val heq; simpa using this
      subst this; intro c; exact Fin.elim0 c
  simp only [hCount]
  rw [Finset.sum_const, Finset.card_univ, hCard, smul_eq_mul, mul_one]
  exact odd_one

-- Key insight: boundary faces NOT on x_n = p have zero rainbow faces.
-- On x_j = 0: color j is forbidden by Sperner condition 1 → not rainbow.
-- On x_j = p for j < n: all colors ≤ j < n, so color n is missing → not rainbow.

/-- A boundary rainbow face in dimension n+1 must be a bottom face (k=0) where perm(0) = ⟨n, ...⟩
(the last coordinate). All other boundary faces cannot be rainbow due to Sperner conditions. -/
private lemma boundary_rainbow_on_last_coord {n p : ℕ} (SC : SpernerColoring (n + 1) p)
    (S : ValidSimplex (n + 1) p) (k : Fin (n + 2))
    (hrainbow : S.val.isRainbowFace S.property SC.color k)
    (hboundary : S.val.faceAdj k = none) :
    -- The boundary face lies on x_n = p
    k.val = 0 ∧ S.val.perm ⟨0, by omega⟩ = ⟨n, by omega⟩ ∧
    ∀ i : Fin (n + 2), i ≠ k → (S.val.vertex S.property i ⟨n, by omega⟩).val = p := by
  -- Case-split faceAdj to determine which boundary
  have hn : n + 1 ≠ 0 := by omega
  unfold KuhnSimplex.faceAdj at hboundary
  simp only [hn, ↓reduceDIte] at hboundary
  split_ifs at hboundary with hk0 hb hkn hb
  · -- k = 0 (bottom): boundary when base(perm(0))+1 ≥ p
    -- First prove perm(0) = ⟨n, _⟩
    have hperm_n : S.val.perm ⟨0, by omega⟩ = ⟨n, by omega⟩ := by
      by_contra hperm_ne
      have hperm_lt : (S.val.perm ⟨0, by omega⟩).val < n := by
        have h1 := (S.val.perm ⟨0, by omega⟩).isLt
        have h2 : (S.val.perm ⟨0, by omega⟩).val ≠ n := fun h => hperm_ne (Fin.ext h)
        omega
      set j := S.val.perm ⟨0, by omega⟩
      obtain ⟨i, hi_ne, hi_color⟩ := hrainbow ⟨n, by omega⟩
      have hi_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi_ne (Fin.ext (by omega)))
      have hsymm : (S.val.perm.symm j).val = 0 := by rw [S.val.perm.symm_apply_apply]
      have hvert_last : S.val.vertex S.property i j = Fin.last p := by
        ext; simp only [KuhnSimplex.vertex, KuhnSimplex.vertexVal, Fin.val_last]
        rw [hsymm, if_pos hi_pos]; have := S.property j; omega
      have hle := (SC.proper (S.val.vertex S.property i) j).2 hvert_last
      have hcn : (SC.color (S.val.vertex S.property i)).val = n := by
        have := congr_arg Fin.val hi_color; simp only [Fin.castSucc] at this; exact this
      omega
    refine ⟨hk0, hperm_n, ?_⟩
    -- All face vertices have coord ⟨n, _⟩ = p
    intro i hi
    have hi_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext (by omega)))
    -- perm⁻¹(⟨n,_⟩) = perm⁻¹(perm(0)) = 0 < i
    have hsymm : (S.val.perm.symm ⟨n, by omega⟩).val = 0 := by
      rw [show (⟨n, by omega⟩ : Fin (n + 1)) = S.val.perm ⟨0, by omega⟩ from hperm_n.symm]
      rw [S.val.perm.symm_apply_apply]
    change S.val.vertexVal i ⟨n, by omega⟩ = p
    unfold KuhnSimplex.vertexVal; rw [hsymm, if_pos hi_pos]
    have := S.property ⟨n, by omega⟩
    rw [show S.val.base ⟨n, by omega⟩ = S.val.base (S.val.perm ⟨0, by omega⟩) from by rw [hperm_n]]
    have := S.property (S.val.perm ⟨0, by omega⟩)
    omega
  · -- k = n+1 (top): base(perm(n)) = 0 → not rainbow
    exfalso
    -- hb : base(perm(⟨n+1-1, _⟩)) = 0, which is base(perm(⟨n, _⟩)) = 0
    have hb' : (S.val.base (S.val.perm ⟨n, by omega⟩)).val = 0 := hb
    set j := S.val.perm ⟨n, by omega⟩
    obtain ⟨i, hi_ne, hi_color⟩ := hrainbow j
    have hi_le : i.val ≤ n := by have := i.isLt; simp [Fin.ext_iff] at hi_ne; omega
    have hvert0 : S.val.vertex S.property i j = 0 := by
      ext; simp only [KuhnSimplex.vertex, KuhnSimplex.vertexVal, Fin.val_zero]
      have hsymm : (S.val.perm.symm j).val = n := by
        change (S.val.perm.symm (S.val.perm ⟨n, _⟩)).val = n; rw [S.val.perm.symm_apply_apply]
      rw [hsymm, if_neg (by omega : ¬(n < i.val))]; exact hb'
    exact (SC.proper (S.val.vertex S.property i) j).1 hvert0 hi_color

-- Helper: perm(0) = n implies σ⁻¹(j) > 0 for j < n
private lemma perm_symm_pos_of_lt {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    (hσ0 : σ ⟨0, by omega⟩ = ⟨n, by omega⟩) {j : Fin (n + 1)} (hj : j.val < n) :
    0 < (σ.symm j).val := by
  by_contra h
  have h0 : (σ.symm j).val = 0 := by omega
  have := σ.apply_symm_apply j
  rw [show σ.symm j = ⟨0, by omega⟩ from Fin.ext h0] at this
  have := congr_arg Fin.val this; simp at this
  have := congr_arg Fin.val hσ0; simp at this
  omega

-- Helper: perm(j+1) < n when perm(0) = n
private lemma perm_succ_lt {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))}
    (hσ0 : σ ⟨0, by omega⟩ = ⟨n, by omega⟩) (j : Fin n) :
    (σ ⟨j.val + 1, by omega⟩).val < n := by
  have hlt := (σ ⟨j.val + 1, by omega⟩).isLt
  by_contra h
  have heq : (σ ⟨j.val + 1, by omega⟩).val = n := by omega
  have h0 := congr_arg Fin.val hσ0; simp only [Fin.zero_eta] at h0
  have := σ.injective (Fin.ext (heq.trans h0.symm))
  simp [Fin.ext_iff] at this

-- Permutation projection: given σ with σ(0) = n, project to Perm (Fin n)
private def permProject {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ0 : σ ⟨0, by omega⟩ = ⟨n, by omega⟩) : Equiv.Perm (Fin n) where
  toFun j := ⟨(σ ⟨j.val + 1, by omega⟩).val, perm_succ_lt hσ0 j⟩
  invFun j := ⟨(σ.symm ⟨j.val, by omega⟩).val - 1, by
    have := (σ.symm ⟨j.val, by omega⟩).isLt
    have := perm_symm_pos_of_lt hσ0 (show (⟨j.val, by omega⟩ : Fin (n + 1)).val < n from j.isLt)
    omega⟩
  left_inv j := by
    ext; simp only
    -- Goal: (σ.symm ⟨(σ ⟨j+1, _⟩).val, _⟩).val - 1 = j.val
    -- ⟨(σ ⟨j+1, _⟩).val, _⟩ = σ ⟨j+1, _⟩ as Fin (n+1)
    have : (⟨(σ ⟨j.val + 1, by omega⟩).val, by omega⟩ : Fin (n + 1)) =
        σ ⟨j.val + 1, by omega⟩ := rfl
    rw [this, σ.symm_apply_apply]; simp
  right_inv j := by
    ext; simp only
    have hpos := perm_symm_pos_of_lt hσ0
      (show (⟨j.val, by omega⟩ : Fin (n + 1)).val < n from j.isLt)
    -- Goal: (σ ⟨(σ.symm ⟨j, _⟩).val - 1 + 1, _⟩).val = j.val
    have h1 : (⟨(σ.symm ⟨j.val, by omega⟩).val - 1 + 1, by omega⟩ : Fin (n + 1)) =
        σ.symm ⟨j.val, by omega⟩ := Fin.ext (by simp; omega)
    rw [h1]; simp [σ.apply_symm_apply]

-- Permutation lifting: given σ' : Perm (Fin n), produce σ with σ(0) = n
private def permLift {n : ℕ} (σ' : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun j :=
    if hj : j.val = 0 then ⟨n, by omega⟩
    else ⟨(σ' ⟨j.val - 1, by omega⟩).val, by have := (σ' ⟨j.val - 1, by omega⟩).isLt; omega⟩
  invFun j :=
    if hj : j.val = n then ⟨0, by omega⟩
    else ⟨(σ'.symm ⟨j.val, by omega⟩).val + 1, by
      have := (σ'.symm ⟨j.val, by omega⟩).isLt; omega⟩
  left_inv j := by
    ext
    simp only []
    by_cases hj : j.val = 0
    · simp [hj]
    · have hne : (σ' ⟨j.val - 1, by omega⟩).val ≠ n := by
        have := (σ' ⟨j.val - 1, by omega⟩).isLt; omega
      simp [hj, hne, σ'.symm_apply_apply]; omega
  right_inv j := by
    ext
    simp only []
    by_cases hj : j.val = n
    · simp [hj]
    · have hne : (σ'.symm ⟨j.val, by omega⟩).val + 1 ≠ 0 := by omega
      simp [hj, show (σ'.symm ⟨j.val, by omega⟩).val + 1 - 1 =
        (σ'.symm ⟨j.val, by omega⟩).val from by omega, σ'.apply_symm_apply]

private lemma permLift_zero {n : ℕ} (σ' : Equiv.Perm (Fin n)) :
    (permLift σ') ⟨0, by omega⟩ = ⟨n, by omega⟩ := by
  simp [permLift]

private lemma permProject_permLift {n : ℕ} (σ' : Equiv.Perm (Fin n)) :
    permProject (permLift σ') (permLift_zero σ') = σ' := by
  ext ⟨j, hj⟩; simp [permProject, permLift]

private lemma permLift_permProject {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ0 : σ ⟨0, by omega⟩ = ⟨n, by omega⟩) :
    permLift (permProject σ hσ0) = σ := by
  ext ⟨j, hj⟩
  simp only [permLift, permProject]
  by_cases hj0 : j = 0
  · simp only [hj0]; exact (congr_arg Fin.val hσ0).symm
  · simp [hj0, show j - 1 + 1 = j from by omega]

private lemma permProject_symm_val {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (hσ0 : σ ⟨0, by omega⟩ = ⟨n, by omega⟩) (j : Fin n) :
    ((permProject σ hσ0).symm j).val = (σ.symm ⟨j.val, by omega⟩).val - 1 := by
  -- permProject.invFun is defined as exactly this
  rfl

-- Project an (n+1)-dim Kuhn simplex with perm(0) = n down to n dimensions.
private def projectSimplex {n p : ℕ} (S : KuhnSimplex (n + 1) p)
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩) : KuhnSimplex n p where
  base j := S.base ⟨j.val, by omega⟩
  perm := permProject S.perm hperm0

-- Lift an n-dim Kuhn simplex to (n+1) dimensions with base(n) = p-1, perm(0) = n.
private def liftSimplex {n p : ℕ} (hp : 0 < p) (S' : KuhnSimplex n p) :
    KuhnSimplex (n + 1) p where
  base j := if h : j.val < n then S'.base ⟨j.val, h⟩ else ⟨p - 1, by omega⟩
  perm := permLift S'.perm

private lemma liftSimplex_perm_zero {n p : ℕ} (hp : 0 < p) (S' : KuhnSimplex n p) :
    (liftSimplex hp S').perm ⟨0, by omega⟩ = ⟨n, by omega⟩ :=
  permLift_zero S'.perm

private lemma projectSimplex_liftSimplex {n p : ℕ} (hp : 0 < p) (S' : KuhnSimplex n p) :
    projectSimplex (liftSimplex hp S') (liftSimplex_perm_zero hp S') = S' := by
  cases S' with | mk b σ =>
  simp only [projectSimplex, liftSimplex, KuhnSimplex.mk.injEq]
  refine ⟨?_, permProject_permLift σ⟩
  ext ⟨j, hj⟩; simp [show j < n from hj]

private lemma liftSimplex_projectSimplex {n p : ℕ} (hp : 0 < p) (S : KuhnSimplex (n + 1) p)
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩)
    (hbase_n : (S.base ⟨n, by omega⟩).val = p - 1) :
    liftSimplex hp (projectSimplex S hperm0) = S := by
  cases S with | mk b σ =>
  simp only [projectSimplex, liftSimplex, KuhnSimplex.mk.injEq]
  refine ⟨?_, permLift_permProject σ hperm0⟩
  ext ⟨j, hj⟩
  simp only
  by_cases hjn : j < n
  · simp [hjn]
  · have hjn' : j = n := by omega
    simp only [hjn', Nat.lt_irrefl, dite_false]
    exact hbase_n.symm

-- projectSimplex preserves validity
private lemma projectSimplex_valid {n p : ℕ} (S : KuhnSimplex (n + 1) p) (hv : S.isValid)
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩) :
    (projectSimplex S hperm0).isValid :=
  fun j => hv ⟨j.val, by omega⟩

-- liftSimplex preserves validity
private lemma liftSimplex_valid {n p : ℕ} (hp : 0 < p) (S' : KuhnSimplex n p) (hv : S'.isValid) :
    (liftSimplex hp S').isValid := by
  intro ⟨j, hj⟩
  simp only [liftSimplex]
  by_cases hjn : j < n
  · simp only [hjn]; exact hv ⟨j, hjn⟩
  · simp [show ¬(j < n) from hjn]; omega

-- Vertex correspondence: vertex (i+1) of S at coord j equals vertex i of projectSimplex S
private lemma projectSimplex_vertex_eq {n p : ℕ} (S : KuhnSimplex (n + 1) p) (hv : S.isValid)
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩)
    (i : Fin (n + 2)) (j : Fin n) :
    S.vertex hv i ⟨j.val, by omega⟩ =
    (projectSimplex S hperm0).vertex (projectSimplex_valid S hv hperm0)
      ⟨i.val - 1, by omega⟩ j := by
  simp only [KuhnSimplex.vertex, KuhnSimplex.vertexVal, projectSimplex]
  ext; simp only
  congr 1
  -- Need: (S.perm.symm ⟨j, _⟩).val < i ↔ (permProject ..).symm j).val < i - 1
  have hsymm := permProject_symm_val S.perm hperm0 j
  have hpos : 0 < (S.perm.symm ⟨j.val, by omega⟩).val :=
    perm_symm_pos_of_lt hperm0 j.isLt
  -- The projected perm.symm j has value = (S.perm.symm ⟨j, _⟩).val - 1
  -- So: projected < i-1 ↔ S.perm.symm < i (since both positive)
  have hiff : (S.perm.symm ⟨j.val, by omega⟩).val < i.val ↔
      ((permProject S.perm hperm0).symm j).val < i.val - 1 := by
    constructor <;> intro h <;> omega
  by_cases hleft : (S.perm.symm ⟨j.val, by omega⟩).val < i.val
  · have hright := hiff.mp hleft
    simp only [if_pos hleft]
    have hright' :
        ((projectSimplex S hperm0).perm.symm j).val <
          (⟨i.val - 1, by omega⟩ : Fin (n + 1)).val := hright
    exact (if_pos hright').symm
  · have hright : ¬ ((permProject S.perm hperm0).symm j).val < i.val - 1 :=
      fun h => hleft (hiff.mpr h)
    simp only [if_neg hleft]
    have hright' : ¬
        ((projectSimplex S hperm0).perm.symm j).val <
          (⟨i.val - 1, by omega⟩ : Fin (n + 1)).val := hright
    exact (if_neg hright').symm

-- childEmbed of the projected vertex equals the original vertex
private lemma childEmbed_projectSimplex_vertex {n p : ℕ} (S : KuhnSimplex (n + 1) p)
    (hv : S.isValid) (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩)
    (i : Fin (n + 2))
    (hcoord_n : (S.vertex hv i ⟨n, by omega⟩).val = p) :
    childEmbed n p ((projectSimplex S hperm0).vertex (projectSimplex_valid S hv hperm0)
      ⟨i.val - 1, by omega⟩) = S.vertex hv i := by
  ext ⟨c, hc⟩
  simp only [childEmbed]
  by_cases hcn : c < n
  · simp only [hcn]
    have := projectSimplex_vertex_eq S hv hperm0 i ⟨c, hcn⟩
    simp only [vertex, Fin.mk.injEq, ↓reduceDIte] at this ⊢
    exact this.symm
  · have hcn' : c = n := by omega
    simp only [hcn', Nat.lt_irrefl, dite_false, Fin.val_last]
    exact hcoord_n.symm

-- The key base(n) = p-1 fact for boundary simplices
private lemma boundary_base_n_eq {n p : ℕ} (S : KuhnSimplex (n + 1) p) (hv : S.isValid)
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩)
    (hboundary : S.faceAdj ⟨0, by omega⟩ = none) :
    (S.base ⟨n, by omega⟩).val = p - 1 := by
  -- faceAdj at 0 = none means base(perm(0)) + 1 ≥ p
  unfold KuhnSimplex.faceAdj at hboundary
  simp only [show n + 1 ≠ 0 from by omega, dite_false] at hboundary
  split_ifs at hboundary with hk0 hb
  · -- k = 0 case: hb says base(perm(0)) + 1 ≥ p
    have hperm0_val : (S.perm ⟨0, by omega⟩) = ⟨n, by omega⟩ := hperm0
    rw [hperm0_val] at hb
    have hvalid := hv ⟨n, by omega⟩
    omega
  · simp at hk0

-- Key coloring lemma: vertex (k+1) of liftSimplex S' = childEmbed (S'.vertex k)
-- This implies SC.color(liftedVertex(k+1)) relates to childColoring(S'.vertex k).
private lemma liftSimplex_vertex_childEmbed {n p : ℕ} (hp : 0 < p) (S' : KuhnSimplex n p)
    (hv' : S'.isValid) (k : Fin (n + 1)) :
    (liftSimplex hp S').vertex (liftSimplex_valid hp S' hv') ⟨k.val + 1, by
      have := k.isLt; omega⟩ =
    childEmbed n p (S'.vertex hv' k) := by
  -- Direct element-wise proof
  ext ⟨c, hc⟩
  simp only [childEmbed]
  by_cases hcn : c < n
  · -- c < n: vertex values match via base and permLift correspondence
    simp only [hcn, dite_true]
    -- Both sides have the same underlying nat value
    simp only [KuhnSimplex.vertex, KuhnSimplex.vertexVal, liftSimplex, Fin.val_mk, hcn, dite_true]
    -- base parts match trivially. If-condition parts match by permLift.symm correspondence.
    have h_pl : ((permLift S'.perm).symm ⟨c, by omega⟩).val =
        (S'.perm.symm ⟨c, hcn⟩).val + 1 := by
      simp [permLift, show c ≠ n from by omega]
    congr 1
    have hiff : ((permLift S'.perm).symm ⟨c, by omega⟩).val < k.val + 1 ↔
        (S'.perm.symm ⟨c, hcn⟩).val < k.val := by
      rw [h_pl]
      omega
    by_cases hleft : ((permLift S'.perm).symm ⟨c, by omega⟩).val < k.val + 1
    · have hright := hiff.mp hleft
      simp only [if_pos hright]
      have hleft' :
          ((liftSimplex hp S').perm.symm ⟨c, hc⟩).val <
            (⟨k.val + 1, by omega⟩ : Fin (n + 2)).val := hleft
      exact if_pos hleft'
    · have hright : ¬ (S'.perm.symm ⟨c, hcn⟩).val < k.val :=
        fun h => hleft (hiff.mpr h)
      simp only [if_neg hright]
      have hleft' : ¬
          ((liftSimplex hp S').perm.symm ⟨c, hc⟩).val <
            (⟨k.val + 1, by omega⟩ : Fin (n + 2)).val := hleft
      exact if_neg hleft'
  · -- c = n: liftSimplex vertex at n = p = Fin.last p
    have hcn' : c = n := by omega
    simp only [hcn', Nat.lt_irrefl, dite_false, KuhnSimplex.vertex, KuhnSimplex.vertexVal,
      liftSimplex, Fin.val_last, Fin.val_mk]
    -- base(n) = p-1, perm.symm(n) = 0 < k+1, so value = p-1+1 = p
    have h_symm : ((permLift S'.perm).symm ⟨n, by omega⟩).val = 0 := by
      have : (permLift S'.perm).symm ⟨n, by omega⟩ = ⟨0, by omega⟩ := by
        apply (permLift S'.perm).injective
        rw [(permLift S'.perm).apply_symm_apply, permLift_zero]
      simp [this]
    rw [h_symm]; simp [show (0 : ℕ) < k.val + 1 from by omega]; omega

open Classical in
-- Lifting a fully colored child simplex produces a boundary rainbow pair
private lemma lift_fullyColored_to_boundary {n p : ℕ} (SC : SpernerColoring (n + 1) p)
    (hp : 0 < p) (S' : KuhnSimplex n p) (hv' : S'.isValid)
    (hfc : S'.fullyColored hv' (childColoring SC).color) :
    decide ((liftSimplex hp S').isRainbowFace (liftSimplex_valid hp S' hv') SC.color
      ⟨0, by omega⟩) = true ∧
    (liftSimplex hp S').faceAdj ⟨0, by omega⟩ = none := by
  constructor
  · -- rainbow face at 0
    rw [decide_eq_true_eq]
    intro color
    obtain ⟨k, hk⟩ := hfc ⟨color.val, by have := color.isLt; omega⟩
    -- vertex k of S' maps to vertex k+1 of liftSimplex
    have hklt := k.isLt
    refine ⟨⟨k.val + 1, by omega⟩, by intro h; exact absurd (congr_arg Fin.val h) (by simp), ?_⟩
    -- SC.color (liftedVertex(k+1)) = color.castSucc
    -- liftedVertex(k+1) = childEmbed(S'.vertex k) by liftSimplex_vertex_childEmbed
    -- childColoring(v) = ⟨SC.color(childEmbed v).val, _⟩
    -- hk says childColoring(S'.vertex k) = ⟨color.val, _⟩
    -- So SC.color(childEmbed(S'.vertex k)).val = color.val = color.castSucc.val
    have hvert := liftSimplex_vertex_childEmbed hp S' hv' k
    rw [hvert]
    -- Now goal: SC.color (childEmbed (S'.vertex hv' k)) = color.castSucc
    -- From hk: (childColoring SC).color (S'.vertex hv' k) = ⟨color.val, _⟩
    -- childColoring SC v = ⟨(SC.color (childEmbed v)).val, _⟩
    have hval : (SC.color (childEmbed n p (S'.vertex hv' k))).val = color.val := by
      have := congr_arg Fin.val hk
      simp only [childColoring] at this
      exact this
    exact Fin.ext (by simp only [Fin.castSucc]; exact hval)
  · -- faceAdj at 0 = none: base(perm(0)) + 1 ≥ p
    -- perm(0) = n (by liftSimplex_perm_zero), base(n) = p-1 (by liftSimplex def)
    have hperm0 := liftSimplex_perm_zero hp S'
    unfold KuhnSimplex.faceAdj
    simp only [
      show n + 1 ≠ 0 from by omega,
      dite_false,
      dite_true]
    -- Now goal: (if base(perm(0))+1 ≥ p then none else some ...) = none
    -- perm(0) = ⟨n, _⟩ and base(n) = p-1 for liftSimplex
    -- The condition is base(perm(0))+1 ≥ p
    -- For liftSimplex: perm(0) = ⟨n, _⟩ and base(n) = p-1
    split_ifs with hb
    · rfl
    · exfalso; apply hb
      rw [show (liftSimplex hp S').perm ⟨0, by omega⟩ = ⟨n, by omega⟩ from hperm0]
      simp [liftSimplex]
      omega

-- Projecting a boundary rainbow pair produces a fully colored child simplex
private lemma project_boundary_to_fullyColored {n p : ℕ} (SC : SpernerColoring (n + 1) p)
    (S : KuhnSimplex (n + 1) p) (hv : S.isValid) (k : Fin (n + 2))
    (hperm0 : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩)
    (hrainbow : S.isRainbowFace hv SC.color k)
    (hboundary : S.faceAdj k = none)
    (hcoord_n : ∀ i : Fin (n + 2), i ≠ k → (S.vertex hv i ⟨n, by omega⟩).val = p) :
    (projectSimplex S hperm0).fullyColored (projectSimplex_valid S hv hperm0)
      (childColoring SC).color := by
  -- fullyColored means: ∀ c : Fin (n+1), ∃ k', childColoring(projected_vertex k') = c
  intro c
  -- Use rainbow at face k to find vertex i with the right color
  obtain ⟨i, hi_ne, hi_color⟩ := hrainbow ⟨c.val, by have := c.isLt; omega⟩
  -- i ≠ k, and k.val = 0 (we'll derive this from hboundary + hperm0)
  have hk0 : k.val = 0 := by
    have hdata := boundary_rainbow_on_last_coord SC ⟨S, hv⟩ k hrainbow hboundary
    exact hdata.1
  have hi_pos : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi_ne (Fin.ext (by omega)))
  -- Map vertex i to projected vertex (i-1)
  refine ⟨⟨i.val - 1, by have := i.isLt; omega⟩, ?_⟩
  -- childColoring SC (projected_vertex (i-1)) = c
  -- childColoring v = ⟨SC.color(childEmbed v).val, _⟩
  -- childEmbed(projected_vertex (i-1)) = S.vertex hv i (by childEmbed_projectSimplex_vertex)
  -- SC.color(S.vertex hv i) = ⟨c.val, _⟩.castSucc (by hi_color)
  -- ⟨c.val, _⟩.castSucc.val = c.val
  -- So childColoring(projected_vertex(i-1)).val = c.val, done.
  have hci := hcoord_n i hi_ne
  have hembed := childEmbed_projectSimplex_vertex S hv hperm0 i hci
  -- hembed: childEmbed (projected vertex (i-1)) = S.vertex hv i
  simp only [childColoring]
  apply Fin.ext
  simp only
  rw [hembed]
  have := congr_arg Fin.val hi_color
  simp only [Fin.castSucc] at this
  exact this

open Classical in
private lemma boundary_odd_inductive {n p : ℕ} (SC : SpernerColoring (n + 1) p) (hp : 0 < p)
    (ih : ∀ (SC' : SpernerColoring n p), Odd (∑ S : ValidSimplex n p, rainbowFaceCount SC' S)) :
    Odd (boundaryRainbowPairs (n + 1) p SC).card := by
  -- Key insight: boundaryRainbowPairs bijects with fully colored simplices of childColoring.
  -- By boundary_rainbow_on_last_coord, each boundary pair has k=0 and perm(0)=n.
  -- Face 0 rainbow ↔ projected simplex is fully colored.
  -- By IH, #{fully colored} is odd, and this equals boundaryRainbowPairs.card.
  --
  -- Step 1: Odd #{S' | fullyColored S' for childColoring}
  have h_fc : Odd (Finset.univ.filter (fun S' : ValidSimplex n p =>
      decide (S'.val.fullyColored S'.property (childColoring SC).color) = true)).card := by
    -- Convert fully-colored filter to odd-rainbowFaceCount filter
    have h1 : (Finset.univ.filter (fun S' : ValidSimplex n p =>
        decide (S'.val.fullyColored S'.property (childColoring SC).color) = true)).card =
      (Finset.univ.filter (fun S' : ValidSimplex n p =>
        Odd (rainbowFaceCount (childColoring SC) S'))).card := by
      congr 1; ext S'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      exact (rainbowFaceCount_odd_iff (childColoring SC) S').symm
    rw [h1, odd_card_odd_iff_odd_sum]
    exact ih (childColoring SC)
  -- Step 2: Biject fully colored child simplices with boundaryRainbowPairs
  -- Each fully colored S' gives boundary pair (liftSimplex S', 0).
  -- Each boundary pair (S, 0) gives fully colored projectSimplex S.
  let fcSet := Finset.univ.filter (fun S' : ValidSimplex n p =>
      decide (S'.val.fullyColored S'.property (childColoring SC).color) = true)
  suffices h_eq : (boundaryRainbowPairs (n + 1) p SC).card = fcSet.card by
    rw [h_eq]; exact h_fc
  -- Define maps between fcSet and boundaryRainbowPairs
  -- Forward: S' ↦ (liftSimplex S', 0)
  -- Backward: (S, 0) ↦ projectSimplex S
  let liftMap : ValidSimplex n p → ValidSimplex (n + 1) p × Fin (n + 2) :=
    fun ⟨S', hv'⟩ => (⟨liftSimplex hp S', liftSimplex_valid hp S' hv'⟩, ⟨0, by omega⟩)
  let projMap : ValidSimplex (n + 1) p × Fin (n + 2) → ValidSimplex n p :=
    fun ⟨⟨S, hv⟩, _⟩ =>
      if h : S.perm ⟨0, by omega⟩ = ⟨n, by omega⟩ then
        ⟨projectSimplex S h, projectSimplex_valid S hv h⟩
      else ⟨⟨fun _ => 0, Equiv.refl _⟩, fun j => by simp; omega⟩
  symm
  apply Finset.card_nbij' liftMap projMap
  · -- liftMap maps fcSet into boundaryRainbowPairs
    intro ⟨S', hv'⟩ hmem
    simp only [Finset.mem_coe] at hmem ⊢
    simp only [fcSet, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hmem
    simp only [liftMap, boundaryRainbowPairs, allRainbowPairs, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact lift_fullyColored_to_boundary SC hp S' hv' hmem
  · -- projMap maps boundaryRainbowPairs into fcSet
    intro ⟨⟨S, hv⟩, k⟩ hmem
    simp only [Finset.mem_coe] at hmem ⊢
    simp only [boundaryRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem
    obtain ⟨hrainbow, hboundary⟩ := hmem
    have hdata := boundary_rainbow_on_last_coord SC ⟨S, hv⟩ k
      (decide_eq_true_eq.mp hrainbow) hboundary
    obtain ⟨hk0, hperm0, hcoord_n⟩ := hdata
    simp only [projMap, dif_pos hperm0, fcSet, Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq]
    exact project_boundary_to_fullyColored SC S hv k hperm0
      (decide_eq_true_eq.mp hrainbow) hboundary hcoord_n
  · -- Left inverse: projMap (liftMap S') = S' for S' ∈ fcSet
    intro ⟨S', hv'⟩ hmem
    simp only [liftMap, projMap]
    have hperm0 := liftSimplex_perm_zero hp S'
    simp only [dif_pos hperm0]
    exact Subtype.ext (projectSimplex_liftSimplex hp S')
  · -- Right inverse: liftMap (projMap x) = x for x ∈ boundaryRainbowPairs
    intro ⟨⟨S, hv⟩, k⟩ hmem
    simp only [Finset.mem_coe] at hmem
    simp only [boundaryRainbowPairs, allRainbowPairs, Finset.mem_filter, Finset.mem_univ,
      true_and] at hmem
    obtain ⟨hrainbow, hboundary⟩ := hmem
    have hdata := boundary_rainbow_on_last_coord SC ⟨S, hv⟩ k
      (decide_eq_true_eq.mp hrainbow) hboundary
    obtain ⟨hk0, hperm0, hcoord_n⟩ := hdata
    simp only [projMap, dif_pos hperm0, liftMap]
    have hbase_n := boundary_base_n_eq S hv hperm0 (by
      rwa [show (⟨0, by omega⟩ : Fin (n + 2)) = k from (Fin.ext (by omega)).symm])
    exact Prod.ext (Subtype.ext (liftSimplex_projectSimplex hp S hperm0 hbase_n))
      (Fin.ext (by simp [hk0]))

/-- The main inductive proof: The total rainbow face count is always odd. -/
private theorem rainbow_sum_odd :
    ∀ (n p : ℕ) (SC : SpernerColoring n p) (_ : 0 < p),
    Odd (∑ S : ValidSimplex n p, rainbowFaceCount SC S) := by
  intro n
  induction n with
  | zero => exact base_case_zero
  | succ n ih =>
    intro p SC hp
    rw [sum_rainbowFaceCount_eq_card]
    rw [(total_parity_eq_boundary (n + 1) p SC)]
    exact boundary_odd_inductive SC hp (fun SC' => ih p SC' hp)

open Classical in
/-- **Cubical Sperner's lemma:** under a Sperner-proper coloring of the grid `[0,p]^n` with
`0 < p`, the number of fully colored valid simplices is odd. -/
theorem cubicalSperner (n p : ℕ) (SC : SpernerColoring n p) (hp : 0 < p) :
    Odd (Finset.card (Finset.univ.filter (fun S : ValidSimplex n p =>
      decide (S.val.fullyColored S.property SC.color) = true))) := by
  -- Rewrite in terms of rainbowFaceCount parity
  suffices h : Odd (Finset.card (Finset.univ.filter (fun S : ValidSimplex n p =>
      Odd (rainbowFaceCount SC S)))) by
    convert h using 2; ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    exact (rainbowFaceCount_odd_iff SC S).symm
  -- #{S | Odd count} ↔ Odd(Σ count)
  rw [odd_card_odd_iff_odd_sum]
  exact rainbow_sum_odd n p SC hp

open Classical in
/-- **Weak Cubical Sperner's Lemma**: There exists a fully colored valid simplex. -/
theorem weakerCubicalSperner (n p : ℕ) (SC : SpernerColoring n p) (hp : 0 < p) :
    ∃ S : KuhnSimplex n p, ∃ hv : S.isValid,
      S.fullyColored hv SC.color := by
  have h := cubicalSperner n p SC hp
  obtain ⟨k, hk⟩ := h
  have hpos : 0 < (Finset.univ.filter (fun S : ValidSimplex n p =>
      decide (S.val.fullyColored S.property SC.color) = true)).card := by omega
  rw [Finset.card_pos] at hpos
  obtain ⟨⟨S, hv⟩, hmem⟩ := hpos
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact ⟨S, hv, of_decide_eq_true hmem⟩

/-- All vertices of a valid simplex are pairwise close: Coordinates differ by ≤ 1. -/
lemma vertex_close {n p : ℕ} (S : KuhnSimplex n p) (hv : S.isValid)
    (k₁ k₂ : Fin (n + 1)) (j : Fin n) :
    (S.vertex hv k₁ j).val ≤ (S.vertex hv k₂ j).val + 1 :=
  S.vertexVal_le_add_one k₁ k₂ j
