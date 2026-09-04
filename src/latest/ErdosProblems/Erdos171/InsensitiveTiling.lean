/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.Tiling
import ErdosProblems.Erdos171.Insensitive
import ErdosProblems.Erdos171.Framework
import ErdosProblems.Erdos171.RestrictedMDHJ

/-!
# Tiling an insensitive set

This file contains the tiling step in the Dodos--Kanellopoulos--Tyros proof.
The first lemma is its elementary geometric core: on an `(i,last)`-insensitive
set, containment of the old-alphabet restriction of a subspace upgrades to
containment of the whole subspace.
-/

namespace Erdos171

open Combinatorics

/-- Membership in the image of a finite set under an equivalence. -/
@[simp] theorem mem_map_equiv_toEmbedding {A B : Type*}
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (S : Finset A) (b : B) :
    b ∈ S.map e.toEmbedding ↔ e.symm b ∈ S := by
  constructor
  · intro hb
    obtain ⟨a, ha, hab⟩ := Finset.mem_map.mp hb
    simpa [← hab] using ha
  · intro hb
    exact Finset.mem_map.mpr ⟨e.symm b, hb, e.apply_symm_apply b⟩

/-- The family of all translates of a common block template over its
support.  It is defined early because both the geometric tiling construction
and the fresh-block invariant use the same finite set. -/
noncomputable def commonBlockLayer {X B Y : Type*}
    [Fintype X] [Fintype B] [Fintype Y]
    (S : Finset (X × Y)) (V : Finset B) : Finset ((X × B) × Y) := by
  classical
  exact Finset.univ.filter fun z ↦ (z.1.1, z.2) ∈ S ∧ z.1.2 ∈ V

@[simp] theorem mem_commonBlockLayer {X B Y : Type*}
    [Fintype X] [Fintype B] [Fintype Y]
    (S : Finset (X × Y)) (V : Finset B) (z : (X × B) × Y) :
    z ∈ commonBlockLayer S V ↔ (z.1.1, z.2) ∈ S ∧ z.1.2 ∈ V := by
  classical
  simp [commonBlockLayer]

section MiddleSubspaces

variable {eta alpha xi mu upsilon : Type*}

/-- Insert a subspace in a middle coordinate block, fixing the coordinates
on both sides. -/
def middleSubspace (x : xi → alpha) (U : Subspace eta alpha mu)
    (y : upsilon → alpha) : Subspace eta alpha ((xi ⊕ mu) ⊕ upsilon) where
  idxFun
    | Sum.inl (Sum.inl a) => Sum.inl (x a)
    | Sum.inl (Sum.inr b) => U.idxFun b
    | Sum.inr c => Sum.inl (y c)
  proper e := by
    obtain ⟨b, hb⟩ := U.proper e
    exact ⟨Sum.inl (Sum.inr b), hb⟩

@[simp] theorem middleSubspace_apply (x : xi → alpha)
    (U : Subspace eta alpha mu) (y : upsilon → alpha) (a : eta → alpha) :
    middleSubspace x U y a = Sum.elim (Sum.elim x (U a)) y := by
  funext c
  rcases c with (c | c) | c <;> simp [middleSubspace, Subspace.coe_apply]

/-- Split a word into the unused coordinates, current block, and used
suffix. -/
def splitMiddleWord : (((xi ⊕ mu) ⊕ upsilon) → alpha) ≃
    (((xi → alpha) × (mu → alpha)) × (upsilon → alpha)) :=
  (Equiv.sumArrowEquivProdArrow (xi ⊕ mu) upsilon alpha).trans
    ((Equiv.sumArrowEquivProdArrow xi mu alpha).prodCongr (Equiv.refl _))

@[simp] theorem splitMiddleWord_middleSubspace_apply
    (x : xi → alpha) (U : Subspace eta alpha mu)
    (y : upsilon → alpha) (a : eta → alpha) :
    splitMiddleWord (middleSubspace x U y a) = ((x, U a), y) := by
  rfl

variable [Fintype (eta → alpha)] [Fintype (xi → alpha)]
  [Fintype (mu → alpha)] [Fintype (upsilon → alpha)]
  [DecidableEq (mu → alpha)]
  [DecidableEq (((xi ⊕ mu) ⊕ upsilon) → alpha)]

/-- The translates of one common middle-block template form a disjoint
subspace tiling. -/
noncomputable def commonBlockTiling
    (S : Finset ((xi → alpha) × (upsilon → alpha)))
    (U : Subspace eta alpha mu) :
    SubspaceTiling eta alpha ((xi ⊕ mu) ⊕ upsilon) := by
  classical
  exact
    { tiles := S.image fun p ↦ middleSubspace p.1 U p.2
      pairwiseDisjoint := by
        intro A hA B hB hAB
        obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨q, hqS, rfl⟩ := Finset.mem_image.mp hB
        change Disjoint (subspacePoints (middleSubspace p.1 U p.2))
          (subspacePoints (middleSubspace q.1 U q.2))
        rw [Finset.disjoint_left]
        intro z hzP hzQ
        rw [mem_subspacePoints] at hzP hzQ
        obtain ⟨a, ha⟩ := hzP
        obtain ⟨b, hb⟩ := hzQ
        have heq : ((p.1, U a), p.2) = ((q.1, U b), q.2) := by
          rw [← splitMiddleWord_middleSubspace_apply p.1 U p.2 a,
            ← splitMiddleWord_middleSubspace_apply q.1 U q.2 b,
            ha, hb]
        have hpq : p = q := by
          apply Prod.ext
          · exact congrArg (fun w ↦ w.1.1) heq
          · exact congrArg
              (fun w : (((xi → alpha) × (mu → alpha)) × (upsilon → alpha)) ↦ w.2) heq
        exact hAB (congrArg (fun r ↦ middleSubspace r.1 U r.2) hpq) }

/-- The covered set of the common-block tiling is exactly the layer obtained
by taking its support times the point set of the template. -/
theorem image_covered_commonBlockTiling
    (S : Finset ((xi → alpha) × (upsilon → alpha)))
    (U : Subspace eta alpha mu) :
    (commonBlockTiling S U).covered.map splitMiddleWord.toEmbedding =
      commonBlockLayer S (subspacePoints U) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Finset.mem_map.mp hz
    obtain ⟨V, hV, hwV⟩ := ((commonBlockTiling S U).mem_covered w).mp hw
    obtain ⟨p, hpS, hpV⟩ := Finset.mem_image.mp hV
    subst V
    rw [mem_subspacePoints] at hwV
    obtain ⟨a, rfl⟩ := hwV
    have hz : z = ((p.1, U a), p.2) := hwz.symm
    subst z
    change ((p.1, U a), p.2) ∈ commonBlockLayer S (subspacePoints U)
    exact (mem_commonBlockLayer S (subspacePoints U) _).mpr
      ⟨hpS, by simp⟩
  · intro hz
    have hz' := (mem_commonBlockLayer S (subspacePoints U) z).mp hz
    rw [mem_subspacePoints] at hz'
    obtain ⟨b, hb⟩ := hz'.2
    apply Finset.mem_map.mpr
    refine ⟨middleSubspace z.1.1 U z.2 b, ?_, ?_⟩
    swap
    · change splitMiddleWord (middleSubspace z.1.1 U z.2 b) = z
      rw [splitMiddleWord_middleSubspace_apply]
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact hb
      · rfl
    apply ((commonBlockTiling S U).mem_covered _).2
    refine ⟨middleSubspace z.1.1 U z.2, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(z.1.1, z.2), hz'.1, rfl⟩
    · simp

end MiddleSubspaces

/-- If the old-alphabet restriction of a subspace lies in an insensitive set,
then its entire parameter cube lies in that set. -/
theorem subspacePoints_subset_of_restricted_of_isLastInsensitive
    {k m n : ℕ} (i : Fin k) (D : Finset (Word (k + 1) n))
    (hD : IsLastInsensitive i (D : Set (Word (k + 1) n)))
    (U : Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (hU : ∀ x : Word k m, U (liftWord x) ∈ D) :
    subspacePoints U ⊆ D := by
  intro z hz
  rw [mem_subspacePoints] at hz
  obtain ⟨y, rfl⟩ := hz
  have heq : LastEquivalent i (U (liftWord (endpoint i y))) (U y) := by
    rw [LastEquivalent]
    funext r
    cases hr : U.idxFun r with
    | inl a =>
        simp [replaceLast, Subspace.coe_apply, hr]
    | inr e =>
        simp [replaceLast, Subspace.coe_apply, hr, liftWord,
          castSucc_endpoint]
  exact (hD _ _ heq).mp (hU (endpoint i y))

/-- The restricted multidimensional theorem extracts a full tile from every
dense insensitive set. -/
theorem FiniteRestrictedMDHJ.exists_subspacePoints_subset_of_insensitive
    {k d : ℕ} (hMDHJ : FiniteRestrictedMDHJ k d)
    (beta : ℝ) (hbeta : 0 < beta) :
    ∃ n : ℕ, ∀ (i : Fin k) (D : Finset (Word (k + 1) n)),
      IsLastInsensitive i (D : Set (Word (k + 1) n)) →
      beta ≤ density D →
      ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin n),
        subspacePoints U ⊆ D := by
  obtain ⟨n, hn⟩ := hMDHJ beta hbeta
  refine ⟨n, ?_⟩
  intro i D hD hden
  obtain ⟨U, hU⟩ := (containsRestrictedSubspace_iff d).mp (hn D hden)
  exact ⟨U, subspacePoints_subset_of_restricted_of_isLastInsensitive i D hD U hU⟩

section CommonBlock

variable {P : Type*} [Fintype P] [Nonempty P]

/-- The one-step extraction in the greedy tiling algorithm.  If a set in a
product cube has insensitive block fibres and density greater than `2 * beta`,
then a positive-density set of outside coordinates admits one and the same
block subspace.  Pigeonholing the common template is what makes the union of
the resulting translates insensitive in the still-unused coordinates. -/
theorem exists_common_block_subspace
    {k d M : ℕ} (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M)))
    (D : Finset (P × Word (k + 1) M))
    (hD : ∀ p : P, IsLastInsensitive i
      (fiber D p : Set (Word (k + 1) M)))
    (hden : 2 * beta ≤ density D) :
    ∃ (U : Subspace (Fin d) (Fin (k + 1)) (Fin M)) (S : Finset P),
      beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) ≤
        density S ∧
      ∀ p ∈ S, subspacePoints U ⊆ fiber D p := by
  classical
  let f : P → ℝ := fun p ↦ density (fiber D p)
  let T : Finset P := superlevel f beta
  have havg : 2 * beta ≤ average f := by
    rw [show average f = density D by
      simpa only [f] using (density_eq_average_fiber D).symm]
    exact hden
  have hTden : beta ≤ density T := by
    have hhalf := half_le_density_superlevel f (δ := 2 * beta)
      (by positivity) havg (fun p ↦ density_le_one (fiber D p))
    simpa only [T, show (2 * beta) / 2 = beta by ring] using hhalf
  have hTpos : 0 < density T := hbeta.trans_le hTden
  have hTne : T.Nonempty := (density_pos T).mp hTpos
  obtain ⟨p₀, hp₀⟩ := hTne
  have hex (p : P) (hp : p ∈ T) :
      ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin M),
        subspacePoints U ⊆ fiber D p := by
    have hpden : beta ≤ density (fiber D p) := by
      exact (mem_superlevel f beta p).mp hp
    obtain ⟨U, hU⟩ := (containsRestrictedSubspace_iff d).mp
      (hblock (fiber D p) hpden)
    exact ⟨U, subspacePoints_subset_of_restricted_of_isLastInsensitive
      i (fiber D p) (hD p) U hU⟩
  obtain ⟨U₀, hU₀⟩ := hex p₀ hp₀
  let : Nonempty (Subspace (Fin d) (Fin (k + 1)) (Fin M)) := ⟨U₀⟩
  have hall : ∀ p : P, ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin M),
      p ∈ T → subspacePoints U ⊆ fiber D p := by
    intro p
    by_cases hp : p ∈ T
    · obtain ⟨U, hU⟩ := hex p hp
      exact ⟨U, fun _ ↦ hU⟩
    · exact ⟨U₀, fun hp' ↦ (hp hp').elim⟩
  choose selected hselected using hall
  obtain ⟨U, hUden⟩ := exists_dense_colorClass T selected
  let S : Finset P := colorClass T selected U
  refine ⟨U, S, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right hTden (by positivity)).trans hUden
  · intro p hp
    have hp' := (mem_colorClass T selected U p).mp hp
    rw [← hp'.2]
    exact hselected p hp'.1

end CommonBlock

section FreshBlockInvariant

variable {X B Y : Type*} [Fintype X] [Fintype B] [Fintype Y]
  [DecidableEq X] [DecidableEq B] [DecidableEq Y]

/-- Coordinate-type-polymorphic version of `LastEquivalent`. -/
def LastEquivalentOn {k : ℕ} (i : Fin k) {I : Type*}
    (x y : I → Fin (k + 1)) : Prop :=
  (fun r ↦ replaceLastLetter i (x r)) =
    (fun r ↦ replaceLastLetter i (y r))

@[refl] theorem LastEquivalentOn.refl {k : ℕ} (i : Fin k)
    {I : Type*} (x : I → Fin (k + 1)) : LastEquivalentOn i x x := rfl

theorem lastEquivalentOn_fin_iff {k n : ℕ} (i : Fin k)
    (x y : Word (k + 1) n) :
    LastEquivalentOn i x y ↔ LastEquivalent i x y := Iff.rfl

/-- A finite set is constant on the classes of a relation.  The fresh-block
argument uses this with `(i,last)`-equivalence, first on a product of unused
coordinates and then on the unused coordinates alone. -/
def IsRelationInsensitive (r : X → X → Prop) (C : Finset X) : Prop :=
  ∀ x x', r x x' → (x ∈ C ↔ x' ∈ C)

/-- Product of two equivalence relations, used for an unused prefix followed
by the current fresh block. -/
def ProductRelation (rX : X → X → Prop) (rB : B → B → Prop) :
    X × B → X × B → Prop :=
  fun z z' ↦ rX z.1 z'.1 ∧ rB z.2 z'.2

/-- Splitting a word across a sum of coordinate types identifies generic
last-equivalence with the product of the two last-equivalences. -/
theorem lastEquivalentOn_sum_iff {k : ℕ} (i : Fin k)
    {I J : Type*} (x y : (I ⊕ J) → Fin (k + 1)) :
    LastEquivalentOn i x y ↔
      ProductRelation (LastEquivalentOn (I := I) i)
        (LastEquivalentOn (I := J) i)
        (Equiv.sumArrowEquivProdArrow I J (Fin (k + 1)) x)
        (Equiv.sumArrowEquivProdArrow I J (Fin (k + 1)) y) := by
  constructor
  · intro h
    constructor <;> funext r
    · exact congrFun h (Sum.inl r)
    · exact congrFun h (Sum.inr r)
  · rintro ⟨hI, hJ⟩
    funext r
    cases r with
    | inl r => exact congrFun hI r
    | inr r => exact congrFun hJ r

/-- Freeze the already used suffix of a three-part word. -/
noncomputable def prefixSection (R : Finset ((X × B) × Y)) (y : Y) :
    Finset (X × B) := by
  classical
  exact Finset.univ.filter fun z ↦ (z, y) ∈ R

/-- Freeze the unused prefix and used suffix, leaving the current block. -/
noncomputable def middleFiber (R : Finset ((X × B) × Y))
    (x : X) (y : Y) : Finset B := by
  classical
  exact Finset.univ.filter fun b ↦ ((x, b), y) ∈ R

/-- Outside coordinates on which every point of the common block template
is still present in the remainder. -/
noncomputable def commonBlockSupport (R : Finset ((X × B) × Y))
    (V : Finset B) : Finset (X × Y) := by
  classical
  exact Finset.univ.filter fun p ↦ ∀ b ∈ V, ((p.1, b), p.2) ∈ R

/-- A support fibre in the coordinates which remain unused. -/
noncomputable def supportFiber (S : Finset (X × Y)) (y : Y) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ (x, y) ∈ S

/-- A fibre of the remainder after both the current block and the used suffix
have been frozen. -/
noncomputable def futureFiber (R : Finset ((X × B) × Y))
    (b : B) (y : Y) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ ((x, b), y) ∈ R

@[simp] theorem mem_prefixSection (R : Finset ((X × B) × Y))
    (y : Y) (z : X × B) : z ∈ prefixSection R y ↔ (z, y) ∈ R := by
  classical
  simp [prefixSection]

@[simp] theorem mem_middleFiber (R : Finset ((X × B) × Y))
    (x : X) (y : Y) (b : B) : b ∈ middleFiber R x y ↔ ((x, b), y) ∈ R := by
  classical
  simp [middleFiber]

@[simp] theorem mem_commonBlockSupport (R : Finset ((X × B) × Y))
    (V : Finset B) (p : X × Y) :
    p ∈ commonBlockSupport R V ↔ ∀ b ∈ V, ((p.1, b), p.2) ∈ R := by
  classical
  simp [commonBlockSupport]

@[simp] theorem mem_supportFiber (S : Finset (X × Y))
    (y : Y) (x : X) : x ∈ supportFiber S y ↔ (x, y) ∈ S := by
  classical
  simp [supportFiber]

@[simp] theorem mem_futureFiber (R : Finset ((X × B) × Y))
    (b : B) (y : Y) (x : X) : x ∈ futureFiber R b y ↔ ((x, b), y) ∈ R := by
  classical
  simp [futureFiber]

theorem commonBlockLayer_subset (R : Finset ((X × B) × Y))
    (V : Finset B) :
    commonBlockLayer (commonBlockSupport R V) V ⊆ R := by
  intro z hz
  have hz' := (mem_commonBlockLayer _ _ _).mp hz
  exact (mem_commonBlockSupport R V (z.1.1, z.2)).mp hz'.1 z.1.2 hz'.2

/-- Joint insensitivity on unused coordinates and the current block implies
insensitivity of every current-block fibre. -/
theorem IsRelationInsensitive.middleFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflX : Reflexive rX) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (x : X) (y : Y) :
    IsRelationInsensitive rB (middleFiber R x y) := by
  intro b b' hbb'
  simpa only [mem_middleFiber, ← mem_prefixSection] using
    hR y (x, b) (x, b') ⟨hreflX x, hbb'⟩

/-- The set of unused prefixes supporting a fixed common block template is
insensitive. -/
theorem IsRelationInsensitive.supportFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflB : Reflexive rB) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (V : Finset B) (y : Y) :
    IsRelationInsensitive rX (supportFiber (commonBlockSupport R V) y) := by
  intro x x' hxx'
  simp only [mem_supportFiber, mem_commonBlockSupport]
  constructor
  · intro hx b hb
    have hmem : (x, b) ∈ prefixSection R y := by simpa using hx b hb
    have := (hR y (x, b) (x', b) ⟨hxx', hreflB b⟩).mp hmem
    simpa using this
  · intro hx b hb
    have hmem : (x', b) ∈ prefixSection R y := by simpa using hx b hb
    have := (hR y (x, b) (x', b) ⟨hxx', hreflB b⟩).mpr hmem
    simpa using this

/-- Before subtraction, every future fibre is insensitive. -/
theorem IsRelationInsensitive.futureFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflB : Reflexive rB) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (b : B) (y : Y) :
    IsRelationInsensitive rX (futureFiber R b y) := by
  intro x x' hxx'
  simpa only [mem_futureFiber, ← mem_prefixSection] using
    hR y (x, b) (x', b) ⟨hxx', hreflB b⟩

/-- Fresh-block preservation: after all translates of the common template
are removed, every fibre over the enlarged used suffix is still insensitive
in all coordinates which remain unused.  This is the precise invariant used
at the next greedy stage. -/
theorem IsRelationInsensitive.residual_futureFiber
    (rX : X → X → Prop) (rB : B → B → Prop)
    (hreflB : Reflexive rB) (R : Finset ((X × B) × Y))
    (hR : ∀ y, IsRelationInsensitive (ProductRelation rX rB)
      (prefixSection R y)) (V : Finset B) (b : B) (y : Y) :
    IsRelationInsensitive rX
      (Erdos171.futureFiber
        (R \ commonBlockLayer (commonBlockSupport R V) V) b y) := by
  have hold := IsRelationInsensitive.futureFiber rX rB hreflB R hR b y
  have hsupp := IsRelationInsensitive.supportFiber rX rB hreflB R hR V y
  intro x x' hxx'
  simp only [mem_futureFiber, Finset.mem_sdiff, mem_commonBlockLayer,
    mem_commonBlockSupport]
  have hold' : (((x, b), y) ∈ R ↔ ((x', b), y) ∈ R) := by
    simpa only [mem_futureFiber] using hold x x' hxx'
  have hsupp' :
      ((∀ c ∈ V, ((x, c), y) ∈ R) ↔
        ∀ c ∈ V, ((x', c), y) ∈ R) := by
    simpa only [mem_supportFiber, mem_commonBlockSupport] using
      hsupp x x' hxx'
  exact and_congr hold' (not_congr (and_congr hsupp' Iff.rfl))

end FreshBlockInvariant

section CommonFreshBlock

variable {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
  [DecidableEq X] [DecidableEq Y]

/-- Reassociate the three blocks so that the current block is the fibre
coordinate used by `exists_common_block_subspace`. -/
def outsideMiddleEquiv (B : Type*) : ((X × B) × Y) ≃ ((X × Y) × B) where
  toFun z := ((z.1.1, z.2), z.1.2)
  invFun z := ((z.1.1, z.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complete one-step form used in DKT Lemma 12.  It selects a common
subspace template in the current coordinate block, takes its full support,
and removes all corresponding translates.  The removed layer has a uniform
positive density, lies in the old remainder, and the new remainder satisfies
the fresh-block invariant. -/
theorem exists_common_block_layer
    {k d M : ℕ} (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (rX : X → X → Prop) (hreflX : Reflexive rX)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M)))
    (R : Finset ((X × Word (k + 1) M) × Y))
    (hR : ∀ y, IsRelationInsensitive
      (ProductRelation rX (LastEquivalent i)) (prefixSection R y))
    (hden : 2 * beta ≤ density R) :
    ∃ U : Subspace (Fin d) (Fin (k + 1)) (Fin M),
      let S := commonBlockSupport R (subspacePoints U)
      let L := commonBlockLayer S (subspacePoints U)
      beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) ≤
          density S ∧
        L ⊆ R ∧
        beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
            density (subspacePoints U) ≤ density L ∧
        ∀ b y, IsRelationInsensitive rX (futureFiber (R \ L) b y) := by
  classical
  let e := outsideMiddleEquiv (X := X) (Y := Y) (Word (k + 1) M)
  let D : Finset ((X × Y) × Word (k + 1) M) := R.map e.toEmbedding
  have hDden : density D = density R := by
    simpa [D, e] using density_map_equiv e R
  have hfiber (p : X × Y) : fiber D p = middleFiber R p.1 p.2 := by
    ext b
    simp [D, e, outsideMiddleEquiv]
  have hDins : ∀ p : X × Y,
      IsLastInsensitive i (fiber D p : Set (Word (k + 1) M)) := by
    intro p
    rw [hfiber]
    exact IsRelationInsensitive.middleFiber rX (LastEquivalent i) hreflX R hR p.1 p.2
  obtain ⟨U, S₀, hS₀den, hS₀⟩ := exists_common_block_subspace
    i beta hbeta hblock D hDins (by simpa only [hDden] using hden)
  let V : Finset (Word (k + 1) M) := subspacePoints U
  let S : Finset (X × Y) := commonBlockSupport R V
  let L : Finset ((X × Word (k + 1) M) × Y) := commonBlockLayer S V
  have hS₀S : S₀ ⊆ S := by
    intro p hp
    rw [show S = commonBlockSupport R V by rfl, mem_commonBlockSupport]
    intro b hb
    have hb' : b ∈ fiber D p := hS₀ p hp (by simpa [V] using hb)
    simpa [hfiber p] using hb'
  have hSden :
      beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) ≤
        density S := hS₀den.trans (density_mono hS₀S)
  have hLsub : L ⊆ R := by
    simpa [L, S] using commonBlockLayer_subset R V
  have hLprod :
      L = (S.product V).map e.symm.toEmbedding := by
    ext z
    simp [L, commonBlockLayer, e, outsideMiddleEquiv]
  have hLden : density L = density S * density V := by
    rw [hLprod, density_map_equiv]
    exact density_product S V
  refine ⟨U, ?_⟩
  dsimp only
  refine ⟨hSden, hLsub, ?_, ?_⟩
  · rw [hLden]
    exact mul_le_mul_of_nonneg_right hSden (density_nonneg V)
  · intro b y
    exact IsRelationInsensitive.residual_futureFiber rX (LastEquivalent i)
      (LastEquivalent.refl i) R hR V b y

end CommonFreshBlock

section GeometricFreshBlockStep

variable {xi upsilon : Type*}

/-- Geometric one-step producer: the common layer returned by
`exists_common_block_layer` is realized as an actual `SubspaceTiling` in the
three-block word cube. -/
theorem exists_common_block_tiling_step
    {k d M : ℕ}
    [Fintype (xi → Fin (k + 1))] [Nonempty (xi → Fin (k + 1))]
    [Fintype (upsilon → Fin (k + 1))] [Nonempty (upsilon → Fin (k + 1))]
    [DecidableEq (xi → Fin (k + 1))]
    [DecidableEq (upsilon → Fin (k + 1))]
    [Fintype (((xi ⊕ Fin M) ⊕ upsilon) → Fin (k + 1))]
    [DecidableEq (((xi ⊕ Fin M) ⊕ upsilon) → Fin (k + 1))]
    (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (rX : (xi → Fin (k + 1)) → (xi → Fin (k + 1)) → Prop)
    (hreflX : Reflexive rX)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M)))
    (R : Finset (((xi ⊕ Fin M) ⊕ upsilon) → Fin (k + 1)))
    (hR : ∀ y, IsRelationInsensitive
      (ProductRelation rX (LastEquivalent i))
      (prefixSection (R.map splitMiddleWord.toEmbedding) y))
    (hden : 2 * beta ≤ density R) :
    ∃ (U : Subspace (Fin d) (Fin (k + 1)) (Fin M))
      (T : SubspaceTiling (Fin d) (Fin (k + 1)) ((xi ⊕ Fin M) ⊕ upsilon)),
      T.IsContainedIn R ∧
      beta / Fintype.card
          (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
          density (subspacePoints U) ≤
        density T.covered ∧
      ∀ b y, IsRelationInsensitive rX
        (futureFiber
          (R.map splitMiddleWord.toEmbedding \ T.covered.map splitMiddleWord.toEmbedding)
          b y) := by
  classical
  let D := R.map splitMiddleWord.toEmbedding
  have hDden : density D = density R := by
    simpa [D] using density_map_equiv
      (splitMiddleWord (xi := xi) (mu := Fin M) (upsilon := upsilon)
        (alpha := Fin (k + 1))) R
  obtain ⟨U, hSden, hLsub, hLden, hres⟩ := exists_common_block_layer
    i beta hbeta rX hreflX hblock D hR (by simpa only [hDden] using hden)
  let S := commonBlockSupport D (subspacePoints U)
  let T : SubspaceTiling (Fin d) (Fin (k + 1)) ((xi ⊕ Fin M) ⊕ upsilon) :=
    commonBlockTiling S U
  have hcoverImage :
      T.covered.map splitMiddleWord.toEmbedding =
        commonBlockLayer S (subspacePoints U) := by
    exact image_covered_commonBlockTiling S U
  have hTsub : T.IsContainedIn R := by
    rw [← T.covered_subset_iff]
    intro x hx
    have hxL : splitMiddleWord x ∈ commonBlockLayer S (subspacePoints U) := by
      rw [← hcoverImage]
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    have hxD : splitMiddleWord x ∈ D := hLsub hxL
    simpa [D] using hxD
  have hTden :
      beta / Fintype.card
          (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
          density (subspacePoints U) ≤ density T.covered := by
    calc
      _ ≤ density (commonBlockLayer S (subspacePoints U)) := hLden
      _ = density (T.covered.map splitMiddleWord.toEmbedding) := by rw [hcoverImage]
      _ = density T.covered := density_map_equiv splitMiddleWord T.covered
  refine ⟨U, T, hTsub, hTden, ?_⟩
  intro b y
  simpa only [D, T, hcoverImage] using hres b y

end GeometricFreshBlockStep

section BlockRecursionCoordinates

/-- Coordinates in the blocks which have not yet been processed. -/
abbrev UnusedBlockCoord (M : ℕ) : ℕ → Type
  | 0 => Fin 0
  | r + 1 => UnusedBlockCoord M r ⊕ Fin M

/-- The recursive unused-block coordinate type is finite. -/
@[instance_reducible] noncomputable def unusedBlockCoordFintype (M : ℕ) :
    ∀ r, Fintype (UnusedBlockCoord M r)
  | 0 => inferInstanceAs (Fintype (Fin 0))
  | r + 1 => by
      letI := unusedBlockCoordFintype M r
      exact inferInstanceAs (Fintype (UnusedBlockCoord M r ⊕ Fin M))

/-- Decidable equality on the recursive unused-block coordinate type. -/
@[instance_reducible] def unusedBlockCoordDecidableEq (M : ℕ) :
    ∀ r, DecidableEq (UnusedBlockCoord M r)
  | 0 => inferInstanceAs (DecidableEq (Fin 0))
  | r + 1 => by
      letI := unusedBlockCoordDecidableEq M r
      exact inferInstanceAs (DecidableEq (UnusedBlockCoord M r ⊕ Fin M))

attribute [local instance] unusedBlockCoordFintype unusedBlockCoordDecidableEq

@[simp] theorem card_unusedBlockCoord (M s : ℕ) :
    Fintype.card (UnusedBlockCoord M s) = s * M := by
  induction s with
  | zero => simp [UnusedBlockCoord]
  | succ s ih => simp [UnusedBlockCoord, ih, Nat.succ_mul]

/-- Coordinates in the blocks already processed by the greedy algorithm. -/
abbrev UsedBlockCoord (M : ℕ) : ℕ → Type
  | 0 => Fin 0
  | s + 1 => Fin M ⊕ UsedBlockCoord M s

/-- Reassociate one newly processed block from the unused side to the used
side. -/
def blockAssocEquiv (M r s : ℕ) :
    ((UnusedBlockCoord M r ⊕ Fin M) ⊕ UsedBlockCoord M s) ≃
      (UnusedBlockCoord M r ⊕ (Fin M ⊕ UsedBlockCoord M s)) where
  toFun
    | Sum.inl (Sum.inl x) => Sum.inl x
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
    | Sum.inr y => Sum.inr (Sum.inr y)
  invFun
    | Sum.inl x => Sum.inl (Sum.inl x)
    | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
    | Sum.inr (Sum.inr y) => Sum.inr y
  left_inv
    | Sum.inl (Sum.inl x) => rfl
    | Sum.inl (Sum.inr b) => rfl
    | Sum.inr y => rfl
  right_inv
    | Sum.inl x => rfl
    | Sum.inr (Sum.inl b) => rfl
    | Sum.inr (Sum.inr y) => rfl

/-- Freeze the used coordinate suffix of a word set. -/
noncomputable def sumSection {A C alpha : Type*}
    [Fintype (A → alpha)] (R : Finset ((A ⊕ C) → alpha))
    (y : C → alpha) : Finset (A → alpha) := by
  classical
  exact Finset.univ.filter fun x ↦ Sum.elim x y ∈ R

@[simp] theorem mem_sumSection {A C alpha : Type*}
    [Fintype (A → alpha)] (R : Finset ((A ⊕ C) → alpha))
    (y : C → alpha) (x : A → alpha) :
    x ∈ sumSection R y ↔ Sum.elim x y ∈ R := by
  classical
  simp [sumSection]

/-- The invariant at a greedy stage: after the used suffix is frozen, the
entire remaining prefix is `(i,last)`-insensitive. -/
def HasFreshBlockInvariant {k : ℕ} (i : Fin k)
    {A C : Type*} [Fintype (A → Fin (k + 1))]
    (R : Finset ((A ⊕ C) → Fin (k + 1))) : Prop :=
  ∀ y, IsRelationInsensitive (LastEquivalentOn (I := A) i) (sumSection R y)

end BlockRecursionCoordinates

section GreedyBlockRun

attribute [local instance] unusedBlockCoordFintype unusedBlockCoordDecidableEq

/-- The uniform density gained at every unsuccessful fresh-block stage. -/
noncomputable def insensitiveBlockGain (k d M : ℕ) (beta : ℝ) : ℝ :=
  beta / Fintype.card (Subspace (Fin d) (Fin (k + 1)) (Fin M)) *
    ((k + 1 : ℝ) ^ d / (k + 1 : ℝ) ^ M)

theorem density_subspacePoints_block {k d M : ℕ}
    (U : Subspace (Fin d) (Fin (k + 1)) (Fin M)) :
    density (subspacePoints U) =
      (k + 1 : ℝ) ^ d / (k + 1 : ℝ) ^ M := by
  simp [density_eq_card_div_card, card_subspacePoints_fin, Word]

/-- The finite fresh-block recursion.  Either it already leaves a remainder
of density below `2 * beta`, or its disjoint tiles occupy at least one copy of
the uniform gain for every available block. -/
theorem exists_tiling_or_density_gain
    {k d M : ℕ} (i : Fin k) (beta : ℝ) (hbeta : 0 < beta)
    (hblock : ∀ A : Finset (Word (k + 1) M),
      beta ≤ density A → ContainsRestrictedSubspace d
        (A : Set (Word (k + 1) M))) :
    ∀ (s : ℕ) {C : Type*} [Fintype C] [DecidableEq C]
      (Q : Finset ((UnusedBlockCoord M s ⊕ C) → Fin (k + 1))),
      HasFreshBlockInvariant i Q →
      ∃ T : SubspaceTiling (Fin d) (Fin (k + 1))
          (UnusedBlockCoord M s ⊕ C),
        T.IsContainedIn Q ∧
          (density (Q \ T.covered) < 2 * beta ∨
            (s : ℝ) * insensitiveBlockGain k d M beta ≤ density T.covered) := by
  intro s
  induction s with
  | zero =>
      intro C _inst _dec Q hQ
      refine ⟨SubspaceTiling.empty, ?_, Or.inr ?_⟩
      · intro U hU
        simp at hU
      · simp [insensitiveBlockGain]
  | succ s ih =>
      intro C _inst _dec Q hQ
      by_cases hsmall : density Q < 2 * beta
      · refine ⟨SubspaceTiling.empty, ?_, Or.inl ?_⟩
        · intro U hU
          simp at hU
        · simpa only [SubspaceTiling.covered_empty, Finset.sdiff_empty] using hsmall
      let D := Q.map splitMiddleWord.toEmbedding
      have hstepInv : ∀ y, IsRelationInsensitive
          (ProductRelation
            (LastEquivalentOn (I := UnusedBlockCoord M s) i)
            (LastEquivalent i)) (prefixSection D y) := by
        intro y p p' hpp'
        let x : (UnusedBlockCoord M s ⊕ Fin M) → Fin (k + 1) :=
          Sum.elim p.1 p.2
        let x' : (UnusedBlockCoord M s ⊕ Fin M) → Fin (k + 1) :=
          Sum.elim p'.1 p'.2
        have hxx' : LastEquivalentOn i x x' := by
          apply (lastEquivalentOn_sum_iff i x x').mpr
          exact ⟨hpp'.1, (lastEquivalentOn_fin_iff i p.2 p'.2).mpr hpp'.2⟩
        have hxmem := hQ y x x' hxx'
        have hxmem' : Sum.elim x y ∈ Q ↔ Sum.elim x' y ∈ Q := by
          simpa only [mem_sumSection] using hxmem
        rw [mem_prefixSection, mem_prefixSection]
        have hp : (p, y) ∈ D ↔ Sum.elim x y ∈ Q := by
          simp only [D, mem_map_equiv_toEmbedding]
          rfl
        have hp' : (p', y) ∈ D ↔ Sum.elim x' y ∈ Q := by
          simp only [D, mem_map_equiv_toEmbedding]
          rfl
        exact hp.trans (hxmem'.trans hp'.symm)
      obtain ⟨U, L, hLsub, hLgain, hres⟩ := exists_common_block_tiling_step
        i beta hbeta (LastEquivalentOn (I := UnusedBlockCoord M s) i)
          (LastEquivalentOn.refl i) hblock Q hstepInv (not_lt.mp hsmall)
      let Q₀ := Q \ L.covered
      let e := blockAssocEquiv M s 0
      -- The suffix type is arbitrary; use the same associator with `C`.
      let eC :
          ((UnusedBlockCoord M s ⊕ Fin M) ⊕ C) ≃
            (UnusedBlockCoord M s ⊕ (Fin M ⊕ C)) :=
        { toFun
            | Sum.inl (Sum.inl x) => Sum.inl x
            | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
            | Sum.inr y => Sum.inr (Sum.inr y)
          invFun
            | Sum.inl x => Sum.inl (Sum.inl x)
            | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
            | Sum.inr (Sum.inr y) => Sum.inr y
          left_inv
            | Sum.inl (Sum.inl x) => rfl
            | Sum.inl (Sum.inr b) => rfl
            | Sum.inr y => rfl
          right_inv
            | Sum.inl x => rfl
            | Sum.inr (Sum.inl b) => rfl
            | Sum.inr (Sum.inr y) => rfl }
      let Q' := Q₀.map (SubspaceTiling.ambientWordEquiv eC).toEmbedding
      have hQ'inv : HasFreshBlockInvariant i Q' := by
        intro y' x x' hxx'
        let b : Word (k + 1) M := fun r ↦ y' (Sum.inl r)
        let y : C → Fin (k + 1) := fun r ↦ y' (Sum.inr r)
        have hh := hres b y x x' hxx'
        let ew := SubspaceTiling.ambientWordEquiv
          (alpha := Fin (k + 1)) eC
        have hamb (z : UnusedBlockCoord M s → Fin (k + 1)) :
            ew.symm (Sum.elim z y') = Sum.elim (Sum.elim z b) y := by
          funext q
          rcases q with (q | q)
          · rcases q with q | q <;> rfl
          · rfl
        have hmem (z : UnusedBlockCoord M s → Fin (k + 1)) :
            Sum.elim z y' ∈ Q' ↔
              z ∈ futureFiber
                (D \ L.covered.map splitMiddleWord.toEmbedding) b y := by
          dsimp only [Q']
          rw [mem_map_equiv_toEmbedding, hamb]
          simp only [Q₀, mem_futureFiber, Finset.mem_sdiff, D,
            mem_map_equiv_toEmbedding]
          rfl
        rw [mem_sumSection, mem_sumSection]
        exact (hmem x).trans (hh.trans (hmem x').symm)
      obtain ⟨T', hT'sub, hT'out⟩ := ih (C := Fin M ⊕ C) Q' hQ'inv
      let T₀ := T'.ambientReindex eC.symm
      have hT₀contained : T₀.IsContainedIn Q₀ := by
        change (T'.ambientReindex eC.symm).IsContainedIn Q₀
        rw [SubspaceTiling.ambientReindex_isContainedIn_iff]
        simpa [Q', SubspaceTiling.ambientWordEquiv, Function.comp_def] using hT'sub
      have hT₀sub : T₀.covered ⊆ Q₀ :=
        (T₀.covered_subset_iff Q₀).mpr hT₀contained
      have hdisj : Disjoint L.covered T₀.covered := by
        rw [Finset.disjoint_left]
        intro x hxL hxT
        exact (Finset.mem_sdiff.mp (hT₀sub hxT)).2 hxL
      let T := L.disjointUnion T₀ hdisj
      have hTsub : T.IsContainedIn Q := by
        rw [← T.covered_subset_iff]
        rw [SubspaceTiling.covered_disjointUnion]
        intro x hx
        rcases Finset.mem_union.mp hx with hxL | hxT
        · exact ((L.covered_subset_iff Q).mpr hLsub) hxL
        · exact (Finset.mem_sdiff.mp (hT₀sub hxT)).1
      refine ⟨T, hTsub, ?_⟩
      rcases hT'out with hT'small | hT'gain
      · left
        have heq : density (Q₀ \ T₀.covered) =
            density (Q' \ T'.covered) := by
          have h := SubspaceTiling.density_sdiff_covered_ambientReindex
            T' eC.symm Q₀
          simpa [T₀, Q', SubspaceTiling.ambientWordEquiv,
            Function.comp_def] using h
        have hresEq : Q \ T.covered = Q₀ \ T₀.covered := by
          have hcover : T.covered = L.covered ∪ T₀.covered :=
            SubspaceTiling.covered_disjointUnion L T₀ hdisj
          rw [hcover]
          ext x
          simp only [Q₀, Finset.mem_sdiff, Finset.mem_union]
          tauto
        rw [hresEq, heq]
        exact hT'small
      · right
        have hT₀den : density T₀.covered = density T'.covered := by
          change density (T'.ambientReindex eC.symm).covered = density T'.covered
          rw [SubspaceTiling.covered_ambientReindex]
          exact density_map_equiv
            (SubspaceTiling.ambientWordEquiv eC.symm) T'.covered
        have hinter : L.covered ∩ T₀.covered = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj
        have hadd : density T.covered = density L.covered + density T₀.covered := by
          rw [show T.covered = L.covered ∪ T₀.covered by
            exact SubspaceTiling.covered_disjointUnion L T₀ hdisj]
          have hu := density_union_add_density_inter L.covered T₀.covered
          rw [hinter, density_empty] at hu
          linarith
        have hgain' : insensitiveBlockGain k d M beta ≤ density L.covered := by
          simpa [insensitiveBlockGain, density_subspacePoints_block U] using hLgain
        rw [hadd, hT₀den]
        push_cast
        nlinarith

end GreedyBlockRun

section OneInsensitiveTiling

attribute [local instance] unusedBlockCoordFintype unusedBlockCoordDecidableEq

/-- Dodos--Kanellopoulos--Tyros, Lemma 12, with an arbitrary lower bound on
the ambient dimension. -/
theorem FiniteRestrictedMDHJ.exists_oneInsensitiveTilingAt_ge
    {k d : ℕ} (hMDHJ : FiniteRestrictedMDHJ k d)
    {beta : ℝ} (hbeta : 0 < beta) (N : ℕ) :
    ∃ n, N ≤ n ∧ OneInsensitiveTilingAt k d n beta := by
  by_cases htriv : 1 ≤ 2 * beta
  · refine ⟨N, le_rfl, ?_⟩
    intro i D hD hden
    exact (not_lt_of_ge ((density_le_one D).trans htriv) hden).elim
  obtain ⟨M, hMpos, hblock⟩ := hMDHJ.positiveWitness beta hbeta
  have hbeta1 : beta ≤ 1 := by linarith
  obtain ⟨U, hU⟩ := hblock (Finset.univ : Finset (Word (k + 1) M))
    (by rw [density_univ]; exact hbeta1)
  let : Nonempty (Subspace (Fin d) (Fin (k + 1)) (Fin M)) := ⟨U⟩
  let theta := insensitiveBlockGain k d M beta
  have htheta : 0 < theta := by
    dsimp only [theta, insensitiveBlockGain]
    positivity
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt (1 / theta)
  let R := max R₀ N
  have hR₀R : (R₀ : ℝ) ≤ R := by
    exact_mod_cast Nat.le_max_left R₀ N
  have hRgain₀ : 1 < (R₀ : ℝ) * theta :=
    (div_lt_iff₀ htheta).mp hR₀
  have hRgain : 1 < (R : ℝ) * theta := by
    nlinarith
  have hNRM : N ≤ R * M := by
    have hNR : N ≤ R := Nat.le_max_right R₀ N
    have hRM : R ≤ R * M := by
      nlinarith [hMpos]
    exact hNR.trans hRM
  let I := UnusedBlockCoord M R ⊕ Fin 0
  have hIcard : Fintype.card I = R * M := by
    simp [I]
  let e : I ≃ Fin (R * M) := Fintype.equivFinOfCardEq hIcard
  refine ⟨R * M, hNRM, ?_⟩
  intro i D hD hDden
  let ew := SubspaceTiling.ambientWordEquiv
    (alpha := Fin (k + 1)) e
  let Q : Finset (I → Fin (k + 1)) := D.map ew.symm.toEmbedding
  have hQinv : HasFreshBlockInvariant i Q := by
    intro y x x' hxx'
    rw [mem_sumSection, mem_sumSection]
    have hsum : LastEquivalentOn i (Sum.elim x y) (Sum.elim x' y) :=
      (lastEquivalentOn_sum_iff i _ _).mpr
        ⟨hxx', LastEquivalentOn.refl i y⟩
    have hew : LastEquivalentOn i (ew (Sum.elim x y))
        (ew (Sum.elim x' y)) := by
      funext r
      exact congrFun hsum (e.symm r)
    have hmem := hD (ew (Sum.elim x y)) (ew (Sum.elim x' y))
      ((lastEquivalentOn_fin_iff i _ _).mp hew)
    simpa only [Q, mem_map_equiv_toEmbedding, Equiv.symm_symm,
      Finset.mem_coe] using hmem
  obtain ⟨T, hTsub, hout⟩ := exists_tiling_or_density_gain
    i beta hbeta hblock R (C := Fin 0) Q hQinv
  rcases hout with hsmall | hgain
  · let Tout := T.ambientReindex e
    refine ⟨Tout, ?_, ?_⟩
    · change (T.ambientReindex e).IsContainedIn D
      apply (SubspaceTiling.ambientReindex_isContainedIn_iff T e D).mpr
      simpa only [Q] using hTsub
    · change density (D \ (T.ambientReindex e).covered) < 2 * beta
      rw [SubspaceTiling.density_sdiff_covered_ambientReindex]
      simpa only [Q] using hsmall
  · have hcap := density_le_one T.covered
    exact (not_lt_of_ge hcap (hRgain.trans_le hgain)).elim

end OneInsensitiveTiling

section FiniteGreedyIteration

variable {Omega : Type*} [Fintype Omega]

/-- A process which gains a fixed positive density whenever it has not
terminated must terminate before more than `1 / theta` steps.  The geometric
fresh-block lemmas supply `covered`, `remainder`, and the step inequality. -/
theorem exists_small_remainder_of_density_gain
    (covered remainder : ℕ → Finset Omega) (theta beta : ℝ) (R : ℕ)
    (htheta : 0 < theta) (hR : 1 < (R : ℝ) * theta)
    (hstep : ∀ j < R, ¬ density (remainder j) < 2 * beta →
      density (covered j) + theta ≤ density (covered (j + 1))) :
    ∃ j ≤ R, density (remainder j) < 2 * beta := by
  by_contra hstop
  push_neg at hstop
  have hlower : ∀ j ≤ R, (j : ℝ) * theta ≤ density (covered j) := by
    intro j hj
    induction j with
    | zero =>
        simpa using density_nonneg (covered 0)
    | succ j ih =>
        have hjR : j < R := by omega
        have hgain := hstep j hjR (not_lt.mpr (hstop j (by omega)))
        have hprev := ih (by omega)
        push_cast
        nlinarith
  have hcap := density_le_one (covered R)
  have := hlower R le_rfl
  nlinarith

end FiniteGreedyIteration

end Erdos171
