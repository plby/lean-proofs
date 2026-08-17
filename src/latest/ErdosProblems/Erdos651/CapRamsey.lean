/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.CapAssembly
import ErdosProblems.Erdos651.FiniteRamsey

/-!
# The second Dilworth--Ramsey--cap step of Pohoata--Zakharov

This file contains the finite combinatorial part of Section 3 of the
Pohoata--Zakharov proof.  The geometric construction preceding this step
associates two polyhedra `P₁, P₂` to every triple of cluster indices and
proves two implications on the middle cluster:

* an antichain for `x ∈ conv({y} ∪ P₁)` is `P₁`-free;
* a chain for the same relation is `P₂`-free.

Those are recorded as fields of `MiddleTripleGadget`; everything else in
this file is derived.  In particular, finite Dilworth gives a free subset
of cardinality at least the integer square root, triple Ramsey makes the
choice of `P₁` or `P₂` uniform, Proposition 2.1 extracts caps, and the cap
assembly lemma gives the final convex set.
-/

namespace Erdos651

open Set
open scoped BigOperators

noncomputable section

/-! ## The source preorder and its square-root dichotomy -/

/-- Relation (4.9) in the source: `x ≼[P] y` means that `x` belongs to
the convex hull of `y` together with the background polyhedron `P`. -/
def sourcePolytopeLE (P : Set (Point 3)) (x y : Point 3) : Prop :=
  x ∈ convexHull ℝ ({y} ∪ P)

/-- The relation in (4.9) is reflexive and transitive.  Antisymmetry is not
needed: finite Dilworth is available for preorders via antisymmetrization. -/
theorem sourcePolytopeLE_isPreorder (P : Set (Point 3)) :
    IsPreorder (Point 3) (sourcePolytopeLE P) := by
  let hr : Std.Refl (sourcePolytopeLE P) := ⟨by
    intro x
    exact subset_convexHull ℝ _ (Or.inl (Set.mem_singleton x))⟩
  let ht : IsTrans (Point 3) (sourcePolytopeLE P) := ⟨by
    intro x y z hxy hyz
    apply convexHull_min ?_ (convex_convexHull ℝ _) hxy
    intro w hw
    rcases hw with rfl | hw
    · exact hyz
    · exact subset_convexHull ℝ _ (Or.inr hw)⟩
  exact @IsPreorder.mk _ _ hr ht

/-- Every two members of `A` are comparable under `r`.  Reflexivity makes
this formulation equivalent to the usual finite-chain predicate, and it is
convenient for fibers of a Dilworth chain coloring. -/
def PairwiseComparable {α : Type*} (r : α → α → Prop)
    (A : Finset α) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → r x y ∨ r y x

/-- The elementary width-height consequence of finite Dilworth.  A finite
preorder has a chain or antichain containing at least `⌊√|X|⌋` elements. -/
theorem exists_sqrt_chain_or_antichain
    {α : Type*} [DecidableEq α] (X : Finset α)
    (r : α → α → Prop) (hr : IsPreorder α r) :
    ∃ A : Finset α, A ⊆ X ∧ Nat.sqrt X.card ≤ A.card ∧
      (IsAntichain r (↑A : Set α) ∨ PairwiseComparable r A) := by
  classical
  let s := Nat.sqrt X.card
  by_cases hs : s = 0
  · refine ⟨∅, Finset.empty_subset _, by simp [hs], Or.inl ?_⟩
    simp
  let αX := ↑X
  let rX : αX → αX → Prop := fun x y => r x.1 y.1
  have hrX : IsPreorder αX rX :=
    { refl := fun x => hr.refl x.1
      trans := fun _ _ _ hxy hyz => hr.trans hxy hyz }
  by_cases hwide : ∃ A : Finset αX,
      IsAntichain rX (↑A : Set αX) ∧ s ≤ A.card
  · obtain ⟨A, hAanti, hAs⟩ := hwide
    let B := A.map (Function.Embedding.subtype _)
    refine ⟨B, ?_, ?_, Or.inl ?_⟩
    · intro x hx
      simp only [B, Finset.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    · simpa [B] using hAs
    · intro x hx y hy hxy hrel
      simp only [B, Finset.mem_coe, Finset.mem_map] at hx hy
      obtain ⟨x', hx'A, rfl⟩ := hx
      obtain ⟨y', hy'A, hy'eq⟩ := hy
      subst y
      exact hAanti hx'A hy'A (fun h => hxy (congrArg Subtype.val h)) hrel
  · push_neg at hwide
    have hspos : 0 < s := Nat.pos_of_ne_zero hs
    letI : Nonempty (Fin s) := Fin.pos_iff_nonempty.1 hspos
    obtain ⟨color, hcolor⟩ :=
      finite_dilworth_of_isPreorder rX hrX s hspos (by
        intro A hA
        exact (hwide A hA).le)
    have hsq : s * s ≤ Fintype.card αX := by
      simpa [s, αX] using Nat.sqrt_le X.card
    obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
      (f := color) (n := s) (by simpa using hsq)
    let A : Finset αX := Finset.univ.filter fun x => color x = c
    have hAcard : s ≤ A.card := by
      simpa [A] using hc
    let B := A.map (Function.Embedding.subtype _)
    refine ⟨B, ?_, by simpa [B] using hAcard, Or.inr ?_⟩
    · intro x hx
      simp only [B, Finset.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    · intro x hx y hy
      simp only [B, Finset.mem_map] at hx hy
      obtain ⟨x', hx'A, rfl⟩ := hx
      obtain ⟨y', hy'A, hy'eq⟩ := hy
      subst y
      apply hcolor
      have hxc : color x' = c := (Finset.mem_filter.mp hx'A).2
      have hyc : color y' = c := (Finset.mem_filter.mp hy'A).2
      exact hxc.trans hyc.symm

/-- Exact (non-rounded) width-height form: the selected chain or antichain
has cardinality whose square is at least the cardinality of the ambient
finite set. -/
theorem exists_chain_or_antichain_card_le_square
    {α : Type*} [DecidableEq α] (X : Finset α)
    (r : α → α → Prop) (hr : IsPreorder α r) :
    ∃ A : Finset α, A ⊆ X ∧ X.card ≤ A.card * A.card ∧
      (IsAntichain r (↑A : Set α) ∨ PairwiseComparable r A) := by
  classical
  let s := Nat.sqrt X.card
  by_cases hsquare : s * s = X.card
  · obtain ⟨A, hAX, hAs, hA⟩ := exists_sqrt_chain_or_antichain X r hr
    refine ⟨A, hAX, ?_, hA⟩
    calc
      X.card = s * s := hsquare.symm
      _ ≤ A.card * A.card := Nat.mul_le_mul hAs hAs
  · have hsle : s * s ≤ X.card := by
      simpa [s] using Nat.sqrt_le X.card
    have hss : s * s < X.card := lt_of_le_of_ne hsle hsquare
    have hspos : 0 < s := by
      rw [s, Nat.sqrt_pos]
      omega
    let αX := ↑X
    let rX : αX → αX → Prop := fun x y => r x.1 y.1
    have hrX : IsPreorder αX rX :=
      { refl := fun x => hr.refl x.1
        trans := fun _ _ _ hxy hyz => hr.trans hxy hyz }
    by_cases hwide : ∃ A : Finset αX,
        IsAntichain rX (↑A : Set αX) ∧ s < A.card
    · obtain ⟨A, hAanti, hAs⟩ := hwide
      let B := A.map (Function.Embedding.subtype _)
      refine ⟨B, ?_, ?_, Or.inl ?_⟩
      · intro x hx
        simp only [B, Finset.mem_map] at hx
        obtain ⟨y, -, rfl⟩ := hx
        exact y.2
      · have hsucc : s + 1 ≤ A.card := by omega
        have hroot : X.card < (s + 1) * (s + 1) := by
          simpa [s] using Nat.lt_succ_sqrt X.card
        calc
          X.card ≤ (s + 1) * (s + 1) := hroot.le
          _ ≤ A.card * A.card := Nat.mul_le_mul hsucc hsucc
          _ = B.card * B.card := by simp [B]
      · intro x hx y hy hxy hrel
        simp only [B, Finset.mem_coe, Finset.mem_map] at hx hy
        obtain ⟨x', hx'A, rfl⟩ := hx
        obtain ⟨y', hy'A, hy'eq⟩ := hy
        subst y
        exact hAanti hx'A hy'A (fun h => hxy (congrArg Subtype.val h)) hrel
    · push_neg at hwide
      letI : Nonempty (Fin s) := Fin.pos_iff_nonempty.1 hspos
      obtain ⟨color, hcolor⟩ :=
        finite_dilworth_of_isPreorder rX hrX s hspos hwide
      obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card
        (f := color) (n := s) (by simpa [αX] using hss)
      let A : Finset αX := Finset.univ.filter fun x => color x = c
      have hAs : s < A.card := by
        simpa [A] using hc
      let B := A.map (Function.Embedding.subtype _)
      refine ⟨B, ?_, ?_, Or.inr ?_⟩
      · intro x hx
        simp only [B, Finset.mem_map] at hx
        obtain ⟨y, -, rfl⟩ := hx
        exact y.2
      · have hsucc : s + 1 ≤ A.card := by omega
        have hroot : X.card < (s + 1) * (s + 1) := by
          simpa [s] using Nat.lt_succ_sqrt X.card
        calc
          X.card ≤ (s + 1) * (s + 1) := hroot.le
          _ ≤ A.card * A.card := Nat.mul_le_mul hsucc hsucc
          _ = B.card * B.card := by simp [B]
      · intro x hx y hy
        simp only [B, Finset.mem_map] at hx hy
        obtain ⟨x', hx'A, rfl⟩ := hx
        obtain ⟨y', hy'A, hy'eq⟩ := hy
        subst y
        apply hcolor
        have hxc : color x' = c := (Finset.mem_filter.mp hx'A).2
        have hyc : color y' = c := (Finset.mem_filter.mp hy'A).2
        exact hxc.trans hyc.symm

/-! ## A triple gadget and the induced Ramsey color -/

/-- The precise geometric output needed from the three-polytope construction
for one triple of cluster indices.  The two fields ending in `_free` are the
line-separation statements proved by the geometry; the square-root loss and
all subsequent selections are not assumptions. -/
structure MiddleTripleGadget where
  middle : Finset (Point 3)
  firstPolytope : Set (Point 3)
  secondPolytope : Set (Point 3)
  antichain_first_free : ∀ A : Finset (Point 3), A ⊆ middle →
    IsAntichain (sourcePolytopeLE firstPolytope) (↑A : Set (Point 3)) →
      PFree firstPolytope A
  chain_second_free : ∀ A : Finset (Point 3), A ⊆ middle →
    PairwiseComparable (sourcePolytopeLE firstPolytope) A →
      PFree secondPolytope A

/-- A convenient adapter from the two line implications established by the
three-convex-set geometry.  The first implication says that any line meeting
`P₁` makes its two middle points comparable; the second says that comparable
middle points span a line missing `P₂`. -/
def MiddleTripleGadget.ofLineSeparation
    (middle : Finset (Point 3))
    (P₁ P₂ : Set (Point 3))
    (hmiddle_first : Disjoint (↑middle : Set (Point 3)) P₁)
    (hmiddle_second : Disjoint (↑middle : Set (Point 3)) P₂)
    (hfirst : ∀ ⦃x⦄, x ∈ middle → ∀ ⦃y⦄, y ∈ middle → x ≠ y →
      ¬ Disjoint (lineThrough x y) P₁ →
        sourcePolytopeLE P₁ x y ∨ sourcePolytopeLE P₁ y x)
    (hsecond : ∀ ⦃x⦄, x ∈ middle → ∀ ⦃y⦄, y ∈ middle → x ≠ y →
      (sourcePolytopeLE P₁ x y ∨ sourcePolytopeLE P₁ y x) →
        Disjoint (lineThrough x y) P₂) :
    MiddleTripleGadget where
  middle := middle
  firstPolytope := P₁
  secondPolytope := P₂
  antichain_first_free := by
    intro A hAmiddle hAanti
    refine ⟨hmiddle_first.mono ?_ (fun _ h => h), ?_⟩
    · intro x hx
      exact hAmiddle hx
    · intro x hxA y hyA hxy
      by_contra hline
      rcases hfirst (hAmiddle hxA) (hAmiddle hyA) hxy hline with hrel | hrel
      · exact hAanti hxA hyA hxy hrel
      · exact hAanti hyA hxA hxy.symm hrel
  chain_second_free := by
    intro A hAmiddle hAchain
    refine ⟨hmiddle_second.mono ?_ (fun _ h => h), ?_⟩
    · intro x hx
      exact hAmiddle hx
    · intro x hxA y hyA hxy
      exact hsecond (hAmiddle hxA) (hAmiddle hyA) hxy (hAchain hxA hyA)

/-- A gadget always supplies a square-root-sized free set for one of its
two background polyhedra, in the exact integer form `|middle| ≤ |Z|²`. -/
theorem MiddleTripleGadget.exists_large_free_subset_exact (G : MiddleTripleGadget) :
    (∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      G.middle.card ≤ Z.card * Z.card ∧ PFree G.firstPolytope Z) ∨
    (∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      G.middle.card ≤ Z.card * Z.card ∧ PFree G.secondPolytope Z) := by
  obtain ⟨A, hAmid, hAcard, hAanti | hAchain⟩ :=
    exists_chain_or_antichain_card_le_square G.middle
      (sourcePolytopeLE G.firstPolytope)
      (sourcePolytopeLE_isPreorder G.firstPolytope)
  · exact Or.inl ⟨A, hAmid, hAcard, G.antichain_first_free A hAmid hAanti⟩
  · exact Or.inr ⟨A, hAmid, hAcard, G.chain_second_free A hAmid hAchain⟩

theorem sqrt_le_of_card_le_square {m a : ℕ} (h : m ≤ a * a) :
    Nat.sqrt m ≤ a := by
  apply Nat.le_of_lt_succ
  rw [Nat.sqrt_lt]
  exact h.trans_lt (Nat.mul_self_lt_mul_self (Nat.lt_succ_self a))

/-- The conventional integer-square-root corollary of the exact form. -/
theorem MiddleTripleGadget.exists_large_free_subset (G : MiddleTripleGadget) :
    (∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      Nat.sqrt G.middle.card ≤ Z.card ∧ PFree G.firstPolytope Z) ∨
    (∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      Nat.sqrt G.middle.card ≤ Z.card ∧ PFree G.secondPolytope Z) := by
  rcases G.exists_large_free_subset_exact with h | h
  · left
    obtain ⟨Z, hZmid, hZsq, hZfree⟩ := h
    exact ⟨Z, hZmid, sqrt_le_of_card_le_square hZsq, hZfree⟩
  · right
    obtain ⟨Z, hZmid, hZsq, hZfree⟩ := h
    exact ⟨Z, hZmid, sqrt_le_of_card_le_square hZsq, hZfree⟩

/-- Red (`true`) means that the first-polytope alternative exists. -/
noncomputable def MiddleTripleGadget.color (G : MiddleTripleGadget) : Bool := by
  classical
  exact decide (∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
    G.middle.card ≤ Z.card * Z.card ∧ PFree G.firstPolytope Z)

/-- The Ramsey color records a genuine free-set choice, with the exact
quadratic cardinality bound. -/
theorem MiddleTripleGadget.color_spec_exact (G : MiddleTripleGadget) :
    ∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      G.middle.card ≤ Z.card * Z.card ∧
      PFree (if G.color then G.firstPolytope else G.secondPolytope) Z := by
  classical
  by_cases h : ∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      G.middle.card ≤ Z.card * Z.card ∧ PFree G.firstPolytope Z
  · obtain ⟨Z, hZ⟩ := h
    refine ⟨Z, hZ.1, hZ.2.1, ?_⟩
    simpa [MiddleTripleGadget.color, h] using hZ.2.2
  · rcases G.exists_large_free_subset_exact with hfirst | hsecond
    · exact (h hfirst).elim
    · obtain ⟨Z, hZ⟩ := hsecond
      refine ⟨Z, hZ.1, hZ.2.1, ?_⟩
      simpa [MiddleTripleGadget.color, h] using hZ.2.2

/-- Integer-square-root version used by the later estimates. -/
theorem MiddleTripleGadget.color_spec (G : MiddleTripleGadget) :
    ∃ Z : Finset (Point 3), Z ⊆ G.middle ∧
      Nat.sqrt G.middle.card ≤ Z.card ∧
      PFree (if G.color then G.firstPolytope else G.secondPolytope) Z := by
  obtain ⟨Z, hZmid, hZsq, hZfree⟩ := G.color_spec_exact
  exact ⟨Z, hZmid, sqrt_le_of_card_le_square hZsq, hZfree⟩

/-- A family assigning geometric data only to genuine triples. -/
abbrev TripleGadgetFamily (ι : Type*) [DecidableEq ι] :=
  ∀ J : Finset ι, J.card = 3 → MiddleTripleGadget

/-- Triple Ramsey makes the same polytope choice for every triple in a
large index clique, while retaining the actual square-root-sized free set
for each triple. -/
theorem exists_monochromatic_gadget_clique
    {ι : Type*} [DecidableEq ι]
    (m : ℕ) (I : Finset ι) (hI : uniformRamseyBound 3 m ≤ I.card)
    (G : TripleGadgetFamily ι) :
    ∃ H : Finset ι, H ⊆ I ∧ H.card = m ∧ ∃ b : Bool,
      ∀ J : Finset ι, J ⊆ H → ∀ hJ : J.card = 3,
        ∃ Z : Finset (Point 3), Z ⊆ (G J hJ).middle ∧
          (G J hJ).middle.card ≤ Z.card * Z.card ∧
          PFree (if b then (G J hJ).firstPolytope
            else (G J hJ).secondPolytope) Z := by
  classical
  let color : Finset ι → Bool := fun J =>
    if hJ : J.card = 3 then (G J hJ).color else false
  obtain ⟨H, hHI, hHcard, b, hb⟩ :=
    uniformRamseyBound_spec 3 m I hI color
  refine ⟨H, hHI, hHcard, b, ?_⟩
  intro J hJH hJcard
  obtain ⟨Z, hZmid, hZcard, hZfree⟩ := (G J hJcard).color_spec_exact
  refine ⟨Z, hZmid, hZcard, ?_⟩
  have hcolor : (G J hJcard).color = b := by
    simpa [color, hJcard] using hb J hJH hJcard
  rw [hcolor] at hZfree
  exact hZfree

/-! ## The alternating triples in an odd monochromatic clique -/

/-- Position immediately before the selected middle position. -/
def alternatingLeftPosition {q : ℕ} (r : Fin q) : Fin (2 * q + 1) :=
  ⟨2 * r.1, by omega⟩

/-- The selected even cluster in the source's one-based numbering (an odd
position in Lean's zero-based indexing). -/
def alternatingMiddlePosition {q : ℕ} (r : Fin q) : Fin (2 * q + 1) :=
  ⟨2 * r.1 + 1, by omega⟩

/-- The common final member of all alternating triples. -/
def alternatingLastPosition (q : ℕ) : Fin (2 * q + 1) :=
  ⟨2 * q, by omega⟩

/-- The triple consisting of a consecutive left/middle pair and the last
point of an odd clique. -/
def alternatingTriple {q : ℕ} {ι : Type*} [DecidableEq ι]
    (j : Fin (2 * q + 1) ↪ ι) (r : Fin q) : Finset ι :=
  {j (alternatingLeftPosition r), j (alternatingMiddlePosition r),
    j (alternatingLastPosition q)}

theorem alternatingTriple_card {q : ℕ} {ι : Type*} [DecidableEq ι]
    (j : Fin (2 * q + 1) ↪ ι) (r : Fin q) :
    (alternatingTriple j r).card = 3 := by
  have hlm : j (alternatingLeftPosition r) ≠ j (alternatingMiddlePosition r) := by
    intro h
    have h' := j.injective h
    have hv := congrArg Fin.val h'
    change 2 * r.1 = 2 * r.1 + 1 at hv
    omega
  have hll : j (alternatingLeftPosition r) ≠ j (alternatingLastPosition q) := by
    intro h
    have h' := j.injective h
    have hv := congrArg Fin.val h'
    change 2 * r.1 = 2 * q at hv
    omega
  have hml : j (alternatingMiddlePosition r) ≠ j (alternatingLastPosition q) := by
    intro h
    have h' := j.injective h
    have hv := congrArg Fin.val h'
    change 2 * r.1 + 1 = 2 * q at hv
    omega
  simp [alternatingTriple, hlm, hll, hml]

/-- The gadget belonging to one of the canonical alternating triples. -/
def alternatingGadget {q : ℕ} {ι : Type*} [DecidableEq ι]
    (G : TripleGadgetFamily ι) (j : Fin (2 * q + 1) ↪ ι) (r : Fin q) :
    MiddleTripleGadget :=
  G (alternatingTriple j r) (alternatingTriple_card j r)

/-- A monochromatic odd clique supplies a free set on every alternating
middle cluster, with the same choice of background polyhedron. -/
theorem exists_alternating_free_subsets_of_monochromatic_clique
    {q : ℕ} {ι : Type*} [DecidableEq ι]
    (G : TripleGadgetFamily ι)
    (H : Finset ι) (j : Fin (2 * q + 1) ↪ ι)
    (hjH : ∀ p, j p ∈ H) (b : Bool)
    (hmono : ∀ J : Finset ι, J ⊆ H → ∀ hJ : J.card = 3,
      (G J hJ).color = b) :
    ∀ r : Fin q, ∃ Z : Finset (Point 3),
      Z ⊆ (alternatingGadget G j r).middle ∧
      (alternatingGadget G j r).middle.card ≤ Z.card * Z.card ∧
      PFree
        (if b then (alternatingGadget G j r).firstPolytope
          else (alternatingGadget G j r).secondPolytope) Z := by
  intro r
  have hJH : alternatingTriple j r ⊆ H := by
    intro x hx
    simp only [alternatingTriple, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hjH _
    · exact hjH _
    · exact hjH _
  obtain ⟨Z, hZmid, hZcard, hZfree⟩ :=
    (alternatingGadget G j r).color_spec_exact
  refine ⟨Z, hZmid, hZcard, ?_⟩
  rw [hmono _ hJH (alternatingTriple_card j r)] at hZfree
  exact hZfree

/-! ## Proposition 2.1 on alternating clusters and cap assembly -/

/-- Inputs retained after the monochromatic triple-clique step.  Each
`freeSet i` lies in a distinct middle cluster, is free from its selected
background polyhedron, and comes with the unconditional three-edge
projection certificate of Proposition 2.1.  The containment field is (4.8). -/
structure AlternatingFreeFamily (q : ℕ) (X : Finset (Point 3)) where
  middle : Fin q → Finset (Point 3)
  background : Fin q → Set (Point 3)
  freeSet : Fin q → Finset (Point 3)
  middle_subset : ∀ i, middle i ⊆ X
  free_subset_middle : ∀ i, freeSet i ⊆ middle i
  middle_card_le_free_square : ∀ i,
    (middle i).card ≤ (freeSet i).card * (freeSet i).card
  free_disjoint : ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint freeSet
  free : ∀ i, PFree (background i) (freeSet i)
  certificate : ∀ i, ProjectionOrderCertificate (background i) (freeSet i) (Fin 3)
  other_free_subset : ∀ i j, i ≠ j →
    (↑(freeSet j) : Set (Point 3)) ⊆ background i

theorem AlternatingFreeFamily.free_subset
    {q : ℕ} {X : Finset (Point 3)} (F : AlternatingFreeFamily q X) (i : Fin q) :
    F.freeSet i ⊆ X :=
  (F.free_subset_middle i).trans (F.middle_subset i)

theorem AlternatingFreeFamily.sqrt_middle_le_free_card
    {q : ℕ} {X : Finset (Point 3)} (F : AlternatingFreeFamily q X) (i : Fin q) :
    Nat.sqrt (F.middle i).card ≤ (F.freeSet i).card :=
  sqrt_le_of_card_le_square (F.middle_card_le_free_square i)

/-- If every alternating free set clears the cups--caps threshold, then
either Proposition 2.1 directly finds `n` convex points or its cap branches
assemble to at least `n` convex points. -/
theorem AlternatingFreeFamily.containsConvexSubset
    {q n a : ℕ} {X : Finset (Point 3)}
    (F : AlternatingFreeFamily q X)
    (ha : 2 ≤ a) (hn : 2 ≤ n)
    (hcount : n ≤ q * a)
    (hlarge : ∀ i,
      Nat.choose (a + n - 4) (a - 2) ^ 3 < (F.freeSet i).card) :
    ContainsConvexSubset 3 n X := by
  classical
  have hbranch (i : Fin q) :
      (∃ C : Finset (Point 3), C ⊆ F.freeSet i ∧ C.card = a ∧
        PCap (F.background i) C) ∨
      (∃ C : Finset (Point 3), C ⊆ F.freeSet i ∧ C.card = n ∧
        InConvexPosition C) :=
    pohoata_zakharov_prop_two_one_three_edges (F.certificate i)
      (F.free i) ha hn (hlarge i)
  by_cases hdirect : ∃ i : Fin q, ∃ C : Finset (Point 3),
      C ⊆ F.freeSet i ∧ C.card = n ∧ InConvexPosition C
  · obtain ⟨i, C, hCZ, hCcard, hCconv⟩ := hdirect
    exact ⟨C, hCZ.trans (F.free_subset i), hCcard, hCconv⟩
  ·
    have hcap (i : Fin q) : ∃ C : Finset (Point 3),
        C ⊆ F.freeSet i ∧ C.card = a ∧ PCap (F.background i) C := by
      rcases hbranch i with h | h
      · exact h
      · exact (hdirect ⟨i, h⟩).elim
    choose K hKsubset hKcard hKcap using hcap
    have hKdisj : ((Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint K := by
      intro i - j - hij
      exact (F.free_disjoint (Finset.mem_univ i) (Finset.mem_univ j) hij).mono
        (hKsubset i) (hKsubset j)
    have hUcard : (Finset.univ.biUnion K).card = q * a := by
      rw [Finset.card_biUnion hKdisj]
      simp [hKcard]
    have hconvU : ContainsConvexSubset 3 n (Finset.univ.biUnion K) := by
      apply containsConvexSubset_of_biUnion_pCaps F.background K hKcap
      · intro i j hij
        exact (hKsubset j).trans (F.other_free_subset i j hij)
      · rw [hUcard]
        exact hcount
    obtain ⟨Y, hYU, hYcard, hYconv⟩ := hconvU
    refine ⟨Y, ?_, hYcard, hYconv⟩
    intro y hy
    obtain ⟨i, -, hyi⟩ := Finset.mem_biUnion.mp (hYU hy)
    exact F.free_subset i (hKsubset i hyi)

/-- Contrapositive form of the previous theorem, exactly matching (4.13):
if the ambient set has no convex `n`-subset, at least one alternating free
set is at most the cube of the relevant binomial coefficient. -/
theorem AlternatingFreeFamily.exists_binomially_bounded_freeSet
    {q n a : ℕ} {X : Finset (Point 3)}
    (F : AlternatingFreeFamily q X)
    (ha : 2 ≤ a) (hn : 2 ≤ n)
    (hcount : n ≤ q * a)
    (hno : ¬ ContainsConvexSubset 3 n X) :
    ∃ i : Fin q,
      (F.freeSet i).card ≤ Nat.choose (a + n - 4) (a - 2) ^ 3 := by
  classical
  by_contra h
  apply hno
  apply F.containsConvexSubset ha hn hcount
  intro i
  exact Nat.lt_of_not_ge (fun hle => h ⟨i, hle⟩)

/-- Combined lower and upper bound furnished by (4.12)--(4.13). -/
theorem AlternatingFreeFamily.exists_sqrt_to_binomial_bound
    {q n a : ℕ} {X : Finset (Point 3)}
    (F : AlternatingFreeFamily q X)
    (ha : 2 ≤ a) (hn : 2 ≤ n)
    (hcount : n ≤ q * a)
    (hno : ¬ ContainsConvexSubset 3 n X) :
    ∃ i : Fin q,
      Nat.sqrt (F.middle i).card ≤ (F.freeSet i).card ∧
      (F.freeSet i).card ≤ Nat.choose (a + n - 4) (a - 2) ^ 3 := by
  obtain ⟨i, hi⟩ := F.exists_binomially_bounded_freeSet ha hn hcount hno
  exact ⟨i, F.sqrt_middle_le_free_card i, hi⟩

/-- The decisive integer inequality obtained by eliminating the selected
free set between the square-root lower bound and the binomial upper bound. -/
theorem AlternatingFreeFamily.exists_sqrt_middle_le_binomial_cube
    {q n a : ℕ} {X : Finset (Point 3)}
    (F : AlternatingFreeFamily q X)
    (ha : 2 ≤ a) (hn : 2 ≤ n)
    (hcount : n ≤ q * a)
    (hno : ¬ ContainsConvexSubset 3 n X) :
    ∃ i : Fin q,
      Nat.sqrt (F.middle i).card ≤
        Nat.choose (a + n - 4) (a - 2) ^ 3 := by
  obtain ⟨i, hlo, hhi⟩ := F.exists_sqrt_to_binomial_bound ha hn hcount hno
  exact ⟨i, hlo.trans hhi⟩

/-- Fully integer, non-rounded version of the decisive bound: squaring
(4.15) bounds a middle cluster by the square of the binomial cube. -/
theorem AlternatingFreeFamily.exists_middle_card_le_binomial_cube_square
    {q n a : ℕ} {X : Finset (Point 3)}
    (F : AlternatingFreeFamily q X)
    (ha : 2 ≤ a) (hn : 2 ≤ n)
    (hcount : n ≤ q * a)
    (hno : ¬ ContainsConvexSubset 3 n X) :
    ∃ i : Fin q,
      (F.middle i).card ≤
        (Nat.choose (a + n - 4) (a - 2) ^ 3) *
          (Nat.choose (a + n - 4) (a - 2) ^ 3) := by
  obtain ⟨i, hi⟩ := F.exists_binomially_bounded_freeSet ha hn hcount hno
  refine ⟨i, (F.middle_card_le_free_square i).trans ?_⟩
  exact Nat.mul_le_mul hi hi

end

end Erdos651
