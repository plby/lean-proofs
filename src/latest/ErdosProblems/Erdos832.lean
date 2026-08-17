/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle, OpenAI Codex
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Erdős Problem 832

The proposed eventual lower bound for the number of edges in an `r`-uniform
hypergraph of chromatic number `k` is false.  We formalize the assertion with
its original quantifiers and disprove it at `r = 4`.

The counterexamples are complements of a concrete Giraud-type
`K₅⁽⁴⁾`-free construction.  Their vertices are two copies of `𝔽₂^d`; all
four-sets on one side and the even `2 × 2` rectangles are edges.  Every five
vertices contain an edge, while the bilinear form on `𝔽₂^d` gives the required
edge count.

The detailed mathematical proof and the Leanization map are in `tex/832.tex`.
-/

namespace Erdos832

open scoped BigOperators
open Finset

/-- A finite simple hypergraph.  Isolated vertices are retained in `V`, which
is important for stating the equality clause of Problem 832 exactly. -/
structure FiniteHypergraph where
  V : Type
  fintypeV : Fintype V
  decidableEqV : DecidableEq V
  edges : Finset (Finset V)

attribute [instance] FiniteHypergraph.fintypeV FiniteHypergraph.decidableEqV

namespace FiniteHypergraph

/-- Every edge has cardinality `r`. -/
def IsUniform (H : FiniteHypergraph) (r : ℕ) : Prop :=
  ∀ e ∈ H.edges, e.card = r

/-- A coloring is proper when every edge contains two differently colored
vertices. -/
def ProperColoring (H : FiniteHypergraph) {κ : Type} (c : H.V → κ) : Prop :=
  ∀ e ∈ H.edges, ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y

/-- `H` admits a proper coloring with colors `Fin k`. -/
def Colorable (H : FiniteHypergraph) (k : ℕ) : Prop :=
  ∃ c : H.V → Fin k, H.ProperColoring c

/-- The exact, minimum-color meaning of `χ(H) = k`, stated without making a
partial `Nat.find` definition for hypergraphs containing singleton edges. -/
def HasChromaticNumber (H : FiniteHypergraph) (k : ℕ) : Prop :=
  H.Colorable k ∧ ∀ j < k, ¬H.Colorable j

/-- The equality case in Problem 832: the ambient vertex set has size `m` and
the edge family is the complete `r`-uniform hypergraph on it. -/
def IsCompleteOn (H : FiniteHypergraph) (r m : ℕ) : Prop :=
  Fintype.card H.V = m ∧
    H.edges = (Finset.univ : Finset H.V).powersetCard r

/-- Change only the edge family of a finite hypergraph. -/
def withEdges (H : FiniteHypergraph) (E : Finset (Finset H.V)) : FiniteHypergraph where
  V := H.V
  fintypeV := H.fintypeV
  decidableEqV := H.decidableEqV
  edges := E

@[simp] lemma withEdges_edges (H : FiniteHypergraph) (E : Finset (Finset H.V)) :
    (H.withEdges E).edges = E := rfl

lemma properColoring_mono {H : FiniteHypergraph} {E E' : Finset (Finset H.V)}
    {κ : Type} {c : H.V → κ} (hsub : E' ⊆ E)
    (hc : (H.withEdges E).ProperColoring c) :
    (H.withEdges E').ProperColoring c := by
  intro e he
  exact hc e (hsub he)

lemma colorable_edges_mono {H : FiniteHypergraph} {E E' : Finset (Finset H.V)}
    {k : ℕ} (hsub : E' ⊆ E) (hc : (H.withEdges E).Colorable k) :
    (H.withEdges E').Colorable k := by
  obtain ⟨c, hc⟩ := hc
  exact ⟨c, properColoring_mono hsub hc⟩

lemma colorable_mono {H : FiniteHypergraph} {a b : ℕ} (hab : a ≤ b)
    (h : H.Colorable a) : H.Colorable b := by
  obtain ⟨c, hc⟩ := h
  let ι : Fin a ↪ Fin b := ⟨Fin.castLE hab, Fin.castLE_injective hab⟩
  refine ⟨fun v ↦ ι (c v), ?_⟩
  intro e he
  obtain ⟨x, hx, y, hy, hxy⟩ := hc e he
  exact ⟨x, hx, y, hy, fun hEq ↦ hxy (ι.injective hEq)⟩

lemma hasChromaticNumber_of_not_pred {H : FiniteHypergraph} {k : ℕ}
    (hk : 1 ≤ k) (hcol : H.Colorable k) (hnot : ¬H.Colorable (k - 1)) :
    H.HasChromaticNumber k := by
  refine ⟨hcol, ?_⟩
  intro j hj hcolj
  apply hnot
  exact colorable_mono (by omega) hcolj

/-- Inclusion-minimal extraction from a non-colorable finite edge family. -/
lemma exists_edgeMinimal_not_colorable (H : FiniteHypergraph) (q : ℕ)
    {E : Finset (Finset H.V)} (hE : ¬(H.withEdges E).Colorable q) :
    ∃ E' ⊆ E, ¬(H.withEdges E').Colorable q ∧
      ∀ e ∈ E', (H.withEdges (E'.erase e)).Colorable q := by
  induction E using Finset.strongInductionOn with
  | _ E ih =>
      by_cases hsmaller : ∃ e ∈ E, ¬(H.withEdges (E.erase e)).Colorable q
      · obtain ⟨e, he, hbad⟩ := hsmaller
        obtain ⟨E', hsub, hbad', hminimal⟩ := ih (E.erase e)
          (Finset.erase_ssubset he) hbad
        exact ⟨E', hsub.trans (Finset.erase_subset _ _), hbad', hminimal⟩
      · refine ⟨E, Subset.rfl, hE, ?_⟩
        intro e he
        exact Classical.byContradiction fun h ↦ hsmaller ⟨e, he, h⟩

lemma empty_colorable (H : FiniteHypergraph) {q : ℕ} (hq : 0 < q) :
    (H.withEdges ∅).Colorable q := by
  let c : H.V → Fin q := fun _ ↦ ⟨0, hq⟩
  refine ⟨c, ?_⟩
  change ∀ e ∈ (∅ : Finset (Finset H.V)), ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y
  intro e he
  have hne : (∅ : Finset (Finset H.V)).Nonempty := ⟨e, he⟩
  exact (Finset.not_nonempty_iff_eq_empty.mpr rfl hne).elim

/-- An edge-minimal hypergraph that is not `(k-1)`-colorable is `k`-colorable:
remove one edge, color with the old colors, and give one vertex of that edge a
fresh color. -/
lemma colorable_of_edgeMinimal {H : FiniteHypergraph} {r k : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) (huniform : H.IsUniform r)
    (hbad : ¬H.Colorable (k - 1))
    (hminimal : ∀ e ∈ H.edges, (H.withEdges (H.edges.erase e)).Colorable (k - 1)) :
    H.Colorable k := by
  classical
  have hne : H.edges.Nonempty := by
    by_contra hempty
    have hEmpty : H.edges = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    apply hbad
    let c : H.V → Fin (k - 1) := fun _ ↦ ⟨0, by omega⟩
    refine ⟨c, ?_⟩
    intro e he
    rw [hEmpty] at he
    simpa using he
  obtain ⟨e, he⟩ := hne
  obtain ⟨v, hv⟩ : e.Nonempty := by
    have hcard := huniform e he
    exact Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := hminimal e he
  let cH : H.V → Fin (k - 1) := fun x ↦ c x
  have hcH : ∀ f ∈ H.edges.erase e, ∃ x ∈ f, ∃ y ∈ f, cH x ≠ cH y := by
    intro f hf
    exact hc f hf
  let old : Fin (k - 1) ↪ Fin k := ⟨Fin.castLE (by omega), Fin.castLE_injective (by omega)⟩
  let fresh : Fin k := ⟨k - 1, by omega⟩
  refine ⟨fun x ↦ if x = v then fresh else old (cH x), ?_⟩
  intro f hf
  by_cases hvf : v ∈ f
  · have hfcard := huniform f hf
    obtain ⟨w, hwf, hwv⟩ : ∃ w ∈ f, w ≠ v := by
      by_contra h
      have hsub : f ⊆ {v} := by
        intro x hx
        have hxv : x = v := by
          by_contra hxv
          exact h ⟨x, hx, hxv⟩
        simpa [hxv]
      have : f.card ≤ 1 := by simpa using Finset.card_le_card hsub
      omega
    refine ⟨v, hvf, w, hwf, ?_⟩
    simp only [if_pos rfl, if_neg hwv]
    intro hEq
    have hval := congrArg Fin.val hEq
    simp only [fresh, old, Fin.castLE, Function.Embedding.coeFn_mk] at hval
    exact (Nat.ne_of_lt (cH w).isLt) hval.symm
  · have hfe : f ≠ e := by
      intro hEq
      apply hvf
      simpa [hEq] using hv
    have hferase : f ∈ H.edges.erase e := Finset.mem_erase.mpr ⟨hfe, hf⟩
    obtain ⟨x, hxf, y, hyf, hxy⟩ := hcH f hferase
    refine ⟨x, hxf, y, hyf, ?_⟩
    have hxv : x ≠ v := fun h ↦ hvf (h ▸ hxf)
    have hyv : y ≠ v := fun h ↦ hvf (h ▸ hyf)
    simp only [if_neg hxv, if_neg hyv]
    exact fun hEq ↦ hxy (old.injective hEq)

/-- Every non-`(k-1)`-colorable `r`-uniform finite hypergraph, for `r,k ≥ 2`,
has a spanning subhypergraph of exact chromatic number `k`. -/
theorem exists_spanning_exact_chromatic {H : FiniteHypergraph} {r k : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k) (huniform : H.IsUniform r)
    (hbad : ¬H.Colorable (k - 1)) :
    ∃ H' : FiniteHypergraph,
      H'.V = H.V ∧ H'.edges.card ≤ H.edges.card ∧ H'.IsUniform r ∧
        H'.HasChromaticNumber k := by
  obtain ⟨E', hsub, hbad', hminimal⟩ :=
    exists_edgeMinimal_not_colorable H (k - 1) hbad
  let H' := H.withEdges E'
  have huniform' : H'.IsUniform r := by
    intro e he
    exact huniform e (hsub he)
  have hcol : H'.Colorable k :=
    colorable_of_edgeMinimal hr hk huniform' hbad' hminimal
  exact ⟨H', rfl, Finset.card_le_card hsub, huniform',
    hasChromaticNumber_of_not_pred (by omega) hcol hbad'⟩

end FiniteHypergraph

/-- The exact eventual assertion asked in Erdős Problem 832, including the
claimed uniqueness of equality. -/
def Erdos832Claim : Prop :=
  ∀ r : ℕ, 3 ≤ r → ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ H : FiniteHypergraph,
      H.IsUniform r → H.HasChromaticNumber k →
        ((r - 1) * (k - 1) + 1).choose r ≤ H.edges.card ∧
          (H.edges.card = ((r - 1) * (k - 1) + 1).choose r →
            H.IsCompleteOn r ((r - 1) * (k - 1) + 1))

/-! ## The explicit binary construction -/

abbrev Code (d : ℕ) := Fin d → Bool

def dot {d : ℕ} (x y : Code d) : Bool := ∑ i, x i * y i

def toggle {d : ℕ} (i : Fin d) (y : Code d) : Code d :=
  fun j => if j = i then !y j else y j

lemma toggle_toggle {d : ℕ} (i : Fin d) (y : Code d) :
    toggle i (toggle i y) = y := by
  funext j
  by_cases h : j = i <;> simp [toggle, h]

lemma dot_toggle {d : ℕ} (x y : Code d) (i : Fin d) :
    dot x (toggle i y) = dot x y + x i := by
  have hb (b : Bool) : (!b : Bool) = b + true := by cases b <;> decide
  calc
    dot x (toggle i y) = ∑ j, (x j * y j + if j = i then x i else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hji : j = i
      · subst j
        simp only [toggle, if_pos, hb]
        rw [mul_add]
        change x i * y i + x i * 1 = x i * y i + x i
        ring
      · simp [toggle, hji]
    _ = (∑ j, x j * y j) + ∑ j, (if j = i then x i else false) :=
      Finset.sum_add_distrib
    _ = dot x y + x i := by
      have hz : (false : Bool) = 0 := by decide
      simp only [hz]
      have hs : (∑ j : Fin d, if j = i then x i else 0) = x i := by
        simpa using (Fintype.sum_ite_eq i (fun _ : Fin d ↦ x i))
      rw [hs]
      change dot x y + x i = dot x y + x i
      rfl

def pairs (d : ℕ) : Finset (Finset (Code d)) :=
  (Finset.univ : Finset (Code d)).powersetCard 2

def pairLabel {d : ℕ} (p : Finset (Code d)) (y : Code d) : Bool :=
  ∑ x ∈ p, dot x y

lemma pairLabel_toggle {d : ℕ} {p : Finset (Code d)} (hp : p ∈ pairs d) :
    ∃ i : Fin d, ∀ y, pairLabel p (toggle i y) = !pairLabel p y := by
  have hpcard : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
  obtain ⟨x, x', hxx', rfl⟩ := Finset.card_eq_two.mp hpcard
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ x' i := by
    simpa [Function.ne_iff] using hxx'
  refine ⟨i, fun y ↦ ?_⟩
  simp only [pairLabel, Finset.sum_pair hxx', dot_toggle]
  have diff_add_true (a b : Bool) (h : a ≠ b) : a + b = true := by
    cases a <;> cases b
    · exact (h rfl).elim
    · decide
    · decide
    · exact (h rfl).elim
  have hbits : x i + x' i = true := diff_add_true _ _ hi
  have hnot (b : Bool) : (!b : Bool) = b + true := by cases b <;> decide
  rw [hnot, ← hbits]
  ring

def fiber {d : ℕ} (p : Finset (Code d)) (b : Bool) : Finset (Code d) :=
  Finset.univ.filter fun y ↦ pairLabel p y = b

lemma fiber_toggle_mem {d : ℕ} {p : Finset (Code d)} (_hp : p ∈ pairs d)
    {i : Fin d} (hi : ∀ y, pairLabel p (toggle i y) = !pairLabel p y)
    {b : Bool} {y : Code d} : y ∈ fiber p b → toggle i y ∈ fiber p (!b) := by
  intro hy
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
  rw [hi, hy]

lemma fiber_card_eq {d : ℕ} {p : Finset (Code d)} (hp : p ∈ pairs d) :
    (fiber p false).card = (fiber p true).card := by
  obtain ⟨i, hi⟩ := pairLabel_toggle hp
  apply Finset.card_bij (fun y _ ↦ toggle i y)
  · intro y hy
    simpa using fiber_toggle_mem hp hi hy
  · intro a ha b hb hab
    have := congrArg (toggle i) hab
    simpa only [toggle_toggle] using this
  · intro y hy
    refine ⟨toggle i y, ?_, ?_⟩
    · have hmem : toggle i y ∈ fiber p (!true) := fiber_toggle_mem hp hi hy
      simpa using hmem
    · exact toggle_toggle i y

lemma bool_add_eq_false_iff (a b : Bool) : a + b = false ↔ a = b := by
  cases a <;> cases b <;> decide

def evenColumns {d : ℕ} (p : Finset (Code d)) : Finset (Finset (Code d)) :=
  (pairs d).filter fun cp ↦ (∑ y ∈ cp, pairLabel p y) = false

lemma evenColumns_eq {d : ℕ} {p : Finset (Code d)} :
    evenColumns p =
      (fiber p false).powersetCard 2 ∪ (fiber p true).powersetCard 2 := by
  ext cp
  simp only [evenColumns, Finset.mem_filter, pairs, Finset.mem_powersetCard,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hsum⟩
    obtain ⟨y, z, hyz, rfl⟩ := Finset.card_eq_two.mp hcard
    simp only [Finset.sum_pair hyz] at hsum
    have heq : pairLabel p y = pairLabel p z :=
      (bool_add_eq_false_iff _ _).mp hsum
    cases hb : pairLabel p y
    · left
      refine ⟨?_, Finset.card_pair hyz⟩
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · simp [fiber, hb]
      · simp [fiber, ← heq, hb]
    · right
      refine ⟨?_, Finset.card_pair hyz⟩
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · simp [fiber, hb]
      · simp [fiber, ← heq, hb]
  · rintro (hfalse | htrue)
    · obtain ⟨hsub, hcard⟩ := hfalse
      refine ⟨⟨hsub.trans (Finset.filter_subset _ _), hcard⟩, ?_⟩
      obtain ⟨y, z, hyz, rfl⟩ := Finset.card_eq_two.mp hcard
      have hy : pairLabel p y = false := (Finset.mem_filter.mp (hsub (by simp))).2
      have hz : pairLabel p z = false := (Finset.mem_filter.mp (hsub (by simp))).2
      simp [Finset.sum_pair hyz, hy, hz]
      decide
    · obtain ⟨hsub, hcard⟩ := htrue
      refine ⟨⟨hsub.trans (Finset.filter_subset _ _), hcard⟩, ?_⟩
      obtain ⟨y, z, hyz, rfl⟩ := Finset.card_eq_two.mp hcard
      have hy : pairLabel p y = true := (Finset.mem_filter.mp (hsub (by simp))).2
      have hz : pairLabel p z = true := (Finset.mem_filter.mp (hsub (by simp))).2
      simp [Finset.sum_pair hyz, hy, hz]
      decide

lemma card_evenColumns_bound {d : ℕ} {p : Finset (Code d)} (hp : p ∈ pairs d) :
    4 * (evenColumns p).card ≤ (Fintype.card (Code d)) ^ 2 := by
  rw [evenColumns_eq]
  calc
    4 * ((fiber p false).powersetCard 2 ∪
        (fiber p true).powersetCard 2).card
        ≤ 4 * ((fiber p false).powersetCard 2).card +
          4 * ((fiber p true).powersetCard 2).card := by
            have h := Finset.card_union_le ((fiber p false).powersetCard 2)
              ((fiber p true).powersetCard 2)
            omega
    _ = 8 * (fiber p false).card.choose 2 := by
      simp only [Finset.card_powersetCard, fiber_card_eq hp]
      omega
    _ ≤ (Fintype.card (Code d)) ^ 2 := by
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Code d)))
        (fun y : Code d ↦ pairLabel p y = false)
      have htrue : (Finset.univ.filter fun y : Code d ↦ ¬pairLabel p y = false) =
          fiber p true := by
        ext y
        simp [fiber]
      have hsum : (fiber p false).card + (fiber p true).card =
          Fintype.card (Code d) := by
        simpa [fiber, htrue] using hpartition
      have hbal := fiber_card_eq hp
      have hchoose : 2 * (fiber p false).card.choose 2 =
          (fiber p false).card * ((fiber p false).card - 1) := by
        have h := Nat.descFactorial_eq_factorial_mul_choose
          (fiber p false).card 2
        norm_num [Nat.descFactorial, Nat.factorial] at h
        calc
          2 * (fiber p false).card.choose 2 =
              ((fiber p false).card - 1) * (fiber p false).card := h.symm
          _ = (fiber p false).card * ((fiber p false).card - 1) :=
            Nat.mul_comm _ _
      rw [← hsum, ← hbal]
      have hrewrite : 8 * (fiber p false).card.choose 2 =
          4 * ((fiber p false).card * ((fiber p false).card - 1)) := by
        calc
          8 * (fiber p false).card.choose 2 =
              4 * (2 * (fiber p false).card.choose 2) := by ring
          _ = 4 * ((fiber p false).card * ((fiber p false).card - 1)) := by
            rw [hchoose]
      rw [hrewrite]
      have hle : (fiber p false).card * ((fiber p false).card - 1) ≤
          (fiber p false).card * (fiber p false).card :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      calc
        4 * ((fiber p false).card * ((fiber p false).card - 1)) ≤
            4 * ((fiber p false).card * (fiber p false).card) :=
          Nat.mul_le_mul_left _ hle
        _ = ((fiber p false).card + (fiber p false).card) ^ 2 := by ring

def evenRectParams (d : ℕ) : Finset (Sigma fun _ : Finset (Code d) ↦ Finset (Code d)) :=
  (pairs d).sigma fun p ↦ evenColumns p

lemma card_pairs (d : ℕ) :
    (pairs d).card = (Fintype.card (Code d)).choose 2 := by
  simp [pairs]

lemma two_mul_choose_two (a : ℕ) : 2 * a.choose 2 = a * (a - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose a 2
  norm_num [Nat.descFactorial, Nat.factorial] at h
  calc
    2 * a.choose 2 = (a - 1) * a := h.symm
    _ = a * (a - 1) := Nat.mul_comm _ _

lemma twentyFour_mul_choose_four (a : ℕ) :
    24 * a.choose 4 = a * (a - 1) * (a - 2) * (a - 3) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose a 4
  norm_num [Nat.descFactorial, Nat.factorial] at h
  calc
    24 * a.choose 4 = (a - 3) * ((a - 2) * ((a - 1) * a)) := h.symm
    _ = a * (a - 1) * (a - 2) * (a - 3) := by ac_rfl

lemma choose_four_bound (a : ℕ) : 24 * a.choose 4 ≤ a ^ 4 := by
  rw [twentyFour_mul_choose_four]
  have h1 : a - 1 ≤ a := Nat.sub_le _ _
  have h2 : a - 2 ≤ a := Nat.sub_le _ _
  have h3 : a - 3 ≤ a := Nat.sub_le _ _
  calc
    a * (a - 1) * (a - 2) * (a - 3) ≤ a * a * a * a := by
      gcongr
    _ = a ^ 4 := by ring

lemma card_evenRectParams_bound (d : ℕ) :
    8 * (evenRectParams d).card ≤ (Fintype.card (Code d)) ^ 4 := by
  let q := Fintype.card (Code d)
  have hsum : 4 * (evenRectParams d).card ≤ (pairs d).card * q ^ 2 := by
    rw [evenRectParams, Finset.card_sigma]
    calc
      4 * ∑ p ∈ pairs d, (evenColumns p).card =
          ∑ p ∈ pairs d, 4 * (evenColumns p).card := by
            simp [Finset.mul_sum]
      _ ≤ ∑ _p ∈ pairs d, q ^ 2 := by
        apply Finset.sum_le_sum
        intro p hp
        exact card_evenColumns_bound hp
      _ = (pairs d).card * q ^ 2 := by simp
  have hpairs : 2 * (pairs d).card ≤ q ^ 2 := by
    rw [card_pairs, two_mul_choose_two]
    exact calc
      q * (q - 1) ≤ q * q := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = q ^ 2 := by ring
  calc
    8 * (evenRectParams d).card = 2 * (4 * (evenRectParams d).card) := by ring
    _ ≤ 2 * ((pairs d).card * q ^ 2) := Nat.mul_le_mul_left _ hsum
    _ = (2 * (pairs d).card) * q ^ 2 := by ring
    _ ≤ q ^ 2 * q ^ 2 := Nat.mul_le_mul_right _ hpairs
    _ = q ^ 4 := by ring

abbrev Vertex (d : ℕ) := Bool × Code d

def fours (d : ℕ) : Finset (Finset (Code d)) :=
  (Finset.univ : Finset (Code d)).powersetCard 4

def sideSet {d : ℕ} (b : Bool) (s : Finset (Code d)) : Finset (Vertex d) :=
  s.image fun x ↦ (b, x)

lemma sideSet_card {d : ℕ} (b : Bool) (s : Finset (Code d)) :
    (sideSet b s).card = s.card := by
  exact Finset.card_image_of_injective s fun _ _ h ↦ congrArg Prod.snd h

lemma sideSet_disjoint {d : ℕ} (s t : Finset (Code d)) :
    Disjoint (sideSet false s) (sideSet true t) := by
  rw [Finset.disjoint_left]
  intro v hvf hvt
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hvf
  obtain ⟨y, hy, hEq⟩ := Finset.mem_image.mp hvt
  exact Bool.false_ne_true (congrArg Prod.fst hEq.symm)

def rectSet {d : ℕ}
    (z : Sigma fun _ : Finset (Code d) ↦ Finset (Code d)) : Finset (Vertex d) :=
  sideSet false z.1 ∪ sideSet true z.2

lemma rectSet_card {d : ℕ}
    {z : Sigma fun _ : Finset (Code d) ↦ Finset (Code d)}
    (hz : z ∈ evenRectParams d) : (rectSet z).card = 4 := by
  have hz' := Finset.mem_sigma.mp hz
  have hp : z.1.card = 2 := (Finset.mem_powersetCard.mp hz'.1).2
  have hcpairs : z.2 ∈ pairs d := (Finset.mem_filter.mp hz'.2).1
  have hq : z.2.card = 2 := (Finset.mem_powersetCard.mp hcpairs).2
  rw [rectSet, Finset.card_union_of_disjoint (sideSet_disjoint _ _),
    sideSet_card, sideSet_card, hp, hq]

def constructionEdges (d : ℕ) : Finset (Finset (Vertex d)) :=
  ((fours d).image (sideSet false) ∪ (fours d).image (sideSet true)) ∪
    (evenRectParams d).image rectSet

lemma construction_uniform (d : ℕ) :
    ∀ e ∈ constructionEdges d, e.card = 4 := by
  intro e he
  simp only [constructionEdges, Finset.mem_union, Finset.mem_image] at he
  rcases he with ((⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩) | ⟨z, hz, rfl⟩)
  · rw [sideSet_card]
    exact (Finset.mem_powersetCard.mp hs).2
  · rw [sideSet_card]
    exact (Finset.mem_powersetCard.mp hs).2
  · exact rectSet_card hz

lemma card_fours (d : ℕ) :
    (fours d).card = (Fintype.card (Code d)).choose 4 := by
  simp [fours]

lemma construction_card_aux (d : ℕ) :
    (constructionEdges d).card ≤ 2 * (fours d).card + (evenRectParams d).card := by
  unfold constructionEdges
  calc
    (((fours d).image (sideSet false) ∪ (fours d).image (sideSet true)) ∪
      (evenRectParams d).image rectSet).card ≤
        ((fours d).image (sideSet false) ∪ (fours d).image (sideSet true)).card +
          ((evenRectParams d).image rectSet).card := Finset.card_union_le _ _
    _ ≤ ((fours d).image (sideSet false)).card +
          ((fours d).image (sideSet true)).card +
          ((evenRectParams d).image rectSet).card := by
      have h := Finset.card_union_le ((fours d).image (sideSet false))
        ((fours d).image (sideSet true))
      omega
    _ ≤ 2 * (fours d).card + (evenRectParams d).card := by
      have hrow := Finset.card_image_le (s := fours d) (f := sideSet false)
      have hcol := Finset.card_image_le (s := fours d) (f := sideSet true)
      have hrect := Finset.card_image_le (s := evenRectParams d) (f := rectSet)
      omega

lemma construction_card_bound (d : ℕ) :
    24 * (constructionEdges d).card ≤ 5 * (Fintype.card (Code d)) ^ 4 := by
  let q := Fintype.card (Code d)
  have hedge := construction_card_aux d
  have hfour : 24 * (fours d).card ≤ q ^ 4 := by
    rw [card_fours]
    exact choose_four_bound q
  have hrect := card_evenRectParams_bound d
  have hmul : 24 * (constructionEdges d).card ≤
      48 * (fours d).card + 24 * (evenRectParams d).card := by omega
  calc
    24 * (constructionEdges d).card ≤
        48 * (fours d).card + 24 * (evenRectParams d).card := hmul
    _ = 2 * (24 * (fours d).card) + 3 * (8 * (evenRectParams d).card) := by ring
    _ ≤ 2 * q ^ 4 + 3 * q ^ 4 := by gcongr
    _ = 5 * q ^ 4 := by ring

/-! ## Every five-set is covered -/

lemma three_points_same_bool {α : Type} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 3) (f : α → Bool) :
    ∃ x y : α, x ≠ y ∧ f x = f y := by
  by_contra h
  have hinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    exact h ⟨x, y, hne, hxy⟩
  have hle := Fintype.card_le_of_injective f hinj
  rw [hcard, Fintype.card_bool] at hle
  omega

lemma pair_in_three_same_bool {α : Type} [Fintype α] [DecidableEq α]
    {s : Finset α} (hcard : s.card = 3) (f : α → Bool) :
    ∃ p ∈ s.powersetCard 2, (∑ x ∈ p, f x) = false := by
  let g : ↥s → Bool := fun x ↦ f x
  have hsubcard : Fintype.card ↥s = 3 := by simpa using hcard
  obtain ⟨x, y, hxy, heq⟩ := three_points_same_bool hsubcard g
  refine ⟨{x.1, y.1}, ?_, ?_⟩
  · apply Finset.mem_powersetCard.mpr
    refine ⟨?_, Finset.card_pair (fun h ↦ hxy (Subtype.ext h))⟩
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact x.2
    · exact y.2
  · rw [Finset.sum_pair (fun h ↦ hxy (Subtype.ext h))]
    have heq' : f x.1 = f y.1 := heq
    rw [bool_add_eq_false_iff]
    exact heq'

def codesOn {d : ℕ} (b : Bool) (S : Finset (Vertex d)) : Finset (Code d) :=
  (S.filter fun v ↦ v.1 = b).image Prod.snd

lemma mem_codesOn {d : ℕ} {b : Bool} {S : Finset (Vertex d)} {x : Code d} :
    x ∈ codesOn b S ↔ (b, x) ∈ S := by
  constructor
  · intro hx
    obtain ⟨v, hv, hsecond⟩ := Finset.mem_image.mp hx
    have hv' := Finset.mem_filter.mp hv
    have hfirst : v.1 = b := hv'.2
    have : v = (b, x) := by
      apply Prod.ext
      · exact hfirst
      · exact hsecond
    simpa [this] using hv'.1
  · intro hx
    exact Finset.mem_image.mpr ⟨(b, x), Finset.mem_filter.mpr ⟨hx, rfl⟩, rfl⟩

lemma sideSet_codesOn_subset {d : ℕ} (b : Bool) (S : Finset (Vertex d)) :
    sideSet b (codesOn b S) ⊆ S := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
  exact mem_codesOn.mp hx

lemma card_codesOn {d : ℕ} (b : Bool) (S : Finset (Vertex d)) :
    (codesOn b S).card = (S.filter fun v ↦ v.1 = b).card := by
  apply Finset.card_image_iff.mpr
  intro v hv w hw hsecond
  have hvb := (Finset.mem_filter.mp hv).2
  have hwb := (Finset.mem_filter.mp hw).2
  apply Prod.ext
  · exact hvb.trans hwb.symm
  · exact hsecond

lemma card_codesOn_add {d : ℕ} (S : Finset (Vertex d)) :
    (codesOn false S).card + (codesOn true S).card = S.card := by
  rw [card_codesOn, card_codesOn]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := S) (fun v : Vertex d ↦ v.1 = false)
  have htrue : (S.filter fun v : Vertex d ↦ ¬v.1 = false) =
      S.filter fun v ↦ v.1 = true := by
    ext v
    simp
  simpa [htrue] using hpartition

lemma side_edge_of_four {d : ℕ} {b : Bool} {S : Finset (Vertex d)}
    (hfour : 4 ≤ (codesOn b S).card) :
    ∃ e ∈ constructionEdges d, e ⊆ S := by
  obtain ⟨s, hsub, hcard⟩ := Finset.exists_subset_card_eq hfour
  refine ⟨sideSet b s, ?_, ?_⟩
  have hs : s ∈ fours d := Finset.mem_powersetCard.mpr
    ⟨hsub.trans (by simp [codesOn]), hcard⟩
  cases b
  · apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    left
    exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
  · apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    right
    exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact mem_codesOn.mp (hsub hx)

lemma rect_param_mem {d : ℕ} {rp cp : Finset (Code d)}
    (hrp : rp ∈ pairs d) (hcp : cp ∈ pairs d)
    (heven : (∑ y ∈ cp, pairLabel rp y) = false) :
    (Sigma.mk rp cp) ∈ evenRectParams d := by
  exact Finset.mem_sigma.mpr ⟨hrp, Finset.mem_filter.mpr ⟨hcp, heven⟩⟩

lemma rectSet_subset_of_codesOn {d : ℕ} {S : Finset (Vertex d)}
    {rp cp : Finset (Code d)} (hr : rp ⊆ codesOn false S)
    (hc : cp ⊆ codesOn true S) : rectSet (Sigma.mk rp cp) ⊆ S := by
  intro v hv
  simp only [rectSet, Finset.mem_union] at hv
  rcases hv with hv | hv
  · exact sideSet_codesOn_subset false S (Finset.mem_image.mpr <|
      let ⟨x, hx, hEq⟩ := Finset.mem_image.mp hv
      ⟨x, hr hx, hEq⟩)
  · exact sideSet_codesOn_subset true S (Finset.mem_image.mpr <|
      let ⟨x, hx, hEq⟩ := Finset.mem_image.mp hv
      ⟨x, hc hx, hEq⟩)

lemma rect_is_edge {d : ℕ} {z : Sigma fun _ : Finset (Code d) ↦ Finset (Code d)}
    (hz : z ∈ evenRectParams d) : rectSet z ∈ constructionEdges d := by
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

lemma mixed_edge_row_three {d : ℕ} {S : Finset (Vertex d)}
    (hr : (codesOn false S).card = 3) (hc : (codesOn true S).card = 2) :
    ∃ e ∈ constructionEdges d, e ⊆ S := by
  let R := codesOn false S
  let C := codesOn true S
  let f : Code d → Bool := fun x ↦ ∑ y ∈ C, dot x y
  obtain ⟨rp, hrpR, hsum⟩ := pair_in_three_same_bool hr f
  have hrpData := Finset.mem_powersetCard.mp hrpR
  have hrp : rp ∈ pairs d := Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, hrpData.2⟩
  have hcp : C ∈ pairs d := Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, hc⟩
  have heven : (∑ y ∈ C, pairLabel rp y) = false := by
    calc
      (∑ y ∈ C, pairLabel rp y) = ∑ x ∈ rp, ∑ y ∈ C, dot x y := by
        simp only [pairLabel]
        rw [Finset.sum_comm]
      _ = false := hsum
  have hz := rect_param_mem hrp hcp heven
  refine ⟨rectSet (Sigma.mk rp C), rect_is_edge hz, ?_⟩
  exact rectSet_subset_of_codesOn hrpData.1 (by rfl)

lemma mixed_edge_col_three {d : ℕ} {S : Finset (Vertex d)}
    (hr : (codesOn false S).card = 2) (hc : (codesOn true S).card = 3) :
    ∃ e ∈ constructionEdges d, e ⊆ S := by
  let R := codesOn false S
  let C := codesOn true S
  obtain ⟨cp, hcpC, heven⟩ :=
    pair_in_three_same_bool hc (pairLabel R)
  have hcpData := Finset.mem_powersetCard.mp hcpC
  have hrp : R ∈ pairs d := Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, hr⟩
  have hcp : cp ∈ pairs d := Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, hcpData.2⟩
  have hz := rect_param_mem hrp hcp heven
  refine ⟨rectSet (Sigma.mk R cp), rect_is_edge hz, ?_⟩
  exact rectSet_subset_of_codesOn (by rfl) hcpData.1

lemma construction_covers_five {d : ℕ} {S : Finset (Vertex d)}
    (hS : S.card = 5) : ∃ e ∈ constructionEdges d, e ⊆ S := by
  have hsum := card_codesOn_add S
  rw [hS] at hsum
  by_cases hr4 : 4 ≤ (codesOn false S).card
  · exact side_edge_of_four hr4
  by_cases hc4 : 4 ≤ (codesOn true S).card
  · exact side_edge_of_four hc4
  have hrle : (codesOn false S).card ≤ 3 := by omega
  have hcle : (codesOn true S).card ≤ 3 := by omega
  by_cases hr3 : (codesOn false S).card = 3
  · apply mixed_edge_row_three hr3
    omega
  · apply mixed_edge_col_three
    · omega
    · omega

/-! ## Chromatic and numerical conclusions -/

lemma card_code (d : ℕ) : Fintype.card (Code d) = 2 ^ d := by
  simp [Code]

lemma card_vertex (d : ℕ) : Fintype.card (Vertex d) = 2 * 2 ^ d := by
  simp [Vertex, Code, Fintype.card_prod]

lemma construction_monochromatic_edge (n : ℕ)
    (c : Vertex (n + 1) → Fin (2 ^ n - 1)) :
    ∃ e ∈ constructionEdges (n + 1), ∃ a, ∀ x ∈ e, c x = a := by
  have hcard : Fintype.card (Fin (2 ^ n - 1)) * 4 <
      Fintype.card (Vertex (n + 1)) := by
    rw [Fintype.card_fin, card_vertex]
    rw [pow_succ]
    have hk : 2 ^ n - 1 < 2 ^ n :=
      Nat.sub_lt (pow_pos (by decide : (0 : ℕ) < 2) n) (by decide)
    calc
      (2 ^ n - 1) * 4 < 2 ^ n * 4 :=
        (Nat.mul_lt_mul_right (a := 4) (by decide)).2 hk
      _ = 2 * (2 ^ n * 2) := by ring
  obtain ⟨a, ha⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := c) hcard
  let fiberA := Finset.univ.filter fun x ↦ c x = a
  have hfive : 5 ≤ fiberA.card := by
    change 5 ≤ (Finset.univ.filter fun x ↦ c x = a).card
    omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hfive
  obtain ⟨e, he, hesub⟩ := construction_covers_five hScard
  refine ⟨e, he, a, ?_⟩
  intro x hx
  exact (Finset.mem_filter.mp (hSsub (hesub hx))).2

def constructionHypergraph (d : ℕ) : FiniteHypergraph where
  V := Vertex d
  fintypeV := inferInstance
  decidableEqV := inferInstance
  edges := constructionEdges d

@[simp] lemma constructionHypergraph_edges (d : ℕ) :
    (constructionHypergraph d).edges = constructionEdges d := rfl

lemma constructionHypergraph_uniform (d : ℕ) :
    (constructionHypergraph d).IsUniform 4 := construction_uniform d

lemma construction_not_colorable (n : ℕ) :
    ¬(constructionHypergraph (n + 1)).Colorable (2 ^ n - 1) := by
  rintro ⟨c, hc⟩
  let cV : Vertex (n + 1) → Fin (2 ^ n - 1) := fun x ↦ c x
  have hcV : ∀ e ∈ constructionEdges (n + 1),
      ∃ x ∈ e, ∃ y ∈ e, cV x ≠ cV y := by
    intro e he
    exact hc e he
  obtain ⟨e, he, a, hmono⟩ := construction_monochromatic_edge n cV
  obtain ⟨x, hx, y, hy, hxy⟩ := hcV e he
  exact hxy ((hmono x hx).trans (hmono y hy).symm)

lemma benchmark_poly (k : ℕ) (hk : 512 ≤ k) :
    80 * k ^ 4 < (3 * k - 2) * (3 * k - 3) * (3 * k - 4) * (3 * k - 5) := by
  let z : ℤ := k
  have hz : (512 : ℤ) ≤ z := by
    dsimp [z]
    exact_mod_cast hk
  have hzpos : 0 < z := by omega
  have hmain : 0 < z ^ 3 * (z - 378) :=
    mul_pos (pow_pos hzpos 3) (by omega)
  have hrestnonneg : 0 ≤ z * (639 * z - 462) :=
    mul_nonneg hzpos.le (by omega)
  have hpoly : 80 * z ^ 4 <
      (3 * z - 2) * (3 * z - 3) * (3 * z - 4) * (3 * z - 5) := by
    have hid :
        (3 * z - 2) * (3 * z - 3) * (3 * z - 4) * (3 * z - 5) - 80 * z ^ 4 =
          z ^ 3 * (z - 378) + (z * (639 * z - 462) + 120) := by ring
    rw [← sub_pos, hid]
    omega
  have h2 : 2 ≤ 3 * k := by omega
  have h3 : 3 ≤ 3 * k := by omega
  have h4 : 4 ≤ 3 * k := by omega
  have h5 : 5 ≤ 3 * k := by omega
  by_contra hn
  have hle : (3 * k - 2) * (3 * k - 3) * (3 * k - 4) * (3 * k - 5) ≤
      80 * k ^ 4 := Nat.le_of_not_gt hn
  have hleZ :
      ((↑(((3 * k - 2) * (3 * k - 3) * (3 * k - 4) * (3 * k - 5) : ℕ)) : ℤ) ≤
        (↑((80 * k ^ 4 : ℕ)) : ℤ)) := by
    exact_mod_cast hle
  push_cast [Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub h4, Nat.cast_sub h5] at hleZ
  dsimp [z] at hpoly
  omega

lemma benchmark_choose_scaled (k : ℕ) (hk : 512 ≤ k) :
    80 * k ^ 4 < 24 * (3 * (k - 1) + 1).choose 4 := by
  have hn : 3 * (k - 1) + 1 = 3 * k - 2 := by omega
  rw [hn, twentyFour_mul_choose_four]
  have h1 : 3 * k - 2 - 1 = 3 * k - 3 := by omega
  have h2 : 3 * k - 2 - 2 = 3 * k - 4 := by omega
  have h3 : 3 * k - 2 - 3 = 3 * k - 5 := by omega
  rw [h1, h2, h3]
  exact benchmark_poly k hk

lemma construction_strict_bound (n : ℕ) (hn : 9 ≤ n) :
    (constructionEdges (n + 1)).card < (3 * (2 ^ n - 1) + 1).choose 4 := by
  let k := 2 ^ n
  have hk : 512 ≤ k := by
    change 2 ^ 9 ≤ 2 ^ n
    exact Nat.pow_le_pow_right (by decide) hn
  have hedge := construction_card_bound (n + 1)
  have hedge' : 24 * (constructionEdges (n + 1)).card ≤ 80 * k ^ 4 := by
    calc
      24 * (constructionEdges (n + 1)).card ≤
          5 * Fintype.card (Code (n + 1)) ^ 4 := hedge
      _ = 80 * k ^ 4 := by
        rw [card_code, pow_succ]
        dsimp [k]
        ring
  have hbenchmark := benchmark_choose_scaled k hk
  have hscaled : 24 * (constructionEdges (n + 1)).card <
      24 * (3 * (k - 1) + 1).choose 4 := hedge'.trans_lt hbenchmark
  exact (Nat.mul_lt_mul_left (a := 24) (by decide)).1 hscaled

/-- Erdős Problem 832 has a negative answer: its exact eventual assertion,
including the proposed equality characterization, is false already for
`4`-uniform hypergraphs. -/
theorem erdos832 : ¬Erdos832Claim := by
  intro hclaim
  obtain ⟨K, hK⟩ := hclaim 4 (by omega)
  let n := K + 9
  let k := 2 ^ n
  let H := constructionHypergraph (n + 1)
  have hn : 9 ≤ n := by omega
  have hk512 : 512 ≤ k := by
    change 2 ^ 9 ≤ 2 ^ n
    exact Nat.pow_le_pow_right (by decide) hn
  have hKpow : K ≤ 2 ^ K := by
    have h := Nat.mul_le_pow (a := 2) (by decide) K
    omega
  have hKk : K ≤ k := by
    apply hKpow.trans
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hbad : ¬H.Colorable (k - 1) := by
    exact construction_not_colorable n
  obtain ⟨H', hsameV, hsubcard, huniform, hchi⟩ :=
    FiniteHypergraph.exists_spanning_exact_chromatic
      (H := H) (r := 4) (k := k) (by omega) (by omega)
      (constructionHypergraph_uniform (n + 1)) hbad
  have hlower := hK k hKk H' huniform hchi
  have hlower' : (3 * (k - 1) + 1).choose 4 ≤ H'.edges.card := by
    simpa using hlower.1
  have hstrictConstruction : H.edges.card < (3 * (k - 1) + 1).choose 4 := by
    exact construction_strict_bound n hn
  have hstrict : H'.edges.card < (3 * (k - 1) + 1).choose 4 :=
    hsubcard.trans_lt hstrictConstruction
  exact (Nat.not_lt_of_ge hlower') hstrict

#print axioms erdos832

end Erdos832
