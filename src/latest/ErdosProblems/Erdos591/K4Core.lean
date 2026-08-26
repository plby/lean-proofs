import ErdosProblems.Erdos590
import Mathlib.Tactic.FinCases

open Set
open Ordinal

universe u v w

namespace Erdos591.Schipperus.K4Core

/-! A set is `B`-large when it contains an order-embedded copy of `B`. -/
def Large (B : Type u) [Preorder B] {X : Type v} [Preorder X]
    (s : Set X) : Prop :=
  Nonempty (B ↪o s)

/-! The precise partition hypothesis used by the ramification argument.
It is deliberately stated as an oracle for all finite colourings. -/
def FinitelyIndivisible (B : Type u) [Preorder B] : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (c : B → Fin n),
    ∃ i : Fin n, ∃ e : B ↪o B, ∀ x, c (e x) = i

theorem finitelyIndivisible_of_subsingleton
    (B : Type u) [Preorder B] [Subsingleton B] [Nonempty B] :
    FinitelyIndivisible B := by
  intro n hn c
  let b : B := Classical.arbitrary B
  refine ⟨c b, OrderEmbedding.id B, ?_⟩
  intro x
  exact congrArg c (Subsingleton.elim x b)

namespace Large

variable {B : Type u} [Preorder B]
variable {X : Type v} [Preorder X]

theorem mono {s t : Set X} (hst : s ⊆ t) (hs : Large B s) : Large B t := by
  rcases hs with ⟨e⟩
  refine ⟨
    { toFun := fun x => ⟨(e x : X), hst (e x).2⟩
      inj' := by
        intro x y h
        apply e.injective
        apply Subtype.ext
        exact congrArg (fun z : t => (z : X)) h
      map_rel_iff' := by
        intro a b
        exact e.le_iff_le }⟩

theorem univ : Large B (Set.univ : Set B) := by
  refine ⟨
    { toFun := fun x => ⟨x, Set.mem_univ x⟩
      inj' := by
        intro x y h
        exact congrArg (fun z : (Set.univ : Set B) => (z : B)) h
      map_rel_iff' := by intro a b; rfl }⟩

theorem nonempty [Nonempty B] {s : Set X} (hs : Large B s) : s.Nonempty := by
  rcases hs with ⟨e⟩
  let b : B := Classical.arbitrary B
  exact ⟨e b, (e b).2⟩

theorem inter_or_diff (hind : FinitelyIndivisible B)
    {a s : Set X} (ha : Large B a) :
    Large B (a ∩ s) ∨ Large B (a \ s) := by
  classical
  rcases ha with ⟨f⟩
  let c : B → Fin 2 := fun x => if (f x : X) ∈ s then 0 else 1
  rcases hind 2 (by omega) c with ⟨i, e, he⟩
  fin_cases i
  · left
    refine ⟨
      { toFun := fun x => ⟨(f (e x) : X), (f (e x)).2, by
          have hx := he x
          simpa [c] using hx⟩
        inj' := by
          intro x y h
          apply e.injective
          apply f.injective
          apply Subtype.ext
          have hv : (f (e x) : X) = (f (e y) : X) :=
            congrArg (fun z : ↥((a ∩ s : Set X)) => (z : X)) h
          exact hv
        map_rel_iff' := by
          intro p q
          exact f.le_iff_le.trans e.le_iff_le }⟩
  · right
    refine ⟨
      { toFun := fun x => ⟨(f (e x) : X), (f (e x)).2, by
          have hx := he x
          simpa [c] using hx⟩
        inj' := by
          intro x y h
          apply e.injective
          apply f.injective
          apply Subtype.ext
          have hv : (f (e x) : X) = (f (e y) : X) :=
            congrArg (fun z : ↥((a \ s : Set X)) => (z : X)) h
          exact hv
        map_rel_iff' := by
          intro p q
          exact f.le_iff_le.trans e.le_iff_le }⟩

theorem diff_of_not_large (hind : FinitelyIndivisible B)
    {a s : Set X} (ha : Large B a) (hs : ¬ Large B s) :
    Large B (a \ s) := by
  rcases inter_or_diff hind ha with has | has
  · exact (hs (has.mono inter_subset_right)).elim
  · exact has

theorem diff_union_of_not_large (hind : FinitelyIndivisible B)
    {a s t : Set X} (ha : Large B a)
    (hs : ¬ Large B s) (ht : ¬ Large B t) :
    Large B (a \ (s ∪ t)) := by
  have h₁ : Large B (a \ s) := diff_of_not_large hind ha hs
  have h₂ : Large B ((a \ s) \ t) := diff_of_not_large hind h₁ ht
  convert h₂ using 1 <;> ext x <;> simp only [Set.mem_diff, Set.mem_union]
  tauto

end Large

theorem typeLT_eq_of_large
    {B : Type u} [LinearOrder B] [WellFoundedLT B]
    {s : Set B} (hs : Large B s) : typeLT s = typeLT B := by
  apply le_antisymm
  · exact Ordinal.type_set_le s
  · rw [Ordinal.type_le_iff']
    exact ⟨hs.some.ltEmbedding⟩

theorem singleton_not_large
    {B : Type u} [Preorder B] [Nontrivial B]
    {X : Type v} [Preorder X] (x : X) :
    ¬ Large B ({x} : Set X) := by
  rintro ⟨e⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne B
  apply hab
  apply e.injective
  apply Subtype.ext
  simpa using (e a).2.trans (e b).2.symm

section Graph

variable {B : Type u} [LinearOrder B] [Nonempty B]
variable {D : Type v} [LinearOrder D] [Nonempty D]
variable {V : Type w} [LinearOrder V]

lemma exists_blue_edge_of_large
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (hnoRed : ¬ ∃ s : Set V, red.IsClique s ∧ Large B s)
    {s : Set V} (hs : Large B s) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ blue.Adj x y := by
  by_contra h
  push_neg at h
  apply hnoRed
  refine ⟨s, ?_, hs⟩
  intro x hx y hy hxy
  rw [hcompl.eq_compl]
  exact ⟨hxy, h x hx y hy hxy⟩

/-!
The four-point ramification core.  `A` is the current large set and
`block d` are the large later blocks.  A point is good when its red
neighbourhood is large in a large set of block indices.
-/
theorem good_large
    (hindB : FinitelyIndivisible B) (hindD : FinitelyIndivisible D)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (hnoRed : ¬ ∃ s : Set V, red.IsClique s ∧ Large B s)
    (hnoK4 : blue.CliqueFree 4)
    (A : Set V) (hA : Large B A)
    (block : D → Set V) (hblock : ∀ d, Large B (block d))
    (hdisjoint : ∀ d, Disjoint A (block d)) :
    Large B {x | x ∈ A ∧
      Large D {d | Large B {y | y ∈ block d ∧ red.Adj x y}}} := by
  classical
  let M : V → Set D := fun x =>
    {d | Large B {y | y ∈ block d ∧ red.Adj x y}}
  let Good : Set V := {x | x ∈ A ∧ Large D (M x)}
  change Large B Good
  by_contra hGood
  have hBad : Large B (A \ Good) :=
    Large.diff_of_not_large hindB hA hGood
  rcases exists_blue_edge_of_large red blue hcompl hnoRed hBad with
    ⟨x₀, hx₀, x₁, hx₁, hxne, hxx⟩
  have hx₀A : x₀ ∈ A := hx₀.1
  have hx₁A : x₁ ∈ A := hx₁.1
  have hM₀ : ¬ Large D (M x₀) := by
    intro hM
    exact hx₀.2 ⟨hx₀A, hM⟩
  have hM₁ : ¬ Large D (M x₁) := by
    intro hM
    exact hx₁.2 ⟨hx₁A, hM⟩
  have hindices : Large D ((Set.univ : Set D) \ (M x₀ ∪ M x₁)) :=
    Large.diff_union_of_not_large hindD Large.univ hM₀ hM₁
  rcases hindices.nonempty with ⟨d, hd⟩
  have hdM₀ : d ∉ M x₀ := by exact fun h => hd.2 (Or.inl h)
  have hdM₁ : d ∉ M x₁ := by exact fun h => hd.2 (Or.inr h)
  let R₀ : Set V := {y | y ∈ block d ∧ red.Adj x₀ y}
  let R₁ : Set V := {y | y ∈ block d ∧ red.Adj x₁ y}
  have hR₀ : ¬ Large B R₀ := by simpa [M, R₀] using hdM₀
  have hR₁ : ¬ Large B R₁ := by simpa [M, R₁] using hdM₁
  let C : Set V := block d \ (R₀ ∪ R₁)
  have hC : Large B C := by
    simpa [C] using
      Large.diff_union_of_not_large hindB (hblock d) hR₀ hR₁
  rcases exists_blue_edge_of_large red blue hcompl hnoRed hC with
    ⟨y₀, hy₀, y₁, hy₁, hyne, hyy⟩
  have hy₀block : y₀ ∈ block d := hy₀.1
  have hy₁block : y₁ ∈ block d := hy₁.1
  have hcross_ne (x y : V) (hx : x ∈ A) (hy : y ∈ block d) : x ≠ y := by
    intro hxy
    subst y
    exact Set.disjoint_left.mp (hdisjoint d) hx hy
  have hx₀y₀_ne : x₀ ≠ y₀ := hcross_ne x₀ y₀ hx₀A hy₀block
  have hx₀y₁_ne : x₀ ≠ y₁ := hcross_ne x₀ y₁ hx₀A hy₁block
  have hx₁y₀_ne : x₁ ≠ y₀ := hcross_ne x₁ y₀ hx₁A hy₀block
  have hx₁y₁_ne : x₁ ≠ y₁ := hcross_ne x₁ y₁ hx₁A hy₁block
  have hnred₀₀ : ¬ red.Adj x₀ y₀ := by
    intro h
    exact hy₀.2 (Or.inl ⟨hy₀block, h⟩)
  have hnred₀₁ : ¬ red.Adj x₀ y₁ := by
    intro h
    exact hy₁.2 (Or.inl ⟨hy₁block, h⟩)
  have hnred₁₀ : ¬ red.Adj x₁ y₀ := by
    intro h
    exact hy₀.2 (Or.inr ⟨hy₀block, h⟩)
  have hnred₁₁ : ¬ red.Adj x₁ y₁ := by
    intro h
    exact hy₁.2 (Or.inr ⟨hy₁block, h⟩)
  have hxy₀₀ : blue.Adj x₀ y₀ := by
    rw [hcompl.symm.eq_compl]
    exact ⟨hx₀y₀_ne, hnred₀₀⟩
  have hxy₀₁ : blue.Adj x₀ y₁ := by
    rw [hcompl.symm.eq_compl]
    exact ⟨hx₀y₁_ne, hnred₀₁⟩
  have hxy₁₀ : blue.Adj x₁ y₀ := by
    rw [hcompl.symm.eq_compl]
    exact ⟨hx₁y₀_ne, hnred₁₀⟩
  have hxy₁₁ : blue.Adj x₁ y₁ := by
    rw [hcompl.symm.eq_compl]
    exact ⟨hx₁y₁_ne, hnred₁₁⟩
  let Q : Finset V := {x₀, x₁, y₀, y₁}
  apply hnoK4 Q
  rw [blue.isNClique_iff]
  refine ⟨?_, ?_⟩
  · simp only [Q, Finset.coe_insert, Finset.coe_singleton]
    simp [SimpleGraph.isClique_insert, hxx, hyy, hxy₀₀, hxy₀₁,
      hxy₁₀, hxy₁₁, hxne, hyne, hx₀y₀_ne, hx₀y₁_ne,
      hx₁y₀_ne, hx₁y₁_ne, SimpleGraph.adj_symm]
  · simp [Q, hxne, hyne, hx₀y₀_ne, hx₀y₁_ne,
      hx₁y₀_ne, hx₁y₁_ne]

/-!
Overlap-capable form of the ramification argument.  No disjointness between
the candidate set and the blocks is required.  Instead we use the exact
property needed in the proof: deleting either of the two chosen candidate
vertices from a large reservoir preserves largeness.
-/
theorem bad_not_large_overlap
    (hindB : FinitelyIndivisible B) (hindD : FinitelyIndivisible D)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (hnoRed : ¬ ∃ s : Set V, red.IsClique s ∧ Large B s)
    (hnoK4 : blue.CliqueFree 4)
    (hsmall : ∀ x : V, ¬ Large B ({x} : Set V))
    (A : Set V)
    (block : D → Set V) (hblock : ∀ d, Large B (block d)) :
    ¬ Large B {x | x ∈ A ∧
      ¬ Large D {d | Large B {y | y ∈ block d ∧ red.Adj x y}}} := by
  classical
  let M : V → Set D := fun x =>
    {d | Large B {y | y ∈ block d ∧ red.Adj x y}}
  let Bad : Set V := {x | x ∈ A ∧ ¬ Large D (M x)}
  change ¬ Large B Bad
  intro hBad
  rcases exists_blue_edge_of_large red blue hcompl hnoRed hBad with
    ⟨x₀, hx₀, x₁, hx₁, hxne, hxx⟩
  have hM₀ : ¬ Large D (M x₀) := hx₀.2
  have hM₁ : ¬ Large D (M x₁) := hx₁.2
  have hindices : Large D ((Set.univ : Set D) \ (M x₀ ∪ M x₁)) :=
    Large.diff_union_of_not_large hindD Large.univ hM₀ hM₁
  rcases hindices.nonempty with ⟨d, hd⟩
  have hdM₀ : d ∉ M x₀ := by exact fun h => hd.2 (Or.inl h)
  have hdM₁ : d ∉ M x₁ := by exact fun h => hd.2 (Or.inr h)
  let R₀ : Set V := {y | y ∈ block d ∧ red.Adj x₀ y}
  let R₁ : Set V := {y | y ∈ block d ∧ red.Adj x₁ y}
  have hR₀ : ¬ Large B R₀ := by simpa [M, R₀] using hdM₀
  have hR₁ : ¬ Large B R₁ := by simpa [M, R₁] using hdM₁
  let C : Set V := block d \ (R₀ ∪ R₁)
  have hC : Large B C := by
    simpa [C] using
      Large.diff_union_of_not_large hindB (hblock d) hR₀ hR₁
  have hC₀ : Large B (C \ ({x₀} : Set V)) :=
    Large.diff_of_not_large hindB hC (hsmall x₀)
  have hC₁ : Large B ((C \ ({x₀} : Set V)) \ ({x₁} : Set V)) :=
    Large.diff_of_not_large hindB hC₀ (hsmall x₁)
  rcases exists_blue_edge_of_large red blue hcompl hnoRed hC₁ with
    ⟨y₀, hy₀, y₁, hy₁, hyne, hyy⟩
  have hy₀C : y₀ ∈ C := hy₀.1.1
  have hy₁C : y₁ ∈ C := hy₁.1.1
  have hy₀block : y₀ ∈ block d := hy₀C.1
  have hy₁block : y₁ ∈ block d := hy₁C.1
  have hy₀x₀_ne : y₀ ≠ x₀ := by simpa using hy₀.1.2
  have hy₁x₀_ne : y₁ ≠ x₀ := by simpa using hy₁.1.2
  have hy₀x₁_ne : y₀ ≠ x₁ := by simpa using hy₀.2
  have hy₁x₁_ne : y₁ ≠ x₁ := by simpa using hy₁.2
  have hx₀y₀_ne : x₀ ≠ y₀ := hy₀x₀_ne.symm
  have hx₀y₁_ne : x₀ ≠ y₁ := hy₁x₀_ne.symm
  have hx₁y₀_ne : x₁ ≠ y₀ := hy₀x₁_ne.symm
  have hx₁y₁_ne : x₁ ≠ y₁ := hy₁x₁_ne.symm
  have hnred₀₀ : ¬ red.Adj x₀ y₀ := by
    intro h
    exact hy₀C.2 (Or.inl ⟨hy₀block, h⟩)
  have hnred₀₁ : ¬ red.Adj x₀ y₁ := by
    intro h
    exact hy₁C.2 (Or.inl ⟨hy₁block, h⟩)
  have hnred₁₀ : ¬ red.Adj x₁ y₀ := by
    intro h
    exact hy₀C.2 (Or.inr ⟨hy₀block, h⟩)
  have hnred₁₁ : ¬ red.Adj x₁ y₁ := by
    intro h
    exact hy₁C.2 (Or.inr ⟨hy₁block, h⟩)
  have hxy₀₀ : blue.Adj x₀ y₀ := by
    rw [hcompl.symm.eq_compl]
    exact ⟨hx₀y₀_ne, hnred₀₀⟩
  have hxy₀₁ : blue.Adj x₀ y₁ := by
    rw [hcompl.symm.eq_compl]
    exact ⟨hx₀y₁_ne, hnred₀₁⟩
  have hxy₁₀ : blue.Adj x₁ y₀ := by
    rw [hcompl.symm.eq_compl]
    exact ⟨hx₁y₀_ne, hnred₁₀⟩
  have hxy₁₁ : blue.Adj x₁ y₁ := by
    rw [hcompl.symm.eq_compl]
    exact ⟨hx₁y₁_ne, hnred₁₁⟩
  let Q : Finset V := {x₀, x₁, y₀, y₁}
  apply hnoK4 Q
  rw [blue.isNClique_iff]
  refine ⟨?_, ?_⟩
  · simp only [Q, Finset.coe_insert, Finset.coe_singleton]
    simp [SimpleGraph.isClique_insert, hxx, hyy, hxy₀₀, hxy₀₁,
      hxy₁₀, hxy₁₁, hxne, hyne, hx₀y₀_ne, hx₀y₁_ne,
      hx₁y₀_ne, hx₁y₁_ne, SimpleGraph.adj_symm]
  · simp [Q, hxne, hyne, hx₀y₀_ne, hx₀y₁_ne,
      hx₁y₀_ne, hx₁y₁_ne]

theorem good_large_overlap
    (hindB : FinitelyIndivisible B) (hindD : FinitelyIndivisible D)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (hnoRed : ¬ ∃ s : Set V, red.IsClique s ∧ Large B s)
    (hnoK4 : blue.CliqueFree 4)
    (hsmall : ∀ x : V, ¬ Large B ({x} : Set V))
    (A : Set V) (hA : Large B A)
    (block : D → Set V) (hblock : ∀ d, Large B (block d)) :
    Large B {x | x ∈ A ∧
      Large D {d | Large B {y | y ∈ block d ∧ red.Adj x y}}} := by
  let Good : Set V := {x | x ∈ A ∧
    Large D {d | Large B {y | y ∈ block d ∧ red.Adj x y}}}
  change Large B Good
  by_contra hGood
  have hBad : Large B (A \ Good) :=
    Large.diff_of_not_large hindB hA hGood
  apply bad_not_large_overlap hindB hindD red blue hcompl hnoRed hnoK4
    hsmall A block hblock
  simpa [Good] using hBad

/-! The proof above actually rules out a large set of bad points.  This
form is what allows finitely many cellwise requirements to be imposed at
one ramification step. -/
theorem bad_not_large
    (hindB : FinitelyIndivisible B) (hindD : FinitelyIndivisible D)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (hnoRed : ¬ ∃ s : Set V, red.IsClique s ∧ Large B s)
    (hnoK4 : blue.CliqueFree 4)
    (A : Set V)
    (block : D → Set V) (hblock : ∀ d, Large B (block d))
    (hdisjoint : ∀ d, Disjoint A (block d)) :
    ¬ Large B {x | x ∈ A ∧
      ¬ Large D {d | Large B {y | y ∈ block d ∧ red.Adj x y}}} := by
  intro hBad
  let Bad : Set V := {x | x ∈ A ∧
    ¬ Large D {d | Large B {y | y ∈ block d ∧ red.Adj x y}}}
  have hBad' : Large B Bad := by simpa [Bad] using hBad
  have hdisjoint' : ∀ d, Disjoint Bad (block d) := by
    intro d
    exact (hdisjoint d).mono (by intro x hx; exact hx.1) Subset.rfl
  have hGood := good_large hindB hindD red blue hcompl hnoRed hnoK4
    Bad hBad' block hblock hdisjoint'
  rcases hGood.nonempty with ⟨x, hx⟩
  exact hx.1.2 hx.2

@[simp] theorem large_unit_setOf_const_iff (P : Prop) :
    Large Unit {u : Unit | P} ↔ P := by
  constructor
  · intro h
    rcases h with ⟨e⟩
    exact (e ()).2
  · intro hP
    have h : Large Unit (Set.univ : Set Unit) := Large.univ
    simpa [hP] using h

/-! Fixed-block specialization used to force the finitely many indices
that the reindexing must leave fixed into the good-index set. -/
theorem one_block_bad_not_large
    (hindB : FinitelyIndivisible B)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (hnoRed : ¬ ∃ s : Set V, red.IsClique s ∧ Large B s)
    (hnoK4 : blue.CliqueFree 4)
    (A Z : Set V) (hZ : Large B Z) (hdisjoint : Disjoint A Z) :
    ¬ Large B {x | x ∈ A ∧
      ¬ Large B {y | y ∈ Z ∧ red.Adj x y}} := by
  have h := bad_not_large (B := B) (D := Unit)
    hindB (finitelyIndivisible_of_subsingleton Unit)
    red blue hcompl hnoRed hnoK4 A (fun _ => Z)
    (fun _ => hZ) (fun _ => hdisjoint)
  simpa only [large_unit_setOf_const_iff] using h

theorem one_block_bad_not_large_overlap
    (hindB : FinitelyIndivisible B)
    (red blue : SimpleGraph V) (hcompl : IsCompl red blue)
    (hnoRed : ¬ ∃ s : Set V, red.IsClique s ∧ Large B s)
    (hnoK4 : blue.CliqueFree 4)
    (hsmall : ∀ x : V, ¬ Large B ({x} : Set V))
    (A Z : Set V) (hZ : Large B Z) :
    ¬ Large B {x | x ∈ A ∧
      ¬ Large B {y | y ∈ Z ∧ red.Adj x y}} := by
  have h := bad_not_large_overlap (B := B) (D := Unit)
    hindB (finitelyIndivisible_of_subsingleton Unit)
    red blue hcompl hnoRed hnoK4 hsmall A (fun _ => Z) (fun _ => hZ)
  simpa only [large_unit_setOf_const_iff] using h

/-! Removing finitely many bad loci from one large set preserves
largeness.  This is the bookkeeping operation needed after applying
`bad_not_large` separately to the finitely many open cells cut out by a
fixed set of indices. -/
theorem large_all_finset
    {I : Type*} [DecidableEq I]
    (hindB : FinitelyIndivisible B) (A : Set V) (hA : Large B A)
    (P : I → V → Prop) (F : Finset I)
    (hbad : ∀ i ∈ F, ¬ Large B {x | x ∈ A ∧ ¬ P i x}) :
    Large B {x | x ∈ A ∧ ∀ i ∈ F, P i x} := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using hA
  | @insert i F hi ih =>
      have hprev : Large B {x | x ∈ A ∧ ∀ j ∈ F, P j x} := by
        apply ih
        intro j hj
        exact hbad j (Finset.mem_insert_of_mem hj)
      have hremove : Large B
          ({x | x ∈ A ∧ ∀ j ∈ F, P j x} \
            {x | x ∈ A ∧ ¬ P i x}) :=
        Large.diff_of_not_large hindB hprev (hbad i (Finset.mem_insert_self i F))
      convert hremove using 1
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_diff, Finset.mem_insert]
      constructor
      · rintro ⟨hxA, hall⟩
        refine ⟨⟨hxA, fun j hj => hall j (Or.inr hj)⟩, ?_⟩
        rintro ⟨-, hnPi⟩
        exact hnPi (hall i (Or.inl rfl))
      · rintro ⟨⟨hxA, hPF⟩, hnot⟩
        refine ⟨hxA, ?_⟩
        intro j hj
        rcases hj with rfl | hj
        · by_contra hnPi
          exact hnot ⟨hxA, hnPi⟩
        · exact hPF j hj

end Graph

end Erdos591.Schipperus.K4Core
