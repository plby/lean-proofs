import Mathlib

namespace Erdos847ConfinementKernels

open Function Set

set_option autoImplicit false

abbrev Alphabet := Fin 3

theorem fin3_cases (i : Alphabet) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

/-! ## Elementary classifications of ternary rows -/

theorem fin3_injective_iff_pairwise_ne {P : Type*} (f : Alphabet → P) :
    Injective f ↔ f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 1 ≠ f 2 := by
  constructor
  · intro hf
    exact ⟨fun h => by simpa using hf h,
      fun h => by simpa using hf h,
      fun h => by simpa using hf h⟩
  · rintro ⟨h01, h02, h12⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem fin3_constant_iff {P : Type*} (f : Alphabet → P) :
    (∃ p, ∀ i, f i = p) ↔ f 0 = f 1 ∧ f 0 = f 2 := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨(hp 0).trans (hp 1).symm, (hp 0).trans (hp 2).symm⟩
  · rintro ⟨h01, h02⟩
    refine ⟨f 0, ?_⟩
    intro i
    fin_cases i <;> simp_all

theorem fin3_injective_or_constant_iff {P : Type*} (f : Alphabet → P) :
    (Injective f ∨ ∃ p, ∀ i, f i = p) ↔
      (f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 1 ≠ f 2) ∨
        (f 0 = f 1 ∧ f 0 = f 2) := by
  rw [fin3_injective_iff_pairwise_ne, fin3_constant_iff]

theorem fin3_range_iff {P : Type*} (f : Alphabet → P) (p : P) :
    p ∈ Set.range f ↔ p = f 0 ∨ p = f 1 ∨ p = f 2 := by
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (h | h | h)
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
    · exact ⟨2, h.symm⟩

/-!
`Admissible fiber c row` is the normalized form of (4.2): in position `i`,
the section is either on the music fiber or is its distinguished source
representative `c i`.
-/
def Admissible {P : Type*} (fiber : P → Prop) (c row : Alphabet → P) : Prop :=
  ∀ i, fiber (row i) ∨ row i = c i

/-- The same-range/different-order normal form in the ternary case. -/
theorem same_range_normal_forms {P : Type*} {fiber : P → Prop}
    {c row : Alphabet → P} {a : P}
    (hc0 : ¬ fiber (c 0)) (hc1 : ¬ fiber (c 1))
    (hrow : Injective row)
    (hadm : Admissible fiber c row)
    (hrange : Set.range row = {c 0, c 1, a})
    (hne : row 0 ≠ c 0 ∨ row 1 ≠ c 1 ∨ row 2 ≠ a) :
    (row 0 = a ∧ row 1 = c 1 ∧ row 2 = c 0 ∧ c 2 = c 0) ∨
      (row 0 = c 0 ∧ row 1 = a ∧ row 2 = c 1 ∧ c 2 = c 1) := by
  have hmem (i : Alphabet) : row i = c 0 ∨ row i = c 1 ∨ row i = a := by
    have : row i ∈ ({c 0, c 1, a} : Set P) := by
      rw [← hrange]
      exact Set.mem_range_self i
    simpa [eq_comm] using this
  have hr0 : row 0 = c 0 ∨ row 0 = a := by
    rcases hadm 0 with hf | hc
    · rcases hmem 0 with h | h | h
      · exact Or.inl h
      · exact False.elim (hc1 (h ▸ hf))
      · exact Or.inr h
    · exact Or.inl hc
  have hr1 : row 1 = c 1 ∨ row 1 = a := by
    rcases hadm 1 with hf | hc
    · rcases hmem 1 with h | h | h
      · exact False.elim (hc0 (h ▸ hf))
      · exact Or.inl h
      · exact Or.inr h
    · exact Or.inl hc
  rcases hr0 with hr0 | hr0 <;> rcases hr1 with hr1 | hr1
  · exfalso
    have hr2 : row 2 = a := by
      rcases hmem 2 with h | h | h
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 0)
          apply hrow
          exact h.trans hr0.symm)
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 1)
          apply hrow
          exact h.trans hr1.symm)
      · exact h
    rcases hne with hne | hne | hne
    · exact hne hr0
    · exact hne hr1
    · exact hne hr2
  · right
    have hr2 : row 2 = c 1 := by
      rcases hmem 2 with h | h | h
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 0)
          apply hrow
          exact h.trans hr0.symm)
      · exact h
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 1)
          apply hrow
          exact h.trans hr1.symm)
    refine ⟨hr0, hr1, hr2, ?_⟩
    rcases hadm 2 with hf | hc
    · exact False.elim (hc1 (hr2 ▸ hf))
    · exact hc.symm.trans hr2
  · left
    have hr2 : row 2 = c 0 := by
      rcases hmem 2 with h | h | h
      · exact h
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 1)
          apply hrow
          exact h.trans hr1.symm)
      · exact False.elim (by
          apply (by decide : (2 : Alphabet) ≠ 0)
          apply hrow
          exact h.trans hr0.symm)
    refine ⟨hr0, hr1, hr2, ?_⟩
    rcases hadm 2 with hf | hc
    · exact False.elim (hc0 (hr2 ▸ hf))
    · exact hc.symm.trans hr2
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 1) <| hrow <|
      hr0.trans hr1.symm

/--
Two distinct ternary source-line ranges, each having at most one fiber
point, have the two normal forms from the second case of Proposition 4.5.
The `Subsingleton` hypothesis is the usual fact that two distinct
combinatorial lines meet in at most one point.
-/
theorem distinct_range_normal_forms {P : Type*} {fiber : P → Prop}
    {c row : Alphabet → P} {a : P}
    (hc01 : c 0 ≠ c 1)
    (hc0 : ¬ fiber (c 0)) (hc1 : ¬ fiber (c 1))
    (hadm : Admissible fiber c row)
    (hfiber : ∀ i j, fiber (row i) → fiber (row j) → i = j)
    (hinter : (Set.range row ∩ ({c 0, c 1, a} : Set P)).Subsingleton) :
    (∃ b, fiber b ∧ b ≠ a ∧
      row 0 = c 0 ∧ row 1 = b ∧ row 2 = c 2) ∨
      (∃ b, fiber b ∧ b ≠ a ∧
        row 0 = b ∧ row 1 = c 1 ∧ row 2 = c 2) := by
  have shared_eq {u v : P}
      (hurow : u ∈ Set.range row) (hubase : u ∈ ({c 0, c 1, a} : Set P))
      (hvrow : v ∈ Set.range row) (hvbase : v ∈ ({c 0, c 1, a} : Set P)) :
      u = v := hinter ⟨hurow, hubase⟩ ⟨hvrow, hvbase⟩
  rcases hadm 0 with h0f | h0c <;>
    rcases hadm 1 with h1f | h1c <;>
    rcases hadm 2 with h2f | h2c
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 1) <| hfiber 0 1 h0f h1f
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 1) <| hfiber 0 1 h0f h1f
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 2) <| hfiber 0 2 h0f h2f
  · right
    refine ⟨row 0, h0f, ?_, rfl, h1c, h2c⟩
    intro h0a
    have hca : c 1 = a := shared_eq
      ⟨1, h1c⟩ (by simp)
      ⟨0, h0a⟩ (by simp)
    exact hc1 (hca ▸ by simpa [h0a] using h0f)
  · exact False.elim <| (by decide : (1 : Alphabet) ≠ 2) <| hfiber 1 2 h1f h2f
  · left
    refine ⟨row 1, h1f, ?_, h0c, rfl, h2c⟩
    intro h1a
    have hca : c 0 = a := shared_eq
      ⟨0, h0c⟩ (by simp)
      ⟨1, h1a⟩ (by simp)
    exact hc0 (hca ▸ by simpa [h1a] using h1f)
  · exfalso
    have hEq : c 0 = c 1 := shared_eq
      ⟨0, h0c⟩ (by simp)
      ⟨1, h1c⟩ (by simp)
    exact hc01 hEq
  · exfalso
    have hEq : c 0 = c 1 := shared_eq
      ⟨0, h0c⟩ (by simp)
      ⟨1, h1c⟩ (by simp)
    exact hc01 hEq

/--
With three normalized outside representatives and at most one fiber entry,
there are only the three `2 + 1` masks or the all-moving mask.  Applied after
the first two distinct ranges have been named, the third disjunct is exactly
the potential `{d,c₁,c₂}` line; the last disjunct meets either named line in
two outside points and is therefore excluded by line uniqueness.
-/
theorem normalized_row_four_forms {P : Type*} {fiber : P → Prop}
    {c row : Alphabet → P}
    (hadm : Admissible fiber c row)
    (hfiber : ∀ i j, fiber (row i) → fiber (row j) → i = j) :
    (fiber (row 0) ∧ row 1 = c 1 ∧ row 2 = c 2) ∨
      (row 0 = c 0 ∧ fiber (row 1) ∧ row 2 = c 2) ∨
      (row 0 = c 0 ∧ row 1 = c 1 ∧ fiber (row 2)) ∨
      (row 0 = c 0 ∧ row 1 = c 1 ∧ row 2 = c 2) := by
  rcases hadm 0 with h0f | h0c <;>
    rcases hadm 1 with h1f | h1c <;>
    rcases hadm 2 with h2f | h2c
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 1) <| hfiber 0 1 h0f h1f
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 1) <| hfiber 0 1 h0f h1f
  · exact False.elim <| (by decide : (0 : Alphabet) ≠ 2) <| hfiber 0 2 h0f h2f
  · exact Or.inl ⟨h0f, h1c, h2c⟩
  · exact False.elim <| (by decide : (1 : Alphabet) ≠ 2) <| hfiber 1 2 h1f h2f
  · exact Or.inr <| Or.inl ⟨h0c, h1f, h2c⟩
  · exact Or.inr <| Or.inr <| Or.inl ⟨h0c, h1c, h2f⟩
  · exact Or.inr <| Or.inr <| Or.inr ⟨h0c, h1c, h2c⟩

/--
Generic form of the triangle-base linearity shortcut.  The two named source
sections project to edges sharing `x` and `y`, so their remaining projected
vertices coincide.
-/
theorem linear_two_edges_force_same_third {V : Type*}
    (Edge : V → V → V → Prop)
    (thirdUnique : ∀ {x y z w}, x ≠ y → Edge x y z → Edge x y w → z = w)
    {x y z w : V} (hxy : x ≠ y)
    (hxyz : Edge x y z) (hxyw : Edge x y w) : z = w :=
  thirdUnique hxy hxyz hxyw

/--
Consequently a putative third source section whose projection is injective
on the two remaining representatives is impossible.  For the complete-graph
triangle hypergraph, instantiate `thirdUnique` with
`Erdos847TriangleBase.third_edge_unique` after putting the two shared graph
edges first.
-/
theorem linear_two_edges_rule_out_third {V : Type*}
    (Edge : V → V → V → Prop)
    (thirdUnique : ∀ {x y z w}, x ≠ y → Edge x y z → Edge x y w → z = w)
    {x y z w : V} (hxy : x ≠ y)
    (hxyz : Edge x y z) (hxyw : Edge x y w) (hzw : z ≠ w) : False :=
  hzw (thirdUnique hxy hxyz hxyw)

/-! ## Moving-mask kernels -/

def LinesIntersect {A N : Type*}
    (U W : Combinatorics.Line A N) : Prop :=
  ∃ a b, U a = W b

def LinesCommonPoint {A N : Type*}
    (U W Z : Combinatorics.Line A N) : Prop :=
  ∃ a b c, U a = W b ∧ W b = Z c

def MovingSet {A N : Type*} (U : Combinatorics.Line A N) : Set N :=
  {s | U.idxFun s = none}

def MovingDisjointUnion {A N : Type*}
    (U W Z : Combinatorics.Line A N) : Prop :=
  MovingSet U = MovingSet W ∪ MovingSet Z ∧
    Disjoint (MovingSet W) (MovingSet Z)

/--
The moving masks `S`, `S ∪ T`, `T` and the common `a`-word give the
tripod incidence in the same-range/different-order case.
-/
theorem same_range_tripod_kernel {A N : Type*}
    (U0 U1 U2 : Combinatorics.Line A N) (kind : N → Fin 3)
    (fixed : N → A) (a : A)
    (htable : ∀ s,
      (kind s = 0 →
        U0.idxFun s = some (fixed s) ∧ U1.idxFun s = some (fixed s) ∧
          U2.idxFun s = some (fixed s)) ∧
      (kind s = 1 →
        U0.idxFun s = none ∧ U1.idxFun s = none ∧ U2.idxFun s = some a) ∧
      (kind s = 2 →
        U0.idxFun s = some a ∧ U1.idxFun s = none ∧ U2.idxFun s = none)) :
    LinesCommonPoint U0 U1 U2 ∧ MovingDisjointUnion U1 U0 U2 := by
  have hcommon : U0 a = U1 a ∧ U1 a = U2 a := by
    constructor <;> funext s
    · rcases fin3_cases (kind s) with hk | hk | hk
      · rcases (htable s).1 hk with ⟨h0, h1, h2⟩
        simp [Combinatorics.Line.coe_apply, h0, h1]
      · rcases (htable s).2.1 hk with ⟨h0, h1, h2⟩
        simp [Combinatorics.Line.coe_apply, h0, h1]
      · rcases (htable s).2.2 hk with ⟨h0, h1, h2⟩
        simp [Combinatorics.Line.coe_apply, h0, h1]
    · rcases fin3_cases (kind s) with hk | hk | hk
      · rcases (htable s).1 hk with ⟨h0, h1, h2⟩
        simp [Combinatorics.Line.coe_apply, h1, h2]
      · rcases (htable s).2.1 hk with ⟨h0, h1, h2⟩
        simp [Combinatorics.Line.coe_apply, h1, h2]
      · rcases (htable s).2.2 hk with ⟨h0, h1, h2⟩
        simp [Combinatorics.Line.coe_apply, h1, h2]
  refine ⟨⟨a, a, a, hcommon⟩, ?_, ?_⟩
  · ext s
    rcases fin3_cases (kind s) with hk | hk | hk
    · rcases (htable s).1 hk with ⟨h0, h1, h2⟩
      simp [MovingSet, h0, h1, h2]
    · rcases (htable s).2.1 hk with ⟨h0, h1, h2⟩
      simp [MovingSet, h0, h1, h2]
    · rcases (htable s).2.2 hk with ⟨h0, h1, h2⟩
      simp [MovingSet, h0, h1, h2]
  · rw [Set.disjoint_left]
    intro s hs0 hs2
    rcases fin3_cases (kind s) with hk | hk | hk
    · rcases (htable s).1 hk with ⟨h0, h1, h2⟩
      simpa [MovingSet, h0] using hs0
    · rcases (htable s).2.1 hk with ⟨h0, h1, h2⟩
      simpa [MovingSet, h2] using hs2
    · rcases (htable s).2.2 hk with ⟨h0, h1, h2⟩
      simpa [MovingSet, h0] using hs0

/--
The masks `S ∪ T`, `S`, `T` give the three pairwise intersections in the
distinct-range case.  A coordinate in each of `S` and `T`, together with
`a ≠ b`, rules out a common point, so the outer lines form a triangle.
-/
theorem distinct_range_triangle_kernel {A N : Type*}
    (U0 U1 U2 : Combinatorics.Line A N) (kind : N → Fin 3)
    (fixed : N → A) (a b : A) (hab : a ≠ b)
    (htable : ∀ s,
      (kind s = 0 →
        U0.idxFun s = some (fixed s) ∧ U1.idxFun s = some (fixed s) ∧
          U2.idxFun s = some (fixed s)) ∧
      (kind s = 1 →
        U0.idxFun s = none ∧ U1.idxFun s = none ∧ U2.idxFun s = some a) ∧
      (kind s = 2 →
        U0.idxFun s = none ∧ U1.idxFun s = some b ∧ U2.idxFun s = none))
    (hS : ∃ s, kind s = 1) (hT : ∃ s, kind s = 2) :
    LinesIntersect U0 U1 ∧ LinesIntersect U0 U2 ∧ LinesIntersect U1 U2 ∧
      ¬ LinesCommonPoint U0 U1 U2 ∧ MovingDisjointUnion U0 U1 U2 := by
  have h01 : U0 b = U1 b := by
    funext s
    rcases fin3_cases (kind s) with hk | hk | hk
    · rcases (htable s).1 hk with ⟨h0, h1, h2⟩
      simp [Combinatorics.Line.coe_apply, h0, h1]
    · rcases (htable s).2.1 hk with ⟨h0, h1, h2⟩
      simp [Combinatorics.Line.coe_apply, h0, h1]
    · rcases (htable s).2.2 hk with ⟨h0, h1, h2⟩
      simp [Combinatorics.Line.coe_apply, h0, h1]
  have h02 : U0 a = U2 a := by
    funext s
    rcases fin3_cases (kind s) with hk | hk | hk
    · rcases (htable s).1 hk with ⟨h0, h1, h2⟩
      simp [Combinatorics.Line.coe_apply, h0, h2]
    · rcases (htable s).2.1 hk with ⟨h0, h1, h2⟩
      simp [Combinatorics.Line.coe_apply, h0, h2]
    · rcases (htable s).2.2 hk with ⟨h0, h1, h2⟩
      simp [Combinatorics.Line.coe_apply, h0, h2]
  have h12 : U1 a = U2 b := by
    funext s
    rcases fin3_cases (kind s) with hk | hk | hk
    · rcases (htable s).1 hk with ⟨h0, h1, h2⟩
      simp [Combinatorics.Line.coe_apply, h1, h2]
    · rcases (htable s).2.1 hk with ⟨h0, h1, h2⟩
      simp [Combinatorics.Line.coe_apply, h1, h2]
    · rcases (htable s).2.2 hk with ⟨h0, h1, h2⟩
      simp [Combinatorics.Line.coe_apply, h1, h2]
  refine ⟨⟨b, b, h01⟩, ⟨a, a, h02⟩, ⟨a, b, h12⟩, ?_, ?_, ?_⟩
  · rintro ⟨i, j, k, hij, hjk⟩
    obtain ⟨s, hs⟩ := hS
    rcases (htable s).2.1 hs with ⟨h0s, h1s, h2s⟩
    have hijs := congrFun hij s
    have hjks := congrFun hjk s
    have hi_a : i = a := by
      have hi_j : i = j := by
        simpa [Combinatorics.Line.coe_apply, h0s, h1s] using hijs
      have hj_a : j = a := by
        simpa [Combinatorics.Line.coe_apply, h1s, h2s] using hjks
      exact hi_j.trans hj_a
    obtain ⟨t, ht⟩ := hT
    rcases (htable t).2.2 ht with ⟨h0t, h1t, h2t⟩
    have hijt := congrFun hij t
    have hi_b : i = b := by
      simpa [Combinatorics.Line.coe_apply, h0t, h1t] using hijt
    exact hab (hi_a.symm.trans hi_b)
  · ext s
    rcases fin3_cases (kind s) with hk | hk | hk
    · rcases (htable s).1 hk with ⟨h0, h1, h2⟩
      simp [MovingSet, h0, h1, h2]
    · rcases (htable s).2.1 hk with ⟨h0, h1, h2⟩
      simp [MovingSet, h0, h1, h2]
    · rcases (htable s).2.2 hk with ⟨h0, h1, h2⟩
      simp [MovingSet, h0, h1, h2]
  · rw [Set.disjoint_left]
    intro s hs1 hs2
    rcases fin3_cases (kind s) with hk | hk | hk
    · rcases (htable s).1 hk with ⟨h0, h1, h2⟩
      simpa [MovingSet, h1] using hs1
    · rcases (htable s).2.1 hk with ⟨h0, h1, h2⟩
      simpa [MovingSet, h2] using hs2
    · rcases (htable s).2.2 hk with ⟨h0, h1, h2⟩
      simpa [MovingSet, h1] using hs1

end Erdos847ConfinementKernels
