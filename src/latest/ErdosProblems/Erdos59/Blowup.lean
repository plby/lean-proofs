/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos59.Matching

/-!
# Three-fold matching blowups

This file isolates the elementary graph-theoretic part of the construction used
for Erdős Problem 59.  Every vertex of a base graph is replaced by a fibre of
three vertices, and every base edge is replaced by an arbitrary matching
between the corresponding fibres.

The projection of a simple six-cycle in the blowup is a closed walk of length
six in the base.  It cannot immediately backtrack: two successive matching
edges over the same base edge would return to the same vertex in the fibre.
Consequently, a repeated vertex in the projected walk gives a triangle; if
there is no repeated vertex, the projected walk is a six-cycle.
-/

namespace Erdos59

/-- Independently choose one of the 34 matchings for each unordered base
edge. -/
abbrev MatchingChoice {V : Type*} (G : SimpleGraph V) := G.edgeSet → Matching

/-- The edge of `G` certified by an adjacency proof. -/
def certifiedEdge {V : Type*} {G : SimpleGraph V} {u v : V} (h : G.Adj u v) :
    G.edgeSet :=
  ⟨s(u, v), h⟩

/-- Interpret the matching on an unordered edge from the orientation `u → v`.
The linear order is used only to decide which endpoint is the left fibre. -/
def matchingChoiceRel {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (C : MatchingChoice G) {u v : V} (h : G.Adj u v) (i j : Fibre) : Prop :=
  if u < v then (C (certifiedEdge h)).Rel i j
  else (C (certifiedEdge h)).Rel j i

lemma matchingChoiceRel_symmetric {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoice G) {u v : V} (h : G.Adj u v)
    (i j : Fibre) :
    matchingChoiceRel C h i j ↔ matchingChoiceRel C h.symm j i := by
  by_cases huv : u < v
  · have hvu : ¬v < u := not_lt_of_ge huv.le
    have he : certifiedEdge h.symm = certifiedEdge h := by
      apply Subtype.ext
      exact Sym2.eq_swap
    simp [matchingChoiceRel, huv, hvu, he]
  · have hvu : v < u := lt_of_le_of_ne (le_of_not_gt huv) h.ne.symm
    have he : certifiedEdge h.symm = certifiedEdge h := by
      apply Subtype.ext
      exact Sym2.eq_swap
    simp [matchingChoiceRel, huv, hvu, he]

/-- Functionality of a chosen matching from the left endpoint of an oriented
base edge. -/
lemma matchingChoiceRel_left_unique {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoice G) {u v : V} (h : G.Adj u v)
    {i j j' : Fibre} (hj : matchingChoiceRel C h i j)
    (hj' : matchingChoiceRel C h i j') : j = j' := by
  by_cases huv : u < v
  · exact (C (certifiedEdge h)).left_unique
      (by simpa [matchingChoiceRel, huv] using hj)
      (by simpa [matchingChoiceRel, huv] using hj')
  · exact (C (certifiedEdge h)).right_unique
      (by simpa [matchingChoiceRel, huv] using hj)
      (by simpa [matchingChoiceRel, huv] using hj')

/-- Functionality of a chosen matching from the right endpoint of an oriented
base edge. -/
lemma matchingChoiceRel_right_unique {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoice G) {u v : V} (h : G.Adj u v)
    {i i' j : Fibre} (hi : matchingChoiceRel C h i j)
    (hi' : matchingChoiceRel C h i' j) : i = i' := by
  have hr : matchingChoiceRel C h.symm j i :=
    (matchingChoiceRel_symmetric C h i j).mp hi
  have hr' : matchingChoiceRel C h.symm j i' :=
    (matchingChoiceRel_symmetric C h i' j).mp hi'
  exact matchingChoiceRel_left_unique C h.symm hr hr'

/-- The three-fold matching blowup specified by `C`. -/
def matchingBlowup {V : Type*} [LinearOrder V]
    (G : SimpleGraph V) (C : MatchingChoice G) : SimpleGraph (V × Fibre) where
  Adj x y := ∃ h : G.Adj x.1 y.1, matchingChoiceRel C h x.2 y.2
  symm := ⟨by
    rintro x y ⟨h, hC⟩
    exact ⟨h.symm, (matchingChoiceRel_symmetric C h _ _).mp hC⟩⟩
  loopless := ⟨by
    rintro x ⟨h, -⟩
    exact h.ne rfl⟩

@[simp] lemma matchingBlowup_adj {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (C : MatchingChoice G) (x y : V × Fibre) :
    (matchingBlowup G C).Adj x y ↔
      ∃ h : G.Adj x.1 y.1, matchingChoiceRel C h x.2 y.2 :=
  Iff.rfl

/-- Restricting the blowup to a fixed ordered pair of fibres recovers the
chosen matching on that base edge. -/
lemma matchingRel_iff_adj {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (C : MatchingChoice G) {u v : V} (h : G.Adj u v) (i j : Fibre) :
    matchingChoiceRel C h i j ↔ (matchingBlowup G C).Adj (u, i) (v, j) := by
  constructor
  · exact fun hij ↦ ⟨h, hij⟩
  · rintro ⟨h', hij⟩
    simpa only [Subsingleton.elim h' h] using hij

/-- The first projection is a graph homomorphism from a matching blowup to its
base graph. -/
def matchingBlowupProjection {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    (C : MatchingChoice G) : matchingBlowup G C →g G where
  toFun := Prod.fst
  map_rel' := by
    rintro x y ⟨h, -⟩
    exact h

@[simp] lemma matchingBlowupProjection_apply {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoice G) (x : V × Fibre) :
    matchingBlowupProjection C x = x.1 :=
  rfl

/-- Equality of matching blowups is exactly agreement of all the choices on
base-edge fibre pairs.  In particular, no information about a choice is lost
by passing to its blowup graph. -/
theorem matchingBlowup_injective {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} : Function.Injective (matchingBlowup G) := by
  intro A B hAB
  funext e
  apply Matching.ext
  intro i j
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := he
      by_cases hlt : u < v
      · calc
          (A ⟨s(u, v), he⟩).Rel i j ↔ matchingChoiceRel A huv i j := by
            simp [matchingChoiceRel, hlt, certifiedEdge]
          _ ↔ (matchingBlowup G A).Adj (u, i) (v, j) :=
            matchingRel_iff_adj A huv i j
          _ ↔ (matchingBlowup G B).Adj (u, i) (v, j) := by rw [hAB]
          _ ↔ matchingChoiceRel B huv i j :=
            (matchingRel_iff_adj B huv i j).symm
          _ ↔ (B ⟨s(u, v), he⟩).Rel i j := by
            simp [matchingChoiceRel, hlt, certifiedEdge]
      · have hgt : v < u := lt_of_le_of_ne (le_of_not_gt hlt) huv.ne.symm
        calc
          (A ⟨s(u, v), he⟩).Rel i j ↔ matchingChoiceRel A huv.symm i j := by
            simp [matchingChoiceRel, hgt, certifiedEdge, Sym2.eq_swap]
          _ ↔ (matchingBlowup G A).Adj (v, i) (u, j) :=
            matchingRel_iff_adj A huv.symm i j
          _ ↔ (matchingBlowup G B).Adj (v, i) (u, j) := by rw [hAB]
          _ ↔ matchingChoiceRel B huv.symm i j :=
            (matchingRel_iff_adj B huv.symm i j).symm
          _ ↔ (B ⟨s(u, v), he⟩).Rel i j := by
            simp [matchingChoiceRel, hgt, certifiedEdge, Sym2.eq_swap]

theorem matchingBlowup_eq_iff {V : Type*} [LinearOrder V]
    {G : SimpleGraph V} {A B : MatchingChoice G} :
    matchingBlowup G A = matchingBlowup G B ↔ A = B := by
  constructor
  · exact fun h ↦ matchingBlowup_injective h
  · rintro rfl
    rfl

/-- Going across one chosen matching and immediately back across the same
base edge returns to the same lifted vertex.  This is the nonbacktracking
input in the six-cycle argument. -/
lemma eq_of_adj_adj_of_fst_eq {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    {C : MatchingChoice G} {x y z : V × Fibre}
    (hxy : (matchingBlowup G C).Adj x y)
    (hyz : (matchingBlowup G C).Adj y z) (hxz : x.1 = z.1) : x = z := by
  rcases x with ⟨xv, xi⟩
  rcases y with ⟨yv, yi⟩
  rcases z with ⟨zv, zi⟩
  change xv = zv at hxz
  subst zv
  rcases hxy with ⟨h, hC⟩
  rcases hyz with ⟨h', hC'⟩
  have hidx : xi = zi := by
    apply matchingChoiceRel_right_unique C h hC
    have hC'' : matchingChoiceRel C h.symm yi zi := by
      simpa only [Subsingleton.elim h' h.symm] using hC'
    exact (matchingChoiceRel_symmetric C h _ _).mpr hC''
  exact Prod.ext rfl hidx

/-- Nonbacktracking form of `eq_of_adj_adj_of_fst_eq`: distinct vertices at
distance two in the lifted walk have distinct projections. -/
lemma fst_ne_of_adj_adj_of_ne {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    {C : MatchingChoice G} {x y z : V × Fibre}
    (hxy : (matchingBlowup G C).Adj x y)
    (hyz : (matchingBlowup G C).Adj y z) (hxz : x ≠ z) : x.1 ≠ z.1 := by
  intro h
  exact hxz (eq_of_adj_adj_of_fst_eq hxy hyz h)

/-- Triangle-freeness in an edge-oriented form convenient for projected
walks. -/
def TriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬G.Adj c a

/-- A graph is `C₆`-free if no six distinct vertices occur consecutively
around a closed six-edge walk. -/
def C6Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c d e f : V⦄,
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d e → G.Adj e f → G.Adj f a →
    ¬[a, b, c, d, e, f].Nodup

/-- The complete length-six projection classification needed below.  A
nonbacktracking closed walk of length six in a triangle-free graph has six
distinct projected vertices. -/
lemma projected_six_nodup {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    {C : MatchingChoice G} (htriangle : TriangleFree G)
    {x₀ x₁ x₂ x₃ x₄ x₅ : V × Fibre}
    (h₀₁ : (matchingBlowup G C).Adj x₀ x₁)
    (h₁₂ : (matchingBlowup G C).Adj x₁ x₂)
    (h₂₃ : (matchingBlowup G C).Adj x₂ x₃)
    (h₃₄ : (matchingBlowup G C).Adj x₃ x₄)
    (h₄₅ : (matchingBlowup G C).Adj x₄ x₅)
    (h₅₀ : (matchingBlowup G C).Adj x₅ x₀)
    (hnodup : [x₀, x₁, x₂, x₃, x₄, x₅].Nodup) :
    [x₀.1, x₁.1, x₂.1, x₃.1, x₄.1, x₅.1].Nodup := by
  have b₀₁ : G.Adj x₀.1 x₁.1 := (matchingBlowupProjection C).map_rel h₀₁
  have b₁₂ : G.Adj x₁.1 x₂.1 := (matchingBlowupProjection C).map_rel h₁₂
  have b₂₃ : G.Adj x₂.1 x₃.1 := (matchingBlowupProjection C).map_rel h₂₃
  have b₃₄ : G.Adj x₃.1 x₄.1 := (matchingBlowupProjection C).map_rel h₃₄
  have b₄₅ : G.Adj x₄.1 x₅.1 := (matchingBlowupProjection C).map_rel h₄₅
  have b₅₀ : G.Adj x₅.1 x₀.1 := (matchingBlowupProjection C).map_rel h₅₀
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
    or_false, not_or] at hnodup ⊢
  rcases hnodup with ⟨h₀, h₁, h₂, h₃, n₄₅, -, -⟩
  rcases h₀ with ⟨n₀₁, n₀₂, n₀₃, n₀₄, n₀₅⟩
  rcases h₁ with ⟨n₁₂, n₁₃, n₁₄, n₁₅⟩
  rcases h₂ with ⟨n₂₃, n₂₄, n₂₅⟩
  rcases h₃ with ⟨n₃₄, n₃₅⟩
  have p₀₁ : x₀.1 ≠ x₁.1 := b₀₁.ne
  have p₀₂ : x₀.1 ≠ x₂.1 := fst_ne_of_adj_adj_of_ne h₀₁ h₁₂ n₀₂
  have p₀₄ : x₀.1 ≠ x₄.1 :=
    (fst_ne_of_adj_adj_of_ne h₄₅ h₅₀ (Ne.symm n₀₄)).symm
  have p₀₅ : x₀.1 ≠ x₅.1 := b₅₀.ne.symm
  have p₁₂ : x₁.1 ≠ x₂.1 := b₁₂.ne
  have p₁₃ : x₁.1 ≠ x₃.1 := fst_ne_of_adj_adj_of_ne h₁₂ h₂₃ n₁₃
  have p₁₅ : x₁.1 ≠ x₅.1 :=
    (fst_ne_of_adj_adj_of_ne h₅₀ h₀₁ (Ne.symm n₁₅)).symm
  have p₂₃ : x₂.1 ≠ x₃.1 := b₂₃.ne
  have p₂₄ : x₂.1 ≠ x₄.1 := fst_ne_of_adj_adj_of_ne h₂₃ h₃₄ n₂₄
  have p₃₄ : x₃.1 ≠ x₄.1 := b₃₄.ne
  have p₃₅ : x₃.1 ≠ x₅.1 := fst_ne_of_adj_adj_of_ne h₃₄ h₄₅ n₃₅
  have p₄₅ : x₄.1 ≠ x₅.1 := b₄₅.ne
  have p₀₃ : x₀.1 ≠ x₃.1 := by
    intro h
    apply htriangle b₀₁ b₁₂
    simpa [h] using b₂₃
  have p₁₄ : x₁.1 ≠ x₄.1 := by
    intro h
    apply htriangle b₁₂ b₂₃
    simpa [h] using b₃₄
  have p₂₅ : x₂.1 ≠ x₅.1 := by
    intro h
    apply htriangle b₂₃ b₃₄
    simpa [h] using b₄₅
  exact ⟨⟨p₀₁, p₀₂, p₀₃, p₀₄, p₀₅⟩,
    ⟨p₁₂, p₁₃, p₁₄, p₁₅⟩, ⟨p₂₃, p₂₄, p₂₅⟩,
    ⟨p₃₄, p₃₅⟩, p₄₅, trivial, List.nodup_nil⟩

/-- A three-fold matching blowup of a triangle-free and `C₆`-free graph is
again `C₆`-free. -/
theorem matchingBlowup_c6Free {V : Type*} [Fintype V] [LinearOrder V]
    {G : SimpleGraph V} (C : MatchingChoice G)
    (htriangle : TriangleFree G) (hC6 : C6Free G) :
    C6Free (matchingBlowup G C) := by
  intro x₀ x₁ x₂ x₃ x₄ x₅ h₀₁ h₁₂ h₂₃ h₃₄ h₄₅ h₅₀ hnodup
  apply hC6
    ((matchingBlowupProjection C).map_rel h₀₁)
    ((matchingBlowupProjection C).map_rel h₁₂)
    ((matchingBlowupProjection C).map_rel h₂₃)
    ((matchingBlowupProjection C).map_rel h₃₄)
    ((matchingBlowupProjection C).map_rel h₄₅)
    ((matchingBlowupProjection C).map_rel h₅₀)
  exact projected_six_nodup htriangle h₀₁ h₁₂ h₂₃ h₃₄ h₄₅ h₅₀ hnodup

end Erdos59
