import Mathlib
import ErdosProblems.Erdos920.MarkedTree

/-!
# The container step in Bradač's off-diagonal Ramsey construction

This file isolates the finite combinatorial part of Lemma 2.12 in Bradač's
paper.  The projective-geometry input is deliberately abstracted into a
finite relation and a rank/closure operator.  Thus this file contains no
assumption that is specific to a choice of coordinates or representatives.

Histories are stored in reverse chronological order.  If `p :: σ` extends
`σ`, then `p` is the newest pair.  This convention makes all generator-set
identities definitional and is also the convention used by `MarkedTree`.
-/

namespace Erdos920.Container

open scoped BigOperators

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The small interface with the linear-algebraic span used by the container
argument.  In the projective application `rank S` is the finrank of the span
of `S`, and `Cl x S` means that `x` belongs to that span. -/
structure RankClosure (P : Type*) [DecidableEq P] where
  rank : Finset P → ℕ
  Cl : P → Finset P → Prop
  decidable_cl : ∀ x S, Decidable (Cl x S)
  rank_mono_insert : ∀ (S : Finset P) (x : P), rank S ≤ rank (insert x S)
  rank_insert_le : ∀ (S : Finset P) (x : P), rank (insert x S) ≤ rank S + 1
  rank_insert_of_not_cl : ∀ (S : Finset P) (x : P), ¬ Cl x S → rank (insert x S) = rank S + 1

attribute [instance] RankClosure.decidable_cl

/-- The generators selected by a history `σ` at a point `y`: a previous
second coordinate is selected exactly when its first coordinate is related
to `y`. -/
def generators (R : P → P → Prop) [DecidableRel R]
    (σ : List (P × P)) (y : P) : Finset P :=
  ((σ.toFinset.filter fun p => R p.1 y).image Prod.snd)

@[simp] lemma generators_nil (R : P → P → Prop) [DecidableRel R] (y : P) :
    generators R [] y = ∅ := by
  simp [generators]

@[simp] lemma generators_cons (R : P → P → Prop) [DecidableRel R]
    (p : P × P) (σ : List (P × P)) (y : P) :
    generators R (p :: σ) y = if R p.1 y then insert p.2 (generators R σ y)
      else generators R σ y := by
  unfold generators
  rw [List.toFinset_cons, Finset.filter_insert]
  split
  · rw [Finset.image_insert]
  · rfl

/-- Rank of the selected generator set. -/
def prefixRank (C : RankClosure P) (R : P → P → Prop) [DecidableRel R]
    (σ : List (P × P)) (y : P) : ℕ :=
  C.rank (generators R σ y)

/-- The rank-at-most-`j` set `U_j^σ`. -/
def U (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (j : ℕ) : Finset P :=
  points.filter fun y => prefixRank C R σ y ≤ j

/-- The exact-rank set `Z_j^σ`. -/
def Z (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (j : ℕ) : Finset P :=
  points.filter fun y => prefixRank C R σ y = j

lemma Z_subset_U (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (j : ℕ) :
    Z points C R σ j ⊆ U points C R σ j := by
  intro y hy
  simp only [Z, Finset.mem_filter] at hy
  simp [U, hy.1, hy.2.le]

lemma U_mono_cons (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (p : P × P) (σ : List (P × P)) (j : ℕ) :
    U points C R (p :: σ) j ⊆ U points C R σ j := by
  intro y hy
  rcases Finset.mem_filter.mp hy with ⟨hypoints, hrank⟩
  apply Finset.mem_filter.mpr
  refine ⟨hypoints, ?_⟩
  simp only [prefixRank, generators_cons] at hrank ⊢
  split at hrank
  · exact (C.rank_mono_insert _ _).trans hrank
  · exact hrank

/-- The compatibility condition for adding `p` after the pairs in `σ`.
It is exactly the forward-independence implication for every old pair. -/
def CanExtend (R : P → P → Prop) (p : P × P) (σ : List (P × P)) : Prop :=
  R p.1 p.2 ∧ ∀ old ∈ σ, R old.1 p.2 → R p.1 old.2

noncomputable instance instDecidableCanExtend (R : P → P → Prop)
    (p : P × P) (σ : List (P × P)) : Decidable (CanExtend R p σ) :=
  Classical.propDecidable _

/-- A reverse history is consistent if every successive addition satisfies
`CanExtend`. -/
def Consistent (R : P → P → Prop) : List (P × P) → Prop
  | [] => True
  | p :: σ => Consistent R σ ∧ CanExtend R p σ

@[simp] lemma consistent_nil (R : P → P → Prop) : Consistent R [] := trivial

@[simp] lemma consistent_cons_iff (R : P → P → Prop) (p : P × P)
    (σ : List (P × P)) :
    Consistent R (p :: σ) ↔ Consistent R σ ∧ CanExtend R p σ := Iff.rfl

/-- All related pairs with both coordinates in `points`.  This is the
vertex set of the abstract looped relation underlying `D★`. -/
noncomputable def relationPairs (points : Finset P) (R : P → P → Prop)
    [DecidableRel R] : Finset (P × P) :=
  points.biUnion fun a => (points.filter fun b => R a b).image fun b => (a, b)

@[simp] theorem mem_relationPairs_iff (points : Finset P) (R : P → P → Prop)
    [DecidableRel R] (p : P × P) :
    p ∈ relationPairs points R ↔ p.1 ∈ points ∧ p.2 ∈ points ∧ R p.1 p.2 := by
  classical
  constructor
  · intro hp
    obtain ⟨a, ha, hpimg⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hpimg
    have hab' := Finset.mem_filter.mp hb
    cases hab
    exact ⟨ha, hab'.1, hab'.2⟩
  · rintro ⟨ha, hb, hR⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1, ha, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨p.2, Finset.mem_filter.mpr ⟨hb, hR⟩, Prod.ext rfl rfl⟩

/-- The children of a consistent prefix: all relation-pairs satisfying the
forward-independence implication against the old prefix. -/
noncomputable def extensionChildren (points : Finset P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) : Finset (P × P) :=
  (relationPairs points R).filter fun p => CanExtend R p σ

lemma extensionChildren_subset_relationPairs
    (points : Finset P) (R : P → P → Prop) [DecidableRel R]
    (σ : List (P × P)) : extensionChildren points R σ ⊆ relationPairs points R :=
  by
    classical
    simpa [extensionChildren] using
      (Finset.filter_subset (fun p => CanExtend R p σ) (relationPairs points R))

/-- Regularity, or merely a uniform degree upper bound, gives the required
total branching bound. -/
theorem relationPairs_card_le (points : Finset P) (R : P → P → Prop)
    [DecidableRel R] (d : ℕ)
    (hdegree : ∀ a ∈ points, (points.filter fun b => R a b).card ≤ d) :
    (relationPairs points R).card ≤ points.card * d := by
  classical
  calc
    (relationPairs points R).card ≤
        ∑ a ∈ points, ((points.filter fun b => R a b).image fun b => (a, b)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ points, d := by
      exact Finset.sum_le_sum fun a ha => Finset.card_image_le.trans (hdegree a ha)
    _ = points.card * d := by simp

theorem extensionChildren_card_le (points : Finset P) (R : P → P → Prop)
    [DecidableRel R] (d : ℕ)
    (hdegree : ∀ a ∈ points, (points.filter fun b => R a b).card ≤ d)
    (σ : List (P × P)) :
    (extensionChildren points R σ).card ≤ points.card * d :=
  (Finset.card_le_card (extensionChildren_subset_relationPairs points R σ)).trans
    (relationPairs_card_le points R d hdegree)

theorem isPath_extensionChildren_consistent
    (points : Finset P) (R : P → P → Prop) [DecidableRel R]
    {xs : List (P × P)}
    (hpath : Erdos920.MarkedTree.IsPath (extensionChildren points R) xs) :
    Consistent R xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
      rcases hpath with ⟨hpath, hx⟩
      have hx' : x ∈ (relationPairs points R).filter fun p => CanExtend R p xs := by
        simpa [extensionChildren] using hx
      exact ⟨ih hpath, (Finset.mem_filter.mp hx').2⟩

/-! ## The poor/popular marking at one node -/

/-- Points of `Z_ℓ` related to a prospective first coordinate. -/
def neighborsInStratum (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (σ : List (P × P)) (ℓ : ℕ) (a : P) :
    Finset P :=
  (Z points C R σ ℓ).filter fun y => R a y

/-- Points of `Z_ℓ` whose old span already contains `b`. -/
def closureInStratum (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (σ : List (P × P)) (ℓ : ℕ) (b : P) :
    Finset P :=
  (Z points C R σ ℓ).filter fun y => C.Cl b (generators R σ y)

/-- A first coordinate is poor if it sees fewer than twice the popularity
threshold many points of the pivot stratum. -/
def Poor (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ) (a : P) : Prop :=
  (neighborsInStratum points C R σ ℓ a).card < 2 * cut

instance instDecidablePoor (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ)
    (a : P) : Decidable (Poor points C R σ ℓ cut a) := by
  unfold Poor
  exact Nat.decLt _ _

/-- A second coordinate is popular if it lies in at least `cut` old spans
over the pivot stratum. -/
def Popular (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ) (b : P) : Prop :=
  cut ≤ (closureInStratum points C R σ ℓ b).card

instance instDecidablePopular (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ)
    (b : P) : Decidable (Popular points C R σ ℓ cut b) := by
  unfold Popular
  exact Nat.decLe _ _

/-- Points which are seen by `a` but whose old span does not contain `b`.
At every such point, adjoining `(a,b)` raises the rank by one. -/
def rankRaisingSet (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (σ : List (P × P)) (ℓ : ℕ)
    (a b : P) : Finset P :=
  (Z points C R σ ℓ).filter fun y => R a y ∧ ¬ C.Cl b (generators R σ y)

/-- The actual Boolean marking used by the tree.  `level` selects the pivot
stratum, while `cut` is the integer popularity threshold at that node. -/
noncomputable def markedByPoorOrPopular {L : Type*}
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (level : List (P × P) → (P × P) → L)
    (levelNat : L → ℕ) (cut : List (P × P) → (P × P) → ℕ)
    (σ : List (P × P)) (p : P × P) : Bool :=
  decide (Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1 ∨
    Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2)

theorem markedByPoorOrPopular_eq_false_iff {L : Type*}
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (level : List (P × P) → (P × P) → L)
    (levelNat : L → ℕ) (cut : List (P × P) → (P × P) → ℕ)
    (σ : List (P × P)) (p : P × P) :
    markedByPoorOrPopular points C R level levelNat cut σ p = false ↔
      ¬ Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1 ∧
      ¬ Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2 := by
  classical
  simp [markedByPoorOrPopular, not_or]

/-- Poor and popular child estimates add to a marked-child estimate. -/
theorem markedChildren_card_le {L : Type*}
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (level : List (P × P) → (P × P) → L)
    (levelNat : L → ℕ) (cut : List (P × P) → (P × P) → ℕ)
    (σ : List (P × P)) (hp hq : ℕ)
    (hpoor : ((extensionChildren points R σ).filter fun p =>
      Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1).card ≤ hp)
    (hpopular : ((extensionChildren points R σ).filter fun p =>
      Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2).card ≤ hq) :
    ((extensionChildren points R σ).filter fun p =>
      markedByPoorOrPopular points C R level levelNat cut σ p = true).card ≤ hp + hq := by
  classical
  let poorChildren := (extensionChildren points R σ).filter fun p =>
    Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1
  let popularChildren := (extensionChildren points R σ).filter fun p =>
    Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2
  have hsubset :
      (extensionChildren points R σ).filter (fun p =>
        markedByPoorOrPopular points C R level levelNat cut σ p = true) ⊆
        poorChildren ∪ popularChildren := by
    intro p hpmark
    have hp' := Finset.mem_filter.mp hpmark
    have hor : Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1 ∨
        Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2 := by
      simpa [markedByPoorOrPopular] using hp'.2
    rcases hor with hor | hor
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp'.1, hor⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp'.1, hor⟩)
  calc
    ((extensionChildren points R σ).filter fun p =>
      markedByPoorOrPopular points C R level levelNat cut σ p = true).card ≤
        (poorChildren ∪ popularChildren).card := Finset.card_le_card hsubset
    _ ≤ poorChildren.card + popularChildren.card :=
      Finset.card_union_le poorChildren popularChildren
    _ ≤ hp + hq := Nat.add_le_add hpoor hpopular

/-- The elementary subtraction behind the poor/popular dichotomy. -/
lemma card_filter_and_not_ge {s : Finset P} {A B : P → Prop}
    [DecidablePred A] [DecidablePred B] {cut : ℕ}
    (hA : 2 * cut ≤ (s.filter A).card) (hB : (s.filter B).card ≤ cut) :
    cut ≤ (s.filter fun x => A x ∧ ¬ B x).card := by
  let a := s.filter A
  let b := s.filter B
  have hdiff : a \ b = s.filter fun x => A x ∧ ¬ B x := by
    ext x
    by_cases hx : x ∈ s <;> simp [a, b, hx]
  have hinter : (a ∩ b).card ≤ b.card :=
    Finset.card_le_card (by intro x hx; exact Finset.mem_of_mem_inter_right hx)
  have hsplit := Finset.card_sdiff_add_card_inter a b
  rw [hdiff] at hsplit
  dsimp [a, b] at hinter hsplit
  omega

lemma rankRaisingSet_card_ge_of_not_poor_not_popular
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ) (a b : P)
    (ha : ¬ Poor points C R σ ℓ cut a)
    (hb : ¬ Popular points C R σ ℓ cut b) :
    cut ≤ (rankRaisingSet points C R σ ℓ a b).card := by
  apply card_filter_and_not_ge
  · simpa [Poor, neighborsInStratum] using (Nat.le_of_not_gt ha)
  · simpa [Popular, closureInStratum] using (Nat.le_of_lt (Nat.lt_of_not_ge hb))

lemma rankRaisingSet_subset_U_diff
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ : ℕ) (a b : P) :
    rankRaisingSet points C R σ ℓ a b ⊆
      U points C R σ ℓ \ U points C R ((a, b) :: σ) ℓ := by
  intro y hy
  simp only [rankRaisingSet, Finset.mem_filter, Z] at hy
  have hyOld : prefixRank C R σ y = ℓ := hy.1.2
  have hyNew : prefixRank C R ((a, b) :: σ) y = ℓ + 1 := by
    simp only [prefixRank, generators_cons, hy.2.1, if_true]
    rw [C.rank_insert_of_not_cl _ _ hy.2.2]
    exact congrArg (fun n => n + 1) hyOld
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hy.1.1, hyOld.le⟩
  · intro h
    have hle : prefixRank C R ((a, b) :: σ) y ≤ ℓ := (Finset.mem_filter.mp h).2
    rw [hyNew] at hle
    omega

/-- An unmarked extension removes at least `cut` elements from its pivot
potential `U_ℓ`.  This is the formal shrinkage assertion corresponding to
(3.21), stated before division so that it works over natural cardinalities. -/
theorem U_card_add_cut_le_of_not_poor_not_popular
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut : ℕ) (a b : P)
    (ha : ¬ Poor points C R σ ℓ cut a)
    (hb : ¬ Popular points C R σ ℓ cut b) :
    (U points C R ((a, b) :: σ) ℓ).card + cut ≤
      (U points C R σ ℓ).card := by
  have hmono := U_mono_cons points C R (a, b) σ ℓ
  have hraise := rankRaisingSet_subset_U_diff points C R σ ℓ a b
  have hcard := rankRaisingSet_card_ge_of_not_poor_not_popular
    points C R σ ℓ cut a b ha hb
  have hdisj : Disjoint (U points C R ((a, b) :: σ) ℓ)
      (rankRaisingSet points C R σ ℓ a b) := by
    apply Finset.disjoint_left.mpr
    intro y hyNew hyRaise
    exact (Finset.mem_sdiff.mp (hraise hyRaise)).2 hyNew
  have hunion :
      U points C R ((a, b) :: σ) ℓ ∪ rankRaisingSet points C R σ ℓ a b ⊆
        U points C R σ ℓ := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hmono hy
    · exact (Finset.mem_sdiff.mp (hraise hy)).1
  have hsum :
      (U points C R ((a, b) :: σ) ℓ).card +
          (rankRaisingSet points C R σ ℓ a b).card ≤
        (U points C R σ ℓ).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  omega

/-- Cleared-denominator version of the multiplicative shrinkage estimate.
If the popularity threshold is at least `|U_ℓ| / K`, then an unmarked step
multiplies the potential by at most `(K-1)/K`. -/
theorem U_card_multiplicative_shrink
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut K : ℕ) (a b : P)
    (hK : 1 ≤ K) (hcut : (U points C R σ ℓ).card ≤ K * cut)
    (ha : ¬ Poor points C R σ ℓ cut a)
    (hb : ¬ Popular points C R σ ℓ cut b) :
    K * (U points C R ((a, b) :: σ) ℓ).card ≤
      (K - 1) * (U points C R σ ℓ).card := by
  have hshrink := U_card_add_cut_le_of_not_poor_not_popular
    points C R σ ℓ cut a b ha hb
  have hKm : K - 1 + 1 = K := Nat.sub_add_cancel hK
  nlinarith

/-! ## Incidence bounds for popular points -/

/-- Double-count the incidences `I x y` between two finite sets. -/
lemma sum_card_filter_eq_sum_card_filter (s t : Finset P) (I : P → P → Prop)
    [DecidableRel I] :
    ∑ x ∈ s, (t.filter fun y => I x y).card =
      ∑ y ∈ t, (s.filter fun x => I x y).card := by
  calc
    ∑ x ∈ s, (t.filter fun y => I x y).card =
        ∑ x ∈ s, ∑ y ∈ t, if I x y then 1 else 0 := by
          congr 1 with x
          exact Finset.card_filter _ _
    _ = ∑ y ∈ t, ∑ x ∈ s, if I x y then 1 else 0 := Finset.sum_comm
    _ = ∑ y ∈ t, (s.filter fun x => I x y).card := by
          congr 1 with y
          exact (Finset.card_filter _ _).symm

/-- If every right fibre has size at most `cap`, then there are at most
`|t|*cap/cut` left points incident with `cut` or more right points.  The
division-free form is what is used in the projective calculation. -/
theorem popular_card_mul_cut_le (s t : Finset P) (I : P → P → Prop)
    [DecidableRel I] (cut cap : ℕ)
    (hfibre : ∀ y ∈ t, (s.filter fun x => I x y).card ≤ cap) :
    ((s.filter fun x => cut ≤ (t.filter fun y => I x y).card).card) * cut ≤
      t.card * cap := by
  let pop := s.filter fun x => cut ≤ (t.filter fun y => I x y).card
  have hleft : pop.card * cut ≤ ∑ x ∈ pop, (t.filter fun y => I x y).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    exact Finset.sum_le_sum fun x hx => by
      simpa [pop] using (Finset.mem_filter.mp hx).2
  have hsub :
      ∑ x ∈ pop, (t.filter fun y => I x y).card ≤
        ∑ x ∈ s, (t.filter fun y => I x y).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact (Finset.mem_filter.mp hx).1
    · intro i hi _
      exact Nat.zero_le _
  have hright : ∑ y ∈ t, (s.filter fun x => I x y).card ≤ t.card * cap := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    exact Finset.sum_le_sum fun y hy => by simpa using hfibre y hy
  dsimp [pop] at hleft ⊢
  exact hleft.trans (hsub.trans ((sum_card_filter_eq_sum_card_filter s t I).le.trans hright))

theorem popularInStratum_card_mul_cut_le
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (σ : List (P × P)) (ℓ cut cap : ℕ)
    (hfibre : ∀ y ∈ Z points C R σ ℓ,
      (points.filter fun b => C.Cl b (generators R σ y)).card ≤ cap) :
    ((points.filter fun b => Popular points C R σ ℓ cut b).card) * cut ≤
      (Z points C R σ ℓ).card * cap := by
  classical
  change
    ((points.filter fun b => cut ≤
      ((Z points C R σ ℓ).filter fun y => C.Cl b (generators R σ y)).card).card) * cut ≤
        (Z points C R σ ℓ).card * cap
  exact popular_card_mul_cut_le points (Z points C R σ ℓ)
    (fun b y => C.Cl b (generators R σ y)) cut cap hfibre

/-! ## Iterating multiplicative shrinkage -/

/-- The product estimate for a potential which is nonincreasing at every
step and contracts by `(K - 1) / K` at selected steps. -/
theorem pow_count_mul_last_le
    {m K : ℕ} (V : Fin (m + 1) → ℕ) (contract : Fin m → Bool)
    (hmono : ∀ i : Fin m, V i.succ ≤ V i.castSucc)
    (hcontract : ∀ i : Fin m, contract i = true →
      K * V i.succ ≤ (K - 1) * V i.castSucc) :
    K ^ (List.ofFn contract).count true * V (Fin.last m) ≤
      (K - 1) ^ (List.ofFn contract).count true * V 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
      let V' : Fin (m + 1) → ℕ := fun i => V i.succ
      let contract' : Fin m → Bool := fun i => contract i.succ
      have hmono' : ∀ i : Fin m, V' i.succ ≤ V' i.castSucc := by
        intro i
        exact hmono i.succ
      have hcontract' : ∀ i : Fin m, contract' i = true →
          K * V' i.succ ≤ (K - 1) * V' i.castSucc := by
        intro i hi
        exact hcontract i.succ hi
      have hi := ih V' contract' hmono' hcontract'
      rw [List.ofFn_succ]
      change
        K ^ ((contract 0 :: List.ofFn contract').count true) * V (Fin.last (m + 1)) ≤
          (K - 1) ^ ((contract 0 :: List.ofFn contract').count true) * V 0
      have hlast : V' (Fin.last m) = V (Fin.last (m + 1)) := rfl
      rw [← hlast]
      cases h0 : contract 0 with
      | false =>
          simp only [h0, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, pow_zero,
            List.count_cons]
          exact hi.trans (Nat.mul_le_mul_left _ (hmono 0))
      | true =>
          simp only [h0, List.count_cons, beq_self_eq_true, if_true, pow_succ]
          calc
            (K ^ (List.ofFn contract').count true * K) * V' (Fin.last m) =
                K * (K ^ (List.ofFn contract').count true * V' (Fin.last m)) := by
                  ac_rfl
            _ ≤ K * ((K - 1) ^ (List.ofFn contract').count true * V' 0) :=
              Nat.mul_le_mul_left K hi
            _ = (K - 1) ^ (List.ofFn contract').count true * (K * V' 0) := by
              ac_rfl
            _ ≤ (K - 1) ^ (List.ofFn contract').count true * ((K - 1) * V 0) :=
              Nat.mul_le_mul_left _ (hcontract 0 h0)
            _ = ((K - 1) ^ (List.ofFn contract').count true * (K - 1)) * V 0 := by
              ac_rfl

/-- Adding one to a potential makes it everywhere positive.  At a selected
step whose old potential is nonzero, a `K`-contraction becomes a
`2*K`-contraction of the shifted potential. -/
lemma shifted_contraction {K A B : ℕ} (hK : 1 ≤ K) (hB : 1 ≤ B)
    (h : K * A ≤ (K - 1) * B) :
    (2 * K) * (A + 1) ≤ (2 * K - 1) * (B + 1) := by
  have hKm : K - 1 + 1 = K := Nat.sub_add_cancel hK
  have htwok : 2 * K - 1 + 1 = 2 * K := Nat.sub_add_cancel (by omega : 1 ≤ 2 * K)
  nlinarith

/-- It is enough to verify the stopping inequality at the first forbidden
exponent `w + 1`; the ratio only decreases at subsequent exponents. -/
theorem power_stopping_of_at_succ {K N w : ℕ} (hK : 1 ≤ K)
    (hstop : (2 * K - 1) ^ (w + 1) * (N + 1) < (2 * K) ^ (w + 1)) :
    ∀ c : ℕ, w < c → (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c := by
  intro c hc
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le (show w + 1 ≤ c by omega)
  rw [hr, pow_add (2 * K - 1) (w + 1) r, pow_add (2 * K) (w + 1) r]
  have hbase : 0 < 2 * K - 1 := by omega
  calc
    ((2 * K - 1) ^ (w + 1) * (2 * K - 1) ^ r) * (N + 1) =
        (2 * K - 1) ^ r * ((2 * K - 1) ^ (w + 1) * (N + 1)) := by ac_rfl
    _ < (2 * K - 1) ^ r * (2 * K) ^ (w + 1) :=
      Nat.mul_lt_mul_of_pos_left hstop (Nat.pow_pos hbase)
    _ ≤ (2 * K) ^ r * (2 * K) ^ (w + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega : 2 * K - 1 ≤ 2 * K) r)
    _ = (2 * K) ^ (w + 1) * (2 * K) ^ r := by ac_rfl

/-- A useful stopping rule for the container argument.  The hypothesis
`hpow` is the sole numerical input: after `w` selected contractions, the
geometric decay beats the initial bound `N`. -/
theorem count_contract_le_of_potential
    {m K N w : ℕ} (V : Fin (m + 1) → ℕ) (contract : Fin m → Bool)
    (hK : 1 ≤ K) (hV0 : V 0 ≤ N)
    (hmono : ∀ i : Fin m, V i.succ ≤ V i.castSucc)
    (hpositive : ∀ i : Fin m, contract i = true → 1 ≤ V i.castSucc)
    (hcontract : ∀ i : Fin m, contract i = true →
      K * V i.succ ≤ (K - 1) * V i.castSucc)
    (hpow : ∀ c : ℕ, w < c →
      (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c) :
    (List.ofFn contract).count true ≤ w := by
  let V' : Fin (m + 1) → ℕ := fun i => V i + 1
  have hmono' : ∀ i : Fin m, V' i.succ ≤ V' i.castSucc := by
    intro i
    exact Nat.add_le_add_right (hmono i) 1
  have hcontract' : ∀ i : Fin m, contract i = true →
      (2 * K) * V' i.succ ≤ (2 * K - 1) * V' i.castSucc := by
    intro i hi
    exact shifted_contraction hK (hpositive i hi) (hcontract i hi)
  have hprod := pow_count_mul_last_le V' contract hmono' hcontract'
  by_contra hc
  have hwc : w < (List.ofFn contract).count true := Nat.lt_of_not_ge hc
  have hstrict := hpow _ hwc
  have hfinal : 1 ≤ V' (Fin.last m) := by simp [V']
  have hstart : V' 0 ≤ N + 1 := Nat.add_le_add_right hV0 1
  have hbad :
      (2 * K) ^ (List.ofFn contract).count true ≤
        (2 * K - 1) ^ (List.ofFn contract).count true * (N + 1) := by
    have hbad' := (Nat.mul_le_mul_left _ hfinal).trans
      (hprod.trans (Nat.mul_le_mul_left _ hstart))
    simpa only [Nat.mul_one] using hbad'
  omega

/-- Sum the fibre cardinalities of a map to a finite type. -/
lemma card_eq_sum_card_fibers {I L : Type*} [DecidableEq I] [Fintype L]
    [DecidableEq L] (s : Finset I) (label : I → L) :
    s.card = ∑ ℓ : L, (s.filter fun i => label i = ℓ).card := by
  classical
  rw [Finset.card_eq_sum_ones]
  calc
    ∑ _i ∈ s, 1 = ∑ i ∈ s, ∑ ℓ : L, if label i = ℓ then 1 else 0 := by simp
    _ = ∑ ℓ : L, ∑ i ∈ s, if label i = ℓ then 1 else 0 := Finset.sum_comm
    _ = ∑ ℓ : L, (s.filter fun i => label i = ℓ).card := by
      apply Finset.sum_congr rfl
      intro ℓ _
      exact (Finset.card_filter _ _).symm

/-- Pigeonhole packaging used after applying the potential estimate once
for each of the `levels` possible ranks. -/
theorem card_le_levels_mul_of_fibers_le {I L : Type*} [DecidableEq I]
    [Fintype L] [DecidableEq L] (s : Finset I) (label : I → L) (r : ℕ)
    (hfibre : ∀ ℓ : L, (s.filter fun i => label i = ℓ).card ≤ r) :
    s.card ≤ Fintype.card L * r := by
  rw [card_eq_sum_card_fibers s label]
  calc
    ∑ ℓ : L, (s.filter fun i => label i = ℓ).card ≤ ∑ _ℓ : L, r :=
      Finset.sum_le_sum fun ℓ _ => hfibre ℓ
    _ = Fintype.card L * r := by simp

/-! ## A reusable certificate for the pathwise unmarked bound -/

/-- Number of unmarked steps on a reversed history. -/
def unmarkedCount {A : Type*} (marked : List A → A → Bool) : List A → ℕ
  | [] => 0
  | x :: xs => unmarkedCount marked xs + if marked xs x = false then 1 else 0

/-- Number of unmarked steps assigned to one potential/level. -/
def selectedCount {A L : Type*} [DecidableEq L]
    (marked : List A → A → Bool) (level : List A → A → L) (ℓ : L) : List A → ℕ
  | [] => 0
  | x :: xs => selectedCount marked level ℓ xs +
      if marked xs x = false ∧ level xs x = ℓ then 1 else 0

@[simp] lemma unmarkedCount_eq_count_false {A : Type*}
    (marked : List A → A → Bool) (xs : List A) :
    unmarkedCount marked xs =
      (Erdos920.MarkedTree.pathSignature marked xs).count false := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [unmarkedCount, Erdos920.MarkedTree.pathSignature, List.count_cons, ih]
      cases h : marked xs x <;> simp [h]

lemma unmarkedCount_eq_sum_selectedCount {A L : Type*} [Fintype L] [DecidableEq L]
    (marked : List A → A → Bool) (level : List A → A → L) (xs : List A) :
    unmarkedCount marked xs = ∑ ℓ : L, selectedCount marked level ℓ xs := by
  classical
  induction xs with
  | nil => simp [unmarkedCount, selectedCount]
  | cons x xs ih =>
      rw [unmarkedCount, ih]
      simp only [selectedCount, Finset.sum_add_distrib]
      by_cases hm : marked xs x = false
      · simp [hm]
      · have ht : marked xs x = true := by
          cases h : marked xs x <;> simp_all
        simp [hm, ht]

/-- Abstract data needed to prove that a root path has few unmarked steps.
The level assigned to a child chooses which monotone potential contracts. -/
structure PathShrinkCertificate {A L : Type*} [DecidableEq A] [Fintype L]
    (children : List A → Finset A) (marked : List A → A → Bool)
    (K N : ℕ) where
  potential : L → List A → ℕ
  level : List A → A → L
  initial_le : ∀ ℓ, potential ℓ [] ≤ N
  mono : ∀ ℓ σ x, x ∈ children σ → potential ℓ (x :: σ) ≤ potential ℓ σ
  positive : ∀ σ x, x ∈ children σ → marked σ x = false →
    1 ≤ potential (level σ x) σ
  contract : ∀ σ x, x ∈ children σ → marked σ x = false →
    K * potential (level σ x) (x :: σ) ≤
      (K - 1) * potential (level σ x) σ

/-- Build the path certificate directly from the rank strata and the
poor/popular marking.  The two explicit geometric obligations are exactly
the ones used in Bradač's proof: the chosen pivot stratum is nonempty, and
its cutoff is at least `|U|/K` after clearing denominators. -/
noncomputable def rankPathShrinkCertificate {L : Type*} [Fintype L] [DecidableEq L]
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (level : List (P × P) → (P × P) → L)
    (levelNat : L → ℕ) (cut : List (P × P) → (P × P) → ℕ)
    (K : ℕ) (hK : 1 ≤ K)
    (hpivot : ∀ σ p, p ∈ extensionChildren points R σ →
      (Z points C R σ (levelNat (level σ p))).Nonempty)
    (hcut : ∀ σ p, p ∈ extensionChildren points R σ →
      (U points C R σ (levelNat (level σ p))).card ≤ K * cut σ p) :
    PathShrinkCertificate (L := L) (extensionChildren points R)
      (markedByPoorOrPopular points C R level levelNat cut) K points.card where
  potential ℓ σ := (U points C R σ (levelNat ℓ)).card
  level := level
  initial_le ℓ := Finset.card_filter_le _ _
  mono ℓ σ p _ := Finset.card_le_card (U_mono_cons points C R p σ (levelNat ℓ))
  positive σ p hp _ := by
    obtain ⟨y, hy⟩ := hpivot σ p hp
    exact (Finset.card_pos.mpr ⟨y, Z_subset_U points C R σ _ hy⟩)
  contract σ p hp hmark := by
    have hn := (markedByPoorOrPopular_eq_false_iff
      points C R level levelNat cut σ p).mp hmark
    exact U_card_multiplicative_shrink points C R σ
      (levelNat (level σ p)) (cut σ p) K p.1 p.2 hK (hcut σ p hp) hn.1 hn.2

/-- Iteration of one selected potential along a certified path.  We use the
shifted potential, hence the denominator `2*K`; see `shifted_contraction`. -/
theorem pow_selectedCount_mul_potential_le
    {A L : Type*} [DecidableEq A] [Fintype L] [DecidableEq L]
    {children : List A → Finset A} {marked : List A → A → Bool}
    {K N : ℕ} (cert : PathShrinkCertificate (L := L) children marked K N)
    (hK : 1 ≤ K) (xs : List A) (hpath : Erdos920.MarkedTree.IsPath children xs)
    (ℓ : L) :
    (2 * K) ^ selectedCount marked cert.level ℓ xs * (cert.potential ℓ xs + 1) ≤
      (2 * K - 1) ^ selectedCount marked cert.level ℓ xs *
        (cert.potential ℓ [] + 1) := by
  induction xs with
  | nil => simp [selectedCount]
  | cons x xs ih =>
      rcases hpath with ⟨hpath, hx⟩
      have ih' := ih hpath
      have hmono := cert.mono ℓ xs x hx
      by_cases hs : marked xs x = false ∧ cert.level xs x = ℓ
      · have hpos : 1 ≤ cert.potential (cert.level xs x) xs :=
          cert.positive xs x hx hs.1
        have hcontract := shifted_contraction hK hpos (cert.contract xs x hx hs.1)
        rw [hs.2] at hcontract
        simp only [selectedCount, hs, if_true, pow_succ]
        calc
          ((2 * K) ^ selectedCount marked cert.level ℓ xs * (2 * K)) *
                (cert.potential ℓ (x :: xs) + 1) =
              (2 * K) ^ selectedCount marked cert.level ℓ xs *
                ((2 * K) * (cert.potential ℓ (x :: xs) + 1)) := by ac_rfl
          _ ≤ (2 * K) ^ selectedCount marked cert.level ℓ xs *
                ((2 * K - 1) * (cert.potential ℓ xs + 1)) :=
              Nat.mul_le_mul_left _ hcontract
          _ = (2 * K - 1) *
                ((2 * K) ^ selectedCount marked cert.level ℓ xs *
                  (cert.potential ℓ xs + 1)) := by ac_rfl
          _ ≤ (2 * K - 1) *
                ((2 * K - 1) ^ selectedCount marked cert.level ℓ xs *
                  (cert.potential ℓ [] + 1)) := Nat.mul_le_mul_left _ ih'
          _ = ((2 * K - 1) ^ selectedCount marked cert.level ℓ xs * (2 * K - 1)) *
                (cert.potential ℓ [] + 1) := by ac_rfl
      · simp only [selectedCount, hs, if_false]
        exact (Nat.mul_le_mul_left _ (Nat.add_le_add_right hmono 1)).trans ih'

/-- The numerical stopping condition bounds the selected steps assigned to
any one level. -/
theorem selectedCount_le_of_certificate
    {A L : Type*} [DecidableEq A] [Fintype L] [DecidableEq L]
    {children : List A → Finset A} {marked : List A → A → Bool}
    {K N w : ℕ} (cert : PathShrinkCertificate (L := L) children marked K N)
    (hK : 1 ≤ K)
    (hpow : ∀ c : ℕ, w < c → (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c)
    (xs : List A) (hpath : Erdos920.MarkedTree.IsPath children xs) (ℓ : L) :
    selectedCount marked cert.level ℓ xs ≤ w := by
  by_contra h
  have hwc : w < selectedCount marked cert.level ℓ xs := Nat.lt_of_not_ge h
  have hprod := pow_selectedCount_mul_potential_le cert hK xs hpath ℓ
  have hfinal : 1 ≤ cert.potential ℓ xs + 1 := by omega
  have hinitial : cert.potential ℓ [] + 1 ≤ N + 1 :=
    Nat.add_le_add_right (cert.initial_le ℓ) 1
  have hbad : (2 * K) ^ selectedCount marked cert.level ℓ xs ≤
      (2 * K - 1) ^ selectedCount marked cert.level ℓ xs * (N + 1) := by
    have hbad' := (Nat.mul_le_mul_left _ hfinal).trans
      (hprod.trans (Nat.mul_le_mul_left _ hinitial))
    simpa only [Nat.mul_one] using hbad'
  exact (Nat.not_lt_of_ge hbad) (hpow _ hwc)

/-- A path has at most `card L * w` unmarked steps: apply the potential bound
to every level and sum the disjoint level classes. -/
theorem unmarkedCount_le_of_certificate
    {A L : Type*} [DecidableEq A] [Fintype L] [DecidableEq L]
    {children : List A → Finset A} {marked : List A → A → Bool}
    {K N w : ℕ} (cert : PathShrinkCertificate (L := L) children marked K N)
    (hK : 1 ≤ K)
    (hpow : ∀ c : ℕ, w < c → (2 * K - 1) ^ c * (N + 1) < (2 * K) ^ c)
    (xs : List A) (hpath : Erdos920.MarkedTree.IsPath children xs) :
    (Erdos920.MarkedTree.pathSignature marked xs).count false ≤ Fintype.card L * w := by
  rw [← unmarkedCount_eq_count_false,
    unmarkedCount_eq_sum_selectedCount (L := L)]
  calc
    ∑ ℓ : L, selectedCount marked cert.level ℓ xs ≤ ∑ _ℓ : L, w :=
      Finset.sum_le_sum fun ℓ _ =>
        selectedCount_le_of_certificate (L := L) cert hK hpow xs hpath ℓ
    _ = Fintype.card L * w := by simp

/-! ## Feeding a certified container into the marked-tree count -/

/-- All paths of length `m`, represented using an arbitrary marking.  The
bound `m` is vacuous, since a Boolean word of length `m` has at most `m`
false entries. -/
noncomputable def allPaths {A : Type*} [DecidableEq A]
    (children : List A → Finset A) (marked : List A → A → Bool) (m : ℕ) :
    Finset (List A) :=
  Erdos920.MarkedTree.boundedPaths children marked m m

@[simp] theorem mem_allPaths_iff {A : Type*} [DecidableEq A]
    (children : List A → Finset A) (marked : List A → A → Bool)
    (xs : List A) (m : ℕ) :
    xs ∈ allPaths children marked m ↔
      Erdos920.MarkedTree.IsPath children xs ∧ xs.length = m := by
  rw [allPaths, Erdos920.MarkedTree.mem_boundedPaths_iff]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hpath, hlen⟩
    refine ⟨hpath, hlen, ?_⟩
    rw [← hlen, ← Erdos920.MarkedTree.pathSignature_length marked xs]
    exact List.count_le_length

/-- The abstract final count: once the geometric work supplies total-child,
marked-child, and pathwise-unmarked bounds, no further loss occurs before
the marked-tree estimate. -/
theorem card_allPaths_le {A : Type*} [DecidableEq A]
    (children : List A → Finset A) (marked : List A → A → Bool)
    {Delta h m w : ℕ}
    (hchildren : ∀ xs, (children xs).card ≤ Delta)
    (hmarked : ∀ xs, ((children xs).filter fun x => marked xs x = true).card ≤ h)
    (hunmarked : ∀ xs, Erdos920.MarkedTree.IsPath children xs → xs.length = m →
      (Erdos920.MarkedTree.pathSignature marked xs).count false ≤ w)
    (hhDelta : h ≤ Delta) (hwm : w ≤ m) :
    (allPaths children marked m).card ≤ 2 ^ m * Delta ^ w * h ^ (m - w) := by
  classical
  have hsubset : allPaths children marked m ⊆
      Erdos920.MarkedTree.boundedPaths children marked m w := by
    intro xs hxs
    have hx := (mem_allPaths_iff children marked xs m).mp hxs
    exact (Erdos920.MarkedTree.mem_boundedPaths_iff children marked xs m w).mpr
      ⟨hx.1, hx.2, hunmarked xs hx.1 hx.2⟩
  exact (Finset.card_le_card hsubset).trans
    (Erdos920.MarkedTree.card_boundedPaths_le children marked
      hchildren hmarked hhDelta hwm)

/-- Complete abstract form of Bradač's forward-independent tuple bound.

The projective instantiation supplies regularity (`hdegree`), the two mixing
and incidence estimates (`hpoor`, `hpopular`), and the maximizing-pivot
facts (`hpivot`, `hcut`).  The rest of the conclusion is proved here. -/
theorem rankContainer_count {L : Type*} [Fintype L] [DecidableEq L]
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (level : List (P × P) → (P × P) → L)
    (levelNat : L → ℕ) (cut : List (P × P) → (P × P) → ℕ)
    {d hp hq K w m : ℕ}
    (hdegree : ∀ a ∈ points, (points.filter fun b => R a b).card ≤ d)
    (hpoor : ∀ σ, ((extensionChildren points R σ).filter fun p =>
      Poor points C R σ (levelNat (level σ p)) (cut σ p) p.1).card ≤ hp)
    (hpopular : ∀ σ, ((extensionChildren points R σ).filter fun p =>
      Popular points C R σ (levelNat (level σ p)) (cut σ p) p.2).card ≤ hq)
    (hK : 1 ≤ K)
    (hpivot : ∀ σ p, p ∈ extensionChildren points R σ →
      (Z points C R σ (levelNat (level σ p))).Nonempty)
    (hcut : ∀ σ p, p ∈ extensionChildren points R σ →
      (U points C R σ (levelNat (level σ p))).card ≤ K * cut σ p)
    (hpow : ∀ c : ℕ, w < c →
      (2 * K - 1) ^ c * (points.card + 1) < (2 * K) ^ c)
    (hmarkedTotal : hp + hq ≤ points.card * d)
    (hunmarkedLength : Fintype.card L * w ≤ m) :
    (allPaths (extensionChildren points R)
      (markedByPoorOrPopular points C R level levelNat cut) m).card ≤
      2 ^ m * (points.card * d) ^ (Fintype.card L * w) *
        (hp + hq) ^ (m - Fintype.card L * w) := by
  classical
  let marked := markedByPoorOrPopular points C R level levelNat cut
  let cert := rankPathShrinkCertificate points C R level levelNat cut K hK hpivot hcut
  apply card_allPaths_le (extensionChildren points R) marked
  · exact fun σ => extensionChildren_card_le points R d hdegree σ
  · intro σ
    exact markedChildren_card_le points C R level levelNat cut σ hp hq
      (hpoor σ) (hpopular σ)
  · intro xs hpath _
    exact unmarkedCount_le_of_certificate (L := L) cert hK hpow xs hpath
  · exact hmarkedTotal
  · exact hunmarkedLength

end Erdos920.Container
