/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Geometric exclusion counts for the sparse Hales--Jewett selection

This standalone scratch module formalizes the three estimates in the proof of
Reiher--Rödl--Sales Claim 3.9.  It uses the same exact tripod and triangle
predicates as `Erdos847SparseLines.lean`, but repeats the small incidence API so
that the file can be checked independently of precompiled scratch modules.
-/

namespace Erdos847LineExclusions

open Function Set
open Combinatorics
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {A : Type u} {I : Type*}

/-- The cube vertices on a combinatorial line. -/
def linePoints (l : Line A I) : Set (I → A) := Set.range l

@[simp] lemma mem_linePoints (l : Line A I) (x : I → A) :
    x ∈ linePoints l ↔ ∃ a, l a = x := Iff.rfl

/-- Moving coordinates of a combinatorial line. -/
def movingSet [Fintype I] (l : Line A I) : Finset I :=
  Finset.univ.filter fun i ↦ l.idxFun i = none

@[simp] lemma mem_movingSet [Fintype I] (l : Line A I) (i : I) :
    i ∈ movingSet l ↔ l.idxFun i = none := by
  simp [movingSet]

lemma line_idxFun_injective :
    Function.Injective (Line.idxFun : Line A I → I → Option A) := by
  intro l m h
  cases l with
  | mk lf lp =>
      cases m with
      | mk mf mp =>
          simp only at h
          subst mf
          rfl

/-- Through a fixed cube point, a line is determined by its moving support. -/
lemma line_eq_of_movingSet_eq_of_mem [Fintype I] {l m : Line A I}
    (hmove : movingSet l = movingSet m) {x : I → A}
    (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m) : l = m := by
  rcases hxl with ⟨a, ha⟩
  rcases hxm with ⟨b, hb⟩
  apply line_idxFun_injective
  funext i
  by_cases hi : i ∈ movingSet l
  · have hil : l.idxFun i = none := (mem_movingSet l i).mp hi
    have him : m.idxFun i = none := (mem_movingSet m i).mp (hmove ▸ hi)
    simp [hil, him]
  · have hil : l.idxFun i ≠ none := fun h ↦ hi ((mem_movingSet l i).mpr h)
    have him : m.idxFun i ≠ none := by
      intro h
      exact hi (hmove.symm ▸ (mem_movingSet m i).mpr h)
    cases hl : l.idxFun i with
    | none => exact (hil hl).elim
    | some c =>
        cases hm : m.idxFun i with
        | none => exact (him hm).elim
        | some d =>
            have h := congrFun (ha.trans hb.symm) i
            simp only [Line.coe_apply, hl, hm, Option.getD_some] at h
            exact congrArg some h

lemma line_apply_injective [Nontrivial A] (l : Line A I) : Function.Injective l := by
  intro a b hab
  obtain ⟨i, hi⟩ := l.proper
  have h := congrFun hab i
  simpa [Line.coe_apply, hi] using h

/-- Two distinct common cube vertices determine a combinatorial line. -/
lemma line_eq_of_two_mem_points [Nontrivial A] {l m : Line A I} {x y : I → A}
    (hxy : x ≠ y) (hxl : x ∈ linePoints l) (hxm : x ∈ linePoints m)
    (hyl : y ∈ linePoints l) (hym : y ∈ linePoints m) : l = m := by
  rcases hxl with ⟨a, rfl⟩
  rcases hyl with ⟨b, hby⟩
  rcases hxm with ⟨c, hca⟩
  rcases hym with ⟨d, hdy⟩
  have hab : a ≠ b := by
    intro hab
    apply hxy
    simpa [hab] using hby
  obtain ⟨i, hi⟩ := l.proper
  have hc : c = a := by
    have h := congrFun hca i
    cases hm : m.idxFun i with
    | none => simpa [Line.coe_apply, hi, hm] using h
    | some z =>
        have h' := congrFun (hdy.trans hby.symm) i
        simp only [Line.coe_apply, hi, hm, Option.getD_none, Option.getD_some] at h h'
        exact (hab (h.symm.trans h')).elim
  have hd : d = b := by
    have h := congrFun (hdy.trans hby.symm) i
    cases hm : m.idxFun i with
    | none => simpa [Line.coe_apply, hi, hm] using h
    | some z =>
        have h' := congrFun hca i
        simp only [Line.coe_apply, hi, hm, Option.getD_none, Option.getD_some] at h h'
        exact (hab (h'.symm.trans h)).elim
  apply line_idxFun_injective
  funext j
  have haj := congrFun hca j
  have hbj := congrFun (hdy.trans hby.symm) j
  cases hl : l.idxFun j <;> cases hm : m.idxFun j <;>
    simp_all [Line.coe_apply]

/-- Finite set of vertices of a line. -/
noncomputable def linePointFinset [Fintype A] (l : Line A I) : Finset (I → A) :=
  Finset.univ.image l

@[simp] lemma mem_linePointFinset [Fintype A] {l : Line A I} {x : I → A} :
    x ∈ linePointFinset l ↔ x ∈ linePoints l := by
  simp [linePointFinset, linePoints]

lemma card_linePointFinset [Fintype A] [Nontrivial A] (l : Line A I) :
    (linePointFinset l).card = Fintype.card A := by
  rw [linePointFinset, Finset.card_image_of_injective _ (line_apply_injective l)]
  exact Finset.card_univ

/-- Selected lines through a point and their degree. -/
noncomputable def incidentLines (S : Finset (Line A I)) (x : I → A) : Finset (Line A I) :=
  S.filter fun l ↦ x ∈ linePoints l

@[simp] lemma mem_incidentLines {S : Finset (Line A I)} {x : I → A} {l : Line A I} :
    l ∈ incidentLines S x ↔ l ∈ S ∧ x ∈ linePoints l := by
  simp [incidentLines]

noncomputable def lineDegree (S : Finset (Line A I)) (x : I → A) : ℕ :=
  (incidentLines S x).card

lemma sum_lineDegree [Fintype A] [Fintype I] [Nontrivial A]
    (S : Finset (Line A I)) :
    ∑ x : I → A, lineDegree S x = Fintype.card A * S.card := by
  let r : Line A I → (I → A) → Prop := fun l x ↦ x ∈ linePoints l
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := S) (t := (Finset.univ : Finset (I → A))) r
  have habove : ∀ l : Line A I,
      Finset.bipartiteAbove r Finset.univ l = linePointFinset l := by
    intro l
    ext x
    simp [r]
  have hbelow : ∀ x : I → A,
      Finset.bipartiteBelow r S x = incidentLines S x := by
    intro x
    ext l
    simp [r]
  simpa only [habove, hbelow, lineDegree, card_linePointFinset, Finset.sum_const_nat,
    Finset.card_univ, Nat.nsmul_eq_mul, Nat.mul_comm] using hdouble.symm

/-- The exact RRS tripod predicate. -/
def HasTripod [Fintype I] (S : Finset (Line A I)) : Prop :=
  ∃ l₁ ∈ S, ∃ l₂ ∈ S, ∃ l₃ ∈ S,
    l₁ ≠ l₂ ∧ l₂ ≠ l₃ ∧ l₃ ≠ l₁ ∧
      (∃ x, x ∈ linePoints l₁ ∧ x ∈ linePoints l₂ ∧ x ∈ linePoints l₃) ∧
      movingSet l₁ = movingSet l₂ ∪ movingSet l₃ ∧
      Disjoint (movingSet l₂) (movingSet l₃)

/-- The exact RRS triangle predicate. -/
def HasTriangle (S : Finset (Line A I)) : Prop :=
  ∃ l₁ ∈ S, ∃ l₂ ∈ S, ∃ l₃ ∈ S,
    l₁ ≠ l₂ ∧ l₂ ≠ l₃ ∧ l₃ ≠ l₁ ∧
      (linePoints l₁ ∩ linePoints l₂).Nonempty ∧
      (linePoints l₂ ∩ linePoints l₃).Nonempty ∧
      (linePoints l₃ ∩ linePoints l₁).Nonempty ∧
      linePoints l₁ ∩ linePoints l₂ ∩ linePoints l₃ = ∅

/-- Point-degree cap used in suitability. -/
def DegreeBound [Fintype A] [Fintype I] (S : Finset (Line A I)) (d : ℕ) : Prop :=
  ∀ x, lineDegree S x ≤ d

/-- Exact suitability condition of the sparse selection. -/
def Suitable [Fintype A] [Fintype I] (S : Finset (Line A I)) (d : ℕ) : Prop :=
  DegreeBound S d ∧ ¬ HasTripod S ∧ ¬ HasTriangle S

/-! ## Candidate lines supported in disjoint Hales--Jewett blocks -/

/-- Every candidate line moves inside one of the displayed coordinate blocks. -/
def SupportedInBlocks [Fintype I] {t : ℕ} (T : Finset (Line A I))
    (blocks : Fin t → Finset I) : Prop :=
  ∀ l ∈ T, ∃ j, movingSet l ⊆ blocks j

/-- Candidate lines through `x` whose moving support is contained in `B`. -/
noncomputable def blockLinesThrough [Fintype I] (T : Finset (Line A I))
    (x : I → A) (B : Finset I) : Finset (Line A I) :=
  T.filter fun l ↦ x ∈ linePoints l ∧ movingSet l ⊆ B

@[simp] lemma mem_blockLinesThrough [Fintype I] {T : Finset (Line A I)}
    {x : I → A} {B : Finset I} {l : Line A I} :
    l ∈ blockLinesThrough T x B ↔
      l ∈ T ∧ x ∈ linePoints l ∧ movingSet l ⊆ B := by
  simp [blockLinesThrough]

/-- A fixed point is on at most `2^|B|` candidate lines moving inside `B`. -/
lemma card_blockLinesThrough_le [Fintype I] (T : Finset (Line A I))
    (x : I → A) (B : Finset I) :
    (blockLinesThrough T x B).card ≤ 2 ^ B.card := by
  let source := blockLinesThrough T x B
  let target := B.powerset
  have hmap : Set.MapsTo movingSet (source : Set (Line A I))
      (target : Set (Finset I)) := by
    intro l hl
    exact Finset.mem_powerset.mpr (mem_blockLinesThrough.mp hl).2.2
  have hinj : (source : Set (Line A I)).InjOn movingSet := by
    intro l hl m hm heq
    exact line_eq_of_movingSet_eq_of_mem heq
      (mem_blockLinesThrough.mp hl).2.1 (mem_blockLinesThrough.mp hm).2.1
  have hcard := Finset.card_le_card_of_injOn movingSet hmap hinj
  simpa [source, target] using hcard

/-- The block-supported candidate lines through one point, written as a union
over the blocks. -/
noncomputable def blockUnionThrough [Fintype I] {t : ℕ}
    (T : Finset (Line A I)) (blocks : Fin t → Finset I) (x : I → A) :
    Finset (Line A I) :=
  Finset.univ.biUnion fun j ↦ blockLinesThrough T x (blocks j)

lemma incidentLines_subset_blockUnionThrough [Fintype I] {t : ℕ}
    {T : Finset (Line A I)} {blocks : Fin t → Finset I}
    (hT : SupportedInBlocks T blocks) (x : I → A) :
    incidentLines T x ⊆ blockUnionThrough T blocks x := by
  intro l hl
  obtain ⟨j, hj⟩ := hT l (mem_incidentLines.mp hl).1
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
    mem_blockLinesThrough.mpr ⟨(mem_incidentLines.mp hl).1,
      (mem_incidentLines.mp hl).2, hj⟩⟩

/-- In `t` blocks of size `m`, a cube point belongs to at most `t 2^m`
candidate lines.  Disjointness is not needed for this upper bound. -/
lemma lineDegree_le_blocks [Fintype I] {t m : ℕ}
    (T : Finset (Line A I)) (blocks : Fin t → Finset I)
    (hT : SupportedInBlocks T blocks) (hcard : ∀ j, (blocks j).card = m)
    (x : I → A) :
    lineDegree T x ≤ t * 2 ^ m := by
  calc
    lineDegree T x ≤ (blockUnionThrough T blocks x).card :=
      Finset.card_le_card (incidentLines_subset_blockUnionThrough hT x)
    _ ≤ ∑ j : Fin t, (blockLinesThrough T x (blocks j)).card := by
      simpa [blockUnionThrough] using
        (Finset.card_biUnion_le
          (s := (Finset.univ : Finset (Fin t)))
          (t := fun j ↦ blockLinesThrough T x (blocks j)))
    _ ≤ ∑ _j : Fin t, 2 ^ m := by
      exact Finset.sum_le_sum fun j _ ↦
        (card_blockLinesThrough_le T x (blocks j)).trans_eq (by rw [hcard j])
    _ = t * 2 ^ m := by simp

/-! ## Saturated-point exclusions -/

/-- Points at which the selected family has reached degree `d`. -/
noncomputable def saturatedPoints [Fintype A] [Fintype I]
    (S : Finset (Line A I)) (d : ℕ) : Finset (I → A) :=
  Finset.univ.filter fun x ↦ d ≤ lineDegree S x

@[simp] lemma mem_saturatedPoints [Fintype A] [Fintype I]
    {S : Finset (Line A I)} {d : ℕ} {x : I → A} :
    x ∈ saturatedPoints S d ↔ d ≤ lineDegree S x := by
  simp [saturatedPoints]

lemma card_saturatedPoints_mul_le [Fintype A] [Fintype I] [Nontrivial A]
    (S : Finset (Line A I)) (d : ℕ) :
    (saturatedPoints S d).card * d ≤ Fintype.card A * S.card := by
  calc
    (saturatedPoints S d).card * d ≤
        ∑ x ∈ saturatedPoints S d, lineDegree S x := by
      simpa [Nat.nsmul_eq_mul] using
        Finset.card_nsmul_le_sum (saturatedPoints S d) (lineDegree S) d
          (fun x hx ↦ mem_saturatedPoints.mp hx)
    _ ≤ ∑ x : I → A, lineDegree S x :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = Fintype.card A * S.card := sum_lineDegree S

/-- Lines from `T` meeting at least one point of `P`. -/
noncomputable def linesMeetingPoints (T : Finset (Line A I)) (P : Finset (I → A)) :
    Finset (Line A I) :=
  P.biUnion (incidentLines T)

@[simp] lemma mem_linesMeetingPoints {T : Finset (Line A I)} {P : Finset (I → A)}
    {l : Line A I} :
    l ∈ linesMeetingPoints T P ↔
      ∃ x ∈ P, l ∈ T ∧ x ∈ linePoints l := by
  simp [linesMeetingPoints]

lemma card_linesMeetingPoints_le (T : Finset (Line A I)) (P : Finset (I → A)) (M : ℕ)
    (hM : ∀ x ∈ P, lineDegree T x ≤ M) :
    (linesMeetingPoints T P).card ≤ P.card * M := by
  calc
    (linesMeetingPoints T P).card ≤ ∑ x ∈ P, lineDegree T x := by
      simpa [linesMeetingPoints, lineDegree] using
        (Finset.card_biUnion_le (s := P) (t := incidentLines T))
    _ ≤ P.card * M := by
      simpa [Nat.nsmul_eq_mul] using Finset.sum_le_card_nsmul P (lineDegree T) M hM

/-- Candidate additions which violate the point-degree cap. -/
noncomputable def degreeExcluded [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) (d : ℕ) : Finset (Line A I) :=
  T.filter fun l ↦ ¬ DegreeBound (insert l S) d

lemma lineDegree_insert_le [Fintype A] [Fintype I]
    (S : Finset (Line A I)) (l : Line A I) (x : I → A) :
    lineDegree (insert l S) x ≤ lineDegree S x + 1 := by
  by_cases hx : x ∈ linePoints l
  · have heq : incidentLines (insert l S) x = insert l (incidentLines S x) := by
      ext q
      simp only [mem_incidentLines, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hqS, hqx⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hqS, hqx⟩
      · rintro (rfl | ⟨hqS, hqx⟩)
        · exact ⟨Or.inl rfl, hx⟩
        · exact ⟨Or.inr hqS, hqx⟩
    rw [lineDegree, heq, lineDegree]
    exact Finset.card_insert_le _ _
  · have heq : incidentLines (insert l S) x = incidentLines S x := by
      ext q
      simp only [mem_incidentLines, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hqS, hqx⟩
        · exact (hx hqx).elim
        · exact ⟨hqS, hqx⟩
      · rintro ⟨hqS, hqx⟩
        exact ⟨Or.inr hqS, hqx⟩
    rw [lineDegree, heq, lineDegree]
    omega

lemma lineDegree_insert_eq_of_not_mem [Fintype A] [Fintype I]
    (S : Finset (Line A I)) (l : Line A I) (x : I → A)
    (hx : x ∉ linePoints l) :
    lineDegree (insert l S) x = lineDegree S x := by
  unfold lineDegree incidentLines
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hqS, hqx⟩
    · exact (hx hqx).elim
    · exact ⟨hqS, hqx⟩
  · rintro ⟨hqS, hqx⟩
    exact ⟨Or.inr hqS, hqx⟩

/-- Any actual degree-violating addition meets a point saturated in the old
family. -/
lemma degreeExcluded_subset_saturated [Fintype A] [Fintype I]
    {T S : Finset (Line A I)} {d : ℕ} (hS : DegreeBound S d) :
    degreeExcluded T S d ⊆ linesMeetingPoints T (saturatedPoints S d) := by
  intro l hl
  have hlT := (Finset.mem_filter.mp hl).1
  have hbad := (Finset.mem_filter.mp hl).2
  simp only [DegreeBound, not_forall, not_le] at hbad
  obtain ⟨x, hxbad⟩ := hbad
  have hxl : x ∈ linePoints l := by
    by_contra hnot
    rw [lineDegree_insert_eq_of_not_mem S l x hnot] at hxbad
    exact (not_lt_of_ge (hS x)) hxbad
  have hsle := hS x
  have hins := lineDegree_insert_le S l x
  have hsat : d ≤ lineDegree S x := by omega
  exact mem_linesMeetingPoints.mpr
    ⟨x, mem_saturatedPoints.mpr hsat, hlT, hxl⟩

/-- RRS (5.5), with division cleared: for block-supported candidates, the
number excluded by saturation satisfies
`excluded * d ≤ a * |S| * (t * 2^m)`. -/
theorem degreeExcluded_mul_le [Fintype A] [Fintype I] [Nontrivial A]
    {t m d : ℕ} (T S : Finset (Line A I)) (blocks : Fin t → Finset I)
    (hT : SupportedInBlocks T blocks) (hblocks : ∀ j, (blocks j).card = m)
    (hS : DegreeBound S d) :
    (degreeExcluded T S d).card * d ≤
      (Fintype.card A * S.card) * (t * 2 ^ m) := by
  have hsub := degreeExcluded_subset_saturated (T := T) hS
  have hmeet : (linesMeetingPoints T (saturatedPoints S d)).card ≤
      (saturatedPoints S d).card * (t * 2 ^ m) :=
    card_linesMeetingPoints_le T (saturatedPoints S d) (t * 2 ^ m)
      (fun x _ ↦ lineDegree_le_blocks T blocks hT hblocks x)
  have hcard : (degreeExcluded T S d).card ≤
      (saturatedPoints S d).card * (t * 2 ^ m) :=
    (Finset.card_le_card hsub).trans hmeet
  calc
    (degreeExcluded T S d).card * d
        ≤ ((saturatedPoints S d).card * (t * 2 ^ m)) * d :=
      Nat.mul_le_mul_right d hcard
    _ = ((saturatedPoints S d).card * d) * (t * 2 ^ m) := by ring
    _ ≤ (Fintype.card A * S.card) * (t * 2 ^ m) :=
      Nat.mul_le_mul_right _ (card_saturatedPoints_mul_le S d)

/-- A numerical hierarchy turning the cleared saturated-point estimate into
the `1/(2 A₀)` exclusion fraction required by the greedy lemma. -/
theorem degreeExcluded_fraction [Fintype A] [Fintype I] [Nontrivial A]
    {t m d A₀ : ℕ} (T S : Finset (Line A I)) (blocks : Fin t → Finset I)
    (hT : SupportedInBlocks T blocks) (hblocks : ∀ j, (blocks j).card = m)
    (hS : DegreeBound S d)
    (hparam : (2 * A₀) * ((Fintype.card A * S.card) * (t * 2 ^ m)) <
      d * T.card) :
    (2 * A₀) * (degreeExcluded T S d).card < T.card := by
  have hb := degreeExcluded_mul_le T S blocks hT hblocks hS
  have hmul := Nat.mul_le_mul_left (2 * A₀) hb
  have hchain : ((2 * A₀) * (degreeExcluded T S d).card) * d < T.card * d := by
    calc
      ((2 * A₀) * (degreeExcluded T S d).card) * d
          = (2 * A₀) * ((degreeExcluded T S d).card * d) := by ring
      _ ≤ (2 * A₀) * ((Fintype.card A * S.card) * (t * 2 ^ m)) := hmul
      _ < d * T.card := hparam
      _ = T.card * d := by ring
  exact Nat.lt_of_mul_lt_mul_right hchain

/-! ## Tripod exclusions -/

/-- Symmetric moving-support form of the tripod relation, with the first
argument reserved for the candidate line. -/
def TripodSupports (X U V : Finset I) : Prop :=
  (X = U ∪ V ∧ Disjoint U V) ∨
  (U = X ∪ V ∧ Disjoint X V) ∨
  (V = X ∪ U ∧ Disjoint X U)

/-- For fixed supports `U,V`, there is at most one possible third support in
a tripod. -/
lemma tripodSupports_left_unique {X Y U V : Finset I}
    (hX : TripodSupports X U V) (hY : TripodSupports Y U V) : X = Y := by
  have canonical (Z : Finset I) (hZ : TripodSupports Z U V) :
      Z = (U \ V) ∪ (V \ U) := by
    rcases hZ with ⟨rfl, hUV⟩ | ⟨hU, hZV⟩ | ⟨hV, hZU⟩
    · ext i
      have hd := Finset.disjoint_left.mp hUV
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hiU | hiV)
        · exact Or.inl ⟨hiU, hd hiU⟩
        · exact Or.inr ⟨hiV, fun hiU ↦ hd hiU hiV⟩
      · rintro (⟨hiU, -⟩ | ⟨hiV, -⟩)
        · exact Or.inl hiU
        · exact Or.inr hiV
    · ext i
      have hUi : i ∈ U ↔ i ∈ Z ∨ i ∈ V := by
        simpa only [Finset.mem_union] using Finset.ext_iff.mp hU i
      have hd := Finset.disjoint_left.mp hZV
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hiZ
        exact Or.inl ⟨hUi.mpr (Or.inl hiZ), hd hiZ⟩
      · rintro (⟨hiU, hiV⟩ | ⟨hiV, hiU⟩)
        · rcases hUi.mp hiU with hiZ | hiV'
          · exact hiZ
          · exact (hiV hiV').elim
        · exact (hiU (hUi.mpr (Or.inr hiV))).elim
    · ext i
      have hVi : i ∈ V ↔ i ∈ Z ∨ i ∈ U := by
        simpa only [Finset.mem_union] using Finset.ext_iff.mp hV i
      have hd := Finset.disjoint_left.mp hZU
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · intro hiZ
        exact Or.inr ⟨hVi.mpr (Or.inl hiZ), hd hiZ⟩
      · rintro (⟨hiU, hiV⟩ | ⟨hiV, hiU⟩)
        · exact (hiV (hVi.mpr (Or.inr hiU))).elim
        · rcases hVi.mp hiV with hiZ | hiU'
          · exact hiZ
          · exact (hiU hiU').elim
  exact (canonical X hX).trans (canonical Y hY).symm

/-- Candidates completing a tripod with a fixed common point and fixed two
selected lines. -/
noncomputable def tripodPairCandidates [Fintype I]
    (T : Finset (Line A I)) (x : I → A) (u v : Line A I) : Finset (Line A I) :=
  T.filter fun l ↦ x ∈ linePoints l ∧
    TripodSupports (movingSet l) (movingSet u) (movingSet v)

lemma card_tripodPairCandidates_le [Fintype I]
    (T : Finset (Line A I)) (x : I → A) (u v : Line A I) :
    (tripodPairCandidates T x u v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro l hl q hq
  have hl' := Finset.mem_filter.mp hl
  have hq' := Finset.mem_filter.mp hq
  exact line_eq_of_movingSet_eq_of_mem
    (tripodSupports_left_unique hl'.2.2 hq'.2.2)
    hl'.2.1 hq'.2.1

/-- All candidates carrying a tripod certificate `(x,u,v)`. -/
noncomputable def tripodCertificateCandidates [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) : Finset (Line A I) :=
  Finset.univ.biUnion fun x ↦
    (incidentLines S x).biUnion fun u ↦
      (incidentLines S x).biUnion fun v ↦ tripodPairCandidates T x u v

lemma card_tripodCertificateCandidates_le [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) {d : ℕ} (hdeg : DegreeBound S d) :
    (tripodCertificateCandidates T S).card ≤
      d ^ 2 * Fintype.card (I → A) := by
  calc
    (tripodCertificateCandidates T S).card ≤
        ∑ x : I → A, ∑ u ∈ incidentLines S x,
          ∑ v ∈ incidentLines S x, (tripodPairCandidates T x u v).card := by
      simp only [tripodCertificateCandidates]
      refine (Finset.card_biUnion_le (s := (Finset.univ : Finset (I → A)))
        (t := fun x ↦ (incidentLines S x).biUnion fun u ↦
          (incidentLines S x).biUnion fun v ↦ tripodPairCandidates T x u v)).trans ?_
      exact Finset.sum_le_sum fun x _ ↦
        (Finset.card_biUnion_le (s := incidentLines S x)
          (t := fun u ↦ (incidentLines S x).biUnion fun v ↦
            tripodPairCandidates T x u v)).trans
          (Finset.sum_le_sum fun u _ ↦ Finset.card_biUnion_le)
    _ ≤ ∑ _x : I → A, ∑ _u ∈ incidentLines S _x,
          ∑ _v ∈ incidentLines S _x, 1 := by
      exact Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun u _ ↦
        Finset.sum_le_sum fun v _ ↦ card_tripodPairCandidates_le T x u v
    _ = ∑ x : I → A, (lineDegree S x) ^ 2 := by
      simp [lineDegree, pow_two]
    _ ≤ ∑ _x : I → A, d ^ 2 := by
      exact Finset.sum_le_sum fun x _ ↦ Nat.pow_le_pow_left (hdeg x) 2
    _ = d ^ 2 * Fintype.card (I → A) := by
      simp [Nat.mul_comm]

/-- Actual additions which create a tripod. -/
noncomputable def tripodExcluded [Fintype I]
    (T S : Finset (Line A I)) : Finset (Line A I) :=
  T.filter fun l ↦ HasTripod (insert l S)

lemma tripodExcluded_subset_certificates [Fintype A] [Fintype I]
    {T S : Finset (Line A I)} (hS : ¬ HasTripod S) :
    tripodExcluded T S ⊆ tripodCertificateCandidates T S := by
  intro l hl
  have hlT := (Finset.mem_filter.mp hl).1
  rcases (Finset.mem_filter.mp hl).2 with
    ⟨l₁, h₁, l₂, h₂, l₃, h₃, h₁₂, h₂₃, h₃₁,
      ⟨x, hx₁, hx₂, hx₃⟩, hsupport, hdisj⟩
  have hcert (u v : Line A I) (hu : u ∈ S) (hv : v ∈ S)
      (hxu : x ∈ linePoints u) (hxv : x ∈ linePoints v)
      (hxl : x ∈ linePoints l)
      (hsup : TripodSupports (movingSet l) (movingSet u) (movingSet v)) :
      l ∈ tripodCertificateCandidates T S := by
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨u, mem_incidentLines.mpr ⟨hu, hxu⟩,
        Finset.mem_biUnion.mpr ⟨v, mem_incidentLines.mpr ⟨hv, hxv⟩,
          Finset.mem_filter.mpr ⟨hlT, hxl, hsup⟩⟩⟩⟩
  simp only [Finset.mem_insert] at h₁ h₂ h₃
  rcases h₁ with rfl | h₁S
  · rcases h₂ with rfl | h₂S
    · exact (h₁₂ rfl).elim
    · rcases h₃ with rfl | h₃S
      · exact (h₃₁ rfl).elim
      · exact hcert l₂ l₃ h₂S h₃S hx₂ hx₃ hx₁
          (Or.inl ⟨hsupport, hdisj⟩)
  · rcases h₂ with rfl | h₂S
    · rcases h₃ with rfl | h₃S
      · exact (h₂₃ rfl).elim
      · exact hcert l₁ l₃ h₁S h₃S hx₁ hx₃ hx₂
          (Or.inr (Or.inl ⟨hsupport, hdisj⟩))
    · rcases h₃ with rfl | h₃S
      · exact hcert l₁ l₂ h₁S h₂S hx₁ hx₂ hx₃
          (Or.inr (Or.inl ⟨by simpa [Finset.union_comm] using hsupport,
            hdisj.symm⟩))
      · exact (hS ⟨l₁, h₁S, l₂, h₂S, l₃, h₃S,
          h₁₂, h₂₃, h₃₁, ⟨x, hx₁, hx₂, hx₃⟩,
          hsupport, hdisj⟩).elim

/-- RRS (5.6): at most `d² |A|^n` additions complete a tripod. -/
theorem card_tripodExcluded_le [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) {d : ℕ}
    (hdeg : DegreeBound S d) (htripod : ¬ HasTripod S) :
    (tripodExcluded T S).card ≤ d ^ 2 * Fintype.card (I → A) :=
  (Finset.card_le_card (tripodExcluded_subset_certificates htripod)).trans
    (card_tripodCertificateCandidates_le T S hdeg)

theorem card_tripodExcluded_fin_le [Fintype A]
    {n d : ℕ} (T S : Finset (Line A (Fin n)))
    (hdeg : DegreeBound S d) (htripod : ¬ HasTripod S) :
    (tripodExcluded T S).card ≤ d ^ 2 * Fintype.card A ^ n := by
  simpa using card_tripodExcluded_le T S hdeg htripod

/-- A hierarchy inequality placing the tripod exclusions below the greedy
`1/(2 A₀)` threshold. -/
theorem tripodExcluded_fraction [Fintype A] [Fintype I]
    {d A₀ : ℕ} (T S : Finset (Line A I))
    (hdeg : DegreeBound S d) (htripod : ¬ HasTripod S)
    (hparam : (2 * A₀) * (d ^ 2 * Fintype.card (I → A)) < T.card) :
    (2 * A₀) * (tripodExcluded T S).card < T.card :=
  (Nat.mul_le_mul_left (2 * A₀)
    (card_tripodExcluded_le T S hdeg htripod)).trans_lt hparam

/-! ## Triangle exclusions -/

/-- Candidate lines through two prescribed distinct points. -/
noncomputable def twoPointCandidates (T : Finset (Line A I))
    (x y : I → A) : Finset (Line A I) :=
  T.filter fun l ↦ x ≠ y ∧ x ∈ linePoints l ∧ y ∈ linePoints l

@[simp] lemma mem_twoPointCandidates {T : Finset (Line A I)}
    {x y : I → A} {l : Line A I} :
    l ∈ twoPointCandidates T x y ↔
      l ∈ T ∧ x ≠ y ∧ x ∈ linePoints l ∧ y ∈ linePoints l := by
  simp [twoPointCandidates]

lemma card_twoPointCandidates_le [Nontrivial A]
    (T : Finset (Line A I)) (x y : I → A) :
    (twoPointCandidates T x y).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro l hl q hq
  have hl' := Finset.mem_filter.mp hl
  have hq' := Finset.mem_filter.mp hq
  exact line_eq_of_two_mem_points hl'.2.1 hl'.2.2.1 hq'.2.2.1
    hl'.2.2.2 hq'.2.2.2

/-- The certificate count for a triangle follows the chain
`x --u-- z --v-- y`; the candidate line is the unique line through `x,y`. -/
noncomputable def triangleCertificateCandidates [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) : Finset (Line A I) :=
  Finset.univ.biUnion fun x ↦
    (incidentLines S x).biUnion fun u ↦
      (linePointFinset u).biUnion fun z ↦
        (incidentLines S z).biUnion fun v ↦
          (linePointFinset v).biUnion fun y ↦ twoPointCandidates T x y

lemma card_triangleCertificateCandidates_le [Fintype A] [Fintype I] [Nontrivial A]
    (T S : Finset (Line A I)) {d : ℕ} (hdeg : DegreeBound S d) :
    (triangleCertificateCandidates T S).card ≤
      (Fintype.card A * d) ^ 2 * Fintype.card (I → A) := by
  have hunion : (triangleCertificateCandidates T S).card ≤
      ∑ x : I → A, ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
        ∑ v ∈ incidentLines S z, ∑ y ∈ linePointFinset v,
          (twoPointCandidates T x y).card := by
    simp only [triangleCertificateCandidates]
    refine (Finset.card_biUnion_le
      (s := (Finset.univ : Finset (I → A)))
      (t := fun x ↦ (incidentLines S x).biUnion fun u ↦
        (linePointFinset u).biUnion fun z ↦
          (incidentLines S z).biUnion fun v ↦
            (linePointFinset v).biUnion fun y ↦ twoPointCandidates T x y)).trans ?_
    exact Finset.sum_le_sum fun x _ ↦
      (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun u _ ↦
        (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun z _ ↦
          (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun v _ ↦
            Finset.card_biUnion_le))))))
  have hpairs :
      (∑ x : I → A, ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
        ∑ v ∈ incidentLines S z, ∑ y ∈ linePointFinset v,
          (twoPointCandidates T x y).card) ≤
      ∑ x : I → A, ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
        ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 := by
    exact Finset.sum_le_sum fun x _ ↦ Finset.sum_le_sum fun u _ ↦
      Finset.sum_le_sum fun z _ ↦ Finset.sum_le_sum fun v _ ↦
        Finset.sum_le_sum fun y _ ↦ card_twoPointCandidates_le T x y
  have hv (z : I → A) :
      ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 ≤
        d * Fintype.card A := by
    calc
      ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 =
          lineDegree S z * Fintype.card A := by
        simp [lineDegree, card_linePointFinset]
      _ ≤ d * Fintype.card A := Nat.mul_le_mul_right _ (hdeg z)
  have hz (u : Line A I) :
      ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 ≤
        Fintype.card A * (d * Fintype.card A) := by
    calc
      ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 ≤
          ∑ _z ∈ linePointFinset u, d * Fintype.card A :=
        Finset.sum_le_sum fun z _ ↦ hv z
      _ = Fintype.card A * (d * Fintype.card A) := by
        simp [card_linePointFinset]
  have hu (x : I → A) :
      ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 ≤
        d * (Fintype.card A * (d * Fintype.card A)) := by
    calc
      ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 ≤
          ∑ _u ∈ incidentLines S x,
            Fintype.card A * (d * Fintype.card A) :=
        Finset.sum_le_sum fun u _ ↦ hz u
      _ = lineDegree S x * (Fintype.card A * (d * Fintype.card A)) := by
        simp [lineDegree]
      _ ≤ d * (Fintype.card A * (d * Fintype.card A)) :=
        Nat.mul_le_mul_right _ (hdeg x)
  calc
    (triangleCertificateCandidates T S).card ≤
        ∑ x : I → A, ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ y ∈ linePointFinset v,
            (twoPointCandidates T x y).card := hunion
    _ ≤ ∑ x : I → A, ∑ u ∈ incidentLines S x, ∑ z ∈ linePointFinset u,
          ∑ v ∈ incidentLines S z, ∑ _y ∈ linePointFinset v, 1 := hpairs
    _ ≤ ∑ _x : I → A,
          d * (Fintype.card A * (d * Fintype.card A)) :=
      Finset.sum_le_sum fun x _ ↦ hu x
    _ = (Fintype.card A * d) ^ 2 * Fintype.card (I → A) := by
      simp [pow_two]
      ring

/-- Actual additions which create a triangle. -/
noncomputable def triangleExcluded
    (T S : Finset (Line A I)) : Finset (Line A I) :=
  T.filter fun l ↦ HasTriangle (insert l S)

lemma triangleExcluded_subset_certificates [Fintype A] [Fintype I] [Nontrivial A]
    {T S : Finset (Line A I)} (hS : ¬ HasTriangle S) :
    triangleExcluded T S ⊆ triangleCertificateCandidates T S := by
  intro l hl
  have hlT := (Finset.mem_filter.mp hl).1
  rcases (Finset.mem_filter.mp hl).2 with
    ⟨l₁, h₁, l₂, h₂, l₃, h₃, h₁₂, h₂₃, h₃₁,
      ⟨x₁₂, hx₁, hx₂⟩, ⟨x₂₃, hx₂', hx₃⟩,
      ⟨x₃₁, hx₃', hx₁'⟩, hempty⟩
  have hpairs (p q : I → A)
      (hp₁ : p ∈ linePoints l₁) (hp₂ : p ∈ linePoints l₂)
      (hq₃ : q ∈ linePoints l₃) (hq₁ : q ∈ linePoints l₁) : p ≠ q := by
    intro hpq
    subst q
    have : p ∈ linePoints l₁ ∩ linePoints l₂ ∩ linePoints l₃ :=
      ⟨⟨hp₁, hp₂⟩, hq₃⟩
    simpa [hempty] using this
  have hne₂₃₁₂ : x₂₃ ≠ x₁₂ := by
    intro h
    subst x₂₃
    have : x₁₂ ∈ linePoints l₁ ∩ linePoints l₂ ∩ linePoints l₃ :=
      ⟨⟨hx₁, hx₂'⟩, hx₃⟩
    simpa [hempty] using this
  have hne₃₁₂₃ : x₃₁ ≠ x₂₃ := by
    intro h
    subst x₃₁
    have : x₂₃ ∈ linePoints l₁ ∩ linePoints l₂ ∩ linePoints l₃ :=
      ⟨⟨hx₁', hx₂'⟩, hx₃⟩
    simpa [hempty] using this
  have hcert (p z q : I → A) (u v : Line A I)
      (hu : u ∈ S) (hv : v ∈ S)
      (hpl : p ∈ linePoints l) (hpu : p ∈ linePoints u)
      (hzu : z ∈ linePoints u) (hzv : z ∈ linePoints v)
      (hqv : q ∈ linePoints v) (hql : q ∈ linePoints l)
      (hpq : p ≠ q) : l ∈ triangleCertificateCandidates T S := by
    have hlpair : l ∈ twoPointCandidates T p q := by
      exact mem_twoPointCandidates.mpr ⟨hlT, hpq, hpl, hql⟩
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨u, mem_incidentLines.mpr ⟨hu, hpu⟩,
        Finset.mem_biUnion.mpr ⟨z, mem_linePointFinset.mpr hzu,
          Finset.mem_biUnion.mpr ⟨v, mem_incidentLines.mpr ⟨hv, hzv⟩,
            Finset.mem_biUnion.mpr ⟨q, mem_linePointFinset.mpr hqv,
              hlpair⟩⟩⟩⟩⟩
  simp only [Finset.mem_insert] at h₁ h₂ h₃
  rcases h₁ with rfl | h₁S
  · rcases h₂ with rfl | h₂S
    · exact (h₁₂ rfl).elim
    · rcases h₃ with rfl | h₃S
      · exact (h₃₁ rfl).elim
      · exact hcert x₁₂ x₂₃ x₃₁ l₂ l₃ h₂S h₃S
          hx₁ hx₂ hx₂' hx₃ hx₃' hx₁'
          (hpairs x₁₂ x₃₁ hx₁ hx₂ hx₃' hx₁')
  · rcases h₂ with rfl | h₂S
    · rcases h₃ with rfl | h₃S
      · exact (h₂₃ rfl).elim
      · exact hcert x₂₃ x₃₁ x₁₂ l₃ l₁ h₃S h₁S
          hx₂' hx₃ hx₃' hx₁' hx₁ hx₂
          hne₂₃₁₂
    · rcases h₃ with rfl | h₃S
      · exact hcert x₃₁ x₁₂ x₂₃ l₁ l₂ h₁S h₂S
          hx₃' hx₁' hx₁ hx₂ hx₂' hx₃
          hne₃₁₂₃
      · exact (hS ⟨l₁, h₁S, l₂, h₂S, l₃, h₃S,
          h₁₂, h₂₃, h₃₁, ⟨x₁₂, hx₁, hx₂⟩,
          ⟨x₂₃, hx₂', hx₃⟩, ⟨x₃₁, hx₃', hx₁'⟩,
          hempty⟩).elim

/-- RRS (5.7): at most `(a d)² a^n` additions complete a triangle. -/
theorem card_triangleExcluded_le [Fintype A] [Fintype I] [Nontrivial A]
    (T S : Finset (Line A I)) {d : ℕ}
    (hdeg : DegreeBound S d) (htriangle : ¬ HasTriangle S) :
    (triangleExcluded T S).card ≤
      (Fintype.card A * d) ^ 2 * Fintype.card (I → A) :=
  (Finset.card_le_card (triangleExcluded_subset_certificates htriangle)).trans
    (card_triangleCertificateCandidates_le T S hdeg)

theorem card_triangleExcluded_fin_le [Fintype A] [Nontrivial A]
    {n d : ℕ} (T S : Finset (Line A (Fin n)))
    (hdeg : DegreeBound S d) (htriangle : ¬ HasTriangle S) :
    (triangleExcluded T S).card ≤
      (Fintype.card A * d) ^ 2 * Fintype.card A ^ n := by
  simpa using card_triangleExcluded_le T S hdeg htriangle

theorem triangleExcluded_fraction [Fintype A] [Fintype I] [Nontrivial A]
    {d A₀ : ℕ} (T S : Finset (Line A I))
    (hdeg : DegreeBound S d) (htriangle : ¬ HasTriangle S)
    (hparam : (2 * A₀) *
      ((Fintype.card A * d) ^ 2 * Fintype.card (I → A)) < T.card) :
    (2 * A₀) * (triangleExcluded T S).card < T.card :=
  (Nat.mul_le_mul_left (2 * A₀)
    (card_triangleExcluded_le T S hdeg htriangle)).trans_lt hparam

/-! ## Combined non-addable bound -/

/-- The exact set of candidate lines whose insertion destroys suitability. -/
noncomputable def nonaddable [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) (d : ℕ) : Finset (Line A I) :=
  T.filter fun l ↦ ¬ Suitable (insert l S) d

/-- Every non-addable candidate is excluded by saturation, a new tripod, or
a new triangle. -/
lemma nonaddable_subset_three_exclusions [Fintype A] [Fintype I]
    {T S : Finset (Line A I)} {d : ℕ} :
    nonaddable T S d ⊆
      degreeExcluded T S d ∪ tripodExcluded T S ∪ triangleExcluded T S := by
  intro l hl
  have hl' := Finset.mem_filter.mp hl
  by_cases hdeg : DegreeBound (insert l S) d
  · by_cases htripod : HasTripod (insert l S)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hl'.1, htripod⟩))
    · have htriangle : HasTriangle (insert l S) := by
        exact Classical.byContradiction fun hn ↦
          hl'.2 ⟨hdeg, htripod, hn⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hl'.1, htriangle⟩)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hl'.1, hdeg⟩))

lemma card_nonaddable_le_three [Fintype A] [Fintype I]
    (T S : Finset (Line A I)) (d : ℕ) :
    (nonaddable T S d).card ≤
      (degreeExcluded T S d).card + (tripodExcluded T S).card +
        (triangleExcluded T S).card := by
  calc
    (nonaddable T S d).card ≤
        (degreeExcluded T S d ∪ tripodExcluded T S ∪ triangleExcluded T S).card :=
      Finset.card_le_card nonaddable_subset_three_exclusions
    _ ≤ (degreeExcluded T S d ∪ tripodExcluded T S).card +
        (triangleExcluded T S).card :=
      Finset.card_union_le (degreeExcluded T S d ∪ tripodExcluded T S)
        (triangleExcluded T S)
    _ ≤ ((degreeExcluded T S d).card + (tripodExcluded T S).card) +
        (triangleExcluded T S).card :=
      Nat.add_le_add_right
        (Finset.card_union_le (degreeExcluded T S d) (tripodExcluded T S)) _

/-- Combined cleared-denominator estimate for block-supported candidates.

The three summands are respectively the saturated-point, tripod, and triangle
certificate bounds. -/
theorem nonaddable_mul_le [Fintype A] [Fintype I] [Nontrivial A]
    {t m d : ℕ} (T S : Finset (Line A I)) (blocks : Fin t → Finset I)
    (hT : SupportedInBlocks T blocks) (hblocks : ∀ j, (blocks j).card = m)
    (hS : Suitable S d) :
    (nonaddable T S d).card * d ≤
      (Fintype.card A * S.card) * (t * 2 ^ m) +
        (d ^ 2 * Fintype.card (I → A) +
          (Fintype.card A * d) ^ 2 * Fintype.card (I → A)) * d := by
  have hcard := card_nonaddable_le_three T S d
  have hdegree := degreeExcluded_mul_le T S blocks hT hblocks hS.1
  have htripod := card_tripodExcluded_le T S hS.1 hS.2.1
  have htriangle := card_triangleExcluded_le T S hS.1 hS.2.2
  calc
    (nonaddable T S d).card * d ≤
        ((degreeExcluded T S d).card + (tripodExcluded T S).card +
          (triangleExcluded T S).card) * d := Nat.mul_le_mul_right d hcard
    _ = (degreeExcluded T S d).card * d +
        ((tripodExcluded T S).card + (triangleExcluded T S).card) * d := by ring
    _ ≤ (Fintype.card A * S.card) * (t * 2 ^ m) +
        (d ^ 2 * Fintype.card (I → A) +
          (Fintype.card A * d) ^ 2 * Fintype.card (I → A)) * d := by
      exact Nat.add_le_add hdegree (Nat.mul_le_mul_right d (Nat.add_le_add htripod htriangle))

/-- The explicit parameter inequality used by the greedy sparse-selection
lemma.  Its conclusion says that fewer than a `1/(2 A₀)` fraction of all
candidates are non-addable. -/
theorem nonaddable_fraction [Fintype A] [Fintype I] [Nontrivial A]
    {t m d A₀ : ℕ} (T S : Finset (Line A I)) (blocks : Fin t → Finset I)
    (hT : SupportedInBlocks T blocks) (hblocks : ∀ j, (blocks j).card = m)
    (hS : Suitable S d)
    (hparam : (2 * A₀) *
      ((Fintype.card A * S.card) * (t * 2 ^ m) +
        (d ^ 2 * Fintype.card (I → A) +
          (Fintype.card A * d) ^ 2 * Fintype.card (I → A)) * d) <
      d * T.card) :
    (2 * A₀) * (nonaddable T S d).card < T.card := by
  have hb := nonaddable_mul_le T S blocks hT hblocks hS
  have hmul := Nat.mul_le_mul_left (2 * A₀) hb
  have hchain : ((2 * A₀) * (nonaddable T S d).card) * d < T.card * d := by
    calc
      ((2 * A₀) * (nonaddable T S d).card) * d
          = (2 * A₀) * ((nonaddable T S d).card * d) := by ring
      _ ≤ (2 * A₀) *
          ((Fintype.card A * S.card) * (t * 2 ^ m) +
            (d ^ 2 * Fintype.card (I → A) +
              (Fintype.card A * d) ^ 2 * Fintype.card (I → A)) * d) := hmul
      _ < d * T.card := hparam
      _ = T.card * d := by ring
  exact Nat.lt_of_mul_lt_mul_right hchain

/-- `Fin n` specialization, exposing the paper's `a^n` factors. -/
theorem nonaddable_fraction_fin [Fintype A] [Nontrivial A]
    {n t m d A₀ : ℕ} (T S : Finset (Line A (Fin n)))
    (blocks : Fin t → Finset (Fin n))
    (hT : SupportedInBlocks T blocks) (hblocks : ∀ j, (blocks j).card = m)
    (hS : Suitable S d)
    (hparam : (2 * A₀) *
      ((Fintype.card A * S.card) * (t * 2 ^ m) +
        (d ^ 2 * Fintype.card A ^ n +
          (Fintype.card A * d) ^ 2 * Fintype.card A ^ n) * d) <
      d * T.card) :
    (2 * A₀) * (nonaddable T S d).card < T.card := by
  apply nonaddable_fraction T S blocks hT hblocks hS
  simpa using hparam

end Erdos847LineExclusions
