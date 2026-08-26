import ErdosProblems.Erdos591.SixClique

namespace Erdos591.Negative

/-!
The negative coloring is stated in the Handbook for finite strictly
increasing sequences.  `G2`, on the other hand, uses gap codes: an outer
list records the level count, and every inner list records first its length
and then its body gaps.  This file makes that translation explicit.  In
particular, no identification of arbitrary lists with increasing lists is
left implicit in the density argument.
-/

/-- A gap together with the information that the corresponding coordinate
is a structural (box) coordinate. -/
abbrev TaggedGap := ℕ × Bool

/-- The self-delimiting word for one height-one level.  Its head records
the number of following body gaps. -/
def levelWord (a : List ℕ) : List ℕ := a.length :: a

/-- The untagged gap word underlying a height-two sequence. -/
def g2Word (s : G2) : List ℕ := s.length :: s.flatMap levelWord

@[simp] theorem levelWord_ne_nil (a : List ℕ) : levelWord a ≠ [] := by
  simp [levelWord]

theorem lex_append_of_length_eq {α : Type*} {r : α → α → Prop}
    {s t : List α} (h : List.Lex r s t) (hlen : s.length = t.length)
    (u v : List α) : List.Lex r (s ++ u) (t ++ v) := by
  induction h with
  | nil => simp at hlen
  | @rel a b s t hab =>
      exact List.Lex.rel hab
  | @cons a s t h ih =>
      exact List.Lex.cons (ih (by simpa using hlen))

theorem levelWord_lex_of_SL {a b : List ℕ} (hab : WeakPigeon.SL a b)
    (u v : List ℕ) :
    List.Lex (· < ·) (levelWord a ++ u) (levelWord b ++ v) := by
  rcases List.shortlex_def.mp hab with hlen | ⟨hlen, hlex⟩
  · exact List.Lex.rel hlen
  · apply lex_append_of_length_eq
    · rw [levelWord, levelWord, hlen]
      exact List.Lex.cons hlex
    · simp [levelWord, hlen]

/-- Concatenating the self-delimiting level words preserves outer
lexicographic comparison. -/
theorem flatMap_levelWord_mono {s t : G2}
    (hst : List.Lex WeakPigeon.SL s t) :
    List.Lex (· < ·) (s.flatMap levelWord) (t.flatMap levelWord) := by
  induction s generalizing t with
  | nil =>
      cases t with
      | nil => cases hst
      | cons b t => simp [levelWord]
  | cons a s ih =>
      cases t with
      | nil => cases hst
      | cons b t =>
          rcases List.cons_lex_cons_iff.mp hst with hab | heq
          · simpa only [List.flatMap_cons] using
              levelWord_lex_of_SL hab (s.flatMap levelWord)
                (t.flatMap levelWord)
          · rw [← heq.1]
            simp only [List.flatMap_cons]
            exact List.Lex.append_left (· < ·) (ih heq.2) (levelWord a)

theorem g2Word_mono {s t : G2} (hst : G2LT s t) :
    List.Lex (· < ·) (g2Word s) (g2Word t) := by
  rcases List.shortlex_def.mp hst with hlen | ⟨hlen, hlex⟩
  · exact List.Lex.rel hlen
  · rw [g2Word, g2Word, hlen]
    exact List.Lex.cons (flatMap_levelWord_mono hlex)

/-- Insert one unit between successive cumulative gaps, retaining tags. -/
def gapsFrom : ℕ → List TaggedGap → List TaggedCoord
  | _, [] => []
  | k, (d, box) :: ds =>
      ⟨k + d, box⟩ :: gapsFrom (k + d + 1) ds

@[simp] theorem gapsFrom_nil (k : ℕ) : gapsFrom k [] = [] := rfl

@[simp] theorem gapsFrom_cons (k d : ℕ) (box : Bool) (ds : List TaggedGap) :
    gapsFrom k ((d, box) :: ds) =
      ⟨k + d, box⟩ :: gapsFrom (k + d + 1) ds := rfl

@[simp] theorem length_gapsFrom (k : ℕ) (ds : List TaggedGap) :
    (gapsFrom k ds).length = ds.length := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih => cases d; simp [gapsFrom, ih]

theorem mem_gapsFrom_value_ge {k : ℕ} {ds : List TaggedGap}
    {q : TaggedCoord} (hq : q ∈ gapsFrom k ds) : k ≤ q.value := by
  induction ds generalizing k with
  | nil => simp [gapsFrom] at hq
  | cons d ds ih =>
      rcases d with ⟨d, box⟩
      simp only [gapsFrom, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Nat.le_add_right _ _
      · exact (Nat.le_add_right k d).trans
          ((Nat.le_succ _).trans (ih hq))

theorem pairwise_gapsFrom_value (k : ℕ) (ds : List TaggedGap) :
    (gapsFrom k ds).Pairwise (fun a b => a.value < b.value) := by
  induction ds generalizing k with
  | nil => simp [gapsFrom]
  | cons d ds ih =>
      rcases d with ⟨d, box⟩
      simp only [gapsFrom, List.pairwise_cons]
      constructor
      · intro q hq
        exact (Nat.lt_succ_self _).trans_le (mem_gapsFrom_value_ge hq)
      · exact ih _

theorem gapsFrom_values (k : ℕ) (ds : List TaggedGap) :
    (gapsFrom k ds).map TaggedCoord.value =
      Erdos590.Larson.intoInc k (ds.map Prod.fst) := by
  induction ds generalizing k with
  | nil => rfl
  | cons d ds ih =>
      rcases d with ⟨d, box⟩
      simp [gapsFrom, Erdos590.Larson.intoInc, ih]

/-- The marker and body gaps for one height-one level. -/
def levelGaps (a : List ℕ) : List TaggedGap :=
  (a.length, true) :: a.map fun d => (d, false)

/-- The complete gap word for a height-two good sequence.  The first gap is
the root marker; each subsequent level starts with its length marker. -/
def g2Gaps (s : G2) : List TaggedGap :=
  (s.length, true) :: s.flatMap levelGaps

@[simp] theorem levelGaps_fst (a : List ℕ) :
    (levelGaps a).map Prod.fst = levelWord a := by
  simp [levelGaps, levelWord, Function.comp_def]

@[simp] theorem g2Gaps_fst (s : G2) :
    (g2Gaps s).map Prod.fst = g2Word s := by
  simp only [g2Gaps, g2Word, List.map_cons, Prod.fst,
    List.map_flatMap, Function.comp_apply, levelGaps_fst]

@[simp] theorem g2Gaps_ne_nil (s : G2) : g2Gaps s ≠ [] := by
  simp [g2Gaps]

/-- Change only the tag of the final coordinate to `true`. -/
def boxLast : List TaggedCoord → List TaggedCoord
  | [] => []
  | q :: qs =>
      if qs = [] then [⟨q.value, true⟩] else q :: boxLast qs

@[simp] theorem boxLast_nil : boxLast [] = [] := rfl

theorem length_boxLast (s : List TaggedCoord) :
    (boxLast s).length = s.length := by
  induction s with
  | nil => rfl
  | cons q qs ih =>
      by_cases h : qs = []
      · simp [boxLast, h]
      · simp [boxLast, h, ih]

theorem boxLast_ne_nil_iff (s : List TaggedCoord) :
    boxLast s ≠ [] ↔ s ≠ [] := by
  cases s with
  | nil => simp
  | cons q qs =>
      by_cases h : qs = [] <;> simp [boxLast, h]

theorem boxLast_values (s : List TaggedCoord) :
    (boxLast s).map TaggedCoord.value = s.map TaggedCoord.value := by
  induction s with
  | nil => rfl
  | cons q qs ih =>
      by_cases h : qs = []
      · simp [boxLast, h]
      · simp [boxLast, h, ih]

theorem pairwise_boxLast_value {s : List TaggedCoord}
    (hs : s.Pairwise (fun a b => a.value < b.value)) :
    (boxLast s).Pairwise (fun a b => a.value < b.value) := by
  have hmap : (boxLast s).map TaggedCoord.value =
      s.map TaggedCoord.value := boxLast_values s
  have hs' : (s.map TaggedCoord.value).Pairwise (· < ·) := by
    simpa only [List.pairwise_map] using hs
  have hb' : ((boxLast s).map TaggedCoord.value).Pairwise (· < ·) :=
    hmap.symm ▸ hs'
  simpa only [List.pairwise_map] using hb'

/-- The literal strictly increasing tagged sequence used by the Handbook
coloring, obtained from the nested gap code. -/
def canonicalSequence (s : G2) : List TaggedCoord :=
  boxLast (gapsFrom 0 (g2Gaps s))

theorem canonicalSequence_ne_nil (s : G2) : canonicalSequence s ≠ [] := by
  rw [canonicalSequence, boxLast_ne_nil_iff]
  intro h
  have hlen := congrArg List.length h
  simp [g2Gaps, length_gapsFrom] at hlen

theorem canonicalSequence_pairwise (s : G2) :
    (canonicalSequence s).Pairwise (fun a b => a.value < b.value) := by
  exact pairwise_boxLast_value (pairwise_gapsFrom_value 0 (g2Gaps s))

theorem canonicalSequence_values (s : G2) :
    (canonicalSequence s).map TaggedCoord.value =
      Erdos590.Larson.intoInc 0 (g2Word s) := by
  rw [canonicalSequence, boxLast_values, gapsFrom_values, g2Gaps_fst]

/-- The numerical words used by the graph preserve the exact `G2LT`
ordering, not merely the cardinality of `G2`. -/
theorem canonicalSequence_lex_mono {s t : G2} (hst : G2LT s t) :
    List.Lex (· < ·)
      ((canonicalSequence s).map TaggedCoord.value)
      ((canonicalSequence t).map TaggedCoord.value) := by
  rw [canonicalSequence_values, canonicalSequence_values,
    Erdos590.Larson.lex_intoInc_iff]
  exact g2Word_mono hst

/-- The first numerical coordinate is exactly the outer marker. -/
@[simp] theorem canonicalSequence_head_value (s : G2) :
    (canonicalSequence s).head?.map TaggedCoord.value = some s.length := by
  by_cases htail : gapsFrom (s.length + 1) (s.flatMap levelGaps) = []
  · simp [canonicalSequence, g2Gaps, boxLast, htail]
  · simp [canonicalSequence, g2Gaps, boxLast, htail]

/-- The concrete blue graph used for the negative half of Problem 591. -/
def handbookGraph : SimpleGraph G2 := interlacingGraph canonicalSequence

theorem handbookGraph_no_six :
    ¬ ∃ S : Set G2, handbookGraph.IsClique S ∧ Cardinal.mk S = 6 := by
  exact interlacingGraph_no_six_clique canonicalSequence

abbrev orderedCanonicalSequence (s : OrderedG2) : List TaggedCoord :=
  canonicalSequence s

def orderedHandbookGraph : SimpleGraph OrderedG2 :=
  interlacingGraph orderedCanonicalSequence

theorem orderedHandbookGraph_no_six :
    ¬ ∃ S : Set OrderedG2,
      orderedHandbookGraph.IsClique S ∧ Cardinal.mk S = 6 := by
  exact interlacingGraph_no_six_clique orderedCanonicalSequence

noncomputable def orderedG2RelIso :
    ((· < ·) : OrderedG2 → OrderedG2 → Prop) ≃r
      ((· < ·) : (Ordinal.omega0 ^ (Ordinal.omega0 ^ 2)).ToType →
        (Ordinal.omega0 ^ (Ordinal.omega0 ^ 2)).ToType → Prop) := by
  apply Classical.choice
  apply Ordinal.type_eq.mp
  rw [orderedG2_type, Ordinal.type_toType]

/-- Once the remaining density lemma has been proved on the ordered wrapper,
the exact negative partition relation follows without any further
combinatorics. -/
theorem handbook_negative_six_of_density
    (hhit : MeetsEveryFullSet
      ((· < ·) : OrderedG2 → OrderedG2 → Prop)
      (Ordinal.omega0 ^ (Ordinal.omega0 ^ 2) : Ordinal.{0})
      orderedHandbookGraph) :
    ¬ OrdinalCardinalRamsey
      (Ordinal.omega0 ^ (Ordinal.omega0 ^ 2) : Ordinal.{0})
      (Ordinal.omega0 ^ (Ordinal.omega0 ^ 2) : Ordinal.{0})
      (6 : Cardinal.{0}) := by
  exact not_ordinalCardinalRamsey_of_model
    (X := OrderedG2)
    (r := ((· < ·) : OrderedG2 → OrderedG2 → Prop))
    (alpha := (Ordinal.omega0 ^ (Ordinal.omega0 ^ 2) : Ordinal.{0}))
    (n := 6) orderedG2RelIso orderedHandbookGraph
    orderedHandbookGraph_no_six hhit

end Erdos591.Negative
