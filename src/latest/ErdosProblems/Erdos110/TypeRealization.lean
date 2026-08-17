/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos110.Closure

/-!
# Realizing finite interleaving patterns

This is the club-guessing/type-realization lemma used in the
Lambie-Hanson construction.  It is phrased by recording, for each selected
point of the lower ladder, the interval between consecutive points of the
upper ladder in which it lies.
-/

noncomputable section

open Cardinal Set Order
open Classical

namespace Erdos110
namespace Height

open Ordinal

local instance realizationOrdinalLT : LT Ordinal := Ordinal.partialOrder.toLT
local instance realizationOrdinalLE : LE Ordinal := Ordinal.partialOrder.toLE

private def zeroBelowLambda : Set.Iio lambda.ord :=
  ⟨0, regular_lambda.ord_pos⟩

/-- The first `n` selected points of a ladder, regarded as ordinals below
`lambda`. -/
def initial (C : (a : S) → Ordinal.Club a.1) (a : S) (n : ℕ) :
    List (Set.Iio lambda.ord) :=
  List.ofFn fun i : Fin n ↦
    ⟨point C a i, (point_lt_height C a i).trans a.2.1⟩

@[simp] theorem length_initial (C : (a : S) → Ordinal.Club a.1)
    (a : S) (n : ℕ) : (initial C a n).length = n := by
  simp [initial]

/-- A list occurs as an initial ladder segment at a height satisfying `P`. -/
def HasPrefix (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (xs : List (Set.Iio lambda.ord)) : Prop :=
  ∃ a : S, P a ∧ initial C a xs.length = xs

/-- `Rich r xs` means that `xs` admits `r` successive unbounded choices and
then occurs as a ladder prefix in `P`. -/
def Rich (C : (a : S) → Ordinal.Club a.1) (P : S → Prop) :
    ℕ → List (Set.Iio lambda.ord) → Prop
  | 0, xs => HasPrefix C P xs
  | r + 1, xs => ∀ b : Set.Iio lambda.ord,
      ∃ x : Set.Iio lambda.ord, b.1 < x.1 ∧ Rich C P r (xs ++ [x])

private def badBound
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (r : ℕ) (xs : List (Set.Iio lambda.ord)) : Set.Iio lambda.ord :=
  if h : ∃ b : Set.Iio lambda.ord,
      ∀ x : Set.Iio lambda.ord, b.1 < x.1 → ¬ Rich C P r (xs ++ [x])
  then Classical.choose h else zeroBelowLambda

private theorem badBound_spec
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (r : ℕ) (xs : List (Set.Iio lambda.ord))
    (h : ¬ Rich C P (r + 1) xs) :
    ∀ x : Set.Iio lambda.ord,
      (badBound C P r xs).1 < x.1 → ¬ Rich C P r (xs ++ [x]) := by
  have hex : ∃ b : Set.Iio lambda.ord,
      ∀ x : Set.Iio lambda.ord, b.1 < x.1 → ¬ Rich C P r (xs ++ [x]) := by
    simpa only [Rich, not_forall, not_exists, not_and,
      Classical.not_not] using h
  rw [badBound, dif_pos hex]
  exact Classical.choose_spec hex

private def goodWitness
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (r : ℕ) (xs : List (Set.Iio lambda.ord))
    (b : Set.Iio lambda.ord) : Set.Iio lambda.ord :=
  if h : Rich C P (r + 1) xs then Classical.choose (h b)
  else zeroBelowLambda

private theorem goodWitness_spec
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (r : ℕ) (xs : List (Set.Iio lambda.ord))
    (b : Set.Iio lambda.ord) (h : Rich C P (r + 1) xs) :
    b.1 < (goodWitness C P r xs b).1 ∧
      Rich C P r (xs ++ [goodWitness C P r xs b]) := by
  rw [goodWitness, dif_pos h]
  exact Classical.choose_spec (h b)

private def prefixHeight
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (xs : List (Set.Iio lambda.ord)) : Set.Iio lambda.ord :=
  if h : HasPrefix C P xs then
    ⟨(Classical.choose h).1, (Classical.choose h).2.1⟩
  else zeroBelowLambda

private theorem prefixHeight_spec
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (xs : List (Set.Iio lambda.ord)) (h : HasPrefix C P xs) :
    ∃ a : S, P a ∧ initial C a xs.length = xs ∧
      a.1 = (prefixHeight C P xs).1 := by
  rw [prefixHeight, dif_pos h]
  exact ⟨Classical.choose h, (Classical.choose_spec h).1,
    (Classical.choose_spec h).2, rfl⟩

/-- A single countable family containing the three kinds of Skolem choices
needed in the realization proof. -/
private def realizationSkolem
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (op : ℕ) (xs : List (Set.Iio lambda.ord)) : Set.Iio lambda.ord :=
  if op % 3 = 0 then prefixHeight C P xs
  else if op % 3 = 1 then badBound C P (op / 3) xs
  else match xs with
    | [] => zeroBelowLambda
    | b :: pre => goodWitness C P (op / 3) pre b

private theorem realizationSkolem_height
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop) (xs) :
    realizationSkolem C P 0 xs = prefixHeight C P xs := by
  simp [realizationSkolem]

private theorem realizationSkolem_bad
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (r : ℕ) (xs) :
    realizationSkolem C P (3 * r + 1) xs = badBound C P r xs := by
  simp [realizationSkolem, Nat.add_mod]
  congr 3
  omega

private theorem realizationSkolem_good
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (r : ℕ) (xs) (b : Set.Iio lambda.ord) :
    realizationSkolem C P (3 * r + 2) (b :: xs) =
      goodWitness C P r xs b := by
  simp [realizationSkolem, Nat.add_mod]
  congr 4
  omega

private theorem rich_of_closed_extension
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (D : Ordinal.Club lambda.ord)
    (hD : ∀ d ∈ D.carrier, ∀ op xs,
      (∀ x ∈ xs, x.1 < d) →
        (realizationSkolem C P op xs).1 < d)
    (pre suf : List (Set.Iio lambda.ord))
    (hfull : HasPrefix C P (pre ++ suf))
    (hcross : ∀ x ∈ pre, ∀ y ∈ suf, x.1 < y.1)
    (hpair : suf.Pairwise fun x y ↦ x.1 < y.1)
    (hclosed : ∀ x ∈ suf, x.1 ∈ D.carrier) :
    Rich C P suf.length pre := by
  induction suf generalizing pre with
  | nil => simpa [Rich] using hfull
  | cons x xs ih =>
      have hpair' := (List.pairwise_cons.1 hpair)
      have hnext : Rich C P xs.length (pre ++ [x]) := by
        apply ih (pre := pre ++ [x])
        · simpa [List.append_assoc] using hfull
        · intro y hy z hz
          simp only [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact hcross y hy z (by simp [hz])
          · exact hpair'.1 z hz
        · exact hpair'.2
        · exact fun y hy ↦ hclosed y (by simp [hy])
      have hgoal : Rich C P (xs.length + 1) pre := by
        by_contra hn
        have hb := hD x.1 (hclosed x (by simp)) (3 * xs.length + 1) pre
          (fun y hy ↦ hcross y hy x (by simp))
        rw [realizationSkolem_bad] at hb
        exact badBound_spec C P xs.length pre hn x hb hnext
      simpa only [List.length_cons] using hgoal

private theorem exists_placed
    (C : (a : S) → Ordinal.Club a.1) (P : S → Prop)
    (D : Ordinal.Club lambda.ord)
    (hD : ∀ d ∈ D.carrier, ∀ op xs,
      (∀ x ∈ xs, x.1 < d) →
        (realizationSkolem C P op xs).1 < d)
    (pre : List (Set.Iio lambda.ord))
    (bounds : List (Set.Iio lambda.ord × Set.Iio lambda.ord))
    (hrich : Rich C P bounds.length pre)
    (hlt : ∀ b ∈ bounds, b.1.1 < b.2.1)
    (hmono : bounds.Pairwise fun b c ↦ b.2.1 ≤ c.2.1)
    (hpre : ∀ x ∈ pre, ∀ b ∈ bounds, x.1 < b.2.1)
    (hclosed : ∀ b ∈ bounds, b.2.1 ∈ D.carrier) :
    ∃ tail : List (Set.Iio lambda.ord),
      HasPrefix C P (pre ++ tail) ∧
      List.Forall₂ (fun b x ↦ b.1.1 < x.1 ∧ x.1 < b.2.1) bounds tail := by
  induction bounds generalizing pre with
  | nil =>
      exact ⟨[], by simpa [Rich] using hrich, .nil⟩
  | cons b bounds ih =>
      have hmono' := List.pairwise_cons.1 hmono
      have hw := goodWitness_spec C P bounds.length pre b.1 (by
        simpa only [List.length_cons] using hrich)
      let x := goodWitness C P bounds.length pre b.1
      have hxlt : x.1 < b.2.1 := by
        have hc := hD b.2.1 (hclosed b (by simp))
          (3 * bounds.length + 2) (b.1 :: pre) (by
            intro y hy
            simp only [List.mem_cons] at hy
            rcases hy with rfl | hy
            · exact hlt b (by simp)
            · exact hpre y hy b (by simp))
        rw [realizationSkolem_good] at hc
        exact hc
      obtain ⟨tail, htail, hrel⟩ := ih (pre := pre ++ [x]) hw.2
        (fun c hc ↦ hlt c (by simp [hc])) hmono'.2 (by
          intro y hy c hc
          simp only [List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact (hpre y hy b (by simp)).trans_le (hmono'.1 c hc)
          · exact hxlt.trans_le (hmono'.1 c hc))
        (fun c hc ↦ hclosed c (by simp [hc]))
      refine ⟨x :: tail, ?_, .cons ⟨hw.1, hxlt⟩ hrel⟩
      simpa [List.append_assoc] using htail

def upperPoint (C : (a : S) → Ordinal.Club a.1)
    (a : S) (r : ℕ) : Set.Iio lambda.ord :=
  ⟨point C a r, (point_lt_height C a r).trans a.2.1⟩

def lowerPoint (C : (a : S) → Ordinal.Club a.1)
    (a : S) (r : ℕ) : Set.Iio lambda.ord :=
  if r = 0 then zeroBelowLambda else upperPoint C a (r - 1)

private def interval (C : (a : S) → Ordinal.Club a.1)
    (a : S) (r : ℕ) : Set.Iio lambda.ord × Set.Iio lambda.ord :=
  (lowerPoint C a r, upperPoint C a r)

private theorem interval_lt
    (C : (a : S) → Ordinal.Club a.1) (a : S) (r : ℕ) :
    (interval C a r).1.1 < (interval C a r).2.1 := by
  by_cases hr : r = 0
  · subst r
    haveI : IsEmpty (Set.Iio (natIndex 0)) := isEmpty_iff.mpr fun j ↦ by
      have hj : j.1.1 < (0 : Ordinal) := by
        exact j.2
      exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1.1)) hj
    simpa [interval, lowerPoint, upperPoint, point, zeroBelowLambda,
      iSup_of_empty] using ladder_above C a (natIndex 0)
  · simp only [interval, lowerPoint, hr, if_false]
    change point C a (r - 1) < point C a r
    apply point_strictMono C a
    exact Nat.sub_one_lt hr

private theorem upperPoint_mono
    (C : (a : S) → Ordinal.Club a.1) (a : S) {r s : ℕ} (h : r ≤ s) :
    (upperPoint C a r).1 ≤ (upperPoint C a s).1 :=
  (point_strictMono C a).monotone h

private theorem upperPoint_mem
    (C : (a : S) → Ordinal.Club a.1) (a : S) (r : ℕ) :
    (upperPoint C a r).1 ∈ C a :=
  point_mem C a r

private theorem forall_right_lt_of_forall₂
    {bounds : List (Set.Iio lambda.ord × Set.Iio lambda.ord)}
    {xs : List (Set.Iio lambda.ord)} {d : Ordinal}
    (hupper : ∀ b ∈ bounds, b.2.1 < d)
    (h : List.Forall₂ (fun b x ↦ b.1.1 < x.1 ∧ x.1 < b.2.1) bounds xs) :
    ∀ x ∈ xs, x.1 < d := by
  induction h with
  | nil => simp
  | cons hr hrs ih =>
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hr.2.trans (hupper _ (by simp))
      · exact ih (fun b hb ↦ hupper b (by simp [hb])) x hx

/-- Finite rank patterns are simultaneously realized inside every
club-guessing cell. -/
theorem realizeRanks
    (C : (a : S) → Ordinal.Club a.1)
    (P : S → Prop)
    (hguess : ∀ D : Ordinal.Club lambda.ord,
      ∃ a : S, P a ∧ (C a).carrier ⊆ D.carrier)
    (ranks : List ℕ)
    (hmono : ranks.Pairwise (fun r s ↦ r ≤ s)) :
    ∃ a b : S, P a ∧ P b ∧ a.1 < b.1 ∧
      List.Forall₂
        (fun r x ↦ (lowerPoint C b r).1 < x.1 ∧
          x.1 < (upperPoint C b r).1)
        ranks (initial C a ranks.length) := by
  let F := realizationSkolem C P
  let D := closureClub F
  obtain ⟨b, hPb, hbD⟩ := hguess D
  have hpointD (r : ℕ) : (upperPoint C b r).1 ∈ D.carrier :=
    hbD (upperPoint_mem C b r)
  have hrich : Rich C P ranks.length [] := by
    simpa only [length_initial] using
      (rich_of_closed_extension C P D
        (fun d hd op xs hxs ↦ closureClub_closed F hd op xs hxs)
        [] (initial C b ranks.length)
        (by
          refine ⟨b, hPb, ?_⟩
          simp) (by simp) (by
          rw [initial, List.pairwise_ofFn]
          intro i j hij
          apply point_strictMono C b
          exact hij) (by
            rw [initial, List.forall_mem_ofFn_iff]
            intro i
            exact hbD (point_mem C b i)))
  let bounds := ranks.map (interval C b)
  obtain ⟨tail, htail, hrel⟩ := exists_placed C P D
    (fun d hd op xs hxs ↦ closureClub_closed F hd op xs hxs)
    [] bounds (by simpa [bounds] using hrich)
    (by intro q hq
        obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
        exact interval_lt C b r)
    (by rw [List.pairwise_map]
        exact hmono.imp (fun h ↦ upperPoint_mono C b h))
    (by simp) (by
      intro q hq
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
      exact hpointD r)
  have hbmem : b.1 ∈ D.carrier := by
    apply D.isClub.mem_of_isAcc b.2.1
    exact (C b).isClub.isAcc.mono hbD
  have htailBound : ∀ x ∈ tail, x.1 < b.1 := by
    apply forall_right_lt_of_forall₂
      (bounds := bounds) (h := hrel)
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hq
    exact point_lt_height C b r
  have hheight := closureClub_closed F hbmem 0 tail htailBound
  change (realizationSkolem C P 0 tail).1 < b.1 at hheight
  rw [realizationSkolem_height] at hheight
  obtain ⟨a, hPa, haprefix, haheight⟩ := prefixHeight_spec C P tail htail
  have hab : a.1 < b.1 := haheight.trans_lt hheight
  refine ⟨a, b, hPa, hPb, hab, ?_⟩
  have hlen : tail.length = ranks.length := by
    simpa [bounds] using hrel.length_eq.symm
  have hpref : initial C a ranks.length = tail := by
    simpa [hlen] using haprefix
  rw [hpref]
  exact List.forall₂_map_left_iff.mp hrel

end Height
end Erdos110
