/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions

/-!
# The sharp cups-versus-caps theorem

This file proves the ordered, two-colour tight-path form of the classical
Erdős--Szekeres cups-versus-caps theorem.  Applying the two colours to the
two possible comparisons of consecutive secant slopes gives the usual planar
statement.  The numerical bound is the sharp one needed in Proposition 2.1
of Pohoata--Zakharov:

`Nat.choose (a + b - 4) (a - 2) + 1`.
-/

namespace Erdos651

noncomputable section

open scoped BigOperators

/-! ## Ordered tight paths -/

/-- A list is ordered when its entries are strictly increasing.  We use a
small recursive definition because its equations are particularly convenient
for the endpoint-gluing induction below. -/
def Ordered : List ℕ → Prop
  | i :: j :: tail => i < j ∧ Ordered (j :: tail)
  | _ => True

/-- Every entry of `I` belongs to the ambient finite set `S`. -/
def ListIn (I : List ℕ) (S : Finset ℕ) : Prop := ∀ i ∈ I, i ∈ S

/-- `TightPath χ c I` means that every three consecutive entries of `I`
have colour `c`. -/
def TightPath (χ : ℕ → ℕ → ℕ → Bool) (c : Bool) : List ℕ → Prop
  | i :: j :: k :: tail => χ i j k = c ∧ TightPath χ c (j :: k :: tail)
  | _ => True

/-- An ordered monochromatic tight path of prescribed length in `S`. -/
def HasTightPath (χ : ℕ → ℕ → ℕ → Bool) (c : Bool)
    (S : Finset ℕ) (n : ℕ) : Prop :=
  ∃ I : List ℕ, Ordered I ∧ ListIn I S ∧ I.length = n ∧ TightPath χ c I

lemma listIn_mono {I : List ℕ} {S T : Finset ℕ} (hST : S ⊆ T)
    (hI : ListIn I S) : ListIn I T := by
  intro i hi
  exact hST (hI i hi)

lemma hasTightPath_mono {χ : ℕ → ℕ → ℕ → Bool} {c : Bool}
    {S T : Finset ℕ} {n : ℕ} (hST : S ⊆ T) :
    HasTightPath χ c S n → HasTightPath χ c T n := by
  rintro ⟨I, hI, hIS, hlen, hpath⟩
  exact ⟨I, hI, listIn_mono hST hIS, hlen, hpath⟩

lemma tightPath_append_last {χ : ℕ → ℕ → ℕ → Bool} {c : Bool}
    (u : List ℕ) {z y w : ℕ}
    (hpath : TightPath χ c (u ++ [z, y])) (hzyw : χ z y w = c) :
    TightPath χ c (u ++ [z, y, w]) := by
  induction u with
  | nil => exact ⟨hzyw, trivial⟩
  | cons x u ih =>
      cases u with
      | nil =>
          exact ⟨hpath.1, hzyw, trivial⟩
      | cons x' u =>
          cases u with
          | nil => exact ⟨hpath.1, hpath.2.1, hzyw, trivial⟩
          | cons q tail => exact ⟨hpath.1, ih hpath.2⟩

lemma exists_append_two_of_two_le_length :
    ∀ {I : List ℕ}, 2 ≤ I.length → ∃ u z y, I = u ++ [z, y]
  | [], h => by simp at h
  | [x], h => by simp at h
  | x :: y :: tail, _ => by
      by_cases ht : tail = []
      · subst tail
        exact ⟨[], x, y, rfl⟩
      · have htail : 2 ≤ (y :: tail).length := by
          cases tail with
          | nil => contradiction
          | cons z tail => simp
        obtain ⟨u, z, w, hu⟩ := exists_append_two_of_two_le_length htail
        exact ⟨x :: u, z, w, by simp [hu]⟩

lemma hasTightPath_two_of_one_lt_card
    (χ : ℕ → ℕ → ℕ → Bool) (c : Bool) (S : Finset ℕ)
    (hS : 1 < S.card) : HasTightPath χ c S 2 := by
  rw [Finset.one_lt_card] at hS
  obtain ⟨x, hx, y, hy, hxy⟩ := hS
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact ⟨[x, y], by simp [Ordered, hlt], by simpa [ListIn, hx, hy], rfl,
      by simp [TightPath]⟩
  · exact (hxy heq).elim
  · exact ⟨[y, x], by simp [Ordered, hgt], by simpa [ListIn, hx, hy], rfl,
      by simp [TightPath]⟩

private lemma ordered_append_last {u : List ℕ} {z y w : ℕ}
    (hord : Ordered (u ++ [z, y])) (hyw : y < w) :
    Ordered (u ++ [z, y, w]) := by
  induction u with
  | nil => exact ⟨hord.1, hyw, trivial⟩
  | cons x u ih =>
      cases u with
      | nil => exact ⟨hord.1, hord.2.1, hyw, trivial⟩
      | cons x' u =>
          exact ⟨hord.1, ih hord.2⟩

private lemma listIn_append_last {u : List ℕ} {z y w : ℕ} {S : Finset ℕ}
    (hI : ListIn (u ++ [z, y]) S) (hw : w ∈ S) :
    ListIn (u ++ [z, y, w]) S := by
  intro i hi
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hi
  by_cases hiw : i = w
  · simpa [hiw] using hw
  · apply hI i
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false]
    tauto

private lemma ordered_last_two {u : List ℕ} {z y : ℕ}
    (h : Ordered (u ++ [z, y])) : z < y := by
  induction u with
  | nil => exact h.1
  | cons x u ih =>
      cases u with
      | nil => exact h.2.1
      | cons x' u => exact ih h.2

/-!
The following bound is proved in its contrapositive form.  The endpoint set
`Y` consists of the right endpoints of blue paths of length `b-1`.  Its
complement avoids a blue path of length `b-1`; and the standard endpoint
gluing argument shows that `Y` avoids a red path of length `a-1`.
-/
private theorem tightPath_avoiding_card_le
    (χ : ℕ → ℕ → ℕ → Bool) :
    ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → ∀ S : Finset ℕ,
      ¬ HasTightPath χ true S a →
      ¬ HasTightPath χ false S b →
      S.card ≤ Nat.choose (a + b - 4) (a - 2) := by
  intro a b ha hb
  generalize hn : a + b = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
      intro S hred hblue
      by_cases ha2 : a = 2
      · subst a
        have hcard : S.card ≤ 1 := by
          by_contra h
          have hone : 1 < S.card := by omega
          exact hred (hasTightPath_two_of_one_lt_card χ true S hone)
        rw [← hn]
        simpa using hcard
      by_cases hb2 : b = 2
      · subst b
        have hcard : S.card ≤ 1 := by
          by_contra h
          have hone : 1 < S.card := by omega
          exact hblue (hasTightPath_two_of_one_lt_card χ false S hone)
        rw [← hn]
        simpa using hcard
      have ha3 : 3 ≤ a := by omega
      have hb3 : 3 ≤ b := by omega
      classical
      let Y : Finset ℕ := S.filter fun y =>
        ∃ (u : List ℕ) (z : ℕ),
          Ordered (u ++ [z, y]) ∧ ListIn (u ++ [z, y]) S ∧
          (u ++ [z, y]).length = b - 1 ∧ TightPath χ false (u ++ [z, y])
      let C : Finset ℕ := S \ Y
      have hYS : Y ⊆ S := by
        simpa [Y] using (Finset.filter_subset
          (fun y : ℕ => ∃ (u : List ℕ) (z : ℕ),
            Ordered (u ++ [z, y]) ∧ ListIn (u ++ [z, y]) S ∧
            (u ++ [z, y]).length = b - 1 ∧ TightPath χ false (u ++ [z, y])) S)
      have hCS : C ⊆ S := Finset.sdiff_subset
      have hC_red : ¬ HasTightPath χ true C a :=
        fun h => hred (hasTightPath_mono hCS h)
      have hC_blue : ¬ HasTightPath χ false C (b - 1) := by
        rintro ⟨I, hord, hIC, hlen, hpath⟩
        have hlen2 : 2 ≤ I.length := by omega
        obtain ⟨u, z, y, rfl⟩ := exists_append_two_of_two_le_length hlen2
        have hyC : y ∈ C := hIC y (by simp)
        have hyY : y ∈ Y := by
          simp only [Y, Finset.mem_filter]
          refine ⟨hCS hyC, u, z, hord, listIn_mono hCS hIC, hlen, hpath⟩
        exact (Finset.mem_sdiff.mp hyC).2 hyY
      have hY_blue : ¬ HasTightPath χ false Y b :=
        fun h => hblue (hasTightPath_mono hYS h)
      have hY_red : ¬ HasTightPath χ true Y (a - 1) := by
        rintro ⟨I, hordI, hIY, hlenI, hpathI⟩
        cases I with
        | nil => simp at hlenI; omega
        | cons y rest =>
            cases rest with
            | nil => simp at hlenI; omega
            | cons w tail =>
                have hyY : y ∈ Y := hIY y (by simp)
                obtain ⟨hyS, u, z, hordT, hTS, hlenT, hpathT⟩ :=
                  (Finset.mem_filter.mp hyY)
                have hzy : z < y := ordered_last_two hordT
                have hyw : y < w := by simpa [Ordered] using hordI.1
                have hzS : z ∈ S := hTS z (by simp)
                have hwS : w ∈ S := hYS (hIY w (by simp))
                by_cases hcol : χ z y w = true
                · apply hred
                  refine ⟨z :: y :: w :: tail, ?_, ?_, ?_, ?_⟩
                  · exact ⟨hzy, hordI⟩
                  · intro q hq
                    simp only [List.mem_cons] at hq
                    rcases hq with rfl | hq
                    · exact hzS
                    · exact hYS (hIY q (by simpa using hq))
                  · simp at hlenI ⊢
                    omega
                  · exact ⟨hcol, hpathI⟩
                · have hcol' : χ z y w = false := by
                    cases h : χ z y w <;> simp_all
                  apply hblue
                  refine ⟨u ++ [z, y, w], ordered_append_last hordT hyw,
                    listIn_append_last hTS hwS, ?_,
                    tightPath_append_last u hpathT hcol'⟩
                  simp at hlenT ⊢
                  omega
      have hCcard : C.card ≤ Nat.choose (a + (b - 1) - 4) (a - 2) := by
        apply ih (a + (b - 1)) (by omega) a (b - 1) ha (by omega) rfl C hC_red hC_blue
      have hYcard : Y.card ≤ Nat.choose ((a - 1) + b - 4) ((a - 1) - 2) := by
        apply ih ((a - 1) + b) (by omega) (a - 1) b (by omega) hb rfl Y hY_red hY_blue
      have hpartition : C.card + Y.card = S.card := by
        dsimp [C]
        rw [Finset.card_sdiff_add_card]
        rw [Finset.union_eq_left.mpr hYS]
      rw [← hpartition]
      calc
        C.card + Y.card ≤
            Nat.choose (a + (b - 1) - 4) (a - 2) +
              Nat.choose ((a - 1) + b - 4) ((a - 1) - 2) :=
          Nat.add_le_add hCcard hYcard
        _ = Nat.choose (a + b - 4) (a - 2) := by
          have h1 : a + (b - 1) - 4 = a + b - 5 := by omega
          have h2 : (a - 1) + b - 4 = a + b - 5 := by omega
          have h3 : (a - 1) - 2 = a - 3 := by omega
          have hn' : a + b - 4 = (a + b - 5) + 1 := by omega
          have hk : a - 2 = (a - 3) + 1 := by omega
          rw [h1, h2, h3, hn', hk, Nat.choose_succ_succ]
          simp only [Nat.succ_eq_add_one]
          ac_rfl
        _ = Nat.choose (n - 4) (a - 2) := by rw [← hn]

/-- The sharp ordered cups-versus-caps theorem for an arbitrary two-colouring
of consecutive triples. -/
theorem ordered_cups_caps
    (χ : ℕ → ℕ → ℕ → Bool) (S : Finset ℕ) (a b : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : Nat.choose (a + b - 4) (a - 2) < S.card) :
    HasTightPath χ true S a ∨ HasTightPath χ false S b := by
  by_contra h
  push_neg at h
  exact (not_le_of_gt hcard) (tightPath_avoiding_card_le χ a b ha hb S h.1 h.2)

/-! ## Planar cups and caps -/

/-- First coordinate of a point of the plane. -/
def planeX (p : Point 2) : ℝ := p 0

/-- Second coordinate of a point of the plane. -/
def planeY (p : Point 2) : ℝ := p 1

/-- Slope of the secant through two planar points. -/
def secantSlope (p q : Point 2) : ℝ :=
  (planeY q - planeY p) / (planeX q - planeX p)

/-- The successive secant slopes along `I` are strictly increasing. -/
def IncreasingSlopes (p : ℕ → Point 2) (I : List ℕ) : Prop :=
  TightPath
    (fun i j k => decide (secantSlope (p i) (p j) < secantSlope (p j) (p k)))
    true I

/-- The decreasing colour together with the no-equal-slopes condition.  By
trichotomy on `ℝ`, these two clauses say exactly that the successive slopes
strictly decrease. -/
def DecreasingSlopes (p : ℕ → Point 2) (I : List ℕ) : Prop :=
  TightPath
      (fun i j k => decide (secantSlope (p i) (p j) < secantSlope (p j) (p k)))
      false I ∧
    ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I, i < j → j < k →
      secantSlope (p i) (p j) ≠ secantSlope (p j) (p k)

/-- The enumeration `I` follows increasing first coordinate. -/
def LeftToRight (p : ℕ → Point 2) (I : List ℕ) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i < j → planeX (p i) < planeX (p j)

/-- An indexed planar cup.  The first conjunct records that indices occur in
their prescribed left-to-right order. -/
def IsPlanarCup (p : ℕ → Point 2) (I : List ℕ) : Prop :=
  Ordered I ∧ LeftToRight p I ∧ IncreasingSlopes p I

/-- An indexed planar cap. -/
def IsPlanarCap (p : ℕ → Point 2) (I : List ℕ) : Prop :=
  Ordered I ∧ LeftToRight p I ∧ DecreasingSlopes p I

private lemma tightPath_slope_true
    (p : ℕ → Point 2) (I : List ℕ)
    (h : TightPath
      (fun i j k => decide (secantSlope (p i) (p j) < secantSlope (p j) (p k)))
      true I) : IncreasingSlopes p I := by
  exact h

private lemma tightPath_slope_false
    (p : ℕ → Point 2) (S : Finset ℕ) (I : List ℕ)
    (hIS : ListIn I S)
    (hne : ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i < j → j < k →
      secantSlope (p i) (p j) ≠ secantSlope (p j) (p k))
    (hord : Ordered I)
    (h : TightPath
      (fun i j k => decide (secantSlope (p i) (p j) < secantSlope (p j) (p k)))
      false I) : DecreasingSlopes p I := by
  refine ⟨h, ?_⟩
  intro i hi j hj k hk hij hjk
  exact hne i (hIS i hi) j (hIS j hj) k (hIS k hk) hij hjk

/-- The exact planar cups-versus-caps bound.  `hne` is the no-three-collinear
condition in slope form.  (The usual harmless rotation of the point set lets
the index order be chosen so first coordinates increase.) -/
theorem planar_cups_caps
    (p : ℕ → Point 2) (S : Finset ℕ) (a b : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hx : ∀ i ∈ S, ∀ j ∈ S, i < j → planeX (p i) < planeX (p j))
    (hne : ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i < j → j < k →
      secantSlope (p i) (p j) ≠ secantSlope (p j) (p k))
    (hcard : Nat.choose (a + b - 4) (a - 2) < S.card) :
    (∃ I : List ℕ, ListIn I S ∧ I.length = a ∧ IsPlanarCup p I) ∨
      (∃ I : List ℕ, ListIn I S ∧ I.length = b ∧ IsPlanarCap p I) := by
  let χ : ℕ → ℕ → ℕ → Bool := fun i j k =>
    decide (secantSlope (p i) (p j) < secantSlope (p j) (p k))
  rcases ordered_cups_caps χ S a b ha hb hcard with hcup | hcap
  · obtain ⟨I, hord, hIS, hlen, hpath⟩ := hcup
    exact Or.inl ⟨I, hIS, hlen, hord,
      (fun i hi j hj hij => hx i (hIS i hi) j (hIS j hj) hij),
      tightPath_slope_true p I hpath⟩
  · obtain ⟨I, hord, hIS, hlen, hpath⟩ := hcap
    exact Or.inr ⟨I, hIS, hlen, hord,
      (fun i hi j hj hij => hx i (hIS i hi) j (hIS j hj) hij),
      tightPath_slope_false p S I hIS hne hord hpath⟩

end

end Erdos651
