import Mathlib
import ErdosProblems.Erdos957.Angle
import ErdosProblems.Erdos957.Hex
import ErdosProblems.Erdos957.Cases13

/-!
# Local-transfer bridges for Cases 1 and 3 of Erdős 957

This file packages the checked coordinate lemmas in `Erdos957Cases13` as actual local transfer
rows.  The hypotheses which belong to the still-unformalized cyclic-hull layer are deliberately
explicit: membership in the hull set, uniqueness of the extreme unit neighbour, and alignment of
two consecutive entries in the regular-hexagon enumeration.

All transfers are doubled.  Thus each source sends exactly two tokens.  A half-unit is one token
and a whole unit is two tokens.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957Case13Bridge

open Erdos957Cases13

abbrev Point := Erdos957Cases13.Point

/-- Unit neighbours in the pair-coordinate model used by Cases 1 and 3. -/
def unitNeighbors (A : Finset Point) (p : Point) : Finset Point :=
  A.filter fun q ↦ sqDist p q = 1

/-- The local shortest-distance degree. -/
def degree (A : Finset Point) (p : Point) : ℕ := (unitNeighbors A p).card

@[simp] lemma mem_unitNeighbors {A : Finset Point} {p q : Point} :
    q ∈ unitNeighbors A p ↔ q ∈ A ∧ sqDist p q = 1 := by
  simp [unitNeighbors]

/-- A recipient is at graph distance at most two from its source. -/
def WithinTwoUnitEdges (source recipient : Point) : Prop :=
  sqDist source recipient = 1 ∨
    ∃ middle, sqDist source middle = 1 ∧ sqDist middle recipient = 1

/-- The pair-coordinate plane is linearly identified with the complex plane. -/
def pointComplexEquiv : Point ≃ ℂ where
  toFun := toComplex
  invFun z := (z.re, z.im)
  left_inv p := rfl
  right_inv z := by apply Complex.ext <;> rfl

def pointComplexEmbedding : Point ↪ ℂ := pointComplexEquiv.toEmbedding

/-- Transport a finite pair-coordinate configuration to Mathlib's concrete complex plane. -/
def complexImage (A : Finset Point) : Finset ℂ := A.map pointComplexEmbedding

@[simp] lemma mem_complexImage {A : Finset Point} {p : Point} :
    toComplex p ∈ complexImage A ↔ p ∈ A := by
  constructor
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, hqp⟩
    have : q = p := pointComplexEquiv.injective hqp
    simpa [this] using hq
  · intro hp
    exact Finset.mem_map.mpr ⟨p, hp, rfl⟩

lemma complexImage_oneSeparated {A : Finset Point} (hA : IsOneSeparated (A : Set Point)) :
    Erdos957Angle.IsOneSeparated (complexImage A) := by
  intro x hx y hy hxy
  rcases Finset.mem_map.mp hx with ⟨p, hp, rfl⟩
  rcases Finset.mem_map.mp hy with ⟨q, hq, rfl⟩
  have hpq : p ≠ q := by
    intro h
    subst q
    exact hxy rfl
  change 1 ≤ dist (toComplex p) (toComplex q)
  rw [← one_le_sqDist_iff_one_le_dist]
  exact hA p hp q hq hpq

lemma mem_complex_unitNeighbors_iff {A : Finset Point} {p q : Point} :
    toComplex q ∈ Erdos957Angle.unitNeighbors (complexImage A) (toComplex p) ↔
      q ∈ unitNeighbors A p := by
  simp only [Erdos957Angle.unitNeighbors, Finset.mem_filter, mem_complexImage,
    mem_unitNeighbors]
  constructor
  · rintro ⟨hq, hd⟩
    exact ⟨hq, (sqDist_eq_one_iff_dist_eq_one p q).2 hd⟩
  · rintro ⟨hq, hd⟩
    exact ⟨hq, (sqDist_eq_one_iff_dist_eq_one p q).1 hd⟩

/-- The unit-neighbour finsets in pair and complex coordinates have the same cardinality. -/
lemma card_complex_unitNeighbors (A : Finset Point) (p : Point) :
    (Erdos957Angle.unitNeighbors (complexImage A) (toComplex p)).card = degree A p := by
  let f : unitNeighbors A p →
      Erdos957Angle.unitNeighbors (complexImage A) (toComplex p) :=
    fun q ↦ ⟨toComplex q, mem_complex_unitNeighbors_iff.2 q.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro q r h
      apply Subtype.ext
      exact pointComplexEquiv.injective (congrArg Subtype.val h)
    · intro z
      let q : Point := pointComplexEquiv.symm z
      have hq : q ∈ unitNeighbors A p := by
        apply mem_complex_unitNeighbors_iff.1
        have hz : toComplex q = (z : ℂ) := pointComplexEquiv.apply_symm_apply z
        rw [hz]
        exact z.property
      refine ⟨⟨q, hq⟩, ?_⟩
      apply Subtype.ext
      exact pointComplexEquiv.apply_symm_apply z
  rw [degree]
  simpa only [Fintype.card_coe] using (Fintype.card_congr (Equiv.ofBijective f hf)).symm

/-- The checked angular packing theorem, transported back to pair coordinates. -/
theorem degree_le_six {A : Finset Point} (hA : IsOneSeparated (A : Set Point)) (p : Point) :
    degree A p ≤ 6 := by
  rw [← card_complex_unitNeighbors A p]
  exact Erdos957Angle.card_unitNeighbors_le_six (complexImage_oneSeparated hA) (toComplex p)

/-- The checked open-half-plane theorem from `Erdos957Hex`, transported to pair coordinates.
This is the source-degree bound used at a strict hull vertex. -/
theorem degree_le_three_of_strict_support {A : Finset Point}
    (hA : IsOneSeparated (A : Set Point)) {p : Point}
    (hstrict : ∀ q ∈ A, q ≠ p → 0 < q.2 - p.2) :
    degree A p ≤ 3 := by
  have hsepHex : Erdos957Hex.IsOneSeparated (complexImage A) := by
    exact complexImage_oneSeparated hA
  have him : ∀ z ∈ Erdos957Hex.unitNeighbors (complexImage A) (toComplex p),
      0 < (z - toComplex p).im := by
    intro z hz
    have hzImage : z ∈ complexImage A := (Finset.mem_filter.mp hz).1
    rcases Finset.mem_map.mp hzImage with ⟨q, hqA, rfl⟩
    have hqp : q ≠ p := by
      intro heq
      subst q
      have hd := (Finset.mem_filter.mp hz).2
      change dist (toComplex p) (toComplex p) = 1 at hd
      simpa using hd
    change 0 < q.2 - p.2
    exact hstrict q hqA hqp
  have h := Erdos957Hex.card_unitNeighbors_le_three_of_sub_im_pos hsepHex him
  change (Erdos957Angle.unitNeighbors (complexImage A) (toComplex p)).card ≤ 3 at h
  rwa [card_complex_unitNeighbors] at h

/-! ## Explicit cyclic-neighbour data -/

/--
An angularly indexed regular hexagon around `center`.  The displayed subtraction identity is
one of the six identities produced by
`Erdos957Angle.exists_unitNeighborEquiv_with_regular_hexagon_identities`.
-/
structure OrderedHexagonAt (A : Finset Point) (center : Point) where
  neighbor : Fin 6 → Point
  neighbor_mem : ∀ i, neighbor i ∈ unitNeighbors A center
  neighbor_injective : Function.Injective neighbor
  neighbor_surjective : ∀ p ∈ unitNeighbors A center, ∃ i, neighbor i = p
  zero_sub_one_eq_five :
    ((neighbor 0).1 - center.1, (neighbor 0).2 - center.2) -
        ((neighbor 1).1 - center.1, (neighbor 1).2 - center.2) =
      ((neighbor 5).1 - center.1, (neighbor 5).2 - center.2)
  one_sub_two_eq_zero :
    ((neighbor 1).1 - center.1, (neighbor 1).2 - center.2) -
        ((neighbor 2).1 - center.1, (neighbor 2).2 - center.2) =
      ((neighbor 0).1 - center.1, (neighbor 0).2 - center.2)
  two_sub_three_eq_one :
    ((neighbor 2).1 - center.1, (neighbor 2).2 - center.2) -
        ((neighbor 3).1 - center.1, (neighbor 3).2 - center.2) =
      ((neighbor 1).1 - center.1, (neighbor 1).2 - center.2)
  three_sub_four_eq_two :
    ((neighbor 3).1 - center.1, (neighbor 3).2 - center.2) -
        ((neighbor 4).1 - center.1, (neighbor 4).2 - center.2) =
      ((neighbor 2).1 - center.1, (neighbor 2).2 - center.2)
  four_sub_five_eq_three :
    ((neighbor 4).1 - center.1, (neighbor 4).2 - center.2) -
        ((neighbor 5).1 - center.1, (neighbor 5).2 - center.2) =
      ((neighbor 3).1 - center.1, (neighbor 3).2 - center.2)
  five_sub_zero_eq_four :
    ((neighbor 5).1 - center.1, (neighbor 5).2 - center.2) -
        ((neighbor 0).1 - center.1, (neighbor 0).2 - center.2) =
      ((neighbor 4).1 - center.1, (neighbor 4).2 - center.2)

/-- The checked angular regular-hexagon theorem supplies an ordered hexagon whenever the local
degree is six. -/
theorem exists_orderedHexagonAt_of_degree_eq_six {A : Finset Point}
    (hA : IsOneSeparated (A : Set Point)) {center : Point}
    (hdegree : degree A center = 6) :
    Nonempty (OrderedHexagonAt A center) := by
  have hdegreeComplex :
      (Erdos957Angle.unitNeighbors (complexImage A) (toComplex center)).card = 6 := by
    rw [card_complex_unitNeighbors, hdegree]
  rcases Erdos957Angle.exists_unitNeighborEquiv_with_regular_hexagon_identities
      (complexImage_oneSeparated hA) (toComplex center) hdegreeComplex with
    ⟨e, _hbin, hzero, hone, htwo, hthree, hfour, hfive⟩
  let neighbor : Fin 6 → Point := fun i ↦ pointComplexEquiv.symm (e i : ℂ)
  refine ⟨{
    neighbor := neighbor
    neighbor_mem := ?_
    neighbor_injective := ?_
    neighbor_surjective := ?_
    zero_sub_one_eq_five := ?_
    one_sub_two_eq_zero := ?_
    two_sub_three_eq_one := ?_
    three_sub_four_eq_two := ?_
    four_sub_five_eq_three := ?_
    five_sub_zero_eq_four := ?_ }⟩
  · intro i
    apply mem_complex_unitNeighbors_iff.1
    have hi : toComplex (neighbor i) = (e i : ℂ) := pointComplexEquiv.apply_symm_apply (e i)
    rw [hi]
    exact (e i).property
  · intro i j hij
    apply e.injective
    apply Subtype.ext
    have h := congrArg pointComplexEquiv hij
    simpa only [neighbor, Equiv.apply_symm_apply] using h
  · intro p hp
    let q : Erdos957Angle.unitNeighbors (complexImage A) (toComplex center) :=
      ⟨toComplex p, mem_complex_unitNeighbors_iff.mpr hp⟩
    refine ⟨e.symm q, ?_⟩
    apply pointComplexEquiv.injective
    have heq := congrArg Subtype.val (e.apply_symm_apply q)
    change (e (e.symm q) : ℂ) = toComplex p
    simpa only [q] using heq
  · apply Prod.ext
    · have h := congrArg Complex.re hzero
      change ((e 0 : ℂ).re - center.1) - ((e 1 : ℂ).re - center.1) =
        (e 5 : ℂ).re - center.1
      simpa only [Complex.sub_re, toComplex] using h
    · have h := congrArg Complex.im hzero
      change ((e 0 : ℂ).im - center.2) - ((e 1 : ℂ).im - center.2) =
        (e 5 : ℂ).im - center.2
      simpa only [Complex.sub_im, toComplex] using h
  · apply Prod.ext
    · have h := congrArg Complex.re hone
      change ((e 1 : ℂ).re - center.1) - ((e 2 : ℂ).re - center.1) =
        (e 0 : ℂ).re - center.1
      simpa only [Complex.sub_re, toComplex] using h
    · have h := congrArg Complex.im hone
      change ((e 1 : ℂ).im - center.2) - ((e 2 : ℂ).im - center.2) =
        (e 0 : ℂ).im - center.2
      simpa only [Complex.sub_im, toComplex] using h
  · apply Prod.ext
    · have h := congrArg Complex.re htwo
      change ((e 2 : ℂ).re - center.1) - ((e 3 : ℂ).re - center.1) =
        (e 1 : ℂ).re - center.1
      simpa only [Complex.sub_re, toComplex] using h
    · have h := congrArg Complex.im htwo
      change ((e 2 : ℂ).im - center.2) - ((e 3 : ℂ).im - center.2) =
        (e 1 : ℂ).im - center.2
      simpa only [Complex.sub_im, toComplex] using h
  · apply Prod.ext
    · have h := congrArg Complex.re hthree
      change ((e 3 : ℂ).re - center.1) - ((e 4 : ℂ).re - center.1) =
        (e 2 : ℂ).re - center.1
      simpa only [Complex.sub_re, toComplex] using h
    · have h := congrArg Complex.im hthree
      change ((e 3 : ℂ).im - center.2) - ((e 4 : ℂ).im - center.2) =
        (e 2 : ℂ).im - center.2
      simpa only [Complex.sub_im, toComplex] using h
  · apply Prod.ext
    · have h := congrArg Complex.re hfour
      change ((e 4 : ℂ).re - center.1) - ((e 5 : ℂ).re - center.1) =
        (e 3 : ℂ).re - center.1
      simpa only [Complex.sub_re, toComplex] using h
    · have h := congrArg Complex.im hfour
      change ((e 4 : ℂ).im - center.2) - ((e 5 : ℂ).im - center.2) =
        (e 3 : ℂ).im - center.2
      simpa only [Complex.sub_im, toComplex] using h
  · apply Prod.ext
    · have h := congrArg Complex.re hfive
      change ((e 5 : ℂ).re - center.1) - ((e 0 : ℂ).re - center.1) =
        (e 4 : ℂ).re - center.1
      simpa only [Complex.sub_re, toComplex] using h
    · have h := congrArg Complex.im hfive
      change ((e 5 : ℂ).im - center.2) - ((e 0 : ℂ).im - center.2) =
        (e 4 : ℂ).im - center.2
      simpa only [Complex.sub_im, toComplex] using h

/-- The regular-hexagon identity determines the neighbour after a specified oriented pair. -/
lemma OrderedHexagonAt.completion_eq {A : Finset Point} {center x y : Point}
    (hex : OrderedHexagonAt A center) (hx : hex.neighbor 0 = x)
    (hy : hex.neighbor 1 = y) :
    hex.neighbor 5 = (center.1 + x.1 - y.1, center.2 + x.2 - y.2) := by
  have h := hex.zero_sub_one_eq_five
  rw [hx, hy] at h
  apply Prod.ext
  · have := congrArg Prod.fst h
    dsimp at this ⊢
    linarith
  · have := congrArg Prod.snd h
    dsimp at this ⊢
    linarith

/-- The aligned regular-hexagon continuation is a genuine member of the configuration. -/
lemma OrderedHexagonAt.completion_mem {A : Finset Point} {center x y : Point}
    (hex : OrderedHexagonAt A center) (hx : hex.neighbor 0 = x)
    (hy : hex.neighbor 1 = y) :
    (center.1 + x.1 - y.1, center.2 + x.2 - y.2) ∈ A := by
  rw [← hex.completion_eq hx hy]
  exact (mem_unitNeighbors.mp (hex.neighbor_mem 5)).1

/-! ## A reusable local-transfer record -/

/-- A complete local row of the doubled-token transfer. -/
structure LocalTransfer (A hull : Finset Point) (source : Point) where
  source_mem : source ∈ A
  source_mem_hull : source ∈ hull
  source_degree_three : degree A source = 3
  recipients : Finset Point
  tokens : Point → ℕ
  tokens_eq_zero : ∀ p, p ∉ recipients → tokens p = 0
  tokens_pos : ∀ p ∈ recipients, 0 < tokens p
  total_tokens : ∑ p ∈ recipients, tokens p = 2
  recipient_mem : ∀ p ∈ recipients, p ∈ A
  recipient_not_hull : ∀ p ∈ recipients, p ∉ hull
  recipient_rectangle : ∀ p ∈ recipients, InSourceRectangle p
  recipient_within_two : ∀ p ∈ recipients, WithinTwoUnitEdges source p
  recipient_capacity : ∀ p ∈ recipients, 2 * degree A p + tokens p ≤ 12

/-- Extending a local row by zero gives a transfer function with row sum exactly two. -/
lemma LocalTransfer.sum_tokens {A hull : Finset Point} {source : Point}
    (T : LocalTransfer A hull source) :
    ∑ p ∈ A, T.tokens p = 2 := by
  rw [← T.total_tokens]
  symm
  apply Finset.sum_subset
  · intro p hp
    exact T.recipient_mem p hp
  · intro p hpA hpNot
    exact T.tokens_eq_zero p hpNot

/-! ## Case 1 -/

def case1Recipients (v : Point) : Finset Point := {case1Left v, case1Right v}

def case1Tokens (v p : Point) : ℕ := if p ∈ case1Recipients v then 1 else 0

lemma case1Left_ne_case1Right {v : Point} (hvunit : sqDist origin v = 1) :
    case1Left v ≠ case1Right v := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [case1Left, case1Right] at hx hy
  have hs := sqrtThree_pos
  simp only [sqDist, origin] at hvunit
  have hvx : v.1 = 0 := by nlinarith
  have hvy : v.2 = 0 := by nlinarith
  nlinarith

lemma case1_forcedLeft_eq_completion (v : Point) :
    case1ForcedAboveLeft v =
      ((case1Left v).1 + origin.1 - v.1, (case1Left v).2 + origin.2 - v.2) := by
  apply Prod.ext <;> simp [case1ForcedAboveLeft, origin]

lemma case1_forcedRight_eq_completion (v : Point) :
    case1ForcedAboveRight v =
      ((case1Right v).1 + origin.1 - v.1, (case1Right v).2 + origin.2 - v.2) := by
  apply Prod.ext <;> simp [case1ForcedAboveRight, origin]

/-- A degree-six left recipient contradicts the supporting half-plane once its two known
neighbours are aligned consecutively in the angular hexagon enumeration. -/
lemma case1_left_degree_le_five {A : Finset Point} {v : Point}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hvcone : InOpenMiddleCone v)
    (halign : degree A (case1Left v) = 6 →
      ∃ hex : OrderedHexagonAt A (case1Left v),
        hex.neighbor 0 = origin ∧ hex.neighbor 1 = v) :
    degree A (case1Left v) ≤ 5 := by
  have hle := degree_le_six hAsep (case1Left v)
  by_contra hnot
  have hdeg : degree A (case1Left v) = 6 := by omega
  obtain ⟨hex, hzero, hone⟩ := halign hdeg
  have hmem := hex.completion_mem hzero hone
  rw [← case1_forcedLeft_eq_completion] at hmem
  exact case1_forcedAboveLeft_not_mem hsupport hvcone hmem

/-- Right-hand counterpart of `case1_left_degree_le_five`. -/
lemma case1_right_degree_le_five {A : Finset Point} {v : Point}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hvcone : InOpenMiddleCone v)
    (halign : degree A (case1Right v) = 6 →
      ∃ hex : OrderedHexagonAt A (case1Right v),
        hex.neighbor 0 = origin ∧ hex.neighbor 1 = v) :
    degree A (case1Right v) ≤ 5 := by
  have hle := degree_le_six hAsep (case1Right v)
  by_contra hnot
  have hdeg : degree A (case1Right v) = 6 := by omega
  obtain ⟨hex, hzero, hone⟩ := halign hdeg
  have hmem := hex.completion_mem hzero hone
  rw [← case1_forcedRight_eq_completion] at hmem
  exact case1_forcedAboveRight_not_mem hsupport hvcone hmem

/--
Complete Case 1 transfer.  `honeExtreme` is the explicit one-extreme-neighbour hypothesis at
the middle vertex.  It turns the two common neighbours into interior recipients.
-/
theorem case1_localTransfer
    {A hull : Finset Point} {v : Point}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hsourceA : origin ∈ A) (hsourceHull : origin ∈ hull)
    (hsourceDegree : degree A origin = 3) (_hmiddleA : v ∈ A)
    (hvunit : sqDist origin v = 1) (hvcone : InOpenMiddleCone v)
    (hleftA : case1Left v ∈ A) (hrightA : case1Right v ∈ A)
    (honeExtreme : ∀ p ∈ hull, sqDist v p = 1 → p = origin)
    (hleftAlign : degree A (case1Left v) = 6 →
      ∃ hex : OrderedHexagonAt A (case1Left v),
        hex.neighbor 0 = origin ∧ hex.neighbor 1 = v)
    (hrightAlign : degree A (case1Right v) = 6 →
      ∃ hex : OrderedHexagonAt A (case1Right v),
        hex.neighbor 0 = origin ∧ hex.neighbor 1 = v) :
    Nonempty (LocalTransfer A hull origin) := by
  have hne := case1Left_ne_case1Right hvunit
  have hleftDeg := case1_left_degree_le_five hAsep hsupport hvcone hleftAlign
  have hrightDeg := case1_right_degree_le_five hAsep hsupport hvcone hrightAlign
  have hrect := case1_recipients_in_sourceRectangle hvunit hvcone
  refine ⟨{
    source_mem := hsourceA
    source_mem_hull := hsourceHull
    source_degree_three := hsourceDegree
    recipients := case1Recipients v
    tokens := case1Tokens v
    tokens_eq_zero := ?_
    tokens_pos := ?_
    total_tokens := ?_
    recipient_mem := ?_
    recipient_not_hull := ?_
    recipient_rectangle := ?_
    recipient_within_two := ?_
    recipient_capacity := ?_ }⟩
  · intro p hp
    simp [case1Tokens, hp]
  · intro p hp
    simp [case1Tokens, hp]
  · rw [show case1Recipients v = insert (case1Left v) {case1Right v} from rfl,
      Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
    simp [case1Tokens, case1Recipients]
  · intro p hp
    simp only [case1Recipients, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hleftA
    · exact hrightA
  · intro p hp hpHull
    simp only [case1Recipients, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · have heq := honeExtreme _ hpHull (case1Left_common_unit hvunit).2
      have hdist := (case1Left_common_unit hvunit).1
      rw [heq, sqDist_self] at hdist
      norm_num at hdist
    · have heq := honeExtreme _ hpHull (case1Right_common_unit hvunit).2
      have hdist := (case1Right_common_unit hvunit).1
      rw [heq, sqDist_self] at hdist
      norm_num at hdist
  · intro p hp
    simp only [case1Recipients, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact hrect.1
    · exact hrect.2
  · intro p hp
    simp only [case1Recipients, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Or.inl (case1Left_common_unit hvunit).1
    · exact Or.inl (case1Right_common_unit hvunit).1
  · intro p hp
    simp only [case1Recipients, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · simp [case1Tokens, case1Recipients]
      omega
    · simp [case1Tokens, case1Recipients]
      omega

/-! ## Case 3 -/

def case3Recipients (secondary : Point) (middleDegree : ℕ) : Finset Point :=
  if middleDegree ≤ 4 then {verticalDown} else {verticalDown, secondary}

def case3Tokens (secondary : Point) (middleDegree : ℕ) (p : Point) : ℕ :=
  if middleDegree ≤ 4 then
    if p = verticalDown then 2 else 0
  else if p = verticalDown ∨ p = secondary then 1 else 0

lemma verticalDown_ne_of_sqDist_origin_eq_one {q : Point}
    (hq : sqDist origin q = 1) (hqv : sqDist verticalDown q = 1) :
    verticalDown ≠ q := by
  intro h
  subst q
  simpa using hqv

lemma case3_common_neighbor_below {t : Point}
    (htU : sqDist origin t = 1) (htV : sqDist verticalDown t = 1) :
    t.2 = -(1 / 2 : ℝ) := by
  simp only [sqDist, origin] at htU
  simp only [sqDist, verticalDown] at htV
  nlinarith

lemma case3_forcedAbove_eq_completion (t : Point) :
    case3ForcedAbove t =
      ((t.1 + origin.1 - verticalDown.1), (t.2 + origin.2 - verticalDown.2)) := by
  apply Prod.ext <;> simp [case3ForcedAbove, verticalDown, origin]

/-- A complete regular hexagon at the secondary Case 3 recipient would cross the source's
supporting line. -/
lemma case3_secondary_degree_le_five {A : Finset Point} {t : Point}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (htU : sqDist origin t = 1) (htV : sqDist verticalDown t = 1)
    (halign : degree A t = 6 → ∃ hex : OrderedHexagonAt A t,
      hex.neighbor 0 = origin ∧ hex.neighbor 1 = verticalDown) :
    degree A t ≤ 5 := by
  have hle := degree_le_six hAsep t
  by_contra hnot
  have hdeg : degree A t = 6 := by omega
  obtain ⟨hex, hzero, hone⟩ := halign hdeg
  have hmem := hex.completion_mem hzero hone
  rw [← case3_forcedAbove_eq_completion] at hmem
  exact case3_forcedAbove_not_mem hsupport htU htV hmem

/-- The common core of both reflected Case 3 pictures, after the selected neighbour has been
identified as a common unit neighbour of the source and the middle recipient. -/
theorem case3_localTransfer_of_common_neighbor
    {A hull : Finset Point} {t : Point} {middleDegree : ℕ}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hsourceA : origin ∈ A) (hsourceHull : origin ∈ hull)
    (hsourceDegree : degree A origin = 3)
    (hmiddleA : verticalDown ∈ A) (htA : t ∈ A)
    (hmiddleDegree : middleDegree = degree A verticalDown)
    (hmiddleLeFive : middleDegree ≤ 5)
    (hmiddleInterior : verticalDown ∉ hull)
    (honeExtreme : ∀ p ∈ hull, sqDist verticalDown p = 1 → p = origin)
    (htU : sqDist origin t = 1)
    (htUnit : sqDist verticalDown t = 1)
    (htAlign : degree A t = 6 → ∃ hex : OrderedHexagonAt A t,
      hex.neighbor 0 = origin ∧ hex.neighbor 1 = verticalDown) :
    Nonempty (LocalTransfer A hull origin) := by
  have htBelowEq : t.2 = -(1 / 2 : ℝ) := case3_common_neighbor_below htU htUnit
  have htBelow : t.2 ≤ 0 := by linarith
  have htRect := unit_point_in_sourceRectangle htU htBelow
  have htDeg := case3_secondary_degree_le_five hAsep hsupport htU htUnit htAlign
  have hne : verticalDown ≠ t := verticalDown_ne_of_sqDist_origin_eq_one htU htUnit
  refine ⟨{
    source_mem := hsourceA
    source_mem_hull := hsourceHull
    source_degree_three := hsourceDegree
    recipients := case3Recipients t middleDegree
    tokens := case3Tokens t middleDegree
    tokens_eq_zero := ?_
    tokens_pos := ?_
    total_tokens := ?_
    recipient_mem := ?_
    recipient_not_hull := ?_
    recipient_rectangle := ?_
    recipient_within_two := ?_
    recipient_capacity := ?_ }⟩
  · intro p hp
    by_cases hlow : middleDegree ≤ 4
    · simp [case3Recipients, case3Tokens, hlow] at hp ⊢
      exact fun h ↦ hp (by simpa [h])
    · simp [case3Recipients, case3Tokens, hlow] at hp ⊢
      exact hp
  · intro p hp
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = verticalDown := by simpa [case3Recipients, hlow] using hp
      subst p
      simp [case3Tokens, hlow]
    · have hpEq : p = verticalDown ∨ p = t := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl <;> simp [case3Tokens, hlow, hne]
  · by_cases hlow : middleDegree ≤ 4
    · simp [case3Recipients, case3Tokens, hlow]
    · rw [show case3Recipients t middleDegree = insert verticalDown {t} by
          simp [case3Recipients, hlow],
        Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
      simp [case3Tokens, hlow, hne]
  · intro p hp
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = verticalDown := by simpa [case3Recipients, hlow] using hp
      simpa [hpEq] using hmiddleA
    · have hpEq : p = verticalDown ∨ p = t := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl
      · exact hmiddleA
      · exact htA
  · intro p hp hpHull
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = verticalDown := by simpa [case3Recipients, hlow] using hp
      subst p
      exact hmiddleInterior hpHull
    · have hpEq : p = verticalDown ∨ p = t := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl
      · exact hmiddleInterior hpHull
      · have heq := honeExtreme _ hpHull htUnit
        rw [heq, sqDist_self] at htU
        norm_num at htU
  · intro p hp
    have hvRect : InSourceRectangle verticalDown :=
      unit_point_in_sourceRectangle (by norm_num [sqDist, origin, verticalDown])
        (by norm_num [verticalDown])
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = verticalDown := by simpa [case3Recipients, hlow] using hp
      simpa [hpEq] using hvRect
    · have hpEq : p = verticalDown ∨ p = t := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl
      · exact hvRect
      · exact htRect
  · intro p hp
    have hvWithin : WithinTwoUnitEdges origin verticalDown :=
      Or.inl (by norm_num [sqDist, origin, verticalDown])
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = verticalDown := by simpa [case3Recipients, hlow] using hp
      simpa [hpEq] using hvWithin
    · have hpEq : p = verticalDown ∨ p = t := by
        simpa [case3Recipients, hlow] using hp
      rcases hpEq with rfl | rfl
      · exact hvWithin
      · exact Or.inl htU
  · intro p hp
    simp only [case3Recipients] at hp
    by_cases hlow : middleDegree ≤ 4
    · have hpEq : p = verticalDown := by simpa [hlow] using hp
      subst p
      simp [case3Tokens, hlow]
      rw [← hmiddleDegree]
      omega
    · simp only [hlow, if_false, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · simp [case3Tokens, hlow]
        rw [← hmiddleDegree]
        omega
      · simp [case3Tokens, hlow]
        omega

/--
Complete right-hand Case 3 transfer.  The checked arc-closeness lemma identifies the selected
high neighbour `t` with the existing right source neighbour `q`; the common-neighbour theorem
then constructs the exact transfer row.
-/
theorem case3_right_localTransfer
    {A hull : Finset Point} {q t : Point} {middleDegree : ℕ}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hsourceA : origin ∈ A) (hsourceHull : origin ∈ hull)
    (hsourceDegree : degree A origin = 3)
    (hmiddleA : verticalDown ∈ A) (hqA : q ∈ A) (htA : t ∈ A)
    (hmiddleDegree : middleDegree = degree A verticalDown)
    (hmiddleLeFive : middleDegree ≤ 5)
    (hmiddleInterior : verticalDown ∉ hull)
    (honeExtreme : ∀ p ∈ hull, sqDist verticalDown p = 1 → p = origin)
    (hqUnit : sqDist origin q = 1)
    (hqAwayFromV : 1 ≤ sqDist verticalDown q)
    (hqBelow : q.2 < 0) (hqx : 0 ≤ q.1)
    (htUnit : sqDist verticalDown t = 1)
    (htAwayFromU : 1 ≤ sqDist origin t)
    (htHigh : verticalDown.2 ≤ t.2) (htx : 0 ≤ t.1)
    (htAlign : degree A t = 6 → ∃ hex : OrderedHexagonAt A t,
      hex.neighbor 0 = origin ∧ hex.neighbor 1 = verticalDown) :
    Nonempty (LocalTransfer A hull origin) := by
  have hqt := case3_right_candidate_eq_existing_of_oneSeparated hAsep hqA htA
    hqUnit hqAwayFromV hqBelow hqx htUnit htAwayFromU htHigh htx
  apply case3_localTransfer_of_common_neighbor hAsep hsupport hsourceA hsourceHull
    hsourceDegree hmiddleA htA
    hmiddleDegree hmiddleLeFive hmiddleInterior honeExtreme
  · exact hqt ▸ hqUnit
  · exact htUnit
  · exact htAlign

/-- Reflected left-hand Case 3 transfer. -/
theorem case3_left_localTransfer
    {A hull : Finset Point} {q t : Point} {middleDegree : ℕ}
    (hAsep : IsOneSeparated (A : Set Point))
    (hsupport : ∀ p ∈ A, p.2 ≤ 0)
    (hsourceA : origin ∈ A) (hsourceHull : origin ∈ hull)
    (hsourceDegree : degree A origin = 3)
    (hmiddleA : verticalDown ∈ A) (hqA : q ∈ A) (htA : t ∈ A)
    (hmiddleDegree : middleDegree = degree A verticalDown)
    (hmiddleLeFive : middleDegree ≤ 5)
    (hmiddleInterior : verticalDown ∉ hull)
    (honeExtreme : ∀ p ∈ hull, sqDist verticalDown p = 1 → p = origin)
    (hqUnit : sqDist origin q = 1)
    (hqAwayFromV : 1 ≤ sqDist verticalDown q)
    (hqBelow : q.2 < 0) (hqx : q.1 ≤ 0)
    (htUnit : sqDist verticalDown t = 1)
    (htAwayFromU : 1 ≤ sqDist origin t)
    (htHigh : verticalDown.2 ≤ t.2) (htx : t.1 ≤ 0)
    (htAlign : degree A t = 6 → ∃ hex : OrderedHexagonAt A t,
      hex.neighbor 0 = origin ∧ hex.neighbor 1 = verticalDown) :
    Nonempty (LocalTransfer A hull origin) := by
  have hsep := eq_or_one_le_sqDist_of_oneSeparated hAsep hqA htA
  have hqt := case3_left_candidate_eq_existing hqUnit hqAwayFromV hqBelow hqx
    htUnit htAwayFromU htHigh htx hsep
  apply case3_localTransfer_of_common_neighbor hAsep hsupport hsourceA hsourceHull
    hsourceDegree hmiddleA htA
    hmiddleDegree hmiddleLeFive hmiddleInterior honeExtreme
  · exact hqt ▸ hqUnit
  · exact htUnit
  · exact htAlign

end Erdos957Case13Bridge
