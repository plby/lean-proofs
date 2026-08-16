import Mathlib

open Function Set

namespace Erdos965

/-! ## Hamel indices and their binary rational-cut codes -/

/-- The index type of Mathlib's chosen Hamel basis of `ℝ` over `ℚ`.
It is definitionally a subtype of `ℝ`, so it inherits the ordinary real order. -/
abbrev HamelIndex := Module.Basis.ofVectorSpaceIndex ℚ ℝ

/-- Mathlib's chosen Hamel basis of `ℝ` over `ℚ`. -/
noncomputable abbrev hamelBasis : Module.Basis HamelIndex ℚ ℝ :=
  Module.Basis.ofVectorSpace ℚ ℝ

/-- A fixed enumeration of the rationals. -/
noncomputable def ratEnum : ℕ ≃ ℚ := (Denumerable.eqv ℚ).symm

@[simp] theorem ratEnum_apply_eq (q : ℚ) :
    ratEnum ((Denumerable.eqv ℚ) q) = q := by
  simp [ratEnum]

/-- The rational-cut code of a Hamel index.  The `n`th bit records whether
the `n`th rational in the fixed enumeration lies strictly below the index. -/
noncomputable def binaryCode (x : HamelIndex) (n : ℕ) : Bool :=
  decide (((ratEnum n : ℚ) : ℝ) < (x : ℝ))

theorem binaryCode_mono {x y : HamelIndex} (hxy : x ≤ y) (n : ℕ) :
    binaryCode x n ≤ binaryCode y n := by
  by_cases hx : (((ratEnum n : ℚ) : ℝ) < (x : ℝ))
  · have hy : (((ratEnum n : ℚ) : ℝ) < (y : ℝ)) := hx.trans_le hxy
    simp [binaryCode, hx, hy]
  · simp [binaryCode, hx]

/-- A `false`/`true` separation at any coordinate forces the corresponding
ordinary order on the underlying reals. -/
theorem lt_of_binaryCode_eq_false_true {x y : HamelIndex} {n : ℕ}
    (hx : binaryCode x n = false) (hy : binaryCode y n = true) : x < y := by
  have hxq : ¬ (((ratEnum n : ℚ) : ℝ) < (x : ℝ)) := by
    apply of_decide_eq_false
    exact hx
  have hqy : (((ratEnum n : ℚ) : ℝ) < (y : ℝ)) := by
    apply of_decide_eq_true
    exact hy
  exact (le_of_not_gt hxq).trans_lt hqy

/-- Rational cuts separate distinct reals, hence also distinct Hamel indices. -/
theorem binaryCode_injective : Injective binaryCode := by
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨q, hxq, hqy⟩ : ∃ q : ℚ, (x : ℝ) < q ∧ (q : ℝ) < y :=
      exists_rat_btwn hlt
    have hbit := congrFun hxy ((Denumerable.eqv ℚ) q)
    simp [binaryCode, ratEnum, hxq.not_gt, hqy] at hbit
  · obtain ⟨q, hyq, hqx⟩ : ∃ q : ℚ, (y : ℝ) < q ∧ (q : ℝ) < x :=
      exists_rat_btwn hgt
    have hbit := congrFun hxy ((Denumerable.eqv ℚ) q)
    simp [binaryCode, ratEnum, hqx, hyq.not_gt] at hbit

/-- The first position at which the rational-cut codes differ. -/
noncomputable def firstDiff (x y : HamelIndex) : ℕ :=
  PiNat.firstDiff (binaryCode x) (binaryCode y)

theorem binaryCode_ne {x y : HamelIndex} (hxy : x ≠ y) :
    binaryCode x ≠ binaryCode y :=
  binaryCode_injective.ne hxy

theorem binaryCode_apply_firstDiff_ne {x y : HamelIndex} (hxy : x ≠ y) :
    binaryCode x (firstDiff x y) ≠ binaryCode y (firstDiff x y) := by
  exact PiNat.apply_firstDiff_ne (binaryCode_ne hxy)

theorem binaryCode_apply_eq_of_lt_firstDiff {x y : HamelIndex} {n : ℕ}
    (hn : n < firstDiff x y) : binaryCode x n = binaryCode y n := by
  exact PiNat.apply_eq_of_lt_firstDiff hn

theorem firstDiff_comm (x y : HamelIndex) : firstDiff x y = firstDiff y x := by
  exact PiNat.firstDiff_comm _ _

/-- At the first difference, the rational-cut code has the same orientation
as the ordinary order on the underlying reals. -/
theorem binaryCode_firstDiff_of_lt {x y : HamelIndex} (hxy : x < y) :
    binaryCode x (firstDiff x y) = false ∧
      binaryCode y (firstDiff x y) = true := by
  have hne := binaryCode_apply_firstDiff_ne hxy.ne
  have hle := binaryCode_mono hxy.le (firstDiff x y)
  revert hne hle
  generalize binaryCode x (firstDiff x y) = a
  generalize binaryCode y (firstDiff x y) = b
  cases a <;> cases b <;> decide

/-- If two different points lie above the same lower point and split from it
at the same level, then they split from each other strictly later. -/
theorem firstDiff_lt_firstDiff_of_common_lower {x y z : HamelIndex}
    (hxy : x < y) (hxz : x < z) (hyz : y ≠ z)
    (hEq : firstDiff x y = firstDiff x z) :
    firstDiff x y < firstDiff y z := by
  have hyzCode : binaryCode y ≠ binaryCode z := binaryCode_ne hyz
  have hle := PiNat.min_firstDiff_le (binaryCode y) (binaryCode x) (binaryCode z) hyzCode
  change min (firstDiff y x) (firstDiff x z) ≤ firstDiff y z at hle
  rw [firstDiff_comm y x, ← hEq, min_self] at hle
  refine hle.lt_of_ne ?_
  intro heq
  have hdiff := PiNat.apply_firstDiff_ne hyzCode
  have hybit := (binaryCode_firstDiff_of_lt hxy).2
  have hzbit := (binaryCode_firstDiff_of_lt hxz).2
  apply hdiff
  change binaryCode y (firstDiff y z) = binaryCode z (firstDiff y z)
  rw [← heq, hybit, hEq, hzbit]

/-! ## The canonical critical pair -/

/-- An oriented pair `(x,y)` is critical for `s` when it belongs to `s`,
maximizes the first-difference level, and its lower endpoint is least among
all ordered pairs attaining that maximum. -/
def IsCriticalPair (s : Finset HamelIndex) (x y : HamelIndex) : Prop :=
  x ∈ s ∧ y ∈ s ∧ x < y ∧
    (∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b →
      firstDiff a b ≤ firstDiff x y) ∧
    (∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b →
      firstDiff a b = firstDiff x y → x ≤ a)

theorem IsCriticalPair.fst_mem {s : Finset HamelIndex} {x y : HamelIndex}
    (h : IsCriticalPair s x y) : x ∈ s := h.1

theorem IsCriticalPair.snd_mem {s : Finset HamelIndex} {x y : HamelIndex}
    (h : IsCriticalPair s x y) : y ∈ s := h.2.1

theorem IsCriticalPair.lt {s : Finset HamelIndex} {x y : HamelIndex}
    (h : IsCriticalPair s x y) : x < y := h.2.2.1

theorem IsCriticalPair.maximal {s : Finset HamelIndex} {x y : HamelIndex}
    (h : IsCriticalPair s x y) {a b : HamelIndex}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    firstDiff a b ≤ firstDiff x y :=
  h.2.2.2.1 ha hb hab

theorem IsCriticalPair.le_lower {s : Finset HamelIndex} {x y : HamelIndex}
    (h : IsCriticalPair s x y) {a b : HamelIndex}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a < b)
    (hdiff : firstDiff a b = firstDiff x y) : x ≤ a :=
  h.2.2.2.2 ha hb hab hdiff

/-- The finite set of all ordinarily oriented pairs from `s`. -/
private noncomputable def orientedPairs (s : Finset HamelIndex) :
    Finset (HamelIndex × HamelIndex) :=
  (s ×ˢ s).filter fun p ↦ p.1 < p.2

private theorem mem_orientedPairs {s : Finset HamelIndex} {p : HamelIndex × HamelIndex} :
    p ∈ orientedPairs s ↔ p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 := by
  rw [orientedPairs, Finset.mem_filter, Finset.mem_product]
  tauto

private theorem orientedPairs_nonempty {s : Finset HamelIndex} (hs : 2 ≤ s.card) :
    (orientedPairs s).Nonempty := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · exact ⟨(a, b), mem_orientedPairs.2 ⟨ha, hb, hablt⟩⟩
  · exact ⟨(b, a), mem_orientedPairs.2 ⟨hb, ha, hbalt⟩⟩

/-- Every finite set with at least two members has a critical pair. -/
theorem exists_isCriticalPair (s : Finset HamelIndex) (hs : 2 ≤ s.card) :
    ∃ x y, IsCriticalPair s x y := by
  classical
  let P := orientedPairs s
  have hP : P.Nonempty := orientedPairs_nonempty hs
  let D : Finset ℕ := P.image fun p ↦ firstDiff p.1 p.2
  have hD : D.Nonempty := hP.image _
  let N : ℕ := D.max' hD
  let Q : Finset (HamelIndex × HamelIndex) :=
    P.filter fun p ↦ firstDiff p.1 p.2 = N
  have hQ : Q.Nonempty := by
    have hNmem : N ∈ D := D.max'_mem hD
    obtain ⟨p, hpP, hpN⟩ := Finset.mem_image.mp hNmem
    exact ⟨p, Finset.mem_filter.2 ⟨hpP, hpN⟩⟩
  let L : Finset HamelIndex := Q.image Prod.fst
  have hL : L.Nonempty := hQ.image _
  let x : HamelIndex := L.min' hL
  have hxL : x ∈ L := L.min'_mem hL
  obtain ⟨⟨a, b⟩, hpQ, hax⟩ := Finset.mem_image.mp hxL
  simp only at hax
  subst a
  have hpP : (x, b) ∈ P := (Finset.mem_filter.mp hpQ).1
  have hpN : firstDiff x b = N := (Finset.mem_filter.mp hpQ).2
  refine ⟨x, b, ?_⟩
  have hxy := mem_orientedPairs.mp hpP
  refine ⟨hxy.1, hxy.2.1, hxy.2.2, ?_, ?_⟩
  · intro a ha b hb hab
    rcases lt_or_gt_of_ne hab with hablt | hbalt
    · have hpab : (a, b) ∈ P := mem_orientedPairs.2 ⟨ha, hb, hablt⟩
      have hmem : firstDiff a b ∈ D := Finset.mem_image.2 ⟨(a, b), hpab, rfl⟩
      simpa only [hpN] using D.le_max' _ hmem
    · have hpba : (b, a) ∈ P := mem_orientedPairs.2 ⟨hb, ha, hbalt⟩
      have hmem : firstDiff b a ∈ D := Finset.mem_image.2 ⟨(b, a), hpba, rfl⟩
      rw [firstDiff_comm]
      simpa only [hpN] using D.le_max' _ hmem
  · intro a ha b hb hab hdiff
    have hpab : (a, b) ∈ P := mem_orientedPairs.2 ⟨ha, hb, hab⟩
    have habN : firstDiff a b = N := hdiff.trans hpN
    have hpabQ : (a, b) ∈ Q := Finset.mem_filter.2 ⟨hpab, habN⟩
    have haL : a ∈ L := Finset.mem_image.2 ⟨(a, b), hpabQ, rfl⟩
    exact L.min'_le _ haL

/-- Critical pairs are unique.  The key point is that two distinct upper
endpoints above the same lower endpoint would have a later first difference. -/
theorem isCriticalPair_unique {s : Finset HamelIndex} {x y x' y' : HamelIndex}
    (h : IsCriticalPair s x y) (h' : IsCriticalPair s x' y') :
    x = x' ∧ y = y' := by
  have hdiff_le := h.maximal h'.fst_mem h'.snd_mem h'.lt.ne
  have hdiff_ge := h'.maximal h.fst_mem h.snd_mem h.lt.ne
  have hdiff : firstDiff x y = firstDiff x' y' := le_antisymm hdiff_ge hdiff_le
  have hxx' : x ≤ x' := h.le_lower h'.fst_mem h'.snd_mem h'.lt hdiff.symm
  have hx'x : x' ≤ x := h'.le_lower h.fst_mem h.snd_mem h.lt hdiff
  have hx : x = x' := le_antisymm hxx' hx'x
  subst x'
  refine ⟨rfl, ?_⟩
  by_contra hyy'
  have hlate : firstDiff x y < firstDiff y y' :=
    firstDiff_lt_firstDiff_of_common_lower h.lt h'.lt hyy' hdiff
  exact (not_le_of_gt hlate) (h.maximal h.snd_mem h'.snd_mem hyy')

private noncomputable instance : Inhabited HamelIndex :=
  ⟨hamelBasis.index_nonempty.some⟩

/-- The canonical critical pair.  Its value on sets of size at most one is an
irrelevant default; all specifications below assume `2 ≤ s.card`. -/
noncomputable def criticalPair (s : Finset HamelIndex) : HamelIndex × HamelIndex :=
  if hs : 2 ≤ s.card then
    let h := exists_isCriticalPair s hs
    (Classical.choose h, Classical.choose (Classical.choose_spec h))
  else default

theorem criticalPair_spec {s : Finset HamelIndex} (hs : 2 ≤ s.card) :
    IsCriticalPair s (criticalPair s).1 (criticalPair s).2 := by
  rw [criticalPair, dif_pos hs]
  exact Classical.choose_spec (Classical.choose_spec (exists_isCriticalPair s hs))

/-- Characterization of the canonical pair.  This is the main interface used
to identify it in structured unions. -/
theorem criticalPair_eq_iff_isCriticalPair {s : Finset HamelIndex}
    (hs : 2 ≤ s.card) {x y : HamelIndex} :
    criticalPair s = (x, y) ↔ IsCriticalPair s x y := by
  constructor
  · intro hp
    have h := criticalPair_spec hs
    rw [hp] at h
    exact h
  · intro h
    have hu := isCriticalPair_unique (criticalPair_spec hs) h
    exact Prod.ext hu.1 hu.2

/-- A convenient cross-union characterization: to identify a proposed pair,
it suffices to prove membership and ordinary orientation, an upper bound for
every first difference in the union, and leastness of its lower endpoint among
the maximizing pairs. -/
theorem criticalPair_eq_of_maximal_least {s : Finset HamelIndex}
    (hs : 2 ≤ s.card) {x y : HamelIndex}
    (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y)
    (hmax : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b →
      firstDiff a b ≤ firstDiff x y)
    (hleast : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a < b →
      firstDiff a b = firstDiff x y → x ≤ a) :
    criticalPair s = (x, y) := by
  exact (criticalPair_eq_iff_isCriticalPair hs).2 ⟨hx, hy, hxy, hmax, hleast⟩

/-! ## The support colouring -/

/-- Colour a finite support by comparing the ordinary orientation of its
critical pair with the fixed choice well-order. -/
noncomputable def supportColor (s : Finset HamelIndex) : Fin 2 :=
  by
    classical
    exact if hs : 2 ≤ s.card then
      if WellOrderingRel (criticalPair s).1 (criticalPair s).2 then 0 else 1
    else 0

theorem supportColor_eq_zero_of_criticalPair {s : Finset HamelIndex}
    (hs : 2 ≤ s.card) {x y : HamelIndex}
    (hp : criticalPair s = (x, y)) (hxy : WellOrderingRel x y) :
    supportColor s = 0 := by
  classical
  simp [supportColor, hs, hp, hxy]

theorem supportColor_eq_one_of_criticalPair {s : Finset HamelIndex}
    (hs : 2 ≤ s.card) {x y : HamelIndex}
    (hp : criticalPair s = (x, y)) (hxy : ¬ WellOrderingRel x y) :
    supportColor s = 1 := by
  classical
  simp [supportColor, hs, hp, hxy]

end Erdos965
