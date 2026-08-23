/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 210.
https://www.erdosproblems.com/forum/thread/210

Informal authors:
- L. M. Kelly
- W. O. J. Moser

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos210.md
-/
/-
This is a Lean formalization of a resolution of Erdős Problem 210.
https://www.erdosproblems.com/forum/thread/210

The quantitative argument formalized here is a closest-line variant of the
Kelly--Moser method: a finite noncollinear set of `n` real planar points
determines at least `n/10` ordinary lines.  Together with the near-pencil
construction this proves the exact linear order of growth, and in particular
that the minimum tends to infinity.  The classical Kelly--Moser constant
`3/7` and the sharper Green--Tao results are documented in `tex/210.tex`.

Informal authors:
- L. M. Kelly
- W. O. J. Moser

Formal authors:
- Codex
- Boris Alexeev
-/
import Mathlib

open scoped Topology

noncomputable section

namespace Erdos210

/-- The concrete real affine plane used in Problem 210. -/
abbrev Point := ℝ × ℝ

/-- The signed twice-area determinant of the ordered triple `a,b,c`. -/
def orient (a b c : Point) : ℝ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Concrete collinearity of three planar points. -/
def Collinear3 (a b c : Point) : Prop := orient a b c = 0

lemma collinear3_refl_left (a b : Point) : Collinear3 a a b := by
  simp [Collinear3, orient]

lemma collinear3_refl_right (a b : Point) : Collinear3 a b b := by
  simp only [Collinear3, orient]
  ring

lemma collinear3_swap_left {a b c : Point} : Collinear3 a b c ↔ Collinear3 b a c := by
  simp only [Collinear3, orient]
  constructor <;> intro h <;> nlinarith

lemma collinear3_rotate {a b c : Point} : Collinear3 a b c ↔ Collinear3 b c a := by
  simp only [Collinear3, orient]
  constructor <;> intro h <;> nlinarith

/-- A two-element finset is an ordinary pair when its joining line contains no
other point of `P`.  Counting these finsets counts geometric ordinary lines:
an ordinary line has exactly one two-element intersection with `P`. -/
def IsOrdinaryPair (P e : Finset Point) : Prop :=
  e.card = 2 ∧ e ⊆ P ∧
    ∀ ⦃a⦄, a ∈ e → ∀ ⦃b⦄, b ∈ e → a ≠ b →
      ∀ ⦃c⦄, c ∈ P → Collinear3 a b c → c ∈ e

/-- The finset of ordinary lines, represented by their two incident points. -/
def ordinaryPairs (P : Finset Point) : Finset (Finset Point) :=
  by
    classical
    exact P.powersetCard 2 |>.filter (IsOrdinaryPair P)

/-- The number of ordinary lines determined by `P`. -/
def ordinaryCount (P : Finset Point) : ℕ := (ordinaryPairs P).card

@[simp] lemma mem_ordinaryPairs {P e : Finset Point} :
    e ∈ ordinaryPairs P ↔ IsOrdinaryPair P e := by
  classical
  constructor
  · intro he
    exact (Finset.mem_filter.mp he).2
  · intro he
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨he.2.1, he.1⟩, he⟩

lemma ordinaryPair_subset {P e : Finset Point} (he : e ∈ ordinaryPairs P) : e ⊆ P :=
  (mem_ordinaryPairs.mp he).2.1

lemma ordinaryPair_card {P e : Finset Point} (he : e ∈ ordinaryPairs P) : e.card = 2 :=
  (mem_ordinaryPairs.mp he).1

lemma ordinaryPair_collinear_mem {P e : Finset Point} (he : e ∈ ordinaryPairs P)
    {a b c : Point} (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b)
    (hc : c ∈ P) (hcol : Collinear3 a b c) : c ∈ e :=
  (mem_ordinaryPairs.mp he).2.2 ha hb hab hc hcol

/-- Ordinary partners of a point; its cardinality is the usual order of the point. -/
def ordinaryPartners (P : Finset Point) (p : Point) : Finset Point :=
  P.filter fun q ↦ q ≠ p ∧ {p, q} ∈ ordinaryPairs P

/-- The number of ordinary lines through a point. -/
def order (P : Finset Point) (p : Point) : ℕ := (ordinaryPartners P p).card

@[simp] lemma mem_ordinaryPartners {P : Finset Point} {p q : Point} :
    q ∈ ordinaryPartners P p ↔ q ∈ P ∧ q ≠ p ∧ {p, q} ∈ ordinaryPairs P := by
  simp [ordinaryPartners]

lemma ordinaryPair_symm (P : Finset Point) (p q : Point) :
    ({p, q} ∈ ordinaryPairs P) ↔ ({q, p} ∈ ordinaryPairs P) := by
  have hpair : ({p, q} : Finset Point) = {q, p} := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hpair]

/-- Squared Euclidean length of the vector from `a` to `b`. -/
def lengthSq (a b : Point) : ℝ :=
  (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2

lemma lengthSq_pos {a b : Point} (hab : a ≠ b) : 0 < lengthSq a b := by
  rw [lengthSq]
  have hcoord : b.1 ≠ a.1 ∨ b.2 ≠ a.2 := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hab (Prod.ext h.1.symm h.2.symm)
  rcases hcoord with h | h
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr h)) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (sub_ne_zero.mpr h))

lemma lengthSq_eq_zero_iff {a b : Point} : lengthSq a b = 0 ↔ a = b := by
  constructor
  · intro h
    have h1 : b.1 - a.1 = 0 := by
      simp only [lengthSq] at h
      nlinarith [sq_nonneg (b.2 - a.2)]
    have h2 : b.2 - a.2 = 0 := by
      simp only [lengthSq] at h
      nlinarith [sq_nonneg (b.1 - a.1)]
    exact Prod.ext (sub_eq_zero.mp h1).symm (sub_eq_zero.mp h2).symm
  · rintro rfl
    simp [lengthSq]

/-- Squared distance from `p` to the affine line through distinct `a,b`.
The definition is algebraic, avoiding square roots in all comparisons. -/
def lineDistSq (p a b : Point) : ℝ := orient a b p ^ 2 / lengthSq a b

lemma lineDistSq_nonneg (p a b : Point) : 0 ≤ lineDistSq p a b := by
  by_cases hab : a = b
  · subst b
    simp [lineDistSq, lengthSq]
  · exact div_nonneg (sq_nonneg _) (lengthSq_pos hab).le

lemma lineDistSq_eq_zero_iff {p a b : Point} (hab : a ≠ b) :
    lineDistSq p a b = 0 ↔ Collinear3 a b p := by
  simp [lineDistSq, Collinear3, div_eq_zero_iff, (lengthSq_pos hab).ne']

/-- The direct similarity sending `a` to `(0,0)` and `b` to `(1,0)`. -/
def normalize (a b p : Point) : Point :=
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let d := lengthSq a b
  (((p.1 - a.1) * dx + (p.2 - a.2) * dy) / d,
    orient a b p / d)

lemma normalize_left {a b : Point} (hab : a ≠ b) : normalize a b a = (0, 0) := by
  have hd : lengthSq a b ≠ 0 := (lengthSq_pos hab).ne'
  simp [normalize, orient, hd]

lemma normalize_right {a b : Point} (hab : a ≠ b) : normalize a b b = (1, 0) := by
  have hd : lengthSq a b ≠ 0 := (lengthSq_pos hab).ne'
  simp only [normalize, orient, Prod.fst, Prod.snd]
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd]
  · rw [div_eq_one_iff_eq hd]
    simp only [lengthSq]
    ring
  · rw [div_eq_zero_iff]
    exact Or.inl (by ring)

lemma normalize_snd_ne_zero_iff {a b p : Point} (hab : a ≠ b) :
    (normalize a b p).2 ≠ 0 ↔ ¬ Collinear3 a b p := by
  have hd : lengthSq a b ≠ 0 := (lengthSq_pos hab).ne'
  simp [normalize, Collinear3, hd]

lemma orient_normalize {a b : Point} (hab : a ≠ b) (p q r : Point) :
    orient (normalize a b p) (normalize a b q) (normalize a b r) =
      orient p q r / lengthSq a b := by
  have hd : lengthSq a b ≠ 0 := (lengthSq_pos hab).ne'
  simp only [normalize, orient, Prod.fst, Prod.snd]
  field_simp [hd]
  simp only [lengthSq]
  ring

lemma lengthSq_normalize {a b : Point} (hab : a ≠ b) (p q : Point) :
    lengthSq (normalize a b p) (normalize a b q) =
      lengthSq p q / lengthSq a b := by
  have hd : lengthSq a b ≠ 0 := (lengthSq_pos hab).ne'
  rw [show lengthSq (normalize a b p) (normalize a b q) =
      ((normalize a b q).1 - (normalize a b p).1) ^ 2 +
      ((normalize a b q).2 - (normalize a b p).2) ^ 2 by rfl]
  simp only [normalize, orient, Prod.fst, Prod.snd]
  field_simp [hd]
  simp only [lengthSq]
  ring

lemma normalize_injective {a b : Point} (hab : a ≠ b) :
    Function.Injective (normalize a b) := by
  intro p q hpq
  have hzero : lengthSq (normalize a b p) (normalize a b q) = 0 := by
    rw [hpq]
    simp [lengthSq]
  rw [lengthSq_normalize hab] at hzero
  have : lengthSq p q = 0 :=
    (div_eq_zero_iff.mp hzero).resolve_right (lengthSq_pos hab).ne'
  exact lengthSq_eq_zero_iff.mp this

lemma lineDistSq_normalize {a b : Point} (hab : a ≠ b) (p q r : Point) (hqr : q ≠ r) :
    lineDistSq (normalize a b p) (normalize a b q) (normalize a b r) =
      lineDistSq p q r / lengthSq a b := by
  have hnorm : normalize a b q ≠ normalize a b r := by
    intro h
    have hzero : lengthSq (normalize a b q) (normalize a b r) = 0 := by
      rw [h]
      simp [lengthSq]
    rw [lengthSq_normalize hab] at hzero
    have hlen : lengthSq q r = 0 :=
      (div_eq_zero_iff.mp hzero).resolve_right (lengthSq_pos hab).ne'
    exact hqr (lengthSq_eq_zero_iff.mp hlen)
  rw [lineDistSq, orient_normalize hab, lengthSq_normalize hab]
  simp only [lineDistSq]
  field_simp [(lengthSq_pos hab).ne', (lengthSq_pos hqr).ne',
    (lengthSq_pos hnorm).ne']

/-- Slope from the normalized left endpoint `(0,0)`. -/
def leftSlope (p : Point) : ℝ := p.1 / p.2

/-- Slope from the normalized right endpoint `(1,0)`. -/
def rightSlope (p : Point) : ℝ := (p.1 - 1) / p.2

lemma lineDistSq_base (p : Point) :
    lineDistSq p (0, 0) (1, 0) = p.2 ^ 2 := by
  simp [lineDistSq, orient, lengthSq]

lemma lineDistSq_from_left (p q : Point) (hp : p.2 ≠ 0) (hq : q.2 ≠ 0) :
    lineDistSq p (0, 0) q =
      p.2 ^ 2 * (leftSlope p - leftSlope q) ^ 2 /
        (leftSlope q ^ 2 + 1) := by
  simp only [lineDistSq, orient, lengthSq, leftSlope, Prod.fst, Prod.snd,
    sub_zero, zero_mul, mul_zero, zero_add]
  field_simp [hp, hq]
  ring

lemma lineDistSq_from_right (p q : Point) (hp : p.2 ≠ 0) (hq : q.2 ≠ 0) :
    lineDistSq p (1, 0) q =
      p.2 ^ 2 * (rightSlope p - rightSlope q) ^ 2 /
        (rightSlope q ^ 2 + 1) := by
  simp only [lineDistSq, orient, lengthSq, rightSlope, Prod.fst, Prod.snd,
    sub_zero, zero_mul, mul_zero, zero_add]
  field_simp [hp, hq]
  ring

/-- The numerical separation forced by two closest-line comparisons. -/
def StrongSeparated (x y : ℝ) : Prop :=
  x ^ 2 + 1 ≤ (x - y) ^ 2 ∧ y ^ 2 + 1 ≤ (x - y) ^ 2

lemma strongSeparated_symm {x y : ℝ} : StrongSeparated x y ↔ StrongSeparated y x := by
  simp only [StrongSeparated]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

lemma strongSeparated_of_left_comparisons {p q : Point}
    (hp : p.2 ≠ 0) (hq : q.2 ≠ 0)
    (hpq : lineDistSq p (0, 0) (1, 0) ≤ lineDistSq p (0, 0) q)
    (hqp : lineDistSq q (0, 0) (1, 0) ≤ lineDistSq q (0, 0) p) :
    StrongSeparated (leftSlope p) (leftSlope q) := by
  rw [lineDistSq_base, lineDistSq_from_left p q hp hq] at hpq
  rw [lineDistSq_base, lineDistSq_from_left q p hq hp] at hqp
  have hdenp : 0 < leftSlope p ^ 2 + 1 := by nlinarith [sq_nonneg (leftSlope p)]
  have hdenq : 0 < leftSlope q ^ 2 + 1 := by nlinarith [sq_nonneg (leftSlope q)]
  rw [le_div_iff₀ hdenq] at hpq
  rw [le_div_iff₀ hdenp] at hqp
  have hpsq : 0 < p.2 ^ 2 := sq_pos_of_ne_zero hp
  have hqsq : 0 < q.2 ^ 2 := sq_pos_of_ne_zero hq
  constructor
  · exact (mul_le_mul_iff_of_pos_left hqsq).mp (by nlinarith [hqp])
  · exact (mul_le_mul_iff_of_pos_left hpsq).mp (by nlinarith [hpq])

lemma strongSeparated_of_right_comparisons {p q : Point}
    (hp : p.2 ≠ 0) (hq : q.2 ≠ 0)
    (hpq : lineDistSq p (0, 0) (1, 0) ≤ lineDistSq p (1, 0) q)
    (hqp : lineDistSq q (0, 0) (1, 0) ≤ lineDistSq q (1, 0) p) :
    StrongSeparated (rightSlope p) (rightSlope q) := by
  rw [lineDistSq_base, lineDistSq_from_right p q hp hq] at hpq
  rw [lineDistSq_base, lineDistSq_from_right q p hq hp] at hqp
  have hdenp : 0 < rightSlope p ^ 2 + 1 := by nlinarith [sq_nonneg (rightSlope p)]
  have hdenq : 0 < rightSlope q ^ 2 + 1 := by nlinarith [sq_nonneg (rightSlope q)]
  rw [le_div_iff₀ hdenq] at hpq
  rw [le_div_iff₀ hdenp] at hqp
  have hpsq : 0 < p.2 ^ 2 := sq_pos_of_ne_zero hp
  have hqsq : 0 < q.2 ^ 2 := sq_pos_of_ne_zero hq
  constructor
  · exact (mul_le_mul_iff_of_pos_left hqsq).mp (by nlinarith [hqp])
  · exact (mul_le_mul_iff_of_pos_left hpsq).mp (by nlinarith [hpq])

lemma no_three_strongSeparated_ordered {x y z : ℝ} (hxy : x < y) (hyz : y < z)
    (h₁ : StrongSeparated x y) (h₂ : StrongSeparated y z) : False := by
  by_cases hy : y ≤ 0
  · have hprod : 0 ≤ y * (2 * x - y) :=
      mul_nonneg_of_nonpos_of_nonpos hy (by linarith)
    nlinarith [h₁.1]
  · have hy' : 0 < y := lt_of_not_ge hy
    have hprod : 0 < y * (2 * z - y) :=
      mul_pos hy' (by linarith)
    nlinarith [h₂.2]

lemma no_three_pairwise_strongSeparated {x y z : ℝ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : ∀ u v, u ∈ ({x, y, z} : Finset ℝ) →
      v ∈ ({x, y, z} : Finset ℝ) → u ≠ v → StrongSeparated u v) : False := by
  have hXY := h x y (by simp) (by simp) hxy
  have hXZ := h x z (by simp) (by simp) hxz
  have hYZ := h y z (by simp) (by simp) hyz
  rcases lt_or_gt_of_ne hxy with hxy' | hyx'
  · rcases lt_or_gt_of_ne hyz with hyz' | hzy'
    · exact no_three_strongSeparated_ordered hxy' hyz' hXY hYZ
    · rcases lt_or_gt_of_ne hxz with hxz' | hzx'
      · exact no_three_strongSeparated_ordered hxz' hzy'
          hXZ (strongSeparated_symm.mp hYZ)
      · exact no_three_strongSeparated_ordered hzx' hxy'
          (strongSeparated_symm.mp hXZ) hXY
  · rcases lt_or_gt_of_ne hxz with hxz' | hzx'
    · exact no_three_strongSeparated_ordered hyx' hxz'
        (strongSeparated_symm.mp hXY) hXZ
    · rcases lt_or_gt_of_ne hyz with hyz' | hzy'
      · exact no_three_strongSeparated_ordered hyz' hzx'
          hYZ (strongSeparated_symm.mp hXZ)
      · exact no_three_strongSeparated_ordered hzy' hyx'
          (strongSeparated_symm.mp hYZ) (strongSeparated_symm.mp hXY)

lemma card_le_two_of_pairwise_strongSeparated (S : Finset ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → StrongSeparated x y) : S.card ≤ 2 := by
  by_contra hn
  have hlt : 2 < S.card := Nat.lt_of_not_ge hn
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp hlt
  exact no_three_pairwise_strongSeparated hxy hxz hyz (by
    intro u v hu hv huv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first | exact (huv rfl).elim | exact h _ hx _ hy huv |
      exact h _ hx _ hz huv | exact h _ hy _ hx huv | exact h _ hy _ hz huv |
      exact h _ hz _ hx huv | exact h _ hz _ hy huv)

lemma slope_pair_injective {p q : Point} (hp : p.2 ≠ 0) (hq : q.2 ≠ 0)
    (hleft : leftSlope p = leftSlope q)
    (hright : rightSlope p = rightSlope q) : p = q := by
  have hsnd : p.2 = q.2 := by
    simp only [leftSlope, rightSlope] at hleft hright
    have hsub := congrArg₂ (fun x y : ℝ ↦ x - y) hleft hright
    field_simp [hp, hq] at hsub
    linarith
  apply Prod.ext
  · simp only [leftSlope] at hleft
    rw [hsnd] at hleft
    exact (div_left_inj' hq).mp hleft
  · exact hsnd

/-- A concrete witness that a finite point set is not contained in one affine line. -/
def HasNoncollinearTriple (P : Finset Point) : Prop :=
  ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, ¬ Collinear3 a b c

lemma exists_offLine_pair (P : Finset Point) (hP : HasNoncollinearTriple P)
    {p : Point} (hp : p ∈ P) :
    ∃ a ∈ P, ∃ b ∈ P, a ≠ b ∧ ¬ Collinear3 a b p := by
  obtain ⟨u, hu, v, hv, w, hw, huv⟩ := hP
  by_cases h₁ : Collinear3 u v p
  · by_cases h₂ : Collinear3 u w p
    · have h₃ : ¬ Collinear3 v w p := by
        intro h₃
        apply huv
        simp only [Collinear3, orient] at h₁ h₂ h₃ ⊢
        nlinarith
      refine ⟨v, hv, w, hw, ?_, h₃⟩
      intro h
      subst w
      exact h₃ (collinear3_refl_left v p)
    · refine ⟨u, hu, w, hw, ?_, h₂⟩
      intro h
      subst w
      exact h₂ (collinear3_refl_left u p)
  · refine ⟨u, hu, v, hv, ?_, h₁⟩
    intro h
    subst v
    exact h₁ (collinear3_refl_left u p)

/-- Ordered pairs which determine a line not passing through `p`. -/
def offLinePairs (P : Finset Point) (p : Point) : Finset (Point × Point) :=
  by
    classical
    exact (P ×ˢ P).filter fun ab ↦ ab.1 ≠ ab.2 ∧ ¬ Collinear3 ab.1 ab.2 p

@[simp] lemma mem_offLinePairs {P : Finset Point} {p a b : Point} :
    (a, b) ∈ offLinePairs P p ↔
      a ∈ P ∧ b ∈ P ∧ a ≠ b ∧ ¬ Collinear3 a b p := by
  classical
  simp [offLinePairs, and_assoc]

/-- The line `ab` is a closest connecting line to `p` among those not through `p`. -/
def IsClosestPair (P : Finset Point) (p a b : Point) : Prop :=
  (a, b) ∈ offLinePairs P p ∧
    ∀ ⦃c d : Point⦄, (c, d) ∈ offLinePairs P p →
      lineDistSq p a b ≤ lineDistSq p c d

lemma exists_closestPair (P : Finset Point) (hP : HasNoncollinearTriple P)
    {p : Point} (hp : p ∈ P) : ∃ a b, IsClosestPair P p a b := by
  classical
  have hne : (offLinePairs P p).Nonempty := by
    obtain ⟨a, ha, b, hb, hab, hoff⟩ := exists_offLine_pair P hP hp
    exact ⟨(a, b), mem_offLinePairs.mpr ⟨ha, hb, hab, hoff⟩⟩
  obtain ⟨ab, hab, hmin⟩ :=
    Set.exists_min_image (offLinePairs P p : Set (Point × Point))
      (fun cd ↦ lineDistSq p cd.1 cd.2) (offLinePairs P p).finite_toSet
      (by simpa [Set.nonempty_coe_sort] using hne)
  exact ⟨ab.1, ab.2, hab, fun _ _ hcd ↦ hmin _ hcd⟩

lemma closestPair_left_mem {P : Finset Point} {p a b : Point}
    (h : IsClosestPair P p a b) : a ∈ P :=
  (mem_offLinePairs.mp h.1).1

lemma closestPair_right_mem {P : Finset Point} {p a b : Point}
    (h : IsClosestPair P p a b) : b ∈ P :=
  (mem_offLinePairs.mp h.1).2.1

lemma closestPair_ne {P : Finset Point} {p a b : Point}
    (h : IsClosestPair P p a b) : a ≠ b :=
  (mem_offLinePairs.mp h.1).2.2.1

lemma closestPair_offLine {P : Finset Point} {p a b : Point}
    (h : IsClosestPair P p a b) : ¬ Collinear3 a b p :=
  (mem_offLinePairs.mp h.1).2.2.2

lemma ordinary_pair_iff {P : Finset Point} {a b : Point}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    {a, b} ∈ ordinaryPairs P ↔
      ∀ ⦃c⦄, c ∈ P → Collinear3 a b c → c = a ∨ c = b := by
  classical
  rw [mem_ordinaryPairs]
  constructor
  · intro h c hc hcol
    have hmem := h.2.2 (by simp) (by simp) hab hc hcol
    simpa [eq_comm] using hmem
  · intro h
    refine ⟨by simp [hab], ?_, ?_⟩
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb
    intro x hx y hy hxy c hc hcol
    have hxy_pair : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact (hxy rfl).elim
    rcases hxy_pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [eq_comm] using h hc hcol
    · have hcol' := collinear3_swap_left.mp hcol
      simpa [eq_comm] using h hc hcol'

lemma exists_third_of_not_ordinary {P : Finset Point} {a b : Point}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b)
    (h : {a, b} ∉ ordinaryPairs P) :
    ∃ c ∈ P, Collinear3 a b c ∧ c ≠ a ∧ c ≠ b := by
  rw [ordinary_pair_iff ha hb hab] at h
  push_neg at h
  obtain ⟨c, hc, hcol, hca, hcb⟩ := h
  exact ⟨c, hc, hcol, hca, hcb⟩

/-- Points of `P` for which the ordered line `ab` realizes the closest
connecting-line distance. -/
def attachedPoints (P : Finset Point) (a b : Point) : Finset Point := by
  classical
  exact P.filter fun p ↦ IsClosestPair P p a b

@[simp] lemma mem_attachedPoints {P : Finset Point} {p a b : Point} :
    p ∈ attachedPoints P a b ↔ p ∈ P ∧ IsClosestPair P p a b := by
  simp [attachedPoints]

lemma attached_normalize_snd_ne {P : Finset Point} {p a b : Point}
    (hp : p ∈ attachedPoints P a b) : (normalize a b p).2 ≠ 0 := by
  have hclose := (mem_attachedPoints.mp hp).2
  exact (normalize_snd_ne_zero_iff (closestPair_ne hclose)).mpr
    (closestPair_offLine hclose)

lemma not_collinear_left_of_slope_ne {p q : Point} (hp : p.2 ≠ 0) (hq : q.2 ≠ 0)
    (h : leftSlope p ≠ leftSlope q) : ¬ Collinear3 (0, 0) q p := by
  intro hcol
  apply h
  rw [leftSlope, leftSlope, div_eq_div_iff hp hq]
  simp only [Collinear3, orient, Prod.fst, Prod.snd, sub_zero, zero_mul, mul_zero,
    zero_add] at hcol
  nlinarith

lemma not_collinear_right_of_slope_ne {p q : Point} (hp : p.2 ≠ 0) (hq : q.2 ≠ 0)
    (h : rightSlope p ≠ rightSlope q) : ¬ Collinear3 (1, 0) q p := by
  intro hcol
  apply h
  rw [rightSlope, rightSlope, div_eq_div_iff hp hq]
  simp only [Collinear3, orient, Prod.fst, Prod.snd, sub_zero, zero_mul, mul_zero,
    zero_add] at hcol
  nlinarith

lemma attached_left_comparison {P : Finset Point} {p q a b : Point}
    (hp : p ∈ attachedPoints P a b) (hq : q ∈ attachedPoints P a b)
    (hslope : leftSlope (normalize a b p) ≠ leftSlope (normalize a b q)) :
    lineDistSq (normalize a b p) (0, 0) (1, 0) ≤
      lineDistSq (normalize a b p) (0, 0) (normalize a b q) := by
  have hpclose := (mem_attachedPoints.mp hp).2
  have hqclose := (mem_attachedPoints.mp hq).2
  have hab : a ≠ b := closestPair_ne hpclose
  have hqn : (normalize a b q).2 ≠ 0 := attached_normalize_snd_ne hq
  have hpn : (normalize a b p).2 ≠ 0 := attached_normalize_snd_ne hp
  have haq : a ≠ q := by
    intro haq
    subst q
    rw [normalize_left hab] at hqn
    exact hqn rfl
  have hoff : ¬ Collinear3 a q p := by
    intro hcol
    have hnormcol : Collinear3 (normalize a b a) (normalize a b q) (normalize a b p) := by
      rw [Collinear3, orient_normalize hab]
      simp [Collinear3] at hcol
      simp [hcol]
    rw [normalize_left hab] at hnormcol
    exact (not_collinear_left_of_slope_ne hpn hqn hslope) hnormcol
  have hcand : (a, q) ∈ offLinePairs P p := mem_offLinePairs.mpr ⟨
    closestPair_left_mem hpclose, (mem_attachedPoints.mp hq).1, haq, hoff⟩
  have hmin := hpclose.2 hcand
  calc
    lineDistSq (normalize a b p) (0, 0) (1, 0) =
        lineDistSq p a b / lengthSq a b := by
          rw [← normalize_left hab, ← normalize_right hab]
          exact lineDistSq_normalize hab p a b hab
    _ ≤ lineDistSq p a q / lengthSq a b :=
      (div_le_div_iff_of_pos_right (lengthSq_pos hab)).mpr hmin
    _ = lineDistSq (normalize a b p) (0, 0) (normalize a b q) := by
      rw [← lineDistSq_normalize hab p a q haq, normalize_left hab]

lemma attached_right_comparison {P : Finset Point} {p q a b : Point}
    (hp : p ∈ attachedPoints P a b) (hq : q ∈ attachedPoints P a b)
    (hslope : rightSlope (normalize a b p) ≠ rightSlope (normalize a b q)) :
    lineDistSq (normalize a b p) (0, 0) (1, 0) ≤
      lineDistSq (normalize a b p) (1, 0) (normalize a b q) := by
  have hpclose := (mem_attachedPoints.mp hp).2
  have hqclose := (mem_attachedPoints.mp hq).2
  have hab : a ≠ b := closestPair_ne hpclose
  have hqn : (normalize a b q).2 ≠ 0 := attached_normalize_snd_ne hq
  have hpn : (normalize a b p).2 ≠ 0 := attached_normalize_snd_ne hp
  have hbq : b ≠ q := by
    intro hbq
    subst q
    rw [normalize_right hab] at hqn
    exact hqn rfl
  have hoff : ¬ Collinear3 b q p := by
    intro hcol
    have hnormcol : Collinear3 (normalize a b b) (normalize a b q) (normalize a b p) := by
      rw [Collinear3, orient_normalize hab]
      simp [Collinear3] at hcol
      simp [hcol]
    rw [normalize_right hab] at hnormcol
    exact (not_collinear_right_of_slope_ne hpn hqn hslope) hnormcol
  have hcand : (b, q) ∈ offLinePairs P p := mem_offLinePairs.mpr ⟨
    closestPair_right_mem hpclose, (mem_attachedPoints.mp hq).1, hbq, hoff⟩
  have hmin := hpclose.2 hcand
  calc
    lineDistSq (normalize a b p) (0, 0) (1, 0) =
        lineDistSq p a b / lengthSq a b := by
          rw [← normalize_left hab, ← normalize_right hab]
          exact lineDistSq_normalize hab p a b hab
    _ ≤ lineDistSq p b q / lengthSq a b :=
      (div_le_div_iff_of_pos_right (lengthSq_pos hab)).mpr hmin
    _ = lineDistSq (normalize a b p) (1, 0) (normalize a b q) := by
      rw [← lineDistSq_normalize hab p b q hbq, normalize_right hab]

lemma attached_leftSlopes_card_le_two (P : Finset Point) (a b : Point) :
    ((attachedPoints P a b).image fun p ↦ leftSlope (normalize a b p)).card ≤ 2 := by
  apply card_le_two_of_pairwise_strongSeparated
  intro x hx y hy hxy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hy
  subst y
  exact strongSeparated_of_left_comparisons
    (attached_normalize_snd_ne hp) (attached_normalize_snd_ne hq)
    (attached_left_comparison hp hq hxy)
    (attached_left_comparison hq hp (Ne.symm hxy))

lemma attached_rightSlopes_card_le_two (P : Finset Point) (a b : Point) :
    ((attachedPoints P a b).image fun p ↦ rightSlope (normalize a b p)).card ≤ 2 := by
  apply card_le_two_of_pairwise_strongSeparated
  intro x hx y hy hxy
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, hq, hqeq⟩ := Finset.mem_image.mp hy
  subst y
  exact strongSeparated_of_right_comparisons
    (attached_normalize_snd_ne hp) (attached_normalize_snd_ne hq)
    (attached_right_comparison hp hq hxy)
    (attached_right_comparison hq hp (Ne.symm hxy))

/-- A fixed closest connecting line can be selected by at most four points.
This is the finite normalized-slope form of Kelly--Moser's four-neighbour
lemma. -/
lemma attachedPoints_card_le_four (P : Finset Point) (a b : Point) :
    (attachedPoints P a b).card ≤ 4 := by
  classical
  let L : Finset ℝ :=
    (attachedPoints P a b).image fun p ↦ leftSlope (normalize a b p)
  let R : Finset ℝ :=
    (attachedPoints P a b).image fun p ↦ rightSlope (normalize a b p)
  let F : Point → ℝ × ℝ := fun p ↦
    (leftSlope (normalize a b p), rightSlope (normalize a b p))
  have hinj : Set.InjOn F (attachedPoints P a b) := by
    intro p hp q hq hpq
    apply normalize_injective (closestPair_ne (mem_attachedPoints.mp hp).2)
    apply slope_pair_injective (attached_normalize_snd_ne hp)
      (attached_normalize_snd_ne hq)
    · exact congrArg Prod.fst hpq
    · exact congrArg Prod.snd hpq
  have himage : (attachedPoints P a b).image F ⊆ L ×ˢ R := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
  calc
    (attachedPoints P a b).card = ((attachedPoints P a b).image F).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (L ×ˢ R).card := Finset.card_le_card himage
    _ = L.card * R.card := Finset.card_product L R
    _ ≤ 2 * 2 := Nat.mul_le_mul (attached_leftSlopes_card_le_two P a b)
      (attached_rightSlopes_card_le_two P a b)
    _ = 4 := by norm_num

/-! ### The closest-line crossing calculation -/

/-- After a closest line has been made horizontal, this second similarity
sends the chosen point to `(0,1)` and its perpendicular foot to `(0,0)`. -/
def verticalNormalize (p z : Point) : Point :=
  ((z.1 - p.1) / p.2, z.2 / p.2)

lemma verticalNormalize_self {p : Point} (hp : p.2 ≠ 0) :
    verticalNormalize p p = (0, 1) := by
  simp [verticalNormalize, hp]

lemma verticalNormalize_injective {p : Point} (hp : p.2 ≠ 0) :
    Function.Injective (verticalNormalize p) := by
  intro x y h
  apply Prod.ext
  · have h₁ := congrArg Prod.fst h
    simp only [verticalNormalize, Prod.fst] at h₁
    have := (div_left_inj' hp).mp h₁
    linarith
  · have h₂ := congrArg Prod.snd h
    simp only [verticalNormalize, Prod.snd] at h₂
    exact (div_left_inj' hp).mp h₂

lemma orient_verticalNormalize {p x y z : Point} (hp : p.2 ≠ 0) :
    orient (verticalNormalize p x) (verticalNormalize p y) (verticalNormalize p z) =
      orient x y z / p.2 ^ 2 := by
  simp only [verticalNormalize, orient, Prod.fst, Prod.snd]
  field_simp [hp]
  ring

lemma lineDistSq_verticalNormalize {p x a b : Point} (hp : p.2 ≠ 0) (hab : a ≠ b) :
    lineDistSq (verticalNormalize p x) (verticalNormalize p a) (verticalNormalize p b) =
      lineDistSq x a b / p.2 ^ 2 := by
  have hnab : verticalNormalize p a ≠ verticalNormalize p b :=
    (verticalNormalize_injective hp).ne hab
  simp only [lineDistSq, verticalNormalize, orient, lengthSq, Prod.fst, Prod.snd]
  field_simp [hp, (lengthSq_pos hab).ne', (lengthSq_pos hnab).ne']
  ring

lemma verticalNormalize_base_snd {p v : Point} (hv : v.2 = 0) :
    (verticalNormalize p v).2 = 0 := by
  simp [verticalNormalize, hv]

/-- The normalized third point on the line from `(0,1)` to `(v,0)`. -/
def thirdPoint (v t : ℝ) : Point := (t * v, 1 - t)

lemma verticalNormalize_eq_thirdPoint {p v w : Point} (hp : p.2 ≠ 0)
    (hv : v.2 = 0) (hcol : Collinear3 p v w) :
    verticalNormalize p w =
      thirdPoint (verticalNormalize p v).1 (1 - (verticalNormalize p w).2) := by
  have hcol' : Collinear3 (verticalNormalize p p) (verticalNormalize p v)
      (verticalNormalize p w) := by
    rw [Collinear3, orient_verticalNormalize hp]
    simp [Collinear3] at hcol
    simp [hcol]
  rw [verticalNormalize_self hp] at hcol'
  have hv' := verticalNormalize_base_snd (p := p) hv
  apply Prod.ext
  · simp only [thirdPoint, Prod.fst]
    simp only [Collinear3, orient, Prod.fst, Prod.snd] at hcol'
    rw [hv'] at hcol'
    nlinarith
  · simp [thirdPoint]

/-- `Closer u v t` says that the line from `(u,0)` to the third point
`thirdPoint v t` is closer to `(0,1)` than the horizontal base line. -/
def Closer (u v t : ℝ) : Prop :=
  lineDistSq (0, 1) (u, 0) (thirdPoint v t) < 1

lemma mul_sq_le_mul_of_same_sign {u v : ℝ} (huv : 0 ≤ u * v)
    (hsq : u ^ 2 ≤ v ^ 2) : u ^ 2 ≤ u * v := by
  rcases (mul_nonneg_iff.mp huv) with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have huv' : u ≤ v := by
      rw [← sq_le_sq₀ hu hv]
      exact hsq
    nlinarith [mul_nonneg hu (sub_nonneg.mpr huv')]
  · have hvu : v ≤ u := by
      have habs := sq_le_sq.mp hsq
      rw [abs_of_nonpos hu, abs_of_nonpos hv] at habs
      linarith
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hu (sub_nonpos.mpr hvu)]

lemma closer_of_inside {u v t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1)
    (hposition : v ^ 2 ≤ u ^ 2 ∨ u * v ≤ 0) : Closer u v t := by
  have hne : ((u, 0) : Point) ≠ thirdPoint v t := by
    intro h
    have hy := congrArg Prod.snd h
    simp [thirdPoint] at hy
    linarith
  rw [Closer, show (1 : ℝ) = lineDistSq (0, 1) (0, 0) (1, 0) by
    simp [lineDistSq_base]]
  rw [lineDistSq_base]
  simp only [lineDistSq, thirdPoint, orient, lengthSq, Prod.fst, Prod.snd,
    sub_zero, zero_mul, mul_zero, zero_add]
  norm_num only [one_pow, mul_one]
  have hden : 0 < (t * v - u) ^ 2 + (1 - t) ^ 2 := by
    simpa [thirdPoint, lengthSq] using lengthSq_pos hne
  rw [div_lt_one hden]
  have hnum : t * v - u - (1 - t) * (0 - u) = t * (v - u) := by ring
  rw [hnum]
  rcases hposition with hfar | hopp
  · have haux : 0 ≤ u * (u - v) := by
      nlinarith [sq_nonneg (u - v)]
    have hfirst : 0 < (1 - t) * (u ^ 2 + 1) :=
      mul_pos (by linarith) (by nlinarith [sq_nonneg u])
    have hsecond : 0 ≤ 2 * t * (u * (u - v)) := by positivity
    have hG : 0 < (1 + t) * u ^ 2 - 2 * t * u * v + 1 - t := by
      nlinarith [hfirst, hsecond]
    have hprod : 0 < (1 - t) * ((1 + t) * u ^ 2 - 2 * t * u * v + 1 - t) :=
      mul_pos (by linarith) hG
    have hdiff : (t * (v - u)) ^ 2 < (t * v - u) ^ 2 + (1 - t) ^ 2 := by
      nlinarith [hprod]
    exact hdiff
  · have hG : 0 < (1 + t) * u ^ 2 - 2 * t * u * v + 1 - t := by
      nlinarith [sq_nonneg u]
    have hprod : 0 < (1 - t) * ((1 + t) * u ^ 2 - 2 * t * u * v + 1 - t) :=
      mul_pos (by linarith) hG
    have hdiff : (t * (v - u)) ^ 2 < (t * v - u) ^ 2 + (1 - t) ^ 2 := by
      nlinarith [hprod]
    exact hdiff

lemma closer_of_outside {u v t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) (ht₁ : t ≠ 1)
    (hsign : 0 ≤ u * v) (hnear : u ^ 2 ≤ v ^ 2) : Closer u v t := by
  have huv : u ^ 2 ≤ u * v := mul_sq_le_mul_of_same_sign hsign hnear
  have hne : ((u, 0) : Point) ≠ thirdPoint v t := by
    intro h
    have hy := congrArg Prod.snd h
    simp [thirdPoint] at hy
    exact ht₁ (by linarith)
  rw [Closer]
  simp only [lineDistSq, thirdPoint, orient, lengthSq, Prod.fst, Prod.snd,
    sub_zero, zero_mul, mul_zero, zero_add]
  norm_num only [one_pow, mul_one]
  have hden : 0 < (t * v - u) ^ 2 + (1 - t) ^ 2 := by
    simpa [thirdPoint, lengthSq] using lengthSq_pos hne
  rw [div_lt_one hden]
  have hnum : t * v - u - (1 - t) * (0 - u) = t * (v - u) := by ring
  rw [hnum]
  have hcoef : u ^ 2 - 2 * u * v - 1 < 0 := by
    nlinarith [sq_nonneg u]
  rcases ht with ht | ht
  · have htprod : 0 ≤ t * (u ^ 2 - 2 * u * v - 1) :=
      mul_nonneg_of_nonpos_of_nonpos ht hcoef.le
    have hG : 0 < (1 + t) * u ^ 2 - 2 * t * u * v + 1 - t := by
      nlinarith [sq_nonneg u]
    have hprod : 0 < (1 - t) * ((1 + t) * u ^ 2 - 2 * t * u * v + 1 - t) :=
      mul_pos (by linarith) hG
    have hdiff : (t * (v - u)) ^ 2 < (t * v - u) ^ 2 + (1 - t) ^ 2 := by
      nlinarith [hprod]
    exact hdiff
  · have ht' : 1 < t := lt_of_le_of_ne ht (Ne.symm ht₁)
    have hfirst : 2 * u * (u - v) ≤ 0 := by nlinarith
    have hsecond : (t - 1) * (u ^ 2 - 2 * u * v - 1) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hcoef
    have hG : (1 + t) * u ^ 2 - 2 * t * u * v + 1 - t < 0 := by
      nlinarith [hfirst, hsecond]
    have hprod : 0 < (1 - t) * ((1 + t) * u ^ 2 - 2 * t * u * v + 1 - t) :=
      mul_pos_of_neg_of_neg (by linarith) hG
    have hdiff : (t * (v - u)) ^ 2 < (t * v - u) ^ 2 + (1 - t) ^ 2 := by
      nlinarith [hprod]
    exact hdiff

lemma two_of_three_have_nonnegative_product (x y z : ℝ) :
    0 ≤ x * y ∨ 0 ≤ x * z ∨ 0 ≤ y * z := by
  rcases le_total 0 x with hx | hx
  · rcases le_total 0 y with hy | hy
    · exact Or.inl (mul_nonneg hx hy)
    · rcases le_total 0 z with hz | hz
      · exact Or.inr (Or.inl (mul_nonneg hx hz))
      · exact Or.inr (Or.inr (mul_nonneg_of_nonpos_of_nonpos hy hz))
  · rcases le_total 0 y with hy | hy
    · rcases le_total 0 z with hz | hz
      · exact Or.inr (Or.inr (mul_nonneg hy hz))
      · exact Or.inr (Or.inl (mul_nonneg_of_nonpos_of_nonpos hx hz))
    · exact Or.inl (mul_nonneg_of_nonpos_of_nonpos hx hy)

lemma outside_of_not_inside {t : ℝ} (h : ¬ (0 < t ∧ t < 1)) : t ≤ 0 ∨ 1 ≤ t := by
  by_cases ht : t ≤ 0
  · exact Or.inl ht
  · exact Or.inr (by
      have : 0 < t := lt_of_not_ge ht
      by_contra h1
      exact h ⟨this, lt_of_not_ge h1⟩)

/-- With three distinct points on the base line and a genuine third point on
each spoke from `(0,1)`, one of the six cross-lines is closer than the base.
This is the finite ordered-field heart of the zero-order Kelly--Moser lemma. -/
lemma three_base_crossing {x y z tx ty tz : ℝ}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (htx₁ : tx ≠ 1) (hty₁ : ty ≠ 1) (htz₁ : tz ≠ 1) :
    Closer y x tx ∨ Closer z x tx ∨ Closer x y ty ∨
      Closer z y ty ∨ Closer x z tz ∨ Closer y z tz := by
  by_contra hn
  simp only [not_or] at hn
  rcases hn with ⟨h_yx, h_zx, h_xy, h_zy, h_xz, h_yz⟩
  by_cases htx : 0 < tx ∧ tx < 1
  · have hxypos : 0 < y * x := by
      by_contra h
      exact h_yx (closer_of_inside htx.1 htx.2 (Or.inr (le_of_not_gt h)))
    have hxzpos : 0 < z * x := by
      by_contra h
      exact h_zx (closer_of_inside htx.1 htx.2 (Or.inr (le_of_not_gt h)))
    have hylt : y ^ 2 < x ^ 2 := by
      by_contra h
      exact h_yx (closer_of_inside htx.1 htx.2 (Or.inl (le_of_not_gt h)))
    have hzlt : z ^ 2 < x ^ 2 := by
      by_contra h
      exact h_zx (closer_of_inside htx.1 htx.2 (Or.inl (le_of_not_gt h)))
    have hty : ¬ (0 < ty ∧ ty < 1) := by
      intro htin
      exact h_xy (closer_of_inside htin.1 htin.2 (Or.inl hylt.le))
    have htz : ¬ (0 < tz ∧ tz < 1) := by
      intro htin
      exact h_xz (closer_of_inside htin.1 htin.2 (Or.inl hzlt.le))
    have hyzsign : 0 ≤ y * z := by
      have hxx : 0 < x ^ 2 := by
        apply sq_pos_of_ne_zero
        intro hxzero
        subst x
        norm_num at hxypos
      have hprod : 0 < (y * x) * (z * x) := mul_pos hxypos hxzpos
      nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg (y * z))]
    rcases le_total (y ^ 2) (z ^ 2) with hyzsq | hzysq
    · exact h_yz (closer_of_outside (outside_of_not_inside htz) htz₁
        hyzsign hyzsq)
    · exact h_zy (closer_of_outside (outside_of_not_inside hty) hty₁
        (by simpa [mul_comm] using hyzsign) hzysq)
  · by_cases hty : 0 < ty ∧ ty < 1
    · have hyxpos : 0 < x * y := by
        by_contra h
        exact h_xy (closer_of_inside hty.1 hty.2 (Or.inr (le_of_not_gt h)))
      have hyzpos : 0 < z * y := by
        by_contra h
        exact h_zy (closer_of_inside hty.1 hty.2 (Or.inr (le_of_not_gt h)))
      have hxlt : x ^ 2 < y ^ 2 := by
        by_contra h
        exact h_xy (closer_of_inside hty.1 hty.2 (Or.inl (le_of_not_gt h)))
      have hzlt : z ^ 2 < y ^ 2 := by
        by_contra h
        exact h_zy (closer_of_inside hty.1 hty.2 (Or.inl (le_of_not_gt h)))
      have htz : ¬ (0 < tz ∧ tz < 1) := by
        intro htin
        exact h_yz (closer_of_inside htin.1 htin.2 (Or.inl hzlt.le))
      have hxzsign : 0 ≤ x * z := by
        have hprod : 0 < (x * y) * (z * y) := mul_pos hyxpos hyzpos
        by_contra h
        have : x * z < 0 := lt_of_not_ge h
        nlinarith [sq_nonneg y]
      rcases le_total (x ^ 2) (z ^ 2) with hxzsq | hzxsq
      · exact h_xz (closer_of_outside (outside_of_not_inside htz) htz₁
          hxzsign hxzsq)
      · exact h_zx (closer_of_outside (outside_of_not_inside htx) htx₁
          (by simpa [mul_comm] using hxzsign) hzxsq)
    · by_cases htz : 0 < tz ∧ tz < 1
      · have hzxpos : 0 < x * z := by
          by_contra h
          exact h_xz (closer_of_inside htz.1 htz.2 (Or.inr (le_of_not_gt h)))
        have hzypos : 0 < y * z := by
          by_contra h
          exact h_yz (closer_of_inside htz.1 htz.2 (Or.inr (le_of_not_gt h)))
        have hxlt : x ^ 2 < z ^ 2 := by
          by_contra h
          exact h_xz (closer_of_inside htz.1 htz.2 (Or.inl (le_of_not_gt h)))
        have hylt : y ^ 2 < z ^ 2 := by
          by_contra h
          exact h_yz (closer_of_inside htz.1 htz.2 (Or.inl (le_of_not_gt h)))
        have hxySign : 0 ≤ x * y := by
          have hprod : 0 < (x * z) * (y * z) := mul_pos hzxpos hzypos
          by_contra h
          have : x * y < 0 := lt_of_not_ge h
          nlinarith [sq_nonneg z]
        rcases le_total (x ^ 2) (y ^ 2) with hxysq | hyxsq
        · exact h_xy (closer_of_outside (outside_of_not_inside hty) hty₁
            hxySign hxysq)
        · exact h_yx (closer_of_outside (outside_of_not_inside htx) htx₁
            (by simpa [mul_comm] using hxySign) hyxsq)
      · rcases two_of_three_have_nonnegative_product x y z with hxy0 | hxz0 | hyz0
        · rcases le_total (x ^ 2) (y ^ 2) with hsq | hsq
          · exact h_xy (closer_of_outside (outside_of_not_inside hty) hty₁
              hxy0 hsq)
          · exact h_yx (closer_of_outside (outside_of_not_inside htx) htx₁
              (by simpa [mul_comm] using hxy0) hsq)
        · rcases le_total (x ^ 2) (z ^ 2) with hsq | hsq
          · exact h_xz (closer_of_outside (outside_of_not_inside htz) htz₁
              hxz0 hsq)
          · exact h_zx (closer_of_outside (outside_of_not_inside htx) htx₁
              (by simpa [mul_comm] using hxz0) hsq)
        · rcases le_total (y ^ 2) (z ^ 2) with hsq | hsq
          · exact h_yz (closer_of_outside (outside_of_not_inside htz) htz₁
              hyz0 hsq)
          · exact h_zy (closer_of_outside (outside_of_not_inside hty) hty₁
              (by simpa [mul_comm] using hyz0) hsq)

lemma not_ordinary_through_of_order_zero {P : Finset Point} {p v : Point}
    (hp : p ∈ P) (hv : v ∈ P) (hpv : p ≠ v) (hzero : order P p = 0) :
    {p, v} ∉ ordinaryPairs P := by
  intro hord
  have hmem : v ∈ ordinaryPartners P p :=
    mem_ordinaryPartners.mpr ⟨hv, Ne.symm hpv, hord⟩
  have hempty : ordinaryPartners P p = ∅ := Finset.card_eq_zero.mp hzero
  rw [hempty] at hmem
  simp at hmem

/-- The closest connecting line to a point of order zero is ordinary.  The
proof is the normalized six-cross-line argument above. -/
lemma closestPair_ordinary_of_order_zero (P : Finset Point)
    {p a b : Point} (hp : p ∈ P) (hzero : order P p = 0)
    (hclose : IsClosestPair P p a b) : {a, b} ∈ ordinaryPairs P := by
  classical
  have ha : a ∈ P := closestPair_left_mem hclose
  have hb : b ∈ P := closestPair_right_mem hclose
  have hab : a ≠ b := closestPair_ne hclose
  have hpoff : ¬ Collinear3 a b p := closestPair_offLine hclose
  by_contra hnord
  obtain ⟨c, hc, habc, hca, hcb⟩ :=
    exists_third_of_not_ordinary ha hb hab hnord
  have hpa : p ≠ a := by
    intro h
    subst p
    exact hpoff (by simp [Collinear3, orient])
  have hpb : p ≠ b := by
    intro h
    subst p
    exact hpoff (collinear3_refl_right a b)
  have hpc : p ≠ c := by
    intro h
    subst p
    exact hpoff habc
  have hpa_not := not_ordinary_through_of_order_zero hp ha hpa hzero
  have hpb_not := not_ordinary_through_of_order_zero hp hb hpb hzero
  have hpc_not := not_ordinary_through_of_order_zero hp hc hpc hzero
  obtain ⟨wa, hwa, hpawa, hwap, hwaa⟩ :=
    exists_third_of_not_ordinary hp ha hpa hpa_not
  obtain ⟨wb, hwb, hpbwb, hwbp, hwbb⟩ :=
    exists_third_of_not_ordinary hp hb hpb hpb_not
  obtain ⟨wc, hwc, hpcwc, hwcp, hwcc⟩ :=
    exists_third_of_not_ordinary hp hc hpc hpc_not
  let np := normalize a b p
  let T : Point → Point := fun z ↦ verticalNormalize np (normalize a b z)
  let x := (T a).1
  let y := (T b).1
  let z := (T c).1
  let tx := 1 - (T wa).2
  let ty := 1 - (T wb).2
  let tz := 1 - (T wc).2
  have hnp : np.2 ≠ 0 := (normalize_snd_ne_zero_iff hab).mpr hpoff
  have hTinj : Function.Injective T :=
    (verticalNormalize_injective hnp).comp (normalize_injective hab)
  have hTp : T p = (0, 1) := by
    simp only [T, np]
    exact verticalNormalize_self hnp
  have hNa : (normalize a b a).2 = 0 := by rw [normalize_left hab]
  have hNb : (normalize a b b).2 = 0 := by rw [normalize_right hab]
  have hNc : (normalize a b c).2 = 0 := by
    simp only [normalize, Prod.snd]
    rw [show orient a b c = 0 by exact habc]
    simp
  have hTa : T a = (x, 0) := by
    apply Prod.ext
    · rfl
    · exact verticalNormalize_base_snd hNa
  have hTb : T b = (y, 0) := by
    apply Prod.ext
    · rfl
    · exact verticalNormalize_base_snd hNb
  have hTc : T c = (z, 0) := by
    apply Prod.ext
    · rfl
    · exact verticalNormalize_base_snd hNc
  have normalized_collinear (u v w : Point) (hcol : Collinear3 u v w) :
      Collinear3 (normalize a b u) (normalize a b v) (normalize a b w) := by
    rw [Collinear3, orient_normalize hab]
    simp [Collinear3] at hcol
    simp [hcol]
  have hTwa : T wa = thirdPoint x tx := by
    change verticalNormalize np (normalize a b wa) = _
    rw [verticalNormalize_eq_thirdPoint hnp hNa
      (normalized_collinear p a wa hpawa)]
  have hTwb : T wb = thirdPoint y ty := by
    change verticalNormalize np (normalize a b wb) = _
    rw [verticalNormalize_eq_thirdPoint hnp hNb
      (normalized_collinear p b wb hpbwb)]
  have hpcwc' : Collinear3 p c wc := hpcwc
  have hTwc : T wc = thirdPoint z tz := by
    change verticalNormalize np (normalize a b wc) = _
    rw [verticalNormalize_eq_thirdPoint hnp hNc
      (normalized_collinear p c wc hpcwc')]
  have hxy : x ≠ y := by
    intro h
    apply hab
    apply hTinj
    rw [hTa, hTb, h]
  have hxz : x ≠ z := by
    intro h
    apply Ne.symm hca
    apply hTinj
    rw [hTa, hTc, h]
  have hyz : y ≠ z := by
    intro h
    apply Ne.symm hcb
    apply hTinj
    rw [hTb, hTc, h]
  have htx₀ : tx ≠ 0 := by
    intro ht
    apply hwap
    apply hTinj
    rw [hTwa, hTp, ht]
    simp [thirdPoint]
  have hty₀ : ty ≠ 0 := by
    intro ht
    apply hwbp
    apply hTinj
    rw [hTwb, hTp, ht]
    simp [thirdPoint]
  have htz₀ : tz ≠ 0 := by
    intro ht
    apply hwcp
    apply hTinj
    rw [hTwc, hTp, ht]
    simp [thirdPoint]
  have htx₁ : tx ≠ 1 := by
    intro ht
    apply hwaa
    apply hTinj
    rw [hTwa, hTa, ht]
    simp [thirdPoint]
  have hty₁ : ty ≠ 1 := by
    intro ht
    apply hwbb
    apply hTinj
    rw [hTwb, hTb, ht]
    simp [thirdPoint]
  have htz₁ : tz ≠ 1 := by
    intro ht
    apply hwcc
    apply hTinj
    rw [hTwc, hTc, ht]
    simp [thirdPoint]
  have cross_contradiction {u v w : Point} {U V t : ℝ}
      (hu : u ∈ P) (hw : w ∈ P) (huv : U ≠ V)
      (hTu : T u = (U, 0)) (hTv : T v = (V, 0))
      (hTw : T w = thirdPoint V t) (ht₀ : t ≠ 0) (ht₁ : t ≠ 1)
      (hcloser : Closer U V t) : False := by
    have huw : u ≠ w := by
      intro huw
      subst w
      have heq : ((U, 0) : Point) = thirdPoint V t := hTu.symm.trans hTw
      have heq2 := congrArg Prod.snd heq
      simp [thirdPoint] at heq2
      exact ht₁ (by linarith)
    have hoff : ¬ Collinear3 u w p := by
      intro hcol
      have hcolN := normalized_collinear u w p hcol
      have hcolT : Collinear3 (T u) (T w) (T p) := by
        change Collinear3 (verticalNormalize np (normalize a b u))
          (verticalNormalize np (normalize a b w))
          (verticalNormalize np (normalize a b p))
        rw [Collinear3, orient_verticalNormalize hnp]
        simp [Collinear3] at hcolN
        simp [hcolN]
      rw [hTu, hTw, hTp] at hcolT
      simp only [Collinear3, orient, thirdPoint, Prod.fst, Prod.snd,
        sub_zero, zero_mul, mul_zero, zero_add] at hcolT
      have : t * (V - U) ≠ 0 := mul_ne_zero ht₀ (sub_ne_zero.mpr (Ne.symm huv))
      exact this (by nlinarith)
    have hcand : (u, w) ∈ offLinePairs P p :=
      mem_offLinePairs.mpr ⟨hu, hw, huw, hoff⟩
    have hmin := hclose.2 hcand
    have hvert := lineDistSq_verticalNormalize
      (p := np) (x := normalize a b p) (a := normalize a b u)
      (b := normalize a b w) hnp ((normalize_injective hab).ne huw)
    change lineDistSq (T p) (T u) (T w) = _ at hvert
    rw [hTp, hTu, hTw] at hvert
    have hNcloser : lineDistSq (normalize a b p) (normalize a b u)
        (normalize a b w) < np.2 ^ 2 := by
      have hdiv : lineDistSq (normalize a b p) (normalize a b u)
          (normalize a b w) / np.2 ^ 2 < 1 := by
        rw [← hvert]
        exact hcloser
      exact (div_lt_one (sq_pos_of_ne_zero hnp)).mp hdiv
    have hbaseN : lineDistSq (normalize a b p) (normalize a b a)
        (normalize a b b) = np.2 ^ 2 := by
      rw [normalize_left hab, normalize_right hab]
      exact lineDistSq_base _
    have hscaled : lineDistSq p u w / lengthSq a b <
        lineDistSq p a b / lengthSq a b := by
      rw [← lineDistSq_normalize hab p u w huw,
        ← lineDistSq_normalize hab p a b hab]
      rw [hbaseN]
      exact hNcloser
    have : lineDistSq p u w < lineDistSq p a b :=
      (div_lt_div_iff_of_pos_right (lengthSq_pos hab)).mp hscaled
    exact (not_lt_of_ge hmin) this
  rcases three_base_crossing hxy hxz hyz htx₁ hty₁ htz₁ with
      h | h | h | h | h | h
  · exact cross_contradiction (U := y) (V := x) (t := tx)
      hb hwa (Ne.symm hxy) hTb hTa hTwa htx₀ htx₁ h
  · exact cross_contradiction (U := z) (V := x) (t := tx)
      hc hwa (Ne.symm hxz) hTc hTa hTwa htx₀ htx₁ h
  · exact cross_contradiction (U := x) (V := y) (t := ty)
      ha hwb hxy hTa hTb hTwb hty₀ hty₁ h
  · exact cross_contradiction (U := z) (V := y) (t := ty)
      hc hwb (Ne.symm hyz) hTc hTb hTwb hty₀ hty₁ h
  · exact cross_contradiction (U := x) (V := z) (t := tz)
      ha hwc hxz hTa hTc hTwc htz₀ htz₁ h
  · exact cross_contradiction (U := y) (V := z) (t := tz)
      hb hwc hyz hTb hTc hTwc htz₀ htz₁ h

/-! ### The finite double count -/

/-- A deterministic closest ordered pair.  The irrelevant branch is used
only when `p ∉ P`; every theorem below evaluates the definition on `p ∈ P`. -/
noncomputable def chosenClosestPair (P : Finset Point) (hP : HasNoncollinearTriple P)
    (p : Point) : Point × Point := by
  classical
  by_cases hp : p ∈ P
  · exact Classical.choose (show ∃ ab : Point × Point,
      IsClosestPair P p ab.1 ab.2 by
        obtain ⟨a, b, hab⟩ := exists_closestPair P hP hp
        exact ⟨(a, b), hab⟩)
  · exact (p, p)

lemma chosenClosestPair_spec (P : Finset Point) (hP : HasNoncollinearTriple P)
    {p : Point} (hp : p ∈ P) :
    IsClosestPair P p (chosenClosestPair P hP p).1 (chosenClosestPair P hP p).2 := by
  classical
  rw [chosenClosestPair]
  split <;> rename_i h
  · exact Classical.choose_spec (show ∃ ab : Point × Point,
      IsClosestPair P p ab.1 ab.2 by
        obtain ⟨a, b, hab⟩ := exists_closestPair P hP hp
        exact ⟨(a, b), hab⟩)
  · exact (h hp).elim

def zeroOrderPoints (P : Finset Point) : Finset Point :=
  P.filter fun p ↦ order P p = 0

def nonzeroOrderPoints (P : Finset Point) : Finset Point :=
  P.filter fun p ↦ order P p ≠ 0

@[simp] lemma mem_zeroOrderPoints {P : Finset Point} {p : Point} :
    p ∈ zeroOrderPoints P ↔ p ∈ P ∧ order P p = 0 := by
  simp [zeroOrderPoints]

@[simp] lemma mem_nonzeroOrderPoints {P : Finset Point} {p : Point} :
    p ∈ nonzeroOrderPoints P ↔ p ∈ P ∧ order P p ≠ 0 := by
  simp [nonzeroOrderPoints]

lemma zero_nonzero_partition (P : Finset Point) :
    zeroOrderPoints P ∪ nonzeroOrderPoints P = P := by
  ext p
  simp only [Finset.mem_union, mem_zeroOrderPoints, mem_nonzeroOrderPoints]
  tauto

lemma zero_nonzero_disjoint (P : Finset Point) :
    Disjoint (zeroOrderPoints P) (nonzeroOrderPoints P) := by
  apply Finset.disjoint_left.mpr
  intro p hp₀ hp₁
  exact (mem_nonzeroOrderPoints.mp hp₁).2 (mem_zeroOrderPoints.mp hp₀).2

/-- Incidences `(p,e)` between an ordinary pair and either of its points. -/
def ordinaryIncidences (P : Finset Point) : Finset (Point × Finset Point) := by
  classical
  exact (ordinaryPairs P).biUnion fun e ↦ e.image fun p ↦ (p, e)

lemma ordinaryIncidences_card (P : Finset Point) :
    (ordinaryIncidences P).card = 2 * ordinaryCount P := by
  classical
  have hdisj : ((ordinaryPairs P : Finset (Finset Point)) : Set (Finset Point)).PairwiseDisjoint
      (fun e ↦ e.image fun p ↦ (p, e)) := by
    intro e he f hf hef
    change Disjoint (e.image fun p ↦ (p, e)) (f.image fun p ↦ (p, f))
    rw [Finset.disjoint_left]
    intro pe hpe hpf
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hpe
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hpf
    have : e = f := (congrArg Prod.snd heq).symm
    exact hef this
  rw [ordinaryIncidences, Finset.card_biUnion hdisj]
  calc
    ∑ e ∈ ordinaryPairs P, (e.image fun p ↦ (p, e)).card =
        ∑ _e ∈ ordinaryPairs P, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.card_image_of_injective]
      · exact ordinaryPair_card he
      · intro p q hpq
        exact congrArg Prod.fst hpq
    _ = 2 * ordinaryCount P := by simp [ordinaryCount, Nat.mul_comm]

lemma nonzeroOrderPoints_card_le (P : Finset Point) :
    (nonzeroOrderPoints P).card ≤ 2 * ordinaryCount P := by
  classical
  have hsub : nonzeroOrderPoints P ⊆ (ordinaryIncidences P).image Prod.fst := by
    intro p hp
    have hp' := (mem_nonzeroOrderPoints.mp hp)
    have hnonempty : (ordinaryPartners P p).Nonempty := by
      rw [← Finset.card_pos]
      exact Nat.pos_of_ne_zero hp'.2
    obtain ⟨q, hq⟩ := hnonempty
    have hq' := mem_ordinaryPartners.mp hq
    apply Finset.mem_image.mpr
    refine ⟨(p, {p, q}), ?_, rfl⟩
    rw [ordinaryIncidences]
    apply Finset.mem_biUnion.mpr
    refine ⟨{p, q}, hq'.2.2, ?_⟩
    exact Finset.mem_image.mpr ⟨p, by simp, rfl⟩
  calc
    (nonzeroOrderPoints P).card ≤ ((ordinaryIncidences P).image Prod.fst).card :=
      Finset.card_le_card hsub
    _ ≤ (ordinaryIncidences P).card := Finset.card_image_le
    _ = 2 * ordinaryCount P := ordinaryIncidences_card P

lemma chosen_line_ordinary (P : Finset Point) (hP : HasNoncollinearTriple P)
    {p : Point} (hp : p ∈ zeroOrderPoints P) :
    ({(chosenClosestPair P hP p).1, (chosenClosestPair P hP p).2} : Finset Point) ∈
      ordinaryPairs P := by
  exact closestPair_ordinary_of_order_zero P (mem_zeroOrderPoints.mp hp).1
    (mem_zeroOrderPoints.mp hp).2 (chosenClosestPair_spec P hP (mem_zeroOrderPoints.mp hp).1)

lemma pair_eq_pair_or_swap {u v a b : Point} (huv : u ≠ v) (hab : a ≠ b)
    (h : ({u, v} : Finset Point) = {a, b}) :
    (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  have hu : u = a ∨ u = b := by
    have : u ∈ ({a, b} : Finset Point) := by rw [← h]; simp
    simpa using this
  have hv : v = a ∨ v = b := by
    have : v ∈ ({a, b} : Finset Point) := by rw [← h]; simp
    simpa using this
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (huv rfl).elim
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact (huv rfl).elim

lemma chosen_line_fiber_card_le_eight (P : Finset Point)
    (hP : HasNoncollinearTriple P) {e : Finset Point} (he : e ∈ ordinaryPairs P) :
    ((zeroOrderPoints P).filter fun p ↦
      ({(chosenClosestPair P hP p).1, (chosenClosestPair P hP p).2} : Finset Point) = e).card ≤ 8 := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (ordinaryPair_card he)
  let fiber := (zeroOrderPoints P).filter fun p ↦
    ({(chosenClosestPair P hP p).1, (chosenClosestPair P hP p).2} : Finset Point) = {a, b}
  have hsub : fiber ⊆ attachedPoints P a b ∪ attachedPoints P b a := by
    intro p hp
    have hpfilter := Finset.mem_filter.mp hp
    have hspec := chosenClosestPair_spec P hP (mem_zeroOrderPoints.mp hpfilter.1).1
    have horient := pair_eq_pair_or_swap (closestPair_ne hspec) hab hpfilter.2
    rcases horient with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · apply Finset.mem_union_left
      exact mem_attachedPoints.mpr ⟨(mem_zeroOrderPoints.mp hpfilter.1).1, by simpa [h₁, h₂] using hspec⟩
    · apply Finset.mem_union_right
      exact mem_attachedPoints.mpr ⟨(mem_zeroOrderPoints.mp hpfilter.1).1, by simpa [h₁, h₂] using hspec⟩
  calc
    fiber.card ≤ (attachedPoints P a b ∪ attachedPoints P b a).card :=
      Finset.card_le_card hsub
    _ ≤ (attachedPoints P a b).card + (attachedPoints P b a).card :=
      Finset.card_union_le _ _
    _ ≤ 4 + 4 := Nat.add_le_add (attachedPoints_card_le_four P a b)
      (attachedPoints_card_le_four P b a)
    _ = 8 := by norm_num

lemma zeroOrderPoints_card_le (P : Finset Point) (hP : HasNoncollinearTriple P) :
    (zeroOrderPoints P).card ≤ 8 * ordinaryCount P := by
  classical
  let f : Point → Finset Point := fun p ↦
    {(chosenClosestPair P hP p).1, (chosenClosestPair P hP p).2}
  have hmaps : ∀ p ∈ zeroOrderPoints P, f p ∈ ordinaryPairs P := by
    intro p hp
    exact chosen_line_ordinary P hP hp
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    ∑ e ∈ ordinaryPairs P,
        ((zeroOrderPoints P).filter fun p ↦ f p = e).card ≤
        ∑ _e ∈ ordinaryPairs P, 8 := by
      apply Finset.sum_le_sum
      intro e he
      exact chosen_line_fiber_card_le_eight P hP he
    _ = 8 * ordinaryCount P := by simp [ordinaryCount, Nat.mul_comm]

/-- A fully explicit linear Kelly--Moser-style bound.  The classical sharper
bookkeeping gives `7m ≥ 3n`; the closest-line fiber argument formalized here
already gives the complete asymptotic resolution `n ≤ 10m`. -/
theorem ten_mul_ordinaryCount_ge_card (P : Finset Point)
    (hP : HasNoncollinearTriple P) : P.card ≤ 10 * ordinaryCount P := by
  have hpartition := zero_nonzero_partition P
  have hdisj := zero_nonzero_disjoint P
  have hcard : P.card = (zeroOrderPoints P).card + (nonzeroOrderPoints P).card := by
    calc
      P.card = (zeroOrderPoints P ∪ nonzeroOrderPoints P).card :=
        congrArg Finset.card hpartition.symm
      _ = _ := Finset.card_union_of_disjoint hdisj
  rw [hcard]
  have hz := zeroOrderPoints_card_le P hP
  have hn := nonzeroOrderPoints_card_le P
  omega

/-- The set of attainable ordinary-line counts for noncollinear `n`-point sets. -/
def attainableCounts (n : ℕ) : Set ℕ :=
  {m | ∃ P : Finset Point,
    P.card = n ∧ HasNoncollinearTriple P ∧ ordinaryCount P = m}

/-- The function `f(n)` in Problem 210.  On the irrelevant values `n < 3`,
the infimum of the empty attainable set is the natural-number default `0`. -/
def ordinaryMinimum (n : ℕ) : ℕ := sInf (attainableCounts n)

/-! ### Nonemptiness, the near-pencil upper bound, and divergence -/

def basePoints (n : ℕ) : Finset Point :=
  (Finset.range (n - 1)).image fun j : ℕ ↦ ((j : ℝ), (0 : ℝ))

def apex : Point := (0, 1)

def nearPencil (n : ℕ) : Finset Point := insert apex (basePoints n)

lemma basePoints_card (n : ℕ) : (basePoints n).card = n - 1 := by
  classical
  rw [basePoints, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro i j h
    have h₁ := congrArg Prod.fst h
    norm_num at h₁
    exact_mod_cast h₁

lemma apex_not_mem_basePoints (n : ℕ) : apex ∉ basePoints n := by
  classical
  intro h
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
  have h₂ := congrArg Prod.snd heq
  norm_num [apex] at h₂

lemma nearPencil_card {n : ℕ} (hn : 1 ≤ n) : (nearPencil n).card = n := by
  rw [nearPencil, Finset.card_insert_of_notMem (apex_not_mem_basePoints n), basePoints_card]
  omega

lemma base_zero_mem {n : ℕ} (hn : 2 ≤ n) : (0, 0) ∈ basePoints n := by
  classical
  rw [basePoints]
  apply Finset.mem_image.mpr
  refine ⟨0, ?_, by norm_num⟩
  exact Finset.mem_range.mpr (by omega)

lemma base_one_mem {n : ℕ} (hn : 3 ≤ n) : (1, 0) ∈ basePoints n := by
  classical
  rw [basePoints]
  apply Finset.mem_image.mpr
  refine ⟨1, ?_, by norm_num⟩
  exact Finset.mem_range.mpr (by omega)

lemma nearPencil_noncollinear {n : ℕ} (hn : 3 ≤ n) :
    HasNoncollinearTriple (nearPencil n) := by
  refine ⟨(0, 0), ?_, (1, 0), ?_, apex, ?_, ?_⟩
  · exact Finset.mem_insert_of_mem (base_zero_mem (by omega))
  · exact Finset.mem_insert_of_mem (base_one_mem hn)
  · exact Finset.mem_insert_self _ _
  · norm_num [Collinear3, orient, apex]

lemma attainableCounts_nonempty {n : ℕ} (hn : 3 ≤ n) :
    (attainableCounts n).Nonempty := by
  refine ⟨ordinaryCount (nearPencil n), nearPencil n, ?_, nearPencil_noncollinear hn, rfl⟩
  exact nearPencil_card (by omega)

lemma basePoints_snd_zero {n : ℕ} {p : Point} (hp : p ∈ basePoints n) : p.2 = 0 := by
  classical
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
  rfl

lemma basePoints_collinear {n : ℕ} {a b c : Point}
    (ha : a ∈ basePoints n) (hb : b ∈ basePoints n) (hc : c ∈ basePoints n) :
    Collinear3 a b c := by
  simp only [Collinear3, orient, basePoints_snd_zero ha, basePoints_snd_zero hb,
    basePoints_snd_zero hc]
  ring

def spokePairs (n : ℕ) : Finset (Finset Point) := by
  classical
  exact (basePoints n).image fun q ↦ {apex, q}

lemma spokePairs_card (n : ℕ) : (spokePairs n).card = n - 1 := by
  classical
  rw [spokePairs, Finset.card_image_of_injOn]
  · exact basePoints_card n
  · intro q hq r hr hqr
    have hqa : q ≠ apex := by
      intro h
      subst q
      exact apex_not_mem_basePoints n hq
    have hra : r ≠ apex := by
      intro h
      subst r
      exact apex_not_mem_basePoints n hr
    have horient := pair_eq_pair_or_swap (Ne.symm hqa) (Ne.symm hra) hqr
    rcases horient with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact (hra h.symm).elim

lemma ordinaryPairs_nearPencil_subset_spokes {n : ℕ} (hn : 4 ≤ n) :
    ordinaryPairs (nearPencil n) ⊆ spokePairs n := by
  classical
  intro e he
  have hecard := ordinaryPair_card he
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hecard
  have hsub := ordinaryPair_subset he
  have huP : u ∈ nearPencil n := hsub (by simp)
  have hvP : v ∈ nearPencil n := hsub (by simp)
  have hcontains : apex = u ∨ apex = v := by
    by_contra h
    push_neg at h
    have huB : u ∈ basePoints n := by
      simp only [nearPencil, Finset.mem_insert] at huP
      exact huP.resolve_left (Ne.symm h.1)
    have hvB : v ∈ basePoints n := by
      simp only [nearPencil, Finset.mem_insert] at hvP
      exact hvP.resolve_left (Ne.symm h.2)
    have hbaseSub : basePoints n ⊆ ({u, v} : Finset Point) := by
      intro w hw
      exact ordinaryPair_collinear_mem he (by simp) (by simp) huv
        (Finset.mem_insert_of_mem hw)
        (basePoints_collinear huB hvB hw)
    have := Finset.card_le_card hbaseSub
    rw [basePoints_card] at this
    simp [huv] at this
    omega
  rcases hcontains with hau | hav
  · subst u
    have hvB : v ∈ basePoints n := by
      simp only [nearPencil, Finset.mem_insert] at hvP
      exact hvP.resolve_left (by exact Ne.symm huv)
    exact Finset.mem_image.mpr ⟨v, hvB, rfl⟩
  · subst v
    have huB : u ∈ basePoints n := by
      simp only [nearPencil, Finset.mem_insert] at huP
      exact huP.resolve_left huv
    refine Finset.mem_image.mpr ⟨u, huB, ?_⟩
    ext q
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

lemma ordinaryCount_nearPencil_le {n : ℕ} (hn : 4 ≤ n) :
    ordinaryCount (nearPencil n) ≤ n - 1 := by
  rw [ordinaryCount, ← spokePairs_card n]
  exact Finset.card_le_card (ordinaryPairs_nearPencil_subset_spokes hn)

theorem ordinaryMinimum_lower {n : ℕ} (hn : 3 ≤ n) :
    n ≤ 10 * ordinaryMinimum n := by
  have hmem : ordinaryMinimum n ∈ attainableCounts n :=
    Nat.sInf_mem (attainableCounts_nonempty hn)
  obtain ⟨P, hcard, hnoncol, hcount⟩ := hmem
  have hbound := ten_mul_ordinaryCount_ge_card P hnoncol
  omega

theorem ordinaryMinimum_upper {n : ℕ} (hn : 4 ≤ n) :
    ordinaryMinimum n ≤ n - 1 := by
  have hmem : ordinaryCount (nearPencil n) ∈ attainableCounts n :=
    ⟨nearPencil n, nearPencil_card (by omega), nearPencil_noncollinear (by omega), rfl⟩
  exact (Nat.sInf_le hmem).trans (ordinaryCount_nearPencil_le hn)

/-- Resolution of Erdős Problem 210: the minimum number of ordinary lines
tends to infinity. -/
theorem erdos_210 : Filter.Tendsto ordinaryMinimum Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  refine ⟨10 * B + 3, ?_⟩
  intro n hn
  have hn3 : 3 ≤ n := by omega
  have hlower := ordinaryMinimum_lower hn3
  omega

/-- The quantitative answer: `f(n)` has linear order of growth. -/
theorem erdos_210_linear_bounds {n : ℕ} (hn : 4 ≤ n) :
    n ≤ 10 * ordinaryMinimum n ∧ ordinaryMinimum n ≤ n - 1 :=
  ⟨ordinaryMinimum_lower (by omega), ordinaryMinimum_upper hn⟩

#print axioms erdos_210

end Erdos210
