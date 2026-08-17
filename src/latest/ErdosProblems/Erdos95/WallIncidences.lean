/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.LineFamilies

/-!
# Incidences with a partition wall

For a polynomial `Q`, every line not contained in `Z(Q)` contributes at
most `degree Q` incidences with any finite point set on the wall.  Combined
with richness, this bounds wall points which are not already rich in the
subfamily contained in an irreducible wall component.
-/

open scoped BigOperators

namespace Erdos95.WallIncidences

open Erdos95.Algebraic Erdos95.ES Erdos95.LineFamilies

abbrev LineIndex := PlanePoint × PlanePoint
abbrev Poly3 := MvPolynomial (Fin 3) ℝ

private theorem linePoint_eq_base_add (a b : PlanePoint) (t : ℝ) :
    (fun i ↦ linePoint a b 0 i + t * lineDirection a b i) =
      linePoint a b t := by
  funext i
  fin_cases i <;> simp [linePoint, lineDirection] <;> ring

theorem mem_intersectionPoints_of_two_lines
    {L : Finset LineIndex} {x : Space3} {l m : LineIndex}
    (hl : l ∈ linesThrough L x) (hm : m ∈ linesThrough L x)
    (hlm : l ≠ m) : x ∈ intersectionPoints L := by
  classical
  unfold intersectionPoints
  apply Finset.mem_image.mpr
  let z : LineIndex × LineIndex := (l, m)
  have hint : Intersects l.1 l.2 m.1 m.2 :=
    ⟨x, (mem_linesThrough_iff.mp hl).2, (mem_linesThrough_iff.mp hm).2⟩
  have hz : z ∈ intersectingPairs L := by
    unfold intersectingPairs z
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_linesThrough_iff.mp hl).1, (mem_linesThrough_iff.mp hm).1⟩,
      hlm, hint⟩
  refine ⟨z, hz, ?_⟩
  exact intersection_unique (p := l.1) (q := l.2) (r := m.1) (s := m.2)
    hlm (pairIntersection_on_first (z := z) hint)
    (pairIntersection_on_second (z := z) hint)
    (mem_linesThrough_iff.mp hl).2 (mem_linesThrough_iff.mp hm).2

/-- Two incident lines suffice to put a point into the finite intersection
point set. -/
theorem mem_richPoints_of_two_le_card_linesThrough
    {L : Finset LineIndex} {x : Space3} {r : ℕ} (hr : 2 ≤ r)
    (hx : r ≤ (linesThrough L x).card) : x ∈ richPoints L r := by
  classical
  have hone : 1 < (linesThrough L x).card := lt_of_lt_of_le (by omega) hx
  obtain ⟨l, m, hl, hm, hlm⟩ := Finset.one_lt_card_iff.mp hone
  exact mem_richPoints_iff.mpr
    ⟨mem_intersectionPoints_of_two_lines hl hm hlm, hx⟩

/-- Lines through `x` which are not contained in `Z(Q)`. -/
noncomputable def externalLinesThrough (L : Finset LineIndex)
    (Q : Poly3) (x : Space3) : Finset LineIndex := by
  classical
  exact (linesThrough L x).filter fun l ↦ ¬LineContained Q
    (linePoint l.1 l.2 0) (lineDirection l.1 l.2)

/-- Lines through `x` which are contained in `Z(Q)`. -/
noncomputable def internalLinesThrough (L : Finset LineIndex)
    (Q : Poly3) (x : Space3) : Finset LineIndex := by
  classical
  exact (linesThrough L x).filter fun l ↦ LineContained Q
    (linePoint l.1 l.2 0) (lineDirection l.1 l.2)

theorem linesThrough_surfaceLines (L : Finset LineIndex) (Q : Poly3)
    (x : Space3) :
    linesThrough (surfaceLines L Q) x =
      internalLinesThrough L Q x := by
  classical
  ext l
  simp only [mem_linesThrough_iff, mem_surfaceLines_iff,
    internalLinesThrough, Finset.mem_filter]
  tauto

theorem card_external_add_card_surface (L : Finset LineIndex)
    (Q : Poly3) (x : Space3) :
    (externalLinesThrough L Q x).card +
      (linesThrough (surfaceLines L Q) x).card =
        (linesThrough L x).card := by
  classical
  rw [linesThrough_surfaceLines]
  unfold externalLinesThrough internalLinesThrough
  simpa only [not_not] using
    (Finset.card_filter_add_card_filter_not
      (s := linesThrough L x)
      (fun l ↦ ¬LineContained Q
        (linePoint l.1 l.2 0) (lineDirection l.1 l.2)))

theorem richness_loss_le_card_external
    {L : Finset LineIndex} {Q : Poly3} {x : Space3}
    {r r' : ℕ} (hr' : 2 ≤ r')
    (hxrich : r ≤ (linesThrough L x).card)
    (hxnot : x ∉ richPoints (surfaceLines L Q) r') :
    r - r' ≤ (externalLinesThrough L Q x).card := by
  have hcontained : (linesThrough (surfaceLines L Q) x).card < r' := by
    by_contra hnot
    have hge : r' ≤ (linesThrough (surfaceLines L Q) x).card := by omega
    exact hxnot (mem_richPoints_of_two_le_card_linesThrough hr' hge)
  have hsum := card_external_add_card_surface L Q x
  omega

/-- The sharp integral form of the richness loss.  Since failure of
`r'`-richness means that at most `r' - 1` contained lines pass through the
point, the number of external lines is at least `r - (r' - 1)`. -/
theorem richness_strict_loss_le_card_external
    {L : Finset LineIndex} {Q : Poly3} {x : Space3}
    {r r' : ℕ} (hr' : 2 ≤ r')
    (hxrich : r ≤ (linesThrough L x).card)
    (hxnot : x ∉ richPoints (surfaceLines L Q) r') :
    r - (r' - 1) ≤ (externalLinesThrough L Q x).card := by
  have hcontained : (linesThrough (surfaceLines L Q) x).card < r' := by
    by_contra hnot
    have hge : r' ≤ (linesThrough (surfaceLines L Q) x).card := by omega
    exact hxnot (mem_richPoints_of_two_le_card_linesThrough hr' hge)
  have hsum := card_external_add_card_surface L Q x
  omega

/-- Points of `S` lying on both a fixed line and the surface `Z(Q)`. -/
noncomputable def pointsOnLineSurface (S : Finset Space3)
    (l : LineIndex) (Q : Poly3) : Finset Space3 := by
  classical
  exact S.filter fun x ↦
    OnLine l.1 l.2 x ∧ MvPolynomial.eval x Q = 0

theorem card_pointsOnLineSurface_le
    (S : Finset Space3) (l : LineIndex) (Q : Poly3)
    (hline : ¬LineContained Q (linePoint l.1 l.2 0)
      (lineDirection l.1 l.2)) :
    (pointsOnLineSurface S l Q).card ≤ Q.totalDegree := by
  classical
  let parameter : Space3 → ℝ := fun x ↦ x 2
  let T := (pointsOnLineSurface S l Q).image parameter
  have hinj : Set.InjOn parameter (pointsOnLineSurface S l Q) := by
    intro x hx y hy hxy
    have hxline := (Finset.mem_filter.mp hx).2.1
    have hyline := (Finset.mem_filter.mp hy).2.1
    obtain ⟨s, rfl⟩ := hxline
    obtain ⟨t, rfl⟩ := hyline
    have hst : s = t := by simpa [parameter, linePoint] using hxy
    rw [hst]
  have hcard : T.card = (pointsOnLineSurface S l Q).card :=
    Finset.card_image_iff.mpr hinj
  have hzero : ∀ t ∈ T,
      MvPolynomial.eval
        (fun i ↦ linePoint l.1 l.2 0 i + t * lineDirection l.1 l.2 i) Q = 0 := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    have hxdata := Finset.mem_filter.mp hx
    obtain ⟨s, rfl⟩ := hxdata.2.1
    have hs : linePoint l.1 l.2 s 2 = s := by simp [linePoint]
    simp only [parameter, hs]
    rw [linePoint_eq_base_add]
    exact hxdata.2.2
  rw [← hcard]
  exact card_line_zeros_le_totalDegree Q
    (linePoint l.1 l.2 0) (lineDirection l.1 l.2) T
    (by
      intro hzero
      exact hline hzero) hzero

/-- External line incidences of wall points. -/
noncomputable def externalIncidences (S : Finset Space3)
    (L : Finset LineIndex) (Q : Poly3) :
    Finset (Σ _x : Space3, LineIndex) := by
  classical
  exact S.sigma fun x ↦ externalLinesThrough L Q x

theorem card_externalIncidences_le (S : Finset Space3)
    (L : Finset LineIndex) (Q : Poly3)
    (hwall : ∀ x ∈ S, MvPolynomial.eval x Q = 0) :
    (externalIncidences S L Q).card ≤ Q.totalDegree * L.card := by
  classical
  rw [externalIncidences, Finset.card_sigma]
  have hrewrite :
      (∑ x ∈ S, (externalLinesThrough L Q x).card) =
        ∑ x ∈ S, ∑ l ∈ L,
          if OnLine l.1 l.2 x ∧ ¬LineContained Q
              (linePoint l.1 l.2 0) (lineDirection l.1 l.2)
          then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [externalLinesThrough, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [linesThrough, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hon : OnLine l.1 l.2 x <;>
      by_cases hext : ¬LineContained Q (linePoint l.1 l.2 0)
        (lineDirection l.1 l.2) <;> simp [hon, hext]
  rw [hrewrite, Finset.sum_comm]
  calc
    (∑ l ∈ L, ∑ x ∈ S,
        if OnLine l.1 l.2 x ∧ ¬LineContained Q
            (linePoint l.1 l.2 0) (lineDirection l.1 l.2)
        then 1 else 0) ≤
      ∑ _l ∈ L, Q.totalDegree := by
        apply Finset.sum_le_sum
        intro l hl
        by_cases hline : LineContained Q (linePoint l.1 l.2 0)
            (lineDirection l.1 l.2)
        · simp [hline]
        · have hsum : (∑ x ∈ S,
              if OnLine l.1 l.2 x ∧ ¬LineContained Q
                  (linePoint l.1 l.2 0) (lineDirection l.1 l.2)
              then 1 else 0) = (pointsOnLineSurface S l Q).card := by
            rw [pointsOnLineSurface, Finset.card_eq_sum_ones,
              Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro x hx
            simp [hline, hwall x hx]
          rw [hsum]
          exact card_pointsOnLineSurface_le S l Q hline
    _ = Q.totalDegree * L.card := by simp [Nat.mul_comm]

theorem mul_card_le_card_externalIncidences
    {S : Finset Space3} {L : Finset LineIndex} {Q : Poly3}
    {r r' : ℕ} (hr' : 2 ≤ r')
    (hSrich : ∀ x ∈ S, r ≤ (linesThrough L x).card)
    (hSnot : ∀ x ∈ S, x ∉ richPoints (surfaceLines L Q) r') :
    (r - r') * S.card ≤ (externalIncidences S L Q).card := by
  rw [externalIncidences, Finset.card_sigma]
  calc
    (r - r') * S.card = ∑ _x ∈ S, (r - r') := by
      simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, (externalLinesThrough L Q x).card :=
      Finset.sum_le_sum fun x hx ↦
        richness_loss_le_card_external hr' (hSrich x hx) (hSnot x hx)

theorem strict_loss_mul_card_le_card_externalIncidences
    {S : Finset Space3} {L : Finset LineIndex} {Q : Poly3}
    {r r' : ℕ} (hr' : 2 ≤ r')
    (hSrich : ∀ x ∈ S, r ≤ (linesThrough L x).card)
    (hSnot : ∀ x ∈ S, x ∉ richPoints (surfaceLines L Q) r') :
    (r - (r' - 1)) * S.card ≤ (externalIncidences S L Q).card := by
  rw [externalIncidences, Finset.card_sigma]
  calc
    (r - (r' - 1)) * S.card = ∑ _x ∈ S, (r - (r' - 1)) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, (externalLinesThrough L Q x).card :=
      Finset.sum_le_sum fun x hx ↦
        richness_strict_loss_le_card_external hr' (hSrich x hx) (hSnot x hx)

/-- Denominator-free wall estimate for one irreducible component. -/
theorem richness_loss_mul_card_le_degree_mul_lines
    {S : Finset Space3} {L : Finset LineIndex} {Q : Poly3}
    {r r' : ℕ} (hr' : 2 ≤ r')
    (hSrich : ∀ x ∈ S, r ≤ (linesThrough L x).card)
    (hSnot : ∀ x ∈ S, x ∉ richPoints (surfaceLines L Q) r')
    (hwall : ∀ x ∈ S, MvPolynomial.eval x Q = 0) :
    (r - r') * S.card ≤ Q.totalDegree * L.card :=
  (mul_card_le_card_externalIncidences hr' hSrich hSnot).trans
    (card_externalIncidences_le S L Q hwall)

/-- Sharp denominator-free wall estimate, valid also for `r = r' = 2`. -/
theorem richness_strict_loss_mul_card_le_degree_mul_lines
    {S : Finset Space3} {L : Finset LineIndex} {Q : Poly3}
    {r r' : ℕ} (hr' : 2 ≤ r')
    (hSrich : ∀ x ∈ S, r ≤ (linesThrough L x).card)
    (hSnot : ∀ x ∈ S, x ∉ richPoints (surfaceLines L Q) r')
    (hwall : ∀ x ∈ S, MvPolynomial.eval x Q = 0) :
    (r - (r' - 1)) * S.card ≤ Q.totalDegree * L.card :=
  (strict_loss_mul_card_le_card_externalIncidences hr' hSrich hSnot).trans
    (card_externalIncidences_le S L Q hwall)

end Erdos95.WallIncidences
