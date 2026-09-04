import ErdosProblems.Erdos957.Case24Bridge
import ErdosProblems.Erdos957.Hex

/-! # Contact graphs on five-point unit neighborhoods for Erdős 957 -/

open Metric
open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957ContactGraph

private def edgeBit (R : Fin 5 → Fin 5 → Prop) [DecidableRel R]
    (i j : Fin 5) : ℕ := if R i j then 1 else 0

private lemma card_filter_fin_five (R : Fin 5 → Fin 5 → Prop)
    [DecidableRel R] (i : Fin 5) :
    (Finset.univ.filter fun j ↦ R i j).card =
      edgeBit R i 0 + edgeBit R i 1 + edgeBit R i 2 +
        edgeBit R i 3 + edgeBit R i 4 := by
  rw [show (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} by decide]
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert,
    Finset.filter_insert, Finset.filter_singleton]
  by_cases h0 : R i 0 <;> by_cases h1 : R i 1 <;>
    by_cases h2 : R i 2 <;> by_cases h3 : R i 3 <;>
    by_cases h4 : R i 4 <;> simp_all [edgeBit]

/-- A five-vertex graph of maximum degree two, with edge `0--1` and all of
`2,3,4` two-valent, contains either the triangle on `2,3,4` or one of the
six possible five-cycles through `0--1`. -/
private lemma triangle_or_five_cycle
    (R : Fin 5 → Fin 5 → Prop) [DecidableRel R]
    (hsymm : ∀ i j, R i j ↔ R j i)
    (h01 : R 0 1)
    (hdeg0 : edgeBit R 0 1 + edgeBit R 0 2 + edgeBit R 0 3 +
      edgeBit R 0 4 ≤ 2)
    (hdeg1 : edgeBit R 1 0 + edgeBit R 1 2 + edgeBit R 1 3 +
      edgeBit R 1 4 ≤ 2)
    (hdeg2 : edgeBit R 2 0 + edgeBit R 2 1 + edgeBit R 2 3 +
      edgeBit R 2 4 = 2)
    (hdeg3 : edgeBit R 3 0 + edgeBit R 3 1 + edgeBit R 3 2 +
      edgeBit R 3 4 = 2)
    (hdeg4 : edgeBit R 4 0 + edgeBit R 4 1 + edgeBit R 4 2 +
      edgeBit R 4 3 = 2) :
    (R 2 3 ∧ R 3 4 ∧ R 4 2) ∨
    (R 0 1 ∧ R 1 2 ∧ R 2 3 ∧ R 3 4 ∧ R 4 0) ∨
    (R 0 1 ∧ R 1 4 ∧ R 4 3 ∧ R 3 2 ∧ R 2 0) ∨
    (R 0 1 ∧ R 1 3 ∧ R 3 2 ∧ R 2 4 ∧ R 4 0) ∨
    (R 0 1 ∧ R 1 4 ∧ R 4 2 ∧ R 2 3 ∧ R 3 0) ∨
    (R 0 1 ∧ R 1 2 ∧ R 2 4 ∧ R 4 3 ∧ R 3 0) ∨
    (R 0 1 ∧ R 1 3 ∧ R 3 4 ∧ R 4 2 ∧ R 2 0) := by
  have h10 : R 1 0 := (hsymm 0 1).mp h01
  have h20 : R 2 0 ↔ R 0 2 := hsymm 2 0
  have h30 : R 3 0 ↔ R 0 3 := hsymm 3 0
  have h40 : R 4 0 ↔ R 0 4 := hsymm 4 0
  have h21 : R 2 1 ↔ R 1 2 := hsymm 2 1
  have h31 : R 3 1 ↔ R 1 3 := hsymm 3 1
  have h41 : R 4 1 ↔ R 1 4 := hsymm 4 1
  have h32 : R 3 2 ↔ R 2 3 := hsymm 3 2
  have h42 : R 4 2 ↔ R 2 4 := hsymm 4 2
  have h43 : R 4 3 ↔ R 3 4 := hsymm 4 3
  by_cases h02 : R 0 2 <;> by_cases h03 : R 0 3 <;>
    by_cases h04 : R 0 4 <;> by_cases h12 : R 1 2 <;>
    by_cases h13 : R 1 3 <;> by_cases h14 : R 1 4 <;>
    by_cases h23 : R 2 3 <;> by_cases h24 : R 2 4 <;>
    by_cases h34 : R 3 4 <;>
    simp_all [edgeBit]

open Erdos957Cases24
open Erdos957Case24Bridge

abbrev Point := Erdos957Cases24.Point

/-- The concrete unit-neighbor finset and its complex-coordinate copy are
canonically equivalent. -/
private noncomputable def unitNeighborComplexEquiv (A : Finset Point) (p : Point) :
    Erdos957Cases24.unitNeighbors A p ≃
      Erdos957Angle.unitNeighbors (complexImage A) (toComplex p) := by
  classical
  let f : Erdos957Cases24.unitNeighbors A p →
      Erdos957Angle.unitNeighbors (complexImage A) (toComplex p) := fun q ↦
    ⟨toComplex q, image_unitNeighbors_subset_angle A p
      (Finset.mem_image.mpr ⟨q, q.property, rfl⟩)⟩
  apply Equiv.ofBijective f
  constructor
  · intro q r hqr
    apply Subtype.ext
    exact toComplex_injective (congrArg Subtype.val hqr)
  · intro z
    have hzImage := (Finset.mem_filter.mp z.property).1
    rcases Finset.mem_image.mp hzImage with ⟨q, hqA, hqz⟩
    have hpq : dist p q = 1 := by
      have hzDist := (Finset.mem_filter.mp z.property).2
      rw [← dist_toComplex]
      simpa [hqz, dist_comm] using hzDist
    let qN : Erdos957Cases24.unitNeighbors A p :=
      ⟨q, Erdos957Cases24.mem_unitNeighbors.mpr ⟨hqA, hpq⟩⟩
    refine ⟨qN, ?_⟩
    apply Subtype.ext
    exact hqz

/-- Every vertex of an indexed regular unit hexagon has two distinct unit
chords to the adjacent indexed vertices. -/
private lemma exists_two_unit_chords_of_regular_hexagon
    (u : Fin 6 → ℂ) (hnorm : ∀ i, ‖u i‖ = 1)
    (hids : u 0 - u 1 = u 5 ∧
      u 1 - u 2 = u 0 ∧
      u 2 - u 3 = u 1 ∧
      u 3 - u 4 = u 2 ∧
      u 4 - u 5 = u 3 ∧
      u 5 - u 0 = u 4)
    (i : Fin 6) :
    ∃ j k : Fin 6, j ≠ k ∧ ‖u i - u j‖ = 1 ∧ ‖u i - u k‖ = 1 := by
  fin_cases i <;> norm_num
  · refine ⟨1, 5, by decide, ?_, ?_⟩
    · change ‖u 0 - u 1‖ = 1
      rw [hids.1, hnorm]
    · change ‖u 0 - u 5‖ = 1
      rw [norm_sub_rev, hids.2.2.2.2.2, hnorm]
  · refine ⟨0, 2, by decide, ?_, ?_⟩
    · change ‖u 1 - u 0‖ = 1
      rw [norm_sub_rev, hids.1, hnorm]
    · change ‖u 1 - u 2‖ = 1
      rw [hids.2.1, hnorm]
  · refine ⟨1, 3, by decide, ?_, ?_⟩
    · change ‖u 2 - u 1‖ = 1
      rw [norm_sub_rev, hids.2.1, hnorm]
    · change ‖u 2 - u 3‖ = 1
      rw [hids.2.2.1, hnorm]
  · refine ⟨2, 4, by decide, ?_, ?_⟩
    · change ‖u 3 - u 2‖ = 1
      rw [norm_sub_rev, hids.2.2.1, hnorm]
    · change ‖u 3 - u 4‖ = 1
      rw [hids.2.2.2.1, hnorm]
  · refine ⟨3, 5, by decide, ?_, ?_⟩
    · change ‖u 4 - u 3‖ = 1
      rw [norm_sub_rev, hids.2.2.2.1, hnorm]
    · change ‖u 4 - u 5‖ = 1
      rw [hids.2.2.2.2.1, hnorm]
  · refine ⟨4, 0, by decide, ?_, ?_⟩
    · change ‖u 5 - u 4‖ = 1
      rw [norm_sub_rev, hids.2.2.2.2.1, hnorm]
    · change ‖u 5 - u 0‖ = 1
      rw [hids.2.2.2.2.2, hnorm]

/-- Unit contacts made inside the unit circle about `v`. -/
def circleContacts (A : Finset Point) (v q : Point) : Finset Point :=
  (Erdos957Cases24.unitNeighbors A v).filter fun y ↦ dist q y = 1

@[simp] lemma mem_circleContacts {A : Finset Point} {v q y : Point} :
    y ∈ circleContacts A v q ↔ y ∈ A ∧ dist v y = 1 ∧ dist q y = 1 := by
  simp [circleContacts, Erdos957Cases24.mem_unitNeighbors, and_assoc]

/-- Two unit circles whose centers are at unit distance have at most two
common points.  This is the cardinal wrapper around `Erdos957Hex` used by
the contact graph. -/
theorem card_circleContacts_le_two {A : Finset Point} {v q : Point}
    (hvq : dist v q = 1) : (circleContacts A v q).card ≤ 2 := by
  classical
  by_contra hnot
  have hthree : 3 ≤ (circleContacts A v q).card := by omega
  obtain ⟨T, hTC, hTcard⟩ := Finset.exists_subset_card_eq hthree
  obtain ⟨y₀, y₁, y₂, hy₀₁, hy₀₂, hy₁₂, hT⟩ :=
    Finset.card_eq_three.mp hTcard
  have hy₀C : y₀ ∈ circleContacts A v q := hTC (by simp [hT])
  have hy₁C : y₁ ∈ circleContacts A v q := hTC (by simp [hT])
  have hy₂C : y₂ ∈ circleContacts A v q := hTC (by simp [hT])
  let V := toComplex v
  let Q := toComplex q
  let D := Q - V
  let z : Point → ℂ := fun y ↦ (toComplex y - V) / D
  have hDnorm : ‖D‖ = 1 := by
    change ‖toComplex q - toComplex v‖ = 1
    rw [← dist_eq_norm, dist_toComplex, dist_comm]
    exact hvq
  have hDne : D ≠ 0 := norm_ne_zero_iff.mp (by rw [hDnorm]; norm_num)
  have hnormSq0 (y : Point) (hvy : dist v y = 1) :
      Complex.normSq (z y) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    have hynorm : ‖toComplex y - V‖ = 1 := by
      change ‖toComplex y - toComplex v‖ = 1
      rw [← dist_eq_norm, dist_toComplex, dist_comm]
      exact hvy
    dsimp [z]
    rw [norm_div, hynorm, hDnorm]
    norm_num
  have hnormSq1 (y : Point) (hqy : dist q y = 1) :
      Complex.normSq (z y - 1) = 1 := by
    have hzsub : z y - 1 = (toComplex y - Q) / D := by
      calc
        z y - 1 = (toComplex y - V) / D - D / D := by
          rw [div_self hDne]
        _ = ((toComplex y - V) - D) / D := by ring
        _ = (toComplex y - Q) / D := by
          congr 1
          dsimp [D]
          ring
    rw [hzsub, Complex.normSq_eq_norm_sq, norm_div, hDnorm]
    have hynorm : ‖toComplex y - Q‖ = 1 := by
      change ‖toComplex y - toComplex q‖ = 1
      rw [← dist_eq_norm, dist_toComplex, dist_comm]
      exact hqy
    rw [hynorm]
    norm_num
  have zinj : Function.Injective z := by
    intro y w hyw
    apply toComplex_injective
    have hsub : toComplex y - V = toComplex w - V := by
      exact (div_left_inj' hDne).mp hyw
    exact sub_left_inj.mp hsub
  have hy₀ := mem_circleContacts.mp hy₀C
  have hy₁ := mem_circleContacts.mp hy₁C
  have hy₂ := mem_circleContacts.mp hy₂C
  exact Erdos957Hex.not_three_pairwise_distinct_common_unit_neighbors
    (hnormSq0 y₀ hy₀.2.1) (hnormSq1 y₀ hy₀.2.2)
    (hnormSq0 y₁ hy₁.2.1) (hnormSq1 y₁ hy₁.2.2)
    (hnormSq0 y₂ hy₂.2.1) (hnormSq1 y₂ hy₂.2.2)
    ⟨zinj.ne hy₀₁, zinj.ne hy₀₂, zinj.ne hy₁₂⟩

/-- A degree-six point on the unit circle about `v` makes exactly two unit
contacts with that circle.  These are its predecessor and successor in its
own regular hexagon of unit neighbors. -/
theorem card_circleContacts_eq_two_of_degree_six
    {A : Finset Point} (hA : Erdos957Cases24.IsOneSeparated A)
    {v q : Point} (hvA : v ∈ A) (hvq : dist v q = 1)
    (hqDegree : Erdos957Case24Bridge.unitDegree A q = 6) :
    (circleContacts A v q).card = 2 := by
  classical
  let E := unitNeighborComplexEquiv A q
  let B := complexImage A
  let Q := toComplex q
  let N := Erdos957Angle.unitNeighbors B Q
  have hNcard : N.card = 6 := by
    have hcardEq := Fintype.card_congr E
    simp only [Fintype.card_coe] at hcardEq
    rw [← hcardEq]
    exact hqDegree
  obtain ⟨e, _hbin, hids⟩ :=
    Erdos957Angle.exists_unitNeighborEquiv_with_regular_hexagon_identities
      (complexImage_oneSeparated hA) Q hNcard
  let u : Fin 6 → ℂ := fun i ↦ ((e i : N) : ℂ) - Q
  have hunorm : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [← dist_eq_norm]
    simpa [u, dist_comm] using (Finset.mem_filter.mp (e i).property).2
  have hvNmem : v ∈ Erdos957Cases24.unitNeighbors A q := by
    apply Erdos957Cases24.mem_unitNeighbors.mpr
    exact ⟨hvA, by simpa [dist_comm] using hvq⟩
  let vN : Erdos957Cases24.unitNeighbors A q := ⟨v, hvNmem⟩
  obtain ⟨i, hi⟩ := e.surjective (E vN)
  obtain ⟨j, k, hjk, hij, hik⟩ :=
    exists_two_unit_chords_of_regular_hexagon u hunorm hids i
  let yN : Erdos957Cases24.unitNeighbors A q := E.symm (e j)
  let zN : Erdos957Cases24.unitNeighbors A q := E.symm (e k)
  let y : Point := yN
  let z : Point := zN
  have hei : ((e i : N) : ℂ) = toComplex v := by
    rw [hi]
    rfl
  have hej : ((e j : N) : ℂ) = toComplex y := by
    have h := congrArg Subtype.val (E.apply_symm_apply (e j))
    exact h.symm
  have hek : ((e k : N) : ℂ) = toComplex z := by
    have h := congrArg Subtype.val (E.apply_symm_apply (e k))
    exact h.symm
  have hvy : dist v y = 1 := by
    dsimp [u] at hij
    rw [hei, hej, sub_sub_sub_cancel_right,
      ← dist_eq_norm, dist_toComplex] at hij
    exact hij
  have hvz : dist v z = 1 := by
    dsimp [u] at hik
    rw [hei, hek, sub_sub_sub_cancel_right,
      ← dist_eq_norm, dist_toComplex] at hik
    exact hik
  have hyC : y ∈ circleContacts A v q := by
    apply mem_circleContacts.mpr
    have hy := Erdos957Cases24.mem_unitNeighbors.mp yN.property
    exact ⟨hy.1, hvy, hy.2⟩
  have hzC : z ∈ circleContacts A v q := by
    apply mem_circleContacts.mpr
    have hz := Erdos957Cases24.mem_unitNeighbors.mp zN.property
    exact ⟨hz.1, hvz, hz.2⟩
  have hyz : y ≠ z := by
    intro hyz
    apply hjk
    apply e.injective
    have hynEq : yN = zN := Subtype.ext hyz
    simpa [yN, zN] using congrArg E hynEq
  apply le_antisymm (card_circleContacts_le_two hvq)
  have : 1 < (circleContacts A v q).card :=
    Finset.one_lt_card.mpr ⟨y, hyC, z, hzC, hyz⟩
  omega

/-! ## Odd-cycle exclusions on a one-separated unit circle -/

private def pointDot (x y : Point) : ℝ := x 0 * y 0 + x 1 * y 1

private lemma pointDot_self_eq_norm_sq (x : Point) :
    pointDot x x = ‖x‖ ^ 2 := by
  calc
    pointDot x x =
        (x 0 - (0 : Point) 0) ^ 2 + (x 1 - (0 : Point) 1) ^ 2 := by
      simp [pointDot]
      ring
    _ = dist x 0 ^ 2 :=
      (Erdos957Cases24.dist_sq_eq_coordinates x 0).symm
    _ = ‖x‖ ^ 2 := by rw [dist_zero_right]

private lemma pointDot_eq_half_of_unit_of_unit_sub {x y : Point}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖x - y‖ = 1) :
    pointDot x y = 1 / 2 := by
  have hx' := congrArg (fun t : ℝ ↦ t ^ 2) hx
  have hy' := congrArg (fun t : ℝ ↦ t ^ 2) hy
  have hxy' := congrArg (fun t : ℝ ↦ t ^ 2) hxy
  rw [← pointDot_self_eq_norm_sq] at hx' hy'
  rw [← pointDot_self_eq_norm_sq] at hxy'
  simp only [pointDot, PiLp.sub_apply] at hx' hy' hxy' ⊢
  nlinarith

private lemma gram_determinant_three (x y z : Point) :
    pointDot x x * (pointDot y y * pointDot z z - pointDot y z ^ 2) -
      pointDot x y *
        (pointDot x y * pointDot z z - pointDot y z * pointDot x z) +
      pointDot x z *
        (pointDot x y * pointDot y z - pointDot y y * pointDot x z) = 0 := by
  simp only [pointDot]
  ring

private lemma eq_sub_of_unit_chain {x y z : Point}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hxy : ‖x - y‖ = 1) (hyz : ‖y - z‖ = 1)
    (hxz : 1 ≤ ‖x - z‖) : z = y - x := by
  have hxx : pointDot x x = 1 := by rw [pointDot_self_eq_norm_sq, hx]; norm_num
  have hyy : pointDot y y = 1 := by rw [pointDot_self_eq_norm_sq, hy]; norm_num
  have hzz : pointDot z z = 1 := by rw [pointDot_self_eq_norm_sq, hz]; norm_num
  have hxyDot : pointDot x y = 1 / 2 :=
    pointDot_eq_half_of_unit_of_unit_sub hx hy hxy
  have hyzDot : pointDot y z = 1 / 2 :=
    pointDot_eq_half_of_unit_of_unit_sub hy hz hyz
  have hxzNonneg : 0 ≤ ‖x - z‖ := norm_nonneg _
  have hsepSq : 1 ≤ ‖x - z‖ ^ 2 := by nlinarith
  have hgram := gram_determinant_three x y z
  rw [hxx, hyy, hzz, hxyDot, hyzDot] at hgram
  have hxzDotLe : pointDot x z ≤ 1 / 2 := by
    rw [← pointDot_self_eq_norm_sq] at hsepSq
    simp only [pointDot, PiLp.sub_apply] at hsepSq hxx hzz ⊢
    nlinarith
  have hxzDot : pointDot x z = -(1 / 2) := by nlinarith
  have hzero : pointDot (z - (y - x)) (z - (y - x)) = 0 := by
    simp only [pointDot, PiLp.sub_apply] at hxx hyy hzz hxyDot hyzDot hxzDot ⊢
    nlinarith
  have hnormZero : ‖z - (y - x)‖ = 0 := by
    have hn : 0 ≤ ‖z - (y - x)‖ := norm_nonneg _
    have hs : ‖z - (y - x)‖ ^ 2 = 0 := by
      rw [← pointDot_self_eq_norm_sq, hzero]
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnormZero)

private lemma no_unit_contact_triangle {x₀ x₁ x₂ : Point}
    (hnorm : ‖x₀‖ = 1 ∧ ‖x₁‖ = 1 ∧ ‖x₂‖ = 1)
    (hsep : 1 ≤ ‖x₀ - x₂‖)
    (h01 : ‖x₀ - x₁‖ = 1) (h12 : ‖x₁ - x₂‖ = 1)
    (h20 : ‖x₂ - x₀‖ = 1) : False := by
  have h2 : x₂ = x₁ - x₀ :=
    eq_sub_of_unit_chain hnorm.1 hnorm.2.1 hnorm.2.2 h01 h12 hsep
  have hdot := pointDot_eq_half_of_unit_of_unit_sub hnorm.1 hnorm.2.1 h01
  have hs := congrArg (fun t : ℝ ↦ t ^ 2) h20
  rw [h2, ← pointDot_self_eq_norm_sq] at hs
  simp only [pointDot, PiLp.sub_apply] at hdot hs
  have hx0 := congrArg (fun t : ℝ ↦ t ^ 2) hnorm.1
  have hx1 := congrArg (fun t : ℝ ↦ t ^ 2) hnorm.2.1
  rw [← pointDot_self_eq_norm_sq] at hx0 hx1
  simp only [pointDot] at hx0 hx1
  nlinarith

private lemma no_unit_contact_five_cycle
    (x : Fin 5 → Point)
    (hnorm : ∀ i, ‖x i‖ = 1)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖x i - x j‖)
    (hedge01 : ‖x 0 - x 1‖ = 1)
    (hedge12 : ‖x 1 - x 2‖ = 1)
    (hedge23 : ‖x 2 - x 3‖ = 1)
    (hedge34 : ‖x 3 - x 4‖ = 1)
    (hedge40 : ‖x 4 - x 0‖ = 1) : False := by
  have h2 : x 2 = x 1 - x 0 :=
    eq_sub_of_unit_chain (hnorm 0) (hnorm 1) (hnorm 2)
      hedge01 hedge12 (hsep 0 2 (by decide))
  have h3 : x 3 = -x 0 := by
    calc
      x 3 = x 2 - x 1 :=
        eq_sub_of_unit_chain (hnorm 1) (hnorm 2) (hnorm 3)
          hedge12 hedge23 (hsep 1 3 (by decide))
      _ = -x 0 := by rw [h2]; abel
  have h4 : x 4 = -x 1 := by
    calc
      x 4 = x 3 - x 2 :=
        eq_sub_of_unit_chain (hnorm 2) (hnorm 3) (hnorm 4)
          hedge23 hedge34 (hsep 2 4 (by decide))
      _ = -x 1 := by rw [h3, h2]; abel
  have hdot := pointDot_eq_half_of_unit_of_unit_sub
    (hnorm 0) (hnorm 1) hedge01
  have hs := congrArg (fun t : ℝ ↦ t ^ 2) hedge40
  rw [h4, ← pointDot_self_eq_norm_sq] at hs
  have hx0 := congrArg (fun t : ℝ ↦ t ^ 2) (hnorm 0)
  have hx1 := congrArg (fun t : ℝ ↦ t ^ 2) (hnorm 1)
  rw [← pointDot_self_eq_norm_sq] at hx0 hx1
  simp only [pointDot, PiLp.sub_apply, PiLp.neg_apply] at hdot hs hx0 hx1
  nlinarith

/-- Outside a specified adjacent pair on the five-point unit circle about
`v`, at least one unit neighbor has ambient unit degree at most five. -/
theorem exists_low_degree_unitNeighbor_outside_adjacent_pair
    {A : Finset Point}
    (hsep : IsOneSeparated A)
    {v s₀ s₁ : Point}
    (hvA : v ∈ A) (hs₀A : s₀ ∈ A) (hs₁A : s₁ ∈ A)
    (hvs₀ : dist v s₀ = 1) (hvs₁ : dist v s₁ = 1)
    (hs₀s₁ : dist s₀ s₁ = 1)
    (hvDegree : unitDegree A v = 5) :
    ∃ low : Point, low ∈ A ∧ dist v low = 1 ∧
      low ≠ s₀ ∧ low ≠ s₁ ∧ low ≠ v ∧ unitDegree A low ≤ 5 := by
  classical
  let N := Erdos957Cases24.unitNeighbors A v
  have hs₀N : s₀ ∈ N := by
    exact Erdos957Cases24.mem_unitNeighbors.mpr ⟨hs₀A, hvs₀⟩
  have hs₁N : s₁ ∈ N := by
    exact Erdos957Cases24.mem_unitNeighbors.mpr ⟨hs₁A, hvs₁⟩
  have hs₀s₁ne : s₀ ≠ s₁ := by
    intro h
    subst s₁
    simpa using hs₀s₁
  let T := (N.erase s₀).erase s₁
  have hs₁erase : s₁ ∈ N.erase s₀ :=
    Finset.mem_erase.mpr ⟨hs₀s₁ne.symm, hs₁N⟩
  have hTcard : T.card = 3 := by
    dsimp [T]
    rw [Finset.card_erase_of_mem hs₁erase,
      Finset.card_erase_of_mem hs₀N]
    change N.card - 1 - 1 = 3
    change N.card = 5 at hvDegree
    omega
  obtain ⟨r₀, r₁, r₂, hr₀r₁, hr₀r₂, hr₁r₂, hT⟩ :=
    Finset.card_eq_three.mp hTcard
  have residual_data (r : Point) (hrT : r ∈ T) :
      r ∈ A ∧ dist v r = 1 ∧ r ≠ s₀ ∧ r ≠ s₁ := by
    have hrErase₁ : r ∈ N.erase s₀ := (Finset.mem_erase.mp hrT).2
    have hrs₁ : r ≠ s₁ := (Finset.mem_erase.mp hrT).1
    have hrN : r ∈ N := (Finset.mem_erase.mp hrErase₁).2
    have hrs₀ : r ≠ s₀ := (Finset.mem_erase.mp hrErase₁).1
    have hr := Erdos957Cases24.mem_unitNeighbors.mp hrN
    exact ⟨hr.1, hr.2, hrs₀, hrs₁⟩
  have hr₀T : r₀ ∈ T := by simp [hT]
  have hr₁T : r₁ ∈ T := by simp [hT]
  have hr₂T : r₂ ∈ T := by simp [hT]
  have hr₀ := residual_data r₀ hr₀T
  have hr₁ := residual_data r₁ hr₁T
  have hr₂ := residual_data r₂ hr₂T
  have hN : N = {s₀, s₁, r₀, r₁, r₂} := by
    ext q
    by_cases hq₀ : q = s₀
    · subst q
      simp [hs₀N]
    by_cases hq₁ : q = s₁
    · subst q
      simp [hs₁N]
    have hqT : q ∈ T ↔ q ∈ N := by
      simp [T, hq₀, hq₁]
    rw [← hqT, hT]
    simp [hq₀, hq₁]
  let x : Fin 5 → Point := ![s₀, s₁, r₀, r₁, r₂]
  have hxA : ∀ i, x i ∈ A := by
    intro i
    fin_cases i <;> simp [x, hs₀A, hs₁A, hr₀.1, hr₁.1, hr₂.1]
  have hxv : ∀ i, dist v (x i) = 1 := by
    intro i
    fin_cases i <;> simp [x, hvs₀, hvs₁, hr₀.2.1, hr₁.2.1, hr₂.2.1]
  have hxinj : Function.Injective x := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [x, hs₀s₁ne, hs₀s₁ne.symm,
        hr₀.2.2.1, hr₀.2.2.1.symm, hr₀.2.2.2, hr₀.2.2.2.symm,
        hr₁.2.2.1, hr₁.2.2.1.symm, hr₁.2.2.2, hr₁.2.2.2.symm,
        hr₂.2.2.1, hr₂.2.2.1.symm, hr₂.2.2.2, hr₂.2.2.2.symm,
        hr₀r₁, hr₀r₁.symm, hr₀r₂, hr₀r₂.symm, hr₁r₂, hr₁r₂.symm]
  let R : Fin 5 → Fin 5 → Prop := fun i j ↦ dist (x i) (x j) = 1
  let : DecidableRel R := fun _ _ ↦ inferInstance
  have hR01 : R 0 1 := by simpa [R, x] using hs₀s₁
  have hRsymm : ∀ i j, R i j ↔ R j i := by
    intro i j
    simp only [R, dist_comm]
  have hcardContact (i : Fin 5) :
      (circleContacts A v (x i)).card =
        edgeBit R i 0 + edgeBit R i 1 + edgeBit R i 2 +
          edgeBit R i 3 + edgeBit R i 4 := by
    have hcontactEq : circleContacts A v (x i) =
        (Finset.univ.filter fun j : Fin 5 ↦ R i j).image x := by
      ext q
      simp only [circleContacts,
        show Erdos957Cases24.unitNeighbors A v = N from rfl, hN,
        Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hq, hunit⟩
        rcases hq with rfl | rfl | rfl | rfl | rfl
        · exact ⟨0, by simpa [R, x], by simp [x]⟩
        · exact ⟨1, by simpa [R, x], by simp [x]⟩
        · exact ⟨2, by simpa [R, x], by simp [x]⟩
        · exact ⟨3, by simpa [R, x], by simp [x]⟩
        · exact ⟨4, by simpa [R, x], by simp [x]⟩
      · rintro ⟨j, hR, rfl⟩
        refine ⟨?_, hR⟩
        fin_cases j <;> simp [x]
    rw [hcontactEq]
    have himage : ((Finset.univ.filter fun j : Fin 5 ↦ R i j).image x).card =
        (Finset.univ.filter fun j : Fin 5 ↦ R i j).card :=
      Finset.card_image_iff.mpr fun _ _ _ _ h ↦ hxinj h
    rw [himage, card_filter_fin_five]
  by_contra hnone
  push Not at hnone
  have hr₀Degree : unitDegree A r₀ = 6 := by
    have hle := unitDegree_le_six hsep r₀
    have hnle : ¬ unitDegree A r₀ ≤ 5 := by
      intro hlow
      have := hnone r₀ hr₀.1 hr₀.2.1 hr₀.2.2.1 hr₀.2.2.2
        (by intro h; subst r₀; simpa using hr₀.2.1)
      omega
    omega
  have hr₁Degree : unitDegree A r₁ = 6 := by
    have hle := unitDegree_le_six hsep r₁
    have hnle : ¬ unitDegree A r₁ ≤ 5 := by
      intro hlow
      have := hnone r₁ hr₁.1 hr₁.2.1 hr₁.2.2.1 hr₁.2.2.2
        (by intro h; subst r₁; simpa using hr₁.2.1)
      omega
    omega
  have hr₂Degree : unitDegree A r₂ = 6 := by
    have hle := unitDegree_le_six hsep r₂
    have hnle : ¬ unitDegree A r₂ ≤ 5 := by
      intro hlow
      have := hnone r₂ hr₂.1 hr₂.2.1 hr₂.2.2.1 hr₂.2.2.2
        (by intro h; subst r₂; simpa using hr₂.2.1)
      omega
    omega
  have hdeg0 : edgeBit R 0 1 + edgeBit R 0 2 + edgeBit R 0 3 +
      edgeBit R 0 4 ≤ 2 := by
    have hc : (circleContacts A v (x 0)).card ≤ 2 := by
      simpa [x] using card_circleContacts_le_two (A := A) hvs₀
    rw [hcardContact] at hc
    simpa [R, edgeBit] using hc
  have hdeg1 : edgeBit R 1 0 + edgeBit R 1 2 + edgeBit R 1 3 +
      edgeBit R 1 4 ≤ 2 := by
    have hc : (circleContacts A v (x 1)).card ≤ 2 := by
      simpa [x] using card_circleContacts_le_two (A := A) hvs₁
    rw [hcardContact] at hc
    simpa [R, edgeBit] using hc
  have hdeg2 : edgeBit R 2 0 + edgeBit R 2 1 + edgeBit R 2 3 +
      edgeBit R 2 4 = 2 := by
    have hc : (circleContacts A v (x 2)).card = 2 := by
      simpa [x] using card_circleContacts_eq_two_of_degree_six hsep hvA
        hr₀.2.1 hr₀Degree
    rw [hcardContact] at hc
    simpa [R, edgeBit] using hc
  have hdeg3 : edgeBit R 3 0 + edgeBit R 3 1 + edgeBit R 3 2 +
      edgeBit R 3 4 = 2 := by
    have hc : (circleContacts A v (x 3)).card = 2 := by
      simpa [x] using card_circleContacts_eq_two_of_degree_six hsep hvA
        hr₁.2.1 hr₁Degree
    rw [hcardContact] at hc
    simpa [R, edgeBit] using hc
  have hdeg4 : edgeBit R 4 0 + edgeBit R 4 1 + edgeBit R 4 2 +
      edgeBit R 4 3 = 2 := by
    have hc : (circleContacts A v (x 4)).card = 2 := by
      simpa [x] using card_circleContacts_eq_two_of_degree_six hsep hvA
        hr₂.2.1 hr₂Degree
    rw [hcardContact] at hc
    simpa [R, edgeBit] using hc
  have hcases := triangle_or_five_cycle R hRsymm hR01
    hdeg0 hdeg1 hdeg2 hdeg3 hdeg4
  let y : Fin 5 → Point := fun i ↦ x i - v
  have hynorm : ∀ i, ‖y i‖ = 1 := by
    intro i
    rw [← dist_eq_norm]
    simpa [y, dist_comm] using hxv i
  have hysep : ∀ i j, i ≠ j → 1 ≤ ‖y i - y j‖ := by
    intro i j hij
    have h := hsep (x i) (hxA i) (x j) (hxA j) (hxinj.ne hij)
    rw [dist_eq_norm] at h
    simpa [y, sub_sub_sub_cancel_right] using h
  have hyedge {i j : Fin 5} (h : R i j) : ‖y i - y j‖ = 1 := by
    simpa [R, y, dist_eq_norm, sub_sub_sub_cancel_right] using h
  have no_cycle (e : Fin 5 → Fin 5) (he : Function.Injective e)
      (h01 : R (e 0) (e 1)) (h12 : R (e 1) (e 2))
      (h23 : R (e 2) (e 3)) (h34 : R (e 3) (e 4))
      (h40 : R (e 4) (e 0)) : False := by
    exact no_unit_contact_five_cycle (fun i ↦ y (e i))
      (fun i ↦ hynorm (e i))
      (fun i j hij ↦ hysep (e i) (e j) (he.ne hij))
      (hyedge h01) (hyedge h12) (hyedge h23) (hyedge h34) (hyedge h40)
  rcases hcases with htri | hcycle₀ | hcycle₁ | hcycle₂ |
      hcycle₃ | hcycle₄ | hcycle₅
  · exact no_unit_contact_triangle
      ⟨hynorm 2, hynorm 3, hynorm 4⟩
      (hysep 2 4 (by decide))
      (hyedge htri.1) (hyedge htri.2.1) (hyedge htri.2.2)
  · exact no_cycle ![0, 1, 2, 3, 4]
      (by intro i j; fin_cases i <;> fin_cases j <;> simp)
      hcycle₀.1 hcycle₀.2.1 hcycle₀.2.2.1
      hcycle₀.2.2.2.1 hcycle₀.2.2.2.2
  · exact no_cycle ![0, 1, 4, 3, 2]
      (by intro i j; fin_cases i <;> fin_cases j <;> simp)
      hcycle₁.1 hcycle₁.2.1 hcycle₁.2.2.1
      hcycle₁.2.2.2.1 hcycle₁.2.2.2.2
  · exact no_cycle ![0, 1, 3, 2, 4]
      (by intro i j; fin_cases i <;> fin_cases j <;> simp)
      hcycle₂.1 hcycle₂.2.1 hcycle₂.2.2.1
      hcycle₂.2.2.2.1 hcycle₂.2.2.2.2
  · exact no_cycle ![0, 1, 4, 2, 3]
      (by intro i j; fin_cases i <;> fin_cases j <;> simp)
      hcycle₃.1 hcycle₃.2.1 hcycle₃.2.2.1
      hcycle₃.2.2.2.1 hcycle₃.2.2.2.2
  · exact no_cycle ![0, 1, 2, 4, 3]
      (by intro i j; fin_cases i <;> fin_cases j <;> simp)
      hcycle₄.1 hcycle₄.2.1 hcycle₄.2.2.1
      hcycle₄.2.2.2.1 hcycle₄.2.2.2.2
  · exact no_cycle ![0, 1, 3, 4, 2]
      (by intro i j; fin_cases i <;> fin_cases j <;> simp)
      hcycle₅.1 hcycle₅.2.1 hcycle₅.2.2.1
      hcycle₅.2.2.2.1 hcycle₅.2.2.2.2

/-- Normalized Case-4 wrapper retaining Dumitrescu's deterministic
farthest-below point.  Either that selected point is already low-degree, or
there is a distinct low-degree residual neighbor.  The latter witness stays
inside the same three-point residual finset, so downstream order arguments
can compare it with `D.point` using `D.order_min`. -/
theorem farthestBelow_degree_le_five_or_exists_distinct_low_residual
    {A : Finset Point}
    (hsep : IsOneSeparated A)
    (hvA : Erdos957Cases24.Case4.v ∈ A)
    (huPrevA : Erdos957Cases24.Case2.uPrev ∈ A)
    (huA : Erdos957Cases24.Case2.u ∈ A)
    (hvDegree : unitDegree A Erdos957Cases24.Case4.v = 5)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData A) :
    unitDegree A D.point ≤ 5 ∨
      ∃ low : Point,
        low ∈ Erdos957Case24Bridge.Case4.residualNeighbors A ∧
        low ≠ D.point ∧ unitDegree A low ≤ 5 := by
  obtain ⟨low, hlowA, hvlow, hlowPrev, hlowU, _hlowV, hlowDegree⟩ :=
    exists_low_degree_unitNeighbor_outside_adjacent_pair hsep hvA
      huPrevA huA
      (by simpa [Erdos957Cases24.Case4.v, dist_comm] using
        Erdos957Cases24.Case2.dist_uPrev_v)
      (by simpa [Erdos957Cases24.Case4.v, dist_comm] using
        Erdos957Cases24.Case2.dist_u_v)
      Erdos957Cases24.Case2.dist_uPrev_u hvDegree
  by_cases hlowD : low = D.point
  · left
    simpa [← hlowD] using hlowDegree
  · right
    refine ⟨low, ?_, hlowD, hlowDegree⟩
    exact Erdos957Case24Bridge.Case4.mem_residualNeighbors.mpr
      ⟨hlowA, hvlow, hlowPrev, hlowU⟩

/-! ## Ordered high-farthest branch -/

private theorem degree_six_residual_not_unit_to_uPrev
    {A : Finset Point}
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    (hvA : Erdos957Cases24.Case4.v ∈ A)
    (huPrevA : Erdos957Cases24.Case2.uPrev ∈ A)
    {q : Point}
    (hq : q ∈ Erdos957Case24Bridge.Case4.residualNeighbors A)
    (hqSix : unitDegree A q = 6) :
    dist q Erdos957Cases24.Case2.uPrev ≠ 1 := by
  intro hqPrev
  have hqv :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hq).2.1
  have hbelow :=
    Erdos957Case24Bridge.Case4.residual_below_support hstrict hq
  change q 1 < 0 at hbelow
  have hvSq := congrArg (fun t : ℝ ↦ t ^ 2) hqv
  have hpSq := congrArg (fun t : ℝ ↦ t ^ 2) hqPrev
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hvSq hpSq
  simp only [Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v,
    Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one, one_pow] at hvSq hpSq
  have hline : q 0 = Erdos957Cases24.sqrtThree * q 1 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hfactor : q 1 * (2 * q 1 + Erdos957Cases24.sqrtThree) = 0 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hq1 : q 1 = -(Erdos957Cases24.sqrtThree / 2) := by
    rcases mul_eq_zero.mp hfactor with hzero | hroot
    · rw [hzero] at hbelow
      exact (lt_irrefl 0 hbelow).elim
    · linarith
  have hq0 : q 0 = -(3 / 2 : ℝ) := by
    rw [hline, hq1]
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  let z := q + Erdos957Cases24.Case2.uPrev - Erdos957Cases24.Case4.v
  have hzA : z ∈ A := by
    exact hexagon_completion_mem hsep huPrevA hvA hqPrev
      (by simpa [dist_comm] using hqv)
      (by simpa [Erdos957Cases24.Case4.v] using
        Erdos957Cases24.Case2.dist_uPrev_v) hqSix
  have hz0 : z 0 = -2 := by
    simp [z, hq0, Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v]
    norm_num
  have hz1 : z 1 = 0 := by
    simp [z, hq1, Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v]
  have hzBoundary : z ∉
      ({Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u} : Finset Point) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hz
      have := congrArg (fun p : Point ↦ p 0) hz
      rw [hz0] at this
      norm_num [Erdos957Cases24.Case2.uPrev] at this
    · intro hz
      have := congrArg (fun p : Point ↦ p 0) hz
      rw [hz0] at this
      norm_num [Erdos957Cases24.Case2.u] at this
  have := hstrict z hzA hzBoundary
  rw [hz1] at this
  exact (lt_irrefl 0 this).elim

private theorem degree_six_residual_not_unit_to_u
    {A : Finset Point}
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    (hvA : Erdos957Cases24.Case4.v ∈ A)
    (huA : Erdos957Cases24.Case2.u ∈ A)
    {q : Point}
    (hq : q ∈ Erdos957Case24Bridge.Case4.residualNeighbors A)
    (hqSix : unitDegree A q = 6) :
    dist q Erdos957Cases24.Case2.u ≠ 1 := by
  intro hqU
  have hqv :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hq).2.1
  have hbelow :=
    Erdos957Case24Bridge.Case4.residual_below_support hstrict hq
  change q 1 < 0 at hbelow
  have hvSq := congrArg (fun t : ℝ ↦ t ^ 2) hqv
  have huSq := congrArg (fun t : ℝ ↦ t ^ 2) hqU
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hvSq huSq
  simp only [Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v,
    Erdos957Cases24.Case2.u, Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one, one_pow] at hvSq huSq
  have hline : q 0 + Erdos957Cases24.sqrtThree * q 1 = -1 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hfactor : q 1 * (2 * q 1 + Erdos957Cases24.sqrtThree) = 0 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hq1 : q 1 = -(Erdos957Cases24.sqrtThree / 2) := by
    rcases mul_eq_zero.mp hfactor with hzero | hroot
    · rw [hzero] at hbelow
      exact (lt_irrefl 0 hbelow).elim
    · linarith
  have hq0 : q 0 = (1 / 2 : ℝ) := by
    rw [hq1] at hline
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  let z := q + Erdos957Cases24.Case2.u - Erdos957Cases24.Case4.v
  have hzA : z ∈ A := by
    exact hexagon_completion_mem hsep huA hvA hqU
      (by simpa [dist_comm] using hqv)
      (by simpa [Erdos957Cases24.Case4.v] using
        Erdos957Cases24.Case2.dist_u_v) hqSix
  have hz0 : z 0 = 1 := by
    simp [z, hq0, Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v]
    norm_num
  have hz1 : z 1 = 0 := by
    simp [z, hq1, Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v]
  have hzBoundary : z ∉
      ({Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u} : Finset Point) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hz
      have := congrArg (fun p : Point ↦ p 0) hz
      rw [hz0] at this
      norm_num [Erdos957Cases24.Case2.uPrev] at this
    · intro hz
      have := congrArg (fun p : Point ↦ p 0) hz
      rw [hz0] at this
      norm_num [Erdos957Cases24.Case2.u] at this
  have := hstrict z hzA hzBoundary
  rw [hz1] at this
  exact (lt_irrefl 0 this).elim

private theorem not_three_pairwise_unit_on_unit_circle
    {v a b c : Point}
    (hva : dist v a = 1) (hvb : dist v b = 1) (hvc : dist v c = 1)
    (hab : dist a b = 1) (hbc : dist b c = 1)
    (hca : dist c a = 1) : False := by
  let x₀ := a - v
  let x₁ := b - v
  let x₂ := c - v
  apply no_unit_contact_triangle (x₀ := x₀) (x₁ := x₁) (x₂ := x₂)
  · constructor
    · simpa [x₀, dist_eq_norm, norm_sub_rev] using hva
    constructor
    · simpa [x₁, dist_eq_norm, norm_sub_rev] using hvb
    · simpa [x₂, dist_eq_norm, norm_sub_rev] using hvc
  · have : ‖x₀ - x₂‖ = 1 := by
      calc
        ‖x₀ - x₂‖ = ‖a - c‖ := by
          simp [x₀, x₂, sub_sub_sub_cancel_right]
        _ = dist a c := by rw [dist_eq_norm]
        _ = 1 := by simpa [dist_comm] using hca
    linarith
  · simpa [x₀, x₁, dist_eq_norm, sub_sub_sub_cancel_right] using hab
  · simpa [x₁, x₂, dist_eq_norm, sub_sub_sub_cancel_right] using hbc
  · simpa [x₂, x₀, dist_eq_norm, sub_sub_sub_cancel_right] using hca

/-- In the high-farthest subbranch, the two unit contacts adjacent to the
selected residual point are precisely the other two residual neighbors, and
both have degree at most five.  This is the incidence-and-capacity core of
Du19 Case 4; the subsequent theorem only adds their deterministic order. -/
theorem exists_two_low_residual_contacts_of_farthest_degree_six
    {A : Finset Point}
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    (hvA : Erdos957Cases24.Case4.v ∈ A)
    (huPrevA : Erdos957Cases24.Case2.uPrev ∈ A)
    (huA : Erdos957Cases24.Case2.u ∈ A)
    (hvDegree : unitDegree A Erdos957Cases24.Case4.v = 5)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData A)
    (hDSix : unitDegree A D.point = 6) :
    ∃ a b : Point,
      a ∈ Erdos957Case24Bridge.Case4.residualNeighbors A ∧
      b ∈ Erdos957Case24Bridge.Case4.residualNeighbors A ∧
      dist D.point a = 1 ∧ dist D.point b = 1 ∧ a ≠ b ∧
      unitDegree A a ≤ 5 ∧ unitDegree A b ≤ 5 := by
  classical
  have hDv :=
    (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp D.point_mem).2.1
  have hcontactCard :
      (circleContacts A Erdos957Cases24.Case4.v D.point).card = 2 :=
    card_circleContacts_eq_two_of_degree_six hsep hvA hDv hDSix
  obtain ⟨a, b, hab, hcontacts⟩ := Finset.card_eq_two.mp hcontactCard
  have haC : a ∈ circleContacts A Erdos957Cases24.Case4.v D.point := by
    rw [hcontacts]
    simp
  have hbC : b ∈ circleContacts A Erdos957Cases24.Case4.v D.point := by
    rw [hcontacts]
    simp
  have haData := mem_circleContacts.mp haC
  have hbData := mem_circleContacts.mp hbC
  have haD : a ≠ D.point := by
    intro h
    subst a
    simpa using haData.2.2
  have hbD : b ≠ D.point := by
    intro h
    subst b
    simpa using hbData.2.2
  have haPrev : a ≠ Erdos957Cases24.Case2.uPrev := by
    intro h
    subst a
    exact degree_six_residual_not_unit_to_uPrev hsep hstrict hvA huPrevA
      D.point_mem hDSix (by simpa [dist_comm] using haData.2.2)
  have haU : a ≠ Erdos957Cases24.Case2.u := by
    intro h
    subst a
    exact degree_six_residual_not_unit_to_u hsep hstrict hvA huA
      D.point_mem hDSix (by simpa [dist_comm] using haData.2.2)
  have hbPrev : b ≠ Erdos957Cases24.Case2.uPrev := by
    intro h
    subst b
    exact degree_six_residual_not_unit_to_uPrev hsep hstrict hvA huPrevA
      D.point_mem hDSix (by simpa [dist_comm] using hbData.2.2)
  have hbU : b ≠ Erdos957Cases24.Case2.u := by
    intro h
    subst b
    exact degree_six_residual_not_unit_to_u hsep hstrict hvA huA
      D.point_mem hDSix (by simpa [dist_comm] using hbData.2.2)
  have haRes : a ∈ Erdos957Case24Bridge.Case4.residualNeighbors A :=
    Erdos957Case24Bridge.Case4.mem_residualNeighbors.mpr
      ⟨haData.1, haData.2.1, haPrev, haU⟩
  have hbRes : b ∈ Erdos957Case24Bridge.Case4.residualNeighbors A :=
    Erdos957Case24Bridge.Case4.mem_residualNeighbors.mpr
      ⟨hbData.1, hbData.2.1, hbPrev, hbU⟩
  have hresCard :
      (Erdos957Case24Bridge.Case4.residualNeighbors A).card = 3 :=
    Erdos957Case24Bridge.Case4.card_residualNeighbors_eq_three
      huPrevA huA hvDegree
  have htripleCard : ({D.point, a, b} : Finset Point).card = 3 := by
    simp [haD.symm, hbD.symm, hab]
  have htripleSub : ({D.point, a, b} : Finset Point) ⊆
      Erdos957Case24Bridge.Case4.residualNeighbors A := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl
    · exact D.point_mem
    · exact haRes
    · exact hbRes
  have hresEq : Erdos957Case24Bridge.Case4.residualNeighbors A =
      {D.point, a, b} := by
    symm
    apply Finset.eq_of_subset_of_card_le htripleSub
    rw [htripleCard, hresCard]
  have degree_le_five_of_contact
      (r other : Point)
      (hrRes : r ∈ Erdos957Case24Bridge.Case4.residualNeighbors A)
      (hotherRes : other ∈ Erdos957Case24Bridge.Case4.residualNeighbors A)
      (hrD : dist D.point r = 1) (hotherD : dist D.point other = 1)
      (hrOther : r ≠ other)
      (hpair : (r = a ∧ other = b) ∨ (r = b ∧ other = a)) :
      unitDegree A r ≤ 5 := by
    by_contra hnle
    have hrSix : unitDegree A r = 6 := by
      have := unitDegree_le_six hsep r
      omega
    have hrv :=
      (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hrRes).2.1
    have hcCard :
        (circleContacts A Erdos957Cases24.Case4.v r).card = 2 :=
      card_circleContacts_eq_two_of_degree_six hsep hvA hrv hrSix
    have hDC : D.point ∈ circleContacts A Erdos957Cases24.Case4.v r := by
      apply mem_circleContacts.mpr
      have hDdata :=
        Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp D.point_mem
      exact ⟨hDdata.1, hDdata.2.1, by simpa [dist_comm] using hrD⟩
    have hcTwo : 1 < (circleContacts A Erdos957Cases24.Case4.v r).card := by
      omega
    obtain ⟨c₀, hc₀, c₁, hc₁, hc₀₁⟩ := Finset.one_lt_card.mp hcTwo
    let t := if c₀ = D.point then c₁ else c₀
    have htC : t ∈ circleContacts A Erdos957Cases24.Case4.v r := by
      dsimp [t]
      split_ifs <;> assumption
    have htD : t ≠ D.point := by
      dsimp [t]
      split_ifs with h
      · intro ht
        apply hc₀₁
        exact h.trans ht.symm
      · exact h
    have htData := mem_circleContacts.mp htC
    have htUnit : dist r t = 1 := htData.2.2
    have htR : t ≠ r := by
      intro h
      rw [h, dist_self] at htUnit
      norm_num at htUnit
    by_cases htPrev : t = Erdos957Cases24.Case2.uPrev
    · exact degree_six_residual_not_unit_to_uPrev hsep hstrict hvA huPrevA
        hrRes hrSix (by simpa [htPrev] using htUnit)
    by_cases htU : t = Erdos957Cases24.Case2.u
    · exact degree_six_residual_not_unit_to_u hsep hstrict hvA huA
        hrRes hrSix (by simpa [htU] using htUnit)
    have htRes : t ∈ Erdos957Case24Bridge.Case4.residualNeighbors A :=
      Erdos957Case24Bridge.Case4.mem_residualNeighbors.mpr
        ⟨htData.1, htData.2.1, htPrev, htU⟩
    have htCases : t = D.point ∨ t = r ∨ t = other := by
      rw [hresEq] at htRes
      simp only [Finset.mem_insert, Finset.mem_singleton] at htRes
      rcases htRes with ht | ht | ht
      · exact Or.inl ht
      · rcases hpair with ⟨hr, ho⟩ | ⟨hr, ho⟩
        · exact Or.inr (Or.inl (ht.trans hr.symm))
        · exact Or.inr (Or.inr (ht.trans ho.symm))
      · rcases hpair with ⟨hr, ho⟩ | ⟨hr, ho⟩
        · exact Or.inr (Or.inr (ht.trans ho.symm))
        · exact Or.inr (Or.inl (ht.trans hr.symm))
    rcases htCases with ht | ht | ht
    · exact htD ht
    · exact htR ht
    · have hrOtherUnit : dist r other = 1 := by simpa [ht] using htUnit
      exact not_three_pairwise_unit_on_unit_circle
        ((Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp D.point_mem).2.1)
        hrv
        ((Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hotherRes).2.1)
        hrD
        hrOtherUnit
        (by simpa [dist_comm] using hotherD)
  exact ⟨a, b, haRes, hbRes, haData.2.2, hbData.2.2, hab,
    degree_le_five_of_contact a b haRes hbRes haData.2.2 hbData.2.2 hab
      (Or.inl ⟨rfl, rfl⟩),
    degree_le_five_of_contact b a hbRes haRes hbData.2.2 haData.2.2 hab.symm
      (Or.inr ⟨rfl, rfl⟩)⟩

/-! The remaining geometry orders the two contacts around the farthest
residual point.  We keep the two reflected angle alternatives explicit,
matching the orientation flag in `HighFarthestRecipients`. -/

private lemma planar_unit_inner_half_gap_sq
    (X Y P Q : ℝ)
    (hXY : X ^ 2 + Y ^ 2 = 1)
    (hPQ : P ^ 2 + Q ^ 2 = 1)
    (hdot : X * P + Y * Q = 1 / 2) :
    (X - 2 * P) ^ 2 = 3 * Y ^ 2 := by
  let C : ℝ := X * Q - Y * P
  have hcrossSq : C ^ 2 = 3 / 4 := by
    calc
      C ^ 2 = (X ^ 2 + Y ^ 2) * (P ^ 2 + Q ^ 2) -
          (X * P + Y * Q) ^ 2 := by simp only [C]; ring
      _ = 3 / 4 := by rw [hXY, hPQ, hdot]; norm_num
  have hrotate : 2 * P - X = -2 * Y * C := by
    calc
      2 * P - X = (X ^ 2 + Y ^ 2) * (2 * P) - X := by
        rw [hXY]
        ring
      _ = -2 * Y * C + X * (2 * (X * P + Y * Q) - 1) := by
        simp only [C]
        ring
      _ = -2 * Y * C := by rw [hdot]; ring
  rw [show X - 2 * P = 2 * Y * C by linarith [hrotate], mul_pow,
    hcrossSq]
  ring

private lemma bracket_of_ordered_unit_chain_coordinates
    (X Y P Q R : ℝ)
    (hR : R = X - P)
    (hPQ : P ^ 2 + Q ^ 2 = 1)
    (hdot : X * P + Y * Q = 1 / 2)
    (hYQ : Y ≤ Q)
    (hQ : Q ≤ 0)
    (hPR : P ≤ R) :
    P ≤ X ∧ X ≤ R := by
  have hQdiff : 0 ≤ Q - Y := sub_nonneg.mpr hYQ
  have hQprod : Q * (Q - Y) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hQ hQdiff
  have hprodEq : (P - X) * (R - X) = Q * (Q - Y) - 1 / 2 := by
    rw [hR]
    calc
      (P - X) * (X - P - X) =
          ((X * P + Y * Q) - 1 / 2) -
            ((P ^ 2 + Q ^ 2) - 1) + Q * (Q - Y) - 1 / 2 := by ring
      _ = Q * (Q - Y) - 1 / 2 := by rw [hdot, hPQ]; ring
  have hprod : (P - X) * (R - X) ≤ 0 := by rw [hprodEq]; linarith
  constructor
  · by_contra hnot
    have hPX : 0 < P - X := sub_pos.mpr (lt_of_not_ge hnot)
    have hRX : 0 < R - X := by linarith
    exact (not_lt_of_ge hprod) (mul_pos hPX hRX)
  · by_contra hnot
    have hPX : P - X < 0 := by linarith
    have hRX : R - X < 0 := sub_neg.mpr (lt_of_not_ge hnot)
    exact (not_lt_of_ge hprod) (mul_pos_of_neg_of_neg hPX hRX)

private lemma gap_eq_negative_sqrt_mul
    (s gap y : ℝ)
    (hsSq : s ^ 2 = 3)
    (hs : 0 ≤ s)
    (hgap : 0 ≤ gap)
    (hy : y ≤ 0)
    (hgapSq : gap ^ 2 = 3 * y ^ 2) :
    gap = -s * y := by
  have hnegativeProduct : 0 ≤ -s * y :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hs) hy
  apply (sq_eq_sq₀ hgap hnegativeProduct).mp
  calc
    gap ^ 2 = 3 * y ^ 2 := hgapSq
    _ = (-s) ^ 2 * y ^ 2 := by
      rw [show (-s) ^ 2 = 3 by simpa only [neg_sq] using hsSq]
    _ = (-s * y) ^ 2 := by ring

private theorem ordered_residual_contacts_geometry
    {A : Finset Point}
    (hsep : IsOneSeparated A)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData A)
    {left right : Point}
    (hleft : left ∈ Erdos957Case24Bridge.Case4.residualNeighbors A)
    (hright : right ∈ Erdos957Case24Bridge.Case4.residualNeighbors A)
    (hleftContact : dist D.point left = 1)
    (hrightContact : dist D.point right = 1)
    (hne : left ≠ right)
    (horder : left 0 ≤ right 0) :
    left 0 ≤ D.point 0 ∧ D.point 0 ≤ right 0 ∧
      ((Erdos957Case24Bridge.Case4.directionDot
          Erdos957Cases24.Case4.v left Erdos957Cases24.Case2.uPrev ≤ 0 ∧
        0 ≤ Erdos957Case24Bridge.Case4.directionDot
          Erdos957Cases24.Case4.v right Erdos957Cases24.Case2.u) ∨
       (0 ≤ Erdos957Case24Bridge.Case4.directionDot
          Erdos957Cases24.Case4.v left Erdos957Cases24.Case2.uPrev ∧
        Erdos957Case24Bridge.Case4.directionDot
          Erdos957Cases24.Case4.v right Erdos957Cases24.Case2.u ≤ 0)) := by
  have hDdata := Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp D.point_mem
  have hleftData := Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hleft
  have hrightData := Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hright
  have hDLeft : D.point ≠ left := by
    intro h
    rw [h, dist_self] at hleftContact
    norm_num at hleftContact
  have hDRight : D.point ≠ right := by
    intro h
    rw [h, dist_self] at hrightContact
    norm_num at hrightContact
  let x : Point := left - Erdos957Cases24.Case4.v
  let y : Point := D.point - Erdos957Cases24.Case4.v
  let z : Point := right - Erdos957Cases24.Case4.v
  have hx : ‖x‖ = 1 := by
    simpa [x, dist_eq_norm, norm_sub_rev] using hleftData.2.1
  have hy : ‖y‖ = 1 := by
    simpa [y, dist_eq_norm, norm_sub_rev] using hDdata.2.1
  have hz : ‖z‖ = 1 := by
    simpa [z, dist_eq_norm, norm_sub_rev] using hrightData.2.1
  have hxy : ‖x - y‖ = 1 := by
    simpa [x, y, dist_eq_norm, sub_sub_sub_cancel_right, norm_sub_rev] using
      hleftContact
  have hyz : ‖y - z‖ = 1 := by
    simpa [y, z, dist_eq_norm, sub_sub_sub_cancel_right] using
      hrightContact
  have hxz : 1 ≤ ‖x - z‖ := by
    simpa [x, z, dist_eq_norm, sub_sub_sub_cancel_right] using
      hsep left hleftData.1 right hrightData.1 hne
  have hvec : z = y - x :=
    eq_sub_of_unit_chain hx hy hz hxy hyz hxz
  have hvec0 := congrArg (fun q : Point ↦ q 0) hvec
  have hvec1 := congrArg (fun q : Point ↦ q 1) hvec
  simp only [x, y, z, PiLp.sub_apply] at hvec0 hvec1
  have hDsq := Erdos957Cases24.dist_sq_eq_coordinates
    Erdos957Cases24.Case4.v D.point
  have hleftSq := Erdos957Cases24.dist_sq_eq_coordinates
    Erdos957Cases24.Case4.v left
  have hDLeftSq := Erdos957Cases24.dist_sq_eq_coordinates D.point left
  rw [hDdata.2.1] at hDsq
  rw [hleftData.2.1] at hleftSq
  rw [hleftContact] at hDLeftSq
  norm_num at hDsq hleftSq hDLeftSq
  simp only [Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one]
    at hvec0 hvec1 hDsq hleftSq
  have hDnorm :
      (D.point 0 + 1 / 2) ^ 2 +
        (D.point 1 + Erdos957Cases24.sqrtThree / 2) ^ 2 = 1 := by
    nlinarith [hDsq]
  have hleftNorm :
      (left 0 + 1 / 2) ^ 2 +
        (left 1 + Erdos957Cases24.sqrtThree / 2) ^ 2 = 1 := by
    nlinarith [hleftSq]
  have hdotHalf :
      (D.point 0 + 1 / 2) * (left 0 + 1 / 2) +
        (D.point 1 + Erdos957Cases24.sqrtThree / 2) *
          (left 1 + Erdos957Cases24.sqrtThree / 2) = 1 / 2 := by
    calc
      _ = (((D.point 0 + 1 / 2) ^ 2 +
              (D.point 1 + Erdos957Cases24.sqrtThree / 2) ^ 2) +
            ((left 0 + 1 / 2) ^ 2 +
              (left 1 + Erdos957Cases24.sqrtThree / 2) ^ 2) -
            ((D.point 0 - left 0) ^ 2 +
              (D.point 1 - left 1) ^ 2)) / 2 := by ring
      _ = 1 / 2 := by rw [hDnorm, hleftNorm, ← hDLeftSq]; norm_num
  have hDleLeft : D.point 1 ≤ left 1 := D.height_le hleft
  have hDleRight : D.point 1 ≤ right 1 := D.height_le hright
  have hleftYNonpos :
      left 1 + Erdos957Cases24.sqrtThree / 2 ≤ 0 := by
    linarith [hvec1, hDleRight]
  have hcenteredOrder :
      left 0 + 1 / 2 ≤ right 0 + 1 / 2 := by linarith
  have hcenteredR :
      right 0 + 1 / 2 =
        (D.point 0 + 1 / 2) - (left 0 + 1 / 2) := by
    linarith [hvec0]
  obtain ⟨hleftBracket', hrightBracket'⟩ :=
    bracket_of_ordered_unit_chain_coordinates
      (D.point 0 + 1 / 2)
      (D.point 1 + Erdos957Cases24.sqrtThree / 2)
      (left 0 + 1 / 2)
      (left 1 + Erdos957Cases24.sqrtThree / 2)
      (right 0 + 1 / 2)
      hcenteredR hleftNorm hdotHalf (by linarith) hleftYNonpos hcenteredOrder
  have hleftBracket : left 0 ≤ D.point 0 := by linarith
  have hrightBracket : D.point 0 ≤ right 0 := by linarith
  have hDverticalNonpos :
      D.point 1 + Erdos957Cases24.sqrtThree / 2 ≤ 0 := by
    linarith
  have hgapNonneg : 0 ≤ right 0 - left 0 := sub_nonneg.mpr horder
  have hgapCoordRaw :
      right 0 - left 0 =
        (D.point 0 + 1 / 2) - 2 * (left 0 + 1 / 2) := by
    linear_combination hvec0
  have hgapSq :
      (right 0 - left 0) ^ 2 =
        3 * (D.point 1 + Erdos957Cases24.sqrtThree / 2) ^ 2 := by
    calc
      (right 0 - left 0) ^ 2 =
          ((D.point 0 + 1 / 2) - 2 * (left 0 + 1 / 2)) ^ 2 := by
        rw [hgapCoordRaw]
      _ = 3 * (D.point 1 + Erdos957Cases24.sqrtThree / 2) ^ 2 :=
        planar_unit_inner_half_gap_sq
          (D.point 0 + 1 / 2)
          (D.point 1 + Erdos957Cases24.sqrtThree / 2)
          (left 0 + 1 / 2)
          (left 1 + Erdos957Cases24.sqrtThree / 2)
          hDnorm hleftNorm hdotHalf
  have hgapEq :
      right 0 - left 0 =
        -Erdos957Cases24.sqrtThree *
          (D.point 1 + Erdos957Cases24.sqrtThree / 2) := by
    exact gap_eq_negative_sqrt_mul
      Erdos957Cases24.sqrtThree
      (right 0 - left 0)
      (D.point 1 + Erdos957Cases24.sqrtThree / 2)
      Erdos957Cases24.sqrtThree_sq Erdos957Cases24.sqrtThree_pos.le
      hgapNonneg hDverticalNonpos hgapSq
  have hdotSum :
      Erdos957Case24Bridge.Case4.directionDot
          Erdos957Cases24.Case4.v left Erdos957Cases24.Case2.uPrev +
        Erdos957Case24Bridge.Case4.directionDot
          Erdos957Cases24.Case4.v right Erdos957Cases24.Case2.u = 0 := by
    simp only [Erdos957Case24Bridge.Case4.directionDot,
      Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v,
      Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one]
    linear_combination
      (1 / 2 : ℝ) * hgapEq +
      (Erdos957Cases24.sqrtThree / 2) * hvec1
  refine ⟨hleftBracket, hrightBracket, ?_⟩
  by_cases hleftDot :
      Erdos957Case24Bridge.Case4.directionDot
        Erdos957Cases24.Case4.v left Erdos957Cases24.Case2.uPrev ≤ 0
  · exact Or.inl ⟨hleftDot, by linarith⟩
  · exact Or.inr ⟨le_of_not_ge hleftDot, by linarith⟩

/-- Construct the complete ordered high-farthest recipient data.  The
orientation bit records which of the two reflected paper charts realizes
the source-specific angle roles. -/
theorem nonempty_highFarthestRecipients_of_degree_six
    {A : Finset Point}
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    (hvA : Erdos957Cases24.Case4.v ∈ A)
    (huPrevA : Erdos957Cases24.Case2.uPrev ∈ A)
    (huA : Erdos957Cases24.Case2.u ∈ A)
    (hvDegree : unitDegree A Erdos957Cases24.Case4.v = 5)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData A)
    (hDSix : unitDegree A D.point = 6) :
    Nonempty (Erdos957Case24Bridge.Case4.HighFarthestRecipients A D) := by
  obtain ⟨a, b, ha, hb, haContact, hbContact, hab, haDegree, hbDegree⟩ :=
    exists_two_low_residual_contacts_of_farthest_degree_six
      hsep hstrict hvA huPrevA huA hvDegree D hDSix
  by_cases habOrder : a 0 ≤ b 0
  · obtain ⟨haD, hDb, horient⟩ :=
      ordered_residual_contacts_geometry hsep D ha hb haContact hbContact hab
        habOrder
    rcases horient with horient | horient
    · exact ⟨⟨a, b, ha, hb, haContact, hbContact, hab, haD, hDb, true,
        by simpa using horient, haDegree, hbDegree⟩⟩
    · exact ⟨⟨a, b, ha, hb, haContact, hbContact, hab, haD, hDb, false,
        by simpa using horient, haDegree, hbDegree⟩⟩
  · have hbaOrder : b 0 ≤ a 0 := le_of_not_ge habOrder
    obtain ⟨hbD, hDa, horient⟩ :=
      ordered_residual_contacts_geometry hsep D hb ha hbContact haContact hab.symm
        hbaOrder
    rcases horient with horient | horient
    · exact ⟨⟨b, a, hb, ha, hbContact, haContact, hab.symm, hbD, hDa, true,
        by simpa using horient, hbDegree, haDegree⟩⟩
    · exact ⟨⟨b, a, hb, ha, hbContact, haContact, hab.symm, hbD, hDa, false,
        by simpa using horient, hbDegree, haDegree⟩⟩

/-- The complete, honest Case-4 farthest-neighbor split.  If the selected
farthest residual point has degree at most five it is used directly;
otherwise the planar kissing bound makes its degree exactly six, and the
two ordered low-degree side recipients are supplied by the high branch. -/
theorem nonempty_farthestBranchData
    {A : Finset Point}
    (hsep : IsOneSeparated A)
    (hstrict : StrictlyBelowOutside A
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u})
    (hvA : Erdos957Cases24.Case4.v ∈ A)
    (huPrevA : Erdos957Cases24.Case2.uPrev ∈ A)
    (huA : Erdos957Cases24.Case2.u ∈ A)
    (hvDegree : unitDegree A Erdos957Cases24.Case4.v = 5)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData A) :
    Nonempty (Erdos957Case24Bridge.Case4.FarthestBranchData A D) := by
  by_cases hlow : unitDegree A D.point ≤ 5
  · exact ⟨Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow⟩
  · have hupper : unitDegree A D.point ≤ 6 := unitDegree_le_six hsep D.point
    have hsix : unitDegree A D.point = 6 := by omega
    obtain ⟨recipients⟩ := nonempty_highFarthestRecipients_of_degree_six
      hsep hstrict hvA huPrevA huA hvDegree D hsix
    exact ⟨Erdos957Case24Bridge.Case4.FarthestBranchData.high hsix recipients⟩

end Erdos957ContactGraph
