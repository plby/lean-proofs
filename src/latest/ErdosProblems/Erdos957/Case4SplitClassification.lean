import ErdosProblems.Erdos957.CoherentRealizedRows
import ErdosProblems.Erdos957.RoleCollisions
import ErdosProblems.Erdos957.Case4NoThree
import ErdosProblems.Erdos957.Case2RoleUniqueness
import ErdosProblems.Erdos957.Case4SplitDistance

/-!
# Classification facts for coincident generalized Case-4 recipients

The two endpoints of one selected Case-4 hull edge use complementary
recipient bits in the same source-free rigid chart.  Consequently, if
their selected split-right targets coincide, the common branch is the low
branch.  This is the exact same-edge part of the honest collision
classification; the adjacent-edge low alternative is intentionally not
excluded here.
-/

noncomputable section

namespace Erdos957Case4SplitClassification

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification
open Erdos957CoherentRealizedRows
open Erdos957CollisionInstantiation
open Erdos957RoleCollisions
open Erdos957Overcharge

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

private lemma cast_twoExtreme_side
    {source : {p // p ∈ P.H}} {m n : Vertex A} (h : m = n)
    (T : TwoExtremeCyclicWitness P source m) :
    (Eq.mp (congrArg (fun z ↦ TwoExtremeCyclicWitness P source z) h) T).side =
      T.side := by
  subst n
  rfl

private lemma cyclicSideAssociation_injective :
    Function.Injective cyclicSideAssociation := by
  intro a b h
  cases a <;> cases b <;> simp_all [cyclicSideAssociation]

/-- Sharp horizontal interval for every residual neighbour of the
normalized Case-4 middle `v=(-1/2,-sqrt 3/2)`.  The asymmetric upper bound
is useful when two consecutive edge charts are compared. -/
lemma residual_fst_mem_sharp_interval
    {B : Finset Point} {q : Point}
    (hq : q ∈ Erdos957Case24Bridge.Case4.residualNeighbors B) :
    -(3 / 2 : ℝ) ≤ q 0 ∧ q 0 ≤ (1 / 2 : ℝ) := by
  have hd := (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hq).2.1
  have hdSq := congrArg (fun x : ℝ ↦ x ^ 2) hd
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hdSq
  simp only [Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow] at hdSq
  constructor
  · nlinarith [sq_nonneg (q 1 + Erdos957Cases24.sqrtThree / 2)]
  · nlinarith [sq_nonneg (q 0 - 1 / 2),
      sq_nonneg (q 1 + Erdos957Cases24.sqrtThree / 2)]

/-- The lexicographically farthest residual neighbor is no higher than the
normalized middle.  If all five unit neighbors of the middle were strictly
above it, translating them to the unit circle would put five one-separated
unit vectors in an open half-plane, contradicting the sharp three-point
half-plane packing bound. -/
lemma farthestBelowData_snd_le_middle
    {B : Finset Point} (hB : IsOneSeparated B)
    (hdegree : Erdos957Case24Bridge.unitDegree B
      Erdos957Cases24.Case4.v = 5)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData B) :
    D.point 1 ≤ Erdos957Cases24.Case4.v 1 := by
  classical
  by_contra hnot
  have hvD : Erdos957Cases24.Case4.v 1 < D.point 1 := lt_of_not_ge hnot
  let N := Erdos957Cases24.unitNeighbors B Erdos957Cases24.Case4.v
  let f : Point → ℂ := fun q ↦
    Erdos957Case24Bridge.toComplex (q - Erdos957Cases24.Case4.v)
  let V : Finset ℂ := N.image f
  have hf : Function.Injective f := by
    intro q r hqr
    change Erdos957Case24Bridge.toComplex
        (q - Erdos957Cases24.Case4.v) =
      Erdos957Case24Bridge.toComplex
        (r - Erdos957Cases24.Case4.v) at hqr
    exact sub_left_injective
      (Erdos957Case24Bridge.toComplex_injective hqr)
  have hcard : V.card = 5 := by
    rw [Finset.card_image_of_injective N hf]
    exact hdegree
  have hnorm : ∀ z ∈ V, ‖z‖ = 1 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
    have hqdist := (Erdos957Cases24.mem_unitNeighbors.mp hq).2
    change ‖Erdos957Case24Bridge.toComplex
      (q - Erdos957Cases24.Case4.v)‖ = 1
    rw [Erdos957Case24Bridge.toComplex_sub, ← dist_eq_norm,
      Erdos957Case24Bridge.dist_toComplex]
    simpa [dist_comm] using hqdist
  have him : ∀ z ∈ V, 0 < z.im := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨q, hq, rfl⟩
    have hqdata := Erdos957Cases24.mem_unitNeighbors.mp hq
    have hqAbove : Erdos957Cases24.Case4.v 1 < q 1 := by
      by_cases hprev : q = Erdos957Cases24.Case2.uPrev
      · subst q
        simp only [Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v,
          Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point_apply_one]
        have := Erdos957Cases24.sqrtThree_pos
        linarith
      by_cases hu : q = Erdos957Cases24.Case2.u
      · subst q
        simp only [Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v,
          Erdos957Cases24.Case2.u, Erdos957Cases24.point_apply_one]
        have := Erdos957Cases24.sqrtThree_pos
        linarith
      · have hres : q ∈ Erdos957Case24Bridge.Case4.residualNeighbors B :=
          Erdos957Case24Bridge.Case4.mem_residualNeighbors.mpr
            ⟨hqdata.1, hqdata.2, hprev, hu⟩
        exact hvD.trans_le (D.height_le hres)
    simpa [f, Erdos957Case24Bridge.toComplex] using
      (sub_pos.mpr hqAbove)
  have hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨r, hr, rfl⟩
    have hqr : q ≠ r := fun h ↦ hxy (congrArg f h)
    have hdist := hB q (Erdos957Cases24.mem_unitNeighbors.mp hq).1
      r (Erdos957Cases24.mem_unitNeighbors.mp hr).1 hqr
    calc
      1 ≤ dist q r := hdist
      _ = ‖Erdos957Case24Bridge.toComplex (q - r)‖ := by
        rw [← Erdos957Case24Bridge.dist_toComplex]
        simp [dist_eq_norm]
      _ = ‖f q - f r‖ := by
        simp [f, ← Erdos957Case24Bridge.toComplex_sub]
  have hle := Erdos957Hex.card_le_three_of_unit_oneSeparated_of_im_pos
    V hnorm him hsep
  rw [hcard] at hle
  omega

/-! The endpoint-sensitive zero convention needs one further fact about the
paper's farthest-below choice.  Measured from the equilateral middle, the
chosen residual direction lies in the closed central lower sector.  The
next three elementary lemmas prove this directly from one-separation; no
lattice rigidity is used. -/

lemma residual_centered_snd_nonpos
    {B : Finset Point} (hB : IsOneSeparated B)
    (huPrev : Erdos957Cases24.Case2.uPrev ∈ B)
    (hu : Erdos957Cases24.Case2.u ∈ B)
    {q : Point}
    (hq : q ∈ Erdos957Case24Bridge.Case4.residualNeighbors B) :
    q 1 - Erdos957Cases24.Case4.v 1 ≤ 0 := by
  have hdata := Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hq
  have hqu := hB q hdata.1 Erdos957Cases24.Case2.u hu hdata.2.2.2
  have hqp := hB q hdata.1 Erdos957Cases24.Case2.uPrev huPrev hdata.2.2.1
  have hquSq : 1 ≤ dist q Erdos957Cases24.Case2.u ^ 2 := by
    nlinarith only [hqu, dist_nonneg
      (x := q) (y := Erdos957Cases24.Case2.u)]
  have hqpSq : 1 ≤ dist q Erdos957Cases24.Case2.uPrev ^ 2 := by
    nlinarith only [hqp, dist_nonneg
      (x := q) (y := Erdos957Cases24.Case2.uPrev)]
  have hqNorm := congrArg (fun z : ℝ ↦ z ^ 2) hdata.2.1
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hquSq hqpSq hqNorm
  simp only [Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v,
    Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.uPrev,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow] at hquSq hqpSq hqNorm ⊢
  let x : ℝ := q 0 + 1 / 2
  let y : ℝ := q 1 + Erdos957Cases24.sqrtThree / 2
  have hnorm : x ^ 2 + y ^ 2 = 1 := by
    dsimp [x, y]
    nlinarith only [hqNorm]
  have hright : x + Erdos957Cases24.sqrtThree * y ≤ 1 := by
    dsimp [x, y]
    nlinarith only [hquSq, hqNorm, Erdos957Cases24.sqrtThree_sq]
  have hleft : -x + Erdos957Cases24.sqrtThree * y ≤ 1 := by
    dsimp [x, y]
    nlinarith only [hqpSq, hqNorm, Erdos957Cases24.sqrtThree_sq]
  by_contra hy
  have hypos : 0 < y := by
    dsimp [y]
    linarith only [lt_of_not_ge hy]
  by_cases hx : 0 ≤ x
  · have hxle : x ≤ 1 := by
      nlinarith only [hnorm, sq_nonneg (x - 1)]
    have hxlt : x < 1 := by
      nlinarith only [hnorm, hypos, sq_nonneg y]
    have hplus : 0 ≤ 1 - x + Erdos957Cases24.sqrtThree * y := by
      have hspos := Erdos957Cases24.sqrtThree_pos
      nlinarith only [hxle, hypos, hspos]
    have hminus : 0 ≤ 1 - x - Erdos957Cases24.sqrtThree * y := by
      linarith only [hright]
    have hprod := mul_nonneg hminus hplus
    have hfactor : 0 < (2 * x + 1) * (1 - x) :=
      mul_pos (by nlinarith only [hx]) (sub_pos.mpr hxlt)
    nlinarith only [hprod, hfactor, hnorm, hx, hypos,
      Erdos957Cases24.sqrtThree_sq]
  · have hxnonpos : x ≤ 0 := le_of_not_ge hx
    have hxge : -1 ≤ x := by
      nlinarith only [hnorm, sq_nonneg (x + 1)]
    have hxgt : -1 < x := by
      nlinarith only [hnorm, hypos, sq_nonneg y]
    have hplus : 0 ≤ 1 + x + Erdos957Cases24.sqrtThree * y := by
      have hspos := Erdos957Cases24.sqrtThree_pos
      nlinarith only [hxge, hypos, hspos]
    have hminus : 0 ≤ 1 + x - Erdos957Cases24.sqrtThree * y := by
      linarith only [hleft]
    have hprod := mul_nonneg hminus hplus
    have hfactor : 0 < (1 - 2 * x) * (1 + x) :=
      mul_pos (by nlinarith only [hxnonpos]) (by linarith only [hxgt])
    nlinarith only [hprod, hfactor, hnorm, hxnonpos, hypos,
      Erdos957Cases24.sqrtThree_sq]

private lemma unit_lower_same_outer_half_sqDist_lt_one
    {px py qx qy : ℝ}
    (hpNorm : px ^ 2 + py ^ 2 = 1)
    (hqNorm : qx ^ 2 + qy ^ 2 = 1)
    (hpLower : py ≤ 0) (hqLower : qy ≤ 0)
    (hside : ((1 / 2 : ℝ) < px ∧ (1 / 2 : ℝ) < qx) ∨
      (px < -(1 / 2 : ℝ) ∧ qx < -(1 / 2 : ℝ))) :
    (px - qx) ^ 2 + (py - qy) ^ 2 < 1 := by
  have hspos := Erdos957Cases24.sqrtThree_pos
  have hsSq := Erdos957Cases24.sqrtThree_sq
  rcases hside with hpos | hneg
  · have hpXle : px ≤ 1 := by
      nlinarith only [hpNorm, sq_nonneg (px - 1)]
    have hqXle : qx ≤ 1 := by
      nlinarith only [hqNorm, sq_nonneg (qx - 1)]
    have hpYlow : -(Erdos957Cases24.sqrtThree / 2) < py := by
      nlinarith only [hpNorm, hpos.1, hpLower, hspos, hsSq]
    have hqYlow : -(Erdos957Cases24.sqrtThree / 2) < qy := by
      nlinarith only [hqNorm, hpos.2, hqLower, hspos, hsSq]
    let dot : ℝ := px * qx + py * qy
    let cross : ℝ := px * qy - py * qx
    have hpyqy : 0 ≤ py * qy := mul_nonneg_of_nonpos_of_nonpos hpLower hqLower
    have hdotPos : 0 < dot := by
      dsimp [dot]
      nlinarith only [hpos.1, hpos.2, hpyqy]
    have hcrossUpper : cross < Erdos957Cases24.sqrtThree / 2 := by
      have h1 : 0 ≤ (1 - qx) * (-py) :=
        mul_nonneg (sub_nonneg.mpr hqXle) (neg_nonneg.mpr hpLower)
      have h2 : 0 ≤ px * (-qy) :=
        mul_nonneg (le_trans (by norm_num) hpos.1.le) (neg_nonneg.mpr hqLower)
      dsimp [cross]
      nlinarith only [h1, h2, hpYlow]
    have hcrossLower : -(Erdos957Cases24.sqrtThree / 2) < cross := by
      have h1 : 0 ≤ (1 - px) * (-qy) :=
        mul_nonneg (sub_nonneg.mpr hpXle) (neg_nonneg.mpr hqLower)
      have h2 : 0 ≤ qx * (-py) :=
        mul_nonneg (le_trans (by norm_num) hpos.2.le) (neg_nonneg.mpr hpLower)
      dsimp [cross]
      nlinarith only [h1, h2, hqYlow]
    have hcrossSq : cross ^ 2 < 3 / 4 := by
      have hprod : 0 <
          (Erdos957Cases24.sqrtThree / 2 - cross) *
            (Erdos957Cases24.sqrtThree / 2 + cross) :=
        mul_pos (sub_pos.mpr hcrossUpper) (by linarith only [hcrossLower])
      nlinarith only [hprod, hsSq]
    have hidentity : dot ^ 2 + cross ^ 2 = 1 := by
      dsimp [dot, cross]
      nlinarith only [hpNorm, hqNorm]
    have hdot : 1 / 2 < dot := by
      nlinarith only [hcrossSq, hidentity, hdotPos]
    dsimp [dot] at hdot
    nlinarith only [hpNorm, hqNorm, hdot]
  · have hpXge : -1 ≤ px := by
      nlinarith only [hpNorm, sq_nonneg (px + 1)]
    have hqXge : -1 ≤ qx := by
      nlinarith only [hqNorm, sq_nonneg (qx + 1)]
    have hpYlow : -(Erdos957Cases24.sqrtThree / 2) < py := by
      nlinarith only [hpNorm, hneg.1, hpLower, hspos, hsSq]
    have hqYlow : -(Erdos957Cases24.sqrtThree / 2) < qy := by
      nlinarith only [hqNorm, hneg.2, hqLower, hspos, hsSq]
    let dot : ℝ := px * qx + py * qy
    let cross : ℝ := px * qy - py * qx
    have hpyqy : 0 ≤ py * qy := mul_nonneg_of_nonpos_of_nonpos hpLower hqLower
    have hdotPos : 0 < dot := by
      dsimp [dot]
      nlinarith only [hneg.1, hneg.2, hpyqy]
    have hcrossUpper : cross < Erdos957Cases24.sqrtThree / 2 := by
      have h1 : 0 ≤ (1 + px) * (-qy) :=
        mul_nonneg (by linarith only [hpXge]) (neg_nonneg.mpr hqLower)
      have h2 : 0 ≤ (-qx) * (-py) :=
        mul_nonneg (by linarith only [hneg.2]) (neg_nonneg.mpr hpLower)
      dsimp [cross]
      nlinarith only [h1, h2, hqYlow]
    have hcrossLower : -(Erdos957Cases24.sqrtThree / 2) < cross := by
      have h1 : 0 ≤ (1 + qx) * (-py) :=
        mul_nonneg (by linarith only [hqXge]) (neg_nonneg.mpr hpLower)
      have h2 : 0 ≤ (-px) * (-qy) :=
        mul_nonneg (by linarith only [hneg.1]) (neg_nonneg.mpr hqLower)
      dsimp [cross]
      nlinarith only [h1, h2, hpYlow]
    have hcrossSq : cross ^ 2 < 3 / 4 := by
      have hprod : 0 <
          (Erdos957Cases24.sqrtThree / 2 - cross) *
            (Erdos957Cases24.sqrtThree / 2 + cross) :=
        mul_pos (sub_pos.mpr hcrossUpper) (by linarith only [hcrossLower])
      nlinarith only [hprod, hsSq]
    have hidentity : dot ^ 2 + cross ^ 2 = 1 := by
      dsimp [dot, cross]
      nlinarith only [hpNorm, hqNorm]
    have hdot : 1 / 2 < dot := by
      nlinarith only [hcrossSq, hidentity, hdotPos]
    dsimp [dot] at hdot
    nlinarith only [hpNorm, hqNorm, hdot]

/-- The farthest-below residual lies horizontally between the two source
normal rays.  In absolute coordinates this is the interval `[-1,0]`. -/
lemma farthestBelowData_fst_mem_source_interval
    {B : Finset Point} (hB : IsOneSeparated B)
    (huPrev : Erdos957Cases24.Case2.uPrev ∈ B)
    (hu : Erdos957Cases24.Case2.u ∈ B)
    (hdegree : Erdos957Case24Bridge.unitDegree B
      Erdos957Cases24.Case4.v = 5)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData B) :
    -(1 : ℝ) ≤ D.point 0 ∧ D.point 0 ≤ 0 := by
  classical
  let R := Erdos957Case24Bridge.Case4.residualNeighbors B
  have hcard : R.card = 3 :=
    Erdos957Case24Bridge.Case4.card_residualNeighbors_eq_three
      huPrev hu hdegree
  have hEraseCard : (R.erase D.point).card = 2 := by
    rw [Finset.card_erase_of_mem D.point_mem, hcard]
  obtain ⟨p, q, hpq, hpqSet⟩ := Finset.card_eq_two.mp hEraseCard
  have hpErase : p ∈ R.erase D.point := by simp [hpqSet]
  have hqErase : q ∈ R.erase D.point := by simp [hpqSet]
  have hpMem : p ∈ R := (Finset.mem_erase.mp hpErase).2
  have hqMem : q ∈ R := (Finset.mem_erase.mp hqErase).2
  have hpNeD : p ≠ D.point := (Finset.mem_erase.mp hpErase).1
  have hqNeD : q ≠ D.point := (Finset.mem_erase.mp hqErase).1
  let dx : ℝ := D.point 0 + 1 / 2
  let dy : ℝ := D.point 1 + Erdos957Cases24.sqrtThree / 2
  let px : ℝ := p 0 + 1 / 2
  let py : ℝ := p 1 + Erdos957Cases24.sqrtThree / 2
  let qx : ℝ := q 0 + 1 / 2
  let qy : ℝ := q 1 + Erdos957Cases24.sqrtThree / 2
  have norm_of_mem : ∀ {r : Point}, r ∈ R →
      (r 0 + 1 / 2) ^ 2 +
        (r 1 + Erdos957Cases24.sqrtThree / 2) ^ 2 = 1 := by
    intro r hr
    have hd := (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hr).2.1
    have hs := congrArg (fun z : ℝ ↦ z ^ 2) hd
    rw [Erdos957Cases24.dist_sq_eq_coordinates] at hs
    simp only [Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
      one_pow] at hs
    nlinarith only [hs]
  have hdNorm : dx ^ 2 + dy ^ 2 = 1 := by
    simpa [dx, dy] using norm_of_mem D.point_mem
  have hpNorm : px ^ 2 + py ^ 2 = 1 := by
    simpa [px, py] using norm_of_mem hpMem
  have hqNorm : qx ^ 2 + qy ^ 2 = 1 := by
    simpa [qx, qy] using norm_of_mem hqMem
  have hdLower : dy ≤ 0 := by
    simpa [dy, Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v] using
      residual_centered_snd_nonpos hB huPrev hu D.point_mem
  have hpLower : py ≤ 0 := by
    simpa [py, Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v] using
      residual_centered_snd_nonpos hB huPrev hu hpMem
  have hqLower : qy ≤ 0 := by
    simpa [qy, Erdos957Cases24.Case4.v, Erdos957Cases24.Case2.v] using
      residual_centered_snd_nonpos hB huPrev hu hqMem
  have hdyPy : dy ≤ py := by
    dsimp [dy, py]
    linarith only [D.height_le hpMem]
  have hdyQy : dy ≤ qy := by
    dsimp [dy, qy]
    linarith only [D.height_le hqMem]
  have sep_sq {r z : Point} (hr : r ∈ R) (hz : z ∈ R)
      (hrz : r ≠ z) :
      1 ≤ (r 0 - z 0) ^ 2 + (r 1 - z 1) ^ 2 := by
    have hrd := Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hr
    have hzd := Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hz
    have hs := hB r hrd.1 z hzd.1 hrz
    have hsSq : 1 ≤ dist r z ^ 2 := by
      nlinarith only [hs, dist_nonneg (x := r) (y := z)]
    rw [Erdos957Cases24.dist_sq_eq_coordinates] at hsSq
    exact hsSq
  constructor
  · by_contra hleft
    have hdx : dx < -(1 / 2 : ℝ) := by
      dsimp [dx]
      linarith only [lt_of_not_ge hleft]
    have hdyAbove : -(Erdos957Cases24.sqrtThree / 2) < dy := by
      nlinarith only [hdNorm, hdx, hdLower,
        Erdos957Cases24.sqrtThree_pos, Erdos957Cases24.sqrtThree_sq]
    have hpYAbove : -(Erdos957Cases24.sqrtThree / 2) < py :=
      lt_of_lt_of_le hdyAbove hdyPy
    have hqYAbove : -(Erdos957Cases24.sqrtThree / 2) < qy :=
      lt_of_lt_of_le hdyAbove hdyQy
    have hpOuter : (1 / 2 : ℝ) < px := by
      have hpSq : (1 / 4 : ℝ) < px ^ 2 := by
        nlinarith only [hpNorm, hpYAbove, hpLower,
          Erdos957Cases24.sqrtThree_pos, Erdos957Cases24.sqrtThree_sq]
      by_contra hpx
      have hpxle : px ≤ 1 / 2 := le_of_not_gt hpx
      by_cases hpxneg : px < -(1 / 2 : ℝ)
      · have hclose := unit_lower_same_outer_half_sqDist_lt_one
          hdNorm hpNorm hdLower hpLower (Or.inr ⟨hdx, hpxneg⟩)
        have hsep := sep_sq D.point_mem hpMem hpNeD.symm
        dsimp [dx, dy, px, py] at hclose
        nlinarith only [hclose, hsep]
      · have hpxge : -(1 / 2 : ℝ) ≤ px := le_of_not_gt hpxneg
        nlinarith only [hpSq, hpxle, hpxge]
    have hqOuter : (1 / 2 : ℝ) < qx := by
      have hqSq : (1 / 4 : ℝ) < qx ^ 2 := by
        nlinarith only [hqNorm, hqYAbove, hqLower,
          Erdos957Cases24.sqrtThree_pos, Erdos957Cases24.sqrtThree_sq]
      by_contra hqx
      have hqxle : qx ≤ 1 / 2 := le_of_not_gt hqx
      by_cases hqxneg : qx < -(1 / 2 : ℝ)
      · have hclose := unit_lower_same_outer_half_sqDist_lt_one
          hdNorm hqNorm hdLower hqLower (Or.inr ⟨hdx, hqxneg⟩)
        have hsep := sep_sq D.point_mem hqMem hqNeD.symm
        dsimp [dx, dy, qx, qy] at hclose
        nlinarith only [hclose, hsep]
      · have hqxge : -(1 / 2 : ℝ) ≤ qx := le_of_not_gt hqxneg
        nlinarith only [hqSq, hqxle, hqxge]
    have hclose := unit_lower_same_outer_half_sqDist_lt_one
      hpNorm hqNorm hpLower hqLower (Or.inl ⟨hpOuter, hqOuter⟩)
    have hsep := sep_sq hpMem hqMem hpq
    dsimp [px, py, qx, qy] at hclose
    nlinarith only [hclose, hsep]
  · by_contra hright
    have hdx : (1 / 2 : ℝ) < dx := by
      dsimp [dx]
      linarith only [lt_of_not_ge hright]
    have hdyAbove : -(Erdos957Cases24.sqrtThree / 2) < dy := by
      nlinarith only [hdNorm, hdx, hdLower,
        Erdos957Cases24.sqrtThree_pos, Erdos957Cases24.sqrtThree_sq]
    have hpYAbove : -(Erdos957Cases24.sqrtThree / 2) < py :=
      lt_of_lt_of_le hdyAbove hdyPy
    have hqYAbove : -(Erdos957Cases24.sqrtThree / 2) < qy :=
      lt_of_lt_of_le hdyAbove hdyQy
    have hpOuter : px < -(1 / 2 : ℝ) := by
      have hpSq : (1 / 4 : ℝ) < px ^ 2 := by
        nlinarith only [hpNorm, hpYAbove, hpLower,
          Erdos957Cases24.sqrtThree_pos, Erdos957Cases24.sqrtThree_sq]
      by_contra hpx
      have hpxge : -(1 / 2 : ℝ) ≤ px := le_of_not_gt hpx
      by_cases hpxpos : (1 / 2 : ℝ) < px
      · have hclose := unit_lower_same_outer_half_sqDist_lt_one
          hdNorm hpNorm hdLower hpLower (Or.inl ⟨hdx, hpxpos⟩)
        have hsep := sep_sq D.point_mem hpMem hpNeD.symm
        dsimp [dx, dy, px, py] at hclose
        nlinarith only [hclose, hsep]
      · have hpxle : px ≤ 1 / 2 := le_of_not_gt hpxpos
        nlinarith only [hpSq, hpxle, hpxge]
    have hqOuter : qx < -(1 / 2 : ℝ) := by
      have hqSq : (1 / 4 : ℝ) < qx ^ 2 := by
        nlinarith only [hqNorm, hqYAbove, hqLower,
          Erdos957Cases24.sqrtThree_pos, Erdos957Cases24.sqrtThree_sq]
      by_contra hqx
      have hqxge : -(1 / 2 : ℝ) ≤ qx := le_of_not_gt hqx
      by_cases hqxpos : (1 / 2 : ℝ) < qx
      · have hclose := unit_lower_same_outer_half_sqDist_lt_one
          hdNorm hqNorm hdLower hqLower (Or.inl ⟨hdx, hqxpos⟩)
        have hsep := sep_sq D.point_mem hqMem hqNeD.symm
        dsimp [dx, dy, qx, qy] at hclose
        nlinarith only [hclose, hsep]
      · have hqxle : qx ≤ 1 / 2 := le_of_not_gt hqxpos
        nlinarith only [hqSq, hqxle, hqxge]
    have hclose := unit_lower_same_outer_half_sqDist_lt_one
      hpNorm hqNorm hpLower hqLower (Or.inr ⟨hpOuter, hqOuter⟩)
    have hsep := sep_sq hpMem hqMem hpq
    dsimp [px, py, qx, qy] at hclose
    nlinarith only [hclose, hsep]

/-- In the low branch the common recipient is shared by the two endpoints,
but the endpoint-sensitive vertical-tie convention assigns it to opposite
cyclic associations. -/
lemma low_commonPairHorizontalAssociations_ne
    {B : Finset Point} (hB : IsOneSeparated B)
    (huPrev : Erdos957Cases24.Case2.uPrev ∈ B)
    (hu : Erdos957Cases24.Case2.u ∈ B)
    (hdegree : Erdos957Case24Bridge.unitDegree B
      Erdos957Cases24.Case4.v = 5)
    (D : Erdos957Case24Bridge.Case4.FarthestBelowData B)
    (hlow : Erdos957Case24Bridge.unitDegree B D.point ≤ 5) :
    commonPairHorizontalAssociation
        (Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow) true ≠
      commonPairHorizontalAssociation
        (Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow) false := by
  have hx := farthestBelowData_fst_mem_source_interval
    hB huPrev hu hdegree D
  have hleft : ¬ D.point 0 + 1 < 0 := by linarith only [hx.1]
  have hrightAssoc : commonPairHorizontalAssociation
      (Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow) true =
        ArrivalAssociation.fromPrevious := by
    simp [commonPairHorizontalAssociation,
      Erdos957Case24Bridge.Case4.sideSource,
      Erdos957Cases24.Case2.u, Erdos957Cases24.point,
      horizontalAssociation, hx.2]
  have hleftAssoc : commonPairHorizontalAssociation
      (Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow) false =
        ArrivalAssociation.fromNext := by
    simp [commonPairHorizontalAssociation,
      Erdos957Case24Bridge.Case4.sideSource,
      Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point, hleft]
  rw [hrightAssoc, hleftAssoc]
  decide

lemma CommonPairedCase4Rows.low_branch_endpoint_associations_ne
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (hA : IsOneSeparated A)
    (Q : CommonPairedCase4Rows rows u hu)
    (hlow : Erdos957Case24Bridge.unitDegree
      (Q.commonFrame.frame.image A) Q.pairBranch.farthest.point ≤ 5)
    (hbranch : Q.pairBranch.branch =
      Erdos957Case24Bridge.Case4.FarthestBranchData.low hlow) :
    commonPairHorizontalAssociation Q.pairBranch.branch
        (ActualCase24Rows.case4SourceIsRight Q.twoExtreme) ≠
      commonPairHorizontalAssociation Q.pairBranch.branch
        (!(ActualCase24Rows.case4SourceIsRight Q.twoExtreme)) := by
  have huPrevA : Erdos957Cases24.Case2.uPrev ∈
      Q.commonFrame.frame.image A := by
    apply Q.commonFrame.frame.mem_image_iff.mpr
    cases hright : ActualCase24Rows.case4SourceIsRight Q.twoExtreme
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.uPrev =
          (sourceIndex P W u hu).1 := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.source_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (sourceIndex P W u hu).1.property
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.uPrev =
          cyclicSideVertex P (sourceIndex P W u hu) Q.twoExtreme.side := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.side_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (cyclicSideVertex P (sourceIndex P W u hu)
        Q.twoExtreme.side).property
  have huA : Erdos957Cases24.Case2.u ∈
      Q.commonFrame.frame.image A := by
    apply Q.commonFrame.frame.mem_image_iff.mpr
    cases hright : ActualCase24Rows.case4SourceIsRight Q.twoExtreme
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.u =
          cyclicSideVertex P (sourceIndex P W u hu) Q.twoExtreme.side := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.side_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (cyclicSideVertex P (sourceIndex P W u hu)
        Q.twoExtreme.side).property
    · have heq : Q.commonFrame.frame.actual Erdos957Cases24.Case2.u =
          (sourceIndex P W u hu).1 := by
        apply Q.commonFrame.frame.toCanonical.injective
        rw [Q.commonFrame.frame.toCanonical_actual,
          Q.commonFrame.source_coordinate]
        simp [hright, Erdos957Case24Bridge.Case4.sideSource]
      rw [heq]
      exact (sourceIndex P W u hu).1.property
  have hvDegree : Erdos957Case24Bridge.unitDegree
      (Q.commonFrame.frame.image A) Erdos957Cases24.Case4.v = 5 := by
    rw [Q.commonFrame.frame.unitDegree_image_actual A,
      Erdos957Cases24.Case4.v, Q.commonFrame.middle_actual]
    rw [← ActualCase24Rows.graph_degree_eq_unitDegree]
    exact Q.middle_degree_five
  have hne := low_commonPairHorizontalAssociations_ne
    (Q.commonFrame.frame.image_oneSeparated hA) huPrevA huA hvDegree
      Q.pairBranch.farthest hlow
  rw [hbranch]
  cases ActualCase24Rows.case4SourceIsRight Q.twoExtreme
  · exact hne.symm
  · exact hne

/-- Formula-level form of the sharp residual interval for every actually
selected split-right recipient. -/
lemma Case4SplitRightFormula.target_horizontal_sharp
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Erdos957Case2RoleUniqueness.Case4SplitRightFormula
      (P := P) (source := source) v) :
    -(3 / 2 : ℝ) ≤ D.targetCanonical 0 ∧
      D.targetCanonical 0 ≤ (1 / 2 : ℝ) := by
  cases D with
  | orderedLow side side_unit frame frame_spec source_actual middle
      middle_coordinate farthest target_coordinate =>
      change -(3 / 2 : ℝ) ≤ (frame.toCanonical v) 0 ∧
        (frame.toCanonical v) 0 ≤ (1 / 2 : ℝ)
      rw [target_coordinate]
      exact residual_fst_mem_sharp_interval farthest.point_mem
  | orderedHigh side side_unit frame frame_spec source_actual middle
      middle_coordinate farthest recipients target_coordinate =>
      change -(3 / 2 : ℝ) ≤ (frame.toCanonical v) 0 ∧
        (frame.toCanonical v) 0 ≤ (1 / 2 : ℝ)
      rw [target_coordinate]
      exact residual_fst_mem_sharp_interval recipients.right_mem
  | paired side frame farthest branch rightSource right_source_eq
      source_coordinate middle middle_coordinate target_coordinate =>
      change -(3 / 2 : ℝ) ≤ (frame.toCanonical v) 0 ∧
        (frame.toCanonical v) 0 ≤ (1 / 2 : ℝ)
      rw [target_coordinate]
      exact residual_fst_mem_sharp_interval
        (branch.sourceRecipient_mem rightSource)

/-- Source-relative horizontal interval of the selected recipient in the
common directed-edge chart.  On the predecessor side the current emitter
is the terminal endpoint `u`; on the successor side it is the initial
endpoint `uPrev`. -/
lemma CommonPairedCase4Rows.current_secondary_displacement_bounds
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu) :
    (Q.twoExtreme.side = .previous ∧
        -(3 / 2 : ℝ) ≤
          (Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex) 0 -
            (Q.commonFrame.frame.toCanonical
              (sourceIndex P W u hu).1) 0 ∧
        (Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex) 0 -
            (Q.commonFrame.frame.toCanonical
              (sourceIndex P W u hu).1) 0 ≤ (1 / 2 : ℝ)) ∨
      (Q.twoExtreme.side = .next ∧
        -(1 / 2 : ℝ) ≤
          (Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex) 0 -
            (Q.commonFrame.frame.toCanonical
              (sourceIndex P W u hu).1) 0 ∧
        (Q.commonFrame.frame.toCanonical Q.currentSecondaryTarget.vertex) 0 -
            (Q.commonFrame.frame.toCanonical
              (sourceIndex P W u hu).1) 0 ≤ (3 / 2 : ℝ)) := by
  let b := ActualCase24Rows.case4SourceIsRight Q.twoExtreme
  let q := Q.pairBranch.branch.sourceRecipient b
  have hqMem : q ∈ Erdos957Case24Bridge.Case4.residualNeighbors
      (Q.commonFrame.frame.image A) :=
    Q.pairBranch.branch.sourceRecipient_mem b
  have hqBounds := residual_fst_mem_sharp_interval hqMem
  have htarget : Q.commonFrame.frame.toCanonical
      Q.currentSecondaryTarget.vertex = q := by
    rw [Q.current_secondary_vertex]
    simp [q, b, CommonCase4.CommonCase4HullPairBranch.actualRecipient]
  have hsource := Q.commonFrame.source_coordinate
  cases hside : Q.twoExtreme.side with
  | previous =>
      have hsource0 :
          (Q.commonFrame.frame.toCanonical
            (sourceIndex P W u hu).1) 0 = 0 := by
        rw [hsource]
        simp [ActualCase24Rows.case4SourceIsRight, hside,
          Erdos957Case24Bridge.Case4.sideSource,
          Erdos957Cases24.Case2.u]
      left
      refine ⟨rfl, ?_, ?_⟩
      · rw [htarget, hsource0]
        linarith [hqBounds.1]
      · rw [htarget, hsource0]
        linarith [hqBounds.2]
  | next =>
      have hsourceNegOne :
          (Q.commonFrame.frame.toCanonical
            (sourceIndex P W u hu).1) 0 = -1 := by
        rw [hsource]
        simp [ActualCase24Rows.case4SourceIsRight, hside,
          Erdos957Case24Bridge.Case4.sideSource,
          Erdos957Cases24.Case2.uPrev]
      right
      refine ⟨rfl, ?_, ?_⟩
      · rw [htarget, hsourceNegOne]
        linarith [hqBounds.1]
      · rw [htarget, hsourceNegOne]
        linarith [hqBounds.2]

/-- The selected split-right recipient is a genuine unit neighbour of the
retained equilateral middle. -/
lemma CommonPairedCase4Rows.middle_adj_currentSecondary
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu) :
    (unitDistanceGraph A).Adj Q.middle Q.currentSecondaryTarget.vertex := by
  rw [Q.current_secondary_vertex]
  change dist (Q.middle : Point)
    (Q.pairBranch.actualRecipient
      (ActualCase24Rows.case4SourceIsRight Q.twoExtreme) : Point) = 1
  let b := ActualCase24Rows.case4SourceIsRight Q.twoExtreme
  let q := Q.pairBranch.branch.sourceRecipient b
  have hq : dist Erdos957Cases24.Case2.v q = 1 := by
    simpa [Erdos957Cases24.Case4.v] using
      (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp
        (Q.pairBranch.branch.sourceRecipient_mem b)).2.1
  calc
    dist (Q.middle : Point) (Q.pairBranch.actualRecipient b : Point) =
        dist (Q.commonFrame.frame.toCanonical Q.middle)
          (Q.commonFrame.frame.toCanonical
            (Q.pairBranch.actualRecipient b)) :=
      (Q.commonFrame.frame.dist_eq _ _).symm
    _ = dist Erdos957Cases24.Case2.v q := by
      rw [show Q.commonFrame.frame.toCanonical Q.middle =
        Erdos957Cases24.Case2.v by
          simpa [ActualCase24Rows.TwoExtremeCommonPairFrame.frame] using
            Q.commonFrame.middle_coordinate]
      simp [q, b, CommonCase4.CommonCase4HullPairBranch.actualRecipient]
    _ = 1 := hq

/-- The selected recipient is a residual neighbour of the canonical middle
also in the source-normalized chart.  This formulation avoids transporting
the common-pair branch through the endpoint reflection. -/
lemma CommonPairedCase4Rows.normalized_currentSecondary_mem_residual
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu) :
    Q.normalized.frame.toCanonical Q.currentSecondaryTarget.vertex ∈
      Erdos957Case24Bridge.Case4.residualNeighbors
        (Q.normalized.frame.image A) := by
  apply Erdos957Case24Bridge.Case4.mem_residualNeighbors.mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr
      ⟨Q.currentSecondaryTarget.vertex,
        Q.currentSecondaryTarget.vertex.property, rfl⟩
  · have h :=
      Erdos957Case4SplitClassification.CommonPairedCase4Rows.middle_adj_currentSecondary Q
    change dist (Q.middle : Point)
      (Q.currentSecondaryTarget.vertex : Point) = 1 at h
    rw [← Q.normalized.frame.dist_eq] at h
    have hm : Q.normalized.frame.toCanonical Q.middle =
        Erdos957Cases24.Case2.v := by
      rw [← Q.normalized.middle_actual,
        Q.normalized.frame.toCanonical_actual]
    simpa [hm, Erdos957Cases24.Case4.v] using h
  · intro h
    have hactual : Q.currentSecondaryTarget.vertex =
        Q.normalized.frame.actual Erdos957Cases24.Case2.uPrev := by
      apply Q.normalized.frame.toCanonical.injective
      rw [Q.normalized.frame.toCanonical_actual]
      exact h
    rw [Q.normalized.side_actual] at hactual
    have hv : Q.currentSecondaryTarget.vertex =
        cyclicSideVertex P (sourceIndex P W u hu) Q.twoExtreme.side :=
      Subtype.ext hactual
    apply Q.currentSecondaryTarget.not_hull
    rw [hv]
    cases hside : Q.twoExtreme.side
    · simpa [cyclicSideVertex, hside] using
        (P.next⁻¹ (sourceIndex P W u hu)).property
    · simpa [cyclicSideVertex, hside] using
        (P.next (sourceIndex P W u hu)).property
  · intro h
    have hactual : Q.currentSecondaryTarget.vertex =
        Q.normalized.frame.actual Erdos957Cases24.Case2.u := by
      apply Q.normalized.frame.toCanonical.injective
      rw [Q.normalized.frame.toCanonical_actual]
      exact h
    rw [Q.normalized.source_actual] at hactual
    have hv : Q.currentSecondaryTarget.vertex =
        (sourceIndex P W u hu).1 := Subtype.ext hactual
    apply Q.currentSecondaryTarget.not_hull
    rw [hv]
    exact (sourceIndex P W u hu).property

/-- In the source-normalized chart, the endpoint-sensitive Case-4 label is
the incident cyclic side exactly on the closed nonpositive horizontal
half-plane. -/
lemma CommonPairedCase4Rows.current_secondary_association_eq_side_iff
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu) :
    (rows u hu).roleAssociation PairCases.TargetRoleName.case4SplitRight =
        cyclicSideAssociation Q.twoExtreme.side ↔
      (Q.normalized.frame.toCanonical
        Q.currentSecondaryTarget.vertex) 0 ≤ 0 := by
  rw [Q.current_secondary_association]
  cases hside : Q.twoExtreme.side with
  | previous =>
      have hb : ActualCase24Rows.case4SourceIsRight Q.twoExtreme = true := by
        simp [ActualCase24Rows.case4SourceIsRight, hside]
      have hcoord : Q.normalized.frame.toCanonical
          Q.currentSecondaryTarget.vertex =
          Q.pairBranch.branch.sourceRecipient true := by
        rw [Q.current_secondary_vertex]
        rw [hb]
        cases Q.normalized.frame_spec with
        | previous hs hunit hframe =>
            rw [hframe]
            simp [CommonCase4.CommonCase4HullPairBranch.actualRecipient,
              ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
              ActualCase24Rows.case4PairEdgeBase, hside]
        | next hs hunit hframe => simp [hside] at hs
      rw [hcoord]
      simp [hside, ActualCase24Rows.case4SourceIsRight,
        cyclicSideAssociation, commonPairHorizontalAssociation_right,
        horizontalAssociation, Erdos957Case24Bridge.Case4.sideSource,
        Erdos957Cases24.Case2.u, Erdos957Cases24.point]
  | next =>
      have hb : ActualCase24Rows.case4SourceIsRight Q.twoExtreme = false := by
        simp [ActualCase24Rows.case4SourceIsRight, hside]
      have hcoord :
          (Q.normalized.frame.toCanonical
            Q.currentSecondaryTarget.vertex) 0 =
          -(Q.pairBranch.branch.sourceRecipient false) 0 - 1 := by
        rw [Q.current_secondary_vertex]
        rw [hb]
        cases Q.normalized.frame_spec with
        | previous hs hunit hframe => simp [hside] at hs
        | next hs hunit hframe =>
            rw [hframe]
            simp [CommonCase4.CommonCase4HullPairBranch.actualRecipient,
              Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart,
              Equiv.trans_apply,
              Erdos957TwoExtremeAligned.swapEndpointEquiv_apply,
              ActualCase24Rows.TwoExtremeCommonPairFrame.frame,
              ActualCase24Rows.case4PairEdgeBase, hside]
      rw [hcoord]
      simp only [Fin.isValue, tsub_le_iff_right, zero_add]
      constructor <;> intro h <;> linarith

private lemma dist_gt_two_of_residual_nonpos_of_right_shallow
    {q p : Point}
    (hq : dist Erdos957Cases24.Case2.v q = 1)
    (hqLower : q 1 ≤ Erdos957Cases24.Case2.v 1)
    (hqx : q 0 ≤ 0)
    (hpx : (399 / 200 : ℝ) < p 0)
    (hpy : -p 1 ≤ p 0 / 10) :
    2 < dist p q := by
  have hqSq := congrArg (fun z : ℝ ↦ z ^ 2) hq
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hqSq
  simp only [Erdos957Cases24.Case2.v,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one, one_pow] at hqSq hqLower
  have hsqrt : (3 / 2 : ℝ) < Erdos957Cases24.sqrtThree := by
    nlinarith only [Erdos957Cases24.sqrtThree_pos,
      Erdos957Cases24.sqrtThree_sq]
  have hdistSq := Erdos957Cases24.dist_sq_eq_coordinates p q
  by_cases hpLarge : (5 / 2 : ℝ) ≤ p 0
  · have hx : 4 < (p 0 - q 0) ^ 2 := by
      nlinarith only [hpLarge, hqx, sq_nonneg (p 0 - q 0 - 2)]
    have hy : 0 ≤ (p 1 - q 1) ^ 2 := sq_nonneg _
    have hdNonneg := dist_nonneg (x := p) (y := q)
    nlinarith only [hdistSq, hx, hy, hdNonneg]
  · have hpUpper : p 0 < 5 / 2 := lt_of_not_ge hpLarge
    have hpyLower : -(1 / 4 : ℝ) < p 1 := by
      linarith only [hpy, hpUpper]
    have hqyUpper : q 1 < -(3 / 4 : ℝ) := by
      linarith only [hqLower, hsqrt]
    have hx : (399 / 200 : ℝ) < p 0 - q 0 := by
      linarith only [hpx, hqx]
    have hy : (1 / 2 : ℝ) < p 1 - q 1 := by
      linarith only [hpyLower, hqyUpper]
    have hxSq : (399 / 200 : ℝ) ^ 2 < (p 0 - q 0) ^ 2 := by
      nlinarith only [hx, sq_nonneg (p 0 - q 0 - 399 / 200)]
    have hySq : (1 / 2 : ℝ) ^ 2 < (p 1 - q 1) ^ 2 := by
      nlinarith only [hy, sq_nonneg (p 1 - q 1 - 1 / 2)]
    have hdNonneg := dist_nonneg (x := p) (y := q)
    norm_num at hxSq hySq
    nlinarith only [hdistSq, hxSq, hySq, hdNonneg]

private lemma dist_gt_two_of_residual_pos_of_left_shallow
    {q p : Point}
    (hq : dist Erdos957Cases24.Case2.v q = 1)
    (hqLower : q 1 ≤ Erdos957Cases24.Case2.v 1)
    (hqx : 0 < q 0)
    (hpx : (399 / 200 : ℝ) < -p 0)
    (hpy : -p 1 ≤ (-p 0) / 10) :
    2 < dist p q := by
  have hqSq := congrArg (fun z : ℝ ↦ z ^ 2) hq
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hqSq
  simp only [Erdos957Cases24.Case2.v,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one, one_pow] at hqSq hqLower
  have hsqrt : (3 / 2 : ℝ) < Erdos957Cases24.sqrtThree := by
    nlinarith only [Erdos957Cases24.sqrtThree_pos,
      Erdos957Cases24.sqrtThree_sq]
  have hdistSq := Erdos957Cases24.dist_sq_eq_coordinates p q
  by_cases hpLarge : (5 / 2 : ℝ) ≤ -p 0
  · have hx : 4 < (p 0 - q 0) ^ 2 := by
      nlinarith only [hpLarge, hqx, sq_nonneg (p 0 - q 0 + 2)]
    have hy : 0 ≤ (p 1 - q 1) ^ 2 := sq_nonneg _
    have hdNonneg := dist_nonneg (x := p) (y := q)
    nlinarith only [hdistSq, hx, hy, hdNonneg]
  · have hpUpper : -p 0 < 5 / 2 := lt_of_not_ge hpLarge
    have hpyLower : -(1 / 4 : ℝ) < p 1 := by
      linarith only [hpy, hpUpper]
    have hqyUpper : q 1 < -(3 / 4 : ℝ) := by
      linarith only [hqLower, hsqrt]
    have hx : (399 / 200 : ℝ) < q 0 - p 0 := by
      linarith only [hpx, hqx]
    have hy : (1 / 2 : ℝ) < p 1 - q 1 := by
      linarith only [hpyLower, hqyUpper]
    have hxSq : (399 / 200 : ℝ) ^ 2 < (p 0 - q 0) ^ 2 := by
      nlinarith only [hx, sq_nonneg (q 0 - p 0 - 399 / 200)]
    have hySq : (1 / 2 : ℝ) ^ 2 < (p 1 - q 1) ^ 2 := by
      nlinarith only [hy, sq_nonneg (p 1 - q 1 - 1 / 2)]
    have hdNonneg := dist_nonneg (x := p) (y := q)
    norm_num at hxSq hySq
    nlinarith only [hdistSq, hxSq, hySq, hdNonneg]

/-- A split recipient labelled toward the incident side cannot also lie
within two unit edges of the second source continuing away from its selected
hull edge. -/
lemma CommonPairedCase4Rows.not_within_two_away_second_of_association_eq_side
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (Q : CommonPairedCase4Rows rows u hu)
    (hi : P.IsFlat (sourceIndex P W u hu))
    (hassoc : (rows u hu).roleAssociation
      PairCases.TargetRoleName.case4SplitRight =
        cyclicSideAssociation Q.twoExtreme.side) :
    ¬ WithinTwoUnitEdges
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 1).1
      Q.currentSecondaryTarget.vertex := by
  intro hwithin
  let q := Q.normalized.frame.toCanonical Q.currentSecondaryTarget.vertex
  let p := Q.normalized.frame.toCanonical
    (Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W u hu) Q.twoExtreme.side 1).1
  have hqMem :=
    Erdos957Case4SplitClassification.CommonPairedCase4Rows.normalized_currentSecondary_mem_residual Q
  have huPrev : Erdos957Cases24.Case2.uPrev ∈
      Q.normalized.frame.image A := by
    apply Q.normalized.frame.mem_image_iff.mpr
    rw [Q.normalized.side_actual]
    exact (cyclicSideVertex P (sourceIndex P W u hu)
      Q.twoExtreme.side).property
  have huCanon : Erdos957Cases24.Case2.u ∈
      Q.normalized.frame.image A := by
    apply Q.normalized.frame.mem_image_iff.mpr
    rw [Q.normalized.source_actual]
    exact (sourceIndex P W u hu).1.property
  have hqLower : q 1 ≤ Erdos957Cases24.Case2.v 1 := by
    have h := residual_centered_snd_nonpos
      (Q.normalized.frame.image_oneSeparated hA) huPrev huCanon hqMem
    change q 1 - Erdos957Cases24.Case4.v 1 ≤ 0 at h
    simpa [Erdos957Cases24.Case4.v] using (sub_nonpos.mp h)
  have hqUnit : dist Erdos957Cases24.Case2.v q = 1 := by
    simpa [q, Erdos957Cases24.Case4.v, dist_comm] using
      (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqMem).2.1
  have hqx : q 0 ≤ 0 :=
    (Erdos957Case4SplitClassification.CommonPairedCase4Rows.current_secondary_association_eq_side_iff Q).mp
      hassoc
  have hpBounds := Erdos957Case4NoThree.normalizedFrame_away_prefix_bounds
    F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized hi 1
  have hpX : (399 / 200 : ℝ) < p 0 := by
    have hx := hpBounds.2.1
    norm_num at hx ⊢
    simpa [p] using hx
  have hpY : -p 1 ≤ p 0 / 10 := by
    simpa [p] using hpBounds.2.2
  have hdistCoord : dist p q ≤ 2 := by
    change dist
      (Q.normalized.frame.toCanonical
        (Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W u hu) Q.twoExtreme.side 1).1)
      (Q.normalized.frame.toCanonical
        Q.currentSecondaryTarget.vertex) ≤ 2
    rw [Q.normalized.frame.dist_eq]
    exact dist_le_two_of_withinTwoUnitEdges hwithin
  exact (not_lt_of_ge hdistCoord)
    (dist_gt_two_of_residual_nonpos_of_right_shallow
      hqUnit hqLower hqx hpX hpY)

/-- Dually, a split recipient labelled away from its selected edge cannot
lie within two unit edges of the second source through the incident
endpoint. -/
lemma CommonPairedCase4Rows.not_within_two_incident_second_of_association_ne_side
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (Q : CommonPairedCase4Rows rows u hu)
    (hi : P.IsFlat (sourceIndex P W u hu))
    (hassoc : (rows u hu).roleAssociation
      PairCases.TargetRoleName.case4SplitRight ≠
        cyclicSideAssociation Q.twoExtreme.side) :
    ¬ WithinTwoUnitEdges
      (Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 1).1
      Q.currentSecondaryTarget.vertex := by
  intro hwithin
  let q := Q.normalized.frame.toCanonical Q.currentSecondaryTarget.vertex
  let p := Q.normalized.frame.toCanonical
    (Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W u hu) Q.twoExtreme.side 1).1
  have hqMem :=
    Erdos957Case4SplitClassification.CommonPairedCase4Rows.normalized_currentSecondary_mem_residual Q
  have huPrev : Erdos957Cases24.Case2.uPrev ∈
      Q.normalized.frame.image A := by
    apply Q.normalized.frame.mem_image_iff.mpr
    rw [Q.normalized.side_actual]
    exact (cyclicSideVertex P (sourceIndex P W u hu)
      Q.twoExtreme.side).property
  have huCanon : Erdos957Cases24.Case2.u ∈
      Q.normalized.frame.image A := by
    apply Q.normalized.frame.mem_image_iff.mpr
    rw [Q.normalized.source_actual]
    exact (sourceIndex P W u hu).1.property
  have hqLower : q 1 ≤ Erdos957Cases24.Case2.v 1 := by
    have h := residual_centered_snd_nonpos
      (Q.normalized.frame.image_oneSeparated hA) huPrev huCanon hqMem
    change q 1 - Erdos957Cases24.Case4.v 1 ≤ 0 at h
    simpa [Erdos957Cases24.Case4.v] using (sub_nonpos.mp h)
  have hqUnit : dist Erdos957Cases24.Case2.v q = 1 := by
    simpa [q, Erdos957Cases24.Case4.v, dist_comm] using
      (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqMem).2.1
  have hqx : 0 < q 0 := by
    by_contra hnot
    apply hassoc
    apply (Erdos957Case4SplitClassification.CommonPairedCase4Rows.current_secondary_association_eq_side_iff Q).mpr
    exact le_of_not_gt hnot
  have hpBounds :=
    Erdos957Case4NoThree.normalizedFrame_incident_prefix_metric_bounds
      F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized hi 1
  have hpX : (399 / 200 : ℝ) < -p 0 := by
    have hx := hpBounds.1
    norm_num at hx ⊢
    simpa [p] using hx
  have hpY : -p 1 ≤ (-p 0) / 10 := by
    simpa [p] using hpBounds.2
  have hdistCoord : dist p q ≤ 2 := by
    change dist
      (Q.normalized.frame.toCanonical
        (Erdos957Case4NoThree.incidentHullVertex P
          (sourceIndex P W u hu) Q.twoExtreme.side 1).1)
      (Q.normalized.frame.toCanonical
        Q.currentSecondaryTarget.vertex) ≤ 2
    rw [Q.normalized.frame.dist_eq]
    exact dist_le_two_of_withinTwoUnitEdges hwithin
  exact (not_lt_of_ge hdistCoord)
    (dist_gt_two_of_residual_pos_of_left_shallow
      hqUnit hqLower hqx hpX hpY)

/-- The same signed residual estimate excludes the third source through the
incident endpoint.  This is kept separate from the distance-two statement so
the realized-row window dispatch can use the exact orbit index directly. -/
lemma CommonPairedCase4Rows.not_within_two_incident_third_of_association_ne_side
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (hA : IsOneSeparated A) (F : P.FlatAlignedFrameData)
    (Q : CommonPairedCase4Rows rows u hu)
    (hi : P.IsFlat (sourceIndex P W u hu))
    (hassoc : (rows u hu).roleAssociation
      PairCases.TargetRoleName.case4SplitRight ≠
        cyclicSideAssociation Q.twoExtreme.side) :
    ¬ WithinTwoUnitEdges
      (Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W u hu) Q.twoExtreme.side 2).1
      Q.currentSecondaryTarget.vertex := by
  intro hwithin
  let q := Q.normalized.frame.toCanonical Q.currentSecondaryTarget.vertex
  let p := Q.normalized.frame.toCanonical
    (Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W u hu) Q.twoExtreme.side 2).1
  have hqMem :=
    Erdos957Case4SplitClassification.CommonPairedCase4Rows.normalized_currentSecondary_mem_residual Q
  have huPrev : Erdos957Cases24.Case2.uPrev ∈
      Q.normalized.frame.image A := by
    apply Q.normalized.frame.mem_image_iff.mpr
    rw [Q.normalized.side_actual]
    exact (cyclicSideVertex P (sourceIndex P W u hu)
      Q.twoExtreme.side).property
  have huCanon : Erdos957Cases24.Case2.u ∈
      Q.normalized.frame.image A := by
    apply Q.normalized.frame.mem_image_iff.mpr
    rw [Q.normalized.source_actual]
    exact (sourceIndex P W u hu).1.property
  have hqLower : q 1 ≤ Erdos957Cases24.Case2.v 1 := by
    have h := residual_centered_snd_nonpos
      (Q.normalized.frame.image_oneSeparated hA) huPrev huCanon hqMem
    change q 1 - Erdos957Cases24.Case4.v 1 ≤ 0 at h
    simpa [Erdos957Cases24.Case4.v] using (sub_nonpos.mp h)
  have hqUnit : dist Erdos957Cases24.Case2.v q = 1 := by
    simpa [q, Erdos957Cases24.Case4.v, dist_comm] using
      (Erdos957Case24Bridge.Case4.mem_residualNeighbors.mp hqMem).2.1
  have hqx : 0 < q 0 := by
    by_contra hnot
    apply hassoc
    apply (Erdos957Case4SplitClassification.CommonPairedCase4Rows.current_secondary_association_eq_side_iff Q).mpr
    exact le_of_not_gt hnot
  have hpBounds :=
    Erdos957Case4NoThree.normalizedFrame_incident_prefix_metric_bounds
      F (sourceIndex P W u hu) Q.middle Q.twoExtreme Q.normalized hi 2
  have hpX : (399 / 200 : ℝ) < -p 0 := by
    have hx := hpBounds.1
    norm_num at hx ⊢
    nlinarith only [hx]
  have hpY : -p 1 ≤ (-p 0) / 10 := by
    simpa [p] using hpBounds.2
  have hdistCoord : dist p q ≤ 2 := by
    change dist
      (Q.normalized.frame.toCanonical
        (Erdos957Case4NoThree.incidentHullVertex P
          (sourceIndex P W u hu) Q.twoExtreme.side 2).1)
      (Q.normalized.frame.toCanonical
        Q.currentSecondaryTarget.vertex) ≤ 2
    rw [Q.normalized.frame.dist_eq]
    exact dist_le_two_of_withinTwoUnitEdges hwithin
  exact (not_lt_of_ge hdistCoord)
    (dist_gt_two_of_residual_pos_of_left_shallow
      hqUnit hqLower hqx hpX hpY)

/-- The retained Case-4 middle is a genuine unit neighbour of its source. -/
lemma CommonPairedCase4Rows.source_adj_middle
    {C : P.AlignedChartData}
    {rows : HasRealizedSourceRows P W C}
    {u : Vertex A} {hu : u ∈ sourceVertices P W}
    (Q : CommonPairedCase4Rows rows u hu) :
    (unitDistanceGraph A).Adj (sourceIndex P W u hu).1 Q.middle := by
  change dist ((sourceIndex P W u hu).1 : Point) (Q.middle : Point) = 1
  rw [← Q.normalized.source_actual, ← Q.normalized.middle_actual,
    Q.normalized.frame.dist_actual]
  exact Erdos957Cases24.Case2.dist_u_v

/-- A unit edge controls the first-coordinate displacement in every rigid
chart. -/
private lemma abs_fst_sub_le_one_of_adj
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    {a b : Vertex A} (hab : (unitDistanceGraph A).Adj a b) :
    |(E.toCanonical a) 0 - (E.toCanonical b) 0| ≤ 1 := by
  have hdist : dist (E.toCanonical a) (E.toCanonical b) = 1 := by
    rw [E.dist_eq]
    exact hab
  have hs := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical a) (E.toCanonical b)
  rw [hdist] at hs
  have hy : 0 ≤ ((E.toCanonical a) 1 - (E.toCanonical b) 1) ^ 2 :=
    sq_nonneg _
  have hx : ((E.toCanonical a) 0 - (E.toCanonical b) 0) ^ 2 ≤ 1 := by
    nlinarith only [hs, hy]
  rw [abs_le]
  constructor <;> nlinarith only [hx,
    sq_nonneg ((E.toCanonical a) 0 - (E.toCanonical b) 0 - 1),
    sq_nonneg ((E.toCanonical a) 0 - (E.toCanonical b) 0 + 1)]

/-- A common unit neighbour of the endpoints of an almost-horizontal
second hull edge lies strictly to the right of the anchor's vertical line.
The deliberately weak conclusion is all that is needed to determine the
recipient-relative Case-4 association. -/
private lemma common_unit_neighbor_fst_gt_one_of_flat_second_edge
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    {a b m : Vertex A}
    (ha : (399 / 400 : ℝ) < (E.toCanonical a) 0)
    (habx : (399 / 400 : ℝ) <
      (E.toCanonical b) 0 - (E.toCanonical a) 0)
    (hab : (unitDistanceGraph A).Adj a b)
    (ham : (unitDistanceGraph A).Adj a m)
    (hbm : (unitDistanceGraph A).Adj b m) :
    1 < (E.toCanonical m) 0 := by
  let dx := (E.toCanonical b) 0 - (E.toCanonical a) 0
  let dy := (E.toCanonical b) 1 - (E.toCanonical a) 1
  let ex := (E.toCanonical m) 0 - (E.toCanonical a) 0
  let ey := (E.toCanonical m) 1 - (E.toCanonical a) 1
  have habDist : dist (E.toCanonical a) (E.toCanonical b) = 1 := by
    rw [E.dist_eq]
    exact hab
  have hamDist : dist (E.toCanonical a) (E.toCanonical m) = 1 := by
    rw [E.dist_eq]
    exact ham
  have hbmDist : dist (E.toCanonical b) (E.toCanonical m) = 1 := by
    rw [E.dist_eq]
    exact hbm
  have habSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical a) (E.toCanonical b)
  have hamSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical a) (E.toCanonical m)
  have hbmSq := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical b) (E.toCanonical m)
  rw [habDist] at habSq
  rw [hamDist] at hamSq
  rw [hbmDist] at hbmSq
  norm_num at habSq hamSq hbmSq
  have hedge : dx ^ 2 + dy ^ 2 = 1 := by
    dsimp [dx, dy]
    nlinarith only [habSq]
  have hmiddle : ex ^ 2 + ey ^ 2 = 1 := by
    dsimp [ex, ey]
    nlinarith only [hamSq]
  have hother : (ex - dx) ^ 2 + (ey - dy) ^ 2 = 1 := by
    dsimp [dx, dy, ex, ey]
    nlinarith only [hbmSq]
  have hdot : dx * ex + dy * ey = 1 / 2 := by
    nlinarith only [hedge, hmiddle, hother]
  have hdx : (399 / 400 : ℝ) < dx := by
    simpa only [dx] using habx
  have hdxpos : 0 < dx := by
    norm_num at hdx ⊢
    linarith only [hdx]
  have hdxSq : (399 / 400 : ℝ) ^ 2 < dx ^ 2 :=
    (sq_lt_sq₀ (by norm_num) hdxpos.le).2 hdx
  have hdySq : dy ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    norm_num at hdxSq ⊢
    nlinarith only [hedge, hdxSq]
  have heySq : ey ^ 2 ≤ 1 := by
    nlinarith only [hmiddle, sq_nonneg ex]
  have hprodSq : (dy * ey) ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    calc
      (dy * ey) ^ 2 = dy ^ 2 * ey ^ 2 := by ring
      _ ≤ dy ^ 2 := by
        simpa only [mul_comm] using
          (mul_le_of_le_one_left (sq_nonneg dy) heySq)
      _ < (1 / 10 : ℝ) ^ 2 := hdySq
  have hprodAbsSq : |dy * ey| ^ 2 < (1 / 10 : ℝ) ^ 2 := by
    simpa only [sq_abs] using hprodSq
  have hprodAbs : |dy * ey| < (1 / 10 : ℝ) :=
    (sq_lt_sq₀ (abs_nonneg _) (by norm_num)).1 hprodAbsSq
  have hprodUpper : dy * ey < (1 / 10 : ℝ) := (abs_lt.mp hprodAbs).2
  have hdex : (2 / 5 : ℝ) < dx * ex := by
    nlinarith only [hdot, hprodUpper]
  have hdxSqLe : dx ^ 2 ≤ (1 : ℝ) ^ 2 := by
    nlinarith only [hedge, sq_nonneg dy]
  have hdxLe : dx ≤ 1 :=
    (sq_le_sq₀ hdxpos.le (by norm_num)).1 hdxSqLe
  have hdexPos : 0 < dx * ex := by
    norm_num at hdex ⊢
    linarith only [hdex]
  have hexpos : 0 < ex := by
    rcases mul_pos_iff.mp hdexPos with h | h
    · exact h.2
    · exact (not_lt_of_ge hdxpos.le h.1).elim
  have hdexLe : dx * ex ≤ ex := by
    simpa only [mul_comm] using
      (mul_le_of_le_one_left hexpos.le hdxLe)
  dsimp [ex] at hexpos hdexLe ⊢
  linarith only [ha, hdex, hdexLe]

/-- The two same-side Case-4 middles based two cyclic steps on opposite
sides of an anchor are more than two horizontal units apart in the
anchor's normalized chart.  The incident middle is controlled by its
farther cyclic endpoint, while the away middle is controlled by its own
source. -/
lemma opposite_distance_two_middle_fst_gap_gt_two
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (huRole : U.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htAssoc : T.descriptor.association = S.descriptor.association)
    (huAssoc : U.descriptor.association = S.descriptor.association)
    (hsEnum : S.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side)
    (htEnum : T.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair t.1 t.property
          ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩).twoExtreme.side)
    (huEnum : U.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair u.1 u.property
          ⟨U.target.target, by simpa [huRole] using U.target.target_at_role⟩).twoExtreme.side)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 1)
    (huIndex : sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 1) :
    2 < |((Q.case4_pair s.1 s.property
        ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).normalized.frame.toCanonical
          (Q.case4_pair t.1 t.property
            ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩).middle) 0 -
      ((Q.case4_pair s.1 s.property
        ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).normalized.frame.toCanonical
          (Q.case4_pair u.1 u.property
            ⟨U.target.target, by simpa [huRole] using U.target.target_at_role⟩).middle) 0| := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  let Qu := Q.case4_pair u.1 u.property
    ⟨U.target.target, by simpa [huRole] using U.target.target_at_role⟩
  have htSide : Qt.twoExtreme.side = Qs.twoExtreme.side := by
    apply cyclicSideAssociation_injective
    rw [← htEnum, ← hsEnum]
    exact htAssoc
  have huSide : Qu.twoExtreme.side = Qs.twoExtreme.side := by
    apply cyclicSideAssociation_injective
    rw [← huEnum, ← hsEnum]
    exact huAssoc
  have htEndpoint : cyclicSideVertex P
      (sourceIndex P W t.1 t.property) Qt.twoExtreme.side =
      Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 := by
    calc
      cyclicSideVertex P (sourceIndex P W t.1 t.property)
          Qt.twoExtreme.side =
          cyclicSideVertex P (sourceIndex P W t.1 t.property)
            Qs.twoExtreme.side := congrArg _ htSide
      _ = Erdos957Case4NoThree.incidentHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 := by
        rw [htIndex]
        cases hside : Qs.twoExtreme.side <;>
          simp [cyclicSideVertex, Erdos957Case4NoThree.incidentHullVertex,
            hside, pow_succ]
  have htUnit : (unitDistanceGraph A).Adj Qt.middle
      (Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2).1 := by
    rw [← htEndpoint]
    exact Qt.twoExtreme.side_adjacent
  have huUnit : (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1 Qu.middle := by
    rw [← huIndex]
    exact CommonPairedCase4Rows.source_adj_middle Qu
  have htFst := abs_fst_sub_le_one_of_adj Qs.normalized.frame htUnit
  have huFst := abs_fst_sub_le_one_of_adj Qs.normalized.frame huUnit
  have hincident :=
    Erdos957Case4NoThree.normalizedFrame_incident_third_fst_lt_neg_five_halves
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized (source_isFlat P W _ s.property)
  have haway :=
    Erdos957Case4NoThree.normalizedFrame_away_second_fst_gt_three_halves
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized (source_isFlat P W _ s.property)
  change 2 < |(Qs.normalized.frame.toCanonical Qt.middle) 0 -
    (Qs.normalized.frame.toCanonical Qu.middle) 0|
  rw [abs_of_neg]
  · rcases (abs_le.mp htFst) with ⟨htLower, htUpper⟩
    rcases (abs_le.mp huFst) with ⟨huLower, huUpper⟩
    linarith
  · rcases (abs_le.mp htFst) with ⟨htLower, htUpper⟩
    rcases (abs_le.mp huFst) with ⟨huLower, huUpper⟩
    linarith

/-- If the incident endpoint of a selected split Case-4 edge is also an
emitter and its split-right target is the current endpoint's split-right
target, the shared source-free branch is necessarily the low branch.

This does not assert that every coincident split-right emitter is the
incident endpoint: an emitter on the next adjacent edge can share the low
recipient, and that alternative belongs in the full cross-edge
classification. -/
theorem eq_low_of_incident_partner_split_right_collision
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (Ds : RealizedPositiveTarget (Q.rows s.1 s.property) v)
    (Dt : RealizedPositiveTarget (Q.rows t.1 t.property) v)
    (hsRole : Ds.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : Dt.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨Ds.target, by simpa [hsRole] using Ds.target_at_role⟩).twoExtreme.side 0) :
    ∃ hdegree,
      (Q.case4_pair s.1 s.property
        ⟨Ds.target, by simpa [hsRole] using Ds.target_at_role⟩).pairBranch.branch =
          Erdos957Case24Bridge.Case4.FarthestBranchData.low hdegree := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨Ds.target, by simpa [hsRole] using Ds.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at htIndex
  have htPartner : t.1 = cyclicSideVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side := by
    have h := congrArg Subtype.val htIndex
    cases hside : Qs.twoExtreme.side <;>
      simpa [sourceIndex, Erdos957Case4NoThree.incidentHullVertex,
        cyclicSideVertex, hside] using h
  have hp : cyclicSideVertex P (sourceIndex P W s.1 s.property)
      Qs.twoExtreme.side ∈ sourceVertices P W := by
    rw [← htPartner]
    exact t.property
  have htSource : t =
      ⟨cyclicSideVertex P (sourceIndex P W s.1 s.property)
        Qs.twoExtreme.side, hp⟩ := by
    apply Subtype.ext
    exact htPartner
  subst t
  rcases Qs.partner_absent_or_coherent with habsent | hcoherent
  · exact (habsent hp).elim
  obtain ⟨partnerMiddleTarget, partnerSecondaryTarget,
      _hpartnerMiddleRole, hpartnerSecondaryRole,
      _hpartnerMiddleVertex, hpartnerSecondaryVertex,
      _hpartnerSecondaryAssociation⟩ := hcoherent hp
  have hsTarget : Ds.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← Ds.target_at_role, hsRole, Qs.current_secondary_role]
  have htTarget : Dt.target = partnerSecondaryTarget := by
    apply Option.some.inj
    rw [← Dt.target_at_role, htRole, hpartnerSecondaryRole]
  have hactual : Qs.pairBranch.actualRecipient
        (ActualCase24Rows.case4SourceIsRight Qs.twoExtreme) =
      Qs.pairBranch.actualRecipient
        (!(ActualCase24Rows.case4SourceIsRight Qs.twoExtreme)) := by
    calc
      Qs.pairBranch.actualRecipient
          (ActualCase24Rows.case4SourceIsRight Qs.twoExtreme) =
          Qs.currentSecondaryTarget.vertex := Qs.current_secondary_vertex.symm
      _ = Ds.target.vertex := congrArg LocalTarget.vertex hsTarget.symm
      _ = v := Ds.vertex_eq.symm
      _ = Dt.target.vertex := Dt.vertex_eq
      _ = partnerSecondaryTarget.vertex := congrArg LocalTarget.vertex htTarget
      _ = Qs.pairBranch.actualRecipient
          (!(ActualCase24Rows.case4SourceIsRight Qs.twoExtreme)) :=
        hpartnerSecondaryVertex
  exact Qs.pairBranch.eq_low_of_actualRecipients_eq _ hactual

/-- Split-right arrivals from the two endpoints of one coherent Case-4
edge have opposite formula-derived associations.  This is independent of
whether their actual recipients coincide; coincidence additionally forces
the low branch by
`eq_low_of_incident_partner_split_right_collision`. -/
theorem incident_partner_split_right_associations_ne
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 0) :
    S.descriptor.association ≠ T.descriptor.association := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at htIndex
  have htPartner : t.1 = cyclicSideVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side := by
    have h := congrArg Subtype.val htIndex
    cases hside : Qs.twoExtreme.side <;>
      simpa [sourceIndex, Erdos957Case4NoThree.incidentHullVertex,
        cyclicSideVertex, hside] using h
  have hp : cyclicSideVertex P (sourceIndex P W s.1 s.property)
      Qs.twoExtreme.side ∈ sourceVertices P W := by
    rw [← htPartner]
    exact t.property
  have htSource : t =
      ⟨cyclicSideVertex P (sourceIndex P W s.1 s.property)
        Qs.twoExtreme.side, hp⟩ := by
    apply Subtype.ext
    exact htPartner
  have hlow := eq_low_of_incident_partner_split_right_collision
    Q S.target T.target hsRole htRole htIndex
  obtain ⟨hlowDegree, hbranch⟩ := hlow
  subst t
  rcases Qs.partner_absent_or_coherent with habsent | hcoherent
  · exact (habsent hp).elim
  obtain ⟨_partnerMiddleTarget, _partnerSecondaryTarget,
      _hpartnerMiddleRole, _hpartnerSecondaryRole,
      _hpartnerMiddleVertex, _hpartnerSecondaryVertex,
      hpartnerSecondaryAssociation⟩ := hcoherent hp
  have hsAssociation : S.descriptor.association =
      commonPairHorizontalAssociation Qs.pairBranch.branch
        (ActualCase24Rows.case4SourceIsRight Qs.twoExtreme) := by
    calc
      S.descriptor.association =
          (Q.rows s.1 s.property).roleAssociation S.target.role :=
        S.descriptor.association_eq
      _ = (Q.rows s.1 s.property).roleAssociation
          PairCases.TargetRoleName.case4SplitRight := by rw [hsRole]
      _ = _ := Qs.current_secondary_association
  have htAssociation : T.descriptor.association =
      commonPairHorizontalAssociation Qs.pairBranch.branch
        (!(ActualCase24Rows.case4SourceIsRight Qs.twoExtreme)) := by
    calc
      T.descriptor.association =
          (Q.rows _ hp).roleAssociation T.target.role :=
        T.descriptor.association_eq
      _ = (Q.rows _ hp).roleAssociation
          PairCases.TargetRoleName.case4SplitRight := by rw [htRole]
      _ = _ := hpartnerSecondaryAssociation
  rw [hsAssociation, htAssociation]
  exact CommonPairedCase4Rows.low_branch_endpoint_associations_ne
    hA Qs hlowDegree hbranch

/-- If a second split-right arrival comes from the second hull source away
from the selected edge, the anchor recipient points to the opposite cyclic
side. -/
theorem split_right_association_eq_opposite_at_away_second
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (_htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 1) :
    S.descriptor.association =
      oppositeCyclicSideAssociation
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 at htIndex
  have htValue : t.1 =
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1 := by
    simpa [sourceIndex] using congrArg Subtype.val htIndex
  have hsTarget : S.target.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← S.target.target_at_role, hsRole, Qs.current_secondary_role]
  have htVertex : T.target.target.vertex =
      Qs.currentSecondaryTarget.vertex := by
    calc
      T.target.target.vertex = v := T.target.vertex_eq.symm
      _ = S.target.target.vertex := S.target.vertex_eq
      _ = Qs.currentSecondaryTarget.vertex :=
        congrArg LocalTarget.vertex hsTarget
  have hwithin : WithinTwoUnitEdges
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1
      Qs.currentSecondaryTarget.vertex := by
    rw [← htValue, ← htVertex]
    exact T.target.target.within_two
  have hrowNe : (Q.rows s.1 s.property).roleAssociation
      PairCases.TargetRoleName.case4SplitRight ≠
        cyclicSideAssociation Qs.twoExtreme.side := by
    intro hrow
    exact (CommonPairedCase4Rows.not_within_two_away_second_of_association_eq_side
      hA F Qs (source_isFlat P W _ s.property) hrow) hwithin
  have hrowOpp : (Q.rows s.1 s.property).roleAssociation
      PairCases.TargetRoleName.case4SplitRight =
        oppositeCyclicSideAssociation Qs.twoExtreme.side := by
    cases hside : Qs.twoExtreme.side <;>
      cases ha : (Q.rows s.1 s.property).roleAssociation
        PairCases.TargetRoleName.case4SplitRight <;>
      simp [hside, ha, cyclicSideAssociation,
        oppositeCyclicSideAssociation] at hrowNe ⊢
  calc
    S.descriptor.association =
        (Q.rows s.1 s.property).roleAssociation S.target.role :=
      S.descriptor.association_eq
    _ = (Q.rows s.1 s.property).roleAssociation
        PairCases.TargetRoleName.case4SplitRight := by rw [hsRole]
    _ = _ := hrowOpp

/-- If the competing split-right source is two hull steps through the
incident endpoint, the anchor recipient has the incident cyclic label. -/
theorem split_right_association_eq_side_at_incident_second
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (_htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 1) :
    S.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 at htIndex
  have htValue : t.1 =
      (Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1 := by
    simpa [sourceIndex] using congrArg Subtype.val htIndex
  have hsTarget : S.target.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← S.target.target_at_role, hsRole, Qs.current_secondary_role]
  have htVertex : T.target.target.vertex =
      Qs.currentSecondaryTarget.vertex := by
    calc
      T.target.target.vertex = v := T.target.vertex_eq.symm
      _ = S.target.target.vertex := S.target.vertex_eq
      _ = Qs.currentSecondaryTarget.vertex :=
        congrArg LocalTarget.vertex hsTarget
  have hwithin : WithinTwoUnitEdges
      (Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1
      Qs.currentSecondaryTarget.vertex := by
    rw [← htValue, ← htVertex]
    exact T.target.target.within_two
  have hrow : (Q.rows s.1 s.property).roleAssociation
      PairCases.TargetRoleName.case4SplitRight =
        cyclicSideAssociation Qs.twoExtreme.side := by
    by_contra hne
    exact (CommonPairedCase4Rows.not_within_two_incident_second_of_association_ne_side
      hA F Qs (source_isFlat P W _ s.property) hne) hwithin
  calc
    S.descriptor.association =
        (Q.rows s.1 s.property).roleAssociation S.target.role :=
      S.descriptor.association_eq
    _ = (Q.rows s.1 s.property).roleAssociation
        PairCases.TargetRoleName.case4SplitRight := by rw [hsRole]
    _ = _ := hrow

/-- If the competing split-right source is three hull steps through the
incident endpoint, the anchor recipient still has the incident cyclic label.
This is the signed counterpart to the side-free three-step gap on the away
prefix. -/
theorem split_right_association_eq_side_at_incident_third
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (_htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 2) :
    S.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 at htIndex
  have htValue : t.1 =
      (Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2).1 := by
    simpa [sourceIndex] using congrArg Subtype.val htIndex
  have hsTarget : S.target.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← S.target.target_at_role, hsRole, Qs.current_secondary_role]
  have htVertex : T.target.target.vertex =
      Qs.currentSecondaryTarget.vertex := by
    calc
      T.target.target.vertex = v := T.target.vertex_eq.symm
      _ = S.target.target.vertex := S.target.vertex_eq
      _ = Qs.currentSecondaryTarget.vertex :=
        congrArg LocalTarget.vertex hsTarget
  have hwithin : WithinTwoUnitEdges
      (Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2).1
      Qs.currentSecondaryTarget.vertex := by
    rw [← htValue, ← htVertex]
    exact T.target.target.within_two
  have hrow : (Q.rows s.1 s.property).roleAssociation
      PairCases.TargetRoleName.case4SplitRight =
        cyclicSideAssociation Qs.twoExtreme.side := by
    by_contra hne
    exact (CommonPairedCase4Rows.not_within_two_incident_third_of_association_ne_side
      hA F Qs (source_isFlat P W _ s.property) hne) hwithin
  calc
    S.descriptor.association =
        (Q.rows s.1 s.property).roleAssociation S.target.role :=
      S.descriptor.association_eq
    _ = (Q.rows s.1 s.property).roleAssociation
        PairCases.TargetRoleName.case4SplitRight := by rw [hsRole]
    _ = _ := hrow

/-- If the competing split-right source is the first source on the away
prefix and its selected edge points farther away from the anchor, the
anchor recipient has the opposite cyclic association.  The competitor's
middle is a common unit neighbour of the two consecutive away hull-edge
endpoints, so the flat per-edge estimates put it past `x=1`; a common
unit recipient must therefore have positive anchor-frame `x`. -/
theorem split_right_association_eq_opposite_at_outward_adjacent
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 0)
    (hsidesNe :
      (Q.case4_pair t.1 t.property
        ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩).twoExtreme.side ≠
      (Q.case4_pair s.1 s.property
        ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side) :
    S.descriptor.association =
      oppositeCyclicSideAssociation
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at htIndex
  change Qt.twoExtreme.side ≠ Qs.twoExtreme.side at hsidesNe
  have htEndpoint : cyclicSideVertex P
      (sourceIndex P W t.1 t.property) Qt.twoExtreme.side =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 := by
    apply Subtype.ext
    have htValue := congrArg Subtype.val htIndex
    cases hsSide : Qs.twoExtreme.side <;>
      cases htSide : Qt.twoExtreme.side <;>
      simp_all [Erdos957Case4NoThree.awayHullVertex,
        cyclicSideVertex, pow_succ]
  have ha :=
    (Erdos957Case4NoThree.normalizedFrame_away_prefix_bounds
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized (source_isFlat P W _ s.property) 0).2.1
  have habx :=
    Erdos957Case4NoThree.normalizedFrame_away_second_edge_fst_increment_gt
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized (source_isFlat P W _ s.property)
  have hab : (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0).1
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1 := by
    change dist
      ((Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0).1 : Point)
      ((Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1 : Point) = 1
    rw [← htIndex, ← htEndpoint]
    exact Qt.normalized.side_unit
  have ham : (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0).1 Qt.middle := by
    rw [← htIndex]
    exact CommonPairedCase4Rows.source_adj_middle Qt
  have hbm : (unitDistanceGraph A).Adj
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1 Qt.middle := by
    rw [← htEndpoint]
    exact Qt.twoExtreme.side_adjacent.symm
  have hmX : 1 < (Qs.normalized.frame.toCanonical Qt.middle) 0 := by
    apply common_unit_neighbor_fst_gt_one_of_flat_second_edge
      Qs.normalized.frame
      (a := (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0).1)
      (b := (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1)
      (m := Qt.middle)
    · norm_num at ha ⊢
      exact ha
    · exact habx
    · exact hab
    · exact ham
    · exact hbm
  have hsTarget : S.target.target = Qs.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← S.target.target_at_role, hsRole, Qs.current_secondary_role]
  have htTarget : T.target.target = Qt.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← T.target.target_at_role, htRole, Qt.current_secondary_role]
  have hsVertex : Qs.currentSecondaryTarget.vertex = v := by
    calc
      Qs.currentSecondaryTarget.vertex = S.target.target.vertex :=
        congrArg LocalTarget.vertex hsTarget.symm
      _ = v := S.target.vertex_eq.symm
  have htVertex : Qt.currentSecondaryTarget.vertex = v := by
    calc
      Qt.currentSecondaryTarget.vertex = T.target.target.vertex :=
        congrArg LocalTarget.vertex htTarget.symm
      _ = v := T.target.vertex_eq.symm
  have hmq : (unitDistanceGraph A).Adj Qt.middle
      Qs.currentSecondaryTarget.vertex := by
    rw [hsVertex, ← htVertex]
    exact CommonPairedCase4Rows.middle_adj_currentSecondary Qt
  have hmqX := abs_fst_sub_le_one_of_adj Qs.normalized.frame hmq
  have hqX : 0 <
      (Qs.normalized.frame.toCanonical Qs.currentSecondaryTarget.vertex) 0 := by
    rcases abs_le.mp hmqX with ⟨hlower, hupper⟩
    linarith only [hmX, hupper]
  have hrowNe : (Q.rows s.1 s.property).roleAssociation
      PairCases.TargetRoleName.case4SplitRight ≠
        cyclicSideAssociation Qs.twoExtreme.side := by
    intro hrow
    have hnonpos :=
      (CommonPairedCase4Rows.current_secondary_association_eq_side_iff Qs).mp hrow
    linarith only [hqX, hnonpos]
  have hrowOpp : (Q.rows s.1 s.property).roleAssociation
      PairCases.TargetRoleName.case4SplitRight =
        oppositeCyclicSideAssociation Qs.twoExtreme.side := by
    cases hsSide : Qs.twoExtreme.side <;>
      cases ha : (Q.rows s.1 s.property).roleAssociation
        PairCases.TargetRoleName.case4SplitRight <;>
      simp [hsSide, ha, cyclicSideAssociation,
        oppositeCyclicSideAssociation] at hrowNe ⊢
  calc
    S.descriptor.association =
        (Q.rows s.1 s.property).roleAssociation S.target.role :=
      S.descriptor.association_eq
    _ = (Q.rows s.1 s.property).roleAssociation
        PairCases.TargetRoleName.case4SplitRight := by rw [hsRole]
    _ = _ := hrowOpp

/-- Two split-right arrivals whose sources are two hull steps apart through
the anchor's incident endpoint have opposite formula-derived associations.
The reverse source is either on the second incident prefix or the second away
prefix of its own selected edge; the signed residual estimates cover both
possibilities. -/
theorem split_right_associations_ne_at_incident_second
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 1) :
    S.descriptor.association ≠ T.descriptor.association := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 at htIndex
  have hsAssoc := split_right_association_eq_side_at_incident_second
    hA Q S T hsRole htRole htIndex
  change S.descriptor.association =
    cyclicSideAssociation Qs.twoExtreme.side at hsAssoc
  cases hsSide : Qs.twoExtreme.side with
  | previous =>
      have htReverse : sourceIndex P W s.1 s.property =
          (P.next ^ 2) (sourceIndex P W t.1 t.property) := by
        have hh := congrArg (fun x ↦ (P.next ^ 2) x) htIndex
        simpa [Erdos957Case4NoThree.incidentHullVertex, hsSide] using hh.symm
      cases htSide : Qt.twoExtreme.side with
      | previous =>
          have htIndex' : sourceIndex P W s.1 s.property =
              Erdos957Case4NoThree.awayHullVertex P
                (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
            simpa [Erdos957Case4NoThree.awayHullVertex, htSide] using htReverse
          have htAssoc := split_right_association_eq_opposite_at_away_second
            hA Q T S htRole hsRole htIndex'
          change T.descriptor.association =
            oppositeCyclicSideAssociation Qt.twoExtreme.side at htAssoc
          intro hEq
          rw [hsAssoc, htAssoc] at hEq
          simpa [hsSide, htSide, cyclicSideAssociation,
            oppositeCyclicSideAssociation] using hEq
      | next =>
          have htIndex' : sourceIndex P W s.1 s.property =
              Erdos957Case4NoThree.incidentHullVertex P
                (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
            simpa [Erdos957Case4NoThree.incidentHullVertex, htSide] using htReverse
          have htAssoc := split_right_association_eq_side_at_incident_second
            hA Q T S htRole hsRole htIndex'
          change T.descriptor.association =
            cyclicSideAssociation Qt.twoExtreme.side at htAssoc
          intro hEq
          rw [hsAssoc, htAssoc] at hEq
          simpa [hsSide, htSide, cyclicSideAssociation] using hEq
  | next =>
      have htReverse : sourceIndex P W s.1 s.property =
          ((P.next⁻¹) ^ 2) (sourceIndex P W t.1 t.property) := by
        have hh := congrArg (fun x ↦ ((P.next⁻¹) ^ 2) x) htIndex
        simpa [Erdos957Case4NoThree.incidentHullVertex, hsSide] using hh.symm
      cases htSide : Qt.twoExtreme.side with
      | previous =>
          have htIndex' : sourceIndex P W s.1 s.property =
              Erdos957Case4NoThree.incidentHullVertex P
                (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
            simpa [Erdos957Case4NoThree.incidentHullVertex, htSide] using htReverse
          have htAssoc := split_right_association_eq_side_at_incident_second
            hA Q T S htRole hsRole htIndex'
          change T.descriptor.association =
            cyclicSideAssociation Qt.twoExtreme.side at htAssoc
          intro hEq
          rw [hsAssoc, htAssoc] at hEq
          simpa [hsSide, htSide, cyclicSideAssociation] using hEq
      | next =>
          have htIndex' : sourceIndex P W s.1 s.property =
              Erdos957Case4NoThree.awayHullVertex P
                (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
            simpa [Erdos957Case4NoThree.awayHullVertex, htSide] using htReverse
          have htAssoc := split_right_association_eq_opposite_at_away_second
            hA Q T S htRole hsRole htIndex'
          change T.descriptor.association =
            oppositeCyclicSideAssociation Qt.twoExtreme.side at htAssoc
          intro hEq
          rw [hsAssoc, htAssoc] at hEq
          simpa [hsSide, htSide, cyclicSideAssociation,
            oppositeCyclicSideAssociation] using hEq

/-- Two split-right arrivals whose sources are two hull steps apart on the
anchor's away prefix also have opposite associations.  Reversing the
comparison either makes the anchor a second incident-prefix source, or
leaves both rows on away prefixes with opposite edge orientations. -/
theorem split_right_associations_ne_at_away_second
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 1) :
    S.descriptor.association ≠ T.descriptor.association := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.awayHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 at htIndex
  have hsAssoc := split_right_association_eq_opposite_at_away_second
    hA Q S T hsRole htRole htIndex
  change S.descriptor.association =
    oppositeCyclicSideAssociation Qs.twoExtreme.side at hsAssoc
  cases hsSide : Qs.twoExtreme.side with
  | previous =>
      have htReverse : sourceIndex P W s.1 s.property =
          ((P.next⁻¹) ^ 2) (sourceIndex P W t.1 t.property) := by
        have hh := congrArg (fun x ↦ ((P.next⁻¹) ^ 2) x) htIndex
        simpa [Erdos957Case4NoThree.awayHullVertex, hsSide] using hh.symm
      cases htSide : Qt.twoExtreme.side with
      | previous =>
          have htIndex' : sourceIndex P W s.1 s.property =
              Erdos957Case4NoThree.incidentHullVertex P
                (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
            simpa [Erdos957Case4NoThree.incidentHullVertex, htSide] using htReverse
          exact (split_right_associations_ne_at_incident_second
            hA Q T S htRole hsRole htIndex').symm
      | next =>
          have htIndex' : sourceIndex P W s.1 s.property =
              Erdos957Case4NoThree.awayHullVertex P
                (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
            simpa [Erdos957Case4NoThree.awayHullVertex, htSide] using htReverse
          have htAssoc := split_right_association_eq_opposite_at_away_second
            hA Q T S htRole hsRole htIndex'
          change T.descriptor.association =
            oppositeCyclicSideAssociation Qt.twoExtreme.side at htAssoc
          intro hEq
          rw [hsAssoc, htAssoc] at hEq
          simpa [hsSide, htSide, oppositeCyclicSideAssociation] using hEq
  | next =>
      have htReverse : sourceIndex P W s.1 s.property =
          (P.next ^ 2) (sourceIndex P W t.1 t.property) := by
        have hh := congrArg (fun x ↦ (P.next ^ 2) x) htIndex
        simpa [Erdos957Case4NoThree.awayHullVertex, hsSide] using hh.symm
      cases htSide : Qt.twoExtreme.side with
      | previous =>
          have htIndex' : sourceIndex P W s.1 s.property =
              Erdos957Case4NoThree.awayHullVertex P
                (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
            simpa [Erdos957Case4NoThree.awayHullVertex, htSide] using htReverse
          have htAssoc := split_right_association_eq_opposite_at_away_second
            hA Q T S htRole hsRole htIndex'
          change T.descriptor.association =
            oppositeCyclicSideAssociation Qt.twoExtreme.side at htAssoc
          intro hEq
          rw [hsAssoc, htAssoc] at hEq
          simpa [hsSide, htSide, oppositeCyclicSideAssociation] using hEq
      | next =>
          have htIndex' : sourceIndex P W s.1 s.property =
              Erdos957Case4NoThree.incidentHullVertex P
                (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 1 := by
            simpa [Erdos957Case4NoThree.incidentHullVertex, htSide] using htReverse
          exact (split_right_associations_ne_at_incident_second
            hA Q T S htRole hsRole htIndex').symm

/-- Three steps through an incident endpoint also force opposite split-right
associations.  If the reverse row points the same way, the anchor is on its
away third prefix and the side-free metric gap already rules out the common
target; otherwise both signed incident-prefix estimates give opposite cyclic
labels. -/
theorem split_right_associations_ne_at_incident_third
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.incidentHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 2) :
    S.descriptor.association ≠ T.descriptor.association := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  change sourceIndex P W t.1 t.property =
    Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 at htIndex
  have hsAssoc := split_right_association_eq_side_at_incident_third
    hA Q S T hsRole htRole htIndex
  change S.descriptor.association =
    cyclicSideAssociation Qs.twoExtreme.side at hsAssoc
  cases hsSide : Qs.twoExtreme.side with
  | previous =>
      have htReverse : sourceIndex P W s.1 s.property =
          (P.next ^ 3) (sourceIndex P W t.1 t.property) := by
        have hh := congrArg (fun x ↦ (P.next ^ 3) x) htIndex
        simpa [Erdos957Case4NoThree.incidentHullVertex, hsSide] using hh.symm
      cases htSide : Qt.twoExtreme.side with
      | previous =>
          exfalso
          apply Erdos957Case4SplitDistance.no_split_right_competitor_at_away_third
            Q T S htRole hsRole
          change sourceIndex P W s.1 s.property =
            Erdos957Case4NoThree.awayHullVertex P
              (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 2
          simpa [Erdos957Case4NoThree.awayHullVertex, htSide] using htReverse
      | next =>
          have htIndex' : sourceIndex P W s.1 s.property =
              Erdos957Case4NoThree.incidentHullVertex P
                (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 2 := by
            simpa [Erdos957Case4NoThree.incidentHullVertex, htSide] using htReverse
          have htAssoc := split_right_association_eq_side_at_incident_third
            hA Q T S htRole hsRole htIndex'
          change T.descriptor.association =
            cyclicSideAssociation Qt.twoExtreme.side at htAssoc
          intro hEq
          rw [hsAssoc, htAssoc] at hEq
          simpa [hsSide, htSide, cyclicSideAssociation] using hEq
  | next =>
      have htReverse : sourceIndex P W s.1 s.property =
          ((P.next⁻¹) ^ 3) (sourceIndex P W t.1 t.property) := by
        have hh := congrArg (fun x ↦ ((P.next⁻¹) ^ 3) x) htIndex
        simpa [Erdos957Case4NoThree.incidentHullVertex, hsSide] using hh.symm
      cases htSide : Qt.twoExtreme.side with
      | previous =>
          have htIndex' : sourceIndex P W s.1 s.property =
              Erdos957Case4NoThree.incidentHullVertex P
                (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 2 := by
            simpa [Erdos957Case4NoThree.incidentHullVertex, htSide] using htReverse
          have htAssoc := split_right_association_eq_side_at_incident_third
            hA Q T S htRole hsRole htIndex'
          change T.descriptor.association =
            cyclicSideAssociation Qt.twoExtreme.side at htAssoc
          intro hEq
          rw [hsAssoc, htAssoc] at hEq
          simpa [hsSide, htSide, cyclicSideAssociation] using hEq
      | next =>
          exfalso
          apply Erdos957Case4SplitDistance.no_split_right_competitor_at_away_third
            Q T S htRole hsRole
          change sourceIndex P W s.1 s.property =
            Erdos957Case4NoThree.awayHullVertex P
              (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 2
          simpa [Erdos957Case4NoThree.awayHullVertex, htSide] using htReverse

/-- Two selected split-right arrivals in one genuine seven-window with the
same recipient-relative association have the same source.  The six
noncentral positions are discharged respectively by the signed third- and
second-prefix estimates, coherent incident-edge opposition, and the two
outward-adjacent flat-edge estimates. -/
theorem split_right_same_association_source_eq_in_window
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hassoc : S.descriptor.association = T.descriptor.association) :
    s = t := by
  by_contra hst
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  have horbits :=
    Erdos957ExceptionalWindowDispatch.sourceIndex_orbit_cases_of_mem_seven_window
      htWindow hst
  cases hsSide : Qs.twoExtreme.side with
  | previous =>
      rcases horbits with h | h | h | h | h | h
      · have hidx : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.incidentHullVertex P
              (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 := by
          simpa [Erdos957Case4NoThree.incidentHullVertex, hsSide] using h
        exact (split_right_associations_ne_at_incident_third
          hA Q S T hsRole htRole hidx) hassoc
      · have hidx : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.incidentHullVertex P
              (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 := by
          simpa [Erdos957Case4NoThree.incidentHullVertex, hsSide] using h
        exact (split_right_associations_ne_at_incident_second
          hA Q S T hsRole htRole hidx) hassoc
      · have hidx : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.incidentHullVertex P
              (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 := by
          simpa [Erdos957Case4NoThree.incidentHullVertex, hsSide] using h
        exact (incident_partner_split_right_associations_ne
          hA Q S T hsRole htRole hidx) hassoc
      · cases htSide : Qt.twoExtreme.side with
        | previous =>
            have hreverse : sourceIndex P W s.1 s.property =
                Erdos957Case4NoThree.incidentHullVertex P
                  (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 0 := by
              have hh := congrArg (fun x ↦ P.next⁻¹ x) h
              simpa [Erdos957Case4NoThree.incidentHullVertex, htSide] using hh.symm
            exact (incident_partner_split_right_associations_ne
              hA Q T S htRole hsRole hreverse) hassoc.symm
        | next =>
            have hidx : sourceIndex P W t.1 t.property =
                Erdos957Case4NoThree.awayHullVertex P
                  (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 := by
              simpa [Erdos957Case4NoThree.awayHullVertex, hsSide] using h
            have hreverse : sourceIndex P W s.1 s.property =
                Erdos957Case4NoThree.awayHullVertex P
                  (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 0 := by
              have hh := congrArg (fun x ↦ P.next⁻¹ x) h
              simpa [Erdos957Case4NoThree.awayHullVertex, htSide] using hh.symm
            have hsAssoc := split_right_association_eq_opposite_at_outward_adjacent
              Q S T hsRole htRole hidx (by
                change Qt.twoExtreme.side ≠ Qs.twoExtreme.side
                simp [hsSide, htSide])
            have htAssoc := split_right_association_eq_opposite_at_outward_adjacent
              Q T S htRole hsRole hreverse (by
                change Qs.twoExtreme.side ≠ Qt.twoExtreme.side
                simp [hsSide, htSide])
            change S.descriptor.association =
              oppositeCyclicSideAssociation Qs.twoExtreme.side at hsAssoc
            change T.descriptor.association =
              oppositeCyclicSideAssociation Qt.twoExtreme.side at htAssoc
            rw [hsAssoc, htAssoc] at hassoc
            simpa [hsSide, htSide, oppositeCyclicSideAssociation] using hassoc
      · have hidx : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.awayHullVertex P
              (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 := by
          simpa [Erdos957Case4NoThree.awayHullVertex, hsSide] using h
        exact (split_right_associations_ne_at_away_second
          hA Q S T hsRole htRole hidx) hassoc
      · apply Erdos957Case4SplitDistance.no_split_right_competitor_at_away_third
          Q S T hsRole htRole
        change sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2
        simpa [Erdos957Case4NoThree.awayHullVertex, hsSide] using h
  | next =>
      rcases horbits with h | h | h | h | h | h
      · apply Erdos957Case4SplitDistance.no_split_right_competitor_at_away_third
          Q S T hsRole htRole
        change sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2
        simpa [Erdos957Case4NoThree.awayHullVertex, hsSide] using h
      · have hidx : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.awayHullVertex P
              (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 := by
          simpa [Erdos957Case4NoThree.awayHullVertex, hsSide] using h
        exact (split_right_associations_ne_at_away_second
          hA Q S T hsRole htRole hidx) hassoc
      · cases htSide : Qt.twoExtreme.side with
        | previous =>
            have hidx : sourceIndex P W t.1 t.property =
                Erdos957Case4NoThree.awayHullVertex P
                  (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 := by
              simpa [Erdos957Case4NoThree.awayHullVertex, hsSide] using h
            have hreverse : sourceIndex P W s.1 s.property =
                Erdos957Case4NoThree.awayHullVertex P
                  (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 0 := by
              have hh := congrArg (fun x ↦ P.next x) h
              simpa [Erdos957Case4NoThree.awayHullVertex, htSide] using hh.symm
            have hsAssoc := split_right_association_eq_opposite_at_outward_adjacent
              Q S T hsRole htRole hidx (by
                change Qt.twoExtreme.side ≠ Qs.twoExtreme.side
                simp [hsSide, htSide])
            have htAssoc := split_right_association_eq_opposite_at_outward_adjacent
              Q T S htRole hsRole hreverse (by
                change Qs.twoExtreme.side ≠ Qt.twoExtreme.side
                simp [hsSide, htSide])
            change S.descriptor.association =
              oppositeCyclicSideAssociation Qs.twoExtreme.side at hsAssoc
            change T.descriptor.association =
              oppositeCyclicSideAssociation Qt.twoExtreme.side at htAssoc
            rw [hsAssoc, htAssoc] at hassoc
            simpa [hsSide, htSide, oppositeCyclicSideAssociation] using hassoc
        | next =>
            have hreverse : sourceIndex P W s.1 s.property =
                Erdos957Case4NoThree.incidentHullVertex P
                  (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 0 := by
              have hh := congrArg (fun x ↦ P.next x) h
              simpa [Erdos957Case4NoThree.incidentHullVertex, htSide] using hh.symm
            exact (incident_partner_split_right_associations_ne
              hA Q T S htRole hsRole hreverse) hassoc.symm
      · have hidx : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.incidentHullVertex P
              (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 := by
          simpa [Erdos957Case4NoThree.incidentHullVertex, hsSide] using h
        exact (incident_partner_split_right_associations_ne
          hA Q S T hsRole htRole hidx) hassoc
      · have hidx : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.incidentHullVertex P
              (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 := by
          simpa [Erdos957Case4NoThree.incidentHullVertex, hsSide] using h
        exact (split_right_associations_ne_at_incident_second
          hA Q S T hsRole htRole hidx) hassoc
      · have hidx : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.incidentHullVertex P
              (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2 := by
          simpa [Erdos957Case4NoThree.incidentHullVertex, hsSide] using h
        exact (split_right_associations_ne_at_incident_third
          hA Q S T hsRole htRole hidx) hassoc
/-- Equal formula-derived associations reduce two distinct split-right
arrivals in the genuine seven-window to the two cyclic positions at
distance two from the anchor.  The incident endpoint is eliminated by
pair coherence, while the two distance-three positions are eliminated by
the checked three-unit metric gap.  No claim is made here about the two
remaining positions: their distinction is exactly the cross-edge
farthest-recipient problem. -/
theorem same_association_split_right_reduces_to_distance_two
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t)
    (hassoc : S.descriptor.association = T.descriptor.association)
    (hsEnum : S.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side)
    (htEnum : T.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair t.1 t.property
          ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩).twoExtreme.side) :
    let Qs := Q.case4_pair s.1 s.property
      ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
    sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.incidentHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  have hsides : Qs.twoExtreme.side = Qt.twoExtreme.side := by
    apply cyclicSideAssociation_injective
    rw [← hsEnum, ← htEnum]
    exact hassoc
  have horbits :=
    Erdos957ExceptionalWindowDispatch.sourceIndex_orbit_cases_of_mem_seven_window
      htWindow hst
  change sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.incidentHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1
  cases hside : Qs.twoExtreme.side with
  | previous =>
      have htSide : Qt.twoExtreme.side = .previous := by
        rw [← hsides, hside]
      rcases horbits with h | h | h | h | h | h
      · exfalso
        apply Erdos957Case4SplitDistance.no_split_right_competitor_at_away_third
          Q T S htRole hsRole
        change sourceIndex P W s.1 s.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 2
        have hh := congrArg (fun x ↦ (P.next ^ 3) x) h
        simpa [Erdos957Case4NoThree.awayHullVertex, htSide] using hh.symm
      · exact Or.inl (by
          simpa [Erdos957Case4NoThree.incidentHullVertex, hside] using h)
      · exfalso
        have hidx : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.incidentHullVertex P
              (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 := by
          simpa [Erdos957Case4NoThree.incidentHullVertex, hside] using h
        exact (incident_partner_split_right_associations_ne hA Q S T
          hsRole htRole hidx) hassoc
      · exfalso
        have hidx : sourceIndex P W s.1 s.property =
          Erdos957Case4NoThree.incidentHullVertex P
            (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 0 := by
          have hh := congrArg (fun x ↦ (P.next⁻¹) x) h
          simpa [Erdos957Case4NoThree.incidentHullVertex, htSide] using hh.symm
        exact (incident_partner_split_right_associations_ne hA Q T S
          htRole hsRole hidx) hassoc.symm
      · exact Or.inr (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)
      · exfalso
        apply Erdos957Case4SplitDistance.no_split_right_competitor_at_away_third
          Q S T hsRole htRole
        change sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h
  | next =>
      have htSide : Qt.twoExtreme.side = .next := by
        rw [← hsides, hside]
      rcases horbits with h | h | h | h | h | h
      · exfalso
        apply Erdos957Case4SplitDistance.no_split_right_competitor_at_away_third
          Q S T hsRole htRole
        change sourceIndex P W t.1 t.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 2
        simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h
      · exact Or.inr (by
          simpa [Erdos957Case4NoThree.awayHullVertex, hside] using h)
      · exfalso
        have hidx : sourceIndex P W s.1 s.property =
          Erdos957Case4NoThree.incidentHullVertex P
            (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 0 := by
          have hh := congrArg (fun x ↦ P.next x) h
          simpa [Erdos957Case4NoThree.incidentHullVertex, htSide] using hh.symm
        exact (incident_partner_split_right_associations_ne hA Q T S
          htRole hsRole hidx) hassoc.symm
      · exfalso
        have hidx : sourceIndex P W t.1 t.property =
            Erdos957Case4NoThree.incidentHullVertex P
              (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 := by
          simpa [Erdos957Case4NoThree.incidentHullVertex, hside] using h
        exact (incident_partner_split_right_associations_ne hA Q S T
          hsRole htRole hidx) hassoc
      · exact Or.inl (by
          simpa [Erdos957Case4NoThree.incidentHullVertex, hside] using h)
      · exfalso
        apply Erdos957Case4SplitDistance.no_split_right_competitor_at_away_third
          Q T S htRole hsRole
        change sourceIndex P W s.1 s.property =
          Erdos957Case4NoThree.awayHullVertex P
            (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 2
        have hh := congrArg (fun x ↦ ((P.next⁻¹) ^ 3) x) h
        simpa [Erdos957Case4NoThree.awayHullVertex, htSide] using hh.symm

/-- Three distinct split-right arrivals with one formula-derived
association cannot share a target.  The two competitors reduce to the two
opposite distance-two positions; their equilateral middles are then more
than two horizontal units apart, although both would be unit from the
common target. -/
theorem three_split_right_same_association_in_window
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (huRole : U.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htAssoc : T.descriptor.association = S.descriptor.association)
    (huAssoc : U.descriptor.association = S.descriptor.association)
    (hsEnum : S.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side)
    (htEnum : T.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair t.1 t.property
          ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩).twoExtreme.side)
    (huEnum : U.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair u.1 u.property
          ⟨U.target.target, by simpa [huRole] using U.target.target_at_role⟩).twoExtreme.side)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) : False := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  let Qu := Q.case4_pair u.1 u.property
    ⟨U.target.target, by simpa [huRole] using U.target.target_at_role⟩
  have htPos := same_association_split_right_reduces_to_distance_two
    hA Q S T hsRole htRole htWindow hst htAssoc.symm hsEnum htEnum
  have huPos := same_association_split_right_reduces_to_distance_two
    hA Q S U hsRole huRole huWindow hsu huAssoc.symm hsEnum huEnum
  change sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.incidentHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 at htPos
  change sourceIndex P W u.1 u.property =
        Erdos957Case4NoThree.incidentHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W u.1 u.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 at huPos
  have htargetT : T.target.target = Qt.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← T.target.target_at_role, htRole, Qt.current_secondary_role]
  have htargetU : U.target.target = Qu.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← U.target.target_at_role, huRole, Qu.current_secondary_role]
  have htVertex : Qt.currentSecondaryTarget.vertex = v := by
    calc
      Qt.currentSecondaryTarget.vertex = T.target.target.vertex :=
        congrArg LocalTarget.vertex htargetT.symm
      _ = v := T.target.vertex_eq.symm
  have huVertex : Qu.currentSecondaryTarget.vertex = v := by
    calc
      Qu.currentSecondaryTarget.vertex = U.target.target.vertex :=
        congrArg LocalTarget.vertex htargetU.symm
      _ = v := U.target.vertex_eq.symm
  have htAdj : (unitDistanceGraph A).Adj Qt.middle v := by
    rw [← htVertex]
    exact CommonPairedCase4Rows.middle_adj_currentSecondary Qt
  have huAdj : (unitDistanceGraph A).Adj Qu.middle v := by
    rw [← huVertex]
    exact CommonPairedCase4Rows.middle_adj_currentSecondary Qu
  rcases htPos with htIncident | htAway <;>
    rcases huPos with huIncident | huAway
  · apply htu
    apply Subtype.ext
    have h := htIncident.trans huIncident.symm
    simpa [sourceIndex] using congrArg Subtype.val h
  · apply Erdos957ExceptionalCollisionGeometry.no_common_unit_target_of_rigid_fst_gap_gt_two
      Qs.normalized.frame htAdj huAdj
    exact opposite_distance_two_middle_fst_gap_gt_two Q S T U
      hsRole htRole huRole htAssoc huAssoc hsEnum htEnum huEnum
      htIncident huAway
  · apply Erdos957ExceptionalCollisionGeometry.no_common_unit_target_of_rigid_fst_gap_gt_two
      Qs.normalized.frame huAdj htAdj
    have hgap := opposite_distance_two_middle_fst_gap_gt_two Q S U T
      hsRole huRole htRole huAssoc htAssoc hsEnum huEnum htEnum
      huIncident htAway
    exact hgap
  · apply htu
    apply Subtype.ext
    have h := htAway.trans huAway.symm
    simpa [sourceIndex] using congrArg Subtype.val h

/-- A split-right middle based at the second away source and a direct
source at the second incident position are more than two horizontal units
apart in the anchor frame. -/
private lemma no_away_second_split_incident_second_direct
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (huDirect : IsDirectTargetRole U.target.role)
    (htIndex : sourceIndex P W t.1 t.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 1)
    (huIndex : sourceIndex P W u.1 u.property =
      Erdos957Case4CollisionLeaves.incidentContinuationHullVertex P
        (sourceIndex P W s.1 s.property)
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side 1) :
    False := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  have htargetT : T.target.target = Qt.currentSecondaryTarget := by
    apply Option.some.inj
    rw [← T.target.target_at_role, htRole, Qt.current_secondary_role]
  have htVertex : Qt.currentSecondaryTarget.vertex = v := by
    calc
      Qt.currentSecondaryTarget.vertex = T.target.target.vertex :=
        congrArg LocalTarget.vertex htargetT.symm
      _ = v := T.target.vertex_eq.symm
  have htAdj : (unitDistanceGraph A).Adj Qt.middle v := by
    rw [← htVertex]
    exact CommonPairedCase4Rows.middle_adj_currentSecondary Qt
  have huAdj : (unitDistanceGraph A).Adj
      (sourceIndex P W u.1 u.property).1 v :=
    U.target.adj_source_of_directRole huDirect
  have htSourceUnit : (unitDistanceGraph A).Adj
      (sourceIndex P W t.1 t.property).1 Qt.middle :=
    CommonPairedCase4Rows.source_adj_middle Qt
  have htFst := abs_fst_sub_le_one_of_adj Qs.normalized.frame htSourceUnit
  have haway :=
    Erdos957Case4NoThree.normalizedFrame_away_second_fst_gt_three_halves
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized (source_isFlat P W _ s.property)
  have hincident :=
    Erdos957Case4NoThree.normalizedFrame_incident_second_fst_lt_neg_three_halves
      F (sourceIndex P W s.1 s.property) Qs.middle Qs.twoExtreme
        Qs.normalized (source_isFlat P W _ s.property)
  change sourceIndex P W u.1 u.property =
    Erdos957Case4NoThree.incidentHullVertex P
      (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 at huIndex
  apply Erdos957ExceptionalCollisionGeometry.no_common_unit_target_of_rigid_fst_gap_gt_two
    Qs.normalized.frame htAdj huAdj
  rw [htIndex] at htFst
  change |(Qs.normalized.frame.toCanonical
      (Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1).1) 0 -
      (Qs.normalized.frame.toCanonical Qt.middle) 0| ≤ 1 at htFst
  rw [huIndex]
  rw [abs_of_pos]
  · rcases abs_le.mp htFst with ⟨htLower, htUpper⟩
    linarith [haway, hincident]
  · rcases abs_le.mp htFst with ⟨htLower, htUpper⟩
    linarith [haway, hincident]

/-- A split-right anchor, a second split-right arrival, and a direct
arrival cannot all have the same formula-derived cyclic association in one
genuine seven-window. -/
theorem two_split_right_one_direct_same_association_in_window
    (hA : IsOneSeparated A)
    (Q : CommonCoherentRealizedSourceRows P W F.chart)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (hsRole : S.target.role = PairCases.TargetRoleName.case4SplitRight)
    (htRole : T.target.role = PairCases.TargetRoleName.case4SplitRight)
    (huDirect : IsDirectTargetRole U.target.role)
    (htAssoc : T.descriptor.association = S.descriptor.association)
    (_huAssoc : U.descriptor.association = S.descriptor.association)
    (hsEnum : S.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair s.1 s.property
          ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩).twoExtreme.side)
    (htEnum : T.descriptor.association =
      cyclicSideAssociation
        (Q.case4_pair t.1 t.property
          ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩).twoExtreme.side)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) : False := by
  let Qs := Q.case4_pair s.1 s.property
    ⟨S.target.target, by simpa [hsRole] using S.target.target_at_role⟩
  let Qt := Q.case4_pair t.1 t.property
    ⟨T.target.target, by simpa [htRole] using T.target.target_at_role⟩
  have htPos := same_association_split_right_reduces_to_distance_two
    hA Q S T hsRole htRole htWindow hst htAssoc.symm hsEnum htEnum
  have huNot2 : U.target.role ≠ PairCases.TargetRoleName.case2Secondary := by
    intro h
    rw [h] at huDirect
    simp [IsDirectTargetRole] at huDirect
  have huNot4 : U.target.role ≠ PairCases.TargetRoleName.case4SplitRight := by
    intro h
    rw [h] at huDirect
    simp [IsDirectTargetRole] at huDirect
  have huPos := Erdos957Case4CollisionLeaves.direct_competitor_reduces_to_near_two
    Q S.target U.target hsRole huNot2 huNot4 huWindow hsu
  change sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.incidentHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W t.1 t.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 at htPos
  change sourceIndex P W u.1 u.property =
        Erdos957Case4CollisionLeaves.incidentContinuationHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 1 ∨
      sourceIndex P W u.1 u.property =
        Erdos957Case4NoThree.awayHullVertex P
          (sourceIndex P W s.1 s.property) Qs.twoExtreme.side 0 at huPos
  have htSide : Qt.twoExtreme.side = Qs.twoExtreme.side := by
    apply cyclicSideAssociation_injective
    rw [← htEnum, ← hsEnum]
    exact htAssoc
  rcases htPos with htIncident | htAway <;>
    rcases huPos with huIncident | huAway
  · apply htu
    apply Subtype.ext
    have h := htIncident.trans huIncident.symm
    simpa [sourceIndex, Erdos957Case4CollisionLeaves.incidentContinuationHullVertex,
      Erdos957Case4NoThree.incidentHullVertex] using congrArg Subtype.val h
  · apply Erdos957Case4CollisionLeaves.realized_no_direct_competitor_at_away_third
      Q T.target U.target htRole huNot2 huNot4
    change sourceIndex P W u.1 u.property =
      Erdos957Case4NoThree.awayHullVertex P
        (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 2
    rw [htSide, htIncident, huAway]
    cases hside : Qs.twoExtreme.side <;>
      simp [Erdos957Case4NoThree.awayHullVertex,
        Erdos957Case4NoThree.incidentHullVertex, hside, pow_succ]
  · exact no_away_second_split_incident_second_direct Q S T U
      hsRole htRole huDirect htAway huIncident
  · apply Erdos957Case4CollisionLeaves.realized_no_direct_competitor_at_incident_partner
      Q T.target U.target htRole huDirect
    change sourceIndex P W u.1 u.property =
      Erdos957Case4CollisionLeaves.incidentContinuationHullVertex P
        (sourceIndex P W t.1 t.property) Qt.twoExtreme.side 0
    rw [htSide, htAway, huAway]
    cases hside : Qs.twoExtreme.side <;>
      simp [Erdos957Case4CollisionLeaves.incidentContinuationHullVertex,
        Erdos957Case4NoThree.awayHullVertex, hside, pow_succ]

/-! ## Weight-aware Case-4 frontier

The charging inequality does not require pairwise uniqueness of split-right
arrivals.  A split-right arrival has doubled weight one.  Consequently a
triple containing two split-right arrivals is automatically safe at degree
at most four, and a whole third arrival itself forces degree at most four.
Only an all-half triple at degree five remains geometric.  Similarly, after
the checked exclusion of two direct competitors, a four-source column with a
split-right anchor has only two role multisets left. -/

/-- A realized split-right role always carries one doubled token. -/
lemma RealizedArrivalAt.token_eq_one_of_case4SplitRight
    {rows : HasRealizedSourceRows P W F.chart}
    {s : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (hrole : S.target.role = PairCases.TargetRoleName.case4SplitRight) :
    (rows s.1 s.property).localCase.tokens v = 1 := by
  rw [S.target.token_eq_roleWeight, hrole]
  cases R : rows s.1 s.property with
  | case1 middle hdegree hone middleCoord hmiddleCoord hmiddleNot hunit row =>
      simp [RealizedSourceRow.roleWeight, ArrivalWeight.tokens]
  | case2 middle hdegree htwo hmiddleNot T normalized row =>
      simp [RealizedSourceRow.roleWeight, ArrivalWeight.tokens]
  | case3 middle hdegree hone middleCoord row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.roleWeight, ArrivalWeight.tokens]
  | case4 middle hdegree htwo T normalized row hmiddleVertex =>
      cases row <;> simp [RealizedSourceRow.roleWeight, ArrivalWeight.tokens]

/-- Every positive formula role carries at most two doubled tokens. -/
private lemma RealizedArrivalAt.token_le_two
    {rows : HasRealizedSourceRows P W F.chart}
    {s : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v) :
    (rows s.1 s.property).localCase.tokens v ≤ 2 := by
  rw [S.target.token_eq_roleWeight]
  cases (rows s.1 s.property).roleWeight S.target.role <;>
    simp [ArrivalWeight.tokens]

/-- Two half arrivals and an arbitrary positive realized arrival fit at
degree at most four. -/
private lemma two_half_triple_fits_of_degree_le_four
    {rows : HasRealizedSourceRows P W F.chart}
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v)
    (hsHalf : (rows s.1 s.property).localCase.tokens v = 1)
    (htHalf : (rows t.1 t.property).localCase.tokens v = 1)
    (hdegree : (unitDistanceGraph A).degree v ≤ 4) :
    Fits ((unitDistanceGraph A).degree v)
      ((rows s.1 s.property).localCase.tokens v +
        (rows t.1 t.property).localCase.tokens v +
        (rows u.1 u.property).localCase.tokens v) := by
  have hu : (rows u.1 u.property).localCase.tokens v ≤ 2 := by
    rw [U.target.token_eq_roleWeight]
    cases (rows u.1 u.property).roleWeight U.target.role <;>
      simp [ArrivalWeight.tokens]
  change 2 * (unitDistanceGraph A).degree v +
    ((rows s.1 s.property).localCase.tokens v +
      (rows t.1 t.property).localCase.tokens v +
      (rows u.1 u.property).localCase.tokens v) ≤ 12
  omega

/-- Arithmetic reduction for the only nontrivial Case-4 triple shape. -/
private lemma two_half_triple_fits_of_no_degree_five_three_halves
    {rows : HasRealizedSourceRows P W F.chart}
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) rows s v)
    (T : RealizedArrivalAt (F := F) rows t v)
    (U : RealizedArrivalAt (F := F) rows u v)
    (hsHalf : (rows s.1 s.property).localCase.tokens v = 1)
    (htHalf : (rows t.1 t.property).localCase.tokens v = 1)
    (hdegree : (unitDistanceGraph A).degree v ≤ 5)
    (hexclude : (rows u.1 u.property).localCase.tokens v = 1 →
      (unitDistanceGraph A).degree v = 5 → False) :
    Fits ((unitDistanceGraph A).degree v)
      ((rows s.1 s.property).localCase.tokens v +
        (rows t.1 t.property).localCase.tokens v +
        (rows u.1 u.property).localCase.tokens v) := by
  rcases (rows u.1 u.property).localCase.positive_weight U.positive with
      huHalf | huWhole
  · by_cases hfour : (unitDistanceGraph A).degree v ≤ 4
    · exact two_half_triple_fits_of_degree_le_four S T U
        hsHalf htHalf hfour
    · exact (hexclude huHalf (by omega)).elim
  · have hfour :=
      (rows u.1 u.property).localCase.whole_target_degree_le_four huWhole
    exact two_half_triple_fits_of_degree_le_four S T U hsHalf htHalf hfour

/-- The exact genuinely geometric residue of the weight-aware Case-4
dispatcher.  The first two fields concern only an all-half triple at degree
five.  The next two retain the honest quadruple `Fits` conclusions rather
than excluding safe four-half columns.  The final two are the
same-association triples to which the no-five argument reduces by Boolean
pigeonhole. -/
structure Case4WeightedCollisionResiduals
    (Q : CommonCoherentRealizedSourceRows P W F.chart) where
  split_split_half_direct_degree_five :
    ∀ {s t u : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v),
      S.target.role = .case4SplitRight →
      T.target.role = .case4SplitRight →
      IsDirectTargetRole U.target.role →
      (Q.rows u.1 u.property).localCase.tokens v = 1 →
      (unitDistanceGraph A).degree v = 5 →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → t ≠ u → False
  three_split_right_degree_five :
    ∀ {s t u : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v),
      S.target.role = .case4SplitRight →
      T.target.role = .case4SplitRight →
      U.target.role = .case4SplitRight →
      (unitDistanceGraph A).degree v = 5 →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → t ≠ u → False
  /-- A safe four-source column is retained rather than excluded.  This is
  the only no-Case-2 quadruple shape with exactly one direct role. -/
  three_split_right_one_direct_quadruple_fits :
    ∀ {s t u d : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v)
      (D : RealizedArrivalAt (F := F) Q.rows d v),
      S.target.role = .case4SplitRight →
      T.target.role = .case4SplitRight →
      U.target.role = .case4SplitRight →
      IsDirectTargetRole D.target.role →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      d.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → s ≠ d →
      t ≠ u → t ≠ d → u ≠ d →
      Fits ((unitDistanceGraph A).degree v)
        ((Q.rows s.1 s.property).localCase.tokens v +
          (Q.rows t.1 t.property).localCase.tokens v +
          (Q.rows u.1 u.property).localCase.tokens v +
          (Q.rows d.1 d.property).localCase.tokens v)
  /-- Four split-right half arrivals are permitted exactly when their
  degree/weight column satisfies `Fits`. -/
  four_split_right_quadruple_fits :
    ∀ {s t u d : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v)
      (D : RealizedArrivalAt (F := F) Q.rows d v),
      S.target.role = .case4SplitRight →
      T.target.role = .case4SplitRight →
      U.target.role = .case4SplitRight →
      D.target.role = .case4SplitRight →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      d.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → s ≠ d →
      t ≠ u → t ≠ d → u ≠ d →
      Fits ((unitDistanceGraph A).degree v)
        ((Q.rows s.1 s.property).localCase.tokens v +
          (Q.rows t.1 t.property).localCase.tokens v +
          (Q.rows u.1 u.property).localCase.tokens v +
          (Q.rows d.1 d.property).localCase.tokens v)
  /-- No three distinct split-right hits with one common formula-derived
  association.  Five split hits reduce to this by two-color pigeonhole. -/
  three_split_right_same_association :
    ∀ {s t u : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v),
      S.target.role = .case4SplitRight →
      T.target.role = .case4SplitRight →
      U.target.role = .case4SplitRight →
      T.descriptor.association = S.descriptor.association →
      U.descriptor.association = S.descriptor.association →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → t ≠ u → False
  /-- The second same-association triple left when five arrivals consist of
  four split-right hits and one direct hit. -/
  two_split_right_one_direct_same_association :
    ∀ {s t u : Source P W} {v : Vertex A}
      (S : RealizedArrivalAt (F := F) Q.rows s v)
      (T : RealizedArrivalAt (F := F) Q.rows t v)
      (U : RealizedArrivalAt (F := F) Q.rows u v),
      S.target.role = .case4SplitRight →
      T.target.role = .case4SplitRight →
      IsDirectTargetRole U.target.role →
      T.descriptor.association = S.descriptor.association →
      U.descriptor.association = S.descriptor.association →
      t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
        (sevenShift P.next j (sourceIndex P W s.1 s.property)).1) →
      s ≠ t → s ≠ u → t ≠ u → False

private lemma direct_of_not_secondary_or_split
    {role : PairCases.TargetRoleName}
    (h2 : role ≠ .case2Secondary) (h4 : role ≠ .case4SplitRight) :
    IsDirectTargetRole role := by
  cases role <;> simp_all [IsDirectTargetRole]

/-- Capacity dispatcher for a split-right anchored triple containing no
Case-2 secondary.  The Case-2-anchored sibling theorem handles the omitted
role symmetrically. -/
theorem Case4WeightedCollisionResiduals.triple_fits_of_no_case2_secondary
    (hA : IsOneSeparated A)
    {Q : CommonCoherentRealizedSourceRows P W F.chart}
    (K : Case4WeightedCollisionResiduals Q)
    {s t u : Source P W} {v : Vertex A}
    (S : RealizedArrivalAt (F := F) Q.rows s v)
    (T : RealizedArrivalAt (F := F) Q.rows t v)
    (U : RealizedArrivalAt (F := F) Q.rows u v)
    (hsRole : S.target.role = .case4SplitRight)
    (htNot2 : T.target.role ≠ .case2Secondary)
    (huNot2 : U.target.role ≠ .case2Secondary)
    (htWindow : t.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (huWindow : u.1 ∈ Finset.univ.image (fun j : Fin 7 ↦
      (sevenShift P.next j (sourceIndex P W s.1 s.property)).1))
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    Fits ((unitDistanceGraph A).degree v)
      ((Q.rows s.1 s.property).localCase.tokens v +
        (Q.rows t.1 t.property).localCase.tokens v +
        (Q.rows u.1 u.property).localCase.tokens v) := by
  have hsHalf :=
    Erdos957Case4SplitClassification.RealizedArrivalAt.token_eq_one_of_case4SplitRight
      S hsRole
  have hdegree : (unitDistanceGraph A).degree v ≤ 5 := by
    rw [S.target.vertex_eq]
    exact S.target.target.degree_le_five
  by_cases ht4 : T.target.role = .case4SplitRight
  · have htHalf :=
      Erdos957Case4SplitClassification.RealizedArrivalAt.token_eq_one_of_case4SplitRight
        T ht4
    by_cases hu4 : U.target.role = .case4SplitRight
    · exact two_half_triple_fits_of_no_degree_five_three_halves
        S T U hsHalf htHalf hdegree
        (fun _huHalf hfive ↦ K.three_split_right_degree_five
          S T U hsRole ht4 hu4 hfive htWindow huWindow hst hsu htu)
    · have huDirect := direct_of_not_secondary_or_split huNot2 hu4
      exact two_half_triple_fits_of_no_degree_five_three_halves
        S T U hsHalf htHalf hdegree
        (fun huHalf hfive ↦ K.split_split_half_direct_degree_five
          S T U hsRole ht4 huDirect huHalf hfive htWindow huWindow
            hst hsu htu)
  · have htDirect := direct_of_not_secondary_or_split htNot2 ht4
    by_cases hu4 : U.target.role = .case4SplitRight
    · have huHalf :=
        Erdos957Case4SplitClassification.RealizedArrivalAt.token_eq_one_of_case4SplitRight
          U hu4
      have hfit := two_half_triple_fits_of_no_degree_five_three_halves
        S U T hsHalf huHalf hdegree
        (fun htHalf hfive ↦ K.split_split_half_direct_degree_five
          S U T hsRole hu4 htDirect htHalf hfive huWindow htWindow
            hsu hst htu.symm)
      unfold Fits at hfit ⊢
      omega
    · have huDirect := direct_of_not_secondary_or_split huNot2 hu4
      exact (Erdos957Case4CollisionLeaves.no_two_direct_competitors_of_split_right
        Q S.target T.target U.target hsRole htNot2 ht4 huNot2 hu4
          htWindow huWindow hst hsu htu).elim

end Erdos957Case4SplitClassification

#print axioms Erdos957Case4SplitClassification.eq_low_of_incident_partner_split_right_collision
#print axioms Erdos957Case4SplitClassification.incident_partner_split_right_associations_ne
#print axioms Erdos957Case4SplitClassification.same_association_split_right_reduces_to_distance_two
#print axioms Erdos957Case4SplitClassification.split_right_same_association_source_eq_in_window
