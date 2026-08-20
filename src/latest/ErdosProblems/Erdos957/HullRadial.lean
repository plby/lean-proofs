/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos957.HullEdge

/-!
# Radially sorted cyclic orders of a finite planar convex hull

This module retains the interior center used to sort the hull vertices by
polar argument.  It proves that the immediate cyclic successor in that sort
is the geometric gift-wrap successor, and hence supplies a genuine cyclic
hull order with a monotone once-around angular lift.
-/

open Set
open scoped EuclideanGeometry

namespace Erdos957

noncomputable section

theorem orientedTurn_eq_centerCross (p q C : Point) :
    orientedTurn p q C = crossVec (p - C) (q - C) := by
  simp [orientedTurn, crossVec]
  ring

/-- Cramer's rule in the oriented plane: a vector lying strictly between
two rays is a positive linear combination of their direction vectors. -/
theorem exists_pos_combo_of_crossVec_pos {a b z : Point}
    (hab : 0 < crossVec a b) (haz : 0 < crossVec a z)
    (hzb : 0 < crossVec z b) :
    ∃ α β : ℝ, 0 < α ∧ 0 < β ∧ z = α • a + β • b := by
  let α := crossVec z b / crossVec a b
  let β := crossVec a z / crossVec a b
  have hα : 0 < α := div_pos hzb hab
  have hβ : 0 < β := div_pos haz hab
  refine ⟨α, β, hα, hβ, ?_⟩
  ext i
  fin_cases i
  · change z 0 = α * a 0 + β * b 0
    dsimp only [α, β]
    field_simp [hab.ne']
    simp only [crossVec]
    ring
  · change z 1 = α * a 1 + β * b 1
    dsimp only [α, β]
    field_simp [hab.ne']
    simp only [crossVec]
    ring

/-- A direction in the open angular sector between `p-C` and `q-C` meets
the open chord `p q` on the same ray from `C`. -/
theorem exists_openSegment_sameRay_of_mem_openCCWSector
    {C p q x : Point} (hpC : p ≠ C) (hqC : q ≠ C) (hxC : x ≠ C)
    (hpqcross : 0 < crossVec (p - C) (q - C))
    (hxsector : InOpenCCWSector (pointComplexEquiv (p - C))
      (pointComplexEquiv (q - C)) (pointComplexEquiv (x - C))) :
    ∃ P ∈ openSegment ℝ p q, SameRay ℝ (P - C) (x - C) := by
  let zp := pointComplexEquiv (p - C)
  let zq := pointComplexEquiv (q - C)
  let zx := pointComplexEquiv (x - C)
  have hzp : zp ≠ 0 := by
    intro hzero
    have hsub : p - C ≠ 0 := fun h ↦ hpC (sub_eq_zero.mp h)
    apply hsub
    apply pointComplexEquiv.injective
    simpa [zp] using hzero
  have hzq : zq ≠ 0 := by
    intro hzero
    have hsub : q - C ≠ 0 := fun h ↦ hqC (sub_eq_zero.mp h)
    apply hsub
    apply pointComplexEquiv.injective
    simpa [zq] using hzero
  have hzx : zx ≠ 0 := by
    intro hzero
    have hsub : x - C ≠ 0 := fun h ↦ hxC (sub_eq_zero.mp h)
    apply hsub
    apply pointComplexEquiv.injective
    simpa [zx] using hzero
  have hcomplexCross : 0 < complexCross zp zq := by
    simpa only [zp, zq, complexCross_pointComplexEquiv, crossVec] using hpqcross
  have hdiff := ccwAngleDiff_mem_Ioo_of_complexCross_pos hcomplexCross
  have hcrosses := complexCross_pos_of_mem_openCCWSector hzp hzq hzx hdiff hxsector
  have hpzx : 0 < crossVec (p - C) (x - C) := by
    simpa only [zp, zx, complexCross_pointComplexEquiv, crossVec] using hcrosses.1
  have hxq : 0 < crossVec (x - C) (q - C) := by
    simpa only [zx, zq, complexCross_pointComplexEquiv, crossVec] using hcrosses.2
  obtain ⟨α, β, hα, hβ, hcombo⟩ :=
    exists_pos_combo_of_crossVec_pos hpqcross hpzx hxq
  let s := α + β
  have hs : 0 < s := add_pos hα hβ
  let t := β / s
  have ht0 : 0 < t := div_pos hβ hs
  have ht1 : t < 1 := (div_lt_one hs).mpr (by dsimp only [s]; linarith)
  let P : Point := (1 - t) • p + t • q
  have hPseg : P ∈ openSegment ℝ p q := by
    rw [openSegment_eq_image]
    exact ⟨t, ⟨ht0, ht1⟩, rfl⟩
  refine ⟨P, hPseg, ?_⟩
  have hPC : P - C = s⁻¹ • (x - C) := by
    rw [hcombo]
    ext i
    simp only [P, t, s, smul_eq_mul, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply]
    field_simp [hs.ne']
    ring
  rw [hPC]
  exact SameRay.sameRay_pos_smul_left _ (inv_pos.mpr hs)

/-- No third hull ray lies in the open counterclockwise sector cut out by a
gift-wrap edge. -/
theorem IsCCWNext.no_hullVertex_openCCWSector
    {A : Finset Point} {p q C x : Point}
    (hthree : 3 ≤ (hullVertices A).card) (hp : p ∈ hullVertices A)
    (hnext : IsCCWNext A p q)
    (hC : C ∈ interior (convexHull ℝ (A : Set Point)))
    (hx : x ∈ hullVertices A) (hxp : x ≠ p) (hxq : x ≠ q) :
    ¬ InOpenCCWSector (pointComplexEquiv (p - C))
      (pointComplexEquiv (q - C)) (pointComplexEquiv (x - C)) := by
  intro hxsector
  have hpC : p ≠ C := by
    intro hpCeq
    exact (hullVertex_mem_frontier A hp).2 (hpCeq ▸ hC)
  have hqC : q ≠ C := by
    intro hqCeq
    exact (hullVertex_mem_frontier A hnext.1).2 (hqCeq ▸ hC)
  have hxC : x ≠ C := by
    intro hxCeq
    exact (hullVertex_mem_frontier A hx).2 (hxCeq ▸ hC)
  have hpqcross : 0 < crossVec (p - C) (q - C) := by
    rw [← orientedTurn_eq_centerCross]
    exact hnext.turn_interior_pos hthree hp hC
  obtain ⟨P, hPopen, hPray⟩ :=
    exists_openSegment_sameRay_of_mem_openCCWSector hpC hqC hxC hpqcross hxsector
  have hpA : p ∈ A := hullVertices_subset A hp
  have hqA : q ∈ A := hullVertices_subset A hnext.1
  have hPfront : P ∈ frontier (convexHull ℝ (A : Set Point)) :=
    (hnext.2.1.segment_subset_frontier hpA hqA)
      (openSegment_subset_segment ℝ p q hPopen)
  have hxfront : x ∈ frontier (convexHull ℝ (A : Set Point)) :=
    hullVertex_mem_frontier A hx
  have hPx : P = x :=
    sameRay_frontier_eq (convex_convexHull ℝ (A : Set Point))
      (Set.Finite.isCompact_convexHull ℝ A.finite_toSet).isClosed hC
      hPfront hxfront hPray
  obtain ⟨-, l, -, hlpq, -, hlstrict⟩ := hnext.2.1
  have hlP : l P = l p := by
    rcases hPopen with ⟨a, b, -, -, hab, hP⟩
    rw [← hP, map_add, map_smul, map_smul, hlpq, ← add_smul, hab, one_smul]
  have hlx := hlstrict x hx hxp hxq
  rw [← hPx, hlP] at hlx
  exact (lt_irrefl _) hlx

theorem cyclicSucc_val {n : ℕ} (i : Fin n) :
    (cyclicSucc i).val = (i.val + 1) % n := by
  letI : NeZero n := i.neZero
  change (finRotate n i).val = _
  rw [finRotate_apply, Fin.val_add, Fin.val_one']
  nth_rw 1 [← Nat.mod_eq_of_lt i.isLt]
  exact (Nat.add_mod i.val 1 n).symm

theorem strictMono_cyclicSucc_between {n : ℕ} (hn : 2 ≤ n)
    {f : Fin n → ℝ} (hf : StrictMono f) (i j : Fin n)
    (hji : j ≠ i) (hjs : j ≠ cyclicSucc i) :
    if f i < f j then f i < f (cyclicSucc i) ∧ f (cyclicSucc i) < f j
    else f i < f (cyclicSucc i) ∨ f (cyclicSucc i) < f j := by
  have hnpos : 0 < n := by omega
  by_cases hi : i.val + 1 < n
  · have hsval : (cyclicSucc i).val = i.val + 1 := by
      rw [cyclicSucc_val, Nat.mod_eq_of_lt hi]
    have his : i < cyclicSucc i := by
      rw [Fin.lt_def, hsval]
      exact i.val.lt_succ_self
    have hfis : f i < f (cyclicSucc i) := hf his
    by_cases hij : i < j
    · rw [if_pos (hf hij)]
      refine ⟨hfis, hf ?_⟩
      rw [Fin.lt_def, hsval]
      have hijval : i.val < j.val := hij
      have hneval : i.val + 1 ≠ j.val := by
        intro h
        apply hjs
        apply Fin.ext
        rw [hsval]
        exact h.symm
      omega
    · have hji' : j < i := lt_of_le_of_ne (not_lt.mp hij) hji
      rw [if_neg (not_lt_of_ge (hf hji').le)]
      exact Or.inl hfis
  · have hilast : i.val + 1 = n := by omega
    have hsval : (cyclicSucc i).val = 0 := by
      rw [cyclicSucc_val, hilast, Nat.mod_self]
    have hji' : j < i := by
      rw [Fin.lt_def]
      have hjlt := j.isLt
      have hjne : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
      omega
    have hfji : f j < f i := hf hji'
    rw [if_neg (not_lt_of_ge hfji.le)]
    apply Or.inr
    apply hf
    rw [Fin.lt_def, hsval]
    have hjpos : 0 < j.val := by
      by_contra hjzero
      have hjzero' : j.val = 0 := Nat.eq_zero_of_not_pos hjzero
      apply hjs
      apply Fin.ext
      rw [hsval]
      exact hjzero'
    exact hjpos

theorem angleSorted_cyclicSucc_mem_openCCWSector {n : ℕ} (hn : 2 ≤ n)
    {C : Point} {v : Fin n → Point}
    (hsorted : ∀ i j, i < j → centerAngle C (v i) < centerAngle C (v j))
    (i j : Fin n) (hji : j ≠ i) (hjs : j ≠ cyclicSucc i) :
    InOpenCCWSector (pointComplexEquiv (v i - C))
      (pointComplexEquiv (v j - C)) (pointComplexEquiv (v (cyclicSucc i) - C)) := by
  change if centerAngle C (v i) < centerAngle C (v j) then
      centerAngle C (v i) < centerAngle C (v (cyclicSucc i)) ∧
        centerAngle C (v (cyclicSucc i)) < centerAngle C (v j)
    else centerAngle C (v i) < centerAngle C (v (cyclicSucc i)) ∨
      centerAngle C (v (cyclicSucc i)) < centerAngle C (v j)
  exact strictMono_cyclicSucc_between hn (fun _ _ hij ↦ hsorted _ _ hij) i j hji hjs

theorem cyclicSucc_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    cyclicSucc i ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  by_cases hi : i.val + 1 < n
  · have hsval : (cyclicSucc i).val = i.val + 1 := by
      rw [cyclicSucc_val, Nat.mod_eq_of_lt hi]
    rw [hsval] at hval
    omega
  · have hilast : i.val + 1 = n := by omega
    have hsval : (cyclicSucc i).val = 0 := by
      rw [cyclicSucc_val, hilast, Nat.mod_self]
    rw [hsval] at hval
    omega

theorem cyclicSucc_cyclicSucc_ne_self {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    cyclicSucc (cyclicSucc i) ≠ i := by
  intro h
  have hval := congrArg Fin.val h
  by_cases hi : i.val + 1 < n
  · have hsval : (cyclicSucc i).val = i.val + 1 := by
      rw [cyclicSucc_val, Nat.mod_eq_of_lt hi]
    by_cases hi2 : i.val + 2 < n
    · have hssval : (cyclicSucc (cyclicSucc i)).val = i.val + 2 := by
        rw [cyclicSucc_val, hsval]
        rw [Nat.mod_eq_of_lt (by omega)]
      rw [hssval] at hval
      omega
    · have hi2last : i.val + 2 = n := by omega
      have hssval : (cyclicSucc (cyclicSucc i)).val = 0 := by
        rw [cyclicSucc_val, hsval, hi2last, Nat.mod_self]
      rw [hssval] at hval
      omega
  · have hilast : i.val + 1 = n := by omega
    have hsval : (cyclicSucc i).val = 0 := by
      rw [cyclicSucc_val, hilast, Nat.mod_self]
    have hssval : (cyclicSucc (cyclicSucc i)).val = 1 := by
      rw [cyclicSucc_val, hsval, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hssval] at hval
    omega

/-- In the exact angular sort around an interior center, the geometric
gift-wrap successor is the immediate cyclic `Fin` successor. -/
theorem ccwNextVertex_eq_angleSorted_cyclicSucc
    (A : Finset Point) (hthree : 3 ≤ (hullVertices A).card)
    {C : Point} (hC : C ∈ interior (convexHull ℝ (A : Set Point)))
    (v : Fin (hullVertexCount A) ↪ Point)
    (hrange : Set.range v = (hullVertices A : Set Point))
    (hsorted : ∀ i j, i < j → centerAngle C (v i) < centerAngle C (v j))
    (i : Fin (hullVertexCount A)) :
    ccwNextVertex A hthree ⟨v i, by
      change v i ∈ (hullVertices A : Set Point)
      have : v i ∈ Set.range v := ⟨i, rfl⟩
      simpa only [hrange] using this⟩ =
      ⟨v (cyclicSucc i), by
        change v (cyclicSucc i) ∈ (hullVertices A : Set Point)
        have : v (cyclicSucc i) ∈ Set.range v := ⟨cyclicSucc i, rfl⟩
        simpa only [hrange] using this⟩ := by
  let p : hullVertices A := ⟨v i, by
    change v i ∈ (hullVertices A : Set Point)
    have : v i ∈ Set.range v := ⟨i, rfl⟩
    simpa only [hrange] using this⟩
  let q : hullVertices A := ccwNextVertex A hthree p
  have hqrange : (q : Point) ∈ Set.range v := by
    rw [hrange]
    exact q.property
  obtain ⟨j, hj⟩ := hqrange
  apply Subtype.ext
  change (q : Point) = v (cyclicSucc i)
  by_contra hqsucc
  have hn2 : 2 ≤ hullVertexCount A := by
    change 2 ≤ (hullVertices A).card
    omega
  have hji : j ≠ i := by
    intro hji
    subst j
    have hnextne := (ccwNextVertex_spec A hthree p).2.1.1
    apply hnextne
    simpa [p, q] using hj
  have hjs : j ≠ cyclicSucc i := by
    intro hjs
    subst j
    exact hqsucc (by simpa [q] using hj.symm)
  have hsector :=
    angleSorted_cyclicSucc_mem_openCCWSector hn2 hsorted i j hji hjs
  have hisucc : cyclicSucc i ≠ i := cyclicSucc_ne_self hn2 i
  have hvsuccp : v (cyclicSucc i) ≠ (p : Point) := by
    intro h
    apply hisucc
    apply v.injective
    simpa [p] using h
  have hvsuccq : v (cyclicSucc i) ≠ (q : Point) := fun h ↦ hqsucc h.symm
  have hnot := (ccwNextVertex_spec A hthree p).no_hullVertex_openCCWSector
    hthree p.property hC
    (x := v (cyclicSucc i))
    (by
      change v (cyclicSucc i) ∈ (hullVertices A : Set Point)
      have : v (cyclicSucc i) ∈ Set.range v := ⟨cyclicSucc i, rfl⟩
      simpa only [hrange] using this)
    hvsuccp hvsuccq
  apply hnot
  simpa [p, q, hj] using hsector

/-- A nonzero linear functional which is bounded above on the hull is
strictly below that bound at every interior point. -/
theorem linear_support_lt_at_interior {A : Finset Point}
    {l : Point →L[ℝ] ℝ} {x C : Point} (hl : l ≠ 0)
    (hmax : ∀ y ∈ A, l y ≤ l x)
    (hC : C ∈ interior (convexHull ℝ (A : Set Point))) :
    l C < l x := by
  have hhalfConvex : Convex ℝ {y : Point | l y ≤ l x} :=
    (convex_Iic (l x)).linear_preimage l.toLinearMap
  have hhull : convexHull ℝ (A : Set Point) ⊆ {y : Point | l y ≤ l x} :=
    convexHull_min hmax hhalfConvex
  have hsurj : Function.Surjective l := by
    have hex : ∃ v : Point, l v ≠ 0 := by
      by_contra h
      push Not at h
      apply hl
      ext v
      simpa using h v
    obtain ⟨v, hv⟩ := hex
    intro t
    refine ⟨(t / l v) • v, ?_⟩
    simp [hv]
  have hinterior :
      interior {y : Point | l y ≤ l x} = {y : Point | l y < l x} := by
    change interior (l ⁻¹' Set.Iic (l x)) = l ⁻¹' Set.Iio (l x)
    rw [l.interior_preimage hsurj, interior_Iic]
  have := interior_mono hhull hC
  rwa [hinterior] at this

/-- If a third hull ray lies strictly between two hull rays spanning less
than a half-turn, convex extremality puts the third vertex strictly outside
their chord.  Equivalently, the three vertices have positive cyclic turn. -/
theorem orientedTurn_pos_of_hullVertex_mem_openCCWSector
    (A : Finset Point) {C a b x : Point}
    (hC : C ∈ interior (convexHull ℝ (A : Set Point)))
    (ha : a ∈ hullVertices A) (hb : b ∈ hullVertices A)
    (hx : x ∈ hullVertices A) (hab : a ≠ b) (hax : a ≠ x)
    (hbx : b ≠ x) (habCross : 0 < crossVec (a - C) (b - C))
    (hxsector : InOpenCCWSector (pointComplexEquiv (a - C))
      (pointComplexEquiv (b - C)) (pointComplexEquiv (x - C))) :
    0 < orientedTurn a x b := by
  have haC : a ≠ C := by
    intro h
    exact (hullVertex_mem_frontier A ha).2 (h ▸ hC)
  have hbC : b ≠ C := by
    intro h
    exact (hullVertex_mem_frontier A hb).2 (h ▸ hC)
  have hxC : x ≠ C := by
    intro h
    exact (hullVertex_mem_frontier A hx).2 (h ▸ hC)
  obtain ⟨P, hPopen, hPray⟩ :=
    exists_openSegment_sameRay_of_mem_openCCWSector
      haC hbC hxC habCross hxsector
  rcases hPopen with ⟨r, s, hr, hs, hrs, hP⟩
  obtain ⟨l, hle, hlt⟩ := hullVertex_exists_strict_support A hx
  have hla : l a < l x := hlt a (hullVertices_subset A ha) hax
  have hlb : l b < l x := hlt b (hullVertices_subset A hb) hbx
  have hlne : l ≠ 0 := by
    intro hlzero
    have := hla
    simp [hlzero] at this
  have hlC : l C < l x := linear_support_lt_at_interior hlne hle hC
  have hlP : l P < l x := by
    rw [← hP, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    calc
      r * l a + s * l b < r * l x + s * l x :=
        add_lt_add (mul_lt_mul_of_pos_left hla hr)
          (mul_lt_mul_of_pos_left hlb hs)
      _ = l x := by rw [← add_mul, hrs, one_mul]
  obtain ⟨t, ht, htEq⟩ :=
    hPray.exists_nonneg_right (sub_ne_zero.mpr hxC)
  have hlEq : l P - l C = t * (l x - l C) := by
    have h := congrArg l htEq
    simpa only [map_sub, map_smul, smul_eq_mul] using h
  have htlt : t < 1 := by
    nlinarith
  have hrEq : r = 1 - s := by linarith
  have hPline : P = a + s • (b - a) := by
    rw [← hP, hrEq]
    module
  have hturnP : orientedTurn a b P = 0 := by
    rw [hPline]
    simp only [orientedTurn, smul_eq_mul, PiLp.add_apply, PiLp.smul_apply,
      PiLp.sub_apply]
    ring
  have hpAffine : P = (1 - t) • C + t • x := by
    ext i
    have hi := congrArg (fun z : Point ↦ z i) htEq
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.add_apply] at hi ⊢
    linarith
  have hturnAffine :
      orientedTurn a b P =
        (1 - t) * orientedTurn a b C + t * orientedTurn a b x := by
    rw [hpAffine]
    simp only [orientedTurn, smul_eq_mul, PiLp.add_apply, PiLp.smul_apply]
    ring
  have hturnC : 0 < orientedTurn a b C := by
    rwa [orientedTurn_eq_centerCross]
  have htpos : 0 < t := by
    rcases ht.eq_or_lt with rfl | htpos
    · simp only [zero_mul, add_zero, one_mul] at hturnAffine
      rw [hturnP] at hturnAffine
      linarith
    · exact htpos
  have hturnX : orientedTurn a b x < 0 := by
    rw [hturnP] at hturnAffine
    nlinarith
  rw [orientedTurn_swap_last]
  linarith

theorem orientedTurn_rotate (p q r : Point) :
    orientedTurn q r p = orientedTurn p q r := by
  simp only [orientedTurn]
  ring

theorem orientedTurn_swap_first (p q r : Point) :
    orientedTurn q p r = -orientedTurn p q r := by
  simp only [orientedTurn]
  ring

theorem orientedTurn_eq_centerCross_sum (C p q r : Point) :
    orientedTurn p q r =
      crossVec (p - C) (q - C) + crossVec (q - C) (r - C) +
        crossVec (r - C) (p - C) := by
  simp only [orientedTurn, crossVec, PiLp.sub_apply]
  ring

theorem crossVec_swap (u v : Point) : crossVec v u = -crossVec u v := by
  simp only [crossVec]
  ring

/-- A cyclic hull order together with the interior center whose ordinary
`Fin` enumeration is strictly sorted by polar argument. -/
structure RadiallySortedCyclicHullOrder (A : Finset Point) where
  center : Point
  center_mem_interior : center ∈ interior (convexHull ℝ (A : Set Point))
  order : CyclicHullOrder A
  angle_strictMono : StrictMono (fun i ↦ centerAngle center (order.vertex i))

theorem exists_radiallySortedCyclicHullOrder (A : Finset Point)
    (hthree : 3 ≤ (hullVertices A).card) :
    Nonempty (RadiallySortedCyclicHullOrder A) := by
  obtain ⟨C, hC⟩ := convexHull_interior_nonempty_of_three_le_hullVertices A hthree
  obtain ⟨v, hrange, hsorted⟩ := exists_angleSorted_hullVertexEmbedding A hC
  have hv : ∀ i : Fin (hullVertexCount A), v i ∈ hullVertices A := by
    intro i
    change v i ∈ (hullVertices A : Set Point)
    rw [← hrange]
    exact ⟨i, rfl⟩
  let w : Fin (hullVertexCount A) → hullVertices A := fun i ↦ ⟨v i, hv i⟩
  have hnext : ∀ i, ccwNextVertex A hthree (w i) = w (cyclicSucc i) := by
    intro i
    simpa only [w] using
      ccwNextVertex_eq_angleSorted_cyclicSucc A hthree hC v hrange hsorted i
  have hn2 : 2 ≤ hullVertexCount A := by
    change 2 ≤ (hullVertices A).card
    omega
  let P : CyclicHullOrder A := {
    vertex := v
    range_vertex := hrange
    edge_support := fun i ↦ by
      have hs := ccwNextVertex_spec A hthree (w i)
      rw [hnext i] at hs
      exact hs.2.1
    strict_turn := fun i ↦ by
      have hs := ccwNextVertex_spec A hthree (w i)
      rw [hnext i] at hs
      have hrp : v (cyclicSucc (cyclicSucc i)) ≠ v i := by
        intro h
        exact cyclicSucc_cyclicSucc_ne_self hthree i (v.injective h)
      have hrq : v (cyclicSucc (cyclicSucc i)) ≠ v (cyclicSucc i) := by
        intro h
        exact cyclicSucc_ne_self hn2 (cyclicSucc i) (v.injective h)
      exact hs.2.2 _ (hv _) hrp hrq }
  refine ⟨⟨C, hC, P, ?_⟩⟩
  intro i j hij
  exact hsorted i j hij

namespace RadiallySortedCyclicHullOrder

variable {A : Finset Point} (R : RadiallySortedCyclicHullOrder A)

/-- Any three vertices in increasing ordinary `Fin` order make a strictly
positive counterclockwise turn. -/
theorem orientedTurn_pos_of_lt {i j k : Fin (hullVertexCount A)}
    (hij : i < j) (hjk : j < k) :
    0 < orientedTurn (R.order.vertex i) (R.order.vertex j)
      (R.order.vertex k) := by
  let u := R.order.vertex i
  let v := R.order.vertex j
  let w := R.order.vertex k
  have hui : u ∈ hullVertices A := R.order.vertex_mem_hullVertices i
  have hvj : v ∈ hullVertices A := R.order.vertex_mem_hullVertices j
  have hwk : w ∈ hullVertices A := R.order.vertex_mem_hullVertices k
  have huv : u ≠ v := by
    intro h
    exact (ne_of_lt hij) (R.order.vertex.injective h)
  have hvw : v ≠ w := by
    intro h
    exact (ne_of_lt hjk) (R.order.vertex.injective h)
  have huw : u ≠ w := by
    intro h
    exact (ne_of_lt (hij.trans hjk)) (R.order.vertex.injective h)
  have hangUV : centerAngle R.center u < centerAngle R.center v :=
    R.angle_strictMono hij
  have hangVW : centerAngle R.center v < centerAngle R.center w :=
    R.angle_strictMono hjk
  have hangUW : centerAngle R.center u < centerAngle R.center w :=
    hangUV.trans hangVW
  by_cases hUW : 0 < crossVec (u - R.center) (w - R.center)
  · apply orientedTurn_pos_of_hullVertex_mem_openCCWSector A
      R.center_mem_interior hui hwk hvj huw huv hvw.symm hUW
    change if centerAngle R.center u < centerAngle R.center w then
        centerAngle R.center u < centerAngle R.center v ∧
          centerAngle R.center v < centerAngle R.center w
      else centerAngle R.center u < centerAngle R.center v ∨
        centerAngle R.center v < centerAngle R.center w
    rw [if_pos hangUW]
    exact ⟨hangUV, hangVW⟩
  · by_cases hVU : 0 < crossVec (v - R.center) (u - R.center)
    · rw [← orientedTurn_rotate]
      apply orientedTurn_pos_of_hullVertex_mem_openCCWSector A
        R.center_mem_interior hvj hui hwk huv.symm hvw huw hVU
      change if centerAngle R.center v < centerAngle R.center u then
          centerAngle R.center v < centerAngle R.center w ∧
            centerAngle R.center w < centerAngle R.center u
        else centerAngle R.center v < centerAngle R.center w ∨
          centerAngle R.center w < centerAngle R.center u
      rw [if_neg (not_lt_of_ge hangUV.le)]
      exact Or.inl hangVW
    · by_cases hWV : 0 < crossVec (w - R.center) (v - R.center)
      · rw [orientedTurn_rotate]
        apply orientedTurn_pos_of_hullVertex_mem_openCCWSector A
          R.center_mem_interior hwk hvj hui hvw.symm huw.symm huv.symm hWV
        change if centerAngle R.center w < centerAngle R.center v then
            centerAngle R.center w < centerAngle R.center u ∧
              centerAngle R.center u < centerAngle R.center v
          else centerAngle R.center w < centerAngle R.center u ∨
            centerAngle R.center u < centerAngle R.center v
        rw [if_neg (not_lt_of_ge hangVW.le)]
        exact Or.inr hangUV
      · have hUVnonneg : 0 ≤ crossVec (u - R.center) (v - R.center) := by
          have h := not_lt.mp hVU
          rw [crossVec_swap] at h
          linarith
        have hVWnonneg : 0 ≤ crossVec (v - R.center) (w - R.center) := by
          have h := not_lt.mp hWV
          rw [crossVec_swap] at h
          linarith
        have hWUnonneg : 0 ≤ crossVec (w - R.center) (u - R.center) := by
          have h := not_lt.mp hUW
          rw [crossVec_swap] at h
          linarith
        have hturnNonneg : 0 ≤ orientedTurn u v w := by
          rw [orientedTurn_eq_centerCross_sum]
          positivity
        have hnotcol := hullVertices_not_collinear_three A
          hui hvj hwk huv hvw huw
        have hturnNe : orientedTurn u v w ≠ 0 := by
          intro hzero
          apply hnotcol
          apply collinear_of_crossVec_sub_eq_zero huv
          rw [← orientedTurn_eq_crossVec]
          exact hzero
        exact lt_of_le_of_ne hturnNonneg (Ne.symm hturnNe)

/-- `j` lies strictly on the counterclockwise cyclic `Fin` arc from `i` to
`k`.  The second branch is precisely the wrap-around case. -/
def InOpenCCWArc {n : ℕ} (i j k : Fin n) : Prop :=
  if i < k then i < j ∧ j < k else i < j ∨ j < k

/-- The closed counterclockwise cyclic `Fin` arc, including both chord
endpoints. -/
def InClosedCCWArc {n : ℕ} (i j k : Fin n) : Prop :=
  if i ≤ k then i ≤ j ∧ j ≤ k else i ≤ j ∨ j ≤ k

/-- Cyclic interval membership is equivalently comparison of the two
bounded forward offsets from the initial index. -/
theorem inClosedCCWArc_iff_sub_val_le {n : ℕ} (i j k : Fin n) :
    InClosedCCWArc i j k ↔ (j - i).val ≤ (k - i).val := by
  unfold InClosedCCWArc
  split <;> fin_omega

/-- The increasing-triple theorem in a rotation-invariant cyclic form. -/
theorem orientedTurn_pos_of_mem_openCCWArc
    {i j k : Fin (hullVertexCount A)} (hik : i ≠ k)
    (hj : InOpenCCWArc i j k) :
    0 < orientedTurn (R.order.vertex i) (R.order.vertex j)
      (R.order.vertex k) := by
  unfold InOpenCCWArc at hj
  by_cases hiklt : i < k
  · rw [if_pos hiklt] at hj
    exact R.orientedTurn_pos_of_lt hj.1 hj.2
  · rw [if_neg hiklt] at hj
    have hki : k < i := lt_of_le_of_ne (not_lt.mp hiklt) hik.symm
    rcases hj with hij | hjk
    · rw [orientedTurn_rotate (R.order.vertex k) (R.order.vertex i)
        (R.order.vertex j)]
      exact R.orientedTurn_pos_of_lt hki hij
    · rw [← orientedTurn_rotate (R.order.vertex i) (R.order.vertex j)
        (R.order.vertex k)]
      exact R.orientedTurn_pos_of_lt hjk hki

/-- A vertex on the forward open arc from `i` to `k` is strictly on the
right side of the directed chord `i → k` in ambient coordinates. -/
theorem orientedTurn_chord_lt_zero_of_mem_openCCWArc
    {i j k : Fin (hullVertexCount A)} (hik : i ≠ k)
    (hj : InOpenCCWArc i j k) :
    orientedTurn (R.order.vertex i) (R.order.vertex k)
      (R.order.vertex j) < 0 := by
  have hturn := R.orientedTurn_pos_of_mem_openCCWArc hik hj
  rw [orientedTurn_swap_last] at hturn
  linarith

/-- Closed-arc version of the ambient chord-side theorem.  Equality occurs
exactly at a chord endpoint; every strict intermediate vertex has negative
turn by the preceding theorem. -/
theorem orientedTurn_chord_le_zero_of_mem_closedCCWArc
    {i j k : Fin (hullVertexCount A)} (hj : InClosedCCWArc i j k) :
    orientedTurn (R.order.vertex i) (R.order.vertex k)
      (R.order.vertex j) ≤ 0 := by
  by_cases hik : i = k
  · subst k
    simp [orientedTurn]
  by_cases hji : j = i
  · subst j
    simp only [orientedTurn]
    ring_nf
    exact le_rfl
  by_cases hjk : j = k
  · subst j
    simp [orientedTurn]
  apply (R.orientedTurn_chord_lt_zero_of_mem_openCCWArc hik ?_).le
  unfold InClosedCCWArc at hj
  unfold InOpenCCWArc
  by_cases hiklt : i < k
  · rw [if_pos hiklt.le] at hj
    rw [if_pos hiklt]
    exact ⟨lt_of_le_of_ne hj.1 (Ne.symm hji), lt_of_le_of_ne hj.2 hjk⟩
  · have hkile : k ≤ i := not_lt.mp hiklt
    have hkile' : ¬ i ≤ k := not_le.mpr (lt_of_le_of_ne hkile (Ne.symm hik))
    rw [if_neg hkile'] at hj
    rw [if_neg hiklt]
    rcases hj with hij | hjk'
    · exact Or.inl (lt_of_le_of_ne hij (Ne.symm hji))
    · exact Or.inr (lt_of_le_of_ne hjk' hjk)

/-- Equivalently, reversing the chord gives the nonnegative-sign convention
used after the orientation-reversing local coordinate chart. -/
theorem orientedTurn_reverse_chord_pos_of_mem_openCCWArc
    {i j k : Fin (hullVertexCount A)} (hik : i ≠ k)
    (hj : InOpenCCWArc i j k) :
    0 < orientedTurn (R.order.vertex k) (R.order.vertex i)
      (R.order.vertex j) := by
  have hturn := R.orientedTurn_chord_lt_zero_of_mem_openCCWArc hik hj
  rw [orientedTurn_swap_first]
  linarith

/-- A vertex on the complementary open arc is strictly on the left side of
the original directed chord. -/
theorem orientedTurn_chord_pos_of_mem_complementaryArc
    {i j k : Fin (hullVertexCount A)} (hik : i ≠ k)
    (hj : InOpenCCWArc k j i) :
    0 < orientedTurn (R.order.vertex i) (R.order.vertex k)
      (R.order.vertex j) := by
  have hturn := R.orientedTurn_pos_of_mem_openCCWArc hik.symm hj
  rw [orientedTurn_rotate] at hturn
  exact hturn

end RadiallySortedCyclicHullOrder

end

end Erdos957
