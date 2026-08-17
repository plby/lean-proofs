import ErdosProblems.Erdos215.RationalLattice

/-!
# Framed lines and finite-line avoidance

This file packages the elementary plane geometry used when constructing the
candidate pools in the Jackson--Mauldin argument.  Lines are recorded in the
coordinates of a fixed oriented frame.  This makes both the rational-distance
line lemma and the integer-slope avoidance argument independent of affine-map
bookkeeping.
-/

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos215

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- Two points have rational squared distance. -/
def HasRationalSqDist (x y : Point) : Prop :=
  ∃ q : ℚ, distSq x y = (q : ℝ)

/-- An affine line, expressed in the coordinates of the frame `L`. -/
structure FramedLine (L : OrientedFrame) where
  point : Point
  direction : Point
  direction_ne : direction ≠ 0

namespace FramedLine

variable {L : OrientedFrame}

/-- The ambient carrier of a line recorded in `L`-coordinates. -/
def carrier (line : FramedLine L) : Set Point :=
  {x | L.toCoords x ∈ affineLine line.point line.direction}

end FramedLine

/-- Passing to frame coordinates preserves squared distance. -/
lemma OrientedFrame.distSq_toCoords (L : OrientedFrame) (p q : Point) :
    distSq (L.toCoords p) (L.toCoords q) = distSq p q := by
  simpa only [L.fromCoords_toCoords] using
    (L.distSq_fromCoords (L.toCoords p) (L.toCoords q)).symm

/-- In a fixed frame, rational points at rational squared distance from an
irrational point lie on one framed affine line. -/
theorem framed_rational_sqDist_line {L : OrientedFrame} {c : Point}
    (hc : ¬L.IsRational c) :
    ∃ line : FramedLine L, ∀ z : Point,
      L.IsRational z → HasRationalSqDist c z → z ∈ line.carrier := by
  have hc' : ¬IsStandardRational (L.toCoords c) := by
    intro h
    apply hc
    rcases h with ⟨q, hq⟩
    exact (L.isRational_iff_toCoords c).2 ⟨q, hq⟩
  obtain ⟨p, v, hv, hline⟩ := rational_sqDist_subset_line hc'
  refine ⟨⟨p, v, hv⟩, ?_⟩
  intro z hz ⟨r, hr⟩
  apply hline
  constructor
  · rcases (L.isRational_iff_toCoords z).1 hz with ⟨q, hq⟩
    exact ⟨q, hq⟩
  · refine ⟨r, ?_⟩
    rw [L.distSq_toCoords, distSq_comm, hr]

/-- Every point in a rational translate has rational coordinates in its
frame. -/
theorem isRational_of_mem_rationalTranslate {L : OrientedFrame}
    {q : RatPoint} {x : Point} (hx : x ∈ L.rationalTranslate q) :
    L.IsRational x := by
  rcases hx with ⟨z, rfl⟩
  let r : RatPoint := fun i ↦ q i + z i
  refine ⟨r, ?_⟩
  apply congrArg L.fromCoords
  ext i
  simp [r, ratPoint, intPoint]

/-- Two points rational in the same frame have rational squared distance. -/
theorem hasRationalSqDist_of_isRational {L : OrientedFrame} {x y : Point}
    (hx : L.IsRational x) (hy : L.IsRational y) :
    HasRationalSqDist x y := by
  rcases hx with ⟨q, rfl⟩
  rcases hy with ⟨r, rfl⟩
  refine ⟨(q 0 - r 0) ^ 2 + (q 1 - r 1) ^ 2, ?_⟩
  rw [L.distSq_fromCoords]
  simp [distSq, Fin.sum_univ_two, ratPoint]

/-- Two points in the same rational translate have integral squared
distance. -/
theorem exists_int_distSq_of_mem_rationalTranslate {L : OrientedFrame}
    {q : RatPoint} {x y : Point}
    (hx : x ∈ L.rationalTranslate q)
    (hy : y ∈ L.rationalTranslate q) :
    ∃ n : ℤ, distSq x y = (n : ℝ) := by
  rcases hx with ⟨z, rfl⟩
  rcases hy with ⟨w, rfl⟩
  refine ⟨intDistSq z w, ?_⟩
  rw [L.distSq_fromCoords]
  simp [distSq, intDistSq, Fin.sum_univ_two, ratPoint, intPoint]

/-- One rank-two residue sublattice in the coordinates of `L`. -/
def FramedResidueSet (L : OrientedFrame) (d : ℕ) (i j : Fin d)
    (a b : ℤ) : Set Point :=
  {x | ∃ k l : ℤ,
    x = L.fromCoords
      (ratPoint (fun r ↦ if r = 0 then (i : ℕ) / d + k else (j : ℕ) / d + l)) ∧
    a ≡ k [ZMOD d] ∧ b ≡ l [ZMOD d]}

/-- An arithmetic progression in a direction not parallel to a line meets
that line in at most one parameter. -/
lemma affineLine_integer_progression_subsingleton
    {base direction p v : Point} (hnonparallel : det₂ direction v ≠ 0) :
    {m : ℤ | base + (m : ℝ) • direction ∈ affineLine p v}.Subsingleton := by
  intro m hm n hn
  obtain ⟨s, hs⟩ := hm
  obtain ⟨t, ht⟩ := hn
  by_contra hmn
  have hmnR : (m : ℝ) - (n : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (Int.cast_injective.ne hmn)
  have hs0 := congrArg (fun x : Point ↦ x 0) hs
  have hs1 := congrArg (fun x : Point ↦ x 1) hs
  have ht0 := congrArg (fun x : Point ↦ x 0) ht
  have ht1 := congrArg (fun x : Point ↦ x 1) ht
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hs0 hs1 ht0 ht1
  have h0 : ((m : ℝ) - (n : ℝ)) * direction 0 = (s - t) * v 0 := by
    linarith
  have h1 : ((m : ℝ) - (n : ℝ)) * direction 1 = (s - t) * v 1 := by
    linarith
  apply hnonparallel
  apply (mul_eq_zero.mp ?_).resolve_left hmnR
  calc
    ((m : ℝ) - (n : ℝ)) * det₂ direction v =
        (((m : ℝ) - (n : ℝ)) * direction 0) * v 1 -
          (((m : ℝ) - (n : ℝ)) * direction 1) * v 0 := by
            simp only [det₂]
            ring
    _ = ((s - t) * v 0) * v 1 - ((s - t) * v 1) * v 0 := by
      rw [h0, h1]
    _ = 0 := by ring

/-- There is an integer slope not parallel to any member of a finite family
of framed lines. -/
lemma exists_integerSlope_nonparallel {L : OrientedFrame}
    (G : Finset (FramedLine L)) :
    ∃ T : ℤ, ∀ line ∈ G,
      line.direction 1 - (T : ℝ) * line.direction 0 ≠ 0 := by
  let bad : Set ℤ := ⋃ line : {line // line ∈ G},
    {T : ℤ | (T : ℝ) * line.1.direction 0 = line.1.direction 1}
  have hsingle : ∀ line : {line // line ∈ G},
      {T : ℤ | (T : ℝ) * line.1.direction 0 =
        line.1.direction 1}.Subsingleton := by
    intro line m hm n hn
    have hv0 : line.1.direction 0 ≠ 0 := by
      intro hv0
      have hv1 : line.1.direction 1 = 0 := by
        simpa only [hv0, mul_zero] using hm.symm
      apply line.1.direction_ne
      ext r
      fin_cases r
      · simpa using hv0
      · simpa using hv1
    have hcast : (m : ℝ) = (n : ℝ) := by
      apply (mul_right_cancel₀ hv0)
      exact hm.trans hn.symm
    exact_mod_cast hcast
  have hbad : bad.Finite := by
    apply Set.finite_iUnion
    intro line
    exact (hsingle line).finite
  obtain ⟨T, -, hT⟩ := (Set.infinite_univ : (Set.univ : Set ℤ).Infinite).exists_notMem_finite hbad
  refine ⟨T, ?_⟩
  intro line hline hzero
  apply hT
  apply mem_iUnion.2
  refine ⟨⟨line, hline⟩, ?_⟩
  exact (sub_eq_zero.mp hzero).symm

/-- A rank-two residue sublattice still has infinitely many points after
removing a finite exceptional set and finitely many framed affine lines.

This is the exact robust form needed for pool richness: the exceptional set
can be the finitely many rational points outside a Davies layer. -/
theorem framedResidueSet_infinite_avoid {L : OrientedFrame}
    {d : ℕ} (hd : d ≠ 0) (i j : Fin d) (a b : ℤ)
    (G : Finset (FramedLine L)) {E : Set Point} (hE : E.Finite) :
    Set.Infinite {x : Point |
      x ∈ FramedResidueSet L d i j a b ∧ x ∉ E ∧
        ∀ line ∈ G, x ∉ line.carrier} := by
  obtain ⟨T, hT⟩ := exists_integerSlope_nonparallel G
  let q : ℤ → RatPoint := fun m r ↦
    if r = 0 then (i : ℕ) / d + (a + d * m : ℤ)
    else (j : ℕ) / d + (b + d * T * m : ℤ)
  let base : Point := ratPoint (fun r ↦
    if r = 0 then (i : ℕ) / d + a else (j : ℕ) / d + b)
  let direction : Point := WithLp.toLp 2 fun r ↦
    if r = 0 then (d : ℝ) else (d : ℝ) * (T : ℝ)
  let coord : ℤ → Point := fun m ↦ base + (m : ℝ) • direction
  let f : ℤ → Point := fun m ↦ L.fromCoords (coord m)
  have hcoord (m : ℤ) : coord m = ratPoint (q m) := by
    ext r
    fin_cases r
    · simp [coord, base, direction, q, ratPoint]
      ring
    · simp [coord, base, direction, q, ratPoint]
      ring
  have hf : Function.Injective f := by
    intro m n hmn
    have hc : coord m = coord n := L.fromCoords_injective hmn
    have hc0 := congrArg (fun x : Point ↦ x 0) hc
    simp [coord, direction] at hc0
    rcases hc0 with hmn | hd0
    · exact hmn
    · exact (hd hd0).elim
  have hnonparallel (line : FramedLine L) (hline : line ∈ G) :
      det₂ direction line.direction ≠ 0 := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    have hslope := hT line hline
    rw [show det₂ direction line.direction =
        (d : ℝ) * (line.direction 1 - (T : ℝ) * line.direction 0) by
      simp [det₂, direction]
      ring]
    exact mul_ne_zero hdR hslope
  let badLines : Set ℤ := ⋃ line : {line // line ∈ G},
    {m : ℤ | f m ∈ line.1.carrier}
  have hbadLines : badLines.Finite := by
    apply Set.finite_iUnion
    intro line
    apply (affineLine_integer_progression_subsingleton
      (hnonparallel line.1 line.2)).finite.subset
    intro m hm
    change L.toCoords (L.fromCoords (coord m)) ∈
      affineLine line.1.point line.1.direction at hm
    change coord m ∈ affineLine line.1.point line.1.direction
    simpa only [L.toCoords_fromCoords] using hm
  let bad : Set ℤ := f ⁻¹' E ∪ badLines
  have hbad : bad.Finite := by
    apply Set.Finite.union
    · exact hE.preimage hf.injOn
    · exact hbadLines
  have hgood : (Set.univ \ bad).Infinite :=
    Set.infinite_univ.sdiff hbad
  have himage : (f '' (Set.univ \ bad)).Infinite :=
    hgood.image hf.injOn
  apply himage.mono
  intro x hx
  rcases hx with ⟨m, hm, rfl⟩
  have hmE : f m ∉ E := by
    intro hfm
    exact hm.2 (Or.inl hfm)
  have hmLines : ∀ line ∈ G, f m ∉ line.carrier := by
    intro line hline hmline
    apply hm.2
    apply Or.inr
    apply mem_iUnion.2
    exact ⟨⟨line, hline⟩, hmline⟩
  refine ⟨?_, hmE, hmLines⟩
  refine ⟨a + d * m, b + d * T * m, ?_, ?_, ?_⟩
  · rw [← hcoord]
  · exact Int.modEq_iff_dvd.2 ⟨m, by ring⟩
  · exact Int.modEq_iff_dvd.2 ⟨T * m, by ring⟩

end

end Erdos215
