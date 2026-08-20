import ErdosProblems.Erdos957.GeometryCore
import ErdosProblems.Erdos957.HullOrder

/-!
# The rigid two-extreme source frame for Erdős 957

This module proves the local geometric bridge used by the exhaustive
Case 2/4 classification.  A degree-three strict-hull source has three
one-separated unit rays in an open semicircle.  Its canonical middle ray is
the unique ray in the middle third.  If a cyclic hull edge endpoint is also
unit-adjacent to that middle point, edge support forces the hull ray outside
the two outer source-neighbor rays.  The common-unit triangle is therefore
equilateral, so the cyclic hull edge has length one.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957TwoExtremeFrame

open Erdos957GeometryCore

abbrev ComplexPoint := Erdos957GeometryCore.Point

private def cCross (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

private lemma cCross_eq_norm_mul_sin_sub (z w : ℂ) :
    cCross z w = ‖z‖ * ‖w‖ * Real.sin (w.arg - z.arg) := by
  simp only [cCross]
  rw [Real.sin_sub, mul_sub]
  rw [← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z,
    ← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  ring

private lemma cCross_neg_of_arg_lt {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0)
    (hzim : z.im < 0) (hwim : w.im < 0) (hwz : w.arg < z.arg) :
    cCross z w < 0 := by
  rw [cCross_eq_norm_mul_sin_sub]
  have hdiffneg : w.arg - z.arg < 0 := sub_neg.mpr hwz
  have hdiffpi : -Real.pi < w.arg - z.arg := by
    have hwarg := Complex.neg_pi_lt_arg w
    have hzarg : z.arg < 0 := Complex.arg_neg_iff.mpr hzim
    linarith
  exact mul_neg_of_pos_of_neg
    (mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw))
    (Real.sin_neg_of_neg_of_neg_pi_lt hdiffneg hdiffpi)

private lemma cCross_pos_of_arg_lt {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0)
    (hzim : z.im < 0) (hwim : w.im < 0) (hzw : z.arg < w.arg) :
    0 < cCross z w := by
  rw [cCross_eq_norm_mul_sin_sub]
  have hdiffpos : 0 < w.arg - z.arg := sub_pos.mpr hzw
  have hdiffpi : w.arg - z.arg < Real.pi := by
    have hzarg := Complex.neg_pi_lt_arg z
    have hwarg : w.arg < 0 := Complex.arg_neg_iff.mpr hwim
    linarith
  exact mul_pos
    (mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw))
    (Real.sin_pos_of_pos_of_lt_pi hdiffpos hdiffpi)

private lemma arg_outside_of_cross_outer_mul_nonneg
    {z₀ z₂ c : ℂ}
    (hz₀ : z₀ ≠ 0) (hz₂ : z₂ ≠ 0) (hc : c ≠ 0)
    (hz₀im : z₀.im < 0) (hz₂im : z₂.im < 0) (hcim : c.im < 0)
    (harg₀₂ : z₀.arg < z₂.arg)
    (hcross : 0 ≤ cCross c z₀ * cCross c z₂) :
    c.arg ≤ z₀.arg ∨ z₂.arg ≤ c.arg := by
  by_contra hnot
  push_neg at hnot
  have hleft : cCross c z₀ < 0 :=
    cCross_neg_of_arg_lt hc hz₀ hcim hz₀im hnot.1
  have hright : 0 < cCross c z₂ :=
    cCross_pos_of_arg_lt hc hz₂ hcim hz₂im hnot.2
  nlinarith

private lemma angle_eq_arg_sub_of_neg_im_of_arg_le
    {z w : ℂ} (hzne : z ≠ 0) (hwne : w ≠ 0)
    (hzim : z.im < 0) (hwim : w.im < 0) (hwz : w.arg ≤ z.arg) :
    InnerProductGeometry.angle z w = z.arg - w.arg := by
  have hdiff : z.arg - w.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · have hwarg := Complex.neg_pi_lt_arg w
      have hzarg : z.arg < 0 := Complex.arg_neg_iff.mpr hzim
      linarith [Real.pi_pos]
    · have hzarg : z.arg < 0 := Complex.arg_neg_iff.mpr hzim
      have hwarg := Complex.neg_pi_lt_arg w
      linarith [Real.pi_pos]
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  have hzexp : Complex.exp (z.arg * Complex.I) = z / ‖z‖ := by
    apply mul_left_cancel₀ (a := (‖z‖ : ℂ))
    · exact_mod_cast hznorm.ne'
    · rw [Complex.norm_mul_exp_arg_mul_I]
      rw [div_eq_mul_inv]
      field_simp
      symm
      apply div_self
      exact_mod_cast hznorm.ne'
  have hzdiv : z / (‖z‖ : ℂ) = (‖z‖⁻¹ : ℝ) • z := by
    apply Complex.ext <;> simp [div_eq_mul_inv] <;> ring
  have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hwexp : Complex.exp (w.arg * Complex.I) = w / ‖w‖ := by
    apply mul_left_cancel₀ (a := (‖w‖ : ℂ))
    · exact_mod_cast hwnorm.ne'
    · rw [Complex.norm_mul_exp_arg_mul_I]
      rw [div_eq_mul_inv]
      field_simp
      symm
      apply div_self
      exact_mod_cast hwnorm.ne'
  have hwdiv : w / (‖w‖ : ℂ) = (‖w‖⁻¹ : ℝ) • w := by
    apply Complex.ext <;> simp [div_eq_mul_inv] <;> ring
  have hscale : InnerProductGeometry.angle (z / ‖z‖) (w / ‖w‖) =
      InnerProductGeometry.angle z w := by
    rw [hzdiv, hwdiv]
    calc
      InnerProductGeometry.angle (‖z‖⁻¹ • z) (‖w‖⁻¹ • w) =
          InnerProductGeometry.angle z (‖w‖⁻¹ • w) :=
        InnerProductGeometry.angle_smul_left_of_pos z (‖w‖⁻¹ • w)
          (inv_pos.mpr hznorm)
      _ = InnerProductGeometry.angle z w :=
        InnerProductGeometry.angle_smul_right_of_pos z w (inv_pos.mpr hwnorm)
  calc
    InnerProductGeometry.angle z w =
        InnerProductGeometry.angle (z / ‖z‖) (w / ‖w‖) := hscale.symm
    _ =
        InnerProductGeometry.angle (Complex.exp (z.arg * Complex.I))
          (Complex.exp (w.arg * Complex.I)) := by
            rw [hzexp, hwexp]
    _ = |toIocMod Real.two_pi_pos (-Real.pi) (z.arg - w.arg)| :=
      Complex.angle_exp_exp z.arg w.arg
    _ = z.arg - w.arg := by
      rw [(toIocMod_eq_self Real.two_pi_pos).2 (by
        simpa [two_mul] using hdiff)]
      exact abs_of_nonneg (sub_nonneg.mpr hwz)

private lemma angle_le_pi_div_three_of_common_unit
    {x y : ℂ} (hx : ‖x‖ = 1) (hyx : ‖y - x‖ = 1)
    (hy : 1 ≤ ‖y‖) :
    InnerProductGeometry.angle x y ≤ Real.pi / 3 := by
  have hcosine :=
    InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
      y x
  have hynorm : 0 < ‖y‖ := lt_of_lt_of_le (by norm_num) hy
  have hcosEq : ‖y‖ =
      2 * Real.cos (InnerProductGeometry.angle x y) := by
    rw [InnerProductGeometry.angle_comm]
    rw [hyx, hx] at hcosine
    have hmul : ‖y‖ * ‖y‖ =
        ‖y‖ * (2 * Real.cos (InnerProductGeometry.angle y x)) := by
      nlinarith
    exact (mul_left_cancel₀ (ne_of_gt hynorm) hmul)
  have hcosLower : (1 / 2 : ℝ) ≤
      Real.cos (InnerProductGeometry.angle x y) := by
    nlinarith
  by_contra hnot
  have hangle : Real.pi / 3 < InnerProductGeometry.angle x y :=
    lt_of_not_ge hnot
  have hcosStrict := Real.cos_lt_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ Real.pi / 3)
    (InnerProductGeometry.angle_le_pi x y) hangle
  rw [Real.cos_pi_div_three] at hcosStrict
  linarith

private lemma norm_eq_one_of_unit_common_of_angle_eq_pi_div_three
    {m c : ℂ} (hm : ‖m‖ = 1) (hmc : ‖c - m‖ = 1)
    (hcNorm : 1 ≤ ‖c‖)
    (hangle : InnerProductGeometry.angle m c = Real.pi / 3) :
    ‖c‖ = 1 := by
  have hcosine :=
    InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
      c m
  rw [hmc, hm, InnerProductGeometry.angle_comm, hangle,
    Real.cos_pi_div_three] at hcosine
  nlinarith [norm_nonneg c]

/-- Pure angular rigidity behind the source-frame bridge.  `z₀` and `z₂`
are the two outer unit neighbors, `m` is the middle unit neighbor, and `c`
is the cyclic hull-edge vector. -/
private theorem norm_eq_one_of_middle_common_and_outer_support
    {z₀ m z₂ c : ℂ}
    (hz₀ : ‖z₀‖ = 1) (hm : ‖m‖ = 1) (hz₂ : ‖z₂‖ = 1)
    (hallim : z₀.im < 0 ∧ m.im < 0 ∧ z₂.im < 0 ∧ c.im < 0)
    (harg : z₀.arg < m.arg ∧ m.arg < z₂.arg)
    (hsep₀ : 1 ≤ ‖z₀ - m‖) (hsep₂ : 1 ≤ ‖m - z₂‖)
    (hcNorm : 1 ≤ ‖c‖) (hcm : ‖c - m‖ = 1)
    (hcross : 0 ≤ cCross c z₀ * cCross c z₂) :
    ‖c‖ = 1 := by
  have hz₀ne : z₀ ≠ 0 := norm_ne_zero_iff.mp (by rw [hz₀]; norm_num)
  have hmne : m ≠ 0 := norm_ne_zero_iff.mp (by rw [hm]; norm_num)
  have hz₂ne : z₂ ≠ 0 := norm_ne_zero_iff.mp (by rw [hz₂]; norm_num)
  have hcne : c ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num) hcNorm))
  have hout := arg_outside_of_cross_outer_mul_nonneg hz₀ne hz₂ne hcne
    hallim.1 hallim.2.2.1 hallim.2.2.2 (harg.1.trans harg.2) hcross
  have hangle₀ : Real.pi / 3 ≤ InnerProductGeometry.angle m z₀ :=
    Erdos957Angle.pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      hm hz₀ (by simpa [norm_sub_rev] using hsep₀)
  have hangle₂ : Real.pi / 3 ≤ InnerProductGeometry.angle m z₂ :=
    Erdos957Angle.pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub hm hz₂ hsep₂
  have hangleC : InnerProductGeometry.angle m c ≤ Real.pi / 3 :=
    angle_le_pi_div_three_of_common_unit hm
      (by simpa [norm_sub_rev] using hcm) hcNorm
  have hangleEq : InnerProductGeometry.angle m c = Real.pi / 3 := by
    rcases hout with hcLeft | hcRight
    · have hmc := angle_eq_arg_sub_of_neg_im_of_arg_le hmne hcne
        hallim.2.1 hallim.2.2.2 (hcLeft.trans harg.1.le)
      have hmz₀ := angle_eq_arg_sub_of_neg_im_of_arg_le hmne hz₀ne
        hallim.2.1 hallim.1 harg.1.le
      rw [hmc] at hangleC
      rw [hmz₀] at hangle₀
      rw [hmc]
      exact le_antisymm hangleC (by linarith)
    · have hcmarg := angle_eq_arg_sub_of_neg_im_of_arg_le hcne hmne
        hallim.2.2.2 hallim.2.1 (harg.2.le.trans hcRight)
      have hmz₂ := angle_eq_arg_sub_of_neg_im_of_arg_le hz₂ne hmne
        hallim.2.2.1 hallim.2.1 harg.2.le
      rw [InnerProductGeometry.angle_comm m c, hcmarg] at hangleC
      rw [InnerProductGeometry.angle_comm m z₂, hmz₂] at hangle₂
      rw [InnerProductGeometry.angle_comm m c, hcmarg]
      exact le_antisymm hangleC (by linarith)
  exact norm_eq_one_of_unit_common_of_angle_eq_pi_div_three hm hcm hcNorm hangleEq

/-! ## The actual degree-three source rays -/

private lemma phaseBin_eq_one_of_unit_in_open_cone {v : ℝ × ℝ}
    (hunit : Erdos957Cases13.sqDist Erdos957Cases13.origin v = 1)
    (hcone : Erdos957Cases13.InOpenMiddleCone v) :
    Erdos957Angle.phaseBin (Erdos957Cases13.toComplex v) = (1 : Fin 6) := by
  let z := Erdos957Cases13.toComplex v
  have him : z.im < 0 := by
    have hsqrt := Erdos957Cases13.sqrtThree_pos
    dsimp [Erdos957Cases13.InOpenMiddleCone] at hcone
    dsimp [z, Erdos957Cases13.toComplex]
    linarith
  have hnorm : ‖z‖ = 1 := by
    have hd := (Erdos957Cases13.sqDist_eq_one_iff_dist_eq_one
      Erdos957Cases13.origin v).mp hunit
    change dist 0 z = 1 at hd
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hd
  have hxy : v.1 ^ 2 + v.2 ^ 2 = 1 := by
    simpa [Erdos957Cases13.sqDist, Erdos957Cases13.origin] using hunit
  have habs : |Erdos957Cases13.sqrtThree * v.1| < -v.2 := by
    rw [abs_lt]
    dsimp [Erdos957Cases13.InOpenMiddleCone] at hcone
    constructor <;> linarith
  have hminusNonneg : 0 ≤ -v.2 := by
    exact le_of_lt (lt_of_le_of_lt (abs_nonneg _) habs)
  have hsquare : (Erdos957Cases13.sqrtThree * v.1) ^ 2 < (-v.2) ^ 2 := by
    have h := (sq_lt_sq₀ (abs_nonneg
      (Erdos957Cases13.sqrtThree * v.1)) hminusNonneg).2 habs
    simpa only [sq_abs] using h
  have hsqrtSq := Erdos957Cases13.sqrtThree_sq
  have hxlo : -(1 / 2 : ℝ) < v.1 := by nlinarith [sq_nonneg (v.1 + 1 / 2)]
  have hxhi : v.1 < (1 / 2 : ℝ) := by nlinarith [sq_nonneg (v.1 - 1 / 2)]
  have harg : z.arg = -Real.arccos v.1 := by
    rw [Complex.arg_of_im_neg him, hnorm]
    norm_num [z, Erdos957Cases13.toComplex]
  have hxmem : v.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith
  have harccosLower : Real.pi / 3 < Real.arccos v.1 := by
    have h := Real.arccos_lt_arccos hxmem.1 hxhi (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hhalf : Real.arccos (1 / 2 : ℝ) = Real.pi / 3 := by
      rw [← Real.cos_pi_div_three, Real.arccos_cos] <;> nlinarith [Real.pi_pos]
    rwa [hhalf] at h
  have harccosUpper : Real.arccos v.1 < 2 * Real.pi / 3 := by
    have hxlo' : (-1 / 2 : ℝ) < v.1 := by linarith
    have h := Real.arccos_lt_arccos (by norm_num : (-1 : ℝ) ≤ -1 / 2)
      hxlo' hxmem.2
    have hhalf : Real.arccos (-1 / 2 : ℝ) = 2 * Real.pi / 3 := by
      rw [show (-1 / 2 : ℝ) = Real.cos (2 * Real.pi / 3) by
        rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]; ring,
        Real.arccos_cos] <;> nlinarith [Real.pi_pos]
    rwa [hhalf] at h
  have hargBounds : -(2 * Real.pi / 3) < z.arg ∧ z.arg < -(Real.pi / 3) := by
    rw [harg]
    constructor <;> linarith
  have hphase : Erdos957Angle.principalPhase z = z.arg := by
    simp [Erdos957Angle.principalPhase,
      ne_of_lt ((Complex.arg_neg_iff.mpr him).trans Real.pi_pos)]
  generalize hi : Erdos957Angle.phaseBin z = i
  fin_cases i
  · have hb := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hi
    norm_num at hb
    rw [hphase] at hb
    linarith
  · rfl
  · have hb := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hi
    norm_num at hb
    rw [hphase] at hb
    linarith
  all_goals
    have hlt := Erdos957Angle.phaseBin_val_lt_three_of_im_neg him
    rw [hi] at hlt
    norm_num at hlt

private def localComplex {A : Finset ComplexPoint} (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) (q : Vertex A) : ℂ :=
  Erdos957Cases13.toComplex (P.localCoord source q)

private lemma localComplex_im_neg {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) {q : Vertex A}
    (hq : q ≠ source.1) : (localComplex P source q).im < 0 := by
  simpa [localComplex, Erdos957Cases13.toComplex] using
    P.localCoord_snd_neg source q hq

private lemma localComplex_norm_of_adj {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) {q : Vertex A}
    (hq : (unitDistanceGraph A).Adj source.1 q) :
    ‖localComplex P source q‖ = 1 := by
  have hsquare : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (P.localCoord source q) = 1 := by
    change Erdos957Cases13.sqDist (0, 0) (P.localCoord source q) = 1
    rw [← P.localCoord_source source, P.sqDist_localCoord, hq]
    norm_num
  have hd := (Erdos957Cases13.sqDist_eq_one_iff_dist_eq_one
    Erdos957Cases13.origin (P.localCoord source q)).mp hsquare
  change dist 0 (localComplex P source q) = 1 at hd
  simpa only [dist_eq_norm, zero_sub, norm_neg] using hd

private lemma localComplex_one_le_norm {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) {q : Vertex A} (hq : q ≠ source.1) :
    1 ≤ ‖localComplex P source q‖ := by
  have hdist := hA source.1 source.1.property q q.property
    (fun h ↦ hq (Subtype.ext h.symm))
  have hsquare : 1 ≤ Erdos957Cases13.sqDist Erdos957Cases13.origin
      (P.localCoord source q) := by
    change 1 ≤ Erdos957Cases13.sqDist (0, 0) (P.localCoord source q)
    rw [← P.localCoord_source source, P.sqDist_localCoord]
    nlinarith [(dist_nonneg : 0 ≤ dist (source.1 : ComplexPoint) q)]
  have hd := (Erdos957Cases13.one_le_sqDist_iff_one_le_dist
    Erdos957Cases13.origin (P.localCoord source q)).mp hsquare
  change 1 ≤ dist 0 (localComplex P source q) at hd
  simpa only [dist_eq_norm, zero_sub, norm_neg] using hd

private lemma localComplex_norm_sub_of_adj {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) {q r : Vertex A}
    (hqr : (unitDistanceGraph A).Adj q r) :
    ‖localComplex P source q - localComplex P source r‖ = 1 := by
  have hsquare : Erdos957Cases13.sqDist (P.localCoord source q)
      (P.localCoord source r) = 1 := by
    rw [P.sqDist_localCoord, hqr]
    norm_num
  have hd := (Erdos957Cases13.sqDist_eq_one_iff_dist_eq_one
    (P.localCoord source q) (P.localCoord source r)).mp hsquare
  simpa only [localComplex, dist_eq_norm] using hd

private lemma localComplex_one_le_norm_sub {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) {q r : Vertex A} (hqr : q ≠ r) :
    1 ≤ ‖localComplex P source q - localComplex P source r‖ := by
  have hdist := hA q q.property r r.property (fun h ↦ hqr (Subtype.ext h))
  have hsquare : 1 ≤ Erdos957Cases13.sqDist (P.localCoord source q)
      (P.localCoord source r) := by
    rw [P.sqDist_localCoord]
    nlinarith [(dist_nonneg : 0 ≤ dist (q : ComplexPoint) r)]
  have hd := (Erdos957Cases13.one_le_sqDist_iff_one_le_dist
    (P.localCoord source q) (P.localCoord source r)).mp hsquare
  simpa only [localComplex, dist_eq_norm] using hd

private theorem exists_outer_source_neighbors
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hmiddleAdj : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (P.localCoord source middle)) :
    ∃ q₀ q₂ : Vertex A,
      (unitDistanceGraph A).Adj source.1 q₀ ∧
      (unitDistanceGraph A).Adj source.1 q₂ ∧
      (localComplex P source q₀).arg < (localComplex P source middle).arg ∧
      (localComplex P source middle).arg <
        (localComplex P source q₂).arg := by
  classical
  let N := (unitDistanceGraph A).neighborFinset source.1
  let z : Vertex A → ℂ := localComplex P source
  have hneSource {q : Vertex A} (hq : q ∈ N) : q ≠ source.1 := by
    intro h
    subst q
    exact (SimpleGraph.notMem_neighborFinset_self
      (G := unitDistanceGraph A) (v := source.1)) hq
  have him {q : Vertex A} (hq : q ∈ N) : (z q).im < 0 := by
    exact localComplex_im_neg P source (hneSource hq)
  have hnorm {q : Vertex A} (hq : q ∈ N) : ‖z q‖ = 1 := by
    apply localComplex_norm_of_adj P source
    exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) q).mp hq
  have hsep {q r : Vertex A} (hq : q ∈ N) (hr : r ∈ N) (hqr : q ≠ r) :
      1 ≤ ‖z q - z r‖ :=
    localComplex_one_le_norm_sub hA P source hqr
  let phase : N → Fin 3 := fun q ↦
    ⟨(Erdos957Angle.phaseBin (z q)).val,
      Erdos957Angle.phaseBin_val_lt_three_of_im_neg (him q.property)⟩
  have hphaseInj : Function.Injective phase := by
    intro q r hqr
    apply Subtype.ext
    by_contra hne
    have hbin : Erdos957Angle.phaseBin (z q) =
        Erdos957Angle.phaseBin (z r) := by
      apply Fin.ext
      simpa [phase] using congrArg Fin.val hqr
    have hangleGe :=
      Erdos957Angle.pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
        (hnorm q.property) (hnorm r.property)
        (hsep q.property r.property hne)
    have hangleEq := Erdos957Angle.angle_eq_abs_principalPhase_sub_of_phaseBin_eq
      (hnorm q.property) (hnorm r.property) hbin
    have hangleLt := Erdos957Angle.abs_principalPhase_sub_lt_of_phaseBin_eq hbin
    linarith
  have hcardN : Fintype.card N = 3 := by
    rw [Fintype.card_coe]
    change ((unitDistanceGraph A).neighborFinset source.1).card = 3
    rw [← SimpleGraph.degree]
    exact hdegree
  have hphaseBij : Function.Bijective phase := by
    apply (Fintype.bijective_iff_injective_and_card phase).mpr
    exact ⟨hphaseInj, by simpa [hcardN]⟩
  obtain ⟨q₀, hq₀⟩ := hphaseBij.2 (0 : Fin 3)
  obtain ⟨q₂, hq₂⟩ := hphaseBij.2 (2 : Fin 3)
  have hbin₀ : Erdos957Angle.phaseBin (z q₀) = (0 : Fin 6) := by
    apply Fin.ext
    simpa [phase] using congrArg Fin.val hq₀
  have hbin₂ : Erdos957Angle.phaseBin (z q₂) = (2 : Fin 6) := by
    apply Fin.ext
    simpa [phase] using congrArg Fin.val hq₂
  have hmiddleN : middle ∈ N :=
    (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) middle).mpr hmiddleAdj
  have hbinMiddle : Erdos957Angle.phaseBin (z middle) = (1 : Fin 6) := by
    exact phaseBin_eq_one_of_unit_in_open_cone
      (by
        change Erdos957Cases13.sqDist (0, 0)
          (P.localCoord source middle) = 1
        rw [← P.localCoord_source source, P.sqDist_localCoord, hmiddleAdj]
        norm_num)
      hmiddleCone
  have hphase₀ : Erdos957Angle.principalPhase (z q₀) = (z q₀).arg := by
    have harg : (z q₀).arg < 0 := Complex.arg_neg_iff.mpr (him q₀.property)
    simp [Erdos957Angle.principalPhase,
      ne_of_lt (harg.trans Real.pi_pos)]
  have hphaseMiddle : Erdos957Angle.principalPhase (z middle) = (z middle).arg := by
    have harg : (z middle).arg < 0 := Complex.arg_neg_iff.mpr (him hmiddleN)
    simp [Erdos957Angle.principalPhase,
      ne_of_lt (harg.trans Real.pi_pos)]
  have hphase₂ : Erdos957Angle.principalPhase (z q₂) = (z q₂).arg := by
    have harg : (z q₂).arg < 0 := Complex.arg_neg_iff.mpr (him q₂.property)
    simp [Erdos957Angle.principalPhase,
      ne_of_lt (harg.trans Real.pi_pos)]
  have hb₀ := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin₀
  have hbMiddle := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbinMiddle
  have hb₂ := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin₂
  norm_num at hb₀ hbMiddle hb₂
  rw [hphase₀] at hb₀
  rw [hphaseMiddle] at hbMiddle
  rw [hphase₂] at hb₂
  refine ⟨q₀, q₂, ?_, ?_, ?_, ?_⟩
  · exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) q₀).mp q₀.property
  · exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) q₂).mp q₂.property
  · change (z q₀).arg < (z middle).arg
    linarith
  · change (z middle).arg < (z q₂).arg
    linarith

/-! ## Orientation-free transport of edge support -/

private def pairDot (p q : ℝ × ℝ) : ℝ := p.1 * q.1 + p.2 * q.2

private def pointDot (p q : ComplexPoint) : ℝ := p 0 * q 0 + p 1 * q 1

private lemma local_normSq_eq_point_normSq {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) (q : Vertex A) :
    (P.localCoord source q).1 ^ 2 + (P.localCoord source q).2 ^ 2 =
      (((q : ComplexPoint) - source.1.1) 0) ^ 2 +
        (((q : ComplexPoint) - source.1.1) 1) ^ 2 := by
  have h := P.sqDist_localCoord source source.1 q
  rw [P.localCoord_source, dist_comm (source.1.1 : ComplexPoint) q,
    Erdos957Cases24.dist_sq_eq_coordinates] at h
  simpa [Erdos957Cases13.sqDist] using h

private lemma local_dot_eq_point_dot {A : Finset ComplexPoint}
    (P : CyclicHullData A) (source : {p // p ∈ P.H}) (q r : Vertex A) :
    pairDot (P.localCoord source q) (P.localCoord source r) =
      pointDot ((q : ComplexPoint) - source.1.1)
        ((r : ComplexPoint) - source.1.1) := by
  have hq := local_normSq_eq_point_normSq P source q
  have hr := local_normSq_eq_point_normSq P source r
  have hqr := P.sqDist_localCoord source q r
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hqr
  simp only [Erdos957Cases13.sqDist] at hqr
  dsimp [pairDot, pointDot]
  dsimp [pairDot, pointDot] at hq hr hqr
  ring_nf at hqr ⊢
  nlinarith

/-- Although the source frame may reverse orientation, it reverses every
cross product by the same sign.  Consequently the product of two crosses
with a common first ray is invariant. -/
private lemma local_cross_product_eq_ambient_cross_product
    {A : Finset ComplexPoint} (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) (c q r : Vertex A) :
    cCross (localComplex P source c) (localComplex P source q) *
        cCross (localComplex P source c) (localComplex P source r) =
      cross ((c : ComplexPoint) - source.1.1)
          ((q : ComplexPoint) - source.1.1) *
        cross ((c : ComplexPoint) - source.1.1)
          ((r : ComplexPoint) - source.1.1) := by
  have hn := local_normSq_eq_point_normSq P source c
  have hdqr := local_dot_eq_point_dot P source q r
  have hdcq := local_dot_eq_point_dot P source c q
  have hdcr := local_dot_eq_point_dot P source c r
  calc
    cCross (localComplex P source c) (localComplex P source q) *
        cCross (localComplex P source c) (localComplex P source r) =
        ((P.localCoord source c).1 ^ 2 + (P.localCoord source c).2 ^ 2) *
            pairDot (P.localCoord source q) (P.localCoord source r) -
          pairDot (P.localCoord source c) (P.localCoord source q) *
            pairDot (P.localCoord source c) (P.localCoord source r) := by
      simp only [cCross, localComplex, Erdos957Cases13.toComplex, pairDot]
      ring
    _ = ((((c : ComplexPoint) - source.1.1) 0) ^ 2 +
            (((c : ComplexPoint) - source.1.1) 1) ^ 2) *
          pointDot ((q : ComplexPoint) - source.1.1)
            ((r : ComplexPoint) - source.1.1) -
        pointDot ((c : ComplexPoint) - source.1.1)
            ((q : ComplexPoint) - source.1.1) *
          pointDot ((c : ComplexPoint) - source.1.1)
            ((r : ComplexPoint) - source.1.1) := by
      rw [hn, hdqr, hdcq, hdcr]
    _ = cross ((c : ComplexPoint) - source.1.1)
          ((q : ComplexPoint) - source.1.1) *
        cross ((c : ComplexPoint) - source.1.1)
          ((r : ComplexPoint) - source.1.1) := by
      simp only [cross, pointDot]
      ring

/-! ## The cyclic two-extreme frame -/

/-- A graph vertex is one of the two actual endpoints of the hull edges
incident to `source`.  This definition is independent of the later case
classification and therefore avoids an import cycle. -/
def IsIncidentCyclicVertex {A : Finset ComplexPoint} (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) (c : Vertex A) : Prop :=
  c = (P.next⁻¹ source).1 ∨ c = (P.next source).1

/-- If a genuine middle unit neighbor of a degree-three hull source is also
unit-adjacent to either incident cyclic hull vertex, then that cyclic vertex
is itself a unit neighbor of the source.  Thus the three actual vertices
form a unit equilateral triangle. -/
theorem source_adj_incidentCyclicVertex_of_middle_adj
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (middle c : Vertex A)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (P.localCoord source middle))
    (hcIncident : IsIncidentCyclicVertex P source c)
    (hm : (unitDistanceGraph A).Adj middle c) :
    (unitDistanceGraph A).Adj source.1 c := by
  obtain ⟨q₀, q₂, hsource₀, hsource₂, harg₀, harg₂⟩ :=
    exists_outer_source_neighbors hA P source middle hdegree
      hsourceMiddle hmiddleCone
  have hq₀Middle : q₀ ≠ middle := by
    intro h
    subst q₀
    exact (lt_irrefl (localComplex P source middle).arg) harg₀
  have hmiddleq₂ : middle ≠ q₂ := by
    intro h
    subst q₂
    exact (lt_irrefl (localComplex P source middle).arg) harg₂
  have hcSource : c ≠ source.1 := by
    rcases hcIncident with hc | hc
    · rw [hc]
      intro h
      apply P.prev_ne_self source
      apply Subtype.ext
      exact h
    · rw [hc]
      intro h
      apply P.next_ne_self source
      apply Subtype.ext
      exact h
  have hcrossAmbient :
      0 ≤ cross ((c : ComplexPoint) - source.1.1)
            ((q₀ : ComplexPoint) - source.1.1) *
          cross ((c : ComplexPoint) - source.1.1)
            ((q₂ : ComplexPoint) - source.1.1) := by
    rcases hcIncident with hc | hc
    · rw [hc]
      have h₀ := P.edge_support (P.next⁻¹ source) q₀
      have h₂ := P.edge_support (P.next⁻¹ source) q₂
      have hnextPrev : P.next (P.next⁻¹ source) = source := by simp
      rw [hnextPrev] at h₀ h₂
      have h₀' :
          cross (((P.next⁻¹ source).1.1 : ComplexPoint) - source.1.1)
              ((q₀ : ComplexPoint) - source.1.1) ≤ 0 := by
        simp only [cross] at h₀ ⊢
        simp only [WithLp.ofLp_sub, Pi.sub_apply] at h₀ ⊢
        nlinarith
      have h₂' :
          cross (((P.next⁻¹ source).1.1 : ComplexPoint) - source.1.1)
              ((q₂ : ComplexPoint) - source.1.1) ≤ 0 := by
        simp only [cross] at h₂ ⊢
        simp only [WithLp.ofLp_sub, Pi.sub_apply] at h₂ ⊢
        nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos h₀' h₂'
    · rw [hc]
      exact mul_nonneg (P.edge_support source q₀) (P.edge_support source q₂)
  have hcrossLocal :
      0 ≤ cCross (localComplex P source c) (localComplex P source q₀) *
        cCross (localComplex P source c) (localComplex P source q₂) := by
    rw [local_cross_product_eq_ambient_cross_product]
    exact hcrossAmbient
  have hcNorm : ‖localComplex P source c‖ = 1 := by
    apply norm_eq_one_of_middle_common_and_outer_support
        (z₀ := localComplex P source q₀)
        (m := localComplex P source middle)
        (z₂ := localComplex P source q₂)
        (c := localComplex P source c)
    · exact localComplex_norm_of_adj P source hsource₀
    · exact localComplex_norm_of_adj P source hsourceMiddle
    · exact localComplex_norm_of_adj P source hsource₂
    · exact ⟨localComplex_im_neg P source hsource₀.ne.symm,
        localComplex_im_neg P source hsourceMiddle.ne.symm,
        localComplex_im_neg P source hsource₂.ne.symm,
        localComplex_im_neg P source hcSource⟩
    · exact ⟨harg₀, harg₂⟩
    · exact localComplex_one_le_norm_sub hA P source hq₀Middle
    · exact localComplex_one_le_norm_sub hA P source hmiddleq₂
    · exact localComplex_one_le_norm hA P source hcSource
    · exact localComplex_norm_sub_of_adj P source hm.symm
    · exact hcrossLocal
  have hlocalSq : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (P.localCoord source c) = 1 := by
    apply (Erdos957Cases13.sqDist_eq_one_iff_dist_eq_one
      Erdos957Cases13.origin (P.localCoord source c)).mpr
    change dist 0 (localComplex P source c) = 1
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hcNorm
  change dist (source.1 : ComplexPoint) c = 1
  change Erdos957Cases13.sqDist (0, 0) (P.localCoord source c) = 1 at hlocalSq
  rw [← P.localCoord_source source, P.sqDist_localCoord] at hlocalSq
  nlinarith [(dist_nonneg : 0 ≤ dist (source.1 : ComplexPoint) c)]

/-- The full equilateral-frame conclusion, retaining all three actual graph
edges for downstream rigid-coordinate constructions. -/
theorem equilateral_source_middle_incidentCyclicVertex
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (middle c : Vertex A)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (P.localCoord source middle))
    (hcIncident : IsIncidentCyclicVertex P source c)
    (hm : (unitDistanceGraph A).Adj middle c) :
    (unitDistanceGraph A).Adj source.1 middle ∧
      (unitDistanceGraph A).Adj middle c ∧
      (unitDistanceGraph A).Adj source.1 c := by
  exact ⟨hsourceMiddle, hm,
    source_adj_incidentCyclicVertex_of_middle_adj hA P source middle c
      hdegree hsourceMiddle hmiddleCone hcIncident hm⟩

/-- Chart-compatible form of the new hull edge: in the source's honest
Euclidean chart the incident cyclic ray has norm exactly one. -/
theorem norm_localComplex_incidentCyclicVertex_eq_one
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (middle c : Vertex A)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (P.localCoord source middle))
    (hcIncident : IsIncidentCyclicVertex P source c)
    (hm : (unitDistanceGraph A).Adj middle c) :
    ‖Erdos957Cases13.toComplex (P.localCoord source c)‖ = 1 := by
  exact localComplex_norm_of_adj P source
    (source_adj_incidentCyclicVertex_of_middle_adj hA P source middle c
      hdegree hsourceMiddle hmiddleCone hcIncident hm)

/-! ## The same rigidity in an arbitrary honest aligned chart -/

private def alignedComplex {A : Finset ComplexPoint} (P : CyclicHullData A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (q : Vertex A) : ℂ :=
  Erdos957Cases13.toComplex (C.coord source q)

private lemma alignedComplex_norm_of_adj {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) {q : Vertex A}
    (hq : (unitDistanceGraph A).Adj source.1 q) :
    ‖alignedComplex P C source q‖ = 1 := by
  have hsquare : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (C.coord source q) = 1 := by
    change Erdos957Cases13.sqDist (0, 0) (C.coord source q) = 1
    rw [← C.coord_source source, C.sqDist_coord, hq]
    norm_num
  have hd := (Erdos957Cases13.sqDist_eq_one_iff_dist_eq_one
    Erdos957Cases13.origin (C.coord source q)).mp hsquare
  change dist 0 (alignedComplex P C source q) = 1 at hd
  simpa only [dist_eq_norm, zero_sub, norm_neg] using hd

private lemma alignedComplex_one_le_norm {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    {q : Vertex A} (hq : q ≠ source.1) :
    1 ≤ ‖alignedComplex P C source q‖ := by
  have hdist := hA source.1 source.1.property q q.property
    (fun h ↦ hq (Subtype.ext h.symm))
  have hsquare : 1 ≤ Erdos957Cases13.sqDist Erdos957Cases13.origin
      (C.coord source q) := by
    change 1 ≤ Erdos957Cases13.sqDist (0, 0) (C.coord source q)
    rw [← C.coord_source source, C.sqDist_coord]
    nlinarith [(dist_nonneg : 0 ≤ dist (source.1 : ComplexPoint) q)]
  have hd := (Erdos957Cases13.one_le_sqDist_iff_one_le_dist
    Erdos957Cases13.origin (C.coord source q)).mp hsquare
  change 1 ≤ dist 0 (alignedComplex P C source q) at hd
  simpa only [dist_eq_norm, zero_sub, norm_neg] using hd

private lemma alignedComplex_norm_sub_of_adj {A : Finset ComplexPoint}
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) {q r : Vertex A}
    (hqr : (unitDistanceGraph A).Adj q r) :
    ‖alignedComplex P C source q - alignedComplex P C source r‖ = 1 := by
  have hsquare : Erdos957Cases13.sqDist (C.coord source q)
      (C.coord source r) = 1 := by
    rw [C.sqDist_coord, hqr]
    norm_num
  have hd := (Erdos957Cases13.sqDist_eq_one_iff_dist_eq_one
    (C.coord source q) (C.coord source r)).mp hsquare
  simpa only [alignedComplex, dist_eq_norm] using hd

private lemma alignedComplex_one_le_norm_sub {A : Finset ComplexPoint}
    (hA : IsOneSeparated A) (P : CyclicHullData A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    {q r : Vertex A} (hqr : q ≠ r) :
    1 ≤ ‖alignedComplex P C source q - alignedComplex P C source r‖ := by
  have hdist := hA q q.property r r.property (fun h ↦ hqr (Subtype.ext h))
  have hsquare : 1 ≤ Erdos957Cases13.sqDist (C.coord source q)
      (C.coord source r) := by
    rw [C.sqDist_coord]
    nlinarith [(dist_nonneg : 0 ≤ dist (q : ComplexPoint) r)]
  have hd := (Erdos957Cases13.one_le_sqDist_iff_one_le_dist
    (C.coord source q) (C.coord source r)).mp hsquare
  simpa only [alignedComplex, dist_eq_norm] using hd

/-- A one-separated configuration has at most one unit neighbour of a
source in the open sixty-degree middle cone of any honest aligned chart.
This is the choice-coherence fact used when two adjacent hull sources share
the same equilateral middle point. -/
theorem eq_of_source_adj_of_inOpenMiddleCone
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) {q r : Vertex A}
    (hq : (unitDistanceGraph A).Adj source.1 q)
    (hr : (unitDistanceGraph A).Adj source.1 r)
    (hqCone : Erdos957Cases13.InOpenMiddleCone (C.coord source q))
    (hrCone : Erdos957Cases13.InOpenMiddleCone (C.coord source r)) :
    q = r := by
  by_contra hqr
  have hqNorm : ‖alignedComplex P C source q‖ = 1 :=
    alignedComplex_norm_of_adj P C source hq
  have hrNorm : ‖alignedComplex P C source r‖ = 1 :=
    alignedComplex_norm_of_adj P C source hr
  have hqUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (C.coord source q) = 1 := by
    change Erdos957Cases13.sqDist (0, 0) (C.coord source q) = 1
    rw [← C.coord_source source, C.sqDist_coord, hq]
    norm_num
  have hrUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (C.coord source r) = 1 := by
    change Erdos957Cases13.sqDist (0, 0) (C.coord source r) = 1
    rw [← C.coord_source source, C.sqDist_coord, hr]
    norm_num
  have hqBin : Erdos957Angle.phaseBin (alignedComplex P C source q) =
      (1 : Fin 6) :=
    phaseBin_eq_one_of_unit_in_open_cone hqUnit hqCone
  have hrBin : Erdos957Angle.phaseBin (alignedComplex P C source r) =
      (1 : Fin 6) :=
    phaseBin_eq_one_of_unit_in_open_cone hrUnit hrCone
  have hangleGe :=
    Erdos957Angle.pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
      hqNorm hrNorm
      (alignedComplex_one_le_norm_sub hA P C source hqr)
  have hangleEq :=
    Erdos957Angle.angle_eq_abs_principalPhase_sub_of_phaseBin_eq
      hqNorm hrNorm (hqBin.trans hrBin.symm)
  have hangleLt :=
    Erdos957Angle.abs_principalPhase_sub_lt_of_phaseBin_eq
      (hqBin.trans hrBin.symm)
  linarith

private theorem exists_outer_source_neighbors_aligned
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hmiddleAdj : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (C.coord source middle)) :
    ∃ q₀ q₂ : Vertex A,
      (unitDistanceGraph A).Adj source.1 q₀ ∧
      (unitDistanceGraph A).Adj source.1 q₂ ∧
      (alignedComplex P C source q₀).arg <
        (alignedComplex P C source middle).arg ∧
      (alignedComplex P C source middle).arg <
        (alignedComplex P C source q₂).arg := by
  classical
  let N := (unitDistanceGraph A).neighborFinset source.1
  let z : Vertex A → ℂ := alignedComplex P C source
  have hneSource {q : Vertex A} (hq : q ∈ N) : q ≠ source.1 := by
    intro h
    subst q
    exact (SimpleGraph.notMem_neighborFinset_self
      (G := unitDistanceGraph A) (v := source.1)) hq
  have him {q : Vertex A} (hq : q ∈ N) : (z q).im < 0 := by
    simpa [z, alignedComplex, Erdos957Cases13.toComplex] using
      hstrict q (hneSource hq)
  have hnorm {q : Vertex A} (hq : q ∈ N) : ‖z q‖ = 1 := by
    apply alignedComplex_norm_of_adj P C source
    exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) q).mp hq
  have hsep {q r : Vertex A} (hq : q ∈ N) (hr : r ∈ N) (hqr : q ≠ r) :
      1 ≤ ‖z q - z r‖ :=
    alignedComplex_one_le_norm_sub hA P C source hqr
  let phase : N → Fin 3 := fun q ↦
    ⟨(Erdos957Angle.phaseBin (z q)).val,
      Erdos957Angle.phaseBin_val_lt_three_of_im_neg (him q.property)⟩
  have hphaseInj : Function.Injective phase := by
    intro q r hqr
    apply Subtype.ext
    by_contra hne
    have hbin : Erdos957Angle.phaseBin (z q) =
        Erdos957Angle.phaseBin (z r) := by
      apply Fin.ext
      simpa [phase] using congrArg Fin.val hqr
    have hangleGe :=
      Erdos957Angle.pi_div_three_le_angle_of_unit_norm_of_one_le_norm_sub
        (hnorm q.property) (hnorm r.property)
        (hsep q.property r.property hne)
    have hangleEq := Erdos957Angle.angle_eq_abs_principalPhase_sub_of_phaseBin_eq
      (hnorm q.property) (hnorm r.property) hbin
    have hangleLt := Erdos957Angle.abs_principalPhase_sub_lt_of_phaseBin_eq hbin
    linarith
  have hcardN : Fintype.card N = 3 := by
    rw [Fintype.card_coe]
    change ((unitDistanceGraph A).neighborFinset source.1).card = 3
    rw [← SimpleGraph.degree]
    exact hdegree
  have hphaseBij : Function.Bijective phase := by
    apply (Fintype.bijective_iff_injective_and_card phase).mpr
    exact ⟨hphaseInj, by simpa [hcardN]⟩
  obtain ⟨q₀, hq₀⟩ := hphaseBij.2 (0 : Fin 3)
  obtain ⟨q₂, hq₂⟩ := hphaseBij.2 (2 : Fin 3)
  have hbin₀ : Erdos957Angle.phaseBin (z q₀) = (0 : Fin 6) := by
    apply Fin.ext
    simpa [phase] using congrArg Fin.val hq₀
  have hbin₂ : Erdos957Angle.phaseBin (z q₂) = (2 : Fin 6) := by
    apply Fin.ext
    simpa [phase] using congrArg Fin.val hq₂
  have hmiddleN : middle ∈ N :=
    (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) middle).mpr hmiddleAdj
  have hbinMiddle : Erdos957Angle.phaseBin (z middle) = (1 : Fin 6) := by
    exact phaseBin_eq_one_of_unit_in_open_cone
      (by
        change Erdos957Cases13.sqDist (0, 0) (C.coord source middle) = 1
        rw [← C.coord_source source, C.sqDist_coord, hmiddleAdj]
        norm_num)
      hmiddleCone
  have hphase₀ : Erdos957Angle.principalPhase (z q₀) = (z q₀).arg := by
    have harg : (z q₀).arg < 0 := Complex.arg_neg_iff.mpr (him q₀.property)
    simp [Erdos957Angle.principalPhase,
      ne_of_lt (harg.trans Real.pi_pos)]
  have hphaseMiddle : Erdos957Angle.principalPhase (z middle) =
      (z middle).arg := by
    have harg : (z middle).arg < 0 := Complex.arg_neg_iff.mpr (him hmiddleN)
    simp [Erdos957Angle.principalPhase,
      ne_of_lt (harg.trans Real.pi_pos)]
  have hphase₂ : Erdos957Angle.principalPhase (z q₂) = (z q₂).arg := by
    have harg : (z q₂).arg < 0 := Complex.arg_neg_iff.mpr (him q₂.property)
    simp [Erdos957Angle.principalPhase,
      ne_of_lt (harg.trans Real.pi_pos)]
  have hb₀ := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin₀
  have hbMiddle := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbinMiddle
  have hb₂ := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin₂
  norm_num at hb₀ hbMiddle hb₂
  rw [hphase₀] at hb₀
  rw [hphaseMiddle] at hbMiddle
  rw [hphase₂] at hb₂
  refine ⟨q₀, q₂, ?_, ?_, ?_, ?_⟩
  · exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) q₀).mp q₀.property
  · exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) q₂).mp q₂.property
  · change (z q₀).arg < (z middle).arg
    linarith
  · change (z middle).arg < (z q₂).arg
    linarith

private lemma aligned_cross_product_eq_ambient_cross_product
    {A : Finset ComplexPoint} (P : CyclicHullData A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (c q r : Vertex A) :
    cCross (alignedComplex P C source c) (alignedComplex P C source q) *
        cCross (alignedComplex P C source c) (alignedComplex P C source r) =
      cross ((c : ComplexPoint) - source.1.1)
          ((q : ComplexPoint) - source.1.1) *
        cross ((c : ComplexPoint) - source.1.1)
          ((r : ComplexPoint) - source.1.1) := by
  have hcq := C.cross_displacements source source.1 c q
  have hcr := C.cross_displacements source source.1 c r
  simp only [C.coord_source, CyclicHullData.pairCross,
    CyclicHullData.pairSub, alignedComplex, Erdos957Cases13.toComplex,
    cCross, Complex.mul_re, Complex.mul_im, Prod.fst, Prod.snd, sub_zero]
    at hcq hcr ⊢
  rw [hcq, hcr]
  ring

/-- Aligned-chart version of the two-extreme rigidity theorem.  It allows
the middle neighbor to be selected in the same honest bisector chart used
by locality, with no identification with `P.localCoord`. -/
theorem source_adj_incidentCyclicVertex_of_middle_adj_aligned
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle c : Vertex A)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (C.coord source middle))
    (hcIncident : IsIncidentCyclicVertex P source c)
    (hm : (unitDistanceGraph A).Adj middle c) :
    (unitDistanceGraph A).Adj source.1 c := by
  obtain ⟨q₀, q₂, hsource₀, hsource₂, harg₀, harg₂⟩ :=
    exists_outer_source_neighbors_aligned hA P C source middle hstrict
      hdegree hsourceMiddle hmiddleCone
  have hq₀Middle : q₀ ≠ middle := by
    intro h
    subst q₀
    exact (lt_irrefl (alignedComplex P C source middle).arg) harg₀
  have hmiddleq₂ : middle ≠ q₂ := by
    intro h
    subst q₂
    exact (lt_irrefl (alignedComplex P C source middle).arg) harg₂
  have hcSource : c ≠ source.1 := by
    rcases hcIncident with hc | hc
    · rw [hc]
      intro h
      apply P.prev_ne_self source
      apply Subtype.ext
      exact h
    · rw [hc]
      intro h
      apply P.next_ne_self source
      apply Subtype.ext
      exact h
  have hcrossAmbient :
      0 ≤ cross ((c : ComplexPoint) - source.1.1)
            ((q₀ : ComplexPoint) - source.1.1) *
          cross ((c : ComplexPoint) - source.1.1)
            ((q₂ : ComplexPoint) - source.1.1) := by
    rcases hcIncident with hc | hc
    · rw [hc]
      have h₀ := P.edge_support (P.next⁻¹ source) q₀
      have h₂ := P.edge_support (P.next⁻¹ source) q₂
      have hnextPrev : P.next (P.next⁻¹ source) = source := by simp
      rw [hnextPrev] at h₀ h₂
      have h₀' :
          cross (((P.next⁻¹ source).1.1 : ComplexPoint) - source.1.1)
              ((q₀ : ComplexPoint) - source.1.1) ≤ 0 := by
        simp only [cross] at h₀ ⊢
        simp only [WithLp.ofLp_sub, Pi.sub_apply] at h₀ ⊢
        nlinarith
      have h₂' :
          cross (((P.next⁻¹ source).1.1 : ComplexPoint) - source.1.1)
              ((q₂ : ComplexPoint) - source.1.1) ≤ 0 := by
        simp only [cross] at h₂ ⊢
        simp only [WithLp.ofLp_sub, Pi.sub_apply] at h₂ ⊢
        nlinarith
      exact mul_nonneg_of_nonpos_of_nonpos h₀' h₂'
    · rw [hc]
      exact mul_nonneg (P.edge_support source q₀) (P.edge_support source q₂)
  have hcrossLocal :
      0 ≤ cCross (alignedComplex P C source c)
          (alignedComplex P C source q₀) *
        cCross (alignedComplex P C source c)
          (alignedComplex P C source q₂) := by
    rw [aligned_cross_product_eq_ambient_cross_product]
    exact hcrossAmbient
  have hcNorm : ‖alignedComplex P C source c‖ = 1 := by
    apply norm_eq_one_of_middle_common_and_outer_support
        (z₀ := alignedComplex P C source q₀)
        (m := alignedComplex P C source middle)
        (z₂ := alignedComplex P C source q₂)
        (c := alignedComplex P C source c)
    · exact alignedComplex_norm_of_adj P C source hsource₀
    · exact alignedComplex_norm_of_adj P C source hsourceMiddle
    · exact alignedComplex_norm_of_adj P C source hsource₂
    · exact ⟨by simpa [alignedComplex, Erdos957Cases13.toComplex] using
          hstrict q₀ hsource₀.ne.symm,
        by simpa [alignedComplex, Erdos957Cases13.toComplex] using
          hstrict middle hsourceMiddle.ne.symm,
        by simpa [alignedComplex, Erdos957Cases13.toComplex] using
          hstrict q₂ hsource₂.ne.symm,
        by simpa [alignedComplex, Erdos957Cases13.toComplex] using
          hstrict c hcSource⟩
    · exact ⟨harg₀, harg₂⟩
    · exact alignedComplex_one_le_norm_sub hA P C source hq₀Middle
    · exact alignedComplex_one_le_norm_sub hA P C source hmiddleq₂
    · exact alignedComplex_one_le_norm hA P C source hcSource
    · exact alignedComplex_norm_sub_of_adj P C source hm.symm
    · exact hcrossLocal
  have hlocalSq : Erdos957Cases13.sqDist Erdos957Cases13.origin
      (C.coord source c) = 1 := by
    apply (Erdos957Cases13.sqDist_eq_one_iff_dist_eq_one
      Erdos957Cases13.origin (C.coord source c)).mpr
    change dist 0 (alignedComplex P C source c) = 1
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hcNorm
  change dist (source.1 : ComplexPoint) c = 1
  change Erdos957Cases13.sqDist (0, 0) (C.coord source c) = 1 at hlocalSq
  rw [← C.coord_source source, C.sqDist_coord] at hlocalSq
  nlinarith [(dist_nonneg : 0 ≤ dist (source.1 : ComplexPoint) c)]

/-- Equilateral wrapper retaining all three actual graph edges. -/
theorem equilateral_source_middle_incidentCyclicVertex_aligned
    {A : Finset ComplexPoint} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle c : Vertex A)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : Erdos957Cases13.InOpenMiddleCone
      (C.coord source middle))
    (hcIncident : IsIncidentCyclicVertex P source c)
    (hm : (unitDistanceGraph A).Adj middle c) :
    (unitDistanceGraph A).Adj source.1 middle ∧
      (unitDistanceGraph A).Adj middle c ∧
      (unitDistanceGraph A).Adj source.1 c := by
  exact ⟨hsourceMiddle, hm,
    source_adj_incidentCyclicVertex_of_middle_adj_aligned hA P C source
      middle c hstrict hdegree hsourceMiddle hmiddleCone hcIncident hm⟩

end Erdos957TwoExtremeFrame
