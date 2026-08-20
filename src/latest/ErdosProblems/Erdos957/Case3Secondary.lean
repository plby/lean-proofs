import ErdosProblems.Erdos957.GeometryCore
import ErdosProblems.Erdos957.Case3General

/-! # The realized secondary recipient in Case 3 of Erdős 957 -/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace Erdos957Case3Secondary

open Erdos957Cases13
open Erdos957GeometryCore

abbrev ComplexPoint := Erdos957GeometryCore.Point
abbrev Point := Erdos957Cases13.Point

private lemma toComplex_injective : Function.Injective toComplex := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg Complex.re hpq
  · exact congrArg Complex.im hpq

private def complexConfiguration {A : Finset ComplexPoint}
    {P : CyclicHullData A} (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) : Finset ℂ :=
  (C.configuration P source).image toComplex

private lemma complexConfiguration_oneSeparated
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) :
    Erdos957Angle.IsOneSeparated (complexConfiguration C source) := by
  intro x hx y hy hxy
  rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨q, hq, rfl⟩
  have hpq : p ≠ q := fun h ↦ hxy (congrArg toComplex h)
  exact (one_le_sqDist_iff_one_le_dist p q).mp
    (C.configuration_oneSeparated P hA source p hp q hq hpq)

private lemma card_lower_middle_neighbors_le_three
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle : Vertex A) :
    (((unitDistanceGraph A).neighborFinset middle).filter fun q ↦
      (C.coord source q).2 < (C.coord source middle).2).card ≤ 3 := by
  classical
  let N := (unitDistanceGraph A).neighborFinset middle
  let L := N.filter fun q ↦
    (C.coord source q).2 < (C.coord source middle).2
  let Z := complexConfiguration C source
  let p := toComplex (C.coord source middle)
  let f : L → Erdos957Angle.lowerUnitNeighbors Z p := fun q ↦
    ⟨toComplex (C.coord source q), by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_image.mpr
            ⟨C.coord source q, C.coord_mem_configuration P source q, rfl⟩
        · have hadj : (unitDistanceGraph A).Adj middle q :=
            (SimpleGraph.mem_neighborFinset
              (G := unitDistanceGraph A) (v := middle) q).mp
              (Finset.mem_filter.mp q.property).1
          apply (sqDist_eq_one_iff_dist_eq_one
            (C.coord source middle) (C.coord source q)).mp
          rw [C.sqDist_coord, hadj]
          norm_num
      · simpa [p, toComplex] using (Finset.mem_filter.mp q.property).2⟩
  have hf : Function.Injective f := by
    rintro ⟨q, hq⟩ ⟨r, hr⟩ hqr
    simp only [f, Subtype.mk.injEq] at hqr ⊢
    exact C.coord_injective P source
      (toComplex_injective (congrArg Subtype.val hqr))
  have hcard := Fintype.card_le_of_injective f hf
  have hcard' : L.card ≤
      (Erdos957Angle.lowerUnitNeighbors Z p).card := by
    simpa only [Fintype.card_coe] using hcard
  have hlower := Erdos957Angle.card_lowerUnitNeighbors_le_three
    (complexConfiguration_oneSeparated hA C source)
    (toComplex (C.coord source middle))
  change L.card ≤ 3
  exact hcard'.trans (by simpa only [Z, p] using hlower)

private lemma exists_nonlower_middle_neighbor_ne_source
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (C.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 5) :
    ∃ t : Vertex A,
      (unitDistanceGraph A).Adj middle t ∧ t ≠ source.1 ∧
        (C.coord source middle).2 ≤ (C.coord source t).2 := by
  classical
  let N := (unitDistanceGraph A).neighborFinset middle
  let L := N.filter fun q ↦
    (C.coord source q).2 < (C.coord source middle).2
  let U := N \ L
  have hcardN : N.card = 5 := by
    change ((unitDistanceGraph A).neighborFinset middle).card = 5
    rw [← SimpleGraph.degree]
    exact hmiddleDegree
  have hcardL : L.card ≤ 3 :=
    card_lower_middle_neighbors_le_three hA C source middle
  have hLsub : L ⊆ N := Finset.filter_subset _ _
  have hcardU : U.card = N.card - L.card := by
    simpa [U, Finset.inter_eq_left.mpr hLsub] using
      (Finset.card_sdiff (s := L) (t := N))
  have hUlarge : 1 < U.card := by omega
  obtain ⟨a, haU, b, hbU, hab⟩ := Finset.one_lt_card.mp hUlarge
  have choose_a_or_b : a ≠ source.1 ∨ b ≠ source.1 := by
    by_contra h
    push_neg at h
    exact hab (h.1.trans h.2.symm)
  rcases choose_a_or_b with ha | hb
  · refine ⟨a, ?_, ha, ?_⟩
    · exact (SimpleGraph.mem_neighborFinset
        (G := unitDistanceGraph A) (v := middle) a).mp
        (Finset.mem_sdiff.mp haU).1
    · have hnot := (Finset.mem_sdiff.mp haU).2
      have : ¬(C.coord source a).2 < (C.coord source middle).2 := by
        intro hlt
        exact hnot (Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp haU).1, hlt⟩)
      exact le_of_not_gt this
  · refine ⟨b, ?_, hb, ?_⟩
    · exact (SimpleGraph.mem_neighborFinset
        (G := unitDistanceGraph A) (v := middle) b).mp
        (Finset.mem_sdiff.mp hbU).1
    · have hnot := (Finset.mem_sdiff.mp hbU).2
      have : ¬(C.coord source b).2 < (C.coord source middle).2 := by
        intro hlt
        exact hnot (Finset.mem_filter.mpr
          ⟨(Finset.mem_sdiff.mp hbU).1, hlt⟩)
      exact le_of_not_gt this

private lemma phaseBin_eq_one_of_unit_in_open_cone {v : Point}
    (hunit : sqDist origin v = 1) (hcone : InOpenMiddleCone v) :
    Erdos957Angle.phaseBin (toComplex v) = (1 : Fin 6) := by
  let z := toComplex v
  have him : z.im < 0 := by
    have hsqrt := sqrtThree_pos
    dsimp [InOpenMiddleCone] at hcone
    dsimp [z, toComplex]
    linarith
  have hnorm : ‖z‖ = 1 := by
    have hd := (sqDist_eq_one_iff_dist_eq_one origin v).mp hunit
    change dist 0 z = 1 at hd
    simpa only [dist_eq_norm, zero_sub, norm_neg] using hd
  have hxy : v.1 ^ 2 + v.2 ^ 2 = 1 := by
    simpa [sqDist, origin] using hunit
  have habs : |sqrtThree * v.1| < -v.2 := by
    rw [abs_lt]
    dsimp [InOpenMiddleCone] at hcone
    constructor <;> linarith
  have hminusNonneg : 0 ≤ -v.2 :=
    le_of_lt (lt_of_le_of_lt (abs_nonneg _) habs)
  have hsquare : (sqrtThree * v.1) ^ 2 < (-v.2) ^ 2 := by
    have h := (sq_lt_sq₀ (abs_nonneg (sqrtThree * v.1)) hminusNonneg).2 habs
    simpa only [sq_abs] using h
  have hsqrtSq := sqrtThree_sq
  have hxlo : -(1 / 2 : ℝ) < v.1 := by
    nlinarith [sq_nonneg (v.1 + 1 / 2)]
  have hxhi : v.1 < (1 / 2 : ℝ) := by
    nlinarith [sq_nonneg (v.1 - 1 / 2)]
  have harg : z.arg = -Real.arccos v.1 := by
    rw [Complex.arg_of_im_neg him, hnorm]
    norm_num [z, toComplex]
  have hxmem : v.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith
  have harccosLower : Real.pi / 3 < Real.arccos v.1 := by
    have h := Real.arccos_lt_arccos hxmem.1 hxhi
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hhalf : Real.arccos (1 / 2 : ℝ) = Real.pi / 3 := by
      rw [← Real.cos_pi_div_three, Real.arccos_cos] <;>
        nlinarith [Real.pi_pos]
    rwa [hhalf] at h
  have harccosUpper : Real.arccos v.1 < 2 * Real.pi / 3 := by
    have hxlo' : (-1 / 2 : ℝ) < v.1 := by linarith
    have h := Real.arccos_lt_arccos
      (by norm_num : (-1 : ℝ) ≤ -1 / 2) hxlo' hxmem.2
    have hhalf : Real.arccos (-1 / 2 : ℝ) = 2 * Real.pi / 3 := by
      rw [show (-1 / 2 : ℝ) = Real.cos (2 * Real.pi / 3) by
        rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]
        ring,
        Real.arccos_cos] <;> nlinarith [Real.pi_pos]
    rwa [hhalf] at h
  have hargBounds : -(2 * Real.pi / 3) < z.arg ∧
      z.arg < -(Real.pi / 3) := by
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

private def chartComplex {A : Finset ComplexPoint} {P : CyclicHullData A}
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (q : Vertex A) : ℂ := toComplex (C.coord source q)

private lemma chartComplex_norm_of_adj {A : Finset ComplexPoint}
    {P : CyclicHullData A} (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) {q : Vertex A}
    (hq : (unitDistanceGraph A).Adj source.1 q) :
    ‖chartComplex C source q‖ = 1 := by
  have hsquare : sqDist origin (C.coord source q) = 1 := by
    change sqDist (0, 0) (C.coord source q) = 1
    rw [← C.coord_source source, C.sqDist_coord, hq]
    norm_num
  have hd := (sqDist_eq_one_iff_dist_eq_one origin
    (C.coord source q)).mp hsquare
  change dist 0 (chartComplex C source q) = 1 at hd
  simpa only [dist_eq_norm, zero_sub, norm_neg] using hd

private lemma chartComplex_one_le_norm_sub {A : Finset ComplexPoint}
    {P : CyclicHullData A} (hA : IsOneSeparated A)
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    {q r : Vertex A} (hqr : q ≠ r) :
    1 ≤ ‖chartComplex C source q - chartComplex C source r‖ := by
  have hdist := hA q q.property r r.property (fun h ↦ hqr (Subtype.ext h))
  have hsquare : 1 ≤ sqDist (C.coord source q) (C.coord source r) := by
    rw [C.sqDist_coord]
    nlinarith [(dist_nonneg : 0 ≤ dist (q : ComplexPoint) r)]
  have hd := (one_le_sqDist_iff_one_le_dist
    (C.coord source q) (C.coord source r)).mp hsquare
  simpa only [chartComplex, dist_eq_norm] using hd

private theorem exists_outer_source_neighbors_aligned
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0)
    (hdegree : (unitDistanceGraph A).degree source.1 = 3)
    (hmiddleAdj : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (C.coord source middle)) :
    ∃ q₀ q₂ : Vertex A,
      (unitDistanceGraph A).Adj source.1 q₀ ∧
      (unitDistanceGraph A).Adj source.1 q₂ ∧
      Erdos957Angle.phaseBin (chartComplex C source q₀) = (0 : Fin 6) ∧
      Erdos957Angle.phaseBin (chartComplex C source q₂) = (2 : Fin 6) ∧
      (chartComplex C source q₀).arg <
        (chartComplex C source middle).arg ∧
      (chartComplex C source middle).arg <
        (chartComplex C source q₂).arg := by
  classical
  let N := (unitDistanceGraph A).neighborFinset source.1
  let z : Vertex A → ℂ := chartComplex C source
  have hneSource {q : Vertex A} (hq : q ∈ N) : q ≠ source.1 := by
    intro h
    subst q
    exact (SimpleGraph.notMem_neighborFinset_self
      (G := unitDistanceGraph A) (v := source.1)) hq
  have him {q : Vertex A} (hq : q ∈ N) : (z q).im < 0 := by
    simpa [z, chartComplex, toComplex] using hstrict q (hneSource hq)
  have hnorm {q : Vertex A} (hq : q ∈ N) : ‖z q‖ = 1 := by
    apply chartComplex_norm_of_adj C source
    exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) q).mp hq
  have hsep {q r : Vertex A} (hq : q ∈ N) (hr : r ∈ N) (hqr : q ≠ r) :
      1 ≤ ‖z q - z r‖ :=
    chartComplex_one_le_norm_sub hA C source hqr
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
        change sqDist (0, 0) (C.coord source middle) = 1
        rw [← C.coord_source source, C.sqDist_coord, hmiddleAdj]
        norm_num)
      hmiddleCone
  have hphase₀ : Erdos957Angle.principalPhase (z q₀) = (z q₀).arg := by
    have harg : (z q₀).arg < 0 := Complex.arg_neg_iff.mpr (him q₀.property)
    simp [Erdos957Angle.principalPhase, ne_of_lt (harg.trans Real.pi_pos)]
  have hphaseMiddle : Erdos957Angle.principalPhase (z middle) =
      (z middle).arg := by
    have harg : (z middle).arg < 0 := Complex.arg_neg_iff.mpr (him hmiddleN)
    simp [Erdos957Angle.principalPhase, ne_of_lt (harg.trans Real.pi_pos)]
  have hphase₂ : Erdos957Angle.principalPhase (z q₂) = (z q₂).arg := by
    have harg : (z q₂).arg < 0 := Complex.arg_neg_iff.mpr (him q₂.property)
    simp [Erdos957Angle.principalPhase, ne_of_lt (harg.trans Real.pi_pos)]
  have hb₀ := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin₀
  have hbMiddle := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbinMiddle
  have hb₂ := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin₂
  norm_num at hb₀ hbMiddle hb₂
  rw [hphase₀] at hb₀
  rw [hphaseMiddle] at hbMiddle
  rw [hphase₂] at hb₂
  refine ⟨q₀, q₂, ?_, ?_, hbin₀, hbin₂, ?_, ?_⟩
  · exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) q₀).mp q₀.property
  · exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := source.1) q₂).mp q₂.property
  · change (z q₀).arg < (z middle).arg
    linarith
  · change (z middle).arg < (z q₂).arg
    linarith

private def pairDot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2
private def pairCross (p q : Point) : ℝ := p.1 * q.2 - p.2 * q.1

private def complexCross (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

private lemma complexCross_eq_norm_mul_sin_sub (z w : ℂ) :
    complexCross z w = ‖z‖ * ‖w‖ * Real.sin (w.arg - z.arg) := by
  simp only [complexCross]
  rw [Real.sin_sub, mul_sub]
  rw [← Complex.norm_mul_cos_arg z, ← Complex.norm_mul_sin_arg z,
    ← Complex.norm_mul_cos_arg w, ← Complex.norm_mul_sin_arg w]
  ring

private lemma pairCross_eq_norm_mul_sin_sub (p q : Point) :
    pairCross p q = ‖toComplex p‖ * ‖toComplex q‖ *
      Real.sin ((toComplex q).arg - (toComplex p).arg) := by
  change complexCross (toComplex p) (toComplex q) = _
  exact complexCross_eq_norm_mul_sin_sub _ _

private lemma pairCross_pos_of_arg_lt {p q : Point}
    (hp : toComplex p ≠ 0) (hq : toComplex q ≠ 0)
    (hpim : p.2 < 0) (hqim : q.2 < 0)
    (hpq : (toComplex p).arg < (toComplex q).arg) :
    0 < pairCross p q := by
  rw [pairCross_eq_norm_mul_sin_sub]
  have hdiffpos : 0 < (toComplex q).arg - (toComplex p).arg :=
    sub_pos.mpr hpq
  have hdiffpi : (toComplex q).arg - (toComplex p).arg < Real.pi := by
    have hparg := Complex.neg_pi_lt_arg (toComplex p)
    have hqarg : (toComplex q).arg < 0 :=
      Complex.arg_neg_iff.mpr (by simpa [toComplex] using hqim)
    linarith
  exact mul_pos (mul_pos (norm_pos_iff.mpr hp) (norm_pos_iff.mpr hq))
    (Real.sin_pos_of_pos_of_lt_pi hdiffpos hdiffpi)

private lemma pairCross_neg_of_arg_lt {p q : Point}
    (hp : toComplex p ≠ 0) (hq : toComplex q ≠ 0)
    (hpim : p.2 < 0) (hqim : q.2 < 0)
    (hqp : (toComplex q).arg < (toComplex p).arg) :
    pairCross p q < 0 := by
  rw [pairCross_eq_norm_mul_sin_sub]
  have hdiffneg : (toComplex q).arg - (toComplex p).arg < 0 :=
    sub_neg.mpr hqp
  have hdiffpi : -Real.pi <
      (toComplex q).arg - (toComplex p).arg := by
    have hqarg := Complex.neg_pi_lt_arg (toComplex q)
    have hparg : (toComplex p).arg < 0 :=
      Complex.arg_neg_iff.mpr (by simpa [toComplex] using hpim)
    linarith
  exact mul_neg_of_pos_of_neg
    (mul_pos (norm_pos_iff.mpr hp) (norm_pos_iff.mpr hq))
    (Real.sin_neg_of_neg_of_neg_pi_lt hdiffneg hdiffpi)

private lemma fst_pos_of_phaseBin_two_of_snd_neg {q : Point}
    (hqim : q.2 < 0)
    (hbin : Erdos957Angle.phaseBin (toComplex q) = (2 : Fin 6)) :
    0 < q.1 := by
  have hphase : Erdos957Angle.principalPhase (toComplex q) =
      (toComplex q).arg := by
    have harg : (toComplex q).arg < 0 :=
      Complex.arg_neg_iff.mpr (by simpa [toComplex] using hqim)
    simp [Erdos957Angle.principalPhase, ne_of_lt (harg.trans Real.pi_pos)]
  have hb := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin
  norm_num at hb
  rw [hphase] at hb
  have hargLower : -(Real.pi / 2) < (toComplex q).arg := by
    nlinarith [Real.pi_pos]
  rcases Complex.neg_pi_div_two_lt_arg_iff.mp hargLower with h | h
  · simpa [toComplex] using h
  · have : ¬0 ≤ (toComplex q).im := by
      simpa [toComplex] using not_le.mpr hqim
    exact (this h).elim

private lemma fst_neg_of_phaseBin_zero_of_snd_neg {q : Point}
    (hqim : q.2 < 0)
    (hbin : Erdos957Angle.phaseBin (toComplex q) = (0 : Fin 6)) :
    q.1 < 0 := by
  have hphase : Erdos957Angle.principalPhase (toComplex q) =
      (toComplex q).arg := by
    have harg : (toComplex q).arg < 0 :=
      Complex.arg_neg_iff.mpr (by simpa [toComplex] using hqim)
    simp [Erdos957Angle.principalPhase, ne_of_lt (harg.trans Real.pi_pos)]
  have hb := Erdos957Angle.principalPhase_bounds_of_phaseBin_eq hbin
  norm_num at hb
  rw [hphase] at hb
  by_contra hnot
  have hqre : 0 ≤ (toComplex q).re := by
    simpa [toComplex] using le_of_not_gt hnot
  have hargLower : -(Real.pi / 2) ≤ (toComplex q).arg :=
    Complex.neg_pi_div_two_le_arg_iff.mpr (Or.inl hqre)
  nlinarith [Real.pi_pos]

private lemma cross_lower_right_upper_right_pos
    {q r : Point} (hqx : 0 < q.1) (hqy : q.2 < 0)
    (hrx : 0 ≤ r.1) (hry : 0 ≤ r.2)
    (hrunit : r.1 ^ 2 + r.2 ^ 2 = 1) :
    0 < pairCross q r := by
  by_cases hrxzero : r.1 = 0
  · have hrypos : 0 < r.2 := by nlinarith
    simp only [pairCross]
    nlinarith [mul_pos hqx hrypos]
  · have hrxpos : 0 < r.1 := lt_of_le_of_ne hrx (Ne.symm hrxzero)
    have hright : 0 < (-q.2) * r.1 :=
      mul_pos (neg_pos.mpr hqy) hrxpos
    have hleft : 0 ≤ q.1 * r.2 := mul_nonneg hqx.le hry
    simp only [pairCross]
    nlinarith

private lemma common_unit_height_ne_of_middle_cone
    {m q : Point} (hm : sqDist origin m = 1)
    (hq : sqDist origin q = 1) (hmq : sqDist m q = 1)
    (hcone : InOpenMiddleCone m) : m.2 ≠ q.2 := by
  intro heq
  have hm' : m.1 ^ 2 + m.2 ^ 2 = 1 := by
    simpa [sqDist, origin] using hm
  have hq' : q.1 ^ 2 + q.2 ^ 2 = 1 := by
    simpa [sqDist, origin] using hq
  have hmq' : (m.1 - q.1) ^ 2 + (m.2 - q.2) ^ 2 = 1 := by
    simpa [sqDist] using hmq
  rcases hcone with ⟨hconeRight, hconeLeft⟩
  have hmy : m.2 < 0 := by linarith
  have hsqEq : q.1 ^ 2 = m.1 ^ 2 := by nlinarith
  have hmxsq : m.1 ^ 2 = 1 / 4 := by
    rcases eq_or_eq_neg_of_sq_eq_sq q.1 m.1 hsqEq with hsame | hopp
    · rw [hsame, heq] at hmq'
      norm_num at hmq'
    · rw [hopp, heq] at hmq'
      nlinarith
  have hmysq : m.2 ^ 2 = 3 / 4 := by nlinarith
  by_cases hmx : 0 ≤ m.1
  · have hleft : 0 ≤ sqrtThree * m.1 :=
      mul_nonneg sqrtThree_pos.le hmx
    have hsquare : (sqrtThree * m.1) ^ 2 < (-m.2) ^ 2 :=
      (sq_lt_sq₀ hleft (neg_nonneg.mpr hmy.le)).mpr hconeRight
    rw [mul_pow, sqrtThree_sq] at hsquare
    nlinarith
  · have hmxneg : m.1 < 0 := lt_of_not_ge hmx
    have hleft : 0 ≤ -sqrtThree * m.1 := by
      exact mul_nonneg_of_nonpos_of_nonpos
        (neg_nonpos.mpr sqrtThree_pos.le) hmxneg.le
    have hsquare : (-sqrtThree * m.1) ^ 2 < (-m.2) ^ 2 :=
      (sq_lt_sq₀ hleft (neg_nonneg.mpr hmy.le)).mpr hconeLeft
    rw [mul_pow, neg_sq, sqrtThree_sq] at hsquare
    nlinarith

private lemma cross_sq_add_dot_sq (p q : Point) :
    pairCross p q ^ 2 + pairDot p q ^ 2 =
      (p.1 ^ 2 + p.2 ^ 2) * (q.1 ^ 2 + q.2 ^ 2) := by
  simp only [pairCross, pairDot]
  ring

private lemma cross_third_eq_of_unit (m q r : Point)
    (hm : m.1 ^ 2 + m.2 ^ 2 = 1) :
    pairCross q r =
      pairDot m q * pairCross m r - pairCross m q * pairDot m r := by
  simp only [pairCross, pairDot]
  calc
    q.1 * r.2 - q.2 * r.1 =
        (m.1 ^ 2 + m.2 ^ 2) * (q.1 * r.2 - q.2 * r.1) := by
      rw [hm]
      ring
    _ = (m.1 * q.1 + m.2 * q.2) * (m.1 * r.2 - m.2 * r.1) -
        (m.1 * q.2 - m.2 * q.1) * (m.1 * r.1 + m.2 * r.2) := by ring

private lemma dot_lt_of_three_positive_crosses
    {m q r : Point}
    (hm : m.1 ^ 2 + m.2 ^ 2 = 1)
    (hq : q.1 ^ 2 + q.2 ^ 2 = 1)
    (hr : r.1 ^ 2 + r.2 ^ 2 = 1)
    (hmq : 0 < pairCross m q)
    (hmr : 0 < pairCross m r)
    (hqr : 0 < pairCross q r) :
    pairDot m r < pairDot m q := by
  let A := pairDot m q
  let B := pairDot m r
  let F := pairCross m q
  let G := pairCross m r
  have hF : 0 < F := hmq
  have hG : 0 < G := hmr
  have hFrel : F ^ 2 + A ^ 2 = 1 := by
    simpa [A, F, hm, hq] using cross_sq_add_dot_sq m q
  have hGrel : G ^ 2 + B ^ 2 = 1 := by
    simpa [B, G, hm, hr] using cross_sq_add_dot_sq m r
  have hcross : 0 < A * G - F * B := by
    rw [cross_third_eq_of_unit m q r hm] at hqr
    simpa [A, B, F, G] using hqr
  by_contra hnot
  have hAB : A ≤ B := le_of_not_gt hnot
  by_cases hB : 0 ≤ B
  · have hA : 0 < A := by
      by_contra hA'
      have hAle : A ≤ 0 := le_of_not_gt hA'
      have hAG : A * G ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hAle hG.le
      have hFB : 0 ≤ F * B := mul_nonneg hF.le hB
      have : A * G - F * B ≤ 0 := by linarith
      linarith
    have hBFnonneg : 0 ≤ B * F := mul_nonneg hB hF.le
    have hAGpos : 0 < A * G := mul_pos hA hG
    have hsquares : (B * F) ^ 2 < (A * G) ^ 2 := by nlinarith
    have hsq : B ^ 2 < A ^ 2 := by
      nlinarith [mul_pow B F 2, mul_pow A G 2]
    nlinarith
  · have hBneg : B < 0 := lt_of_not_ge hB
    have hAneg : A < 0 := lt_of_le_of_lt hAB hBneg
    have hnegAG : 0 < (-A) * G := mul_pos (neg_pos.mpr hAneg) hG
    have hnegBF : 0 < (-B) * F := mul_pos (neg_pos.mpr hBneg) hF
    have hprod : (-A) * G < (-B) * F := by nlinarith
    have hsquares : ((-A) * G) ^ 2 < ((-B) * F) ^ 2 := by nlinarith
    have hsq : A ^ 2 < B ^ 2 := by
      nlinarith [mul_pow (-A) G 2, mul_pow (-B) F 2]
    nlinarith

private lemma ordered_unit_arc_closeness
    {m q r : Point}
    (hm : m.1 ^ 2 + m.2 ^ 2 = 1)
    (hq : q.1 ^ 2 + q.2 ^ 2 = 1)
    (hr : r.1 ^ 2 + r.2 ^ 2 = 1)
    (hmq : 0 < pairCross m q)
    (hmr : 0 < pairCross m r)
    (hqr : 0 < pairCross q r) :
    sqDist q (m.1 + r.1, m.2 + r.2) < 1 := by
  let A := pairDot m q
  let B := pairDot m r
  let F := pairCross m q
  let G := pairCross m r
  have hAB : B < A :=
    dot_lt_of_three_positive_crosses hm hq hr hmq hmr hqr
  have hF : 0 < F := hmq
  have hG : 0 < G := hmr
  have hFrel : F ^ 2 + A ^ 2 = 1 := by
    simpa [A, F, hm, hq] using cross_sq_add_dot_sq m q
  have hGrel : G ^ 2 + B ^ 2 = 1 := by
    simpa [B, G, hm, hr] using cross_sq_add_dot_sq m r
  have hAOne : A < 1 := by nlinarith
  have hBOne : -1 < B := by nlinarith
  have hfactorPos : 0 < (1 - A) * (1 + B) :=
    mul_pos (sub_pos.mpr hAOne) (by linarith)
  have hsquareIdentity :
      (F * G) ^ 2 - ((1 - A) * (1 + B)) ^ 2 =
        2 * (A - B) * (1 - A) * (1 + B) := by
    calc
      (F * G) ^ 2 - ((1 - A) * (1 + B)) ^ 2 =
          (1 - A ^ 2) * (1 - B ^ 2) -
            ((1 - A) * (1 + B)) ^ 2 := by
        have hFsq : F ^ 2 = 1 - A ^ 2 := by linarith
        have hGsq : G ^ 2 = 1 - B ^ 2 := by linarith
        rw [mul_pow, hFsq, hGsq]
      _ = 2 * (A - B) * (1 - A) * (1 + B) := by ring
  have hsquares : ((1 - A) * (1 + B)) ^ 2 < (F * G) ^ 2 := by
    have hrhs : 0 < 2 * (A - B) * (1 - A) * (1 + B) := by
      exact mul_pos
        (mul_pos (mul_pos (by norm_num) (sub_pos.mpr hAB))
          (sub_pos.mpr hAOne)) (by linarith)
    linarith [hsquareIdentity]
  have hproduct : (1 - A) * (1 + B) < F * G := by
    nlinarith [mul_pos hF hG]
  have hdotQR : pairDot q r = A * B + F * G := by
    have hcross := cross_third_eq_of_unit m q r hm
    have hdotIdentity :
        pairDot q r * (m.1 ^ 2 + m.2 ^ 2) =
          pairDot m q * pairDot m r + pairCross m q * pairCross m r := by
      simp only [pairDot, pairCross]
      ring
    rw [hm, mul_one] at hdotIdentity
    simpa [A, B, F, G] using hdotIdentity
  dsimp [A, B, F, G, pairDot, pairCross] at hproduct hdotQR
  simp only [sqDist]
  nlinarith

private lemma cross_middle_upper_right_pos
    {m r : Point}
    (hm : m.1 ^ 2 + m.2 ^ 2 = 1)
    (hcone : InOpenMiddleCone m)
    (hr : r.1 ^ 2 + r.2 ^ 2 = 1)
    (hrx : 0 ≤ r.1) (hry : 0 ≤ r.2)
    (haway : -(1 / 2 : ℝ) ≤ pairDot m r) :
    0 < pairCross m r := by
  rcases hcone with ⟨hconeRight, hconeLeft⟩
  have hmy : m.2 < 0 := by linarith
  by_contra hnot
  have hcross : pairCross m r ≤ 0 := le_of_not_gt hnot
  by_cases hmx : 0 ≤ m.1
  · have hterm₁ : 0 ≤ m.1 * r.2 := mul_nonneg hmx hry
    have hterm₂ : 0 ≤ (-m.2) * r.1 :=
      mul_nonneg (neg_nonneg.mpr hmy.le) hrx
    have hterm₁zero : m.1 * r.2 = 0 := by
      simp only [pairCross] at hcross
      nlinarith
    have hterm₂zero : (-m.2) * r.1 = 0 := by
      simp only [pairCross] at hcross
      nlinarith
    have hrxzero : r.1 = 0 :=
      (mul_eq_zero.mp hterm₂zero).resolve_left (neg_ne_zero.mpr (ne_of_lt hmy))
    have hrypos : 0 < r.2 := by nlinarith
    have hmxzero : m.1 = 0 :=
      (mul_eq_zero.mp hterm₁zero).resolve_right (ne_of_gt hrypos)
    simp only [pairDot] at haway
    nlinarith
  · have hmxneg : m.1 < 0 := lt_of_not_ge hmx
    let a : ℝ := -m.1
    let b : ℝ := -m.2
    have ha : 0 ≤ a := (neg_pos.mpr hmxneg).le
    have hb : 0 ≤ b := (neg_pos.mpr hmy).le
    have hab : a ^ 2 + b ^ 2 = 1 := by
      dsimp [a, b]
      nlinarith
    have hbru : b * r.1 ≤ a * r.2 := by
      dsimp [a, b]
      simp only [pairCross] at hcross
      linarith
    have hleftNonneg : 0 ≤ b * r.1 := mul_nonneg hb hrx
    have hrightNonneg : 0 ≤ a * r.2 := mul_nonneg ha hry
    have hsquare : (b * r.1) ^ 2 ≤ (a * r.2) ^ 2 :=
      (sq_le_sq₀ hleftNonneg hrightNonneg).mpr hbru
    have hbSqLe : b ^ 2 ≤ r.2 ^ 2 := by
      calc
        b ^ 2 = b ^ 2 * (r.1 ^ 2 + r.2 ^ 2) := by rw [hr]; ring
        _ ≤ a ^ 2 * r.2 ^ 2 + b ^ 2 * r.2 ^ 2 := by
          nlinarith [mul_pow b r.1 2, mul_pow a r.2 2]
        _ = (a ^ 2 + b ^ 2) * r.2 ^ 2 := by ring
        _ = r.2 ^ 2 := by rw [hab]; ring
    have hbLe : b ≤ r.2 := (sq_le_sq₀ hb hry).mp hbSqLe
    have hcone' : sqrtThree * a < b := by
      dsimp [a, b]
      nlinarith
    have hsa : 0 ≤ sqrtThree * a :=
      mul_nonneg sqrtThree_pos.le ha
    have hconeSq : (sqrtThree * a) ^ 2 < b ^ 2 :=
      (sq_lt_sq₀ hsa hb).mpr hcone'
    have hbLarge : 3 / 4 < b ^ 2 := by
      rw [mul_pow, sqrtThree_sq] at hconeSq
      nlinarith
    have hbr : b ^ 2 ≤ b * r.2 := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left hbLe hb
    have har : 0 ≤ a * r.1 := mul_nonneg ha hrx
    simp only [pairDot] at haway
    dsimp [a, b] at har hbr hbLarge
    nlinarith

/-- A five-valent Case-3 middle has a genuine second common neighbor with
the source, strictly above the middle in the same aligned chart. -/
theorem exists_case3_secondary_incidence_aligned
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0)
    (hsourceDegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (C.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 5) :
    ∃ secondary : Vertex A,
      (unitDistanceGraph A).Adj source.1 secondary ∧
      (unitDistanceGraph A).Adj middle secondary ∧
      (C.coord source middle).2 < (C.coord source secondary).2 := by
  classical
  obtain ⟨t, hmiddleT, htSource, hheight⟩ :=
    exists_nonlower_middle_neighbor_ne_source hA C source middle
      hsourceMiddle hmiddleCone hmiddleDegree
  obtain ⟨q₀, q₂, hsource₀, hsource₂, hbin₀, hbin₂,
      harg₀, harg₂⟩ :=
    exists_outer_source_neighbors_aligned hA C source middle hstrict
      hsourceDegree hsourceMiddle hmiddleCone
  let m : Point := C.coord source middle
  let tc : Point := C.coord source t
  let r : Point := (tc.1 - m.1, tc.2 - m.2)
  have hmiddleNe : middle ≠ source.1 := hsourceMiddle.ne.symm
  have hmUnit : sqDist origin m = 1 := by
    change sqDist (0, 0) (C.coord source middle) = 1
    rw [← C.coord_source source, C.sqDist_coord, hsourceMiddle]
    norm_num
  have hmNorm : m.1 ^ 2 + m.2 ^ 2 = 1 := by
    simpa [sqDist, origin] using hmUnit
  have hmIm : m.2 < 0 := by
    exact hstrict middle hmiddleNe
  have htUnit : sqDist m tc = 1 := by
    change sqDist (C.coord source middle) (C.coord source t) = 1
    rw [C.sqDist_coord, hmiddleT]
    norm_num
  have hrNorm : r.1 ^ 2 + r.2 ^ 2 = 1 := by
    simp only [sqDist] at htUnit
    dsimp [r]
    nlinarith
  have hry : 0 ≤ r.2 := by
    dsimp [r, tc, m]
    linarith
  have htAway : 1 ≤ sqDist origin tc := by
    rw [show origin = C.coord source source.1 by
      simpa [origin] using (C.coord_source source).symm]
    change 1 ≤ sqDist (C.coord source source.1) (C.coord source t)
    rw [C.sqDist_coord]
    have hd := hA source.1 source.1.property t t.property
      (fun h ↦ htSource (Subtype.ext h.symm))
    nlinarith [(dist_nonneg : 0 ≤ dist (source.1 : ComplexPoint) t)]
  have haway : -(1 / 2 : ℝ) ≤ pairDot m r := by
    simp only [sqDist] at htAway
    dsimp [origin, tc, m, r, pairDot] at htAway ⊢
    dsimp [m] at hmNorm
    nlinarith [hmNorm]
  have hmComplexNe : toComplex m ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [toComplex, Complex.zero_re, Complex.zero_im] at hre him
    nlinarith
  by_cases hrx : 0 ≤ r.1
  · let q : Point := C.coord source q₂
    have hqUnit : sqDist origin q = 1 := by
      change sqDist (0, 0) (C.coord source q₂) = 1
      rw [← C.coord_source source, C.sqDist_coord, hsource₂]
      norm_num
    have hqNorm : q.1 ^ 2 + q.2 ^ 2 = 1 := by
      simpa [sqDist, origin] using hqUnit
    have hqIm : q.2 < 0 := hstrict q₂ hsource₂.ne.symm
    have hqComplexNe : toComplex q ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [toComplex, Complex.zero_re, Complex.zero_im] at hre him
      nlinarith
    have hmq : 0 < pairCross m q := by
      apply pairCross_pos_of_arg_lt hmComplexNe hqComplexNe hmIm hqIm
      simpa [m, q, chartComplex] using harg₂
    have hmr : 0 < pairCross m r :=
      cross_middle_upper_right_pos hmNorm hmiddleCone hrNorm hrx hry haway
    have hqx : 0 < q.1 := by
      exact fst_pos_of_phaseBin_two_of_snd_neg hqIm
        (by simpa [q, chartComplex] using hbin₂)
    have hqr : 0 < pairCross q r :=
      cross_lower_right_upper_right_pos hqx hqIm hrx hry hrNorm
    have hclose : sqDist q tc < 1 := by
      have h := ordered_unit_arc_closeness hmNorm hqNorm hrNorm hmq hmr hqr
      simpa [m, tc, r, q] using h
    have hqt : q₂ = t := by
      by_contra hne
      have hd := hA q₂ q₂.property t t.property
        (fun h ↦ hne (Subtype.ext h))
      have hsquare : 1 ≤ sqDist q tc := by
        change 1 ≤ sqDist (C.coord source q₂) (C.coord source t)
        rw [C.sqDist_coord]
        simpa only [one_pow] using
          (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
            (dist_nonneg : 0 ≤ dist (q₂ : ComplexPoint) t)).mpr hd
      exact (not_lt_of_ge hsquare) hclose
    have hsourceT : (unitDistanceGraph A).Adj source.1 t := by
      simpa [hqt] using hsource₂
    have htSourceUnit : sqDist origin tc = 1 := by
      change sqDist (0, 0) (C.coord source t) = 1
      rw [← C.coord_source source, C.sqDist_coord, hsourceT]
      norm_num
    have hheightNe : m.2 ≠ tc.2 :=
      common_unit_height_ne_of_middle_cone hmUnit htSourceUnit htUnit hmiddleCone
    have hheightNe' : (C.coord source t).2 ≠
        (C.coord source middle).2 := by
      intro h
      apply hheightNe
      simpa [m, tc] using h.symm
    exact ⟨t, hsourceT, hmiddleT,
      lt_of_le_of_ne hheight hheightNe'.symm⟩
  · have hrx' : 0 ≤ -r.1 := by linarith
    let m' : Point := (-m.1, m.2)
    let q : Point := C.coord source q₀
    let q' : Point := (-q.1, q.2)
    let r' : Point := (-r.1, r.2)
    have hmNorm' : m'.1 ^ 2 + m'.2 ^ 2 = 1 := by
      simpa [m'] using hmNorm
    have hrNorm' : r'.1 ^ 2 + r'.2 ^ 2 = 1 := by
      simpa [r'] using hrNorm
    have hcone' : InOpenMiddleCone m' := by
      rcases hmiddleCone with ⟨hconeR, hconeL⟩
      constructor <;> dsimp [m'] <;> nlinarith
    have haway' : -(1 / 2 : ℝ) ≤ pairDot m' r' := by
      simpa [m', r', pairDot] using haway
    have hqUnit : sqDist origin q = 1 := by
      change sqDist (0, 0) (C.coord source q₀) = 1
      rw [← C.coord_source source, C.sqDist_coord, hsource₀]
      norm_num
    have hqNorm : q.1 ^ 2 + q.2 ^ 2 = 1 := by
      simpa [sqDist, origin] using hqUnit
    have hqNorm' : q'.1 ^ 2 + q'.2 ^ 2 = 1 := by
      simpa [q'] using hqNorm
    have hqIm : q.2 < 0 := hstrict q₀ hsource₀.ne.symm
    have hqComplexNe : toComplex q ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [toComplex, Complex.zero_re, Complex.zero_im] at hre him
      nlinarith
    have hmqNeg : pairCross m q < 0 := by
      apply pairCross_neg_of_arg_lt hmComplexNe hqComplexNe hmIm hqIm
      simpa [m, q, chartComplex] using harg₀
    have hmq' : 0 < pairCross m' q' := by
      dsimp [m', q', pairCross]
      dsimp [pairCross] at hmqNeg
      linarith
    have hmr' : 0 < pairCross m' r' :=
      cross_middle_upper_right_pos hmNorm' hcone' hrNorm' hrx' hry haway'
    have hqx : q.1 < 0 :=
      fst_neg_of_phaseBin_zero_of_snd_neg hqIm
        (by simpa [q, chartComplex] using hbin₀)
    have hqr' : 0 < pairCross q' r' := by
      apply cross_lower_right_upper_right_pos
      · dsimp [q']
        linarith
      · simpa [q'] using hqIm
      · exact hrx'
      · exact hry
      · exact hrNorm'
    have hclose' : sqDist q' (m'.1 + r'.1, m'.2 + r'.2) < 1 :=
      ordered_unit_arc_closeness hmNorm' hqNorm' hrNorm' hmq' hmr' hqr'
    have hclose : sqDist q tc < 1 := by
      have heq : sqDist q tc =
          sqDist q' (m'.1 + r'.1, m'.2 + r'.2) := by
        simp only [sqDist]
        dsimp [q', m', r', q, m, r, tc]
        ring
      rw [heq]
      exact hclose'
    have hqt : q₀ = t := by
      by_contra hne
      have hd := hA q₀ q₀.property t t.property
        (fun h ↦ hne (Subtype.ext h))
      have hsquare : 1 ≤ sqDist q tc := by
        change 1 ≤ sqDist (C.coord source q₀) (C.coord source t)
        rw [C.sqDist_coord]
        simpa only [one_pow] using
          (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1)
            (dist_nonneg : 0 ≤ dist (q₀ : ComplexPoint) t)).mpr hd
      exact (not_lt_of_ge hsquare) hclose
    have hsourceT : (unitDistanceGraph A).Adj source.1 t := by
      simpa [hqt] using hsource₀
    have htSourceUnit : sqDist origin tc = 1 := by
      change sqDist (0, 0) (C.coord source t) = 1
      rw [← C.coord_source source, C.sqDist_coord, hsourceT]
      norm_num
    have hheightNe : m.2 ≠ tc.2 :=
      common_unit_height_ne_of_middle_cone hmUnit htSourceUnit htUnit hmiddleCone
    have hheightNe' : (C.coord source t).2 ≠
        (C.coord source middle).2 := by
      intro h
      apply hheightNe
      simpa [m, tc] using h.symm
    exact ⟨t, hsourceT, hmiddleT,
      lt_of_le_of_ne hheight hheightNe'.symm⟩

/-- The selected secondary is itself at most five-valent: a regular
hexagon at it would force a point above the aligned supporting line. -/
theorem exists_case3_secondary_aligned
    {A : Finset ComplexPoint} {P : CyclicHullData A}
    (hA : IsOneSeparated A) (C : P.AlignedChartData)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (hstrict : ∀ q : Vertex A, q ≠ source.1 →
      (C.coord source q).2 < 0)
    (hsourceDegree : (unitDistanceGraph A).degree source.1 = 3)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hmiddleCone : InOpenMiddleCone (C.coord source middle))
    (hmiddleDegree : (unitDistanceGraph A).degree middle = 5) :
    ∃ secondary : Vertex A,
      (unitDistanceGraph A).Adj source.1 secondary ∧
      (unitDistanceGraph A).Adj middle secondary ∧
      (C.coord source middle).2 < (C.coord source secondary).2 ∧
      (unitDistanceGraph A).degree secondary ≤ 5 := by
  obtain ⟨secondary, hsourceSecondary, hmiddleSecondary, hhigh⟩ :=
    exists_case3_secondary_incidence_aligned hA C source middle hstrict
      hsourceDegree hsourceMiddle hmiddleCone hmiddleDegree
  have hmiddleUnit : sqDist origin (C.coord source middle) = 1 := by
    change sqDist (0, 0) (C.coord source middle) = 1
    rw [← C.coord_source source, C.sqDist_coord, hsourceMiddle]
    norm_num
  have hsecondarySource : sqDist origin (C.coord source secondary) = 1 := by
    change sqDist (0, 0) (C.coord source secondary) = 1
    rw [← C.coord_source source, C.sqDist_coord, hsourceSecondary]
    norm_num
  have hsecondaryMiddle : sqDist (C.coord source middle)
      (C.coord source secondary) = 1 := by
    rw [C.sqDist_coord, hmiddleSecondary]
    norm_num
  have hdegreeLocal := Erdos957Case3General.secondary_degree_le_five
    (C.configuration_oneSeparated P hA source)
    (C.configuration_below_support P source)
    (C.origin_mem_configuration P source)
    (C.coord_mem_configuration P source middle)
    hmiddleUnit hsecondarySource hsecondaryMiddle hhigh
  have hdegree : (unitDistanceGraph A).degree secondary ≤ 5 := by
    rw [← C.case13_degree_coord P source secondary]
    exact hdegreeLocal
  exact ⟨secondary, hsourceSecondary, hmiddleSecondary, hhigh, hdegree⟩

end Erdos957Case3Secondary
