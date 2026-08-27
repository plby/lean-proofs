/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkStageBudget
import ErdosProblems.Erdos207.SourceLinkNumericBudget
import ErdosProblems.Erdos207.SourceLinkNumericalCompletion
import ErdosProblems.Erdos207.UniformSourceMomentBudgets
import ErdosProblems.Erdos207.EventualLinkSamplingBudget
import ErdosProblems.Erdos207.SourceLinkFiniteUnionBudgets
import ErdosProblems.Erdos207.SourcePhysicalExtensionBudgets
import ErdosProblems.Erdos207.PreliminaryDegreePowerBudgets
import ErdosProblems.Erdos207.FiniteBackwardErrorSchedule

/-! # Construct every final link-stage scalar from fixed physical powers -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem eventually_exists_source_link_stage_budget
    (q h ell b reserveExp v D L rootExp R : ℕ) (C B0 eta0 : ℝ≥0)
    (hb : 2 ≤ b) (heta0 : 0 < eta0) (heta01 : eta0 ≤ 1)
    (hreserveGap : v+2*b+4 ≤ reserveExp)
    (hfutureGap : v+b*(h+2)+4 ≤ reserveExp)
    (hinnerGap : 2*reserveExp+3*b+v+2 ≤ L)
    (hcurrentGap : 2*reserveExp ≤ D)
    (hmarkedGap : v+(1+v+reserveExp+2*b)*(q+1)+1 ≤ D)
    (hrootGap : b*(h+1)+2 ≤ rootExp) :
    ∃ errorExponent T : ℕ, 1 ≤ errorExponent ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (W : Vortex V ell) (i : Fin ell)
        (bank : TripleSystemOn V) (p beta eta xi xi' : ℝ≥0),
      Fintype.card V ≤ t^R → t^D ≤ (W.U i.castSucc).card → t^L ≤ (W.U i.succ).card →
      (W.U i.castSucc).card ≤ t^v*(W.U i.succ).card →
      (∀ j ∈ Icc 4 q, sourcePrefixZ q bank i.val j ≤ (t : ℝ≥0)^v) →
      (∀ a ∈ futureLevelPairs i.succ, t^rootExp ≤ (W.U a.2).card) →
      (∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ Icc 4 q, sourcePrefixZ q bank a.1.val j ≤ t) →
      1/(t : ℝ≥0)^b ≤ p → p ≤ 2/(t : ℝ≥0)^b → p ≤ 1 → eta0 ≤ eta → eta ≤ 1 →
      xi+1/t ≤ xi' → 6/t ≤ xi' → beta ≤ B0/(t : ℝ≥0)^errorExponent →
      ∃ budget : SourceLinkStageBudget q h W i bank p (1/(t : ℝ≥0)^reserveExp) C beta eta xi xi',
        budget.d = ⌊(1/(t : ℝ≥0)^reserveExp)^2*p^2*eta*(W.U i.succ).card/256⌋₊ ∧
        budget.degreeError = 2/(t : ℝ≥0)^3 ∧ budget.referenceTolerance = 1/1048576 := by
  let orders := Icc 4 q
  let referenceTolerance : ℝ≥0 := 1/1048576
  let epsilon0 : ℝ≥0 := 1/(1+h+h^2 : ℕ)
  let A : ℝ≥0 := 1920/eta0
  let linkDecay := 2*R+3
  let degreeDecay := R+3
  let quasiDecay := R*(2*h^2)+3
  let kappa : ℝ≥0 := 3/(orders.card+1 : ℝ≥0)
  have hepsilon0 : 0 < epsilon0 := by dsimp only [epsilon0]; positivity
  have heffective : 0 < epsilon0/(orders.card+1 : ℝ≥0) := by positivity
  obtain ⟨overlapMoment, overlapExponent, Toverlap, hsoverlap, hToverlap, hoverlap⟩ :=
    eventually_source_reserve_overlap_budget R reserveExp D 3 C B0 hcurrentGap
  obtain ⟨linkExponent, Tlink, hlinkExponent, hTlink, hlink⟩ :=
    eventually_uniform_source_link_moments q ell R linkDecay C kappa B0 (by dsimp only [kappa]; positivity)
  obtain ⟨quasiExponent, Tquasi, hquasiExponent, hTquasi, hquasi⟩ :=
    eventually_uniform_source_quasi_moments q ell h R b quasiDecay (2*max (C^5) 1)
      (epsilon0/(orders.card+1 : ℝ≥0)) eta0 B0 hb heffective heta0
  obtain ⟨Tdegree, hTdegree, hdegree⟩ := eventually_source_link_future_degree_moment reserveExp b v h
    degreeDecay A eta0 epsilon0 heta0 hepsilon0 hfutureGap
  obtain ⟨Tgeom, hTgeom, hgeom⟩ := eventually_source_link_geometric_budget R 2
  let quasiCoefficient : ℝ≥0 := (ell*(ell+1) : ℕ)*(h^2+1 : ℕ)*2^(2*h^2)*h^2*orders.card
  let constraints : Finset ℝ≥0 := {3, 2*A, 24*A^2, A^(q+1), 512/eta0,
    18*(65537+4)/eta0, 1/(128*referenceTolerance*eta0), (orders.card : ℝ≥0),
    ((ell*(ell+1) : ℕ) : ℝ≥0), quasiCoefficient,
    max (h : ℝ≥0) (2*(degreeDecay+1 : ℕ))/(epsilon0*eta0^(h^2))}
  let Tscalar := ⌈∑ x ∈ constraints, x⌉₊
  let errorExponent := max overlapExponent (max linkExponent quasiExponent)
  let T := Toverlap+Tlink+Tquasi+Tdegree+Tgeom+Tscalar+3
  refine ⟨errorExponent, T, hlinkExponent.trans ((le_max_left _ _).trans (le_max_right _ _)),
    by dsimp only [T]; omega, ?_⟩
  intro t ht V _ _ W i bank p beta eta xi xi' hN hn hu hratio hz hfutureSize hfutureZ
    hp hpUpper hp1 heta heta1 hxiStep hxiSize hbeta
  have ht3 : 3 ≤ t := by dsimp only [T] at ht; omega
  have ht1 : 1 ≤ t := by omega
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht1
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le htNN
  have htScalar : Tscalar ≤ t := by dsimp only [T] at ht; omega
  have hconstraints : ∀ x ∈ constraints, x ≤ (t : ℝ≥0) := by
    intro x hx
    exact (single_le_sum (fun _ _ ↦ zero_le) hx).trans
      ((Nat.le_ceil (∑ x ∈ constraints, x)).trans (by exact_mod_cast htScalar))
  have hA : 1 ≤ A := by
    apply (le_div_iff₀ heta0).mpr
    simpa only [one_mul] using heta01.trans (by norm_num : (1 : ℝ≥0) ≤ 1920)
  have hAt : 2*A ≤ (t : ℝ≥0) := hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hcollisionT : 24*A^2 ≤ (t : ℝ≥0) := hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hmarkedT : A^(q+1) ≤ (t : ℝ≥0) := hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hmassT : 512/eta0 ≤ (t : ℝ≥0) := hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hreferenceT : 18*(65537+4)/eta0 ≤ (t : ℝ≥0) := hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hrecenteringT : 1/(128*referenceTolerance*eta0) ≤ (t : ℝ≥0) := hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hordersT : (orders.card : ℝ≥0) ≤ t := hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hlevelsT : (ell*(ell+1) : ℕ) ≤ (t : ℝ≥0) := hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hquasiT : quasiCoefficient ≤ (t : ℝ≥0) := hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hpatternT : max (h : ℝ≥0) (2*(degreeDecay+1 : ℕ))/(epsilon0*eta0^(h^2)) ≤ (t : ℝ≥0) :=
    hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true])
  let n := (W.U i.castSucc).card
  let u := (W.U i.succ).card
  let r : ℝ≥0 := 1/(t : ℝ≥0)^reserveExp
  let a := A*(t : ℝ≥0)
  let epsilon := epsilon0/(t : ℝ≥0)
  let mu := r^2*p^2*eta*u
  let x := r*p^2*eta*u
  let overlap := ⌈(t : ℝ≥0)*r^2*n⌉₊
  let cap := ⌊3*(t : ℝ≥0)/(orders.card+1 : ℝ≥0)⌋₊
  let Delta := 2*t+∑ _j ∈ orders, cap
  have hnUpper : n ≤ t^R := (card_le_univ (W.U i.castSucc)).trans hN
  have hu0 : (0 : ℝ≥0) < u := (pow_pos ht0 L).trans_le (by exact_mod_cast hu)
  have hun : (u : ℝ≥0) ≤ n := by
    exact_mod_cast card_le_card (W.antitone i.castSucc i.succ (by change i.val ≤ i.val+1; omega))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1 := (div_le_one (pow_pos ht0 _)).mpr (one_le_pow₀ htNN)
  have hp0 : 0 < p := (by positivity : 0 < 1/(t : ℝ≥0)^b).trans_le hp
  have hmuLower : eta0*(t : ℝ≥0)^2 ≤ mu := reserve_internal_supply_power_lower
    t u r p eta eta0 reserveExp b L 2 htNN le_rfl hp heta (by exact_mod_cast hu) (by omega)
  have hmuX : mu ≤ x := by
    dsimp only [mu, x]
    have hh : r^2 ≤ r := by simpa only [pow_one] using pow_le_pow_of_le_one zero_le hr1 (by norm_num : 1 ≤ 2)
    gcongr
  have hmass : (512 : ℝ≥0) ≤ eta0*t := by
    have hh := (div_le_iff₀ heta0).mp hmassT
    simpa only [mul_comm (t : ℝ≥0) eta0] using hh
  have hX80 : (80 : ℝ≥0) ≤ x := by
    calc
      (80 : ℝ≥0) ≤ 512 := by norm_num
      _ ≤ eta0*t := hmass
      _ ≤ eta0*(t : ℝ≥0)^2 := by gcongr; simpa only [pow_one] using pow_le_pow_right₀ htNN (by norm_num : 1 ≤ 2)
      _ ≤ x := hmuLower.trans hmuX
  obtain ⟨c, degree, hcUpper, hcLower, hdegreeLower, hdegreeUpper⟩ := exists_source_link_rounding x hX80
  have hbetaOverlap : beta ≤ B0/(t : ℝ≥0)^overlapExponent := hbeta.trans
    (polynomial_incoming_error_budget t B0 errorExponent overlapExponent htNN (le_max_left _ _))
  have hbetaLink : beta ≤ B0/(t : ℝ≥0)^linkExponent := hbeta.trans
    (polynomial_incoming_error_budget t B0 errorExponent linkExponent htNN ((le_max_left _ _).trans (le_max_right _ _)))
  have hbetaQuasi : beta ≤ B0/(t : ℝ≥0)^quasiExponent := hbeta.trans
    (polynomial_incoming_error_budget t B0 errorExponent quasiExponent htNN ((le_max_right _ _).trans (le_max_right _ _)))
  have hOverlap := hoverlap t (by dsimp only [T] at ht; omega) (Fintype.card V) n hN hnUpper hn beta hbetaOverlap
  have hpoint := source_link_remaining_numeric_budget t n u A p b reserveExp v L htNN hA hAt hb hp hpUpper hp1
    (by exact_mod_cast hu) hun (by exact_mod_cast hratio) (by omega) (by omega)
  have hdegreeBound : (degree : ℝ≥0) ≤ 3*r*p^2*u := by
    calc
      _ ≤ 3*x := hdegreeUpper
      _ = (3*r*p^2*u)*eta := by dsimp only [x]; ring
      _ ≤ (3*r*p^2*u)*1 := mul_le_mul_of_nonneg_left heta1 zero_le
      _ = _ := mul_one _
  have hcollision := source_link_collision_power_budget t n u A a r p degree overlap
    (a/(r*p^2*u)) reserveExp b v htNN hr hu0 le_rfl le_rfl hp (by exact_mod_cast hratio)
    hreserveGap hdegreeBound (by simpa only [overlap, r, mul_assoc] using hOverlap.2.1) le_rfl hcollisionT
  have hcenters : Fintype.card {z : V // z ∉ W.U i.succ} ≤ Fintype.card V :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hGeom := hgeom t (by dsimp only [T] at ht; omega) (Fintype.card V)
    (Fintype.card {z : V // z ∉ W.U i.succ}) degree overlap hN hcenters (a/(r*p^2*u))
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hcollision)
  have hDegree := hdegree t (by dsimp only [T] at ht; omega) n u a r p eta epsilon overlap
    (a/(r*p^2*u)) hr hu0 le_rfl le_rfl hp heta le_rfl (by exact_mod_cast hratio)
    (by simpa only [overlap, r, mul_assoc] using hOverlap.2.2.1) le_rfl
  have hlinkScalar : ∀ j ∈ orders, sourceLinkFailureBound i.val j (linkDecay+1)
      (Fintype.card V) cap C beta (sourcePrefixY q i.val) ≤ 1/(t : ℝ≥0)^linkDecay := by
    intro j hj
    exact hlink t (by dsimp only [T] at ht; omega) i.val (by have := i.isLt; omega) j (mem_Icc.mp hj).2
      (Fintype.card V) cap beta hN (source_link_fixed_caps_budget orders t).2.1 hbetaLink
  have hquasiScalar : ∀ aa ∈ futureLevelPairs i.succ, ∀ j ∈ orders,
      sourceQuasiUniformFailureBound aa.1.val j (quasiDecay+1) h (Fintype.card V) p
        (2*max (C^5) 1) beta (sourcePrefixY q aa.1.val) (epsilon/(orders.card+1 : ℝ≥0)) eta
        (W.U aa.2).card ≤ 1/(t : ℝ≥0)^quasiDecay := by
    intro aa haa j hj
    have hsize : (1 : ℝ≥0) ≤ (W.U aa.2).card :=
      (one_le_pow₀ htNN).trans (by exact_mod_cast hfutureSize aa haa)
    exact hquasi t (by dsimp only [T] at ht; omega) aa.1.val (by have := aa.1.isLt; omega)
      j (mem_Icc.mp hj).2 (Fintype.card V) p beta (epsilon/(orders.card+1 : ℝ≥0)) eta (W.U aa.2).card
      hN hsize hp hpUpper (by dsimp only [epsilon]; ring_nf; exact le_rfl) heta hbetaQuasi
  have hpriorBound : 2/(t : ℝ≥0)^3+(Fintype.card V : ℝ≥0)^2*
      ((2*(n : ℝ≥0)*C^2*r^2/(overlap+1))^overlapMoment+
        (2*(n : ℝ≥0)*C^2/(overlap+1))^overlapMoment*beta) ≤ 1/(t : ℝ≥0)^2 := by
    calc
      _ ≤ 2/(t : ℝ≥0)^3+1/(t : ℝ≥0)^3 := add_le_add le_rfl hOverlap.2.2.2
      _ = 3/(t : ℝ≥0)^(2+1) := by ring
      _ ≤ _ := inverse_power_absorb_coefficient t 3 2 ht0 (by exact_mod_cast ht3)
  have hUnions := source_link_finite_union_power_budgets orders (Fintype.card V) ell h R t
    (1/(t : ℝ≥0)^degreeDecay) (fun _ ↦ 1/(t : ℝ≥0)^linkDecay) (fun _ ↦ 1/(t : ℝ≥0)^quasiDecay)
    htNN (by exact_mod_cast hN) (fun _ _ ↦ le_rfl) le_rfl (fun _ _ ↦ le_rfl) hordersT hlevelsT hquasiT
  have hProb := source_link_final_probability_budgets t (1/(t : ℝ≥0)^2)
    (rawLinkGeometricFailure (Fintype.card {z : V // z ∉ W.U i.succ}) (Fintype.card V)
      degree overlap (2*t) t t (a/(r*p^2*u)))
    ((Fintype.card V : ℝ≥0)^2*∑ _j ∈ orders, (1/(t : ℝ≥0)^linkDecay))
    ((ell*(ell+1) : ℕ)*(Fintype.card V : ℝ≥0)*(1/(t : ℝ≥0)^degreeDecay))
    ((ell*(ell+1) : ℕ)*((h^2+1 : ℕ)*(Fintype.card V+1 : ℝ≥0)^(2*h^2))*h^2*
      ∑ _j ∈ orders, (1/(t : ℝ≥0)^quasiDecay)) xi' (by exact_mod_cast ht3)
    le_rfl hGeom.2 hUnions.1 hUnions.2.1 hUnions.2.2 hxiSize
  have hpattern : ∀ aa ∈ futureLevelPairs i.succ,
      max (h : ℝ≥0) (2*(degreeDecay+1 : ℕ)) ≤ epsilon*p^h*eta^(h^2)*(W.U aa.2).card := by
    intro aa haa
    have hlarge := (div_le_iff₀ (by positivity : 0 < epsilon0*eta0^(h^2))).mp hpatternT
    have hdensity := future_pattern_density_power_lower t (W.U aa.2).card p eta epsilon eta0 epsilon0
      b 1 h rootExp 1 htNN hp heta (by simpa only [pow_one] using (le_rfl : epsilon ≤ epsilon))
      (by exact_mod_cast hfutureSize aa haa) (by nlinarith only [hrootGap])
    apply le_trans _ hdensity
    simpa only [pow_one, mul_comm (t : ℝ≥0) (epsilon0*eta0^(h^2))] using hlarge
  have hrecentering := source_link_recenter_power_budget t p eta eta0 referenceTolerance b reserveExp
    htNN heta0 (by dsimp only [referenceTolerance]; norm_num) hp heta (by omega) hrecenteringT
  have hdegreeLoss := rounded_internal_degree_recenter r p eta u referenceTolerance hrecentering
  have hlargeRef := source_link_large_reference t x eta0 htNN heta0 (hmuLower.trans hmuX) hreferenceT
  have hmarked : ∀ j ∈ orders, sourcePrefixZ q bank i.val j*
      (a*n/(r*p^2*u))^(q+1)/n ≤ sourcePrefixY q i.val := by
    intro j hj
    exact source_link_marked_numeric_budget t n u A a p (sourcePrefixZ q bank i.val j) (sourcePrefixY q i.val)
      q b reserveExp v D htNN hu0 le_rfl hp (hz j hj) (one_le_sourcePrefixY q i.val)
      (by exact_mod_cast hn) (by exact_mod_cast hratio) hmarkedGap hmarkedT
  have hfutureScale : ∀ aa ∈ futureLevelPairs i.succ, ∀ j ∈ orders,
      sourcePrefixZ q bank aa.1.val j ≤ sourcePrefixY q aa.1.val*p^(h+1)*(W.U aa.2).card := by
    intro aa haa j hj
    exact source_future_quasi_extension_power t (W.U aa.2).card p (sourcePrefixZ q bank aa.1.val j)
      (sourcePrefixY q aa.1.val) b h rootExp htNN (one_le_sourcePrefixY q aa.1.val) hp
      (hfutureZ aa haa j hj) (by exact_mod_cast hfutureSize aa haa) (by omega)
  have hepsilonId : (1+h+h^2 : ℕ)*epsilon = 1/(t : ℝ≥0) := by
    dsimp only [epsilon, epsilon0]
    field_simp
  refine ⟨{
    a := a, referenceTolerance := referenceTolerance, epsilon := epsilon,
    d := ⌊mu/256⌋₊, degreeError := 2/(t : ℝ≥0)^3,
    futureDegreeError := 1/(t : ℝ≥0)^degreeDecay, priorError := 1/(t : ℝ≥0)^2,
    Delta := Delta, collisionCap := 2*t, degree := degree, overlap := overlap,
    collisionMoment := t, scale := t, c := c, overlapMoment := overlapMoment, degreeMoment := degreeDecay+1,
    linkMoment := fun _ ↦ linkDecay+1, cap := fun _ ↦ cap, quasiMoment := fun _ ↦ quasiDecay+1,
    linkError := fun _ ↦ 1/(t : ℝ≥0)^linkDecay, quasiError := fun _ ↦ 1/(t : ℝ≥0)^quasiDecay,
    reference_small := by
      dsimp only [referenceTolerance]
      apply NNReal.coe_le_coe.mp
      norm_num,
    degree_loss := hdegreeLoss, reference_large := by
      have hx : ((18*(65537+4*t) : ℕ) : ℝ≥0) ≤ x := by exact_mod_cast hlargeRef
      exact hx,
    hall_upper := hcUpper, degree_lower := by simpa only [x, mul_assoc] using hdegreeLower,
    cap_budget := le_rfl, collision_moment := by omega,
    hall_budget := source_link_fixed_hall_budget orders t r p eta eta0 u c hr hp0 hu0 heta0 heta hcLower,
    hall_small := hGeom.1, overlap_moment := hOverlap.1, prior_bound := hpriorBound,
    block := by simpa only [Vortex.prefix_terminalSize] using hpoint.1,
    pa := hpoint.2.1, marked_ge_one := by simpa only [Vortex.prefix_terminalSize] using hpoint.2.2.1,
    sampling_le_one := hpoint.2.2.2.1, point_charge := hpoint.2.2.2.2,
    marked_scale := by simpa only [Vortex.prefix_terminalSize] using hmarked,
    link_scalar := hlinkScalar, epsilon_pos := by dsimp only [epsilon]; positivity,
    xi_mono := (le_add_of_nonneg_right zero_le).trans hxiStep,
    loss := hepsilonId ▸ le_tsub_of_add_le_left hxiStep,
    pattern_support := fun aa haa ↦ (le_max_left _ _).trans (hpattern aa haa),
    degree_size := fun aa haa ↦ (le_max_right _ _).trans (hpattern aa haa),
    degree_scalar := hDegree, future_scale := hfutureScale, quasi_scalar := hquasiScalar,
    coverage_half := hProb.1, future_budget := hProb.2 }, rfl, rfl, rfl⟩

end

end Erdos207
