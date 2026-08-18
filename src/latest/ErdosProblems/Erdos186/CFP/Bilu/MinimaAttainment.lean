/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.MahlerBasis
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Attainment of successive minima

This file proves that the infima in `successiveMinimum` are attained when
the seminorm is definite.  The main input is that a definite seminorm on a
finite-dimensional real vector space can itself be used as a norm.  In that
norm every coordinate projection is continuous, so a bounded seminorm ball
contains only finitely many integral points.
-/

namespace Erdos186.CFP.Bilu.Mahler

open scoped BigOperators
open Module

/-- A definite seminorm, regarded as an additive-group norm. -/
def addGroupNormOfDefinite {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (hp : ∀ x, p x = 0 → x = 0) : AddGroupNorm E :=
  { p.toAddGroupSeminorm with
    eq_zero_of_map_eq_zero' := hp }

/-- Every seminorm on finite real coordinate space is bounded above by a
constant multiple of the standard sup norm. -/
theorem seminorm_le_sum_basis_mul_norm {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (x : Fin n → ℝ) :
    p x ≤ (∑ i : Fin n, p (Pi.basisFun ℝ (Fin n) i)) * ‖x‖ := by
  calc
    p x = p (∑ i, x i • Pi.basisFun ℝ (Fin n) i) := by
      congr 1
      simpa using ((Pi.basisFun ℝ (Fin n)).sum_repr x).symm
    _ ≤ (∑ i : Fin n, |x i| * p (Pi.basisFun ℝ (Fin n) i)) :=
      seminorm_sum_le p x (Pi.basisFun ℝ (Fin n))
    _ ≤ ∑ i : Fin n, ‖x‖ * p (Pi.basisFun ℝ (Fin n) i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (by simpa [Real.norm_eq_abs] using norm_le_pi_norm x i)
        (apply_nonneg p _)
    _ = (∑ i : Fin n, p (Pi.basisFun ℝ (Fin n) i)) * ‖x‖ := by
      rw [Finset.sum_mul]
      ac_rfl

/-- Every seminorm on finite real coordinate space is continuous. -/
theorem seminorm_continuous_pi {n : ℕ} (p : Seminorm ℝ (Fin n → ℝ)) :
    Continuous p := by
  let C : ℝ := ∑ i : Fin n, p (Pi.basisFun ℝ (Fin n) i)
  let q : Seminorm ℝ (Fin n → ℝ) :=
    (Real.toNNReal C) • normSeminorm ℝ (Fin n → ℝ)
  apply Seminorm.continuous_of_le (q := q)
  · change Continuous (fun x : Fin n → ℝ ↦ (Real.toNNReal C : ℝ) * ‖x‖)
    fun_prop
  · intro x
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ apply_nonneg p _
    change p x ≤ (Real.toNNReal C : ℝ) * ‖x‖
    rw [Real.coe_toNNReal C hC]
    exact seminorm_le_sum_basis_mul_norm p x

/-- A definite seminorm on finite real coordinate space bounds the standard
sup norm from below by a positive constant. -/
theorem exists_pos_mul_norm_le_seminorm {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ p x := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, zero_lt_one, fun x ↦ ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    calc
      1 * ‖x‖ = 0 := by rw [hx, norm_zero, mul_zero]
      _ ≤ p x := apply_nonneg p x
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let e : Fin n → ℝ := Pi.basisFun ℝ (Fin n) ⟨0, hnpos⟩
    have he : e ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      simp [e, Pi.norm_single]
    obtain ⟨u, hu, hmin⟩ :=
      (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn
        ⟨e, he⟩ (seminorm_continuous_pi p).continuousOn
    refine ⟨p u, ?_, fun x ↦ ?_⟩
    · have hu_ne : u ≠ 0 := by
        intro hu0
        subst u
        simp at hu
      exact (lt_of_le_of_ne (apply_nonneg p u) (Ne.symm fun h ↦ hu_ne (hp u h)))
    · by_cases hx : x = 0
      · simp [hx]
      · let y : Fin n → ℝ := ‖x‖⁻¹ • x
        have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
        have hy : y ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
          rw [Metric.mem_sphere, dist_zero_right]
          simp [y, norm_smul, hnx]
        have hmin_y : p u ≤ p y := hmin hy
        have hpy : p y = ‖x‖⁻¹ * p x := by
          dsimp only [y]
          rw [map_smul_eq_mul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
        rw [hpy] at hmin_y
        calc
          p u * ‖x‖ ≤ (‖x‖⁻¹ * p x) * ‖x‖ :=
            mul_le_mul_of_nonneg_right hmin_y (norm_nonneg x)
          _ = p x := by field_simp

/-- A closed ball for a definite seminorm contains only finitely many
standard integral lattice points. -/
theorem finite_integralPoint_closedBall {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (R : ℝ) :
    Set.Finite {z : IntegralPoint n | p (integralEmbed z) ≤ R} := by
  classical
  obtain ⟨c, hc, hcp⟩ := exists_pos_mul_norm_le_seminorm p hp
  choose N hN using exists_nat_ge (max (R / c) 0)
  refine (Set.Finite.pi' fun i : Fin n ↦
    Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  intro z hz i
  have hR : 0 ≤ R := (apply_nonneg p (integralEmbed z)).trans hz
  have hnorm : ‖integralEmbed z‖ ≤ R / c := by
    rw [le_div_iff₀ hc]
    simpa [mul_comm] using (hcp (integralEmbed z)).trans hz
  have hzi_real : |((z i : ℤ) : ℝ)| ≤ (N : ℝ) := by
    calc
      |((z i : ℤ) : ℝ)| = |integralEmbed z i| := by rfl
      _ ≤ ‖integralEmbed z‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm (integralEmbed z) i
      _ ≤ R / c := hnorm
      _ ≤ max (R / c) 0 := le_max_left _ _
      _ ≤ (N : ℝ) := hN
  have hzi_int : |z i| ≤ (N : ℤ) := by
    exact_mod_cast hzi_real
  exact (abs_le.mp hzi_int)

/-- The first `i+1` standard integral basis vectors give an admissible
family.  In particular, the set defining every successive minimum is
nonempty. -/
theorem admitsIndependent_standard {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (i : Fin n) :
    AdmitsIndependent p (i.val + 1)
      (∑ j : Fin (i.val + 1),
        p (Pi.basisFun ℝ (Fin n) ⟨j.val, j.isLt.trans_le i.isLt⟩)) := by
  let e (j : Fin (i.val + 1)) : Fin n :=
    ⟨j.val, j.isLt.trans_le i.isLt⟩
  let v (j : Fin (i.val + 1)) : IntegralPoint n :=
    Pi.basisFun ℤ (Fin n) (e j)
  have hvembed (j : Fin (i.val + 1)) :
      integralEmbed (v j) = Pi.basisFun ℝ (Fin n) (e j) := by
    ext a
    by_cases h : e j = a
    · subst a
      simp [v, integralEmbed]
    · simp [v, integralEmbed, h]
  have he_inj : Function.Injective e := by
    intro a b hab
    apply Fin.ext
    exact Fin.mk.inj_iff.mp hab
  have hvli : LinearIndependent ℝ (fun j ↦ integralEmbed (v j)) := by
    have hfun : (fun j ↦ integralEmbed (v j)) =
        (fun a ↦ Pi.basisFun ℝ (Fin n) a) ∘ e := by
      funext j
      exact hvembed j
    rw [hfun]
    exact (Pi.basisFun ℝ (Fin n)).linearIndependent.comp e he_inj
  refine ⟨v, hvli, fun j ↦ ?_⟩
  rw [hvembed]
  exact Finset.single_le_sum
    (fun a _ ↦ apply_nonneg p (Pi.basisFun ℝ (Fin n) (e a)))
    (Finset.mem_univ j)

/-- For a definite seminorm, each successive minimum is attained by a
linearly independent family of integral points. -/
theorem admitsIndependent_successiveMinimum {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (i : Fin n) :
    AdmitsIndependent p (i.val + 1) (successiveMinimum p i) := by
  classical
  let k : ℕ := i.val + 1
  let j0 : Fin k := ⟨0, Nat.succ_pos i.val⟩
  let R : ℝ :=
    ∑ j : Fin k,
      p (Pi.basisFun ℝ (Fin n) ⟨j.val, j.isLt.trans_le i.isLt⟩)
  have hstandard : AdmitsIndependent p k R := by
    simpa [k, R] using admitsIndependent_standard p i
  have hball : Set.Finite {z : IntegralPoint n | p (integralEmbed z) ≤ R} :=
    finite_integralPoint_closedBall p hp R
  let candidates : Set (Fin k → IntegralPoint n) :=
    {v | LinearIndependent ℝ (fun j ↦ integralEmbed (v j)) ∧
      ∀ j, p (integralEmbed (v j)) ≤ R}
  have hcandidates : candidates.Finite := by
    refine (Set.Finite.pi' fun _ : Fin k ↦ hball).subset ?_
    intro v hv j
    exact hv.2 j
  let radius (v : Fin k → IntegralPoint n) : ℝ :=
    Finset.univ.sup' ⟨j0, Finset.mem_univ j0⟩
      (fun j ↦ p (integralEmbed (v j)))
  have hradius_le (v : Fin k → IntegralPoint n) (r : ℝ)
      (hvr : ∀ j, p (integralEmbed (v j)) ≤ r) : radius v ≤ r := by
    apply Finset.sup'_le
    intro j _
    exact hvr j
  have hle_radius (v : Fin k → IntegralPoint n) (j : Fin k) :
      p (integralEmbed (v j)) ≤ radius v := by
    exact Finset.le_sup' (fun a ↦ p (integralEmbed (v a))) (Finset.mem_univ j)
  obtain ⟨vstd, hvstdli, hvstdR⟩ := hstandard
  have hvstd_mem : vstd ∈ candidates := ⟨hvstdli, hvstdR⟩
  have hnonempty : hcandidates.toFinset.Nonempty := by
    exact ⟨vstd, hcandidates.mem_toFinset.mpr hvstd_mem⟩
  obtain ⟨v, hvF, hvmin⟩ :=
    hcandidates.toFinset.exists_min_image radius hnonempty
  have hv : v ∈ candidates := hcandidates.mem_toFinset.mp hvF
  have hadmits_radius : AdmitsIndependent p k (radius v) :=
    ⟨v, hv.1, hle_radius v⟩
  have hradR : radius v ≤ R := hradius_le v R hv.2
  have hrad_lower : ∀ r, AdmitsIndependent p k r → radius v ≤ r := by
    intro r hr
    by_cases hrR : r ≤ R
    · obtain ⟨w, hwli, hwr⟩ := hr
      have hw_mem : w ∈ candidates :=
        ⟨hwli, fun j ↦ (hwr j).trans hrR⟩
      have hwF : w ∈ hcandidates.toFinset :=
        hcandidates.mem_toFinset.mpr hw_mem
      exact (hvmin w hwF).trans (hradius_le w r hwr)
    · exact hradR.trans (le_of_not_ge hrR)
  have heq : successiveMinimum p i = radius v := by
    apply le_antisymm
    · exact successiveMinimum_le_of_admits hadmits_radius
    · rw [successiveMinimum]
      exact le_csInf ⟨radius v, hadmits_radius⟩ hrad_lower
  rw [heq]
  simpa [k] using hadmits_radius

/-- An explicit witness form of attainment of the `i`th successive minimum. -/
theorem exists_independent_integralPoint_at_successiveMinimum {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) (i : Fin n) :
    ∃ v : Fin (i.val + 1) → IntegralPoint n,
      LinearIndependent ℝ (fun j ↦ integralEmbed (v j)) ∧
        ∀ j, p (integralEmbed (v j)) ≤ successiveMinimum p i :=
  admitsIndependent_successiveMinimum p hp i

/-- Successive minima of a definite seminorm are nondecreasing. -/
theorem successiveMinimum_mono {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p)
    {i j : Fin n} (hij : i ≤ j) :
    successiveMinimum p i ≤ successiveMinimum p j := by
  obtain ⟨v, hvli, hvbound⟩ :=
    admitsIndependent_successiveMinimum p hp j
  let e : Fin (i.val + 1) → Fin (j.val + 1) :=
    Fin.castLE (Nat.succ_le_succ hij)
  have he : Function.Injective e := by
    intro a b hab
    apply Fin.ext
    exact Fin.mk.inj_iff.mp hab
  apply successiveMinimum_le_of_admits
  refine ⟨fun a ↦ v (e a), ?_, fun a ↦ hvbound (e a)⟩
  exact hvli.comp e he

/-- Among `k+1` independent vectors, one lies outside the span of any
given independent `k`-tuple. -/
theorem exists_notMem_span_of_fin_succ
    {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    {v : Fin k → E} {w : Fin (k + 1) → E}
    (hv : LinearIndependent ℝ v) (hw : LinearIndependent ℝ w) :
    ∃ j, w j ∉ Submodule.span ℝ (Set.range v) := by
  by_contra h
  have h : ∀ j, w j ∈ Submodule.span ℝ (Set.range v) := by
    simpa only [not_exists, not_not] using h
  have hspan : Submodule.span ℝ (Set.range w) ≤
      Submodule.span ℝ (Set.range v) := by
    rw [Submodule.span_le]
    rintro y ⟨j, rfl⟩
    exact h j
  let _ : Module.Finite ℝ (Submodule.span ℝ (Set.range v)) :=
    Module.Finite.span_of_finite ℝ (Set.finite_range v)
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hw, finrank_span_eq_card hv] at hdim
  simp only [Fintype.card_fin] at hdim
  omega

/-- Simultaneous compatible attainment, in the inequality form needed by
Mahler's basis reduction: one can choose a full independent integral family
whose `i`th member is no larger than the `i`th successive minimum. -/
theorem exists_independent_integralPoint_le_successiveMinimum {n : ℕ}
    (p : Seminorm ℝ (Fin n → ℝ)) (hp : IsDefinite p) :
    ∃ x : Fin n → IntegralPoint n,
      LinearIndependent ℝ (fun i ↦ integralEmbed (x i)) ∧
        ∀ i, p (integralEmbed (x i)) ≤ successiveMinimum p i := by
  have hprefix : ∀ (k : ℕ) (hkn : k ≤ n),
      ∃ x : Fin k → IntegralPoint n,
        LinearIndependent ℝ (fun i ↦ integralEmbed (x i)) ∧
          ∀ i, p (integralEmbed (x i)) ≤
            successiveMinimum p (Fin.castLE hkn i) := by
    intro k
    induction k with
    | zero =>
        intro _hkn
        refine ⟨fun i ↦ Fin.elim0 i, ?_, fun i ↦ Fin.elim0 i⟩
        exact linearIndependent_empty_type
    | succ k ih =>
        intro hkn
        have hk_le : k ≤ n := k.le_succ.trans hkn
        obtain ⟨x, hxli, hxbound⟩ := ih hk_le
        let last : Fin n := ⟨k, hkn⟩
        obtain ⟨w, hwli, hwbound⟩ :=
          admitsIndependent_successiveMinimum p hp last
        have hwli' : LinearIndependent ℝ
            (fun j : Fin (k + 1) ↦ integralEmbed (w j)) := by
          simpa [last] using hwli
        obtain ⟨j, hj⟩ := exists_notMem_span_of_fin_succ hxli hwli'
        let x' : Fin (k + 1) → IntegralPoint n := Fin.snoc x (w j)
        have hx'li : LinearIndependent ℝ (fun i ↦ integralEmbed (x' i)) := by
          have hs := hxli.finSnoc hj
          have hfun : (fun i ↦ integralEmbed (x' i)) =
              Fin.snoc (fun i ↦ integralEmbed (x i)) (integralEmbed (w j)) := by
            funext i
            refine Fin.lastCases ?_ (fun a ↦ ?_) i
            · simp [x']
            · simp [x']
          rw [hfun]
          exact hs
        refine ⟨x', hx'li, fun a ↦ ?_⟩
        refine Fin.lastCases ?_ (fun b ↦ ?_) a
        · have hjbound := hwbound j
          have hidx : Fin.castLE hkn (Fin.last k) = last := rfl
          simpa [x', hidx] using hjbound
        · have hb := hxbound b
          simpa [x'] using hb
  obtain ⟨x, hxli, hxbound⟩ := hprefix n le_rfl
  refine ⟨x, hxli, fun i ↦ ?_⟩
  simpa using hxbound i

end Erdos186.CFP.Bilu.Mahler
