import ErdosProblems.Erdos520.HarperConsecutiveBlocks
import ErdosProblems.Erdos520.HarperFiniteSlicing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Fair moments of Euler products evaluated at varying heights

Harper's global good event evaluates a different scheduled prime block at
each point of a nested vertical mesh.  Independence is coordinatewise, so
the fair first moment is unchanged by these varying heights.  This file
records that exact factorization and the resulting finite-union Markov
bound.
-/

/-- The fair finite product law on prime coordinates through `y`. -/
noncomputable def harperFairCubeLaw (y : Nat) :
    Measure (HarperPrimeCube y) :=
  Measure.pi (fun _ : HarperPrimeIndex y => coin)

instance harperFairCubeLaw_isProbabilityMeasure (y : Nat) :
    IsProbabilityMeasure (harperFairCubeLaw y) := by
  unfold harperFairCubeLaw
  infer_instance

/-- Expectations of products of coordinate observables factor under the
fair prime cube. -/
theorem integral_prod_harperFairCubeLaw
    (y : Nat) (g : HarperPrimeIndex y -> Bool -> Real) :
    (integral (harperFairCubeLaw y) fun eta =>
        ∏ p : HarperPrimeIndex y, g p (eta p)) =
      ∏ p : HarperPrimeIndex y, integral coin (g p) := by
  let X : HarperPrimeIndex y -> HarperPrimeCube y -> Real :=
    fun p eta => g p (eta p)
  have hbase : iIndepFun
      (fun p : HarperPrimeIndex y =>
        fun eta : HarperPrimeCube y => eta p)
      (harperFairCubeLaw y) := by
    unfold harperFairCubeLaw
    exact iIndepFun_pi
      (X := fun _ : HarperPrimeIndex y => id)
      (fun _ => aemeasurable_id)
  have hX : iIndepFun X (harperFairCubeLaw y) := by
    have hcomp := hbase.comp g (fun _ => measurable_of_finite _)
    simpa only [X, Function.comp_apply] using! hcomp
  have hprod := hX.integral_fun_prod_eq_prod_integral
    (fun p => (measurable_of_finite (X p)).aestronglyMeasurable)
  calc
    (integral (harperFairCubeLaw y) fun eta =>
        ∏ p : HarperPrimeIndex y, g p (eta p)) =
        ∏ p : HarperPrimeIndex y,
          integral (harperFairCubeLaw y) (fun eta => g p (eta p)) := by
      simpa only [X] using! hprod
    _ = ∏ p : HarperPrimeIndex y, integral coin (g p) := by
      apply Finset.prod_congr rfl
      intro p _hp
      have hmp : MeasurePreserving
          (fun eta : HarperPrimeCube y => eta p)
          (harperFairCubeLaw y) coin := by
        unfold harperFairCubeLaw
        exact measurePreserving_eval
          (fun _ : HarperPrimeIndex y => coin) p
      calc
        integral (harperFairCubeLaw y) (fun eta => g p (eta p)) =
            integral (Measure.map
              (fun eta : HarperPrimeCube y => eta p)
              (harperFairCubeLaw y)) (g p) := by
          symm
          exact integral_map hmp.measurable.aemeasurable
            (measurable_of_finite (g p)).aestronglyMeasurable
        _ = integral coin (g p) := by rw [hmp.map_eq]

theorem integral_coin_harperCoordinateFactor
    (p : Nat) (u : Real) :
    integral coin (harperCoordinateFactor p u) =
      1 + (p : Real)⁻¹ := by
  rw [integral_coin_bool, harperCoordinateFactor_false_add_true]
  ring

/-- Squared Euler energy over an arbitrary finite prime set, with a
potentially different height at every coordinate. -/
noncomputable def harperVaryingEulerEnergy
    (y : Nat) (S : Finset (HarperPrimeIndex y))
    (u : HarperPrimeIndex y -> Real) (eta : HarperPrimeCube y) : Real :=
  ∏ p ∈ S, harperCoordinateFactor p.1 (u p) (eta p)

theorem harperVaryingEulerEnergy_nonneg
    (y : Nat) (S : Finset (HarperPrimeIndex y))
    (u : HarperPrimeIndex y -> Real) (eta : HarperPrimeCube y) :
    0 <= harperVaryingEulerEnergy y S u eta := by
  unfold harperVaryingEulerEnergy
  exact Finset.prod_nonneg fun p _hp =>
    harperCoordinateFactor_nonneg p.1 (u p) (eta p)

/-- Exact fair first moment; it is independent of every chosen height. -/
theorem integral_harperVaryingEulerEnergy
    (y : Nat) (S : Finset (HarperPrimeIndex y))
    (u : HarperPrimeIndex y -> Real) :
    integral (harperFairCubeLaw y)
        (harperVaryingEulerEnergy y S u) =
      ∏ p ∈ S, (1 + (p.1 : Real)⁻¹) := by
  let g : HarperPrimeIndex y -> Bool -> Real := fun p b =>
    if p ∈ S then harperCoordinateFactor p.1 (u p) b else 1
  have hfactor := integral_prod_harperFairCubeLaw y g
  have hleft : (fun eta => ∏ p : HarperPrimeIndex y, g p (eta p)) =
      harperVaryingEulerEnergy y S u := by
    funext eta
    simp only [g, Finset.prod_ite_mem, Finset.univ_inter]
    rfl
  have hright : (∏ p : HarperPrimeIndex y, integral coin (g p)) =
      ∏ p ∈ S, (1 + (p.1 : Real)⁻¹) := by
    calc
      (∏ p : HarperPrimeIndex y, integral coin (g p)) =
          ∏ p : HarperPrimeIndex y,
            if p ∈ S then 1 + (p.1 : Real)⁻¹ else 1 := by
        apply Finset.prod_congr rfl
        intro p _hp
        by_cases hpS : p ∈ S
        · simp only [g, if_pos hpS]
          exact integral_coin_harperCoordinateFactor p.1 (u p)
        · simp only [g, if_neg hpS]
          rw [integral_coin_bool]
          norm_num
      _ = ∏ p ∈ S, (1 + (p.1 : Real)⁻¹) :=
        Fintype.prod_ite_mem S _
  rw [hleft, hright] at hfactor
  exact hfactor

/-- A blockwise height sequence, extended canonically to all prime
coordinates.  Outside the scheduled range its value is irrelevant. -/
noncomputable def harperScheduledPrimeHeight
    (y start n : Nat) (u : Fin n -> Real)
    (p : HarperPrimeIndex y) : Real :=
  if h : ∃ i : Fin n,
      p ∈ harperScheduledPrimeBlock y (start + (i : Nat)) then
    u (Classical.choose h)
  else 0

theorem harperScheduledPrimeHeight_eq
    (y start n : Nat) (u : Fin n -> Real) (i : Fin n)
    {p : HarperPrimeIndex y}
    (hp : p ∈ harperScheduledPrimeBlock y (start + (i : Nat))) :
    harperScheduledPrimeHeight y start n u p = u i := by
  unfold harperScheduledPrimeHeight
  let h : ∃ k : Fin n,
      p ∈ harperScheduledPrimeBlock y (start + (k : Nat)) := ⟨i, hp⟩
  rw [dif_pos h]
  let k : Fin n := Classical.choose h
  have hk : p ∈ harperScheduledPrimeBlock y (start + (k : Nat)) :=
    Classical.choose_spec h
  have hki : k = i := by
    by_contra hne
    have hblocks := disjoint_harperScheduledPrimeBlock y
      (show start + (k : Nat) ≠ start + (i : Nat) by
        intro heq
        apply hne
        apply Fin.ext
        omega)
    exact (Finset.disjoint_left.mp hblocks hk hp)
  exact congrArg u hki

/-- Product of scheduled block energies evaluated at their own heights. -/
noncomputable def harperScheduledVaryingEulerEnergy
    (y start n : Nat) (u : Fin n -> Real)
    (eta : HarperPrimeCube y) : Real :=
  ∏ i : Fin n, ∏ p ∈ harperScheduledPrimeBlock y (start + (i : Nat)),
    harperCoordinateFactor p.1 (u i) (eta p)

theorem harperScheduledVaryingEulerEnergy_nonneg
    (y start n : Nat) (u : Fin n -> Real) (eta : HarperPrimeCube y) :
    0 <= harperScheduledVaryingEulerEnergy y start n u eta := by
  unfold harperScheduledVaryingEulerEnergy
  exact Finset.prod_nonneg fun i _hi =>
    Finset.prod_nonneg fun p _hp =>
      harperCoordinateFactor_nonneg p.1 (u i) (eta p)

theorem harperScheduledVaryingEulerEnergy_eq_rangeFrom
    (y start n : Nat) (u : Fin n -> Real) (eta : HarperPrimeCube y) :
    harperScheduledVaryingEulerEnergy y start n u eta =
      harperVaryingEulerEnergy y
        (harperScheduledPrimeRangeFrom y start n)
        (harperScheduledPrimeHeight y start n u) eta := by
  unfold harperScheduledVaryingEulerEnergy harperVaryingEulerEnergy
    harperScheduledPrimeRangeFrom
  rw [Finset.prod_biUnion
    (pairwiseDisjoint_harperScheduledPrimeBlock_add y start n)]
  rw [Finset.prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro p hp
  rw [harperScheduledPrimeHeight_eq y start n u
    ⟨i, by simp⟩ hp]

/-- Exact first moment of the actual varying-height scheduled product. -/
theorem integral_harperScheduledVaryingEulerEnergy
    (y start n : Nat) (u : Fin n -> Real) :
    integral (harperFairCubeLaw y)
        (harperScheduledVaryingEulerEnergy y start n u) =
      ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
        (1 + (p.1 : Real)⁻¹) := by
  apply Eq.trans _ (integral_harperVaryingEulerEnergy y
    (harperScheduledPrimeRangeFrom y start n)
    (harperScheduledPrimeHeight y start n u))
  apply integral_congr_ae
  exact ae_of_all (harperFairCubeLaw y) fun eta =>
    harperScheduledVaryingEulerEnergy_eq_rangeFrom y start n u eta

/-- Markov's inequality for one scheduled varying-height Euler product. -/
theorem harperFairCubeLaw_real_scheduledVaryingEulerEnergy_ge_le
    (y start n : Nat) (u : Fin n -> Real) {T : Real} (hT : 0 < T) :
    (harperFairCubeLaw y).real
        {eta | T <= harperScheduledVaryingEulerEnergy y start n u eta} <=
      (∏ p ∈ harperScheduledPrimeRangeFrom y start n,
        (1 + (p.1 : Real)⁻¹)) / T := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := harperFairCubeLaw y)
    (ae_of_all _ fun eta =>
      harperScheduledVaryingEulerEnergy_nonneg y start n u eta)
    (Integrable.of_finite : Integrable
      (harperScheduledVaryingEulerEnergy y start n u)
      (harperFairCubeLaw y)) T
  rw [integral_harperScheduledVaryingEulerEnergy] at hmarkov
  exact (le_div_iff₀ hT).2 (by simpa [mul_comm] using! hmarkov)

/-- Union-bound form used after discretizing the vertical variable. -/
theorem harperFairCubeLaw_real_iUnion_scheduledVaryingEulerEnergy_ge_le
    {a : Type*} (s : Finset a)
    (y start n : Nat) (u : a -> Fin n -> Real)
    (T : a -> Real) (hT : ∀ z, z ∈ s -> 0 < T z) :
    (harperFairCubeLaw y).real
        (⋃ z ∈ s,
          {eta | T z <= harperScheduledVaryingEulerEnergy
            y start n (u z) eta}) <=
      ∑ z ∈ s,
        (∏ p ∈ harperScheduledPrimeRangeFrom y start n,
          (1 + (p.1 : Real)⁻¹)) / T z := by
  classical
  calc
    (harperFairCubeLaw y).real
        (⋃ z ∈ s,
          {eta | T z <= harperScheduledVaryingEulerEnergy
            y start n (u z) eta}) <=
        ∑ z ∈ s, (harperFairCubeLaw y).real
          {eta | T z <= harperScheduledVaryingEulerEnergy
            y start n (u z) eta} :=
      measureReal_biUnion_finset_le s _
    _ <= ∑ z ∈ s,
        (∏ p ∈ harperScheduledPrimeRangeFrom y start n,
          (1 + (p.1 : Real)⁻¹)) / T z := by
      exact Finset.sum_le_sum fun z hz =>
        harperFairCubeLaw_real_scheduledVaryingEulerEnergy_ge_le
          y start n (u z) (hT z hz)

end Problem520
end Erdos
