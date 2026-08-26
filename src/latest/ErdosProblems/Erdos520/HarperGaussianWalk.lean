import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Nat.Log
import ErdosProblems.Erdos520.HarperGaussianBarrier

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos
namespace Problem520

noncomputable section

/-!
# A killed standard-Gaussian walk

This file iterates the one-step superharmonic estimate from
`HarperGaussianBarrier`.  The recursion is the dynamic-programming value of
the affine terminal potential for a standard-Gaussian walk killed when its
distance from the barrier becomes negative.
-/

/-- The `n`-step killed affine potential.  Starting at distance `x` from the
barrier, a step `z` is retained precisely when `z ≤ x`; after that step the
new distance is `x - z`. -/
noncomputable def gaussianKilledPotential : ℕ → ℝ → ℝ
  | 0, x => x + 2
  | n + 1, x =>
      ∫ z in Iic x, gaussianKilledPotential n (x - z) ∂gaussianReal 0 1

@[simp]
theorem gaussianKilledPotential_zero (x : ℝ) :
    gaussianKilledPotential 0 x = x + 2 := rfl

@[simp]
theorem gaussianKilledPotential_succ (n : ℕ) (x : ℝ) :
    gaussianKilledPotential (n + 1) x =
      ∫ z in Iic x, gaussianKilledPotential n (x - z) ∂gaussianReal 0 1 := rfl

private theorem integrable_id_gaussianReal_zero_one :
    Integrable (fun z : ℝ ↦ z) (gaussianReal 0 1) := by
  exact memLp_one_iff_integrable.mp
    (by simpa only [id_eq] using!
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 1 (by norm_num)))

private theorem integrable_gaussianBarrierAffine (x : ℝ) :
    Integrable (fun z : ℝ ↦ x - z + 2) (gaussianReal 0 1) := by
  exact ((integrable_const (μ := gaussianReal 0 1) x).sub
    integrable_id_gaussianReal_zero_one).add
      (integrable_const (μ := gaussianReal 0 1) 2)

/-- At every finite time the killed potential is nonnegative and is bounded
by its initial affine value.  This is the finite-step supermartingale
estimate, proved without any ballot theorem. -/
theorem gaussianKilledPotential_nonneg_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gaussianKilledPotential n x ∧ gaussianKilledPotential n x ≤ x + 2 := by
  induction n generalizing x with
  | zero =>
      simp only [gaussianKilledPotential_zero]
      constructor <;> linarith
  | succ n ih =>
      rw [gaussianKilledPotential_succ]
      have hnonneg :
          0 ≤ᵐ[(gaussianReal 0 1).restrict (Iic x)]
            fun z ↦ gaussianKilledPotential n (x - z) := by
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦
          (ih (sub_nonneg.mpr hz)).1
      have hle :
          (fun z ↦ gaussianKilledPotential n (x - z)) ≤ᵐ[
              (gaussianReal 0 1).restrict (Iic x)]
            fun z ↦ x - z + 2 := by
        exact (ae_restrict_mem measurableSet_Iic).mono fun z hz ↦
          (ih (sub_nonneg.mpr hz)).2
      constructor
      · exact integral_nonneg_of_ae hnonneg
      · calc
          (∫ z in Iic x,
              gaussianKilledPotential n (x - z) ∂gaussianReal 0 1) ≤
              ∫ z in Iic x, (x - z + 2) ∂gaussianReal 0 1 := by
            exact integral_mono_of_nonneg hnonneg
              (integrable_gaussianBarrierAffine x).integrableOn hle
          _ ≤ x + 2 := integral_Iic_gaussianReal_barrierPotential_le hx

theorem gaussianKilledPotential_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gaussianKilledPotential n x :=
  (gaussianKilledPotential_nonneg_le n hx).1

theorem gaussianKilledPotential_le (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gaussianKilledPotential n x ≤ x + 2 :=
  (gaussianKilledPotential_nonneg_le n hx).2

/-- The terminal distance of an unrestricted finite walk. -/
def gaussianWalkTerminalDistance (n : ℕ) (x : ℝ) (omega : Fin n → ℝ) : ℝ :=
  x - ∑ i, omega i

/-- Recursive barrier event, ordered with the first coordinate as the first
Gaussian increment. -/
def gaussianWalkSurvives : (n : ℕ) → ℝ → (Fin n → ℝ) → Prop
  | 0, _x, _omega => True
  | n + 1, x, omega =>
      omega 0 ≤ x ∧ gaussianWalkSurvives n (x - omega 0) (fun i ↦ omega i.succ)

/-- Terminal affine payoff, set to zero on paths killed at the barrier. -/
def gaussianWalkKilledPayoff : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ
  | 0, x, _omega => x + 2
  | n + 1, x, omega =>
      if omega 0 ≤ x then
        gaussianWalkKilledPayoff n (x - omega 0) (fun i ↦ omega i.succ)
      else 0

@[simp]
theorem gaussianWalkKilledPayoff_zero (x : ℝ) (omega : Fin 0 → ℝ) :
    gaussianWalkKilledPayoff 0 x omega = x + 2 := rfl

@[simp]
theorem gaussianWalkKilledPayoff_succ (n : ℕ) (x : ℝ)
    (omega : Fin (n + 1) → ℝ) :
    gaussianWalkKilledPayoff (n + 1) x omega =
      if omega 0 ≤ x then
        gaussianWalkKilledPayoff n (x - omega 0) (fun i ↦ omega i.succ)
      else 0 := rfl

theorem measurable_gaussianWalkKilledPayoff_joint (n : ℕ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) ↦
      gaussianWalkKilledPayoff n p.1 p.2) := by
  induction n with
  | zero =>
      simpa only [gaussianWalkKilledPayoff_zero] using!
        (measurable_fst.add measurable_const)
  | succ n ih =>
      simp only [gaussianWalkKilledPayoff_succ]
      have hhead : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ p.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable
          (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ fun i : Fin n ↦ p.2 i.succ) :=
        measurable_pi_lambda _ fun i ↦
          (measurable_pi_apply i.succ).comp measurable_snd
      apply Measurable.ite
      · exact measurableSet_le hhead measurable_fst
      · exact ih.comp ((measurable_fst.sub hhead).prodMk htail)
      · exact measurable_const

theorem measurable_gaussianWalkKilledPayoff (n : ℕ) (x : ℝ) :
    Measurable (gaussianWalkKilledPayoff n x) := by
  exact (measurable_gaussianWalkKilledPayoff_joint n).comp
    (measurable_const.prodMk measurable_id)

/-- On a surviving path, the killed payoff is its terminal affine
distance. -/
theorem gaussianWalkKilledPayoff_eq_of_survives (n : ℕ) (x : ℝ)
    (omega : Fin n → ℝ) (h : gaussianWalkSurvives n x omega) :
    gaussianWalkKilledPayoff n x omega =
      gaussianWalkTerminalDistance n x omega + 2 := by
  induction n generalizing x with
  | zero => simp [gaussianWalkTerminalDistance]
  | succ n ih =>
    rw [gaussianWalkKilledPayoff_succ]
    have hfirst : omega 0 ≤ x := h.1
    rw [if_pos hfirst,
      ih (x - omega 0) (fun i ↦ omega i.succ) h.2]
    simp only [gaussianWalkTerminalDistance]
    rw [Fin.sum_univ_succ]
    ring

/-- A killed path has zero payoff. -/
theorem gaussianWalkKilledPayoff_eq_zero_of_not_survives (n : ℕ) (x : ℝ)
    (omega : Fin n → ℝ) (h : ¬gaussianWalkSurvives n x omega) :
    gaussianWalkKilledPayoff n x omega = 0 := by
  induction n generalizing x with
  | zero => exact (h trivial).elim
  | succ n ih =>
      rw [gaussianWalkKilledPayoff_succ]
      by_cases hfirst : omega 0 ≤ x
      · rw [if_pos hfirst]
        apply ih
        intro htail
        exact h ⟨hfirst, htail⟩
      · rw [if_neg hfirst]

/-- A simple `L¹` majorant for the killed terminal payoff. -/
theorem norm_gaussianWalkKilledPayoff_le (n : ℕ) (x : ℝ)
    (omega : Fin n → ℝ) :
    ‖gaussianWalkKilledPayoff n x omega‖ ≤
      |x| + ∑ i, |omega i| + 2 := by
  by_cases h : gaussianWalkSurvives n x omega
  · rw [gaussianWalkKilledPayoff_eq_of_survives n x omega h]
    simp only [gaussianWalkTerminalDistance]
    calc
      |x - ∑ i, omega i + 2| ≤ |x - ∑ i, omega i| + 2 := by
        simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using!
          abs_add_le (x - ∑ i, omega i) 2
      _ ≤ |x| + |∑ i, omega i| + 2 := by
        gcongr
        exact abs_sub x (∑ i, omega i)
      _ ≤ |x| + ∑ i, |omega i| + 2 := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
  · rw [gaussianWalkKilledPayoff_eq_zero_of_not_survives n x omega h, norm_zero]
    positivity

theorem integrable_gaussianWalkKilledPayoff (n : ℕ) (x : ℝ) :
    Integrable (gaussianWalkKilledPayoff n x)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  let Pn : Measure (Fin n → ℝ) :=
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  have heval (i : Fin n) :
      Integrable (fun omega : Fin n → ℝ ↦ omega i) Pn := by
    exact integrable_eval integrable_id_gaussianReal_zero_one
  have habs (i : Fin n) :
      Integrable (fun omega : Fin n → ℝ ↦ |omega i|) Pn := by
    simpa only [Real.norm_eq_abs] using! (heval i).norm
  have hmajorant : Integrable
      (fun omega : Fin n → ℝ ↦ |x| + ∑ i, |omega i| + 2) Pn := by
    fun_prop
  exact hmajorant.mono'
    (measurable_gaussianWalkKilledPayoff n x).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_gaussianWalkKilledPayoff_le n x))

/-- The dynamic-programming recursion is exactly the expected killed payoff
on the finite iid standard-Gaussian product space. -/
theorem integral_gaussianWalkKilledPayoff_eq (n : ℕ) (x : ℝ) :
    (∫ omega : Fin n → ℝ, gaussianWalkKilledPayoff n x omega
      ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) =
        gaussianKilledPotential n x := by
  induction n generalizing x with
  | zero =>
      simp [gaussianWalkKilledPayoff, gaussianKilledPotential]
  | succ n ih =>
      let gamma : Measure ℝ := gaussianReal 0 1
      let Ptail : Measure (Fin n → ℝ) :=
        Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ ℝ) 0
      have hmp :=
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) 0).symm
      have he_symm (p : ℝ × (Fin n → ℝ)) :
          e.symm p = Fin.cons p.1 p.2 := by
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv]
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Fin.zero_succAbove]
      have hint : Integrable
          (fun p : ℝ × (Fin n → ℝ) ↦
            gaussianWalkKilledPayoff (n + 1) x (e.symm p))
          (gamma.prod Ptail) := by
        exact hmp.integrable_comp_of_integrable
          (integrable_gaussianWalkKilledPayoff (n + 1) x)
      rw [← hmp.integral_comp']
      rw [integral_prod _ hint]
      simp_rw [he_symm]
      simp only [Fin.cons_zero, Fin.cons_succ, gaussianWalkKilledPayoff_succ]
      rw [gaussianKilledPotential_succ]
      rw [← integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        by_cases hz : z ≤ x
        · simp only [hz, if_true, mem_Iic, Set.indicator_of_mem]
          simpa only [Ptail] using! ih (x - z)
        · have hnot : z ∉ Iic x := hz
          simp only [hz, if_false, integral_zero,
            Set.indicator_of_notMem hnot]

/-- The sum of `n` coordinates on the finite iid standard-Gaussian product
space is Gaussian with variance `n`. -/
theorem map_gaussianWalk_sum_eq (n : ℕ) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).map
        (fun omega ↦ ∑ i, omega i) =
      gaussianReal 0 (n : ℝ≥0) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_map_sum_pi_eq_prod]
  simp_rw [charFun_gaussianReal]
  rw [Finset.prod_const]
  simp only [Finset.card_univ, Fintype.card_fin, Pi.pow_apply]
  rw [charFun_gaussianReal]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Consequently, the unrestricted terminal distance from a barrier started
at `x` is Gaussian with mean `x` and variance `n`. -/
theorem map_gaussianWalkTerminalDistance_eq (n : ℕ) (x : ℝ) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).map
        (gaussianWalkTerminalDistance n x) =
      gaussianReal x (n : ℝ≥0) := by
  let S : (Fin n → ℝ) → ℝ := fun omega ↦ ∑ i, omega i
  have hfun : gaussianWalkTerminalDistance n x = (fun z ↦ x - z) ∘ S := by
    funext omega
    rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    show (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).map S =
      gaussianReal 0 (n : ℝ≥0) by simpa only [S] using! map_gaussianWalk_sum_eq n,
    gaussianReal_map_const_sub]
  simp only [sub_zero]

theorem gaussianWalkTerminalDistance_nonneg_of_survives
    (n : ℕ) (x : ℝ) (omega : Fin n → ℝ) (hx : 0 ≤ x)
    (h : gaussianWalkSurvives n x omega) :
    0 ≤ gaussianWalkTerminalDistance n x omega := by
  induction n generalizing x with
  | zero =>
      simpa [gaussianWalkTerminalDistance] using! hx
  | succ n ih =>
      have htail := ih (x - omega 0) (fun i ↦ omega i.succ)
        (sub_nonneg.mpr h.1) h.2
      simp only [gaussianWalkTerminalDistance] at htail ⊢
      rw [Fin.sum_univ_succ]
      linarith

/-- The measurable finite-path survival event. -/
def gaussianWalkSurvivalSet (n : ℕ) (x : ℝ) : Set (Fin n → ℝ) :=
  {omega | gaussianWalkSurvives n x omega}

theorem measurableSet_gaussianWalkSurvivalSet (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    MeasurableSet (gaussianWalkSurvivalSet n x) := by
  have heq : gaussianWalkSurvivalSet n x =
      gaussianWalkKilledPayoff n x ⁻¹' Ioi 0 := by
    ext omega
    simp only [gaussianWalkSurvivalSet, mem_setOf_eq, mem_preimage, mem_Ioi]
    constructor
    · intro h
      rw [gaussianWalkKilledPayoff_eq_of_survives n x omega h]
      linarith [gaussianWalkTerminalDistance_nonneg_of_survives n x omega hx h]
    · intro hpos
      by_contra hsurv
      rw [gaussianWalkKilledPayoff_eq_zero_of_not_survives n x omega hsurv]
        at hpos
      linarith
  rw [heq]
  exact (measurable_gaussianWalkKilledPayoff n x) measurableSet_Ioi

theorem integrable_gaussianWalkTerminalDistance (n : ℕ) (x : ℝ) :
    Integrable (gaussianWalkTerminalDistance n x)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  have heval (i : Fin n) : Integrable
      (fun omega : Fin n → ℝ ↦ omega i)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
    exact integrable_eval integrable_id_gaussianReal_zero_one
  unfold gaussianWalkTerminalDistance
  have hsum : Integrable (fun omega : Fin n → ℝ ↦ ∑ i, omega i)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
    exact integrable_finset_sum Finset.univ fun i _hi ↦ heval i
  exact (integrable_const (μ :=
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) x).sub hsum

/-- The killed-potential recursion is the affine terminal moment on the
actual survival event. -/
theorem integralOn_gaussianWalkSurvival_terminal_eq (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∫ omega in gaussianWalkSurvivalSet n x,
        (gaussianWalkTerminalDistance n x omega + 2)
        ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) =
      gaussianKilledPotential n x := by
  calc
    (∫ omega in gaussianWalkSurvivalSet n x,
        (gaussianWalkTerminalDistance n x omega + 2)
        ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) =
        ∫ omega : Fin n → ℝ,
          gaussianWalkKilledPayoff n x omega
          ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) := by
      rw [← integral_indicator (measurableSet_gaussianWalkSurvivalSet n hx)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega ↦ by
        by_cases h : gaussianWalkSurvives n x omega
        · have hmem : omega ∈ gaussianWalkSurvivalSet n x := h
          rw [Set.indicator_of_mem hmem,
            gaussianWalkKilledPayoff_eq_of_survives n x omega h]
        · have hmem : omega ∉ gaussianWalkSurvivalSet n x := h
          rw [Set.indicator_of_notMem hmem,
            gaussianWalkKilledPayoff_eq_zero_of_not_survives n x omega h]
    _ = gaussianKilledPotential n x :=
      integral_gaussianWalkKilledPayoff_eq n x

/-- Terminal-density completion of the soft barrier argument.  If the
unrestricted endpoint has Gaussian law and the killed affine potential has
expectation at most its initial value, splitting at terminal distance `r`
gives the displayed near/far estimate. -/
theorem measureReal_gaussianWalk_barrier_le
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P] {A : Set Omega} (hA : MeasurableSet A)
    {D : Omega → ℝ} (hDmeas : Measurable D)
    {x : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {r : ℝ} (hr : 0 < r)
    (hlaw : P.map D = gaussianReal x v)
    (hDnonneg : ∀ omega ∈ A, 0 ≤ D omega)
    (hDintegrable : IntegrableOn (fun omega ↦ D omega + 2) A P)
    (hweighted : ∫ omega in A, (D omega + 2) ∂P ≤ x + 2) :
    P.real A ≤ (x + 2) / r + r / Real.sqrt (v : ℝ) := by
  let near : Set Omega := D ⁻¹' Icc 0 r
  have hnear : MeasurableSet near := hDmeas measurableSet_Icc
  have hfar : ∀ omega ∈ A \ near, r ≤ D omega + 2 := by
    intro omega homega
    have hD0 : 0 ≤ D omega := hDnonneg omega homega.1
    have hnot : D omega ∉ Icc (0 : ℝ) r := homega.2
    have hrD : r < D omega := by
      by_contra h
      exact hnot ⟨hD0, le_of_not_gt h⟩
    linarith
  have hnearMass : P.real (A ∩ near) ≤
      r * (1 / Real.sqrt (v : ℝ)) := by
    calc
      P.real (A ∩ near) ≤ P.real near :=
        measureReal_mono inter_subset_right
      _ = (P.map D).real (Icc 0 r) := by
        exact (map_measureReal_apply hDmeas measurableSet_Icc).symm
      _ = (gaussianReal x v).real (Icc 0 r) := by rw [hlaw]
      _ ≤ r / Real.sqrt (v : ℝ) := by
        simpa only [sub_zero] using!
          gaussianReal_real_Icc_le_inv_sqrt x hv hr.le
      _ = r * (1 / Real.sqrt (v : ℝ)) := by ring
  have hsplit := measureReal_barrier_le_of_terminal_split P hA hnear hr
    (D := fun omega ↦ D omega + 2)
    (fun omega homega ↦ by linarith [hDnonneg omega homega])
    hDintegrable hfar hweighted hnearMass
  simpa only [div_eq_mul_inv, one_mul] using! hsplit

/-- Optimized fourth-root form of `measureReal_gaussianWalk_barrier_le`.
The loss `v⁻¹/⁴` is weaker than the sharp Gaussian ballot exponent but is
already a genuine polynomial survival saving. -/
theorem measureReal_gaussianWalk_barrier_le_fourthRoot
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P] {A : Set Omega} (hA : MeasurableSet A)
    {D : Omega → ℝ} (hDmeas : Measurable D)
    {x : ℝ} {v : ℝ≥0} (hv : v ≠ 0)
    (hlaw : P.map D = gaussianReal x v)
    (hDnonneg : ∀ omega ∈ A, 0 ≤ D omega)
    (hDintegrable : IntegrableOn (fun omega ↦ D omega + 2) A P)
    (hweighted : ∫ omega in A, (D omega + 2) ∂P ≤ x + 2) :
    P.real A ≤
      (x + 3) / Real.sqrt (Real.sqrt (v : ℝ)) := by
  have hvreal : 0 < (v : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvreal
  have hr : 0 < Real.sqrt (Real.sqrt (v : ℝ)) :=
    Real.sqrt_pos.2 hsqrt
  have hbase := measureReal_gaussianWalk_barrier_le P hA hDmeas hv hr
    hlaw hDnonneg hDintegrable hweighted
  calc
    P.real A ≤
        (x + 2) / Real.sqrt (Real.sqrt (v : ℝ)) +
          Real.sqrt (Real.sqrt (v : ℝ)) / Real.sqrt (v : ℝ) := hbase
    _ = (x + 3) / Real.sqrt (Real.sqrt (v : ℝ)) := by
      have hsquare : (Real.sqrt (Real.sqrt (v : ℝ))) ^ 2 =
          Real.sqrt (v : ℝ) := Real.sq_sqrt hsqrt.le
      field_simp [hr.ne', hsqrt.ne']
      nlinarith

/-- The genuinely optimized near/far split.  Its square-root dependence on
the starting potential is the form suitable for a dyadic Markov bootstrap. -/
theorem measureReal_gaussianWalk_barrier_le_optimized
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P] {A : Set Omega} (hA : MeasurableSet A)
    {D : Omega → ℝ} (hDmeas : Measurable D)
    {x : ℝ} (hx : 0 ≤ x) {v : ℝ≥0} (hv : v ≠ 0)
    (hlaw : P.map D = gaussianReal x v)
    (hDnonneg : ∀ omega ∈ A, 0 ≤ D omega)
    (hDintegrable : IntegrableOn (fun omega ↦ D omega + 2) A P)
    (hweighted : ∫ omega in A, (D omega + 2) ∂P ≤ x + 2) :
    P.real A ≤
      2 * Real.sqrt (x + 2) / Real.sqrt (Real.sqrt (v : ℝ)) := by
  let a : ℝ := x + 2
  let b : ℝ := Real.sqrt (v : ℝ)
  have ha : 0 < a := by dsimp [a]; linarith
  have hvreal : 0 < (v : ℝ) := by positivity
  have hb : 0 < b := by exact Real.sqrt_pos.2 hvreal
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hr : 0 < Real.sqrt (a * b) := Real.sqrt_pos.2 (mul_pos ha hb)
  have hbase := measureReal_gaussianWalk_barrier_le P hA hDmeas hv hr
    hlaw hDnonneg hDintegrable hweighted
  have hsqrtMul : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul ha.le]
  calc
    P.real A ≤ a / Real.sqrt (a * b) + Real.sqrt (a * b) / b := by
      simpa only [a, b] using! hbase
    _ = 2 * Real.sqrt a / Real.sqrt b := by
      rw [hsqrtMul]
      have hsaSq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha.le
      have hsbSq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
      field_simp [hsa.ne', hsb.ne', hb.ne']
      nlinarith
    _ = 2 * Real.sqrt (x + 2) /
        Real.sqrt (Real.sqrt (v : ℝ)) := by rfl

/-- Unconditional finite-walk soft ballot estimate. -/
theorem gaussianWalk_survival_probability_le_fourthRoot
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).real
        (gaussianWalkSurvivalSet n x) ≤
      2 * Real.sqrt (x + 2) /
        Real.sqrt (Real.sqrt (n : ℝ)) := by
  let Pn : Measure (Fin n → ℝ) :=
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
  let D : (Fin n → ℝ) → ℝ := gaussianWalkTerminalDistance n x
  have hv : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hDmeas : Measurable D := by
    unfold D gaussianWalkTerminalDistance
    fun_prop
  have hlaw : Pn.map D = gaussianReal x (n : ℝ≥0) := by
    simpa only [Pn, D] using! map_gaussianWalkTerminalDistance_eq n x
  have hnonneg : ∀ omega ∈ gaussianWalkSurvivalSet n x, 0 ≤ D omega := by
    intro omega homega
    exact gaussianWalkTerminalDistance_nonneg_of_survives n x omega hx homega
  have hint : IntegrableOn (fun omega ↦ D omega + 2)
      (gaussianWalkSurvivalSet n x) Pn := by
    have hfull : Integrable (fun omega : Fin n → ℝ ↦
        gaussianWalkTerminalDistance n x omega + 2)
        (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) :=
      (integrable_gaussianWalkTerminalDistance n x).add
        (integrable_const (μ :=
          Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) 2)
    simpa only [Pn, D] using! hfull.integrableOn
  have hweighted : (∫ omega in gaussianWalkSurvivalSet n x,
      (D omega + 2) ∂Pn) ≤ x + 2 := by
    have heq := integralOn_gaussianWalkSurvival_terminal_eq n hx
    rw [show (∫ omega in gaussianWalkSurvivalSet n x,
        (D omega + 2) ∂Pn) = gaussianKilledPotential n x by
          simpa only [Pn, D] using! heq]
    exact gaussianKilledPotential_le n hx
  simpa only [Pn, NNReal.coe_natCast] using!
    (measureReal_gaussianWalk_barrier_le_optimized Pn
      (measurableSet_gaussianWalkSurvivalSet n hx) hDmeas
      (x := x) hx (v := (n : ℝ≥0)) hv hlaw hnonneg hint hweighted)

/-! ## Markov concatenation -/

/-- Iteration of the killed Gaussian transition operator with arbitrary
terminal payoff. -/
noncomputable def gaussianKilledExpectation : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, x => f x
  | n + 1, f, x =>
      ∫ z in Iic x, gaussianKilledExpectation n f (x - z)
        ∂gaussianReal 0 1

@[simp]
theorem gaussianKilledExpectation_zero (f : ℝ → ℝ) (x : ℝ) :
    gaussianKilledExpectation 0 f x = f x := rfl

@[simp]
theorem gaussianKilledExpectation_succ (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    gaussianKilledExpectation (n + 1) f x =
      ∫ z in Iic x, gaussianKilledExpectation n f (x - z)
        ∂gaussianReal 0 1 := rfl

/-- Exact Markov/concatenation identity for the killed transition. -/
theorem gaussianKilledExpectation_add (m n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    gaussianKilledExpectation (m + n) f x =
      gaussianKilledExpectation m (gaussianKilledExpectation n f) x := by
  induction m generalizing x with
  | zero => simp only [Nat.zero_add, gaussianKilledExpectation_zero]
  | succ m ih =>
      rw [Nat.succ_add, gaussianKilledExpectation_succ,
        gaussianKilledExpectation_succ]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ ih (x - z)

/-- A terminal payoff evaluated only on paths that survive. -/
noncomputable def gaussianWalkKilledTerminalPayoff
    (f : ℝ → ℝ) : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ
  | 0, x, _omega => f x
  | n + 1, x, omega =>
      if omega 0 ≤ x then
        gaussianWalkKilledTerminalPayoff f n (x - omega 0)
          (fun i ↦ omega i.succ)
      else 0

theorem measurable_gaussianWalkKilledTerminalPayoff_joint
    {f : ℝ → ℝ} (hf : Measurable f) (n : ℕ) :
    Measurable (fun p : ℝ × (Fin n → ℝ) ↦
      gaussianWalkKilledTerminalPayoff f n p.1 p.2) := by
  induction n with
  | zero => simpa [gaussianWalkKilledTerminalPayoff] using! hf.comp measurable_fst
  | succ n ih =>
      simp only [gaussianWalkKilledTerminalPayoff]
      have hhead : Measurable (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ p.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      have htail : Measurable
          (fun p : ℝ × (Fin (n + 1) → ℝ) ↦ fun i : Fin n ↦ p.2 i.succ) :=
        measurable_pi_lambda _ fun i ↦
          (measurable_pi_apply i.succ).comp measurable_snd
      apply Measurable.ite
      · exact measurableSet_le hhead measurable_fst
      · exact ih.comp ((measurable_fst.sub hhead).prodMk htail)
      · exact measurable_const

theorem measurable_gaussianWalkKilledTerminalPayoff
    {f : ℝ → ℝ} (hf : Measurable f) (n : ℕ) (x : ℝ) :
    Measurable (gaussianWalkKilledTerminalPayoff f n x) :=
  (measurable_gaussianWalkKilledTerminalPayoff_joint hf n).comp
    (measurable_const.prodMk measurable_id)

theorem norm_gaussianWalkKilledTerminalPayoff_le
    {f : ℝ → ℝ} {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C)
    (n : ℕ) (x : ℝ) (omega : Fin n → ℝ) :
    ‖gaussianWalkKilledTerminalPayoff f n x omega‖ ≤ C := by
  induction n generalizing x with
  | zero => simpa [gaussianWalkKilledTerminalPayoff] using! hC x
  | succ n ih =>
      rw [gaussianWalkKilledTerminalPayoff]
      split_ifs
      · exact ih (x - omega 0) (fun i ↦ omega i.succ)
      · simpa only [norm_zero] using! (norm_nonneg (f x)).trans (hC x)

theorem integrable_gaussianWalkKilledTerminalPayoff
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) (n : ℕ) (x : ℝ) :
    Integrable (gaussianWalkKilledTerminalPayoff f n x)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  exact (integrable_const (μ :=
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) C).mono'
      (measurable_gaussianWalkKilledTerminalPayoff hf n x).aestronglyMeasurable
      (Filter.Eventually.of_forall
        (norm_gaussianWalkKilledTerminalPayoff_le hC n x))

/-- Finite-product realization of the killed Markov operator for any
measurable bounded terminal payoff. -/
theorem integral_gaussianWalkKilledTerminalPayoff_eq
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) (n : ℕ) (x : ℝ) :
    (∫ omega : Fin n → ℝ,
        gaussianWalkKilledTerminalPayoff f n x omega
        ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) =
      gaussianKilledExpectation n f x := by
  induction n generalizing x with
  | zero => simp [gaussianWalkKilledTerminalPayoff, gaussianKilledExpectation]
  | succ n ih =>
      let gamma : Measure ℝ := gaussianReal 0 1
      let Ptail : Measure (Fin n → ℝ) :=
        Measure.pi fun _ : Fin n ↦ gaussianReal 0 1
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) ↦ ℝ) 0
      have hmp :=
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) 0).symm
      have he_symm (p : ℝ × (Fin n → ℝ)) :
          e.symm p = Fin.cons p.1 p.2 := by
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv]
        · simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv, Fin.zero_succAbove]
      have hint : Integrable
          (fun p : ℝ × (Fin n → ℝ) ↦
            gaussianWalkKilledTerminalPayoff f (n + 1) x (e.symm p))
          (gamma.prod Ptail) := by
        exact hmp.integrable_comp_of_integrable
          (integrable_gaussianWalkKilledTerminalPayoff hf hC (n + 1) x)
      rw [← hmp.integral_comp']
      rw [integral_prod _ hint]
      simp_rw [he_symm]
      simp only [Fin.cons_zero, Fin.cons_succ,
        gaussianWalkKilledTerminalPayoff]
      rw [gaussianKilledExpectation_succ]
      rw [← integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z ↦ by
        by_cases hz : z ≤ x
        · simp only [hz, if_true, mem_Iic, Set.indicator_of_mem]
          simpa only [Ptail] using! ih (x - z)
        · have hnot : z ∉ Iic x := hz
          simp only [hz, if_false, integral_zero,
            Set.indicator_of_notMem hnot]

theorem gaussianWalkKilledTerminalPayoff_eq_of_survives
    (f : ℝ → ℝ) (n : ℕ) (x : ℝ) (omega : Fin n → ℝ)
    (h : gaussianWalkSurvives n x omega) :
    gaussianWalkKilledTerminalPayoff f n x omega =
      f (gaussianWalkTerminalDistance n x omega) := by
  induction n generalizing x with
  | zero => simp [gaussianWalkKilledTerminalPayoff, gaussianWalkTerminalDistance]
  | succ n ih =>
      rw [gaussianWalkKilledTerminalPayoff, if_pos h.1,
        ih (x - omega 0) (fun i ↦ omega i.succ) h.2]
      simp only [gaussianWalkTerminalDistance]
      rw [Fin.sum_univ_succ]
      congr 1
      ring

theorem gaussianWalkKilledTerminalPayoff_eq_zero_of_not_survives
    (f : ℝ → ℝ) (n : ℕ) (x : ℝ) (omega : Fin n → ℝ)
    (h : ¬gaussianWalkSurvives n x omega) :
    gaussianWalkKilledTerminalPayoff f n x omega = 0 := by
  induction n generalizing x with
  | zero => exact (h trivial).elim
  | succ n ih =>
      rw [gaussianWalkKilledTerminalPayoff]
      by_cases hfirst : omega 0 ≤ x
      · rw [if_pos hfirst]
        exact ih (x - omega 0) (fun i ↦ omega i.succ)
          (fun htail ↦ h ⟨hfirst, htail⟩)
      · rw [if_neg hfirst]

/-- Set-integral version of the Markov identity. -/
theorem integralOn_gaussianWalkSurvival_eq_killedExpectation
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ y, ‖f y‖ ≤ C) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∫ omega in gaussianWalkSurvivalSet n x,
        f (gaussianWalkTerminalDistance n x omega)
        ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) =
      gaussianKilledExpectation n f x := by
  calc
    (∫ omega in gaussianWalkSurvivalSet n x,
        f (gaussianWalkTerminalDistance n x omega)
        ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) =
        ∫ omega : Fin n → ℝ,
          gaussianWalkKilledTerminalPayoff f n x omega
          ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) := by
      rw [← integral_indicator (measurableSet_gaussianWalkSurvivalSet n hx)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun omega ↦ by
        by_cases h : gaussianWalkSurvives n x omega
        · have hmem : omega ∈ gaussianWalkSurvivalSet n x := h
          rw [Set.indicator_of_mem hmem,
            gaussianWalkKilledTerminalPayoff_eq_of_survives f n x omega h]
        · have hmem : omega ∉ gaussianWalkSurvivalSet n x := h
          rw [Set.indicator_of_notMem hmem,
            gaussianWalkKilledTerminalPayoff_eq_zero_of_not_survives f n x omega h]
    _ = gaussianKilledExpectation n f x :=
      integral_gaussianWalkKilledTerminalPayoff_eq hf hC n x

/-- Survival probability written as a killed-semigroup value. -/
noncomputable def gaussianWalkSurvivalProbability (n : ℕ) (x : ℝ) : ℝ :=
  gaussianKilledExpectation n (fun _ ↦ 1) x

theorem gaussianWalkSurvivalProbability_nonneg_le_one (n : ℕ) (x : ℝ) :
    0 ≤ gaussianWalkSurvivalProbability n x ∧
      gaussianWalkSurvivalProbability n x ≤ 1 := by
  have hint := integrable_gaussianWalkKilledTerminalPayoff
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const
    (C := 1) (fun _ ↦ by norm_num) n x
  have heq := integral_gaussianWalkKilledTerminalPayoff_eq
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const
    (C := 1) (fun _ ↦ by norm_num) n x
  have hnonneg : ∀ omega : Fin n → ℝ,
      0 ≤ gaussianWalkKilledTerminalPayoff (fun _ : ℝ ↦ (1 : ℝ)) n x omega := by
    intro omega
    by_cases h : gaussianWalkSurvives n x omega
    · rw [gaussianWalkKilledTerminalPayoff_eq_of_survives _ n x omega h]
      norm_num
    · rw [gaussianWalkKilledTerminalPayoff_eq_zero_of_not_survives _ n x omega h]
  have hle : ∀ omega : Fin n → ℝ,
      gaussianWalkKilledTerminalPayoff (fun _ : ℝ ↦ (1 : ℝ)) n x omega ≤ 1 := by
    intro omega
    by_cases h : gaussianWalkSurvives n x omega
    · rw [gaussianWalkKilledTerminalPayoff_eq_of_survives _ n x omega h]
    · rw [gaussianWalkKilledTerminalPayoff_eq_zero_of_not_survives _ n x omega h]
      norm_num
  change 0 ≤ gaussianKilledExpectation n (fun _ ↦ (1 : ℝ)) x ∧
    gaussianKilledExpectation n (fun _ ↦ (1 : ℝ)) x ≤ 1
  rw [← heq]
  constructor
  · exact integral_nonneg hnonneg
  · calc
      (∫ omega : Fin n → ℝ,
          gaussianWalkKilledTerminalPayoff (fun _ : ℝ ↦ (1 : ℝ)) n x omega
          ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) ≤
          ∫ _omega : Fin n → ℝ, (1 : ℝ)
            ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) := by
        exact integral_mono hint
          (integrable_const (μ :=
            Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) 1)
          hle
      _ = 1 := by simp

theorem measurable_gaussianWalkSurvivalProbability (n : ℕ) :
    Measurable (gaussianWalkSurvivalProbability n) := by
  have hjoint := measurable_gaussianWalkKilledTerminalPayoff_joint
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const n
  have hintMeas : Measurable (fun x : ℝ ↦
      ∫ omega : Fin n → ℝ,
        gaussianWalkKilledTerminalPayoff (fun _ : ℝ ↦ (1 : ℝ)) n x omega
        ∂Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) :=
    hjoint.stronglyMeasurable.integral_prod_right.measurable
  convert! hintMeas using 1
  funext x
  exact (integral_gaussianWalkKilledTerminalPayoff_eq
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const
    (C := 1) (fun _ ↦ by norm_num) n x).symm

/-- The semigroup definition agrees with the real measure of the concrete
finite-product survival event. -/
theorem gaussianWalkSurvivalProbability_eq_measureReal
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gaussianWalkSurvivalProbability n x =
      (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).real
        (gaussianWalkSurvivalSet n x) := by
  have h := integralOn_gaussianWalkSurvival_eq_killedExpectation
    (f := fun _ : ℝ ↦ (1 : ℝ)) measurable_const
    (C := 1) (fun _ ↦ by norm_num) n hx
  simpa only [gaussianWalkSurvivalProbability, setIntegral_const,
    smul_eq_mul, one_mul, mul_one] using! h.symm

theorem gaussianWalkSurvivalProbability_le_fourthRoot
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    gaussianWalkSurvivalProbability n x ≤
      2 * Real.sqrt (x + 2) /
        Real.sqrt (Real.sqrt (n : ℝ)) := by
  rw [gaussianWalkSurvivalProbability_eq_measureReal n hx]
  exact gaussianWalk_survival_probability_le_fourthRoot n hn hx

theorem gaussianWalkSurvivalProbability_add (m n : ℕ) (x : ℝ) :
    gaussianWalkSurvivalProbability (m + n) x =
      gaussianKilledExpectation m (gaussianWalkSurvivalProbability n) x := by
  simpa only [gaussianWalkSurvivalProbability] using!
    gaussianKilledExpectation_add m n (fun _ ↦ (1 : ℝ)) x

/-- Concrete Markov/concatenation identity: after surviving the first `m`
steps, restart from the random terminal distance for the remaining `n`
steps. -/
theorem gaussianWalkSurvivalProbability_add_eq_integralOn
    (m n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gaussianWalkSurvivalProbability (m + n) x =
      ∫ omega in gaussianWalkSurvivalSet m x,
        gaussianWalkSurvivalProbability n
          (gaussianWalkTerminalDistance m x omega)
        ∂Measure.pi (fun _ : Fin m ↦ gaussianReal 0 1) := by
  rw [gaussianWalkSurvivalProbability_add]
  symm
  apply integralOn_gaussianWalkSurvival_eq_killedExpectation
    (measurable_gaussianWalkSurvivalProbability n) (C := 1) _ m hx
  intro y
  rw [Real.norm_eq_abs, abs_of_nonneg
    (gaussianWalkSurvivalProbability_nonneg_le_one n y).1]
  exact (gaussianWalkSurvivalProbability_nonneg_le_one n y).2

/-- Cauchy--Schwarz in the exact square-root form used by the barrier
bootstrap. -/
theorem integral_sqrt_le_sqrt_measure_mul_integral
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    [IsFiniteMeasure P] {g : Omega → ℝ} (hgmeas : Measurable g)
    (hgnonneg : 0 ≤ᵐ[P] g) (hgint : Integrable g P) :
    (∫ omega, Real.sqrt (g omega) ∂P) ≤
      Real.sqrt (P.real univ) * Real.sqrt (∫ omega, g omega ∂P) := by
  have hsmeas : AEStronglyMeasurable (fun omega ↦ Real.sqrt (g omega)) P :=
    (Real.continuous_sqrt.measurable.comp hgmeas).aestronglyMeasurable
  have hsquare : Integrable (fun omega ↦ (Real.sqrt (g omega)) ^ 2) P := by
    apply hgint.congr
    filter_upwards [hgnonneg] with omega homega
    exact (Real.sq_sqrt homega).symm
  have hsLp : MemLp (fun omega ↦ Real.sqrt (g omega)) 2 P :=
    (memLp_two_iff_integrable_sq hsmeas).2 hsquare
  have hsLp' : MemLp (fun omega ↦ Real.sqrt (g omega))
      (ENNReal.ofReal (2 : ℝ)) P := by simpa using! hsLp
  have honeMeas : AEStronglyMeasurable (fun _omega : Omega ↦ (1 : ℝ)) P :=
    aestronglyMeasurable_const
  have honeLp : MemLp (fun _omega : Omega ↦ (1 : ℝ)) 2 P :=
    (memLp_two_iff_integrable_sq honeMeas).2 (by
      simpa only [one_pow] using! (integrable_const (μ := P) (1 : ℝ)))
  have honeLp' : MemLp (fun _omega : Omega ↦ (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) P := by simpa using! honeLp
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (μ := P)
    (f := fun _omega : Omega ↦ (1 : ℝ))
    (g := fun omega ↦ Real.sqrt (g omega))
    (Filter.Eventually.of_forall fun _ ↦ zero_le_one)
    (Filter.Eventually.of_forall fun omega ↦ Real.sqrt_nonneg (g omega))
    honeLp' hsLp'
  have hsquareIntegral :
      (∫ omega, (Real.sqrt (g omega)) ^ (2 : ℝ) ∂P) =
        ∫ omega, g omega ∂P := by
    apply integral_congr_ae
    filter_upwards [hgnonneg] with omega homega
    simpa using! Real.sq_sqrt homega
  have honeIntegral :
      (∫ _omega : Omega, (1 : ℝ) ^ (2 : ℝ) ∂P) = P.real univ := by
    simp
  rw [honeIntegral, hsquareIntegral] at hholder
  simpa only [one_mul, Real.sqrt_eq_rpow] using! hholder

/-- One dyadic bootstrap step: the fourth-root bound on the second half,
combined with Cauchy--Schwarz and the affine killed moment on the first half. -/
theorem gaussianWalkSurvivalProbability_add_self_le
    (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) :
    gaussianWalkSurvivalProbability (m + m) x ≤
      (2 / Real.sqrt (Real.sqrt (m : ℝ))) *
        (Real.sqrt (gaussianWalkSurvivalProbability m x) *
          Real.sqrt (x + 2)) := by
  let Pm : Measure (Fin m → ℝ) :=
    Measure.pi fun _ : Fin m ↦ gaussianReal 0 1
  let A : Set (Fin m → ℝ) := gaussianWalkSurvivalSet m x
  let D : (Fin m → ℝ) → ℝ := gaussianWalkTerminalDistance m x
  let c : ℝ := 2 / Real.sqrt (Real.sqrt (m : ℝ))
  have hA : MeasurableSet A := measurableSet_gaussianWalkSurvivalSet m hx
  have hDmeas : Measurable D := by
    unfold D gaussianWalkTerminalDistance
    fun_prop
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hD0 : ∀ omega ∈ A, 0 ≤ D omega := by
    intro omega homega
    exact gaussianWalkTerminalDistance_nonneg_of_survives m x omega hx homega
  have hgint : IntegrableOn (fun omega ↦ D omega + 2) A Pm := by
    have hfull : Integrable (fun omega : Fin m → ℝ ↦
        gaussianWalkTerminalDistance m x omega + 2)
        (Measure.pi fun _ : Fin m ↦ gaussianReal 0 1) :=
      (integrable_gaussianWalkTerminalDistance m x).add
        (integrable_const (μ :=
          Measure.pi fun _ : Fin m ↦ gaussianReal 0 1) 2)
    simpa only [Pm, D, A] using! hfull.integrableOn
  have hsqrtInt : IntegrableOn (fun omega ↦ Real.sqrt (D omega + 2)) A Pm := by
    have hmeas : AEStronglyMeasurable (fun omega ↦ Real.sqrt (D omega + 2))
        (Pm.restrict A) :=
      (Real.continuous_sqrt.measurable.comp
        (hDmeas.add measurable_const)).aestronglyMeasurable
    have hmajorant : Integrable (fun omega ↦ |D omega + 2| + 1)
        (Pm.restrict A) := hgint.norm.add (integrable_const (μ := Pm.restrict A) 1)
    apply hmajorant.mono' hmeas
    exact Filter.Eventually.of_forall fun omega ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      by_cases ht : 0 ≤ D omega + 2
      · rw [abs_of_nonneg ht]
        nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg (D omega + 2)]
      · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ht)]
        positivity
  have hsqrtBound :
      (∫ omega in A, Real.sqrt (D omega + 2) ∂Pm) ≤
        Real.sqrt (Pm.real A) *
          Real.sqrt (∫ omega in A, (D omega + 2) ∂Pm) := by
    have hnonneg : 0 ≤ᵐ[Pm.restrict A] fun omega ↦ D omega + 2 := by
      exact (ae_restrict_mem hA).mono fun omega homega ↦ by
        change 0 ≤ D omega + 2
        linarith [hD0 omega homega]
    have hcs := integral_sqrt_le_sqrt_measure_mul_integral
      (Pm.restrict A) (hDmeas.add measurable_const) hnonneg hgint
    rw [measureReal_restrict_apply MeasurableSet.univ, univ_inter] at hcs
    exact hcs
  have hmass : Pm.real A = gaussianWalkSurvivalProbability m x := by
    simpa only [Pm, A] using!
      (gaussianWalkSurvivalProbability_eq_measureReal m hx).symm
  have hmoment : (∫ omega in A, (D omega + 2) ∂Pm) ≤ x + 2 := by
    have heq := integralOn_gaussianWalkSurvival_terminal_eq m hx
    rw [show (∫ omega in A, (D omega + 2) ∂Pm) =
        gaussianKilledPotential m x by simpa only [Pm, A, D] using! heq]
    exact gaussianKilledPotential_le m hx
  have hsqrtBound' :
      (∫ omega in A, Real.sqrt (D omega + 2) ∂Pm) ≤
        Real.sqrt (gaussianWalkSurvivalProbability m x) *
          Real.sqrt (x + 2) := by
    rw [hmass] at hsqrtBound
    exact hsqrtBound.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hmoment) (Real.sqrt_nonneg _))
  calc
    gaussianWalkSurvivalProbability (m + m) x =
        ∫ omega in A,
          gaussianWalkSurvivalProbability m (D omega) ∂Pm := by
      simpa only [Pm, A, D] using!
        gaussianWalkSurvivalProbability_add_eq_integralOn m m hx
    _ ≤ ∫ omega in A, c * Real.sqrt (D omega + 2) ∂Pm := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun omega ↦
          (gaussianWalkSurvivalProbability_nonneg_le_one m (D omega)).1
      · exact hsqrtInt.const_mul c
      · exact (ae_restrict_mem hA).mono fun omega homega ↦ by
          have hsoft := gaussianWalkSurvivalProbability_le_fourthRoot m hm
            (hD0 omega homega)
          dsimp only [c]
          simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using! hsoft
    _ = c * ∫ omega in A, Real.sqrt (D omega + 2) ∂Pm := by
      rw [integral_const_mul]
    _ ≤ c * (Real.sqrt (gaussianWalkSurvivalProbability m x) *
          Real.sqrt (x + 2)) := mul_le_mul_of_nonneg_left hsqrtBound' hc0
    _ = (2 / Real.sqrt (Real.sqrt (m : ℝ))) *
        (Real.sqrt (gaussianWalkSurvivalProbability m x) *
          Real.sqrt (x + 2)) := rfl

/-- The constant `16` is stable under doubling. -/
theorem gaussianWalkSurvivalProbability_double_of_le
    (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x)
    (hprev : gaussianWalkSurvivalProbability m x ≤
      16 * (x + 2) / Real.sqrt (m : ℝ)) :
    gaussianWalkSurvivalProbability (m + m) x ≤
      16 * (x + 2) / Real.sqrt ((m + m : ℕ) : ℝ) := by
  let a : ℝ := x + 2
  let u : ℝ := Real.sqrt (m : ℝ)
  let r : ℝ := Real.sqrt u
  let s : ℝ := Real.sqrt a
  let p : ℝ := gaussianWalkSurvivalProbability m x
  have ha : 0 < a := by dsimp [a]; linarith
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hu : 0 < u := by exact Real.sqrt_pos.2 hmreal
  have hr : 0 < r := by exact Real.sqrt_pos.2 hu
  have hs : 0 < s := by exact Real.sqrt_pos.2 ha
  have hp0 : 0 ≤ p := gaussianWalkSurvivalProbability_nonneg_le_one m x |>.1
  have huSq : u ^ 2 = (m : ℝ) := Real.sq_sqrt hmreal.le
  have hrSq : r ^ 2 = u := Real.sq_sqrt hu.le
  have hsSq : s ^ 2 = a := Real.sq_sqrt ha.le
  have hsqrtP : Real.sqrt p ≤ 4 * s / r := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have heq : (4 * s / r) ^ 2 = 16 * a / u := by
        field_simp [hr.ne', hu.ne']
        nlinarith
      rw [heq]
      simpa only [p, a, u] using! hprev
  have hboot := gaussianWalkSurvivalProbability_add_self_le m hm hx
  have hcoarse : gaussianWalkSurvivalProbability (m + m) x ≤ 8 * a / u := by
    calc
      gaussianWalkSurvivalProbability (m + m) x ≤
          (2 / r) * (Real.sqrt p * s) := by
        simpa only [p, a, u, r, s] using! hboot
      _ ≤ (2 / r) * ((4 * s / r) * s) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsqrtP hs.le)
          (by positivity)
      _ = 8 * a / u := by
        field_simp [hr.ne', hu.ne']
        nlinarith
  have hv : 0 < Real.sqrt ((m + m : ℕ) : ℝ) := by
    apply Real.sqrt_pos.2
    positivity
  have hvle : Real.sqrt ((m + m : ℕ) : ℝ) ≤ 2 * u := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · push_cast
      nlinarith
  calc
    gaussianWalkSurvivalProbability (m + m) x ≤ 8 * a / u := hcoarse
    _ ≤ 16 * a / Real.sqrt ((m + m : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ hu hv).2
      have h8 : 8 * Real.sqrt ((m + m : ℕ) : ℝ) ≤ 16 * u := by
        nlinarith
      simpa only [mul_assoc, mul_comm, mul_left_comm] using!
        mul_le_mul_of_nonneg_left h8 ha.le
    _ = 16 * (x + 2) / Real.sqrt ((m + m : ℕ) : ℝ) := rfl

/-- Sharp `n⁻¹/²` survival on dyadic time scales. -/
theorem gaussianWalkSurvivalProbability_pow_two_le
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gaussianWalkSurvivalProbability (2 ^ k) x ≤
      16 * (x + 2) / Real.sqrt ((2 ^ k : ℕ) : ℝ) := by
  induction k with
  | zero =>
      have hp := (gaussianWalkSurvivalProbability_nonneg_le_one 1 x).2
      norm_num only [pow_zero, Nat.cast_one, Real.sqrt_one, div_one]
      nlinarith
  | succ k ih =>
      have hm : 0 < 2 ^ k := pow_pos (by norm_num) _
      have hdouble := gaussianWalkSurvivalProbability_double_of_le
        (2 ^ k) hm hx ih
      simpa only [pow_succ, mul_comm, two_mul] using! hdouble

theorem gaussianWalkSurvivalProbability_add_le_left
    (m n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gaussianWalkSurvivalProbability (m + n) x ≤
      gaussianWalkSurvivalProbability m x := by
  let Pm : Measure (Fin m → ℝ) :=
    Measure.pi fun _ : Fin m ↦ gaussianReal 0 1
  let A : Set (Fin m → ℝ) := gaussianWalkSurvivalSet m x
  have hmarkov := gaussianWalkSurvivalProbability_add_eq_integralOn m n hx
  calc
    gaussianWalkSurvivalProbability (m + n) x =
        ∫ omega in A,
          gaussianWalkSurvivalProbability n
            (gaussianWalkTerminalDistance m x omega) ∂Pm := by
      simpa only [Pm, A] using! hmarkov
    _ ≤ ∫ _omega in A, (1 : ℝ) ∂Pm := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun omega ↦
          (gaussianWalkSurvivalProbability_nonneg_le_one n
            (gaussianWalkTerminalDistance m x omega)).1
      · exact integrableOn_const
      · exact Filter.Eventually.of_forall fun omega ↦
          (gaussianWalkSurvivalProbability_nonneg_le_one n
            (gaussianWalkTerminalDistance m x omega)).2
    _ = Pm.real A := by
      rw [setIntegral_const]
      simp only [smul_eq_mul, mul_one]
    _ = gaussianWalkSurvivalProbability m x := by
      simpa only [Pm, A] using!
        (gaussianWalkSurvivalProbability_eq_measureReal m hx).symm

theorem gaussianWalkSurvivalProbability_antitone
    {m n : ℕ} (hmn : m ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    gaussianWalkSurvivalProbability n x ≤
      gaussianWalkSurvivalProbability m x := by
  obtain ⟨d, rfl⟩ := exists_add_of_le hmn
  exact gaussianWalkSurvivalProbability_add_le_left m d hx

/-- Sharp `n⁻¹/²` survival bound for every positive integer time. -/
theorem gaussianWalkSurvivalProbability_le
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    gaussianWalkSurvivalProbability n x ≤
      32 * (x + 2) / Real.sqrt (n : ℝ) := by
  let k : ℕ := Nat.log 2 n
  let p : ℕ := 2 ^ k
  have hpNat : 0 < p := by dsimp [p]; positivity
  have hp_le : p ≤ n := by
    exact Nat.pow_log_le_self 2 hn.ne'
  have hn_lt : n < p + p := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) n
    simpa only [k, p, pow_succ, mul_comm, two_mul] using! h
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hpNat
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  let u : ℝ := Real.sqrt (p : ℝ)
  let v : ℝ := Real.sqrt (n : ℝ)
  have hu : 0 < u := Real.sqrt_pos.2 hpReal
  have hv : 0 < v := Real.sqrt_pos.2 hnReal
  have huSq : u ^ 2 = (p : ℝ) := Real.sq_sqrt hpReal.le
  have hvle : v ≤ 2 * u := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hnCast : (n : ℝ) < (p : ℝ) + p := by exact_mod_cast hn_lt
      dsimp only [u]
      nlinarith
  calc
    gaussianWalkSurvivalProbability n x ≤
        gaussianWalkSurvivalProbability p x :=
      gaussianWalkSurvivalProbability_antitone hp_le hx
    _ ≤ 16 * (x + 2) / Real.sqrt (p : ℝ) := by
      simpa only [p, k] using! gaussianWalkSurvivalProbability_pow_two_le k hx
    _ = 16 * (x + 2) / u := rfl
    _ ≤ 32 * (x + 2) / v := by
      apply (div_le_div_iff₀ hu hv).2
      have h16 : 16 * v ≤ 32 * u := by nlinarith
      have ha : 0 ≤ x + 2 := by linarith
      simpa only [mul_assoc, mul_comm, mul_left_comm] using!
        mul_le_mul_of_nonneg_right h16 ha
    _ = 32 * (x + 2) / Real.sqrt (n : ℝ) := rfl

/-- Measure-theoretic form of the sharp finite iid Gaussian ballot bound. -/
theorem gaussianWalk_survival_probability_le
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).real
        (gaussianWalkSurvivalSet n x) ≤
      32 * (x + 2) / Real.sqrt (n : ℝ) := by
  rw [← gaussianWalkSurvivalProbability_eq_measureReal n hx]
  exact gaussianWalkSurvivalProbability_le n hn hx

/-! ## Constant-variance rescaling -/

theorem gaussianWalkSurvives_div_iff
    (n : ℕ) {s : ℝ} (hs : 0 < s) (x : ℝ) (omega : Fin n → ℝ) :
    gaussianWalkSurvives n x omega ↔
      gaussianWalkSurvives n (x / s) (fun i ↦ omega i / s) := by
  induction n generalizing x with
  | zero => simp only [gaussianWalkSurvives]
  | succ n ih =>
      simp only [gaussianWalkSurvives]
      constructor
      · rintro ⟨hfirst, htail⟩
        refine ⟨(div_le_div_iff_of_pos_right hs).2 hfirst, ?_⟩
        simpa only [sub_div] using!
          (ih (x - omega 0) (fun i ↦ omega i.succ)).1 htail
      · rintro ⟨hfirst, htail⟩
        refine ⟨(div_le_div_iff_of_pos_right hs).1 hfirst, ?_⟩
        exact (ih (x - omega 0) (fun i ↦ omega i.succ)).2
          (by simpa only [sub_div] using! htail)

theorem gaussianReal_map_div_sqrt_variance
    {v : ℝ≥0} (hv : v ≠ 0) :
    (gaussianReal 0 v).map
        (fun z ↦ z / Real.sqrt (v : ℝ)) =
      gaussianReal 0 1 := by
  have hvreal : 0 < (v : ℝ) := by positivity
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvreal
  rw [gaussianReal_map_div_const]
  have hvar : v / NNReal.mk (Real.sqrt (v : ℝ) ^ 2)
      (sq_nonneg _) = 1 := by
    ext
    simp only [NNReal.coe_div, NNReal.coe_mk, NNReal.coe_one]
    rw [Real.sq_sqrt hvreal.le]
    exact div_self hvreal.ne'
  rw [hvar]
  simp only [zero_div]

theorem map_gaussianWalk_div_sqrt_variance
    (n : ℕ) {v : ℝ≥0} (hv : v ≠ 0) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 v)).map
        (fun omega i ↦ omega i / Real.sqrt (v : ℝ)) =
      Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) := by
  let f : (i : Fin n) → ℝ → ℝ :=
    fun _ z ↦ z / Real.sqrt (v : ℝ)
  have hpi := Measure.pi_map_pi
    (μ := fun _ : Fin n ↦ gaussianReal 0 v) (f := f)
    (fun _ ↦ (by fun_prop))
  calc
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 v)).map
        (fun omega i ↦ omega i / Real.sqrt (v : ℝ)) =
        Measure.pi (fun i : Fin n ↦
          (gaussianReal 0 v).map (f i)) := by
      simpa only [f] using! hpi
    _ = Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) := by
      have hfun : (fun i : Fin n ↦ (gaussianReal 0 v).map (f i)) =
          (fun _ : Fin n ↦ gaussianReal 0 1) := by
        funext i
        simpa only [f] using! gaussianReal_map_div_sqrt_variance hv
      rw [hfun]

/-- Iid centered Gaussians of any fixed nonzero variance reduce exactly to
the standard walk. -/
theorem gaussianWalk_fixedVariance_survival_probability_le
    (n : ℕ) (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x)
    {v : ℝ≥0} (hv : v ≠ 0) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 v)).real
        (gaussianWalkSurvivalSet n x) ≤
      32 * (x / Real.sqrt (v : ℝ) + 2) /
        Real.sqrt (n : ℝ) := by
  let s : ℝ := Real.sqrt (v : ℝ)
  let F : (Fin n → ℝ) → (Fin n → ℝ) := fun omega i ↦ omega i / s
  let Pv : Measure (Fin n → ℝ) :=
    Measure.pi fun _ : Fin n ↦ gaussianReal 0 v
  have hvreal : 0 < (v : ℝ) := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 hvreal
  have hF : Measurable F := by
    unfold F
    fun_prop
  have hset : F ⁻¹' gaussianWalkSurvivalSet n (x / s) =
      gaussianWalkSurvivalSet n x := by
    ext omega
    exact (gaussianWalkSurvives_div_iff n hs x omega).symm
  calc
    Pv.real (gaussianWalkSurvivalSet n x) =
        (Pv.map F).real (gaussianWalkSurvivalSet n (x / s)) := by
      rw [map_measureReal_apply hF
        (measurableSet_gaussianWalkSurvivalSet n (div_nonneg hx hs.le))]
      rw [hset]
    _ = (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).real
        (gaussianWalkSurvivalSet n (x / s)) := by
      rw [show Pv.map F =
          Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1) by
        simpa only [Pv, F, s] using! map_gaussianWalk_div_sqrt_variance n hv]
    _ ≤ 32 * (x / s + 2) / Real.sqrt (n : ℝ) :=
      gaussianWalk_survival_probability_le n hn (div_nonneg hx hs.le)
    _ = 32 * (x / Real.sqrt (v : ℝ) + 2) /
        Real.sqrt (n : ℝ) := rfl

/-! ## Deterministic moving upper barriers -/

/-- Survival below an absolute, time-dependent barrier, with `s` the sum
already accumulated before this segment. -/
def gaussianWalkTimeBarrierSurvives :
    (n : ℕ) → ℝ → (Fin n → ℝ) → (Fin n → ℝ) → Prop
  | 0, _s, _b, _omega => True
  | n + 1, s, b, omega =>
      s + omega 0 ≤ b 0 ∧
        gaussianWalkTimeBarrierSurvives n (s + omega 0)
          (fun i ↦ b i.succ) (fun i ↦ omega i.succ)

def gaussianWalkTimeBarrierSet (n : ℕ) (s : ℝ) (b : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {omega | gaussianWalkTimeBarrierSurvives n s b omega}

theorem gaussianWalkTimeBarrierSurvives_mono
    (n : ℕ) (s : ℝ) {b c : Fin n → ℝ}
    (hbc : ∀ i, b i ≤ c i) {omega : Fin n → ℝ}
    (h : gaussianWalkTimeBarrierSurvives n s b omega) :
    gaussianWalkTimeBarrierSurvives n s c omega := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
      exact ⟨h.1.trans (hbc 0),
        ih (s + omega 0) (fun i ↦ hbc i.succ) h.2⟩

theorem gaussianWalkTimeBarrierSurvives_const_iff
    (n : ℕ) (s B : ℝ) (omega : Fin n → ℝ) :
    gaussianWalkTimeBarrierSurvives n s (fun _ ↦ B) omega ↔
      gaussianWalkSurvives n (B - s) omega := by
  induction n generalizing s with
  | zero => simp only [gaussianWalkTimeBarrierSurvives, gaussianWalkSurvives]
  | succ n ih =>
      simp only [gaussianWalkTimeBarrierSurvives, gaussianWalkSurvives]
      rw [ih (s + omega 0)]
      constructor <;> rintro ⟨hfirst, htail⟩
      · constructor
        · linarith
        · convert! htail using 1 <;> ring
      · constructor
        · linarith
        · convert! htail using 1 <;> ring

/-- Any deterministic barrier bounded by `B` is controlled by the flat
barrier at `B`. -/
theorem gaussianWalk_timeBarrier_probability_le
    (n : ℕ) (hn : 0 < n) (s B : ℝ) (b : Fin n → ℝ)
    (hstart : 0 ≤ B - s) (hb : ∀ i, b i ≤ B) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).real
        (gaussianWalkTimeBarrierSet n s b) ≤
      32 * (B - s + 2) / Real.sqrt (n : ℝ) := by
  have hsubset : gaussianWalkTimeBarrierSet n s b ⊆
      gaussianWalkSurvivalSet n (B - s) := by
    intro omega homega
    have hflat := gaussianWalkTimeBarrierSurvives_mono n s hb homega
    exact (gaussianWalkTimeBarrierSurvives_const_iff n s B omega).1 hflat
  exact (measureReal_mono hsubset).trans
    (gaussianWalk_survival_probability_le n hn hstart)

/-- A direct logarithmic-barrier corollary.  This deliberately uses the
largest barrier value, giving a robust (if non-sharp in the logarithm)
`(x + c log n)/sqrt n` bound. -/
theorem gaussianWalk_logBarrier_probability_le
    (n : ℕ) (hn : 0 < n) {x c : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ c) :
    (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)).real
        (gaussianWalkTimeBarrierSet n 0
          (fun i ↦ x + c * Real.log ((i.val + 2 : ℕ) : ℝ))) ≤
      32 * (x + c * Real.log ((n + 1 : ℕ) : ℝ) + 2) /
        Real.sqrt (n : ℝ) := by
  let B : ℝ := x + c * Real.log ((n + 1 : ℕ) : ℝ)
  have hlog0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    norm_num
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb : ∀ i : Fin n,
      x + c * Real.log ((i.val + 2 : ℕ) : ℝ) ≤ B := by
    intro i
    have hiNat : i.val + 2 ≤ n + 1 := by omega
    have hiReal : ((i.val + 2 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hiNat
    have hilog : Real.log ((i.val + 2 : ℕ) : ℝ) ≤
        Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) hiReal
    dsimp only [B]
    simpa only [add_comm] using!
      add_le_add_left (mul_le_mul_of_nonneg_left hilog hc) x
  have h := gaussianWalk_timeBarrier_probability_le n hn 0 B
    (fun i ↦ x + c * Real.log ((i.val + 2 : ℕ) : ℝ))
    (by simpa using! hB) hb
  simpa only [B, sub_zero] using! h

end
end Problem520
end Erdos
