import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic

open scoped ENNReal NNReal Topology

open Filter MeasureTheory ProbabilityTheory Set

namespace Erdos1217

namespace UpwardChain

abbrev Multiplier := {q : ℕ // 2 ≤ q}

/-- Abstract data needed to form the upward chain.  The `incoming` identity is the
stationarity/adjoint identity proved analytically for the measure used in Problem 1217. -/
structure Data where
  nu : ℕ → ℝ
  nu_one : nu 1 = 1
  nu_pos : ∀ {n : ℕ}, 1 ≤ n → 0 < nu n
  incoming : ∀ {n : ℕ}, 1 ≤ n →
    HasSum (fun q : Multiplier ↦
      nu (n * q.1) * ArithmeticFunction.vonMangoldt q.1 /
        Real.log (n * q.1)) (nu n)

variable (D : Data)

namespace Data


/-- The real-valued probability of multiplying `n` by `q`. -/
noncomputable def weight (n : ℕ) (q : Multiplier) : ℝ :=
  D.nu (n * q.1) * ArithmeticFunction.vonMangoldt q.1 /
      Real.log ((n : ℝ) * (q.1 : ℝ)) / D.nu n

lemma weight_nonneg {n : ℕ} (hn : 1 ≤ n) (q : Multiplier) :
    0 ≤ D.weight n q := by
  have hnq : 1 < n * q.1 := by
    have htwo : 1 * 2 ≤ n * q.1 := Nat.mul_le_mul hn q.2
    exact (by omega : 1 < 2).trans_le htwo
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (2 : ℝ) ≤ q.1 := by exact_mod_cast q.2
  have hnqR : (1 : ℝ) < (n : ℝ) * (q.1 : ℝ) :=
    (by norm_num : (1 : ℝ) < 1 * 2).trans_le
      (mul_le_mul hnR hqR (by positivity) (by positivity))
  exact div_nonneg
    (div_nonneg
      (mul_nonneg (D.nu_pos hnq.le).le ArithmeticFunction.vonMangoldt_nonneg)
      (Real.log_pos hnqR).le)
    (D.nu_pos hn).le

lemma hasSum_weight_one {n : ℕ} (hn : 1 ≤ n) :
    HasSum (D.weight n) 1 := by
  have h := (D.incoming hn).mul_right (D.nu n)⁻¹
  have h' : HasSum (D.weight n) (D.nu n * (D.nu n)⁻¹) :=
    h.congr_fun fun q ↦ by simp only [weight, div_eq_mul_inv, mul_assoc]
  simpa only [mul_inv_cancel₀ (ne_of_gt (D.nu_pos hn))] using h'

/-- Distribution of the multiplier at a positive state.  The arbitrary `n = 0`
row is never reached from the initial state `1`. -/
noncomputable def multiplierPMF (n : ℕ) : PMF Multiplier := by
  by_cases hn : 1 ≤ n
  · refine ⟨fun q ↦ ENNReal.ofReal (D.weight n q), ?_⟩
    apply ENNReal.hasSum_coe.mpr
    rw [← Real.toNNReal_one]
    exact (D.hasSum_weight_one hn).toNNReal (D.weight_nonneg hn)
  · exact PMF.pure ⟨2, le_rfl⟩

@[simp] lemma multiplierPMF_apply_of_pos {n : ℕ} (hn : 1 ≤ n) (q : Multiplier) :
    D.multiplierPMF n q = ENNReal.ofReal (D.weight n q) := by
  simp only [multiplierPMF, hn, ↓reduceDIte]
  rfl

lemma nu_mul_weight {n : ℕ} (hn : 1 ≤ n) (q : Multiplier) :
    D.nu n * D.weight n q =
      D.nu (n * q.1) * ArithmeticFunction.vonMangoldt q.1 /
        Real.log (n * q.1) := by
  rw [weight]
  field_simp [ne_of_gt (D.nu_pos hn)]

/-- Distribution of the next state. -/
noncomputable def nextPMF (n : ℕ) : PMF ℕ :=
  (D.multiplierPMF n).map fun q ↦ n * q.1

lemma nextPMF_apply_mul {n : ℕ} (hn : 1 ≤ n) (q : Multiplier) :
    D.nextPMF n (n * q.1) = D.multiplierPMF n q := by
  rw [nextPMF, PMF.map_apply, tsum_eq_single q]
  · simp
  · intro r hr
    split_ifs with h
    · have : r = q := Subtype.ext (Nat.mul_left_cancel (by omega) h.symm)
      exact (hr this).elim
    · rfl

/-- The time-homogeneous upward transition kernel. -/
noncomputable def transitionKernel : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun n ↦ (D.nextPMF n).toMeasure

instance : IsMarkovKernel D.transitionKernel := by
  refine ⟨fun n ↦ ?_⟩
  change IsProbabilityMeasure (D.nextPMF n).toMeasure
  infer_instance

/-- Ionescu--Tulcea kernels, written in the history-dependent interface expected
by `Kernel.trajMeasure`; only the final coordinate is used. -/
noncomputable def stepKernel (k : ℕ) :
    Kernel ((i : Finset.Iic k) → ℕ) ℕ :=
  D.transitionKernel.comap (fun x ↦ x ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance (k : ℕ) : IsMarkovKernel (D.stepKernel k) := by
  dsimp [stepKernel]
  infer_instance

/-- Law of the infinite upward trajectory starting at `1`. -/
noncomputable def pathMeasure : Measure (ℕ → ℕ) :=
  Kernel.trajMeasure (Measure.dirac 1) D.stepKernel

instance : IsProbabilityMeasure D.pathMeasure := by
  dsimp [pathMeasure]
  infer_instance

/-- A single allowed upward step. -/
def IsStep (m n : ℕ) : Prop := m < n ∧ m ∣ n

lemma nextPMF_support {n m : ℕ} (hn : 1 ≤ n) (hm : m ∈ (D.nextPMF n).support) :
    n < m ∧ n ∣ m := by
  rw [nextPMF, PMF.mem_support_map_iff] at hm
  obtain ⟨q, hq, rfl⟩ := hm
  have hnlt : n < n * 2 := by
    simpa only [mul_one] using
      (mul_lt_mul_of_pos_left (by omega : (1 : ℕ) < 2) (by omega : 0 < n))
  exact ⟨hnlt.trans_le (Nat.mul_le_mul_left n q.2), dvd_mul_right _ _⟩

lemma nextPMF_apply_eq_zero_of_not_mem_properDivisors {m n : ℕ}
    (hn : n ≠ 0) (hm : m ∉ n.properDivisors) :
    D.nextPMF m n = 0 := by
  cases m with
  | zero =>
      simp [nextPMF, multiplierPMF, hn]
  | succ m =>
      rw [PMF.apply_eq_zero_iff]
      intro hsupport
      exact hm (Nat.mem_properDivisors.mpr
        ⟨(D.nextPMF_support (by omega) hsupport).2,
          (D.nextPMF_support (by omega) hsupport).1⟩)

lemma ofReal_nu_mul_nextPMF_of_mem_properDivisors {m n : ℕ}
    (hm : m ∈ n.properDivisors) :
    ENNReal.ofReal (D.nu m) * D.nextPMF m n =
      ENNReal.ofReal (D.nu n * ArithmeticFunction.vonMangoldt (n / m) /
        Real.log n) := by
  have hmpos : 1 ≤ m := Nat.pos_of_mem_properDivisors hm
  have hq : 2 ≤ n / m := by
    have := Nat.one_lt_div_of_mem_properDivisors hm
    omega
  let q : Multiplier := ⟨n / m, hq⟩
  have hmul : m * q.1 = n := Nat.mul_div_cancel' (Nat.mem_properDivisors.mp hm).1
  rw [← hmul, D.nextPMF_apply_mul hmpos q,
    D.multiplierPMF_apply_of_pos hmpos,
    ← ENNReal.ofReal_mul (D.nu_pos hmpos).le,
    D.nu_mul_weight hmpos]
  have hdiv : m * (n / m) / m = n / m := by
    rw [Nat.mul_comm, Nat.mul_div_left _ (by omega)]
  rw [hdiv]
  simp [q, Nat.cast_mul]

lemma sum_properDivisors_incoming {n : ℕ} (hn : 2 ≤ n) :
    (∑ m ∈ n.properDivisors,
      D.nu n * ArithmeticFunction.vonMangoldt (n / m) / Real.log n) =
        D.nu n := by
  let F : ℕ → ℝ := fun q ↦
    D.nu n * ArithmeticFunction.vonMangoldt q / Real.log n
  have hn0 : n ≠ 0 := by omega
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  calc
    (∑ m ∈ n.properDivisors,
        D.nu n * ArithmeticFunction.vonMangoldt (n / m) / Real.log n) =
        ∑ m ∈ n.properDivisors, F (n / m) := by rfl
    _ = ∑ m ∈ insert n n.properDivisors, F (n / m) := by
      rw [Finset.sum_insert Nat.self_notMem_properDivisors]
      rw [Nat.div_self (by omega)]
      simp [F]
    _ = ∑ m ∈ n.divisors, F (n / m) := by
      rw [Nat.insert_self_properDivisors hn0]
    _ = ∑ q ∈ n.divisors, F q := by
      rw [← Nat.sum_divisorsAntidiagonal (fun _ q ↦ F q),
        Nat.sum_divisorsAntidiagonal' (fun _ q ↦ F q)]
    _ = ∑ q ∈ n.divisors,
        D.nu n * (ArithmeticFunction.vonMangoldt q / Real.log n) := by
      simp only [F]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = D.nu n * ((∑ q ∈ n.divisors,
        ArithmeticFunction.vonMangoldt q) / Real.log n) := by
      rw [← Finset.mul_sum, Finset.sum_div]
    _ = D.nu n := by
      rw [ArithmeticFunction.vonMangoldt_sum]
      field_simp

/-- The adjoint balance identity: if the incoming mass at every positive
predecessor `m` is `ν(m)`, then the total one-step incoming mass at `n` is
`ν(n)`. -/
lemma predecessor_balance {n : ℕ} (hn : 2 ≤ n) :
    ∑' m : ℕ, ENNReal.ofReal (D.nu m) * D.nextPMF m n =
      ENNReal.ofReal (D.nu n) := by
  rw [tsum_eq_sum (s := n.properDivisors)]
  · have hterms :
        (∑ m ∈ n.properDivisors,
          ENNReal.ofReal (D.nu m) * D.nextPMF m n) =
          ∑ m ∈ n.properDivisors,
            ENNReal.ofReal (D.nu n * ArithmeticFunction.vonMangoldt (n / m) /
              Real.log n) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact D.ofReal_nu_mul_nextPMF_of_mem_properDivisors hm
    rw [hterms]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [D.sum_properDivisors_incoming hn]
    · intro m hm
      exact div_nonneg
        (mul_nonneg (D.nu_pos (by omega)).le
          ArithmeticFunction.vonMangoldt_nonneg)
        (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).le
  · intro m hm
    rw [D.nextPMF_apply_eq_zero_of_not_mem_properDivisors (by omega) hm,
      mul_zero]

@[simp] lemma transitionKernel_apply (n : ℕ) :
    D.transitionKernel n = (D.nextPMF n).toMeasure := rfl

lemma transitionKernel_apply_singleton (n m : ℕ) :
    D.transitionKernel n {m} = D.nextPMF n m := by
  rw [transitionKernel_apply, PMF.toMeasure_apply_singleton]
  exact MeasurableSet.singleton m

lemma transitionKernel_isStep {n : ℕ} (hn : 1 ≤ n) :
    D.transitionKernel n {m | IsStep n m} = 1 := by
  rw [transitionKernel_apply, PMF.toMeasure_apply_eq_one_iff]
  · intro m hm
    exact D.nextPMF_support hn hm
  · exact (Set.to_countable {m | IsStep n m}).measurableSet

/-- The finite-time laws, equivalently obtained by repeatedly composing the
transition kernel.  Keeping them as PMFs makes all countable recurrences literal
`tsum` identities. -/
noncomputable def statePMF (D : Data) (k : ℕ) : PMF ℕ :=
  Nat.rec (PMF.pure 1) (fun _ p ↦ p.bind D.nextPMF) k

@[simp] lemma statePMF_zero : D.statePMF 0 = PMF.pure 1 := rfl

@[simp] lemma statePMF_succ (k : ℕ) :
    D.statePMF (k + 1) = (D.statePMF k).bind D.nextPMF := rfl

/-- Chapman--Kolmogorov recurrence at a singleton. -/
lemma statePMF_succ_apply (k n : ℕ) :
    D.statePMF (k + 1) n =
      ∑' m : ℕ, D.statePMF k m * D.nextPMF m n := by
  simp only [statePMF_succ, PMF.bind_apply]

lemma statePMF_support_pos {k n : ℕ} (hn : n ∈ (D.statePMF k).support) :
    1 ≤ n := by
  induction k generalizing n with
  | zero =>
      have : n = 1 := by simpa [statePMF] using hn
      omega
  | succ k ih =>
      rw [statePMF_succ, PMF.mem_support_bind_iff] at hn
      obtain ⟨m, hm, hmn⟩ := hn
      exact (D.nextPMF_support (ih hm) hmn).1.le.trans' (ih hm)

lemma statePMF_support_time_lt {k n : ℕ} (hn : n ∈ (D.statePMF k).support) :
    k < n := by
  induction k generalizing n with
  | zero => exact D.statePMF_support_pos hn
  | succ k ih =>
      rw [statePMF_succ, PMF.mem_support_bind_iff] at hn
      obtain ⟨m, hm, hmn⟩ := hn
      have hmpos := D.statePMF_support_pos hm
      have hmn' := (D.nextPMF_support hmpos hmn).1
      exact Nat.succ_le_of_lt (ih hm) |>.trans_lt hmn'

lemma statePMF_apply_eq_zero_of_le_time {k n : ℕ} (hn : n ≤ k) :
    D.statePMF k n = 0 := by
  rw [PMF.apply_eq_zero_iff]
  exact fun hmem ↦ (not_lt_of_ge hn) (D.statePMF_support_time_lt hmem)

/-- A state with `Ω(n)` prime factors can occur only in the first `Ω(n)`
positive-multiplier steps. -/
lemma statePMF_support_time_le_cardFactors {k n : ℕ}
    (hn : n ∈ (D.statePMF k).support) :
    k ≤ ArithmeticFunction.cardFactors n := by
  induction k generalizing n with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      rw [statePMF_succ, PMF.mem_support_bind_iff] at hn
      obtain ⟨m, hm, hmn⟩ := hn
      rw [nextPMF, PMF.mem_support_map_iff] at hmn
      obtain ⟨q, hq, rfl⟩ := hmn
      have hmpos := D.statePMF_support_pos hm
      have hk := ih hm
      have hqpos : 0 < q.1 := by omega
      rw [ArithmeticFunction.cardFactors_mul (by omega) hqpos.ne']
      have hOmegaq : 0 < ArithmeticFunction.cardFactors q.1 :=
        ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr (by omega)
      omega

lemma statePMF_apply_eq_zero_of_cardFactors_lt {k n : ℕ}
    (hn : ArithmeticFunction.cardFactors n < k) :
    D.statePMF k n = 0 := by
  rw [PMF.apply_eq_zero_iff]
  exact fun hmem ↦ (not_le_of_gt hn) (D.statePMF_support_time_le_cardFactors hmem)

/-- Total mass of all finite-time visits to `n`.  Strict upward motion makes
these events disjoint on the eventual path measure. -/
noncomputable def hitMass (n : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, D.statePMF k n

lemma hitMass_eq_finite_sum (n : ℕ) :
    D.hitMass n =
      ∑ k ∈ Finset.range (ArithmeticFunction.cardFactors n + 1), D.statePMF k n := by
  rw [hitMass, tsum_eq_sum]
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  exact D.statePMF_apply_eq_zero_of_cardFactors_lt hk

@[simp] lemma hitMass_one : D.hitMass 1 = 1 := by
  rw [D.hitMass_eq_finite_sum]
  simp [statePMF]

@[simp] lemma hitMass_zero : D.hitMass 0 = 0 := by
  rw [D.hitMass_eq_finite_sum]
  simp [statePMF]

/-- The visit-mass recurrence obtained by summing Chapman--Kolmogorov in time. -/
lemma hitMass_recurrence (n : ℕ) :
    D.hitMass n = (if n = 1 then 1 else 0) +
      ∑' m : ℕ, D.hitMass m * D.nextPMF m n := by
  change (∑' k : ℕ, D.statePMF k n) = (if n = 1 then 1 else 0) +
    ∑' m : ℕ, (∑' k : ℕ, D.statePMF k m) * D.nextPMF m n
  have hsplit :
      (∑' k : ℕ, D.statePMF k n) =
        D.statePMF 0 n + ∑' k : ℕ, D.statePMF (k + 1) n :=
    tsum_eq_zero_add' (f := fun k : ℕ ↦ D.statePMF k n) ENNReal.summable
  calc
    _ = D.statePMF 0 n + ∑' k : ℕ, D.statePMF (k + 1) n := hsplit
    _ = (if n = 1 then 1 else 0) +
        ∑' k : ℕ, ∑' m : ℕ, D.statePMF k m * D.nextPMF m n := by
      simp only [statePMF_zero, PMF.pure_apply, statePMF_succ_apply]
      split_ifs <;> rfl
    _ = (if n = 1 then 1 else 0) +
        ∑' m : ℕ, ∑' k : ℕ, D.statePMF k m * D.nextPMF m n := by
      rw [ENNReal.tsum_comm]
    _ = _ := by
      congr 1
      apply tsum_congr
      intro m
      rw [← ENNReal.tsum_mul_right]

/-- Exact hitting mass.  This is the algebraic heart of the upward-chain
construction: the von Mangoldt divisor sum makes `ν` the unique incoming
solution when the chain starts from `1`. -/
theorem hitMass_eq_ofReal_nu {n : ℕ} (hn : 1 ≤ n) :
    D.hitMass n = ENNReal.ofReal (D.nu n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn1 : n = 1
      · subst n
        simp [D.nu_one]
      · have hn2 : 2 ≤ n := by omega
        rw [D.hitMass_recurrence, if_neg hn1, zero_add,
          ← D.predecessor_balance hn2]
        apply tsum_congr
        intro m
        by_cases hm : m ∈ n.properDivisors
        · rw [ih m (Nat.mem_properDivisors.mp hm).2
              (Nat.pos_of_mem_properDivisors hm)]
        · rw [D.nextPMF_apply_eq_zero_of_not_mem_properDivisors (by omega) hm,
            mul_zero, mul_zero]

/-- Marginal law of the coordinate at time `k` under the Ionescu--Tulcea
trajectory. -/
noncomputable def coordinateMeasure (k : ℕ) : Measure ℕ :=
  D.pathMeasure.map fun ω ↦ ω k

lemma coordinateMeasure_succ (k : ℕ) :
    D.coordinateMeasure (k + 1) =
      D.transitionKernel ∘ₘ D.coordinateMeasure k := by
  let last : ((i : Finset.Iic k) → ℕ) → ℕ :=
    fun x ↦ x ⟨k, Finset.mem_Iic.mpr le_rfl⟩
  have hpair :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ ↦ ℕ) (μ₀ := Measure.dirac (1 : ℕ))
      (κ := D.stepKernel) (a := k)
  have hsnd := congrArg Measure.snd hpair
  rw [Measure.snd_compProd,
    Measure.snd_map_prodMk (by fun_prop : Measurable (fun x : ℕ → ℕ ↦
      Preorder.frestrictLe k x))] at hsnd
  have hcomp :
      D.stepKernel k ∘ₘ D.pathMeasure.map
          (Preorder.frestrictLe k) =
        D.transitionKernel ∘ₘ D.coordinateMeasure k := by
    calc
      _ = (D.transitionKernel ∘ₖ Kernel.deterministic last (by fun_prop)) ∘ₘ
          D.pathMeasure.map (Preorder.frestrictLe k) := by
            rw [Kernel.comp_deterministic_eq_comap]
            rfl
      _ = D.transitionKernel ∘ₘ
          (Kernel.deterministic last (by fun_prop) ∘ₘ
            D.pathMeasure.map (Preorder.frestrictLe k)) :=
        Measure.comp_assoc.symm
      _ = D.transitionKernel ∘ₘ
          (D.pathMeasure.map (Preorder.frestrictLe k)).map last := by
        rw [Measure.deterministic_comp_eq_map]
      _ = D.transitionKernel ∘ₘ D.coordinateMeasure k := by
        rw [coordinateMeasure, Measure.map_map]
        · rfl
        · fun_prop
        · fun_prop
  change D.stepKernel k ∘ₘ D.pathMeasure.map (Preorder.frestrictLe k) =
    D.coordinateMeasure (k + 1) at hsnd
  rw [hcomp] at hsnd
  exact hsnd.symm

@[simp] lemma coordinateMeasure_zero :
    D.coordinateMeasure 0 = Measure.dirac 1 := by
  rw [coordinateMeasure, pathMeasure, Kernel.trajMeasure,
    Measure.map_comp _ _ (by fun_prop)]
  have hmap :
      (Kernel.traj D.stepKernel 0).map (fun x : ℕ → ℕ ↦ x 0) =
        Kernel.deterministic
          (fun x : (i : Finset.Iic 0) → ℕ ↦ x ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
          (by fun_prop) := by
    have h := Kernel.traj_map_frestrictLe_of_le
      (X := fun _ : ℕ ↦ ℕ) (κ := D.stepKernel) (a := 0) (b := 0) le_rfl
    have hm := congrArg
      (fun K : Kernel ((i : Finset.Iic 0) → ℕ) ((i : Finset.Iic 0) → ℕ) ↦
        K.map (fun x ↦ x ⟨0, Finset.mem_Iic.mpr le_rfl⟩)) h
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop),
      Kernel.deterministic_map (by fun_prop) (by fun_prop)] at hm
    simpa [Function.comp_def] using hm
  rw [hmap, Measure.deterministic_comp_eq_map, Measure.map_map]
  · simp
  · fun_prop
  · fun_prop

lemma transitionKernel_comp_toMeasure (p : PMF ℕ) :
    D.transitionKernel ∘ₘ p.toMeasure = (p.bind D.nextPMF).toMeasure := by
  ext s hs
  rw [Measure.bind_apply hs D.transitionKernel.aemeasurable,
    PMF.toMeasure_bind_apply p D.nextPMF s hs, lintegral_countable']
  simp only [transitionKernel_apply, PMF.toMeasure_apply_singleton,
    measurableSet_singleton, mul_comm]

/-- Every coordinate of the Ionescu--Tulcea trajectory has the recursively
defined finite-time PMF as its law. -/
lemma coordinateMeasure_eq_statePMF_toMeasure (k : ℕ) :
    D.coordinateMeasure k = (D.statePMF k).toMeasure := by
  induction k with
  | zero => rw [coordinateMeasure_zero, statePMF_zero, PMF.toMeasure_pure]
  | succ k ih =>
      rw [coordinateMeasure_succ, ih, statePMF_succ,
        transitionKernel_comp_toMeasure]

lemma statePMF_toMeasure_ae_pos (k : ℕ) :
    ∀ᵐ n ∂(D.statePMF k).toMeasure, 1 ≤ n := by
  change {n : ℕ | 1 ≤ n} ∈ ae (D.statePMF k).toMeasure
  rw [mem_ae_iff]
  have hcompl : {n : ℕ | 1 ≤ n}ᶜ = {0} := by
    ext n
    simp
  rw [hcompl, PMF.toMeasure_apply_singleton]
  · exact D.statePMF_apply_eq_zero_of_le_time (Nat.zero_le k)
  · measurability

lemma pathMeasure_ae_initial :
    ∀ᵐ ω ∂D.pathMeasure, ω 0 = 1 := by
  apply (ae_map_iff (μ := D.pathMeasure) (f := fun ω : ℕ → ℕ ↦ ω 0)
    (p := fun n : ℕ ↦ n = 1)
    ((by fun_prop : Measurable (fun ω : ℕ → ℕ ↦ ω 0)).aemeasurable)
    (by measurability)).mp
  rw [← coordinateMeasure, coordinateMeasure_zero]
  simp

lemma pathMeasure_ae_isStep (k : ℕ) :
    ∀ᵐ ω ∂D.pathMeasure, IsStep (ω k) (ω (k + 1)) := by
  let last : ((i : Finset.Iic k) → ℕ) → ℕ :=
    fun x ↦ x ⟨k, Finset.mem_Iic.mpr le_rfl⟩
  let μk : Measure ((i : Finset.Iic k) → ℕ) :=
    D.pathMeasure.map (Preorder.frestrictLe k)
  have hlast : μk.map last = D.coordinateMeasure k := by
    simp only [μk]
    rw [coordinateMeasure, Measure.map_map]
    · rfl
    · fun_prop
    · fun_prop
  have hpos : ∀ᵐ x ∂μk, 1 ≤ last x := by
    apply ae_of_ae_map (by fun_prop)
    rw [hlast, D.coordinateMeasure_eq_statePMF_toMeasure]
    exact D.statePMF_toMeasure_ae_pos k
  have hrows : ∀ᵐ x ∂μk, ∀ᵐ n ∂D.stepKernel k x, IsStep (last x) n := by
    filter_upwards [hpos] with x hx
    change {n : ℕ | IsStep (last x) n} ∈ ae (D.stepKernel k x)
    rw [mem_ae_iff_prob_eq_one (by measurability)]
    change D.transitionKernel (last x) {n | IsStep (last x) n} = 1
    exact D.transitionKernel_isStep hx
  have hprod :
      ∀ᵐ z ∂(μk ⊗ₘ D.stepKernel k), IsStep (last z.1) z.2 :=
    Measure.ae_compProd_of_ae_ae (by measurability) hrows
  have hpair :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ : ℕ ↦ ℕ) (μ₀ := Measure.dirac (1 : ℕ))
      (κ := D.stepKernel) (a := k)
  change μk ⊗ₘ D.stepKernel k =
    D.pathMeasure.map (fun x ↦ (Preorder.frestrictLe k x, x (k + 1))) at hpair
  rw [hpair] at hprod
  exact (ae_map_iff (by fun_prop) (by measurability)).mp hprod

/-- The path properties supplied by the abstract upward chain. -/
def IsGoodPath (ω : ℕ → ℕ) : Prop :=
  ω 0 = 1 ∧ ∀ k, IsStep (ω k) (ω (k + 1))

lemma pathMeasure_ae_good :
    ∀ᵐ ω ∂D.pathMeasure, IsGoodPath ω := by
  filter_upwards [D.pathMeasure_ae_initial,
    ae_all_iff.mpr D.pathMeasure_ae_isStep] with ω hzero hstep
  exact ⟨hzero, hstep⟩

lemma IsGoodPath.strictMono {ω : ℕ → ℕ} (hω : IsGoodPath ω) : StrictMono ω :=
  strictMono_nat_of_lt_succ fun k ↦ (hω.2 k).1

/-- The measurable event that the trajectory visits `n` at some finite time. -/
def hitEvent (n : ℕ) : Set (ℕ → ℕ) :=
  {ω | ∃ k, ω k = n}

lemma measurableSet_hitEvent (n : ℕ) : MeasurableSet (hitEvent n) := by
  rw [show hitEvent n = ⋃ k : ℕ, {ω : ℕ → ℕ | ω k = n} by
    ext ω
    simp [hitEvent]]
  exact MeasurableSet.iUnion fun k ↦ by measurability

lemma pathMeasure_apply_coordinate_eq (k n : ℕ) :
    D.pathMeasure {ω : ℕ → ℕ | ω k = n} = D.statePMF k n := by
  calc
    _ = D.coordinateMeasure k {n} := by
      rw [coordinateMeasure,
        Measure.map_apply (by fun_prop) (MeasurableSet.singleton n)]
      rfl
    _ = (D.statePMF k).toMeasure {n} := by
      rw [D.coordinateMeasure_eq_statePMF_toMeasure]
    _ = _ := PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton n)

/-- Since paths are almost surely strictly increasing, the mass of ever
visiting `n` is the sum of its finite-coordinate masses. -/
lemma pathMeasure_hitEvent (n : ℕ) :
    D.pathMeasure (hitEvent n) = D.hitMass n := by
  let E : ℕ → Set (ℕ → ℕ) := fun k ↦ {ω | ω k = n}
  have hE : hitEvent n = ⋃ k, E k := by
    ext ω
    simp [hitEvent, E]
  have hdisj : Pairwise (fun k l ↦ AEDisjoint D.pathMeasure (E k) (E l)) := by
    intro k l hkl
    rw [AEDisjoint, measure_eq_zero_iff_ae_notMem]
    filter_upwards [D.pathMeasure_ae_good] with ω hω
    simp only [E, Set.mem_inter_iff, Set.mem_ofPred_eq, not_and]
    intro hk hl
    exact hkl (hω.strictMono.injective (hk.trans hl.symm))
  rw [hE, measure_iUnion₀ hdisj]
  · exact tsum_congr fun k ↦ D.pathMeasure_apply_coordinate_eq k n
  · intro k
    exact (by measurability : MeasurableSet (E k)).nullMeasurableSet

/-- Exact probability that the trajectory ever visits a positive state. -/
theorem pathMeasure_hitEvent_eq_ofReal_nu {n : ℕ} (hn : 1 ≤ n) :
    D.pathMeasure (hitEvent n) = ENNReal.ofReal (D.nu n) :=
  (D.pathMeasure_hitEvent n).trans (D.hitMass_eq_ofReal_nu hn)

end Data

end UpwardChain

end Erdos1217
