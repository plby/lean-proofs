import ErdosProblems.Erdos788.SimplexCode
import Mathlib.Probability.Moments.SubGaussian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Short linear codes over `ZMod p`

This file formalizes the probabilistic part of the short-code lemma.  A
matrix is represented by its list of rows.  For every fixed nonzero input,
its row evaluations are independent uniform field elements; Hoeffding's
inequality and a finite union bound then give one matrix having the required
near-Plotkin distance.  The deterministic simplex argument converting that
distance into an agreement-list bound is proved at the end of the file.
-/

namespace Erdos788

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

/-- Evaluation against a fixed vector, viewed as a linear functional in the
row variable. -/
def rowDotLinear (p m : ℕ) [Fact p.Prime]
    (x : Fin m → ZMod p) : (Fin m → ZMod p) →ₗ[ZMod p] ZMod p where
  toFun a := ∑ j, a j * x j
  map_add' a b := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring

@[simp]
theorem rowDotLinear_apply {p m : ℕ} [Fact p.Prime]
    (x a : Fin m → ZMod p) :
    rowDotLinear p m x a = ∑ j, a j * x j := rfl

theorem rowDotLinear_surjective {p m : ℕ} [Fact p.Prime]
    {x : Fin m → ZMod p} (hx : x ≠ 0) :
    Function.Surjective (rowDotLinear p m x) := by
  classical
  have hex : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨j, hj⟩ := hex
  intro c
  let a : Fin m → ZMod p := fun i ↦ if i = j then c / x j else 0
  refine ⟨a, ?_⟩
  simp only [rowDotLinear_apply, a]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro i _hi hij
    simp [hij]
  · simp

/-- A nonzero linear functional on `m` field coordinates has exactly
`p^(m-1)` zeros. -/
theorem card_rowDotLinear_eq_zero {p m : ℕ} [Fact p.Prime]
    {x : Fin m → ZMod p} (hx : x ≠ 0) :
    Fintype.card {a : Fin m → ZMod p // rowDotLinear p m x a = 0} =
      p ^ (m - 1) := by
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact hx (Subsingleton.elim _ _)
  let F := rowDotLinear p m x
  have hsurj : Function.Surjective F := rowDotLinear_surjective hx
  have hrange : F.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hfrange : Module.finrank (ZMod p) F.range = 1 := by
    rw [hrange, finrank_top]
    simp
  have hfdomain : Module.finrank (ZMod p) (Fin m → ZMod p) = m := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hfker : Module.finrank (ZMod p) F.ker = m - 1 := by
    have h := F.finrank_range_add_finrank_ker
    rw [hfrange, hfdomain] at h
    omega
  change Fintype.card {a : Fin m → ZMod p // F a = 0} = p ^ (m - 1)
  rw [← Nat.card_eq_fintype_card]
  change Nat.card F.ker = p ^ (m - 1)
  rw [
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := F.ker),
    Nat.card_zmod, hfker]

/-- The exact finite average of the zero indicator of a nonzero row
functional is `1/p`. -/
theorem average_rowDotLinear_eq_zero {p m : ℕ} [Fact p.Prime]
    {x : Fin m → ZMod p} (hx : x ≠ 0) :
    (Fintype.card (Fin m → ZMod p) : ℝ)⁻¹ *
        (∑ a : Fin m → ZMod p,
          if rowDotLinear p m x a = 0 then (1 : ℝ) else 0) =
      1 / p := by
  classical
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos h
    subst m
    exact hx (Subsingleton.elim _ _)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsum :
      (∑ a : Fin m → ZMod p,
          if rowDotLinear p m x a = 0 then (1 : ℝ) else 0) =
        ((p ^ (m - 1) : ℕ) : ℝ) := by
    rw [← card_rowDotLinear_eq_zero hx]
    norm_cast
    change (∑ a ∈ (Finset.univ : Finset (Fin m → ZMod p)),
      if rowDotLinear p m x a = 0 then (1 : ℕ) else 0) = _
    rw [Finset.sum_boole]
    simpa only [rowDotLinear_apply] using!
      (Fintype.card_subtype (fun a : Fin m → ZMod p ↦
        rowDotLinear p m x a = 0)).symm
  rw [hsum]
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  rw [← hm', pow_succ]
  push_cast
  field_simp

/-- The real-valued indicator that a row annihilates `x`. -/
noncomputable def rowZeroIndicator {p m : ℕ} [Fact p.Prime]
    (x a : Fin m → ZMod p) : ℝ :=
  if rowDotLinear p m x a = 0 then 1 else 0

theorem integral_rowZeroIndicator_uniform {p m : ℕ} [Fact p.Prime]
    [MeasurableSpace (Fin m → ZMod p)]
    [MeasurableSingletonClass (Fin m → ZMod p)]
    {x : Fin m → ZMod p} (hx : x ≠ 0) :
    ∫ a, rowZeroIndicator x a ∂(PMF.uniformOfFintype
        (Fin m → ZMod p)).toMeasure = 1 / p := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul]
  rw [← Finset.mul_sum]
  exact average_rowDotLinear_eq_zero hx

/-- A finite product of uniform random rows contains a matrix for which every
nonzero input has agreement with zero at most `1/p + τ`, as soon as the
explicit Hoeffding union bound is below one. -/
theorem exists_rows_nearPlotkin_of_exponential_bound
    (p m R : ℕ) [Fact p.Prime] (hR : 0 < R) (τ : ℝ) (hτ : 0 ≤ τ)
    (hbound :
      (Fintype.card {x : Fin m → ZMod p // x ≠ 0} : ℝ) *
          Real.exp (-2 * R * τ ^ 2) < 1) :
    ∃ T : Fin R → (Fin m → ZMod p),
      ∀ x : Fin m → ZMod p, x ≠ 0 →
        (∑ i, rowZeroIndicator x (T i)) ≤
          (R : ℝ) * (1 / p + τ) := by
  classical
  let Row := Fin m → ZMod p
  letI : MeasurableSpace Row := ⊤
  let μ₀ : Measure Row := (PMF.uniformOfFintype Row).toMeasure
  letI : IsProbabilityMeasure μ₀ := inferInstance
  let μ : Measure (Fin R → Row) := Measure.pi (fun _ ↦ μ₀)
  letI : IsProbabilityMeasure μ := inferInstance
  let bad (x : {x : Fin m → ZMod p // x ≠ 0}) :
      Set (Fin R → Row) :=
    {T | (R : ℝ) * (1 / p + τ) <
      ∑ i, rowZeroIndicator x.1 (T i)}
  have htail (x : {x : Fin m → ZMod p // x ≠ 0}) :
      μ.real (bad x) ≤ Real.exp (-2 * R * τ ^ 2) := by
    let X₀ : Fin R → Row → ℝ := fun _ a ↦
      rowZeroIndicator x.1 a - 1 / p
    have hmean : ∀ i : Fin R,
        ∫ a, rowZeroIndicator x.1 a ∂μ₀ = 1 / p := by
      intro i
      exact integral_rowZeroIndicator_uniform x.2
    have hcomponent : ∀ i : Fin R,
        HasSubgaussianMGF (X₀ i) (1 / 4 : ℝ≥0) μ₀ := by
      intro i
      have hm : AEMeasurable (fun a : Row ↦ rowZeroIndicator x.1 a) μ₀ :=
        (measurable_of_finite _).aemeasurable
      have hrange : ∀ᵐ a ∂μ₀,
          rowZeroIndicator x.1 a ∈ Set.Icc (0 : ℝ) 1 := by
        filter_upwards [] with a
        simp only [rowZeroIndicator]
        split <;> simp
      have hs := hasSubgaussianMGF_of_mem_Icc hm hrange
      rw [hmean i] at hs
      convert! hs using 1
      all_goals norm_num [X₀]
    have hind : iIndepFun
        (fun i (T : Fin R → Row) ↦ X₀ i (T i)) μ := by
      apply iIndepFun_pi
      intro i
      exact (measurable_of_finite _).aemeasurable
    have hsub : ∀ i ∈ (Finset.univ : Finset (Fin R)),
        HasSubgaussianMGF
          (fun T : Fin R → Row ↦ X₀ i (T i)) (1 / 4 : ℝ≥0) μ := by
      intro i _hi
      have hmapped : HasSubgaussianMGF (X₀ i) (1 / 4 : ℝ≥0)
          (μ.map (fun T : Fin R → Row ↦ T i)) := by
        rw [(measurePreserving_eval (fun _ : Fin R ↦ μ₀) i).map_eq]
        exact hcomponent i
      simpa only [Function.comp_apply] using!
        (HasSubgaussianMGF.of_map
          (X := X₀ i) (Y := fun T : Fin R → Row ↦ T i)
          (measurable_pi_apply i).aemeasurable hmapped)
    have hhoeff := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub
      (s := (Finset.univ : Finset (Fin R)))
      (c := fun _ ↦ (1 / 4 : ℝ≥0))
      (hε := mul_nonneg (by positivity : (0 : ℝ) ≤ R) hτ)
      ( ε := (R : ℝ) * τ)
    have hclosed :
        μ.real {T : Fin R → Row |
            (R : ℝ) * τ ≤ ∑ i, X₀ i (T i)} ≤
          Real.exp (-2 * R * τ ^ 2) := by
      calc
        μ.real {T : Fin R → Row |
            (R : ℝ) * τ ≤ ∑ i, X₀ i (T i)} ≤
            Real.exp (-((R : ℝ) * τ) ^ 2 /
              (2 * ((R : ℝ) * (1 / 4)))) := by
                simpa only [Finset.sum_const, Finset.card_univ,
                  Fintype.card_fin, nsmul_eq_mul, NNReal.coe_mul,
                  NNReal.coe_natCast, NNReal.coe_ofNat] using! hhoeff
        _ = Real.exp (-2 * R * τ ^ 2) := by
          congr 1
          have hRne : (R : ℝ) ≠ 0 := by positivity
          field_simp
          ring
    apply (measureReal_mono ?_).trans hclosed
    intro T hT
    change (R : ℝ) * (1 / p + τ) <
      ∑ i, rowZeroIndicator x.1 (T i) at hT
    change (R : ℝ) * τ ≤ ∑ i, X₀ i (T i)
    simp only [X₀, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hunion : μ.real (⋃ x, bad x) < 1 := by
    calc
      μ.real (⋃ x, bad x) ≤ ∑ x, μ.real (bad x) :=
        measureReal_iUnion_fintype_le bad
      _ ≤ ∑ _x : {x : Fin m → ZMod p // x ≠ 0},
          Real.exp (-2 * R * τ ^ 2) := Finset.sum_le_sum fun x _hx ↦ htail x
      _ = (Fintype.card {x : Fin m → ZMod p // x ≠ 0} : ℝ) *
          Real.exp (-2 * R * τ ^ 2) := by simp
      _ < 1 := hbound
  by_contra hgood
  push Not at hgood
  have hall : (⋃ x, bad x) = Set.univ := by
    ext T
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨x, hx, hbad⟩ := hgood T
    exact ⟨⟨x, hx⟩, hbad⟩
  rw [hall, probReal_univ] at hunion
  exact (lt_irrefl (1 : ℝ) hunion).elim

theorem exponential_union_bound_of_length
    (p m R : ℕ) [Fact p.Prime] (τ : ℝ) (hτ : 0 < τ)
    (hR : (m + 1 : ℝ) * Real.log p / (2 * τ ^ 2) < R) :
    (Fintype.card {x : Fin m → ZMod p // x ≠ 0} : ℝ) *
        Real.exp (-2 * R * τ ^ 2) < 1 := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hscale : 0 < 2 * τ ^ 2 := by positivity
  have hexpArg : -2 * (R : ℝ) * τ ^ 2 <
      -(m + 1 : ℝ) * Real.log p := by
    have := (div_lt_iff₀ hscale).mp hR
    nlinarith
  have hexp : Real.exp (-2 * (R : ℝ) * τ ^ 2) <
      ((p : ℝ) ^ (m + 1))⁻¹ := by
    calc
      Real.exp (-2 * (R : ℝ) * τ ^ 2) <
          Real.exp (-(m + 1 : ℝ) * Real.log p) :=
        Real.exp_lt_exp.mpr hexpArg
      _ = (Real.exp ((m + 1 : ℝ) * Real.log p))⁻¹ := by
        rw [show -(m + 1 : ℝ) * Real.log p =
          -((m + 1 : ℝ) * Real.log p) by ring, Real.exp_neg]
      _ = ((p : ℝ) ^ (m + 1))⁻¹ := by
        rw [show (m + 1 : ℝ) * Real.log p =
          (m + 1 : ℕ) * Real.log p by norm_num,
          Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < p)]
  have hcard :
      Fintype.card {x : Fin m → ZMod p // x ≠ 0} ≤ p ^ m := by
    calc
      Fintype.card {x : Fin m → ZMod p // x ≠ 0} ≤
          Fintype.card (Fin m → ZMod p) := Fintype.card_subtype_le _
      _ = p ^ m := by simp [ZMod.card]
  have hpowpos : (0 : ℝ) < (p : ℝ) ^ m := by positivity
  calc
    (Fintype.card {x : Fin m → ZMod p // x ≠ 0} : ℝ) *
        Real.exp (-2 * R * τ ^ 2)
        ≤ (p : ℝ) ^ m * Real.exp (-2 * R * τ ^ 2) := by
          gcongr
          exact_mod_cast hcard
    _ < (p : ℝ) ^ m * ((p : ℝ) ^ (m + 1))⁻¹ :=
      mul_lt_mul_of_pos_left hexp hpowpos
    _ = (p : ℝ)⁻¹ := by
      rw [pow_succ]
      field_simp
    _ < 1 := inv_lt_one_of_one_lt₀ hpR

/-- Binary-coordinate version of the random near-Plotkin construction.
The displayed length estimate is an explicit real inequality; in particular
the block length is polynomial in `m`, `log p`, and `1/τ`. -/
theorem exists_binary_rows_nearPlotkin
    (p m : ℕ) [Fact p.Prime] (τ : ℝ) (hτ : 0 < τ) :
    ∃ ell : ℕ, ∃ T : BinaryCoord ell → (Fin m → ZMod p),
      (∀ x : Fin m → ZMod p, x ≠ 0 →
        (∑ z, rowZeroIndicator x (T z)) ≤
          (2 ^ ell : ℝ) * (1 / p + τ)) ∧
      (2 ^ ell : ℝ) < (m + 1 : ℝ) * Real.log p / τ ^ 2 + 4 := by
  classical
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  let A : ℝ := (m + 1 : ℝ) * Real.log p / (2 * τ ^ 2)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  let n : ℕ := ⌈A⌉₊ + 1
  have hn2 : 2 ≤ n := by
    dsimp [n]
    have : 1 ≤ ⌈A⌉₊ := (Nat.one_le_ceil_iff).2 hA
    omega
  let ell : ℕ := Nat.clog 2 n
  let R : ℕ := 2 ^ ell
  have hnR : n ≤ R := by
    exact Nat.le_pow_clog (by omega) n
  have hAR : A < R := by
    have hAce : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
    have hAn : A < (n : ℝ) := by
      dsimp [n]
      push_cast
      linarith
    exact hAn.trans_le (by exact_mod_cast hnR)
  have hRpos : 0 < R := pow_pos (by omega) _
  have hbound := exponential_union_bound_of_length p m R τ hτ (by
    simpa [A] using! hAR)
  obtain ⟨T₀, hT₀⟩ := exists_rows_nearPlotkin_of_exponential_bound
    p m R hRpos τ hτ.le hbound
  have hcard : Fintype.card (BinaryCoord ell) = R := by
    simp [BinaryCoord, R]
  let e : BinaryCoord ell ≃ Fin R := Fintype.equivOfCardEq (by simpa using! hcard)
  let T : BinaryCoord ell → (Fin m → ZMod p) := fun z ↦ T₀ (e z)
  refine ⟨ell, T, ?_, ?_⟩
  · intro x hx
    have hsum : (∑ z, rowZeroIndicator x (T z)) =
        ∑ i, rowZeroIndicator x (T₀ i) := by
      exact Fintype.sum_equiv e _ _ (fun z ↦ rfl)
    rw [hsum]
    simpa [R] using! hT₀ x hx
  · have hellpos : 0 < ell := by
      exact Nat.clog_pos (by omega) (lt_of_lt_of_le (by omega) hn2)
    have hpred : 2 ^ (ell - 1) < n := by
      simpa [ell] using! Nat.pow_pred_clog_lt_self (b := 2) (by omega) (by omega : 1 < n)
    have hRlt : R < 2 * n := by
      change 2 ^ ell < 2 * n
      calc
        2 ^ ell = 2 * 2 ^ (ell - 1) := by
          calc
            2 ^ ell = 2 ^ (ell - 1 + 1) := by
              exact congrArg (fun k ↦ 2 ^ k) (Nat.sub_add_cancel hellpos).symm
            _ = 2 * 2 ^ (ell - 1) := by rw [pow_succ]; omega
        _ < 2 * n :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).2 hpred
    have hnA : (n : ℝ) < A + 2 := by
      have hc := Nat.ceil_lt_add_one hA.le
      dsimp [n]
      push_cast
      linarith
    have hRreal : (R : ℝ) < 2 * (A + 2) := by
      have : (R : ℝ) < 2 * n := by exact_mod_cast hRlt
      nlinarith
    dsimp [A] at hRreal
    simpa [R] using! (show (R : ℝ) <
      (m + 1 : ℝ) * Real.log p / τ ^ 2 + 4 by
        convert! hRreal using 1
        all_goals field_simp
        all_goals ring)

/-- The linear encoder whose coordinate `z` is evaluation against row
`T z`. -/
def binaryRowEncoder (p m ell : ℕ) [Fact p.Prime]
    (T : BinaryCoord ell → (Fin m → ZMod p)) :
    (Fin m → ZMod p) →ₗ[ZMod p] (BinaryCoord ell → ZMod p) where
  toFun x z := ∑ j, T z j * x j
  map_add' x y := by
    funext z
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring

@[simp]
theorem binaryRowEncoder_apply {p m ell : ℕ} [Fact p.Prime]
    (T : BinaryCoord ell → (Fin m → ZMod p))
    (x : Fin m → ZMod p) (z : BinaryCoord ell) :
    binaryRowEncoder p m ell T x z = ∑ j, T z j * x j := rfl

theorem sum_rowZeroIndicator_sub_eq_agreementCount
    {p m ell : ℕ} [Fact p.Prime]
    (T : BinaryCoord ell → (Fin m → ZMod p))
    (x y : Fin m → ZMod p) :
    (∑ z, rowZeroIndicator (x - y) (T z)) =
      (agreementCount (binaryRowEncoder p m ell T x)
        (binaryRowEncoder p m ell T y) : ℕ) := by
  classical
  have hiff (z : BinaryCoord ell) :
      rowDotLinear p m (x - y) (T z) = 0 ↔
        binaryRowEncoder p m ell T x z =
          binaryRowEncoder p m ell T y z := by
    change binaryRowEncoder p m ell T (x - y) z = 0 ↔
      binaryRowEncoder p m ell T x z = binaryRowEncoder p m ell T y z
    rw [(binaryRowEncoder p m ell T).map_sub, Pi.sub_apply, sub_eq_zero]
  rw [agreementCount]
  simp only [rowZeroIndicator, hiff]
  norm_cast
  simp

/-- A packaged binary-coordinate linear code with a checked near-Plotkin
pairwise-agreement bound. -/
structure NearPlotkinCode (p m : ℕ) [Fact p.Prime] (τ : ℝ) where
  ell : ℕ
  encoder : (Fin m → ZMod p) →ₗ[ZMod p]
    (BinaryCoord ell → ZMod p)
  injective : Function.Injective encoder
  pairAgreement : ∀ x y, x ≠ y →
    agreement (encoder x) (encoder y) ≤ 1 / p + τ
  length_lt : (2 ^ ell : ℝ) <
    (m + 1 : ℝ) * Real.log p / τ ^ 2 + 4

theorem exists_nearPlotkinCode
    (p m : ℕ) [Fact p.Prime] (τ : ℝ) (hτ : 0 < τ)
    (hsmall : 1 / (p : ℝ) + τ < 1) :
    Nonempty (NearPlotkinCode p m τ) := by
  classical
  obtain ⟨ell, T, hT, hlength⟩ := exists_binary_rows_nearPlotkin p m τ hτ
  let E := binaryRowEncoder p m ell T
  have hpair : ∀ x y, x ≠ y →
      agreement (E x) (E y) ≤ 1 / p + τ := by
    intro x y hxy
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
    rw [agreement, ← sum_rowZeroIndicator_sub_eq_agreementCount T x y]
    have hN : (0 : ℝ) < Fintype.card (BinaryCoord ell) := by positivity
    apply (div_le_iff₀ hN).2
    simpa [BinaryCoord, mul_comm] using! hT (x - y) hsub
  have hinj : Function.Injective E := by
    intro x y hE
    by_contra hxy
    have hb := hpair x y hxy
    rw [hE, agreement_self] at hb
    exact (not_le_of_gt hsmall hb).elim
  exact ⟨⟨ell, E, hinj, hpair, hlength⟩⟩

/-- Inputs whose codeword has agreement strictly above `1/p + η` with a
received word. -/
noncomputable def codeAgreementList {p m ell : ℕ} [Fact p.Prime]
    (E : (Fin m → ZMod p) →ₗ[ZMod p] (BinaryCoord ell → ZMod p))
    (Q : BinaryCoord ell → ZMod p) (η : ℝ) :
    Finset (Fin m → ZMod p) := by
  classical
  exact Finset.univ.filter fun x ↦ 1 / (p : ℝ) + η < agreement (E x) Q

/-- The regular-simplex calculation: a near-Plotkin pairwise-agreement
bound implies a uniform agreement-list bound. -/
theorem card_codeAgreementList_lt
    {p m ell : ℕ} [Fact p.Prime]
    (E : (Fin m → ZMod p) →ₗ[ZMod p] (BinaryCoord ell → ZMod p))
    (Q : BinaryCoord ell → ZMod p) (η τ : ℝ)
    (hη : 0 < η)
    (hτ : τ = (p : ℝ) * η ^ 2 / (2 * ((p : ℝ) - 1)))
    (hpair : ∀ x y, x ≠ y →
      agreement (E x) (E y) ≤ 1 / (p : ℝ) + τ) :
    ((codeAgreementList E Q η).card : ℝ) < 2 / η ^ 2 + 1 := by
  classical
  let L := codeAgreementList E Q η
  apply card_lt_two_div_sq_add_one_of_pairwise_agreement
    η τ hη hτ L (fun x ↦ E x) Q
  · intro x _hx y _hy hxy
    exact hpair x y hxy
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

/-- The complete short-code object used by reconstruction. -/
structure ShortLinearCode (p m : ℕ) [Fact p.Prime] (η : ℝ) where
  ell : ℕ
  encoder : (Fin m → ZMod p) →ₗ[ZMod p]
    (BinaryCoord ell → ZMod p)
  injective : Function.Injective encoder
  listBound : ∀ Q : BinaryCoord ell → ZMod p,
    ((codeAgreementList encoder Q η).card : ℝ) < 2 / η ^ 2 + 1
  length_lt : (2 ^ ell : ℝ) <
    9 * m * Real.log p / η ^ 4

/-- Short binary-coordinate linear list-decodable code.  This is the exact
finite existence statement needed in reconstruction: every received word
has fewer than `2/η²` messages above agreement `1/p+η`, and the block
length is at most an absolute constant times `m log(p)/η⁴`. -/
theorem exists_shortLinearCode
    (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m)
    (η : ℝ) (hη : 0 < η) (hηhalf : η < 1 / 2) :
    Nonempty (ShortLinearCode p m η) := by
  have hpNat : 1 < p := (Fact.out : p.Prime).one_lt
  have hp : (1 : ℝ) < p := by exact_mod_cast hpNat
  have hp0 : (0 : ℝ) < p := hp.trans' zero_lt_one
  have hp1 : (0 : ℝ) < p - 1 := sub_pos.mpr hp
  let τ : ℝ := (p : ℝ) * η ^ 2 / (2 * (p - 1))
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  have hpRatio : (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
    apply (div_le_iff₀ hp1).2
    have hp2Nat : 2 ≤ p := by omega
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp2Nat
    nlinarith
  have hηsq : η ^ 2 < 1 / 4 := by
    have hs := (sq_lt_sq₀ hη.le
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hηhalf
    norm_num at hs ⊢
    exact hs
  have hτquarter : τ < 1 / 4 := by
    calc
      τ = ((p : ℝ) / ((p : ℝ) - 1)) * η ^ 2 / 2 := by
        dsimp [τ]
        field_simp
      _ ≤ 2 * η ^ 2 / 2 := by gcongr
      _ = η ^ 2 := by ring
      _ < 1 / 4 := hηsq
  have hinvp : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa [one_div] using!
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
        (by
          have hp2Nat : 2 ≤ p := by omega
          exact_mod_cast hp2Nat))
  have hsmall : 1 / (p : ℝ) + τ < 1 := by
    rw [one_div]
    nlinarith
  obtain ⟨C⟩ := exists_nearPlotkinCode p m τ hτ hsmall
  have hlist (Q : BinaryCoord C.ell → ZMod p) :
      ((codeAgreementList C.encoder Q η).card : ℝ) < 2 / η ^ 2 + 1 := by
    apply card_codeAgreementList_lt C.encoder Q η τ hη rfl
    exact C.pairAgreement
  have hlogLower : (1 / 2 : ℝ) ≤ Real.log p := by
    have hlog := Real.one_sub_inv_le_log_of_pos hp0
    nlinarith
  have hηfour : η ^ 4 < 1 / 16 := by
    have hsquare : (η ^ 2) ^ 2 < (1 / 4 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (sq_nonneg η) (by norm_num : (0 : ℝ) ≤ 1 / 4)).2 hηsq
    nlinarith
  have heta4pos : 0 < η ^ 4 := by positivity
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfour : (4 : ℝ) ≤ (m : ℝ) * Real.log p / η ^ 4 := by
    apply (le_div_iff₀ heta4pos).2
    have hmLog : (1 / 2 : ℝ) ≤ (m : ℝ) * Real.log p := by
      calc
        (1 / 2 : ℝ) = 1 * (1 / 2) := by ring
        _ ≤ (m : ℝ) * Real.log p :=
          mul_le_mul hmR hlogLower (by norm_num) (by positivity)
    nlinarith
  have htauSq : τ ^ 2 =
      (p : ℝ) ^ 2 * η ^ 4 / (4 * (p - 1) ^ 2) := by
    dsimp [τ]
    field_simp
    ring
  have hbase :
      (m + 1 : ℝ) * Real.log p / τ ^ 2 ≤
        8 * m * Real.log p / η ^ 4 := by
    have hm2 : (m + 1 : ℝ) ≤ 2 * m := by
      exact_mod_cast (show m + 1 ≤ 2 * m by omega)
    have hsquares : ((p : ℝ) - 1) ^ 2 ≤ p ^ 2 := by nlinarith
    rw [htauSq]
    have hpSq : 0 < (p : ℝ) ^ 2 := by positivity
    have hp1Sq : 0 < ((p : ℝ) - 1) ^ 2 := by positivity
    have hlogpos : 0 < Real.log (p : ℝ) := Real.log_pos hp
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsquares (by positivity :
      (0 : ℝ) ≤ 2 * m * Real.log p)]
  have hlength : (2 ^ C.ell : ℝ) <
      9 * m * Real.log p / η ^ 4 := by
    calc
      (2 ^ C.ell : ℝ) <
          (m + 1 : ℝ) * Real.log p / τ ^ 2 + 4 := C.length_lt
      _ ≤ 8 * m * Real.log p / η ^ 4 +
          m * Real.log p / η ^ 4 := add_le_add hbase hfour
      _ = 9 * m * Real.log p / η ^ 4 := by ring
  exact ⟨⟨C.ell, C.encoder, C.injective, hlist, hlength⟩⟩

end Erdos788
