import ErdosProblems.Erdos381.VariableZeta
import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormula
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaZeroFree
import BoundedGaps.BombieriVinogradov.Analytic.DirichletZeroReciprocalSum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Erdos381

open Complex Set
open scoped BigOperators ComplexConjugate
open BoundedGaps.Maynard

noncomputable section

/-- The modified explicit-formula kernel has the expected short-interval
Lipschitz bound.  The division by the zero ordinate cancels on
differentiation; this is the analytic gain needed in Hoheisel's argument. -/
theorem norm_dirichletExplicitFormulaKernel_sub_le
    {x y : ℝ} {rho : ℂ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hrho : rho ≠ 0)
    (hre : rho.re ≤ 1) :
    ‖dirichletExplicitFormulaKernel y rho -
        dirichletExplicitFormulaKernel x rho‖ ≤
      x ^ (rho.re - 1) * (y - x) := by
  let F : ℝ → ℂ := fun t ↦ (t : ℂ) ^ rho / rho
  let F' : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (rho - 1)
  have hderiv : ∀ t ∈ Set.Icc x y,
      HasDerivWithinAt F (F' t) (Set.Icc x y) t := by
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans_le (hx.trans ht.1)
    have hbase := hasDerivAt_ofReal_cpow_const'
      htpos.ne' (r := rho - 1) (by simpa using hrho)
    simpa only [F, F', sub_add_cancel] using
      hbase.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico x y,
      ‖F' t‖ ≤ x ^ (rho.re - 1) := by
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans_le (hx.trans ht.1)
    have hexp : rho.re - 1 ≤ 0 := by linarith
    dsimp [F']
    rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos]
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) ht.1 hexp
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment'
    hderiv hbound y (right_mem_Icc.mpr hxy)
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hypos : 0 < y := hxpos.trans_le hxy
  rw [dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hypos hrho,
    dirichletExplicitFormulaKernel_eq_cpow_sub_one_div hxpos hrho]
  convert hmv using 1 <;> dsimp [F]
  ring_nf

theorem riemannZeta₀_conj (s : ℂ) :
    riemannZeta₀ (conj s) = conj (riemannZeta₀ s) := by
  by_cases hs : s = 1
  · subst s
    simp [riemannZeta₀]
  · have hcs : conj s ≠ 1 := by
      intro h
      apply hs
      simpa using congrArg conj h
    rw [riemannZeta₀, if_neg hcs, riemannZeta₀, if_neg hs,
      riemannZeta_conj, map_sub, map_inv₀, map_sub, map_one]

theorem riemannZeta₁_conj (s : ℂ) :
    riemannZeta₁ (conj s) = conj (riemannZeta₁ s) := by
  simp only [riemannZeta₁, map_add, map_one, map_mul, map_sub,
    riemannZeta₀_conj]

private theorem iteratedDeriv_conj_comp_conj (n : ℕ) (f : ℂ → ℂ) :
    iteratedDeriv n (conj ∘ f ∘ conj) =
      conj ∘ iteratedDeriv n f ∘ conj := by
  induction n generalizing f with
  | zero =>
      ext z
      simp
  | succ n ih =>
      simp only [iteratedDeriv_succ', deriv_conj_conj, ih]

theorem analyticOrderNatAt_riemannZeta₁_conj (rho : ℂ) :
    analyticOrderNatAt riemannZeta₁ (conj rho) =
      analyticOrderNatAt riemannZeta₁ rho := by
  let f : ℂ → ℂ := riemannZeta₁
  let g : ℂ → ℂ := conj ∘ f ∘ conj
  have hgf : f = g := by
    funext z
    dsimp [f, g, Function.comp_def]
    simpa using riemannZeta₁_conj (conj z)
  have hf : AnalyticAt ℂ f rho :=
    differentiable_riemannZeta₁.analyticAt rho
  have hfc : AnalyticAt ℂ f (conj rho) :=
    differentiable_riemannZeta₁.analyticAt (conj rho)
  have horder : analyticOrderAt f (conj rho) = analyticOrderAt f rho := by
    apply ENat.eq_of_forall_natCast_le_iff
    intro n
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hfc,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
    constructor
    · intro H i hi
      have hiZero := H i hi
      rw [hgf, iteratedDeriv_conj_comp_conj] at hiZero
      simpa [g, f, Function.comp_def] using congrArg conj hiZero
    · intro H i hi
      rw [hgf, iteratedDeriv_conj_comp_conj]
      simp only [Function.comp_apply, map_eq_zero]
      simpa [f] using H i hi
  simpa only [analyticOrderNatAt, f, horder]

private theorem riemannZeta₁_eq_zero_of_modOne_nontrivialZero
    {rho : ℂ}
    (hzero : IsDirichletNontrivialLFunctionZero
      (1 : DirichletCharacter ℂ 1) rho) :
    riemannZeta₁ rho = 0 := by
  have hrhoOne : rho ≠ 1 := by
    intro hrho
    have hre := congrArg Complex.re hrho
    norm_num at hre
    linarith [hzero.2.2]
  have hzeta : riemannZeta rho = 0 := by
    simpa [DirichletCharacter.LFunction_modOne_eq] using hzero.1
  have hfactor := riemannZeta_eq_inv_sub_mul hrhoOne
  rw [hzeta] at hfactor
  exact (mul_eq_zero.mp hfactor.symm).resolve_left
    (inv_ne_zero (sub_ne_zero.mpr hrhoOne))

noncomputable def zetaExplicitUpperRectangle (eta T : ℝ) : Finset ℂ :=
  (dirichletNontrivialLFunctionZerosFinset
    (1 : DirichletCharacter ℂ 1) T).filter fun rho ↦
      1 - eta ≤ rho.re ∧ 1 ≤ rho.im

noncomputable def zetaExplicitLowerRectangle (eta T : ℝ) : Finset ℂ :=
  (dirichletNontrivialLFunctionZerosFinset
    (1 : DirichletCharacter ℂ 1) T).filter fun rho ↦
      1 - eta ≤ rho.re ∧ rho.im ≤ -1

theorem zetaExplicitUpperRectangle_subset_zetaHigh
    {eta T : ℝ} (heta : eta ≤ 1) (hT : 1 ≤ T) :
    zetaExplicitUpperRectangle eta T ⊆ zetaHighZeroRectangle eta T := by
  intro rho hrho
  have hm := Finset.mem_filter.mp hrho
  have hz :=
    (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hm.1)
  rw [abs_of_nonneg (show 0 ≤ T by linarith)] at hz
  exact (mem_zetaHighZeroRectangle_iff heta hT rho).mpr
    ⟨riemannZeta₁_eq_zero_of_modOne_nontrivialZero hz.1,
      hm.2.1, hz.1.2.2.le, hm.2.2,
      (by
        rw [← abs_of_nonneg (zero_le_one.trans hm.2.2)]
        exact hz.2)⟩

theorem sum_zetaExplicitUpperRectangle_multiplicity_le
    {eta T : ℝ} (heta : eta ≤ 1) (hT : 1 ≤ T) :
    (∑ rho ∈ zetaExplicitUpperRectangle eta T,
      (analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℝ)) ≤
      (zetaHighZeroRectangleMass eta T : ℝ) := by
  let S := zetaExplicitUpperRectangle eta T
  let Z := zetaHighZeroRectangle eta T
  have hsub : S ⊆ Z :=
    zetaExplicitUpperRectangle_subset_zetaHigh heta hT
  calc
    (∑ rho ∈ S,
      (analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℝ)) =
        ∑ rho ∈ S, (analyticOrderNatAt riemannZeta₁ rho : ℝ) := by
          apply Finset.sum_congr rfl
          intro rho hrho
          have hz :=
            (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp
              (Finset.mem_filter.mp hrho).1).1
          have hrhoOne : rho ≠ 1 := by
            intro hrho
            have hre := congrArg Complex.re hrho
            norm_num at hre
            linarith [hz.2.2]
          rw [analyticOrderNatAt_LFunction_modOne_eq_riemannZeta₁_of_ne_one
            hrhoOne]
    _ ≤ ∑ rho ∈ Z, (analyticOrderNatAt riemannZeta₁ rho : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro rho hrhoZ hrhoS
      positivity
    _ = (zetaHighZeroRectangleMass eta T : ℝ) := by
      dsimp [Z]
      simp only [zetaHighZeroRectangleMass, Nat.cast_sum]

noncomputable def zetaExplicitLowerConjugates (eta T : ℝ) : Finset ℂ :=
  (zetaExplicitLowerRectangle eta T).image conj

theorem zetaExplicitLowerConjugates_subset_zetaHigh
    {eta T : ℝ} (heta : eta ≤ 1) (hT : 1 ≤ T) :
    zetaExplicitLowerConjugates eta T ⊆ zetaHighZeroRectangle eta T := by
  intro z hz
  rw [zetaExplicitLowerConjugates, Finset.mem_image] at hz
  obtain ⟨rho, hrho, rfl⟩ := hz
  have hm := Finset.mem_filter.mp hrho
  have hzero :=
    (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hm.1)
  rw [abs_of_nonneg (show 0 ≤ T by linarith)] at hzero
  have hreg := riemannZeta₁_eq_zero_of_modOne_nontrivialZero hzero.1
  exact (mem_zetaHighZeroRectangle_iff heta hT (conj rho)).mpr
    ⟨by simpa [riemannZeta₁_conj] using congrArg conj hreg,
      by simpa using hm.2.1, by simpa using hzero.1.2.2.le,
      by simpa using (neg_le_neg hm.2.2),
      by simpa using (neg_le_abs rho.im).trans hzero.2⟩

theorem sum_zetaExplicitLowerRectangle_multiplicity_le
    {eta T : ℝ} (heta : eta ≤ 1) (hT : 1 ≤ T) :
    (∑ rho ∈ zetaExplicitLowerRectangle eta T,
      (analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℝ)) ≤
      (zetaHighZeroRectangleMass eta T : ℝ) := by
  let S := zetaExplicitLowerRectangle eta T
  let I := zetaExplicitLowerConjugates eta T
  let Z := zetaHighZeroRectangle eta T
  have hsum :
      (∑ rho ∈ S,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℝ)) =
        ∑ z ∈ I, (analyticOrderNatAt riemannZeta₁ z : ℝ) := by
    apply Finset.sum_bij (fun rho _ ↦ conj rho)
    · intro rho hrho
      exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩
    · intro a ha b hb hab
      simpa using congrArg conj hab
    · intro z hz
      change z ∈ zetaExplicitLowerConjugates eta T at hz
      rw [zetaExplicitLowerConjugates, Finset.mem_image] at hz
      obtain ⟨rho, hrho, hrhoz⟩ := hz
      exact ⟨rho, hrho, by simpa using hrhoz⟩
    · intro rho hrho
      have hz :=
        (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp
          (Finset.mem_filter.mp hrho).1).1
      have hrhoOne : rho ≠ 1 := by
        intro hrho
        have hre := congrArg Complex.re hrho
        norm_num at hre
        linarith [hz.2.2]
      rw [analyticOrderNatAt_LFunction_modOne_eq_riemannZeta₁_of_ne_one
        hrhoOne, analyticOrderNatAt_riemannZeta₁_conj]
  rw [hsum]
  calc
    (∑ z ∈ I, (analyticOrderNatAt riemannZeta₁ z : ℝ)) ≤
        ∑ z ∈ Z, (analyticOrderNatAt riemannZeta₁ z : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (zetaExplicitLowerConjugates_subset_zetaHigh heta hT)
      intro z hzZ hzI
      positivity
    _ = (zetaHighZeroRectangleMass eta T : ℝ) := by
      dsimp [Z]
      simp only [zetaHighZeroRectangleMass, Nat.cast_sum]

noncomputable def zetaExplicitUpperRealBand
    (etaLo etaHi T : ℝ) : Finset ℂ :=
  (zetaExplicitUpperRectangle etaHi T).filter fun rho ↦
    rho.re < 1 - etaLo

noncomputable def zetaExplicitLowerRealBand
    (etaLo etaHi T : ℝ) : Finset ℂ :=
  (zetaExplicitLowerRectangle etaHi T).filter fun rho ↦
    rho.re < 1 - etaLo

noncomputable def zetaExplicitTwoSidedRealBandKernelDiff
    (x y etaLo etaHi T : ℝ) : ℂ :=
  (∑ rho ∈ zetaExplicitUpperRealBand etaLo etaHi T,
      (analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
        (dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho)) +
    ∑ rho ∈ zetaExplicitLowerRealBand etaLo etaHi T,
      (analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
        (dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho)

private theorem norm_zetaExplicitRealBandKernelDiff_le
    {x y etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hetaHi : etaHi ≤ 1) (hT : 1 ≤ T)
    (S : Finset ℂ)
    (hSsub : S ⊆ zetaExplicitUpperRectangle etaHi T ∨
      S ⊆ zetaExplicitLowerRectangle etaHi T)
    (hSre : ∀ rho ∈ S, rho.re < 1 - etaLo) :
    ‖∑ rho ∈ S,
      (analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
        (dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho)‖ ≤
      (zetaHighZeroRectangleMass etaHi T : ℝ) *
        (x ^ (-etaLo) * (y - x)) := by
  let m : ℂ → ℝ := fun rho ↦
    analyticOrderNatAt
      (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1)) rho
  let C : ℝ := x ^ (-etaLo) * (y - x)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hterm : ∀ rho ∈ S,
      ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
          (dirichletExplicitFormulaKernel y rho -
            dirichletExplicitFormulaKernel x rho)‖ ≤ m rho * C := by
    intro rho hrho
    have hrhoZero : IsDirichletNontrivialLFunctionZero
        (1 : DirichletCharacter ℂ 1) rho := by
      rcases hSsub with hupper | hlower
      · exact (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp
          (Finset.mem_filter.mp (hupper hrho)).1).1
      · exact (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp
          (Finset.mem_filter.mp (hlower hrho)).1).1
    have hrhoNe : rho ≠ 0 := by
      intro hrho
      subst rho
      have hpositive := hrhoZero.2.1
      norm_num at hpositive
    have hdiff := norm_dirichletExplicitFormulaKernel_sub_le
      hx hxy hrhoNe hrhoZero.2.2.le
    have hpow : x ^ (rho.re - 1) ≤ x ^ (-etaLo) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith [hSre rho hrho])
    rw [norm_mul, Complex.norm_natCast]
    calc
      (m rho) *
          ‖dirichletExplicitFormulaKernel y rho -
            dirichletExplicitFormulaKernel x rho‖ ≤
        m rho * (x ^ (rho.re - 1) * (y - x)) := by
          exact mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ ≤ m rho * C := by
        dsimp [C]
        gcongr
      _ = m rho * C := rfl
  calc
    ‖∑ rho ∈ S,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
          (dirichletExplicitFormulaKernel y rho -
            dirichletExplicitFormulaKernel x rho)‖ ≤
        ∑ rho ∈ S,
          ‖(analyticOrderNatAt
            (DirichletCharacter.LFunction
              (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
            (dirichletExplicitFormulaKernel y rho -
              dirichletExplicitFormulaKernel x rho)‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ S, m rho * C := Finset.sum_le_sum hterm
    _ = (∑ rho ∈ S, m rho) * C := by rw [Finset.sum_mul]
    _ ≤ (zetaHighZeroRectangleMass etaHi T : ℝ) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      rcases hSsub with hupper | hlower
      · exact (Finset.sum_le_sum_of_subset_of_nonneg hupper
          (fun rho hrho hnot ↦ by dsimp [m]; positivity)).trans
          (sum_zetaExplicitUpperRectangle_multiplicity_le hetaHi hT)
      · exact (Finset.sum_le_sum_of_subset_of_nonneg hlower
          (fun rho hrho hnot ↦ by dsimp [m]; positivity)).trans
          (sum_zetaExplicitLowerRectangle_multiplicity_le hetaHi hT)
    _ = (zetaHighZeroRectangleMass etaHi T : ℝ) *
        (x ^ (-etaLo) * (y - x)) := rfl

theorem norm_zetaExplicitTwoSidedRealBandKernelDiff_le
    {x y etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hetaHi : etaHi ≤ 1) (hT : 1 ≤ T) :
    ‖zetaExplicitTwoSidedRealBandKernelDiff x y etaLo etaHi T‖ ≤
      2 * ((zetaHighZeroRectangleMass etaHi T : ℝ) *
        (x ^ (-etaLo) * (y - x))) := by
  have hu := norm_zetaExplicitRealBandKernelDiff_le
    hx hxy hetaHi hT (zetaExplicitUpperRealBand etaLo etaHi T)
    (Or.inl (Finset.filter_subset _ _))
    (fun rho hrho ↦ (Finset.mem_filter.mp hrho).2)
  have hl := norm_zetaExplicitRealBandKernelDiff_le
    hx hxy hetaHi hT (zetaExplicitLowerRealBand etaLo etaHi T)
    (Or.inr (Finset.filter_subset _ _))
    (fun rho hrho ↦ (Finset.mem_filter.mp hrho).2)
  unfold zetaExplicitTwoSidedRealBandKernelDiff
  calc
    ‖(∑ rho ∈ zetaExplicitUpperRealBand etaLo etaHi T,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
          (dirichletExplicitFormulaKernel y rho -
            dirichletExplicitFormulaKernel x rho)) +
      ∑ rho ∈ zetaExplicitLowerRealBand etaLo etaHi T,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
          (dirichletExplicitFormulaKernel y rho -
            dirichletExplicitFormulaKernel x rho)‖ ≤
        ‖∑ rho ∈ zetaExplicitUpperRealBand etaLo etaHi T,
          (analyticOrderNatAt
            (DirichletCharacter.LFunction
              (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
            (dirichletExplicitFormulaKernel y rho -
              dirichletExplicitFormulaKernel x rho)‖ +
        ‖∑ rho ∈ zetaExplicitLowerRealBand etaLo etaHi T,
          (analyticOrderNatAt
            (DirichletCharacter.LFunction
              (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
            (dirichletExplicitFormulaKernel y rho -
              dirichletExplicitFormulaKernel x rho)‖ := norm_add_le _ _
    _ ≤ 2 * ((zetaHighZeroRectangleMass etaHi T : ℝ) *
        (x ^ (-etaLo) * (y - x))) := by linarith

private theorem sum_norm_zetaExplicitRealBandKernelDiff_le
    {x y etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hetaHi : etaHi ≤ 1) (hT : 1 ≤ T)
    (S : Finset ℂ)
    (hSsub : S ⊆ zetaExplicitUpperRectangle etaHi T ∨
      S ⊆ zetaExplicitLowerRectangle etaHi T)
    (hSre : ∀ rho ∈ S, rho.re < 1 - etaLo) :
    (∑ rho ∈ S,
      ‖(analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
        (dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho)‖) ≤
      (zetaHighZeroRectangleMass etaHi T : ℝ) *
        (x ^ (-etaLo) * (y - x)) := by
  let m : ℂ → ℝ := fun rho ↦
    analyticOrderNatAt
      (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1)) rho
  let C : ℝ := x ^ (-etaLo) * (y - x)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm : ∀ rho ∈ S,
      ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
          (dirichletExplicitFormulaKernel y rho -
            dirichletExplicitFormulaKernel x rho)‖ ≤ m rho * C := by
    intro rho hrho
    have hrhoZero : IsDirichletNontrivialLFunctionZero
        (1 : DirichletCharacter ℂ 1) rho := by
      rcases hSsub with hupper | hlower
      · exact (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp
          (Finset.mem_filter.mp (hupper hrho)).1).1
      · exact (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp
          (Finset.mem_filter.mp (hlower hrho)).1).1
    have hrhoNe : rho ≠ 0 := by
      intro hrho
      subst rho
      have hpositive := hrhoZero.2.1
      norm_num at hpositive
    have hdiff := norm_dirichletExplicitFormulaKernel_sub_le
      hx hxy hrhoNe hrhoZero.2.2.le
    have hpow : x ^ (rho.re - 1) ≤ x ^ (-etaLo) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith [hSre rho hrho])
    rw [norm_mul, Complex.norm_natCast]
    calc
      m rho * ‖dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho‖ ≤
        m rho * (x ^ (rho.re - 1) * (y - x)) := by
          exact mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ ≤ m rho * C := by dsimp [C]; gcongr
  calc
    (∑ rho ∈ S,
      ‖(analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
        (dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho)‖) ≤
        ∑ rho ∈ S, m rho * C := Finset.sum_le_sum hterm
    _ = (∑ rho ∈ S, m rho) * C := by rw [Finset.sum_mul]
    _ ≤ (zetaHighZeroRectangleMass etaHi T : ℝ) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      rcases hSsub with hupper | hlower
      · exact (Finset.sum_le_sum_of_subset_of_nonneg hupper
          (fun rho hrho hnot ↦ by dsimp [m]; positivity)).trans
          (sum_zetaExplicitUpperRectangle_multiplicity_le hetaHi hT)
      · exact (Finset.sum_le_sum_of_subset_of_nonneg hlower
          (fun rho hrho hnot ↦ by dsimp [m]; positivity)).trans
          (sum_zetaExplicitLowerRectangle_multiplicity_le hetaHi hT)
    _ = _ := rfl

noncomputable def zetaExplicitHighRealBand
    (etaLo etaHi T : ℝ) : Finset ℂ :=
  zetaExplicitUpperRealBand etaLo etaHi T ∪
    zetaExplicitLowerRealBand etaLo etaHi T

private theorem disjoint_zetaExplicitUpperLowerRealBand
    (etaLo etaHi T : ℝ) :
    Disjoint (zetaExplicitUpperRealBand etaLo etaHi T)
      (zetaExplicitLowerRealBand etaLo etaHi T) := by
  rw [Finset.disjoint_left]
  intro rho hu hl
  have hu' := (Finset.mem_filter.mp
    (Finset.mem_filter.mp hu).1).2.2
  have hl' := (Finset.mem_filter.mp
    (Finset.mem_filter.mp hl).1).2.2
  linarith

theorem sum_norm_zetaExplicitHighRealBandKernelDiff_le
    {x y etaLo etaHi T : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hetaHi : etaHi ≤ 1) (hT : 1 ≤ T) :
    (∑ rho ∈ zetaExplicitHighRealBand etaLo etaHi T,
      ‖(analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
        (dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho)‖) ≤
      2 * ((zetaHighZeroRectangleMass etaHi T : ℝ) *
        (x ^ (-etaLo) * (y - x))) := by
  rw [zetaExplicitHighRealBand,
    Finset.sum_union (disjoint_zetaExplicitUpperLowerRealBand
      etaLo etaHi T)]
  have hu := sum_norm_zetaExplicitRealBandKernelDiff_le
    hx hxy hetaHi hT (zetaExplicitUpperRealBand etaLo etaHi T)
    (Or.inl (Finset.filter_subset _ _))
    (fun rho hrho ↦ (Finset.mem_filter.mp hrho).2)
  have hl := sum_norm_zetaExplicitRealBandKernelDiff_le
    hx hxy hetaHi hT (zetaExplicitLowerRealBand etaLo etaHi T)
    (Or.inr (Finset.filter_subset _ _))
    (fun rho hrho ↦ (Finset.mem_filter.mp hrho).2)
  linarith

/-! ### Exact finite band decomposition -/

/-- The complete set of modulus-one nontrivial zeros in the explicit
formula whose ordinate has absolute value at least one. -/
noncomputable def zetaExplicitHighZeros (T : ℝ) : Finset ℂ :=
  (dirichletNontrivialLFunctionZerosFinset
    (1 : DirichletCharacter ℂ 1) T).filter fun rho ↦ 1 ≤ |rho.im|

/-- The high-ordinate zeros left of the first `J+1` bands of width `eta`. -/
noncomputable def zetaExplicitHighFar
    (eta : ℝ) (J : ℕ) (T : ℝ) : Finset ℂ :=
  (zetaExplicitHighZeros T).filter fun rho ↦
    rho.re < 1 - ((J + 1 : ℕ) : ℝ) * eta

theorem mem_zetaExplicitHighRealBand_iff
    {etaLo etaHi T : ℝ} {rho : ℂ} :
    rho ∈ zetaExplicitHighRealBand etaLo etaHi T ↔
      rho ∈ dirichletNontrivialLFunctionZerosFinset
          (1 : DirichletCharacter ℂ 1) T ∧
        1 ≤ |rho.im| ∧ 1 - etaHi ≤ rho.re ∧
          rho.re < 1 - etaLo := by
  simp only [zetaExplicitHighRealBand, zetaExplicitUpperRealBand,
    zetaExplicitLowerRealBand, zetaExplicitUpperRectangle,
    zetaExplicitLowerRectangle, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨⟨hrho, hre, him⟩, hhi⟩ | ⟨⟨hrho, hre, him⟩, hhi⟩)
    · exact ⟨hrho, by rw [abs_of_nonneg (zero_le_one.trans him)]; exact him,
        hre, hhi⟩
    · exact ⟨hrho, by rw [abs_of_nonpos (him.trans (by norm_num))]; linarith,
        hre, hhi⟩
  · rintro ⟨hrho, him, hre, hhi⟩
    rcases le_total 0 rho.im with himPos | himNeg
    · have himOne : 1 ≤ rho.im := by
        rw [abs_of_nonneg himPos] at him
        exact him
      exact Or.inl ⟨⟨hrho, hre, himOne⟩, hhi⟩
    · have himOne : rho.im ≤ -1 := by
        rw [abs_of_nonpos himNeg] at him
        linarith
      exact Or.inr ⟨⟨hrho, hre, himOne⟩, hhi⟩

private theorem zetaExplicitHighFar_eq_nextBand_union_far
    (eta T : ℝ) (J : ℕ) (heta : 0 ≤ eta) :
    zetaExplicitHighFar eta J T =
      zetaExplicitHighRealBand
          (((J + 1 : ℕ) : ℝ) * eta)
          (((J + 2 : ℕ) : ℝ) * eta) T ∪
        zetaExplicitHighFar eta (J + 1) T := by
  ext rho
  simp only [zetaExplicitHighFar, zetaExplicitHighZeros,
    Finset.mem_filter, mem_zetaExplicitHighRealBand_iff,
    Finset.mem_union]
  constructor
  · rintro ⟨⟨hrho, him⟩, hupp⟩
    by_cases hlow : 1 - (((J + 2 : ℕ) : ℝ) * eta) ≤ rho.re
    · exact Or.inl ⟨hrho, him, hlow, hupp⟩
    · exact Or.inr ⟨⟨hrho, him⟩, by
        have h := lt_of_not_ge hlow
        push_cast at h ⊢
        norm_num at h ⊢
        linarith⟩
  · rintro (hband | hfar)
    · exact ⟨⟨hband.1, hband.2.1⟩, hband.2.2.2⟩
    · refine ⟨hfar.1, ?_⟩
      have h := hfar.2
      push_cast at h ⊢
      nlinarith

private theorem disjoint_zetaExplicitHighRealBand_highFar
    (eta T : ℝ) (J : ℕ) :
    Disjoint
      (zetaExplicitHighRealBand
        (((J + 1 : ℕ) : ℝ) * eta)
        (((J + 2 : ℕ) : ℝ) * eta) T)
      (zetaExplicitHighFar eta (J + 1) T) := by
  rw [Finset.disjoint_left]
  intro rho hband hfar
  rw [mem_zetaExplicitHighRealBand_iff] at hband
  rw [zetaExplicitHighFar, Finset.mem_filter] at hfar
  have hleft := hband.2.2.1
  have hright := hfar.2
  push_cast at hright
  linarith

/-- The high-ordinate zero set is the first band plus the first far-left
remainder.  This form intentionally retains the empty zero-free band. -/
theorem zetaExplicitHighZeros_eq_firstBand_union_far
    (eta T : ℝ) :
    zetaExplicitHighZeros T =
      zetaExplicitHighRealBand 0 eta T ∪
        zetaExplicitHighFar eta 0 T := by
  ext rho
  simp only [zetaExplicitHighZeros, zetaExplicitHighFar,
    Finset.mem_filter, mem_zetaExplicitHighRealBand_iff,
    Finset.mem_union, Nat.zero_add, Nat.cast_one, one_mul, sub_zero]
  constructor
  · rintro ⟨hrho, him⟩
    have hzero :=
      (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho).1
    by_cases hleft : 1 - eta ≤ rho.re
    · exact Or.inl ⟨hrho, him, hleft, hzero.2.2⟩
    · exact Or.inr ⟨⟨hrho, him⟩, lt_of_not_ge hleft⟩
  · rintro (hband | hfar)
    · exact ⟨hband.1, hband.2.1⟩
    · exact hfar.1

private theorem disjoint_zetaExplicitFirstBand_highFar
    (eta T : ℝ) :
    Disjoint (zetaExplicitHighRealBand 0 eta T)
      (zetaExplicitHighFar eta 0 T) := by
  rw [Finset.disjoint_left]
  intro rho hband hfar
  rw [mem_zetaExplicitHighRealBand_iff] at hband
  rw [zetaExplicitHighFar, Finset.mem_filter] at hfar
  apply (not_lt_of_ge hband.2.2.1)
  simpa using hfar.2

/-- Exact termwise decomposition of the high-ordinate zero contribution into
`J+1` adjacent bands followed by one far-left remainder. -/
theorem sum_zetaExplicitHighZeros_eq_sum_linearBands_add_far
    (f : ℂ → ℝ) (eta T : ℝ) (J : ℕ) (heta : 0 ≤ eta) :
    (∑ rho ∈ zetaExplicitHighZeros T, f rho) =
      (∑ j ∈ Finset.range (J + 1),
        ∑ rho ∈ zetaExplicitHighRealBand
          ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T,
          f rho) +
        ∑ rho ∈ zetaExplicitHighFar eta J T, f rho := by
  induction J with
  | zero =>
      rw [zetaExplicitHighZeros_eq_firstBand_union_far,
        Finset.sum_union (disjoint_zetaExplicitFirstBand_highFar eta T)]
      simp
  | succ J ih =>
      calc
        (∑ rho ∈ zetaExplicitHighZeros T, f rho) =
            (∑ j ∈ Finset.range (J + 1),
              ∑ rho ∈ zetaExplicitHighRealBand
                ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T,
                f rho) +
              ∑ rho ∈ zetaExplicitHighFar eta J T, f rho := ih
        _ = (∑ j ∈ Finset.range (J + 1),
              ∑ rho ∈ zetaExplicitHighRealBand
                ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T,
                f rho) +
              (∑ rho ∈ zetaExplicitHighRealBand
                  (((J + 1 : ℕ) : ℝ) * eta)
                  (((J + 2 : ℕ) : ℝ) * eta) T, f rho) +
              ∑ rho ∈ zetaExplicitHighFar eta (J + 1) T, f rho := by
                rw [zetaExplicitHighFar_eq_nextBand_union_far eta T J heta,
                  Finset.sum_union
                    (disjoint_zetaExplicitHighRealBand_highFar eta T J)]
                ring
        _ = (∑ j ∈ Finset.range ((J + 1) + 1),
              ∑ rho ∈ zetaExplicitHighRealBand
                ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T,
                f rho) +
              ∑ rho ∈ zetaExplicitHighFar eta (J + 1) T, f rho := by
                conv_rhs =>
                  lhs
                  rw [Finset.sum_range_succ]

/-! ### Zero-free and reciprocal estimates for the omitted pieces -/

/-- The first high-ordinate band is empty when its width lies inside the
classical conductor-one zero-free region. -/
theorem zetaExplicitHighRealBand_zero_eq_empty
    {M : ℕ} (hM : 2 ≤ M) {eta T : ℝ}
    (hT : 2 ≤ T) (heta : 0 ≤ eta)
    (hetaZF : eta ≤
      1 / ((M : ℝ) ^ 2 * Real.log (T + 2)))
    (hzeroFree : ∀ rho : ℂ, riemannZeta rho = 0 →
      rho.re < 1 - 1 / ((M : ℝ) ^ 2 *
        Real.log (|rho.im| + 2))) :
    zetaExplicitHighRealBand 0 eta T = ∅ := by
  ext rho
  simp only [Finset.notMem_empty, iff_false]
  intro hrho
  rw [mem_zetaExplicitHighRealBand_iff] at hrho
  have hzeroData :=
    (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho.1)
  have hzeta : riemannZeta rho = 0 := by
    simpa [DirichletCharacter.LFunction_modOne_eq] using hzeroData.1.1
  have hbound := hzeroFree rho hzeta
  have himT : |rho.im| ≤ T := by
    simpa [abs_of_nonneg (by linarith : 0 ≤ T)] using hzeroData.2
  have hargPos : 0 < |rho.im| + 2 := by positivity
  have hTargPos : 0 < T + 2 := by linarith
  have hlogMono : Real.log (|rho.im| + 2) ≤ Real.log (T + 2) :=
    Real.log_le_log hargPos (by linarith)
  have hlogPos : 0 < Real.log (|rho.im| + 2) := by
    apply Real.log_pos
    linarith [abs_nonneg rho.im]
  have hlogTPos : 0 < Real.log (T + 2) := hlogPos.trans_le hlogMono
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hdenMono :
      (M : ℝ) ^ 2 * Real.log (|rho.im| + 2) ≤
        (M : ℝ) ^ 2 * Real.log (T + 2) := by gcongr
  have hinvMono :
      1 / ((M : ℝ) ^ 2 * Real.log (T + 2)) ≤
        1 / ((M : ℝ) ^ 2 * Real.log (|rho.im| + 2)) := by
    exact one_div_le_one_div_of_le
      (mul_pos (sq_pos_of_pos hMpos) hlogPos) hdenMono
  have : 1 - eta ≥
      1 - 1 / ((M : ℝ) ^ 2 * Real.log (|rho.im| + 2)) := by
    linarith
  linarith [hrho.2.2.1]

noncomputable def zetaExplicitFar (delta T : ℝ) : Finset ℂ :=
  (dirichletNontrivialLFunctionZerosFinset
    (1 : DirichletCharacter ℂ 1) T).filter fun rho ↦
      rho.re < 1 - delta

/-- A short-interval far-left contribution is controlled by the standard
reciprocal-height zero multiplicity, at the cost of `1+T`. -/
theorem sum_norm_zetaExplicitFarKernelDiff_le_reciprocal
    {x y delta T : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hdelta : 0 ≤ delta)
    (hT : 0 ≤ T) :
    (∑ rho ∈ zetaExplicitFar delta T,
      ‖(analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
        (dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho)‖) ≤
      (x ^ (-delta) * (y - x)) * (1 + T) *
        dirichletNontrivialZeroReciprocalMultiplicitySum
          (1 : DirichletCharacter ℂ 1) T := by
  let Z := dirichletNontrivialLFunctionZerosFinset
    (1 : DirichletCharacter ℂ 1) T
  let m : ℂ → ℝ := fun rho ↦
    analyticOrderNatAt
      (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1)) rho
  let C : ℝ := x ^ (-delta) * (y - x) * (1 + T)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hterm : ∀ rho ∈ zetaExplicitFar delta T,
      ‖(analyticOrderNatAt
          (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
          (dirichletExplicitFormulaKernel y rho -
            dirichletExplicitFormulaKernel x rho)‖ ≤
        C * (m rho / (1 + |rho.im|)) := by
    intro rho hrho
    have hrhoData := Finset.mem_filter.mp hrho
    have hzero :=
      (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrhoData.1)
    have hrhoNe : rho ≠ 0 := by
      intro h
      subst rho
      have := hzero.1.2.1
      norm_num at this
    have hdiff := norm_dirichletExplicitFormulaKernel_sub_le
      hx hxy hrhoNe hzero.1.2.2.le
    have hpow : x ^ (rho.re - 1) ≤ x ^ (-delta) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith [hrhoData.2])
    have himT : |rho.im| ≤ T := by
      simpa [abs_of_nonneg hT] using hzero.2
    have hden : 0 < 1 + |rho.im| := by positivity
    have hheight : 1 + |rho.im| ≤ 1 + T := by linarith
    rw [norm_mul, Complex.norm_natCast]
    calc
      m rho * ‖dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho‖ ≤
        m rho * (x ^ (rho.re - 1) * (y - x)) := by
          exact mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ ≤ m rho * (x ^ (-delta) * (y - x)) := by gcongr
      _ = C * (m rho / (1 + |rho.im|)) *
          ((1 + |rho.im|) / (1 + T)) := by
            dsimp [C]
            have hTone : 0 < 1 + T := by linarith
            field_simp [hden.ne', hTone.ne']
      _ ≤ C * (m rho / (1 + |rho.im|)) * 1 := by
        gcongr
        exact (div_le_one (by linarith : 0 < 1 + T)).2 hheight
      _ = C * (m rho / (1 + |rho.im|)) := mul_one _
  calc
    (∑ rho ∈ zetaExplicitFar delta T,
      ‖(analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
        (dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho)‖) ≤
        ∑ rho ∈ zetaExplicitFar delta T,
          C * (m rho / (1 + |rho.im|)) := Finset.sum_le_sum hterm
    _ = C * ∑ rho ∈ zetaExplicitFar delta T,
          m rho / (1 + |rho.im|) := by rw [Finset.mul_sum]
    _ ≤ C * ∑ rho ∈ Z, m rho / (1 + |rho.im|) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro rho hrhoZ hrhoFar
      dsimp [m]
      positivity
    _ = (x ^ (-delta) * (y - x)) * (1 + T) *
        dirichletNontrivialZeroReciprocalMultiplicitySum
          (1 : DirichletCharacter ℂ 1) T := by
      rw [dirichletNontrivialZeroReciprocalMultiplicitySum]

noncomputable def zetaExplicitLowZeros (T : ℝ) : Finset ℂ :=
  (dirichletNontrivialLFunctionZerosFinset
    (1 : DirichletCharacter ℂ 1) T).filter fun rho ↦ |rho.im| < 1

private theorem disjoint_zetaExplicitHighLowZeros (T : ℝ) :
    Disjoint (zetaExplicitHighZeros T) (zetaExplicitLowZeros T) := by
  rw [Finset.disjoint_left]
  intro rho hhigh hlow
  rw [zetaExplicitHighZeros, Finset.mem_filter] at hhigh
  rw [zetaExplicitLowZeros, Finset.mem_filter] at hlow
  linarith

theorem dirichletZeros_eq_high_union_low (T : ℝ) :
    dirichletNontrivialLFunctionZerosFinset
        (1 : DirichletCharacter ℂ 1) T =
      zetaExplicitHighZeros T ∪ zetaExplicitLowZeros T := by
  ext rho
  simp only [zetaExplicitHighZeros, zetaExplicitLowZeros,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · intro hrho
    rcases le_total 1 |rho.im| with hhigh | hlow
    · exact Or.inl ⟨hrho, hhigh⟩
    · by_cases heq : |rho.im| = 1
      · exact Or.inl ⟨hrho, heq.ge⟩
      · exact Or.inr ⟨hrho, lt_of_le_of_ne hlow heq⟩
  · rintro (h | h) <;> exact h.1

theorem zetaExplicitHighFar_subset_far
    {eta delta T : ℝ} {J : ℕ}
    (hdelta : delta ≤ ((J + 1 : ℕ) : ℝ) * eta) :
    zetaExplicitHighFar eta J T ⊆ zetaExplicitFar delta T := by
  intro rho hrho
  rw [zetaExplicitHighFar, Finset.mem_filter] at hrho
  rw [zetaExplicitFar, Finset.mem_filter]
  exact ⟨(Finset.mem_filter.mp hrho.1).1, by linarith [hrho.2]⟩

/-- Low ordinates lie a fixed distance left of one by the same quantitative
zeta zero-free region. -/
theorem zetaExplicitLowZeros_subset_far
    {M : ℕ} (hM : 2 ≤ M) {delta T : ℝ}
    (hdelta : delta ≤ 1 / ((M : ℝ) ^ 2 * Real.log 3))
    (hzeroFree : ∀ rho : ℂ, riemannZeta rho = 0 →
      rho.re < 1 - 1 / ((M : ℝ) ^ 2 *
        Real.log (|rho.im| + 2))) :
    zetaExplicitLowZeros T ⊆ zetaExplicitFar delta T := by
  intro rho hrho
  rw [zetaExplicitLowZeros, Finset.mem_filter] at hrho
  rw [zetaExplicitFar, Finset.mem_filter]
  refine ⟨hrho.1, ?_⟩
  have hzeroData :=
    (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho.1)
  have hzeta : riemannZeta rho = 0 := by
    simpa [DirichletCharacter.LFunction_modOne_eq] using hzeroData.1.1
  have hbound := hzeroFree rho hzeta
  have hargPos : 0 < |rho.im| + 2 := by positivity
  have hthreePos : (0 : ℝ) < 3 := by norm_num
  have hargThree : |rho.im| + 2 < 3 := by linarith
  have hlogMono : Real.log (|rho.im| + 2) < Real.log 3 :=
    Real.strictMonoOn_log hargPos hthreePos hargThree
  have hlogPos : 0 < Real.log (|rho.im| + 2) := by
    apply Real.log_pos
    linarith [abs_nonneg rho.im]
  have hlogThreePos : 0 < Real.log 3 := hlogPos.trans hlogMono
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hdenLt :
      (M : ℝ) ^ 2 * Real.log (|rho.im| + 2) <
        (M : ℝ) ^ 2 * Real.log 3 := by gcongr
  have hinvLt :
      1 / ((M : ℝ) ^ 2 * Real.log 3) <
        1 / ((M : ℝ) ^ 2 * Real.log (|rho.im| + 2)) := by
    exact one_div_lt_one_div_of_lt
      (mul_pos (sq_pos_of_pos hMpos) hlogPos) hdenLt
  linarith

/-- The full modulus-one explicit-formula zero kernel over a short interval
is bounded by `J` density bands and two copies of one reciprocal far tail.
The index shift discards the zero-free first band. -/
theorem sum_norm_all_zetaKernelDiff_le_densityBands_add_far
    {M : ℕ} (hM : 2 ≤ M) {x y eta delta T : ℝ} {J : ℕ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hT : 2 ≤ T)
    (heta : 0 ≤ eta)
    (hetaZF : eta ≤
      1 / ((M : ℝ) ^ 2 * Real.log (T + 2)))
    (hdelta0 : 0 ≤ delta)
    (hdeltaLow : delta ≤ 1 / ((M : ℝ) ^ 2 * Real.log 3))
    (hdeltaHigh : delta ≤ ((J + 1 : ℕ) : ℝ) * eta)
    (hwidth : ∀ j ∈ Finset.range J,
      (((j + 2 : ℕ) : ℝ) * eta) ≤ 1)
    (hzeroFree : ∀ rho : ℂ, riemannZeta rho = 0 →
      rho.re < 1 - 1 / ((M : ℝ) ^ 2 *
        Real.log (|rho.im| + 2))) :
    (∑ rho ∈ dirichletNontrivialLFunctionZerosFinset
        (1 : DirichletCharacter ℂ 1) T,
      ‖(analyticOrderNatAt
        (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
        (dirichletExplicitFormulaKernel y rho -
          dirichletExplicitFormulaKernel x rho)‖) ≤
      (∑ j ∈ Finset.range J,
        2 * ((zetaHighZeroRectangleMass
            (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
          (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * (y - x)))) +
        2 * ((x ^ (-delta) * (y - x)) * (1 + T) *
          dirichletNontrivialZeroReciprocalMultiplicitySum
            (1 : DirichletCharacter ℂ 1) T) := by
  let f : ℂ → ℝ := fun rho ↦
    ‖(analyticOrderNatAt
      (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1)) rho : ℂ) *
      (dirichletExplicitFormulaKernel y rho -
        dirichletExplicitFormulaKernel x rho)‖
  have hfirst : zetaExplicitHighRealBand 0 eta T = ∅ :=
    zetaExplicitHighRealBand_zero_eq_empty hM hT heta hetaZF hzeroFree
  have hdecomp := sum_zetaExplicitHighZeros_eq_sum_linearBands_add_far
    f eta T J heta
  have hhighFar :
      (∑ rho ∈ zetaExplicitHighFar eta J T, f rho) ≤
        ∑ rho ∈ zetaExplicitFar delta T, f rho := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (zetaExplicitHighFar_subset_far hdeltaHigh)
    intro rho hrho hnot
    dsimp [f]
    positivity
  have hlow :
      (∑ rho ∈ zetaExplicitLowZeros T, f rho) ≤
        ∑ rho ∈ zetaExplicitFar delta T, f rho := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (zetaExplicitLowZeros_subset_far hM hdeltaLow hzeroFree)
    intro rho hrho hnot
    dsimp [f]
    positivity
  have hfar := sum_norm_zetaExplicitFarKernelDiff_le_reciprocal
    hx hxy hdelta0 (by linarith : 0 ≤ T)
  have hband : ∀ j ∈ Finset.range J,
      (∑ rho ∈ zetaExplicitHighRealBand
          (((j + 1 : ℕ) : ℝ) * eta)
          (((j + 2 : ℕ) : ℝ) * eta) T, f rho) ≤
        2 * ((zetaHighZeroRectangleMass
            (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
          (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * (y - x))) := by
    intro j hj
    simpa only [f] using
      sum_norm_zetaExplicitHighRealBandKernelDiff_le
        hx hxy (hwidth j hj) (by linarith : 1 ≤ T)
  rw [dirichletZeros_eq_high_union_low T,
    Finset.sum_union (disjoint_zetaExplicitHighLowZeros T)]
  rw [hdecomp]
  have hshift :
      (∑ j ∈ Finset.range (J + 1),
        ∑ rho ∈ zetaExplicitHighRealBand
          ((j : ℝ) * eta) (((j + 1 : ℕ) : ℝ) * eta) T,
          f rho) =
        ∑ j ∈ Finset.range J,
          ∑ rho ∈ zetaExplicitHighRealBand
            (((j + 1 : ℕ) : ℝ) * eta)
            (((j + 2 : ℕ) : ℝ) * eta) T, f rho := by
    rw [Finset.sum_range_succ']
    have hfirst' :
        zetaExplicitHighRealBand
          (((0 : ℕ) : ℝ) * eta)
          (((0 + 1 : ℕ) : ℝ) * eta) T = ∅ := by
      simpa using hfirst
    rw [hfirst']
    simp only [Finset.sum_empty, add_zero]
  rw [hshift]
  calc
    ((∑ j ∈ Finset.range J,
        ∑ rho ∈ zetaExplicitHighRealBand
          (((j + 1 : ℕ) : ℝ) * eta)
          (((j + 2 : ℕ) : ℝ) * eta) T, f rho) +
        ∑ rho ∈ zetaExplicitHighFar eta J T, f rho) +
      ∑ rho ∈ zetaExplicitLowZeros T, f rho ≤
        (∑ j ∈ Finset.range J,
          2 * ((zetaHighZeroRectangleMass
              (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
            (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * (y - x)))) +
          2 * (∑ rho ∈ zetaExplicitFar delta T, f rho) := by
            have hbands := Finset.sum_le_sum hband
            linarith
    _ ≤ (∑ j ∈ Finset.range J,
          2 * ((zetaHighZeroRectangleMass
              (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
            (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * (y - x)))) +
        2 * ((x ^ (-delta) * (y - x)) * (1 + T) *
          dirichletNontrivialZeroReciprocalMultiplicitySum
            (1 : DirichletCharacter ℂ 1) T) := by
              gcongr

/-! ### Scalar geometric summation for short intervals -/

/-- Short-interval analogue of the endpoint geometric-band lemma: the
derivative gain removes the leading factor `x` and leaves the interval
length `h`. -/
theorem shortDensityKernelBand_le_geometric
    {B x D c eta h : ℝ} {j : ℕ}
    (hB : 0 < B) (hx : 1 ≤ x) (hD : 0 ≤ D) (heta : 0 ≤ eta)
    (hh : 0 ≤ h)
    (hscale : c * Real.log B ≤ Real.log x / 4)
    (hcontract : 2 * Real.log 2 ≤ eta * Real.log x) :
    2 * ((D * B ^ (c * (((j + 2 : ℕ) : ℝ) * eta))) *
      (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * h)) ≤
        2 * D * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) * h *
            (1 / 2 : ℝ) ^ (j + 1) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hratio : Real.exp (-(eta * Real.log x) / 2) ≤ (1 / 2 : ℝ) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2), Real.exp_le_exp]
    have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
    rw [hloghalf]
    linarith
  have hratioPow :
      Real.exp (-(eta * Real.log x) / 2) ^ (j + 1) ≤
        (1 / 2 : ℝ) ^ (j + 1) :=
    pow_le_pow_left₀ (Real.exp_pos _).le hratio _
  have hexponent :
      Real.log B * (c * (((j + 2 : ℕ) : ℝ) * eta)) +
          Real.log x * (-(((j + 1 : ℕ) : ℝ) * eta)) ≤
        (c * eta * Real.log B - eta * Real.log x / 4) +
          ((j + 1 : ℕ) : ℝ) * (-(eta * Real.log x) / 2) := by
    have hj : (0 : ℝ) ≤ (j + 1 : ℕ) := by positivity
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hnonneg : 0 ≤ (j : ℝ) * eta * Real.log x := by positivity
    have hm := mul_le_mul_of_nonneg_left hscale (mul_nonneg hj heta)
    have hm' :
        c * eta * Real.log B * ((j + 1 : ℕ) : ℝ) ≤
          ((j + 1 : ℕ) : ℝ) * eta * Real.log x / 2 -
            eta * Real.log x / 4 := by
      calc
        c * eta * Real.log B * ((j + 1 : ℕ) : ℝ) =
            ((j + 1 : ℕ) : ℝ) * eta * (c * Real.log B) := by ring
        _ ≤ ((j + 1 : ℕ) : ℝ) * eta * (Real.log x / 4) := hm
        _ ≤ ((j + 1 : ℕ) : ℝ) * eta * Real.log x / 2 -
            eta * Real.log x / 4 := by
          push_cast
          nlinarith [hnonneg]
    push_cast at hm' ⊢
    nlinarith [hm']
  rw [Real.rpow_def_of_pos hB, Real.rpow_def_of_pos hxpos]
  have hexp := Real.exp_le_exp.mpr hexponent
  have hrearrange :
      Real.exp ((c * eta * Real.log B - eta * Real.log x / 4) +
          ((j + 1 : ℕ) : ℝ) * (-(eta * Real.log x) / 2)) =
        Real.exp (c * eta * Real.log B - eta * Real.log x / 4) *
          Real.exp (-(eta * Real.log x) / 2) ^ (j + 1) := by
    rw [Real.exp_add, Real.exp_nat_mul]
  rw [hrearrange] at hexp
  calc
    2 * ((D * Real.exp
          (Real.log B * (c * (((j + 2 : ℕ) : ℝ) * eta)))) *
        (Real.exp (Real.log x *
          (-(((j + 1 : ℕ) : ℝ) * eta))) * h)) =
        2 * D * Real.exp
          (Real.log B * (c * (((j + 2 : ℕ) : ℝ) * eta)) +
            Real.log x * (-(((j + 1 : ℕ) : ℝ) * eta))) * h := by
      rw [Real.exp_add]
      ring
    _ ≤ 2 * D *
        (Real.exp (c * eta * Real.log B - eta * Real.log x / 4) *
          Real.exp (-(eta * Real.log x) / 2) ^ (j + 1)) * h := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexp (mul_nonneg (by norm_num) hD)) hh
    _ ≤ 2 * D *
        (Real.exp (c * eta * Real.log B - eta * Real.log x / 4) *
          (1 / 2 : ℝ) ^ (j + 1)) * h := by
      gcongr
    _ = _ := by ring

/-- A power-form density estimate summed over all retained short-interval
bands. -/
theorem sum_densityBands_le_geometric
    {B x C c eta h T : ℝ} {J : ℕ}
    (hB : 0 < B) (hBone : 1 ≤ B) (hx : 1 ≤ x) (hC : 0 ≤ C)
    (heta : 0 ≤ eta) (hh : 0 ≤ h)
    (hdensity : ∀ j ∈ Finset.range J,
      (zetaHighZeroRectangleMass
        (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) ≤
          C * Real.log B ^ 3 *
            B ^ (c * (((j + 2 : ℕ) : ℝ) * eta)))
    (hscale : c * Real.log B ≤ Real.log x / 4)
    (hcontract : 2 * Real.log 2 ≤ eta * Real.log x) :
    (∑ j ∈ Finset.range J,
      2 * ((zetaHighZeroRectangleMass
          (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
        (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * h))) ≤
      2 * (C * Real.log B ^ 3) * Real.exp
        (c * eta * Real.log B - eta * Real.log x / 4) * h := by
  let D : ℝ := C * Real.log B ^ 3
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hBone
  have hD : 0 ≤ D := by dsimp [D]; positivity
  calc
    (∑ j ∈ Finset.range J,
      2 * ((zetaHighZeroRectangleMass
          (((j + 2 : ℕ) : ℝ) * eta) T : ℝ) *
        (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * h))) ≤
      ∑ j ∈ Finset.range J,
        2 * ((D * B ^ (c * (((j + 2 : ℕ) : ℝ) * eta))) *
          (x ^ (-(((j + 1 : ℕ) : ℝ) * eta)) * h)) := by
            apply Finset.sum_le_sum
            intro j hj
            gcongr
            simpa only [D, mul_assoc] using hdensity j hj
    _ ≤ ∑ j ∈ Finset.range J,
        (2 * D * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) * h) *
            (1 / 2 : ℝ) ^ (j + 1) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc] using shortDensityKernelBand_le_geometric
        hB hx hD heta hh hscale hcontract (j := j)
    _ ≤ (2 * D * Real.exp
          (c * eta * Real.log B - eta * Real.log x / 4) * h) * 1 := by
      let A : ℝ := 2 * D * Real.exp
        (c * eta * Real.log B - eta * Real.log x / 4) * h
      change (∑ j ∈ Finset.range J, A * (1 / 2 : ℝ) ^ (j + 1)) ≤ A * 1
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by dsimp [A]; positivity)
      rw [show (∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ (j + 1)) =
          (1 / 2 : ℝ) * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [pow_succ']]
      nlinarith [sum_geometric_two_le J]
    _ = _ := by dsimp [D]; ring

end

end Erdos381
