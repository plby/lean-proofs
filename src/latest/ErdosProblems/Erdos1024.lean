/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import ErdosProblems.Erdos1024.UpperAnalytic
import ErdosProblems.Erdos1024.LowerAnalytic

/-!
# Erdős Problem 1024

For an `n`-vertex three-uniform linear hypergraph, let `f(n)` be the largest
integer which is always the size of some independent set.  Phelps and Rödl
proved

`f(n) = Θ(√(n log n))`.

The mathematical reconstruction, including the quantitative probabilistic
lemmas and the formalization plan, is in `tex/1024.tex`.
-/

open Filter
open scoped BigOperators

namespace Erdos1024

/-! ## Exact finite formulation -/

/-- A finite triple system on the fixed vertex type `Fin n`. -/
abbrev TripleSystem (n : ℕ) := Finset (Finset (Fin n))

/-- All three-element subsets of `Fin n`. -/
def allTriples (n : ℕ) : TripleSystem n :=
  Finset.univ.powersetCard 3

/-- Every member of `H` is a triple. -/
def IsThreeUniform {n : ℕ} (H : TripleSystem n) : Prop :=
  ∀ e ∈ H, e.card = 3

instance isThreeUniformDecidable {n : ℕ} (H : TripleSystem n) :
    Decidable (IsThreeUniform H) := by
  unfold IsThreeUniform
  infer_instance

/-- Distinct edges meet in at most one vertex. -/
def IsLinear {n : ℕ} (H : TripleSystem n) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ∀ ⦃f⦄, f ∈ H → e ≠ f → (e ∩ f).card ≤ 1

instance isLinearDecidable {n : ℕ} (H : TripleSystem n) :
    Decidable (IsLinear H) := by
  unfold IsLinear
  infer_instance

/-- `I` contains no whole edge of `H`. -/
def IsIndependent {n : ℕ} (H : TripleSystem n) (I : Finset (Fin n)) : Prop :=
  ∀ ⦃e⦄, e ∈ H → ¬e ⊆ I

instance isIndependentDecidable {n : ℕ} (H : TripleSystem n)
    (I : Finset (Fin n)) : Decidable (IsIndependent H I) := by
  unfold IsIndependent
  infer_instance

theorem subset_allTriples_iff {n : ℕ} {H : TripleSystem n} :
    H ⊆ allTriples n ↔ IsThreeUniform H := by
  constructor
  · intro h e he
    exact (Finset.mem_powersetCard.mp (h he)).2
  · intro h e he
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ e, h e he⟩

@[simp]
theorem independent_empty {n : ℕ} (H : TripleSystem n) :
    IsIndependent H ∅ ↔ ∅ ∉ H := by
  constructor
  · intro h hmem
    exact h hmem (Finset.empty_subset _)
  · intro hempty e he hesub
    have : e = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx ↦ by
      simpa using hesub hx
    exact hempty (this ▸ he)

theorem independent_mono {n : ℕ} {H : TripleSystem n}
    {I J : Finset (Fin n)} (hI : IsIndependent H I) (hJI : J ⊆ I) :
    IsIndependent H J := by
  intro e he heJ
  exact hI he (heJ.trans hJI)

/-- The largest cardinality of an independent vertex set. -/
noncomputable def independenceNumber {n : ℕ} (H : TripleSystem n) : ℕ :=
  (Finset.univ.powerset.filter (IsIndependent H)).sup Finset.card

theorem card_le_independenceNumber {n : ℕ} {H : TripleSystem n}
    {I : Finset (Fin n)} (hI : IsIndependent H I) :
    I.card ≤ independenceNumber H := by
  classical
  unfold independenceNumber
  apply Finset.le_sup
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.subset_univ I), hI⟩

theorem independenceNumber_le {n : ℕ} (H : TripleSystem n) :
    independenceNumber H ≤ n := by
  classical
  unfold independenceNumber
  apply Finset.sup_le
  intro I hI
  have hcard := Finset.card_le_card (Finset.mem_powerset.mp
    (Finset.mem_filter.mp hI).1)
  simpa using hcard

theorem independentFamily_nonempty {n : ℕ} (H : TripleSystem n)
    (hempty : ∅ ∉ H) :
    (Finset.univ.powerset.filter (IsIndependent H)).Nonempty := by
  classical
  exact ⟨∅, Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),
      (independent_empty H).mpr hempty⟩⟩

theorem exists_independent_card_eq {n : ℕ} (H : TripleSystem n)
    (hempty : ∅ ∉ H) :
    ∃ I : Finset (Fin n), IsIndependent H I ∧
      I.card = independenceNumber H := by
  classical
  obtain ⟨I, hI, hcard⟩ := Finset.exists_mem_eq_sup
    (Finset.univ.powerset.filter (IsIndependent H))
    (independentFamily_nonempty H hempty) Finset.card
  refine ⟨I, (Finset.mem_filter.mp hI).2, ?_⟩
  simpa [independenceNumber] using hcard.symm

/-- Adding edges can only decrease the independence number. -/
theorem independenceNumber_antitone {n : ℕ} {H K : TripleSystem n}
    (hHK : H ⊆ K) : independenceNumber K ≤ independenceNumber H := by
  classical
  unfold independenceNumber
  apply Finset.sup_le
  intro I hIK
  apply Finset.le_sup
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hIK).1, ?_⟩
  intro e heH
  exact (Finset.mem_filter.mp hIK).2 (hHK heH)

/-- The finite collection of all linear triple systems on `Fin n`. -/
noncomputable def linearSystems (n : ℕ) : Finset (TripleSystem n) :=
  (allTriples n).powerset.filter IsLinear

theorem linearSystems_nonempty (n : ℕ) : (linearSystems n).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [linearSystems, IsLinear]

theorem mem_linearSystems_iff {n : ℕ} {H : TripleSystem n} :
    H ∈ linearSystems n ↔ IsThreeUniform H ∧ IsLinear H := by
  classical
  rw [linearSystems, Finset.mem_filter, Finset.mem_powerset,
    subset_allTriples_iff]

/-- The least possible independence number of an `n`-vertex linear triple
system.  This is the precise extremal interpretation of `f(n)` in the
problem. -/
noncomputable def guaranteedIndependence (n : ℕ) : ℕ :=
  (linearSystems n).inf' (linearSystems_nonempty n) independenceNumber

theorem guaranteedIndependence_le {n : ℕ} {H : TripleSystem n}
    (h3 : IsThreeUniform H) (hlin : IsLinear H) :
    guaranteedIndependence n ≤ independenceNumber H := by
  classical
  unfold guaranteedIndependence
  exact Finset.inf'_le independenceNumber
    (mem_linearSystems_iff.mpr ⟨h3, hlin⟩)

theorem exists_extremal_system (n : ℕ) :
    ∃ H : TripleSystem n,
      IsThreeUniform H ∧ IsLinear H ∧
        independenceNumber H = guaranteedIndependence n := by
  classical
  obtain ⟨H, hH, heq⟩ := Finset.exists_mem_eq_inf'
    (linearSystems_nonempty n) independenceNumber
  exact ⟨H, (mem_linearSystems_iff.mp hH).1,
    (mem_linearSystems_iff.mp hH).2, heq.symm⟩

theorem guaranteedIndependence_le_n (n : ℕ) :
    guaranteedIndependence n ≤ n := by
  obtain ⟨H, -, -, hH⟩ := exists_extremal_system n
  rw [← hH]
  exact independenceNumber_le H

/-- `k` is universally guaranteed if every linear triple system on `Fin n`
has an independent set with at least `k` vertices. -/
def UniversallyGuarantees (n k : ℕ) : Prop :=
  ∀ H : TripleSystem n, IsThreeUniform H → IsLinear H →
    ∃ I : Finset (Fin n), IsIndependent H I ∧ k ≤ I.card

/-- The extremal definition really is the largest universally guaranteed
integer, rather than merely some one-sided bound. -/
theorem universallyGuarantees_iff_le {n k : ℕ} :
    UniversallyGuarantees n k ↔ k ≤ guaranteedIndependence n := by
  constructor
  · intro h
    obtain ⟨H, h3, hlin, hH⟩ := exists_extremal_system n
    obtain ⟨I, hI, hkI⟩ := h H h3 hlin
    rw [← hH]
    exact hkI.trans (card_le_independenceNumber hI)
  · intro hk H h3 hlin
    have hempty : ∅ ∉ H := by
      intro h0
      have := h3 ∅ h0
      simp at this
    obtain ⟨I, hI, hcard⟩ := exists_independent_card_eq H hempty
    exact ⟨I, hI, hk.trans ((guaranteedIndependence_le h3 hlin).trans_eq
      hcard.symm)⟩

/-- There is a linear triple system witnessing sharpness of the universal
guarantee at each finite order. -/
theorem exists_system_sharp_for_guarantee (n : ℕ) :
    ∃ H : TripleSystem n, IsThreeUniform H ∧ IsLinear H ∧
      ∀ I : Finset (Fin n), IsIndependent H I →
        I.card ≤ guaranteedIndependence n := by
  obtain ⟨H, h3, hlin, hH⟩ := exists_extremal_system n
  refine ⟨H, h3, hlin, ?_⟩
  intro I hI
  rw [← hH]
  exact card_le_independenceNumber hI

/-! The quantitative Phelps--Rödl lower and upper bounds, and their
asymptotic assembly, follow below. -/

/-! ## The asymptotic scale and a two-sided-bound assembler -/

/-- The real-valued scale occurring in the Phelps--Rödl theorem. -/
noncomputable def resolutionScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log n)

theorem resolutionScale_eq_upperScale (n : ℕ) :
    resolutionScale n = Upper.upperScale n := rfl

/-! ## The Phelps--Rödl upper bound -/

/-- The explicit local-lemma construction bounds the exact extremal
quantity by `ceil (200 * sqrt (n log n))`. -/
theorem guaranteedIndependence_lt_upperThreshold (n : ℕ) (hn : 3 ≤ n) :
    guaranteedIndependence n < Upper.upperThreshold n := by
  obtain ⟨H, h3, hlin, hhits⟩ := Upper.exists_upper_system n hn
  have hempty : ∅ ∉ H := by
    intro h0
    have := h3 ∅ h0
    simp at this
  obtain ⟨I, hI, hcard⟩ := exists_independent_card_eq H hempty
  have hIt : I.card < Upper.upperThreshold n := by
    by_contra hnot
    obtain ⟨S, hSI, hScard⟩ :=
      Finset.exists_subset_card_eq (Nat.le_of_not_gt hnot)
    obtain ⟨e, heH, heS⟩ := hhits S hScard
    exact hI heH (heS.trans hSI)
  exact (guaranteedIndependence_le h3 hlin).trans_lt (hcard ▸ hIt)

theorem guaranteedIndependence_upper_bound (n : ℕ) (hn : 3 ≤ n) :
    (guaranteedIndependence n : ℝ) ≤ 201 * resolutionScale n := by
  have hnat := (guaranteedIndependence_lt_upperThreshold n hn).le
  have hcast : (guaranteedIndependence n : ℝ) ≤ Upper.upperThreshold n := by
    exact_mod_cast hnat
  rw [resolutionScale_eq_upperScale]
  exact hcast.trans (Upper.threshold_bounds hn).2.1

theorem resolutionScale_nonneg (n : ℕ) : 0 ≤ resolutionScale n := by
  exact Real.sqrt_nonneg _

/-- Eventual positive two-sided constant bounds are exactly what is needed
to manufacture a `Theta` statement.  Keeping this bookkeeping separate
prevents the probabilistic arguments from being entangled with norms. -/
theorem isTheta_of_eventually_two_sided
    (f g : ℕ → ℝ) (c C : ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n)
    (hc : 0 < c)
    (hlower : ∀ᶠ n in atTop, c * g n ≤ f n)
    (hupper : ∀ᶠ n in atTop, f n ≤ C * g n) :
    f =Θ[atTop] g := by
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    exact hupper.mono fun n hn ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf n), abs_of_nonneg (hg n)] using hn
  · apply Asymptotics.IsBigO.of_bound c⁻¹
    exact hlower.mono fun n hn ↦ by
      simp only [Real.norm_eq_abs, abs_of_nonneg (hf n), abs_of_nonneg (hg n)]
      calc
        g n = c⁻¹ * (c * g n) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
        _ ≤ c⁻¹ * f n := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hc.le)

/-! ## The Phelps--Rödl lower bound and final resolution -/

/-- The finite sampling-and-weight argument gives a universal lower bound
with an explicit positive constant. -/
theorem eventually_guaranteedIndependence_lower_bound :
    ∀ᶠ n : ℕ in atTop,
      Lower.lowerConstant * resolutionScale n ≤
        (guaranteedIndependence n : ℝ) := by
  filter_upwards [Lower.eventually_exists_independent_gt] with n hn
  have huniv : UniversallyGuarantees n (Lower.independenceCutoff n + 1) := by
    intro H h3 hlin
    have h3' : Lower.ThreeUniform H := h3
    have hlin' : Lower.Linear H := hlin
    obtain ⟨I, hI, hcard⟩ := hn H h3' hlin'
    refine ⟨I, ?_, by omega⟩
    exact hI
  have hguar : Lower.independenceCutoff n + 1 ≤
      guaranteedIndependence n := universallyGuarantees_iff_le.mp huniv
  have hfloor : Lower.lowerConstant * resolutionScale n <
      (Lower.independenceCutoff n : ℝ) + 1 := by
    simpa [Lower.independenceCutoff, Lower.lowerScale, resolutionScale] using
      (Nat.lt_floor_add_one (Lower.lowerConstant * Lower.lowerScale n))
  have hguarR : (Lower.independenceCutoff n : ℝ) + 1 ≤
      guaranteedIndependence n := by exact_mod_cast hguar
  exact (hfloor.trans_le hguarR).le

/-- Resolution of Erdős Problem 1024: the exact minimum guaranteed
independence number is of order `sqrt (n log n)`. -/
theorem erdos_problem_1024 :
    (fun n : ℕ ↦ (guaranteedIndependence n : ℝ)) =Θ[atTop]
      resolutionScale := by
  apply isTheta_of_eventually_two_sided
    (fun n : ℕ ↦ (guaranteedIndependence n : ℝ)) resolutionScale
    Lower.lowerConstant 201
  · intro n
    positivity
  · exact resolutionScale_nonneg
  · exact Lower.lowerConstant_pos
  · exact eventually_guaranteedIndependence_lower_bound
  · filter_upwards [eventually_ge_atTop 3] with n hn
    exact guaranteedIndependence_upper_bound n hn

end Erdos1024

#print axioms Erdos1024.erdos_problem_1024
