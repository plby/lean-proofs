import ErdosProblems.Erdos4.FiberAsymptotic
import ErdosProblems.Erdos4.ProductProjectionComparison
import ErdosProblems.Erdos4.UnitFourier

/-!
# Principal gain after discarding excessive reciprocal mass

The positive ideal kernel permits the bad coefficient labels to be
discarded. On the remaining labels the actual arithmetic fiber lower
bound is combined with the pointwise variational gain. The coefficient
energy, not the cardinality of the divisor support, measures the loss.
-/

open scoped BigOperators

namespace Erdos4.PrincipalLowerBound

open DivisorCoefficients IdealProjection IdealAction CutoffSimplex
open PrimitiveProfile RestrictedProductNorm CoefficientMass

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem fiberSum_nonneg {m : ℝ} (hm : 0 ≤ m) (R : ℕ) (ell : P → ℕ)
    (j : Fin k) (a : P → Option (Fin k)) : 0 ≤ fiberSum m R ell j a := by
  classical
  unfold fiberSum
  apply Finset.sum_nonneg
  intro b _hb
  split_ifs
  · apply mul_nonneg
    · exact (profile_pos hm (Nat.cast_nonneg k)
        (div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))).le
    · exact Finset.prod_nonneg (fun p _hp => by split_ifs <;> positivity)
  · exact le_rfl

theorem unitDensity_nonneg (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) :
    0 ≤ UnitFourier.unitDensity ell := by
  apply Finset.prod_nonneg
  intro p _hp
  have hh : (1 : ℝ) ≤ ell p := by exact_mod_cast hell p
  exact div_nonneg (by linarith) (Nat.cast_nonneg _)

/-- The fiber lower bound may be negative. Positivity of the fiber and
the Euler product still makes the density comparison valid. -/
theorem coefficient_action_lower {m : ℝ} (hm : 0 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 2 ≤ ell p) (j : Fin k)
    (a : P → Option (Fin k)) (ha : totalDivisor ell a ≤ R)
    {B : ℝ} (hB : B ≤ fiberSum m R ell j a) :
    coefficient m R ell a ^ 2 * UnitFourier.unitDensity ell * B /
        profile m k (coordinate R ell a j) ≤
      coefficient m R ell a *
        ProjectionKernel.action (ProjectionKernel.tensor (fun p => normal (ell p : ℝ) j))
          (coefficient m R ell) a := by
  have hg : 0 < profile m k (coordinate R ell a j) :=
    profile_pos hm (Nat.cast_nonneg k) (coordinate_nonneg ell a j)
  have hV : 0 ≤ UnitFourier.unitDensity ell :=
    unitDensity_nonneg ell (fun p => (by have := hell p; omega))
  have hprod : UnitFourier.unitDensity ell * B ≤
      activeDensity ell j a * fiberSum m R ell j a := by
    calc
      _ ≤ UnitFourier.unitDensity ell * fiberSum m R ell j a :=
        mul_le_mul_of_nonneg_left hB hV
      _ ≤ _ := mul_le_mul_of_nonneg_right (density_product_le_active ell hell j a)
        (fiberSum_nonneg hm R ell j a)
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprod (sq_nonneg (coefficient m R ell a))) hg.le
  rw [action_coefficient_eq_ratio hm hR ell hell j a ha]
  calc
    _ = coefficient m R ell a ^ 2 * (UnitFourier.unitDensity ell * B) /
        profile m k (coordinate R ell a j) := by ring
    _ ≤ coefficient m R ell a ^ 2 * (activeDensity ell j a * fiberSum m R ell j a) /
        profile m k (coordinate R ell a j) := hh
    _ = _ := by unfold coordinate; ring

theorem perturbed_gain {m : ℝ} (hm : 1 ≤ m) (t : Fin k → ℝ)
    (ht : ∀ i, 0 ≤ t i) (hS : (∑ i, t i) ≤ 1) {e G : ℝ} (he : 0 ≤ e)
    (hG : G ≤ ∑ i, primitive m k (1 - (∑ j, t j) + t i) / profile m k (t i)) :
    G - e * k / profile m k 1 ≤
      ∑ i, (primitive m k (1 - (∑ j, t j) + t i) - e) / profile m k (t i) := by
  have hg1 : 0 < profile m k 1 := profile_pos (by linarith) (Nat.cast_nonneg k) (by norm_num)
  have hpoint : ∀ i, e / profile m k (t i) ≤ e / profile m k 1 := by
    intro i
    have hti : t i ≤ 1 :=
      (Finset.single_le_sum (fun j _hj => ht j) (Finset.mem_univ i)).trans hS
    exact div_le_div_of_nonneg_left he hg1 (profile_one_le hm (Nat.cast_nonneg k) (ht i) hti)
  have herr := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun i _hi => hpoint i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at herr
  have herr' : (∑ i : Fin k, e / profile m k (t i)) ≤ e * k / profile m k 1 :=
    herr.trans_eq (by ring)
  simp_rw [sub_div]
  rw [Finset.sum_sub_distrib]
  linarith

theorem pointwise_sum_lower {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 2 ≤ ell p)
    (a : P → Option (Fin k)) (ha : totalDivisor ell a ≤ R)
    {L e M : ℝ} (hL : 0 ≤ L) (he : 0 ≤ e)
    (hgain : M + e * k / profile m k 1 ≤
      ∑ j, primitive m k (1 - (∑ i, coordinate R ell a i) + coordinate R ell a j) /
        profile m k (coordinate R ell a j))
    (hfiber : ∀ j, L *
      (primitive m k (1 - (∑ i, coordinate R ell a i) + coordinate R ell a j) - e) ≤
        fiberSum m R ell j a) :
    UnitFourier.unitDensity ell * L * M * coefficient m R ell a ^ 2 ≤
      ∑ j : Fin k, coefficient m R ell a *
        ProjectionKernel.action (ProjectionKernel.tensor (fun p => normal (ell p : ℝ) j))
          (coefficient m R ell) a := by
  have hell1 : ∀ p, 1 ≤ ell p := fun p => by have := hell p; omega
  have hpert := perturbed_gain hm (coordinate R ell a) (coordinate_nonneg ell a)
    (sum_coordinate_le_one hR ell hell1 a ha) he hgain
  have hM : M ≤ ∑ j : Fin k,
      (primitive m k (1 - (∑ i, coordinate R ell a i) + coordinate R ell a j) - e) /
        profile m k (coordinate R ell a j) := by linarith
  have hfac : 0 ≤ coefficient m R ell a ^ 2 * UnitFourier.unitDensity ell * L :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (unitDensity_nonneg ell hell1)) hL
  calc
    _ = coefficient m R ell a ^ 2 * UnitFourier.unitDensity ell * L * M := by ring
    _ ≤ coefficient m R ell a ^ 2 * UnitFourier.unitDensity ell * L *
        ∑ j : Fin k,
          (primitive m k (1 - (∑ i, coordinate R ell a i) + coordinate R ell a j) - e) /
            profile m k (coordinate R ell a j) := mul_le_mul_of_nonneg_left hM hfac
    _ = ∑ j : Fin k, coefficient m R ell a ^ 2 * UnitFourier.unitDensity ell *
        (L * (primitive m k (1 - (∑ i, coordinate R ell a i) + coordinate R ell a j) - e)) /
          profile m k (coordinate R ell a j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ ≤ _ := Finset.sum_le_sum (fun j _hj =>
      coefficient_action_lower (by linarith) hR ell hell j a ha (hfiber j))

theorem good_energy_lower {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) {η : ℝ} (hη : 0 < η) :
    energy (coefficient (k := k) m R ell) -
      (energy (coefficient (k := k) m R ell) * k * ∑ p, (((ell p : ℝ) - 1)⁻¹) ^ 2) / η ≤
    ∑ a ∈ (Finset.univ : Finset (P → Option (Fin k))).filter
        (fun a => reciprocalMass ell a ≤ η), coefficient m R ell a ^ 2 := by
  classical
  have hbad := excessive_mass_energy_le (k := k) hm hR ell hell hη
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (P → Option (Fin k))) (fun a => reciprocalMass ell a ≤ η)
    (fun a => coefficient m R ell a ^ 2)
  simp only [not_le] at hsplit
  change _ = energy (coefficient (k := k) m R ell) at hsplit
  linarith

theorem sum_forms_lower {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 2 ≤ ell p)
    {L e M η : ℝ} (hL : 0 ≤ L) (he : 0 ≤ e) (hM : 0 ≤ M) (hη : 0 < η)
    (hgain : ∀ t : Fin k → ℝ, (∀ i, 0 ≤ t i) → (∑ i, t i) ≤ 1 →
      M + e * k / profile m k 1 ≤ ∑ j, primitive m k (1 - (∑ i, t i) + t j) / profile m k (t j))
    (hfiber : ∀ (a : P → Option (Fin k)), totalDivisor ell a ≤ R →
      reciprocalMass ell a ≤ η → ∀ j,
      L * (primitive m k (1 - (∑ i, coordinate R ell a i) + coordinate R ell a j) - e) ≤
        fiberSum m R ell j a) :
    UnitFourier.unitDensity ell * L * M *
      (energy (coefficient (k := k) m R ell) -
        (energy (coefficient (k := k) m R ell) * k * ∑ p, (((ell p : ℝ) - 1)⁻¹) ^ 2) / η) ≤
      ∑ j : Fin k, ProjectionSliceBound.form (fun p => normal (ell p : ℝ) j)
        (coefficient m R ell) (coefficient m R ell) := by
  classical
  have hell1 : ∀ p, 1 ≤ ell p := fun p => by have := hell p; omega
  let S := (Finset.univ : Finset (P → Option (Fin k))).filter (fun a => reciprocalMass ell a ≤ η)
  let T : (P → Option (Fin k)) → ℝ := fun a =>
    ∑ j : Fin k, coefficient m R ell a *
      ProjectionKernel.action (ProjectionKernel.tensor (fun p => normal (ell p : ℝ) j))
        (coefficient m R ell) a
  have hT : ∀ a, 0 ≤ T a := by
    intro a
    apply Finset.sum_nonneg
    intro j _hj
    exact mul_nonneg (coefficient_nonneg (by linarith) hR ell a)
      (action_coefficient_nonneg (by linarith) hR ell hell j a)
  have hpoint : ∀ a ∈ S,
      UnitFourier.unitDensity ell * L * M * coefficient m R ell a ^ 2 ≤ T a := by
    intro a ha
    by_cases hs : totalDivisor ell a ≤ R
    · exact pointwise_sum_lower hm hR ell hell a hs hL he
        (hgain (coordinate R ell a) (coordinate_nonneg ell a)
          (sum_coordinate_le_one hR ell hell1 a hs))
        (hfiber a hs (Finset.mem_filter.mp ha).2)
    · have hz : coefficient m R ell a = 0 := by simp [coefficient, hs]
      simpa only [hz, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using hT a
  have hfac : 0 ≤ UnitFourier.unitDensity ell * L * M :=
    mul_nonneg (mul_nonneg (unitDensity_nonneg ell hell1) hL) hM
  calc
    _ ≤ UnitFourier.unitDensity ell * L * M * ∑ a ∈ S, coefficient m R ell a ^ 2 :=
      mul_le_mul_of_nonneg_left (good_energy_lower hm hR ell hell1 hη) hfac
    _ = ∑ a ∈ S, UnitFourier.unitDensity ell * L * M * coefficient m R ell a ^ 2 :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ a ∈ S, T a := Finset.sum_le_sum hpoint
    _ ≤ ∑ a, T a := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ha _hnot => hT a)
    _ = _ := Finset.sum_comm

end Erdos4.PrincipalLowerBound
