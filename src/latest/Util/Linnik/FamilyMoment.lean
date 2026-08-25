import Util.Linnik.FamilyExceptionalZero
import Util.Linnik.MomentDecay

/-!
# Small primitive-family moments with or without an exceptional zero

The parameter in the exponential is absolute.  In the exceptional case,
the bound retains the exceptional gap as a factor; no lower bound for that
gap is used in this step.
-/

namespace Linnik

open Complex Erdos48 BoundedGaps.Maynard
open scoped BigOperators Classical

local instance {Q : ℕ} (q : ↥(Finset.Ioc 1 Q)) : NeZero q.val :=
  ⟨by have hq := (Finset.mem_Ioc.mp q.property).1; omega⟩

theorem exp_moment_antitone_parameter
    {ι : Type*} (S : Finset ι) (u a : ι → ℝ) {c D : ℝ} (hcD : c ≤ D)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hu : ∀ i ∈ S, 0 ≤ u i) :
    (∑ i ∈ S, a i * Real.exp (-D * u i)) ≤
      ∑ i ∈ S, a i * Real.exp (-c * u i) := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (ha i hi)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hcD) (hu i hi)

theorem exists_family_moment_bounds {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ kappa H₀ D : ℝ, 0 < kappa ∧ kappa ≤ 1 ∧ 16 ≤ H₀ ∧ 1 ≤ D ∧
      ∀ Q T : ℕ, 2 ≤ Q → 2 ≤ T →
        let H := Real.log ((Q : ℝ) * ((T : ℝ) + 2))
        H₀ ≤ H →
        ((∀ i : upperHighZeroIndex Q T, kappa < H * upperHighZeroGap i) →
          (∑ i : upperHighZeroIndex Q T,
            upperHighZeroWeight i * Real.exp (-D * (H * upperHighZeroGap i))) ≤ epsilon) ∧
        (∀ i₀ : upperHighZeroIndex Q T, H * upperHighZeroGap i₀ ≤ kappa →
          i₀.2.1.1 ^ 2 = 1 ∧ i₀.2.2.val.im = 0 ∧ upperHighZeroWeight i₀ = 1 ∧
          (∑ i ∈ (Finset.univ : Finset (upperHighZeroIndex Q T)).erase i₀,
            upperHighZeroWeight i * Real.exp (-D * (H * upperHighZeroGap i))) ≤
              epsilon * (H * upperHighZeroGap i₀)) := by
  obtain ⟨kappa, hkappa, hkappa₁, hwidth⟩ := exists_family_exceptional_width
  obtain ⟨H₀, C, c, hH₀, hC, hc, hmoment⟩ := exists_upperHighZero_moment_bound
  obtain ⟨A, hA, hrepulsion⟩ := exists_crossLevel_exceptional_zero_repulsion
  let R : ℝ := 16384 * A
  let b : ℝ := 262144 * A
  obtain ⟨D₀, hcD₀, hD₀⟩ := exists_small_exp_moment_parameter (c := c) hC.le hkappa hepsilon
  obtain ⟨D₁, hcD₁, hD₁⟩ := exists_small_repelled_moment_parameter
    (c := c) (R := R) (b := b) hC.le hkappa hepsilon
  let D := max 1 (max D₀ D₁)
  have hD₀D : D₀ ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have hD₁D : D₁ ≤ D := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨kappa, H₀, D, hkappa, hkappa₁, hH₀, le_max_left _ _, ?_⟩
  intro Q T hQ hT H hH
  have hHpos : 0 < H := by linarith
  have hT₀ : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  let u : upperHighZeroIndex Q T → ℝ := fun i ↦ H * upperHighZeroGap i
  have hu (i : upperHighZeroIndex Q T) : 0 ≤ u i :=
    mul_nonneg hHpos.le (upperHighZeroGap_bounds hT₀ i).1
  have ha (i : upperHighZeroIndex Q T) : 0 ≤ upperHighZeroWeight i := Nat.cast_nonneg _
  have hbase := hmoment Q T hQ hT hH
  obtain ⟨hshape, hunique⟩ := hwidth Q T hT₀
  constructor
  · intro hgap
    apply (exp_moment_antitone_parameter Finset.univ u upperHighZeroWeight hD₀D
      (fun i _ ↦ ha i) (fun i _ ↦ hu i)).trans
    exact hD₀ _ Finset.univ u upperHighZeroWeight (fun i _ ↦ ha i)
      (fun i _ ↦ (hgap i).le) hbase
  · intro i₀ hi₀
    obtain ⟨hsquare, him, hweight⟩ := hshape i₀ hi₀
    refine ⟨hsquare, him, hweight, ?_⟩
    let S : Finset (upperHighZeroIndex Q T) := Finset.univ.erase i₀
    have hgap (i : upperHighZeroIndex Q T) (hi : i ∈ S) : kappa ≤ u i := by
      by_contra h
      have heq := hunique i i₀ (le_of_lt (lt_of_not_ge h)) hi₀
      exact (Finset.mem_erase.mp hi).1 heq
    have hbaseS : (∑ i ∈ S, upperHighZeroWeight i * Real.exp (-c * u i)) ≤ C := by
      apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ ↦ mul_nonneg (ha i) (Real.exp_pos _).le)) hbase
    have hrho₀ := upperHighZero_zero_data hT₀ i₀
    have hrhoReal : i₀.2.2.val = (i₀.2.2.val.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hrep (i : upperHighZeroIndex Q T) (hi : i ∈ S) :
        Real.exp (-R * u i) ≤ b * u i₀ := by
      have hrho := upperHighZero_zero_data hT₀ i
      have hne : goldfeldCharactersDistinct i₀.2.1.1 i.2.1.1 ∨
          i.2.2.val ≠ (i₀.2.2.val.re : ℂ) := by
        by_contra h
        push Not at h
        have heq := upperHighZeroIndex_eq_of_lifts_eq i₀ i h.1 (hrhoReal.trans h.2.symm)
        exact (Finset.mem_erase.mp hi).1 heq.symm
      have hz : DirichletCharacter.LFunction i₀.2.1.1 (i₀.2.2.val.re : ℂ) = 0 := by
        rw [← hrhoReal]
        exact hrho₀.1
      have h := hrepulsion i₀.1.val i.1.val Q (Finset.mem_Ioc.mp i₀.1.property).1
        (Finset.mem_Ioc.mp i₀.1.property).2 (Finset.mem_Ioc.mp i.1.property).2
        i₀.2.1.1 i.2.1.1 (primitiveCharacter_ne_one_of_one_lt
          (Finset.mem_Ioc.mp i₀.1.property).1 i₀.2.1) hsquare
        i₀.2.2.val.re hrho₀.2.1 hrho₀.2.2.1 hz T hT₀ i.2.2.val
        hrho.2.2.2 hrho.2.1 hrho.2.2.1 hrho.1 hne
      simpa only [R, b, u, H, upperHighZeroGap, neg_mul, mul_assoc] using h.le
    apply (exp_moment_antitone_parameter S u upperHighZeroWeight hD₁D
      (fun i _ ↦ ha i) (fun i _ ↦ hu i)).trans
    exact hD₁ _ S u upperHighZeroWeight (u i₀) (hu i₀) (hi₀.trans hkappa₁)
      (fun i _ ↦ ha i) hgap hrep hbaseS

end Linnik
