import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedRoots
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedRegular
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedElliptic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedCusp

/-!
# Remark 9.25: the actual finite subgroups have the same fixed locus

Every nonidentity finite-order parameter of the original multiplicative
action fixes exactly `D₀`. Its real-time lift has no fixed point in the
genuine regular and elliptic pieces, while the original cusp quotient
has the same finite-order fixed points as its toric cover because its
deck lattice is torsion-free. The argument uses the actual four-piece
cover and quotient formulas, not the normal weights along `D₀`.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed

/-- Any nontrivial finite-order element of the original action has
exactly the full-action fixed locus on the original compact threefold. -/
theorem actionBiholomorph_fixed_iff_D₀ (u : ℂˣ) (hu : u ≠ 1)
    (hfin : IsOfFinOrder u) (x : Space) :
    VerticalAction.actionBiholomorph u x = x ↔ x ∈ VerticalAction.D₀ := by
  let := VerticalAction.action
  constructor
  · intro hx
    obtain ⟨s, hs, hsi⟩ := exists_noninteger_real_parameter u hu hfin
    have ht : VerticalAction.flow (s : ℂ) x = x := by
      rw [← VerticalAction.actionBiholomorph_exponential, hs]
      exact hx
    obtain ⟨i, y, rfl⟩ := gluingData.inclusion_jointly_surjective x
    have hy : VerticalAction.localFlow i (s : ℂ) y = y :=
      (gluingData.inclusion_openEmbedding i).injective
        ((VerticalAction.flow_inclusion (s : ℂ) i y).symm.trans ht)
    cases i with
    | none => exact (Regular.real_flow_ne_self s hsi y hy).elim
    | some i =>
        cases i with
        | none => exact (Cusp.actionBiholomorph_inclusion_fixed_iff_D₀ u hu hfin y).mp hx
        | some j => exact (Elliptic.real_specialFlow_ne_self j s hsi y hy).elim
  · intro hx
    exact (VerticalAction.action_fixed_iff x).mpr hx u

/-- The same criterion in the literal notation of the existing action. -/
theorem action_fixed_iff_D₀ (u : ℂˣ) (hu : u ≠ 1) (hfin : IsOfFinOrder u) (x : Space) :
    letI := VerticalAction.action
    u • x = x ↔ x ∈ VerticalAction.D₀ :=
  actionBiholomorph_fixed_iff_D₀ u hu hfin x

/-- The set fixed by one nonidentity finite-order parameter is the
actual double curve, with no remaining geometric input. -/
theorem fixedSet_eq_D₀ (u : ℂˣ) (hu : u ≠ 1) (hfin : IsOfFinOrder u) :
    {x : Space | VerticalAction.actionBiholomorph u x = x} = VerticalAction.D₀ := by
  ext x
  exact actionBiholomorph_fixed_iff_D₀ u hu hfin x

/-- For every `n ≥ 2`, the literal roots-of-unity subgroup, acting by
restriction of the original action, has fixed-point set precisely `D₀`. -/
theorem rootsOfUnity_fixedPoints_eq_D₀ (n : ℕ) (hn : 2 ≤ n) :
    letI := VerticalAction.action
    MulAction.fixedPoints (rootsOfUnity n ℂ) Space = VerticalAction.D₀ := by
  let := VerticalAction.action
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  ext x
  constructor
  · intro hx
    have hs : standardRoot n • x = x := hx ⟨standardRoot n, standardRoot_mem hn0⟩
    exact (action_fixed_iff_D₀ (standardRoot n) (standardRoot_ne_one hn)
      (standardRoot_isOfFinOrder hn0) x).mp hs
  · intro hx u
    exact (VerticalAction.action_fixed_iff x).mpr hx u.val

/-- This is equality with the fixed-point set of the full original
complex multiplicative action, not just equality of abstract models. -/
theorem rootsOfUnity_fixedPoints_eq_full (n : ℕ) (hn : 2 ≤ n) :
    letI := VerticalAction.action
    MulAction.fixedPoints (rootsOfUnity n ℂ) Space = MulAction.fixedPoints ℂˣ Space :=
  (rootsOfUnity_fixedPoints_eq_D₀ n hn).trans VerticalAction.fixedPoints_eq_D₀.symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed
