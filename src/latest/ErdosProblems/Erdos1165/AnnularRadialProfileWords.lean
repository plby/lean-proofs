/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialLabelWord
import ErdosProblems.Erdos1165.AnnularIntegratedProfileKernel
import ErdosProblems.Erdos1165.TerminalNegativeBinomialWindow

/-!
# Fixed-profile families of chronological radial words

This module selects the finite radial-label words whose literal inward
transition counts realize a prescribed HLOZ internal profile and whose last
count lies in the successful terminal window.  Membership in the resulting
path event is converted back to the exact `excursionProfile` coordinates.

The initial level-one crossing is intentionally not included: it belongs to
the separate initial stopped piece in the final successful-event splice.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AnnularRadialProfileWords

open AppendixFirstMoment AnnularRadialLabelWord
  AnnularIntegratedProfileKernel
  TerminalNegativeBinomialWindow ThickPoint
  TerminalExcursionBridge TerminalSequentialVisitLaw PlanarPotential

noncomputable section

/-- A generous finite transition cutoff.  The exact identity
`L = 2 * (sum of all upcrossings) + 1` will show that every successful radial
word lies below this bound. -/
def profileRadialWordMaxTransitions (n : ℕ) : ℕ := 8 * n ^ 3 + 1

/-- A finite cutoff depending on one exact internal profile.  Unlike
`profileRadialWordMaxTransitions`, this remains valid when a bounded number
of profile coordinates are deliberately left unconstrained. -/
def exactProfileRadialWordMaxTransitions {n : ℕ} (m : Profile n) : ℕ :=
  2 * ((profileList m).sum + n ^ 3) + 1

/-- The ideal killed-chain factor from the forced count `N₁ = 1` to the
first stored profile coordinate `m₂`.  It is not part of `profileWeight`. -/
def firstProfileTransitionMass {n : ℕ} (hn : 2 ≤ n) (m : Profile n) : ℝ :=
  transitionMass 1 (m ⟨0, by omega⟩)

/-- Under the chosen HLOZ window, the omitted first transition has a fixed
explicit lower bound.  The index `2` entry is at most `3 * 2² = 12`. -/
theorem one_div_8192_le_firstProfileTransitionMass
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} (hdelta : delta ≤ 1)
    {m : Profile n} (hm : IsConstrainedProfile delta m) :
    (1 / 8192 : ℝ) ≤ firstProfileTransitionMass hn m := by
  let i : Fin (n - 1) := ⟨0, by omega⟩
  have hscale : scaleIndex i = 2 := by simp [i, scaleIndex]
  have hmBound : m i ≤ 12 := by
    have h := inProfileWindow_le_three_mul_sq hdelta
      (show 1 ≤ scaleIndex i by simp [scaleIndex]) (hm i)
    rw [hscale] at h
    norm_num at h ⊢
    exact h
  have hpow : (2 : ℝ) ^ (m i + 1) ≤ 8192 := by
    calc
      (2 : ℝ) ^ (m i + 1) ≤ 2 ^ (13 : ℕ) := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 8192 := by norm_num
  have hpowPos : 0 < (2 : ℝ) ^ (m i + 1) := by positivity
  rw [firstProfileTransitionMass, transitionMass_formula (by omega)]
  have hi : m ⟨0, by omega⟩ = m i := rfl
  rw [hi]
  rw [show 1 + m i - 1 = m i by omega, Nat.choose_self]
  norm_num only [Nat.cast_one, one_div, one_mul]
  simpa [div_eq_mul_inv, Nat.add_comm] using inv_anti₀ hpowPos hpow

/-- Internal profile and terminal-window predicate on a bounded literal
radial-label word. -/
def IsFixedProfileRadialWord
    (n : ℕ) (delta : ℝ) (m : Profile n)
    (word : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n)) : Prop :=
  (∀ i : Fin (n - 1),
      radialUpcrossingCount word.2
        ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i) ∧
    terminalLower n delta ≤
      (radialUpcrossingCount word.2 ⟨n + 1, by omega⟩ : ℝ) ∧
    radialUpcrossingCount word.2 ⟨n + 1, by omega⟩ ≤ n ^ 3

/-- The fixed-profile predicate with an arbitrary ambient finite cutoff. -/
def IsFixedProfileRadialWordWithCutoff
    (n cutoff : ℕ) (delta : ℝ) (m : Profile n)
    (word : BoundedRadialLabelWord n cutoff) : Prop :=
  (∀ i : Fin (n - 1),
      radialUpcrossingCount word.2
        ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i) ∧
    terminalLower n delta ≤
      (radialUpcrossingCount word.2 ⟨n + 1, by omega⟩ : ℝ) ∧
    radialUpcrossingCount word.2 ⟨n + 1, by omega⟩ ≤ n ^ 3

/-- Union of all chronological radial words realizing one fixed profile,
using its own exact finite transition cutoff. -/
def exactFixedProfileRadialWordFamilyAtom
    (n : ℕ) (delta : ℝ) (center start : Point) (m : Profile n) :
    Set StepPath :=
  radialLabelWordFamilyAtom n (exactProfileRadialWordMaxTransitions m)
    center start
    (IsFixedProfileRadialWordWithCutoff n
      (exactProfileRadialWordMaxTransitions m) delta m)

theorem measurableSet_exactFixedProfileRadialWordFamilyAtom
    (n : ℕ) (delta : ℝ) (center start : Point) (m : Profile n) :
    MeasurableSet
      (exactFixedProfileRadialWordFamilyAtom n delta center start m) := by
  exact measurableSet_radialLabelWordFamilyAtom _ _ _ _ _

theorem fairSteps_exactFixedProfileRadialWordFamilyAtom
    (n : ℕ) (delta : ℝ) (center start : Point) (m : Profile n) :
    fairSteps (exactFixedProfileRadialWordFamilyAtom n delta center start m) =
      ∑ word : {word : BoundedRadialLabelWord n
          (exactProfileRadialWordMaxTransitions m) //
          IsFixedProfileRadialWordWithCutoff n
            (exactProfileRadialWordMaxTransitions m) delta m word},
        fairSteps (boundedRadialLabelWordAtom n
          (exactProfileRadialWordMaxTransitions m) center start word.1) := by
  exact fairSteps_radialLabelWordFamilyAtom _ _ _ _ _

/-- Union of all bounded chronological radial words realizing one fixed
internal profile and the literal successful terminal window. -/
def fixedProfileRadialWordFamilyAtom
    (n : ℕ) (delta : ℝ) (center start : Point) (m : Profile n) :
    Set StepPath :=
  radialLabelWordFamilyAtom n (profileRadialWordMaxTransitions n) center start
    (IsFixedProfileRadialWord n delta m)

theorem measurableSet_fixedProfileRadialWordFamilyAtom
    (n : ℕ) (delta : ℝ) (center start : Point) (m : Profile n) :
    MeasurableSet (fixedProfileRadialWordFamilyAtom n delta center start m) := by
  exact measurableSet_radialLabelWordFamilyAtom _ _ _ _ _

/-- Exact disjoint finite-sum formula for the fixed-profile radial family. -/
theorem fairSteps_fixedProfileRadialWordFamilyAtom
    (n : ℕ) (delta : ℝ) (center start : Point) (m : Profile n) :
    fairSteps (fixedProfileRadialWordFamilyAtom n delta center start m) =
      ∑ word : {word : BoundedRadialLabelWord n
          (profileRadialWordMaxTransitions n) //
          IsFixedProfileRadialWord n delta m word},
        fairSteps (boundedRadialLabelWordAtom n
          (profileRadialWordMaxTransitions n) center start word.1) := by
  exact fairSteps_radialLabelWordFamilyAtom _ _ _ _ _

/-- A member of the fixed-profile word family has a literal first level-zero
hit whose every internal excursion coordinate equals `m` and whose terminal
coordinate lies in the successful window. -/
theorem profile_coordinates_of_mem_fixedProfileRadialWordFamilyAtom
    {n : ℕ} (hn : 2 ≤ n) {delta : ℝ} {center start : Point}
    {m : Profile n} {omega : StepPath}
    (homega : omega ∈
      fixedProfileRadialWordFamilyAtom n delta center start m) :
    ∃ horizon : ℕ,
      AbsoluteBoundaryFirstAt (radialBoundary n center ⟨0, by omega⟩)
        start omega horizon ∧
      (∀ i : Fin (n - 1),
        excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center
            ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i) ∧
      terminalLower n delta ≤
        (excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center ⟨n + 1, by omega⟩ : ℝ) ∧
      excursionProfile (fun q ↦ trajectoryFrom start omega q)
          n horizon center ⟨n + 1, by omega⟩ ≤ n ^ 3 := by
  obtain ⟨word, hword, hmem⟩ :=
    (mem_radialLabelWordFamilyAtom_iff _ _ _ _ _ _).mp homega
  obtain ⟨horizon, hfirst, htrace⟩ :=
    (mem_radialLabelWordAtom_iff n word.1 center start word.2 omega).mp hmem
  refine ⟨horizon, hfirst, ?_, ?_, ?_⟩
  · intro i
    let k : Fin (n + 2) :=
      ⟨scaleIndex i, by unfold scaleIndex; omega⟩
    have hk2 : 2 ≤ (k : ℕ) := by simp [k, scaleIndex]
    have hcompleted := radialWordCompletedCount_eq_excursionProfile_of_trace
      hn (by omega : 0 < (k : ℕ)) k.2 center _ word.2 htrace
    have hscan := radialWordCompletedCount_eq_radialUpcrossingCount word.2 k hk2
    have hfixed := hword.1 i
    exact hcompleted.symm.trans (hscan.trans hfixed)
  · let k : Fin (n + 2) := ⟨n + 1, by omega⟩
    have hcompleted := radialWordCompletedCount_eq_excursionProfile_of_trace
      hn (by change 0 < n + 1; omega) k.2 center _ word.2 htrace
    have hscan := radialWordCompletedCount_eq_radialUpcrossingCount word.2 k
      (by change 2 ≤ n + 1; omega)
    rw [← hcompleted, hscan]
    exact hword.2.1
  · let k : Fin (n + 2) := ⟨n + 1, by omega⟩
    have hcompleted := radialWordCompletedCount_eq_excursionProfile_of_trace
      hn (by change 0 < n + 1; omega) k.2 center _ word.2 htrace
    have hscan := radialWordCompletedCount_eq_radialUpcrossingCount word.2 k
      (by change 2 ≤ n + 1; omega)
    rw [← hcompleted, hscan]
    exact hword.2.2

end

end Erdos1165.AnnularRadialProfileWords
