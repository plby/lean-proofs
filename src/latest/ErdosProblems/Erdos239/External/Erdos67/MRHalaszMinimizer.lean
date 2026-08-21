import ErdosProblems.Erdos239.External.Erdos67.MRHalaszNearMediumEnergy

/-!
# A minimizing Archimedean frequency

The squared pretentious distance is a finite continuous function of the
Archimedean frequency.  Consequently it attains its minimum on every
compact frequency interval.  This is the compactness step used when the
near and medium vertical ranges in the Halasz argument are centered at a
minimizing frequency.
-/

open scoped BigOperators ComplexConjugate
open Set

namespace Erdos67

noncomputable section

/-- The Archimedean character at a positive natural number depends
continuously on its real frequency. -/
theorem continuous_archimedeanTwist_of_pos {n : ℕ} (hn : 0 < n) :
    Continuous (fun t : ℝ ↦ archimedeanTwist t n) := by
  have hphase : Continuous (logarithmicPhase n) := by
    unfold logarithmicPhase
    fun_prop
  convert hphase using 1
  funext t
  exact (logarithmicPhase_eq_archimedeanTwist hn t).symm

/-- The finite squared pretentious distance to `n ↦ n^(it)` is a
continuous real-valued function of `t`. -/
theorem continuous_pretentiousDistSq_archimedeanTwist
    (f : ℕ → ℂ) (X : ℕ) :
    Continuous (fun t : ℝ ↦
      pretentiousDistSq f (archimedeanTwist t) X) := by
  unfold pretentiousDistSq pretentiousTerm
  apply continuous_finsetSum
  intro p hp
  have hpPrime : p.Prime := (mem_primesUpTo.mp hp).1
  have htwist : Continuous (fun t : ℝ ↦ archimedeanTwist t p) :=
    continuous_archimedeanTwist_of_pos hpPrime.pos
  fun_prop

/-- On a symmetric compact interval, the finite Archimedean pretentious
distance has an actual minimizing frequency. -/
theorem exists_pretentiousDistSq_archimedean_minimizer
    (f : ℕ → ℂ) (X : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ∃ t₀ ∈ Set.Icc (-T) T, ∀ t ∈ Set.Icc (-T) T,
      pretentiousDistSq f (archimedeanTwist t₀) X ≤
        pretentiousDistSq f (archimedeanTwist t) X := by
  have hcompact : IsCompact (Set.Icc (-T) T) := isCompact_Icc
  have hnonempty : (Set.Icc (-T) T).Nonempty := by
    exact ⟨0, by constructor <;> linarith⟩
  exact hcompact.exists_isMinOn hnonempty
    (continuous_pretentiousDistSq_archimedeanTwist f X).continuousOn

/-- A minimizer on the natural MR frequency window inherits the prescribed
nonpretentious lower bound. -/
theorem exists_pretentiousDistSq_archimedean_minimizer_ge
    {f : ℕ → ℂ} {A X : ℕ}
    (hnonpret : MRArchimedeanNonpretentious f A X) :
    ∃ t₀ : ℝ, |t₀| ≤ X ∧
      (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t₀) X ∧
      ∀ t : ℝ, |t| ≤ X →
        pretentiousDistSq f (archimedeanTwist t₀) X ≤
          pretentiousDistSq f (archimedeanTwist t) X := by
  obtain ⟨t₀, ht₀, hmin⟩ :=
    exists_pretentiousDistSq_archimedean_minimizer f X
      (show (0 : ℝ) ≤ X by positivity)
  have habs₀ : |t₀| ≤ X := abs_le.mpr ⟨ht₀.1, ht₀.2⟩
  refine ⟨t₀, habs₀, hnonpret t₀ habs₀, ?_⟩
  intro t ht
  exact hmin t (abs_le.mp ht)

/-- Ready-to-use minimizing-frequency package, including the uniform
conversion of the attained Halasz error to the prescribed MRArch
threshold. -/
theorem exists_pretentiousDistSq_archimedean_minimizer_error_le
    {f : ℕ → ℂ} {A X : ℕ}
    (hnonpret : MRArchimedeanNonpretentious f A X) :
    ∃ t₀ M : ℝ, |t₀| ≤ X ∧
      M = pretentiousDistSq f (archimedeanTwist t₀) X ∧
      (A : ℝ) ≤ M ∧
      (∀ t : ℝ, |t| ≤ X →
        M ≤ pretentiousDistSq f (archimedeanTwist t) X) ∧
      (M + 1) * Real.exp (-M) ≤
        2 * ((A : ℝ) + 1) * Real.exp (-(1 / 2 : ℝ) * A) := by
  obtain ⟨t₀, ht₀, hA, hmin⟩ :=
    exists_pretentiousDistSq_archimedean_minimizer_ge hnonpret
  let M := pretentiousDistSq f (archimedeanTwist t₀) X
  refine ⟨t₀, M, ht₀, rfl, hA, hmin, ?_⟩
  exact halaszError_le_two_mul_archimedeanError
    (by positivity : (0 : ℝ) ≤ A) hA

end

end Erdos67
