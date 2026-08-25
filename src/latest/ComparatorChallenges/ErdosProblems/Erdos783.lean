/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos783

def PairwiseCoprime (A : Finset ℕ) : Prop :=
  Set.Pairwise (A : Set ℕ) Nat.Coprime

lemma pairwiseCoprime_empty : PairwiseCoprime ∅ := by
  simp [PairwiseCoprime]

noncomputable def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (a : ℝ)⁻¹

lemma reciprocalMass_empty : reciprocalMass ∅ = 0 := by
  simp [reciprocalMass]

def Admissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 N ∧ PairwiseCoprime A ∧ reciprocalMass A ≤ C

lemma admissible_empty {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    Admissible C N ∅ := by
  exact ⟨by simp, pairwiseCoprime_empty, by simpa only [reciprocalMass_empty] using hC⟩

open scoped Classical in
noncomputable def admissibleFamily (C : ℝ) (N : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 2 N).powerset.filter (Admissible C N)

lemma mem_admissibleFamily {C : ℝ} {N : ℕ} {A : Finset ℕ} :
    A ∈ admissibleFamily C N ↔ Admissible C N A := by
  classical
  simp only [admissibleFamily, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h.1, h⟩

lemma admissibleFamily_nonempty {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    (admissibleFamily C N).Nonempty := by
  exact ⟨∅, mem_admissibleFamily.mpr (admissible_empty hC N)⟩

def unsieved (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => ∀ a ∈ A, ¬a ∣ n

noncomputable def sieveDensity (N : ℕ) (A : Finset ℕ) : ℝ :=
  (unsieved N A).card / (N : ℝ)

noncomputable def minimumDensity (C : ℝ) (N : ℕ) : ℝ :=
  if hC : 0 ≤ C then
    ((admissibleFamily C N).image (sieveDensity N)).min'
      ((admissibleFamily_nonempty hC N).image (sieveDensity N))
  else 0

def AsymptoticResolution (ρ : ℝ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C →
    Tendsto (minimumDensity C) atTop (nhds (ρ (Real.exp C)))

end Erdos783

namespace Erdos390

noncomputable def poissonDickmanScaledUniformDensity
    (c u : ℝ) : ℝ≥0∞ :=
  (Ioc (0 : ℝ) c).indicator
    (fun _ ↦ ENNReal.ofReal c⁻¹) u

abbrev PoissonDickmanConfiguration := ℕ → ℝ

abbrev PoissonDickmanGapSequence := ℕ → ℝ

noncomputable def poissonDickmanGapLaw : Measure PoissonDickmanGapSequence :=
  Measure.infinitePi fun _ : ℕ ↦ expMeasure 1

def poissonDickmanArrival
    (e : PoissonDickmanGapSequence) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), max (e k) 0

noncomputable def poissonDickmanSpacingConfiguration
    (e : PoissonDickmanGapSequence) :
    PoissonDickmanConfiguration :=
  fun n ↦ Real.exp (-poissonDickmanArrival e n)

noncomputable def poissonDickmanUnconditionedLaw :
    Measure PoissonDickmanConfiguration :=
  poissonDickmanGapLaw.map
    poissonDickmanSpacingConfiguration

noncomputable def poissonDickmanTotalMass
    (π : PoissonDickmanConfiguration) : ℝ :=
  ∑' n : ℕ, π n

noncomputable def poissonDickmanTotalMassLaw : Measure ℝ :=
  poissonDickmanUnconditionedLaw.map
    poissonDickmanTotalMass

noncomputable def poissonDickmanTotalDensityFormula
    (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ,
    poissonDickmanScaledUniformDensity (1 + t) u
    ∂poissonDickmanTotalMassLaw

noncomputable def poissonDickmanTotalDensityReal (u : ℝ) : ℝ :=
  (poissonDickmanTotalDensityFormula u).toReal

noncomputable def poissonDickmanDensityNormalizer : ℝ≥0∞ :=
  ∫⁻ t : ℝ,
    ENNReal.ofReal (1 + t)⁻¹
    ∂poissonDickmanTotalMassLaw

noncomputable def poissonDickmanDensityNormalizerReal : ℝ :=
  poissonDickmanDensityNormalizer.toReal

noncomputable def poissonDickmanProfile (u : ℝ) : ℝ :=
  if u = 0 then 1
  else
    poissonDickmanTotalDensityReal u /
      poissonDickmanDensityNormalizerReal

end Erdos390

namespace Erdos783

noncomputable def dickmanRho : ℝ → ℝ :=
  Erdos390.poissonDickmanProfile

theorem erdos_783 : AsymptoticResolution dickmanRho := by
  sorry

end Erdos783
