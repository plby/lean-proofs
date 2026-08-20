import Mathlib

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos783

def PairwiseCoprime (A : Finset ℕ) : Prop :=
  Set.Pairwise (A : Set ℕ) Nat.Coprime

@[simp] lemma pairwiseCoprime_empty : PairwiseCoprime ∅ := by
  simp [PairwiseCoprime]

end Erdos783

namespace Erdos783

def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (a : ℝ)⁻¹

@[simp] lemma reciprocalMass_empty : reciprocalMass ∅ = 0 := by
  simp [reciprocalMass]

end Erdos783

namespace Erdos783

def Admissible (C : ℝ) (N : ℕ) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.Icc 2 N ∧ PairwiseCoprime A ∧ reciprocalMass A ≤ C

lemma admissible_empty {C : ℝ} (hC : 0 ≤ C) (N : ℕ) :
    Admissible C N ∅ := by
  exact ⟨by simp, pairwiseCoprime_empty, by simpa using hC⟩

end Erdos783

namespace Erdos783

def admissibleFamily (C : ℝ) (N : ℕ) : Finset (Finset ℕ) :=
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

end Erdos783

namespace Erdos783

def unsieved (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => ∀ a ∈ A, ¬a ∣ n

end Erdos783

namespace Erdos783

def sieveDensity (N : ℕ) (A : Finset ℕ) : ℝ :=
  (unsieved N A).card / (N : ℝ)

end Erdos783

namespace Erdos783

def minimumDensity (C : ℝ) (N : ℕ) : ℝ :=
  if hC : 0 ≤ C then
    ((admissibleFamily C N).image (sieveDensity N)).min'
      ((admissibleFamily_nonempty hC N).image (sieveDensity N))
  else 0

end Erdos783

namespace Erdos783

def AsymptoticResolution (ρ : ℝ → ℝ) : Prop :=
  ∀ C : ℝ, 0 < C →
    Tendsto (minimumDensity C) atTop (nhds (ρ (Real.exp C)))

end Erdos783

namespace Erdos390

def poissonDickmanScaledUniformDensity
    (c u : ℝ) : ℝ≥0∞ :=
  (Ioc (0 : ℝ) c).indicator
    (fun _ ↦ ENNReal.ofReal c⁻¹) u

end Erdos390

namespace Erdos390

abbrev PoissonDickmanConfiguration := ℕ → ℝ

end Erdos390

namespace Erdos390

abbrev PoissonDickmanGapSequence := ℕ → ℝ

end Erdos390

namespace Erdos390

def poissonDickmanGapLaw : Measure PoissonDickmanGapSequence :=
  Measure.infinitePi fun _ : ℕ ↦ expMeasure 1

end Erdos390

namespace Erdos390

def poissonDickmanArrival
    (e : PoissonDickmanGapSequence) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), max (e k) 0

end Erdos390

namespace Erdos390

def poissonDickmanSpacingConfiguration
    (e : PoissonDickmanGapSequence) :
    PoissonDickmanConfiguration :=
  fun n ↦ Real.exp (-poissonDickmanArrival e n)

end Erdos390

namespace Erdos390

def poissonDickmanUnconditionedLaw :
    Measure PoissonDickmanConfiguration :=
  poissonDickmanGapLaw.map
    poissonDickmanSpacingConfiguration

end Erdos390

namespace Erdos390

def poissonDickmanTotalMass
    (π : PoissonDickmanConfiguration) : ℝ :=
  ∑' n : ℕ, π n

end Erdos390

namespace Erdos390

def poissonDickmanTotalMassLaw : Measure ℝ :=
  poissonDickmanUnconditionedLaw.map
    poissonDickmanTotalMass

end Erdos390

namespace Erdos390

def poissonDickmanTotalDensityFormula
    (u : ℝ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ,
    poissonDickmanScaledUniformDensity (1 + t) u
    ∂poissonDickmanTotalMassLaw

end Erdos390

namespace Erdos390

def poissonDickmanTotalDensityReal (u : ℝ) : ℝ :=
  (poissonDickmanTotalDensityFormula u).toReal

end Erdos390

namespace Erdos390

def poissonDickmanDensityNormalizer : ℝ≥0∞ :=
  ∫⁻ t : ℝ,
    ENNReal.ofReal (1 + t)⁻¹
    ∂poissonDickmanTotalMassLaw

end Erdos390

namespace Erdos390

def poissonDickmanDensityNormalizerReal : ℝ :=
  poissonDickmanDensityNormalizer.toReal

end Erdos390

namespace Erdos390

def poissonDickmanProfile (u : ℝ) : ℝ :=
  if u = 0 then 1
  else
    poissonDickmanTotalDensityReal u /
      poissonDickmanDensityNormalizerReal

end Erdos390

namespace Erdos783

def dickmanRho : ℝ → ℝ :=
  Erdos390.poissonDickmanProfile

end Erdos783

namespace Erdos783

theorem erdos_783 : AsymptoticResolution dickmanRho := by
  sorry

end Erdos783

end
