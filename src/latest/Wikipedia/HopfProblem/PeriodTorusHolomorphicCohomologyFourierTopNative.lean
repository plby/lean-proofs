import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierTopSolver
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarNative

/-!
# The top-degree Fourier potential in the actual period coordinates

The constructed torus potential is lifted through the original real
period equivalence.  Its two components are smooth and periodic under
the actual period lattice.  Their actual coordinate Dolbeault row is
the prescribed coefficient minus its genuine probability Haar mean.
Both potential components have zero mean.  No closedness hypothesis is
required for a top-degree coefficient.
-/

noncomputable section

open MeasureTheory UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierTop

open PeriodTorusLineBundleClassification

/-- The two constructed functions in the original complex period coordinates. -/
def liftedPotential (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (i : Fin 2) : ComplexPlane₂ → ℂ :=
  periodTorusLift p (potential p h i)

theorem liftedPotential_smooth (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (i : Fin 2) : ContDiff ℝ ∞ (liftedPotential p h i) :=
  contDiff_periodTorusLift p (potential p h i)

/-- Periodicity is with respect to the original period lattice, not an auxiliary lattice. -/
theorem liftedPotential_add_lattice (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (i : Fin 2) (z : ComplexPlane₂) (l : p.lattice) :
    liftedPotential p h i (z + l) = liftedPotential p h i z :=
  periodTorusLift_add_lattice p (potential p h i) z l l.property

/-- The actual coordinate antiholomorphic derivatives satisfy the signed top-degree row. -/
theorem liftedPotential_equation (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (z : ComplexPlane₂) :
    dbarCoordinate (liftedPotential p h 1) 0 z -
        dbarCoordinate (liftedPotential p h 0) 1 z =
      periodTorusLift p h z - torusFourierMean h := by
  change dbarCoordinate (periodTorusLift p (potential p h 1)) 0 z -
      dbarCoordinate (periodTorusLift p (potential p h 0)) 1 z = _
  rw [dbarCoordinate_periodTorusLift, dbarCoordinate_periodTorusLift]
  simp only [periodTorusLift_apply]
  exact potential_equation p h _

/-- Descending the actual lifted functions recovers the original constructed torus components. -/
theorem liftedPotential_descend_apply (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (i : Fin 2) (t : UnitAddTorus (Fin 4)) :
    smoothTorusOfLatticePeriodic p (liftedPotential p h i)
      (liftedPotential_smooth p h i) (liftedPotential_add_lattice p h i) t =
        potential p h i t :=
  smoothTorusOfLatticePeriodic_periodTorusLift_apply p (potential p h i)
    (liftedPotential_smooth p h i) (liftedPotential_add_lattice p h i) t

/-- Each actual descended component has zero Fourier mean. -/
theorem liftedPotential_mean (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (i : Fin 2) :
    torusFourierMean (smoothTorusOfLatticePeriodic p (liftedPotential p h i)
      (liftedPotential_smooth p h i) (liftedPotential_add_lattice p h i)) = 0 :=
  (torusFourierMean_smoothTorusOfLatticePeriodic_periodTorusLift p (potential p h i)
    (liftedPotential_smooth p h i) (liftedPotential_add_lattice p h i)).trans
      (potential_mean p h i)

/-- The normalization is the genuine product probability Haar integral. -/
theorem liftedPotential_haarMean (p : PeriodDomain) (h : SmoothTorusFunction (Fin 4))
    (i : Fin 2) :
    (∫ t : UnitAddTorus (Fin 4),
      smoothTorusOfLatticePeriodic p (liftedPotential p h i)
        (liftedPotential_smooth p h i) (liftedPotential_add_lattice p h i) t
      ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle)) = 0 :=
  (torusFourierMean_eq_haarIntegral _).symm.trans (liftedPotential_mean p h i)

/-- The potential for any smooth function periodic under the actual period lattice. -/
def periodicPotential (p : PeriodDomain) (f : ComplexPlane₂ → ℂ)
    (hf : ContDiff ℝ ∞ f)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (i : Fin 2) : ComplexPlane₂ → ℂ :=
  liftedPotential p (smoothTorusOfLatticePeriodic p f hf hpf) i

theorem periodicPotential_smooth (p : PeriodDomain) (f : ComplexPlane₂ → ℂ)
    (hf : ContDiff ℝ ∞ f)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (i : Fin 2) : ContDiff ℝ ∞ (periodicPotential p f hf hpf i) :=
  liftedPotential_smooth p (smoothTorusOfLatticePeriodic p f hf hpf) i

theorem periodicPotential_add_lattice (p : PeriodDomain) (f : ComplexPlane₂ → ℂ)
    (hf : ContDiff ℝ ∞ f)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (i : Fin 2) (z : ComplexPlane₂) (l : p.lattice) :
    periodicPotential p f hf hpf i (z + l) = periodicPotential p f hf hpf i z :=
  liftedPotential_add_lattice p (smoothTorusOfLatticePeriodic p f hf hpf) i z l

/-- The exact original function is recovered after subtracting its actual descended mean. -/
theorem periodicPotential_equation (p : PeriodDomain) (f : ComplexPlane₂ → ℂ)
    (hf : ContDiff ℝ ∞ f)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (z : ComplexPlane₂) :
    dbarCoordinate (periodicPotential p f hf hpf 1) 0 z -
        dbarCoordinate (periodicPotential p f hf hpf 0) 1 z =
      f z - torusFourierMean (smoothTorusOfLatticePeriodic p f hf hpf) := by
  simpa only [periodicPotential, periodTorusLift_smoothTorusOfLatticePeriodic] using
    liftedPotential_equation p (smoothTorusOfLatticePeriodic p f hf hpf) z

theorem periodicPotential_mean (p : PeriodDomain) (f : ComplexPlane₂ → ℂ)
    (hf : ContDiff ℝ ∞ f)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (i : Fin 2) :
    torusFourierMean (smoothTorusOfLatticePeriodic p (periodicPotential p f hf hpf i)
      (periodicPotential_smooth p f hf hpf i)
      (periodicPotential_add_lattice p f hf hpf i)) = 0 :=
  liftedPotential_mean p (smoothTorusOfLatticePeriodic p f hf hpf) i

theorem periodicPotential_haarMean (p : PeriodDomain) (f : ComplexPlane₂ → ℂ)
    (hf : ContDiff ℝ ∞ f)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (i : Fin 2) :
    (∫ t : UnitAddTorus (Fin 4),
      smoothTorusOfLatticePeriodic p (periodicPotential p f hf hpf i)
        (periodicPotential_smooth p f hf hpf i)
        (periodicPotential_add_lattice p f hf hpf i) t
      ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle)) = 0 :=
  liftedPotential_haarMean p (smoothTorusOfLatticePeriodic p f hf hpf) i

/-- Every actual smooth lattice-periodic top coefficient has a normalized periodic potential. -/
theorem exists_normalized_periodic_potential (p : PeriodDomain) (f : ComplexPlane₂ → ℂ)
    (hf : ContDiff ℝ ∞ f)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z) :
    ∃ (u : Fin 2 → ComplexPlane₂ → ℂ) (hu : ∀ i, ContDiff ℝ ∞ (u i))
      (hpu : ∀ i, ∀ z : ComplexPlane₂, ∀ l : p.lattice, u i (z + l) = u i z),
      (∀ i, torusFourierMean (smoothTorusOfLatticePeriodic p (u i) (hu i) (hpu i)) = 0) ∧
      ∀ z, dbarCoordinate (u 1) 0 z - dbarCoordinate (u 0) 1 z =
        f z - torusFourierMean (smoothTorusOfLatticePeriodic p f hf hpf) :=
  ⟨periodicPotential p f hf hpf, periodicPotential_smooth p f hf hpf,
    periodicPotential_add_lattice p f hf hpf, periodicPotential_mean p f hf hpf,
    periodicPotential_equation p f hf hpf⟩

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierTop
