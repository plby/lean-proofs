import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarSolver

/-!
# A constructed periodic primitive in the actual complex coordinates

Arbitrary smooth functions periodic under the actual period lattice descend
to the unit torus.  Their literal coordinate closedness gives the proved
Fourier compatibility, and the normalized torus potential lifts to a smooth
periodic function satisfying both actual coordinate Dolbeault equations.
-/

noncomputable section

open UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

theorem smoothTorusOfLatticePeriodic_periodTorusLift_apply (p : PeriodDomain)
    (f : SmoothTorusFunction (Fin 4))
    (hf : ContDiff ℝ ∞ (periodTorusLift p f))
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice,
      periodTorusLift p f (z + l) = periodTorusLift p f z)
    (t : UnitAddTorus (Fin 4)) :
    smoothTorusOfLatticePeriodic p (periodTorusLift p f) hf hpf t = f t := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  have h := periodTorusLift_smoothTorusOfLatticePeriodic p
    (periodTorusLift p f) hf hpf (PeriodTorusTypeOneOne.periodEquiv p x)
  simpa only [periodTorusLift_periodEquiv, torusLift, Function.comp_apply] using h

theorem torusFourierMean_smoothTorusOfLatticePeriodic_periodTorusLift
    (p : PeriodDomain) (f : SmoothTorusFunction (Fin 4))
    (hf : ContDiff ℝ ∞ (periodTorusLift p f))
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice,
      periodTorusLift p f (z + l) = periodTorusLift p f z) :
    torusFourierMean (smoothTorusOfLatticePeriodic p (periodTorusLift p f) hf hpf) =
      torusFourierMean f := by
  unfold torusFourierMean
  apply congrArg (fun F : UnitAddTorus (Fin 4) → ℂ => mFourierCoeff F 0)
  funext t
  exact smoothTorusOfLatticePeriodic_periodTorusLift_apply p f hf hpf t

theorem dbarCoordinate_periodTorusLift_torusDbarPotential (p : PeriodDomain)
    (a : Fin 2 → SmoothTorusFunction (Fin 4)) (ha : TorusDbarClosed p a)
    (i : Fin 2) (z : ComplexPlane₂) :
    dbarCoordinate (periodTorusLift p (torusDbarPotential p a)) i z =
      periodTorusLift p (a i) z - torusFourierMean (a i) := by
  rw [dbarCoordinate_periodTorusLift, periodTorusLift_apply,
    torusDbar_torusDbarPotential p a ha, periodTorusLift_apply]

/-- The actual smooth periodic function constructed from the given two
coefficient functions; neither a torus representative nor a solver is assumed. -/
def periodicDbarPotential (p : PeriodDomain)
    (f g : ComplexPlane₂ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (hpg : ∀ z : ComplexPlane₂, ∀ l : p.lattice, g (z + l) = g z) :
    ComplexPlane₂ → ℂ :=
  periodTorusLift p (torusDbarPotential p
    ![smoothTorusOfLatticePeriodic p f hf hpf,
      smoothTorusOfLatticePeriodic p g hg hpg])

theorem contDiff_periodicDbarPotential (p : PeriodDomain)
    (f g : ComplexPlane₂ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (hpg : ∀ z : ComplexPlane₂, ∀ l : p.lattice, g (z + l) = g z) :
    ContDiff ℝ ∞ (periodicDbarPotential p f g hf hg hpf hpg) :=
  contDiff_periodTorusLift p _

theorem periodicDbarPotential_add_lattice (p : PeriodDomain)
    (f g : ComplexPlane₂ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (hpg : ∀ z : ComplexPlane₂, ∀ l : p.lattice, g (z + l) = g z)
    (z : ComplexPlane₂) (l : p.lattice) :
    periodicDbarPotential p f g hf hg hpf hpg (z + l) =
      periodicDbarPotential p f g hf hg hpf hpg z :=
  periodTorusLift_add_lattice p _ z l l.property

theorem dbarCoordinate_periodicDbarPotential_zero (p : PeriodDomain)
    (f g : ComplexPlane₂ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (hpg : ∀ z : ComplexPlane₂, ∀ l : p.lattice, g (z + l) = g z)
    (hclosed : ∀ z, dbarCoordinate g 0 z = dbarCoordinate f 1 z)
    (z : ComplexPlane₂) :
    dbarCoordinate (periodicDbarPotential p f g hf hg hpf hpg) 0 z =
      f z - torusFourierMean (smoothTorusOfLatticePeriodic p f hf hpf) := by
  simpa only [periodicDbarPotential, Matrix.cons_val_zero,
    periodTorusLift_smoothTorusOfLatticePeriodic] using
    dbarCoordinate_periodTorusLift_torusDbarPotential p
      ![smoothTorusOfLatticePeriodic p f hf hpf,
        smoothTorusOfLatticePeriodic p g hg hpg]
      (torusDbarClosed_of_latticeClosed p f g hf hg hpf hpg hclosed) 0 z

theorem dbarCoordinate_periodicDbarPotential_one (p : PeriodDomain)
    (f g : ComplexPlane₂ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (hpg : ∀ z : ComplexPlane₂, ∀ l : p.lattice, g (z + l) = g z)
    (hclosed : ∀ z, dbarCoordinate g 0 z = dbarCoordinate f 1 z)
    (z : ComplexPlane₂) :
    dbarCoordinate (periodicDbarPotential p f g hf hg hpf hpg) 1 z =
      g z - torusFourierMean (smoothTorusOfLatticePeriodic p g hg hpg) := by
  simpa only [periodicDbarPotential, Matrix.cons_val_one, Matrix.cons_val_zero,
    periodTorusLift_smoothTorusOfLatticePeriodic] using
    dbarCoordinate_periodTorusLift_torusDbarPotential p
      ![smoothTorusOfLatticePeriodic p f hf hpf,
        smoothTorusOfLatticePeriodic p g hg hpg]
      (torusDbarClosed_of_latticeClosed p f g hf hg hpf hpg hclosed) 1 z

theorem torusFourierMean_periodicDbarPotential (p : PeriodDomain)
    (f g : ComplexPlane₂ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (hpg : ∀ z : ComplexPlane₂, ∀ l : p.lattice, g (z + l) = g z) :
    torusFourierMean (smoothTorusOfLatticePeriodic p
      (periodicDbarPotential p f g hf hg hpf hpg)
      (contDiff_periodicDbarPotential p f g hf hg hpf hpg)
      (periodicDbarPotential_add_lattice p f g hf hg hpf hpg)) = 0 := by
  exact (torusFourierMean_smoothTorusOfLatticePeriodic_periodTorusLift p
    (torusDbarPotential p ![smoothTorusOfLatticePeriodic p f hf hpf,
      smoothTorusOfLatticePeriodic p g hg hpg])
    (contDiff_periodTorusLift p _)
    (fun z l => periodTorusLift_add_lattice p _ z l l.property)).trans
      (torusFourierMean_torusDbarPotential p _)

/-- Arbitrary actual smooth closed lattice-periodic data admit a smooth
lattice-periodic primitive after subtracting their actual Haar means. -/
theorem exists_periodic_dbar_primitive (p : PeriodDomain)
    (f g : ComplexPlane₂ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (hpg : ∀ z : ComplexPlane₂, ∀ l : p.lattice, g (z + l) = g z)
    (hclosed : ∀ z, dbarCoordinate g 0 z = dbarCoordinate f 1 z) :
    ∃ u : ComplexPlane₂ → ℂ, ContDiff ℝ ∞ u ∧
      (∀ z : ComplexPlane₂, ∀ l : p.lattice, u (z + l) = u z) ∧
      (∀ z, dbarCoordinate u 0 z =
        f z - torusFourierMean (smoothTorusOfLatticePeriodic p f hf hpf)) ∧
      (∀ z, dbarCoordinate u 1 z =
        g z - torusFourierMean (smoothTorusOfLatticePeriodic p g hg hpg)) :=
  ⟨periodicDbarPotential p f g hf hg hpf hpg,
    contDiff_periodicDbarPotential p f g hf hg hpf hpg,
    periodicDbarPotential_add_lattice p f g hf hg hpf hpg,
    dbarCoordinate_periodicDbarPotential_zero p f g hf hg hpf hpg hclosed,
    dbarCoordinate_periodicDbarPotential_one p f g hf hg hpf hpg hclosed⟩

/-- The same constructed primitive is normalized by its genuine Haar mean. -/
theorem exists_normalized_periodic_dbar_primitive (p : PeriodDomain)
    (f g : ComplexPlane₂ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hpf : ∀ z : ComplexPlane₂, ∀ l : p.lattice, f (z + l) = f z)
    (hpg : ∀ z : ComplexPlane₂, ∀ l : p.lattice, g (z + l) = g z)
    (hclosed : ∀ z, dbarCoordinate g 0 z = dbarCoordinate f 1 z) :
    ∃ (u : ComplexPlane₂ → ℂ) (hu : ContDiff ℝ ∞ u)
      (hpu : ∀ z : ComplexPlane₂, ∀ l : p.lattice, u (z + l) = u z),
      torusFourierMean (smoothTorusOfLatticePeriodic p u hu hpu) = 0 ∧
      (∀ z, dbarCoordinate u 0 z =
        f z - torusFourierMean (smoothTorusOfLatticePeriodic p f hf hpf)) ∧
      (∀ z, dbarCoordinate u 1 z =
        g z - torusFourierMean (smoothTorusOfLatticePeriodic p g hg hpg)) :=
  ⟨periodicDbarPotential p f g hf hg hpf hpg,
    contDiff_periodicDbarPotential p f g hf hg hpf hpg,
    periodicDbarPotential_add_lattice p f g hf hg hpf hpg,
    torusFourierMean_periodicDbarPotential p f g hf hg hpf hpg,
    dbarCoordinate_periodicDbarPotential_zero p f g hf hg hpf hpg hclosed,
    dbarCoordinate_periodicDbarPotential_one p f g hf hg hpf hpg hclosed⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
