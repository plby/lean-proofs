import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierTopNative

/-!
# The normalized top-degree Dolbeault solver for every period torus

The top differential uses the actual torus Dolbeault derivatives.  At every
nonzero integer frequency its actual symbol has a proved controlled right
inverse; the symbol gap proves rapid decay, and smooth Fourier synthesis
constructs two zero-Haar-mean potentials.  Fourier reconstruction proves the
exact differential equation with only the actual Haar mean removed.

The native-coordinate results lift these potentials to `ComplexPlane₂`,
prove periodicity under the original period lattice, and identify their
literal `dbarCoordinate` differential.  Every actual smooth lattice-periodic
top coefficient is covered, without a closedness or solvability hypothesis.
-/
