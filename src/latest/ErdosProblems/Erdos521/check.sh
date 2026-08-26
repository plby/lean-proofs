#!/usr/bin/env bash
# Run from src/latest with: lake env bash ErdosProblems/Erdos521/check.sh
# This checks every supporting module and the unconditional disproof.
set -eu

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."
export LEAN_PATH="$PWD/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}"

mkdir -p .lake/build/lib/lean/ErdosProblems/Erdos521
mkdir -p .lake/build/lib/lean/ErdosProblems/Erdos1165
lean -o .lake/build/lib/lean/ErdosProblems/Erdos1165/SecondMoment.olean \
  ErdosProblems/Erdos1165/SecondMoment.lean

for erdos521_module in \
  Abel Records Model ZeroOne RecordProbability SecondMoment \
  Pitman BridgeCounts ConeSurvival CoefficientProbability \
  InteriorBounds RootStatistics GeometricVariance Characteristic \
  GaussianSmoothing SmallBall Moments Maximal MaximalMoment \
  ComplexMaximal PolynomialDisk CircularMaximal JensenDisk \
  LocalRootBounds CenterChanges LocalMaximal \
  EndpointScale Decay EndpointTerms EndpointProbability EndpointAlmostSure \
  EndpointCover EndpointBounds EndpointLimit SignSymmetry \
  SeparatedSigns FiniteSigns SmallBallAddition LacunarySums LacunaryScale RepulsionSmallBall \
  PolynomialDerivatives IntervalGrid RepulsionParameters RepulsionGrid \
  RepulsionScale RootRepulsion AlmostSureRepulsion \
  RootSeparation RootTransfer RootPairing BulkComparison PolynomialTails BulkParameters BulkStability \
  InteriorDecomposition InteriorStability DyadicInterpolation \
  IntervalSquare TwoRoots DerivativeMoments DerivativeEnergy TwoRootProbability \
  ComplexMoments CircleMoments SingleLocalRoots LocalVariance NormalizedSmallBall NormalizedLocalRoots \
  NormalizedTwoRoots SignChanges SignGrid SignGridProbability \
  ProductDifference CharacteristicComparison TriangularComparison WeightedCentralLimit \
  VarianceLimits ValueCentralLimit VectorCentralLimit SignGridLowerBound \
  ScaleLimits CovarianceLimits CorrelationLimits \
  LocalTailParameters LocalTailFrequency LocalSmallVariance LocalRootTail LocalTailDecay \
  NatTailMoments TailMomentIntegral LocalMomentSeries LocalMomentBound MomentCutoff UniformLocalMoments \
  RareEventMoments GaussianPair PairWeights PairCentralLimit NormalizedWeights ValuePairLimit \
  GaussianPairBoundary PairSignLimit PolynomialSignProbability GaussianAbsoluteMoment \
  GaussianIntervals GaussianIntervalSlope GaussianLinearMaps GaussianSignSections GaussianProduct \
  GaussianFlipIntegral LogGaussianParameters LogGaussianSlope GaussianSignSlope IntervalMoments \
  NatComparisonError SignGridExpectation RootGridError SmallBallLimits TwoRootLimits \
  LogGrid LogGridExpectation AsymptoticBounds LogGridScale LogGridProbabilities \
  SimpleRootProbability LogGridDisagreement BoundedConcentration DyadicWindows WindowIndependence \
  RefinementSpacing RefinementPowers RefinementError ApproximationLimits RefinedGridEndpoints \
  LogIntervalMoments LocalMeanLimit IntervalPartition PartitionExpectation LogGridPartition LogarithmicMean \
  UniformLimitCriterion BulkDegreeRatio UniformLogarithmicMean PartitionMoments LogarithmicMoments \
  WindowSums SignPerturbation WindowVariance WindowGrid DyadicIntervals WindowGridIndependence WindowError \
  TriangularMeans SqrtScales MainBins MainBinBulk MainBinMean IcoPartitionExpectation WindowGridMoments \
  CentralIntervalMean BlockConcentration WindowScales ColoredWindows BoundedSumMGF ResidueSums \
  ColoredConcentration RelativeIntervalMoments ClampedDyadicGrid IcoPartitionMoments SummableDeviations \
  CentralIntervalMoments FourthMomentNegligible LeftTrim RightTrimGeometry RightTrim WindowCapBounds \
  CappedCentralSum WindowConcentrationScale WindowAlmostSureConcentration AffineGrid DyadicFineGrid \
  DyadicWindowGeometry DyadicWindowError WindowScaleGrowth MainBinVariance FineGridPowers FineGridSmallBall \
  FineGridTwoRoots FineGridRootError MainWindowGeometry MainWindowValueError MainWindowMoments FineGridCapping \
  FineErrorPowers FineGridWindowError FineGridCoarseErrors CappedCentralNat IcoRootPartition \
  DisagreementProbability BinCappedError CentralStatistics CentralComparisonCover CentralComparisonProbability \
  NatExpectationError CentralExpectationTransfer CentralStrongLaw PositiveDyadicStrongLaw InteriorStrongLaw \
  ReversalLaw ReversalRoots ReversalConvergence RootLiminf RootSubsequenceBounds RootLimsup \
  Oscillation ProbabilitySpaceTransfer
do
  lean -o ".lake/build/lib/lean/ErdosProblems/Erdos521/$erdos521_module.olean" \
    "ErdosProblems/Erdos521/$erdos521_module.lean"
done

lean -o .lake/build/lib/lean/ErdosProblems/Erdos521.olean ErdosProblems/Erdos521.lean
