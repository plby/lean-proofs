/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Prop48XDirections
import ErdosProblems.Erdos1166.Erdos1166HLOZLemma410Prop48YColumns

/-!
# Canonically coded stopped atoms for HLOZ Lemma 4.10

The literal Proposition-4.8 interfaces previously asked the source to
enumerate a stopped-atom family by `ℕ` and separately prove its cover and
pairwise disjointness.  A natural-valued code makes those two facts formal
consequences.  It need not itself be measurable: only a code fibre which
actually meets the branch failure needs a measurable stopped source witness;
empty fibres are padded by a checked zero-mass atom.
-/

namespace Erdos1166.HLOZLemma410CodedAtoms

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

open HLOZPairing HLOZPairingProfiles HLOZProp47Prop45XRotations
open HLOZPairing.ScreeningBridge
open HLOZProp47Parameters HLOZProp47SourceObjects HLOZProp47SourceAssembly
open HLOZLemma410Prop48Connector HLOZLemma410Prop48XDirections
open HLOZLemma410Prop48YColumns HLOZColumnSourceConsumers
open HLOZBandRatios HLOZLemma411 HLOZLemma411Recursion HLOZLemma412Windows
open HLOZProp47Canonical
open HLOZProp47Lemma411412Connector HLOZProp47Lemma411412SourceAtoms
open HLOZLemma410SourceBands HLOZLemma410SourceAbsorption
open HLOZLemma410PotentialRace
open HLOZProp48Truncated HLOZProp48SourceBands
open HLOZEquation447

abbrev Path := ℕ → Site

/-- Fibre of a natural-valued stopped-data code. -/
def lemma410RawCodeFiber (rawCode : Path → ℕ) (eta : ℕ) : Set Path :=
  rawCode ⁻¹' {eta}

theorem lemma410RawCodeFiber_pairwise (rawCode : Path → ℕ) :
    Pairwise fun eta zeta ↦
      Disjoint (lemma410RawCodeFiber rawCode eta)
        (lemma410RawCodeFiber rawCode zeta) := by
  intro eta zeta hne
  rw [Set.disjoint_left]
  intro s hsEta hsZeta
  have he : rawCode s = eta := by
    simpa [lemma410RawCodeFiber] using hsEta
  have hz : rawCode s = zeta := by
    simpa [lemma410RawCodeFiber] using hsZeta
  exact hne (he.symm.trans hz)

theorem measurableSet_lemma410RawCodeFiber (rawCode : Path → ℕ)
    (hrawCode : Measurable rawCode) (eta : ℕ) :
    MeasurableSet (lemma410RawCodeFiber rawCode eta) :=
  (measurableSet_singleton eta).preimage hrawCode

theorem iUnion_lemma410RawCodeFiber (rawCode : Path → ℕ) :
    (⋃ eta, lemma410RawCodeFiber rawCode eta) = Set.univ := by
  ext s
  simp [lemma410RawCodeFiber]

/-- Codes whose fibre actually meets a specified branch failure on the
genuine full-walk support.  Abstract paths outside the image of increment
space have zero law, and no literal stopped source atom can contain them. -/
def FailureCode (failure : Set Path) (rawCode : Path → ℕ) :=
  {eta : ℕ //
    ((failure ∩ HLOZSourceInstantiation.simpleRandomWalkSupport) ∩
      lemma410RawCodeFiber rawCode eta).Nonempty}

instance (failure : Set Path) (rawCode : Path → ℕ) :
    Countable (FailureCode failure rawCode) :=
  Subtype.val_injective.countable

/-! ### Canonical coding of a disjoint countable atom family

The source decomposition is naturally presented as a countable disjoint
family of stopped atoms.  A natural-valued code should be derived from that
family, not supplied as additional mathematical data.  We use the least atom
index containing a path and reserve code `0` for paths outside the union.
Pairwise disjointness then makes the least-index choice immaterial and proves
that every positive code fibre is exactly the corresponding atom. -/

/-- Least index of an atom containing `s`, with an irrelevant fallback value
outside the union. -/
noncomputable def firstDisjointAtomIndex
    (atom : ℕ → Set Path) (s : Path) : ℕ := by
  classical
  exact if h : ∃ n, s ∈ atom n then Nat.find h else 0

theorem firstDisjointAtomIndex_mem
    (atom : ℕ → Set Path) {s : Path}
    (h : ∃ n, s ∈ atom n) :
    s ∈ atom (firstDisjointAtomIndex atom s) := by
  classical
  rw [firstDisjointAtomIndex, dif_pos h]
  exact Nat.find_spec h

/-- In a disjoint family, membership in the `n`-th atom forces the canonical
least containing index to be `n`. -/
theorem firstDisjointAtomIndex_eq_of_mem
    (atom : ℕ → Set Path)
    (hpairwise : Pairwise fun n l ↦ Disjoint (atom n) (atom l))
    {s : Path} {n : ℕ} (hs : s ∈ atom n) :
    firstDisjointAtomIndex atom s = n := by
  classical
  let h : ∃ l, s ∈ atom l := ⟨n, hs⟩
  have hmem : s ∈ atom (firstDisjointAtomIndex atom s) :=
    firstDisjointAtomIndex_mem atom h
  by_contra hne
  exact Set.disjoint_left.mp (hpairwise hne) hmem hs

/-- Canonical natural code of a countable disjoint atom family.  Positive
code `n + 1` denotes `atom n`; code zero denotes the complement of the
family's union. -/
noncomputable def disjointAtomRawCode
    (atom : ℕ → Set Path) (s : Path) : ℕ := by
  classical
  exact if h : ∃ n, s ∈ atom n then
      firstDisjointAtomIndex atom s + 1
    else 0

theorem disjointAtomRawCode_eq_succ_of_mem
    (atom : ℕ → Set Path)
    (hpairwise : Pairwise fun n l ↦ Disjoint (atom n) (atom l))
    {s : Path} {n : ℕ} (hs : s ∈ atom n) :
    disjointAtomRawCode atom s = n + 1 := by
  classical
  rw [disjointAtomRawCode, dif_pos ⟨n, hs⟩,
    firstDisjointAtomIndex_eq_of_mem atom hpairwise hs]

/-- Every positive fibre of the canonical code is the corresponding source
atom, as an equality in the full path space. -/
theorem lemma410RawCodeFiber_disjointAtomRawCode_succ
    (atom : ℕ → Set Path)
    (hpairwise : Pairwise fun n l ↦ Disjoint (atom n) (atom l))
    (n : ℕ) :
    lemma410RawCodeFiber (disjointAtomRawCode atom) (n + 1) = atom n := by
  classical
  ext s
  simp only [lemma410RawCodeFiber, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · intro hcode
    by_cases h : ∃ l, s ∈ atom l
    · have hmem : s ∈ atom (firstDisjointAtomIndex atom s) :=
        firstDisjointAtomIndex_mem atom h
      have hindex : firstDisjointAtomIndex atom s = n := by
        rw [disjointAtomRawCode, dif_pos h] at hcode
        omega
      simpa only [hindex] using hmem
    · rw [disjointAtomRawCode, dif_neg h] at hcode
      omega
  · intro hs
    exact disjointAtomRawCode_eq_succ_of_mem atom hpairwise hs

/-- A failure code cannot be the reserved outside-union code when the atom
family covers the failure event. -/
theorem failureCode_disjointAtomRawCode_ne_zero
    {failure : Set Path} (atom : ℕ → Set Path)
    (cover : failure ∩ HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
      ⋃ n, atom n)
    (eta : FailureCode failure (disjointAtomRawCode atom)) :
    eta.1 ≠ 0 := by
  classical
  rcases eta.2 with ⟨s, hsFailureSupport, hsCode⟩
  have hsUnion : s ∈ ⋃ n, atom n := cover hsFailureSupport
  have hexists : ∃ n, s ∈ atom n := by
    simpa only [Set.mem_iUnion] using hsUnion
  have hpositive : 0 < disjointAtomRawCode atom s := by
    rw [disjointAtomRawCode, dif_pos hexists]
    omega
  have hcode : disjointAtomRawCode atom s = eta.1 := by
    simpa only [lemma410RawCodeFiber, Set.mem_preimage,
      Set.mem_singleton_iff] using hsCode
  omega

/-- Consequently every code fibre that meets the failure is the atom indexed
by the predecessor of its positive code. -/
theorem lemma410RawCodeFiber_disjointAtomRawCode_failureCode
    {failure : Set Path} (atom : ℕ → Set Path)
    (cover : failure ∩ HLOZSourceInstantiation.simpleRandomWalkSupport ⊆
      ⋃ n, atom n)
    (hpairwise : Pairwise fun n l ↦ Disjoint (atom n) (atom l))
    (eta : FailureCode failure (disjointAtomRawCode atom)) :
    lemma410RawCodeFiber (disjointAtomRawCode atom) eta.1 =
      atom (eta.1 - 1) := by
  have heta := failureCode_disjointAtomRawCode_ne_zero atom cover eta
  have hsucc : eta.1 - 1 + 1 = eta.1 := by omega
  rw [← hsucc]
  exact lemma410RawCodeFiber_disjointAtomRawCode_succ atom hpairwise _

/-- Empty padding atom used when a natural number is not the code of a
nonempty failure fibre. -/
noncomputable def emptyPathWitnessBranchAtom
    (cWindow m : ℕ) (c : ℝ) (failure : Set Path) (rho : ℝ) :
    StoppedEquation447PathWitnessBranchAtom
      cWindow m c failure rho where
  Coord := Fin 0
  Path := Fin 0
  pathAtom := ∅
  measurableSet_pathAtom := MeasurableSet.empty
  profile := fun x ↦ Fin.elim0 x
  profile_lt := fun x ↦ Fin.elim0 x
  lazyVector := fun _ ↦ fun x ↦ Fin.elim0 x
  measurable_lazyVector := measurable_const
  nextDirection := fun _ ↦ 0
  measurable_nextDirection := measurable_const
  forcedDirection := 0
  D := ∅
  badAtom := fun _ _ ↦ ∅
  witnessAtom := fun _ _ ↦ ∅
  map_law := by simp
  failure_subset := by simp
  thetaPathEvent := ∅
  theta_preimage_subset := by simp
  equation447_cover := by
    simp [HLOZEquation447.sourceEquation447ByCount]
  path_switch := by simp
  witness_disjoint := by simp [Pairwise]
  witness_measurable := by simp

/-- The strict rectangular path-switch data imply the older exponential
path-witness remainder once the checked optimal binomial layer is available.
This helper lets Lemma 4.10 consume the same literal changed-path interface
as Lemmas 4.11--4.12, instead of assuming the aggregate path-switch bound. -/
noncomputable def lemma410RectangularRemainingToPathWitness
    {Coord : Type} [Fintype Coord]
    {cWindow m : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent pathAtom : Set Path}
    {profile : Coord → ℕ}
    {lazyVector : Path → Coord → ℕ}
    {nextDirection : Path → Direction}
    (R :
      Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
        cWindow m ratioC rho failure thetaPathEvent pathAtom
          profile lazyVector nextDirection)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q, Nat.ceil rho ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    Equation447PathWitnessBranchRemainingData cWindow m
      (categoricalOptimalRate ratioC) rho
      failure pathAtom profile lazyVector nextDirection :=
  R.toLengthSeparatedOptimalCategoricalPathWitnessBranchRemainingData
    |>.toOptimalCategoricalPathWitnessBranchRemainingData
    |>.toRemainingData hC hbinomial

@[simp] theorem lemma410RectangularRemainingToPathWitness_D
    {Coord : Type} [Fintype Coord]
    {cWindow m : ℕ} {ratioC rho : ℝ}
    {failure thetaPathEvent pathAtom : Set Path}
    {profile : Coord → ℕ}
    {lazyVector : Path → Coord → ℕ}
    {nextDirection : Path → Direction}
    (R :
      Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
        cWindow m ratioC rho failure thetaPathEvent pathAtom
          profile lazyVector nextDirection)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q, Nat.ceil rho ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    (lemma410RectangularRemainingToPathWitness R hC hbinomial).D =
      R.core.D := rfl

/-- Coded version of the countable stopped-atom aggregation theorem.

Coverage and pairwise disjointness are obtained from the code.  The code
itself need not be measurable: the caller supplies a literal measurable
stopped atom only for a nonempty failure fibre, and unused natural numbers
are represented by the empty atom. -/
theorem measure_diff_le_of_coded_pathWitnessGoodBandAtoms
    {cWindow m : ℕ} {witnessRate cBase alpha rho : ℝ}
    {failure thetaPath : Set Path}
    (rawCode : Path → ℕ)
    (atom : FailureCode failure rawCode →
      StoppedEquation447PathWitnessBranchAtom
        cWindow m witnessRate failure rho)
    (pathAtom_eq : ∀ eta,
      (atom eta).pathAtom = lemma410RawCodeFiber rawCode eta.1)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hwitnessRate : 0 < witnessRate)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hrho : rho ≤ Real.log (m : ℝ) ^ 2)
    (failure_subset : ∀ eta,
      failure ∩ (atom eta).pathAtom ⊆
        (fun s ↦ ((atom eta).lazyVector s,
          (atom eta).nextDirection s)) ⁻¹'
          (((@sourceProfileQEvent (atom eta).Coord
              (atom eta).coordFintype m
              (sourceAlphaIntervalCount m alpha) (atom eta).profile
              (geometricThreshold (Real.log (m : ℝ) ^ 2)
                (sourceLemma411GrowthFactor cWindow)
                (sourceAlphaIntervalCount m alpha)) ∩ (atom eta).D)) ×ˢ
            (Set.univ : Set Direction)))
    (theta_subset : ∀ eta,
      (failure ∩ (atom eta).pathAtom) ∩
          (fun s ↦ ((atom eta).lazyVector s,
            (atom eta).nextDirection s)) ⁻¹'
            ((@sourceProfileThetaUpTo (atom eta).Coord
                (atom eta).coordFintype cWindow m
                (sourceAlphaIntervalCount m alpha) (atom eta).profile) ×ˢ
              (Set.univ : Set Direction)) ⊆ thetaPath)
    (hbaseAbsorb :
      4 * (Real.exp (-witnessRate * rho) *
          (1 - Real.exp (-witnessRate))⁻¹) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp
        (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw (failure \ thetaPath) ≤ tail := by
  letI : Encodable (FailureCode failure rawCode) := Encodable.ofCountable _
  let codedAtom : ℕ →
      StoppedEquation447PathWitnessBranchAtom
        cWindow m witnessRate failure rho := fun n ↦
    match Encodable.decode₂ (FailureCode failure rawCode) n with
    | some eta => atom eta
    | none => emptyPathWitnessBranchAtom
        cWindow m witnessRate failure rho
  have hsupported :
      simpleRandomWalkLaw
          ((failure ∩ HLOZSourceInstantiation.simpleRandomWalkSupport) \
            thetaPath) ≤ tail := by
    apply measure_diff_le_of_disjoint_stopped_atoms
      (fun n ↦ (codedAtom n).pathAtom) tail
    · intro s hs
      let eta : FailureCode failure rawCode :=
        ⟨rawCode s, ⟨s, hs, by simp [lemma410RawCodeFiber]⟩⟩
      refine Set.mem_iUnion.mpr ⟨Encodable.encode eta, ?_⟩
      simp only [codedAtom, Encodable.decode₂_encode]
      rw [pathAtom_eq eta]
      simp [lemma410RawCodeFiber, eta]
    · intro n k hne
      simp only [codedAtom]
      split
      · rename_i eta hn
        split
        · rename_i zeta hk
          have hencodeEta : Encodable.encode eta = n :=
            Encodable.decode₂_eq_some.mp hn
          have hencodeZeta : Encodable.encode zeta = k :=
            Encodable.decode₂_eq_some.mp hk
          have hetazeta : eta ≠ zeta := by
            intro h
            apply hne
            rw [← hencodeEta, ← hencodeZeta, h]
          rw [pathAtom_eq eta, pathAtom_eq zeta]
          exact lemma410RawCodeFiber_pairwise rawCode
            (fun h ↦ hetazeta (Subtype.ext h))
        · simp [emptyPathWitnessBranchAtom]
      · simp [emptyPathWitnessBranchAtom]
    · intro n
      simp only [codedAtom]
      split
      · rename_i eta hdecode
        exact (atom eta).measurableSet_pathAtom
      · simp [emptyPathWitnessBranchAtom]
    · intro n
      simp only [codedAtom]
      split
      · rename_i eta hdecode
        calc
          simpleRandomWalkLaw
              ((((failure ∩
                  HLOZSourceInstantiation.simpleRandomWalkSupport) \
                thetaPath) ∩ (atom eta).pathAtom)) ≤
              simpleRandomWalkLaw
                ((failure \ thetaPath) ∩ (atom eta).pathAtom) := by
            apply measure_mono
            rintro s ⟨⟨⟨hsFailure, _hsSupport⟩, hsTheta⟩, hsAtom⟩
            exact ⟨⟨hsFailure, hsTheta⟩, hsAtom⟩
          _ ≤ tail * simpleRandomWalkLaw (atom eta).pathAtom :=
            stoppedEquation447PathWitnessBranchAtom_prop48_good_band_local_bound
              (atom eta) G hwitnessRate halpha hAlpha hrho
              (failure_subset eta) (theta_subset eta) hbaseAbsorb tail hshift
      · simp [emptyPathWitnessBranchAtom]
  have hevent :
      (failure ∩ HLOZSourceInstantiation.simpleRandomWalkSupport) \
          thetaPath =
        HLOZSourceInstantiation.simpleRandomWalkSupport ∩
          (failure \ thetaPath) := by
    ext s
    simp only [Set.mem_diff, Set.mem_inter_iff]
    tauto
  rw [hevent,
    HLOZSourceInstantiation.simpleRandomWalkLaw_inter_support] at hsupported
  exact hsupported

/-! ## The four literal X-east branches -/

/-- Unprimed-even/tie-left source data on the nonempty fibres of a code. -/
structure UnprimedEvenCodedGoodBandData
    (cWindow m : ℕ) (witnessRate capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (xEastLeftEvenWinnerContextualFailure capCoeff m r a j) rawCode →
    UnprimedEvenLeftWinnerSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastLeftEvenWinnerContextualFailure capCoeff m r a j)
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    xEastLeftEvenWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (xEastLeftEvenWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)

namespace UnprimedEvenCodedGoodBandData

variable {cWindow m : ℕ} {witnessRate capCoeff : ℝ}
  {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}
  (D : UnprimedEvenCodedGoodBandData
    cWindow m witnessRate capCoeff r a j)

noncomputable def atom (eta : FailureCode
    (xEastLeftEvenWinnerContextualFailure capCoeff m r a j) D.rawCode) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (xEastLeftEvenWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.source eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (xEastLeftEvenWinnerContextualFailure capCoeff m r a j)
    (D.remaining eta)

@[simp] theorem atom_pathAtom (eta) :
    (D.atom eta).pathAtom = lemma410RawCodeFiber D.rawCode eta.1 :=
  D.pathAtom_eq eta

theorem measure_diff_le
    {cBase : ℝ}
    (D : UnprimedEvenCodedGoodBandData
      cWindow m witnessRate capCoeff r a j)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hwitnessRate : 0 < witnessRate)
    (halpha : kappaOne ≤ sourceBeta (alphaValue a) j)
    (hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      4 * (Real.exp (-witnessRate *
          ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)) *
        (1 - Real.exp (-witnessRate))⁻¹) ≤
          Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp
        (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw
        (xEastLeftEvenWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m (xIndex east) r (alphaValue a)) ≤ tail := by
  have hrho : (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤
      Real.log (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (m : ℝ))]
  exact measure_diff_le_of_coded_pathWitnessGoodBandAtoms
    D.rawCode D.atom D.atom_pathAtom G
      hwitnessRate halpha hAlpha hrho
      (fun eta ↦ D.failure_subset eta)
      (fun eta ↦ D.theta_subset eta) hbaseAbsorb tail hshift

end UnprimedEvenCodedGoodBandData

/-- Unprimed odd-terminal/tie-left source data on nonempty code fibres. -/
structure UnprimedOddTerminalCodedGoodBandData
    (cWindow m : ℕ) (witnessRate capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j) rawCode →
    UnprimedOddTerminalTieLeftSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j)
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)

namespace UnprimedOddTerminalCodedGoodBandData

variable {cWindow m : ℕ} {witnessRate capCoeff : ℝ}
  {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}

noncomputable def atom
    (D : UnprimedOddTerminalCodedGoodBandData
      cWindow m witnessRate capCoeff r a j)
    (eta : FailureCode
      (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j)
        D.rawCode) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.source eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j)
    (D.remaining eta)

@[simp] theorem atom_pathAtom
    (D : UnprimedOddTerminalCodedGoodBandData
      cWindow m witnessRate capCoeff r a j) (eta) :
    (D.atom eta).pathAtom = lemma410RawCodeFiber D.rawCode eta.1 :=
  D.pathAtom_eq eta

end UnprimedOddTerminalCodedGoodBandData

/-- Primed-odd/strict-right source data on nonempty code fibres. -/
structure PrimedOddCodedGoodBandData
    (cWindow m : ℕ) (witnessRate capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (xEastRightOddWinnerContextualFailure capCoeff m r a j) rawCode →
    PrimedOddStrictRightWinnerSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastRightOddWinnerContextualFailure capCoeff m r a j)
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    xEastRightOddWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (xEastRightOddWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)

namespace PrimedOddCodedGoodBandData

variable {cWindow m : ℕ} {witnessRate capCoeff : ℝ}
  {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}

noncomputable def atom
    (D : PrimedOddCodedGoodBandData
      cWindow m witnessRate capCoeff r a j)
    (eta : FailureCode
      (xEastRightOddWinnerContextualFailure capCoeff m r a j) D.rawCode) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (xEastRightOddWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.source eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (xEastRightOddWinnerContextualFailure capCoeff m r a j)
    (D.remaining eta)

@[simp] theorem atom_pathAtom
    (D : PrimedOddCodedGoodBandData
      cWindow m witnessRate capCoeff r a j) (eta) :
    (D.atom eta).pathAtom = lemma410RawCodeFiber D.rawCode eta.1 :=
  D.pathAtom_eq eta

end PrimedOddCodedGoodBandData

/-- Primed even-terminal/strict-right source data on nonempty code fibres. -/
structure PrimedEvenTerminalCodedGoodBandData
    (cWindow m : ℕ) (witnessRate capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j)
        rawCode → PrimedEvenTerminalStrictRightSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j)
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)

namespace PrimedEvenTerminalCodedGoodBandData

variable {cWindow m : ℕ} {witnessRate capCoeff : ℝ}
  {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}

noncomputable def atom
    (D : PrimedEvenTerminalCodedGoodBandData
      cWindow m witnessRate capCoeff r a j)
    (eta : FailureCode
      (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j)
        D.rawCode) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.source eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j)
    (D.remaining eta)

@[simp] theorem atom_pathAtom
    (D : PrimedEvenTerminalCodedGoodBandData
      cWindow m witnessRate capCoeff r a j) (eta) :
    (D.atom eta).pathAtom = lemma410RawCodeFiber D.rawCode eta.1 :=
  D.pathAtom_eq eta

end PrimedEvenTerminalCodedGoodBandData

/-- The four checkerboard branches with canonical coded partitions. -/
structure XEastCanonicalCodedPathWitnessGoodBandData
    (cWindow m : ℕ) (witnessRate capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  unprimedEven : UnprimedEvenCodedGoodBandData
    cWindow m witnessRate capCoeff r a j
  unprimedOddTerminal : UnprimedOddTerminalCodedGoodBandData
    cWindow m witnessRate capCoeff r a j
  primedOdd : PrimedOddCodedGoodBandData
    cWindow m witnessRate capCoeff r a j
  primedEvenTerminal : PrimedEvenTerminalCodedGoodBandData
    cWindow m witnessRate capCoeff r a j

namespace XEastCanonicalCodedPathWitnessGoodBandData

theorem measure_diff_le
    {cWindow m : ℕ} {witnessRate capCoeff cBase : ℝ}
    {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}
    (D : XEastCanonicalCodedPathWitnessGoodBandData
      cWindow m witnessRate capCoeff r a j)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hwitnessRate : 0 < witnessRate)
    (halpha : kappaOne ≤ sourceBeta (alphaValue a) j)
    (hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      4 * (Real.exp (-witnessRate *
          ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)) *
        (1 - Real.exp (-witnessRate))⁻¹) ≤
          Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp
        (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw
        (xEastLeftEvenWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m (xIndex east) r (alphaValue a)) ≤ tail ∧
      simpleRandomWalkLaw
        (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m (xIndex east) r (alphaValue a)) ≤ tail ∧
      simpleRandomWalkLaw
        (xEastRightOddWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m (xIndex east) r (alphaValue a)) ≤ tail ∧
      simpleRandomWalkLaw
        (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m (xIndex east) r (alphaValue a)) ≤ tail := by
  have hrho : (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤
      Real.log (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (m : ℝ))]
  refine ⟨D.unprimedEven.measure_diff_le G hwitnessRate halpha hAlpha
      hbaseAbsorb tail hshift, ?_, ?_, ?_⟩
  · exact measure_diff_le_of_coded_pathWitnessGoodBandAtoms
      D.unprimedOddTerminal.rawCode
      D.unprimedOddTerminal.atom D.unprimedOddTerminal.atom_pathAtom G
      hwitnessRate halpha hAlpha hrho
      D.unprimedOddTerminal.failure_subset
      D.unprimedOddTerminal.theta_subset hbaseAbsorb tail hshift
  · exact measure_diff_le_of_coded_pathWitnessGoodBandAtoms
      D.primedOdd.rawCode
      D.primedOdd.atom D.primedOdd.atom_pathAtom G
      hwitnessRate halpha hAlpha hrho D.primedOdd.failure_subset
      D.primedOdd.theta_subset hbaseAbsorb tail hshift
  · exact measure_diff_le_of_coded_pathWitnessGoodBandAtoms
      D.primedEvenTerminal.rawCode
      D.primedEvenTerminal.atom D.primedEvenTerminal.atom_pathAtom G
      hwitnessRate halpha hAlpha hrho
      D.primedEvenTerminal.failure_subset
      D.primedEvenTerminal.theta_subset hbaseAbsorb tail hshift

end XEastCanonicalCodedPathWitnessGoodBandData

/-- Coded literal changed-path input at X-east.  Its code fibres replace all
four caller-supplied covers and disjointness proofs; their measurability is
needed only on nonempty failure fibres and follows from the literal atoms. -/
def Prop47Lemma410Prop48CanonicalCodedPathWitnessXEastLowBandInputs
    (cWindow : ℕ) (witnessRate capCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (XEastCanonicalCodedPathWitnessGoodBandData
      cWindow m witnessRate capCoeff r a j)

/-! ## Strict rectangular X-east source cut

The final source interface should not assume the already-summed path-switch
inequality stored in `Equation447PathWitnessBranchRemainingData`.  The four
records below retain the literal bad and changed-path coordinate rectangles,
their one-coordinate likelihood comparison, and the stopped-length
separation certificate.  Finite-product factorization, the optimal binomial
layer, witness disjointness, and the exponential path-switch estimate are all
derived by Lean. -/

structure UnprimedEvenCodedRectangularGoodBandData
    (cWindow m : ℕ) (ratioC capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (xEastLeftEvenWinnerContextualFailure capCoeff m r a j) rawCode →
    UnprimedEvenLeftWinnerSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastLeftEvenWinnerContextualFailure capCoeff m r a j)
      (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a))
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    xEastLeftEvenWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).core.D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (xEastLeftEvenWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)

structure UnprimedOddTerminalCodedRectangularGoodBandData
    (cWindow m : ℕ) (ratioC capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j) rawCode →
    UnprimedOddTerminalTieLeftSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j)
      (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a))
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).core.D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (xEastLeftOddTerminalWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)

structure PrimedOddCodedRectangularGoodBandData
    (cWindow m : ℕ) (ratioC capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (xEastRightOddWinnerContextualFailure capCoeff m r a j) rawCode →
    PrimedOddStrictRightWinnerSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastRightOddWinnerContextualFailure capCoeff m r a j)
      (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a))
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    xEastRightOddWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).core.D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (xEastRightOddWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)

structure PrimedEvenTerminalCodedRectangularGoodBandData
    (cWindow m : ℕ) (ratioC capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j)
        rawCode → PrimedEvenTerminalStrictRightSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j)
      (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a))
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).core.D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (xEastRightEvenTerminalWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m (xIndex east) r (alphaValue a)

structure XEastCanonicalCodedRectangularGoodBandData
    (cWindow m : ℕ) (ratioC capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  unprimedEven : UnprimedEvenCodedRectangularGoodBandData
    cWindow m ratioC capCoeff r a j
  unprimedOddTerminal : UnprimedOddTerminalCodedRectangularGoodBandData
    cWindow m ratioC capCoeff r a j
  primedOdd : PrimedOddCodedRectangularGoodBandData
    cWindow m ratioC capCoeff r a j
  primedEvenTerminal : PrimedEvenTerminalCodedRectangularGoodBandData
    cWindow m ratioC capCoeff r a j

namespace XEastCanonicalCodedRectangularGoodBandData

variable {cWindow m : ℕ} {ratioC capCoeff : ℝ}
  {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}

noncomputable def toPathWitness
    (D : XEastCanonicalCodedRectangularGoodBandData
      cWindow m ratioC capCoeff r a j)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    XEastCanonicalCodedPathWitnessGoodBandData cWindow m
      (categoricalOptimalRate ratioC) capCoeff r a j where
  unprimedEven :=
    { rawCode := D.unprimedEven.rawCode
      source := D.unprimedEven.source
      pathAtom_eq := D.unprimedEven.pathAtom_eq
      remaining := fun eta ↦ lemma410RectangularRemainingToPathWitness
        (D.unprimedEven.remaining eta) hC hbinomial
      failure_subset := by
        intro eta
        simpa only [lemma410RectangularRemainingToPathWitness_D] using
          D.unprimedEven.failure_subset eta
      theta_subset := D.unprimedEven.theta_subset }
  unprimedOddTerminal :=
    { rawCode := D.unprimedOddTerminal.rawCode
      source := D.unprimedOddTerminal.source
      pathAtom_eq := D.unprimedOddTerminal.pathAtom_eq
      remaining := fun eta ↦ lemma410RectangularRemainingToPathWitness
        (D.unprimedOddTerminal.remaining eta) hC hbinomial
      failure_subset := by
        intro eta
        simpa only [lemma410RectangularRemainingToPathWitness_D] using
          D.unprimedOddTerminal.failure_subset eta
      theta_subset := D.unprimedOddTerminal.theta_subset }
  primedOdd :=
    { rawCode := D.primedOdd.rawCode
      source := D.primedOdd.source
      pathAtom_eq := D.primedOdd.pathAtom_eq
      remaining := fun eta ↦ lemma410RectangularRemainingToPathWitness
        (D.primedOdd.remaining eta) hC hbinomial
      failure_subset := by
        intro eta
        simpa only [lemma410RectangularRemainingToPathWitness_D] using
          D.primedOdd.failure_subset eta
      theta_subset := D.primedOdd.theta_subset }
  primedEvenTerminal :=
    { rawCode := D.primedEvenTerminal.rawCode
      source := D.primedEvenTerminal.source
      pathAtom_eq := D.primedEvenTerminal.pathAtom_eq
      remaining := fun eta ↦ lemma410RectangularRemainingToPathWitness
        (D.primedEvenTerminal.remaining eta) hC hbinomial
      failure_subset := by
        intro eta
        simpa only [lemma410RectangularRemainingToPathWitness_D] using
          D.primedEvenTerminal.failure_subset eta
      theta_subset := D.primedEvenTerminal.theta_subset }

end XEastCanonicalCodedRectangularGoodBandData

def Prop47Lemma410Prop48CanonicalCodedRectangularXEastLowBandInputs
    (cWindow : ℕ) (ratioC capCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (XEastCanonicalCodedRectangularGoodBandData
      cWindow m ratioC capCoeff r a j)

theorem codedPathWitnessXEastLowBandInputs_of_rectangular
    (cWindow : ℕ) {ratioC capCoeff : ℝ} (hC : 0 < ratioC)
    (h : Prop47Lemma410Prop48CanonicalCodedRectangularXEastLowBandInputs
      cWindow ratioC capCoeff) :
    Prop47Lemma410Prop48CanonicalCodedPathWitnessXEastLowBandInputs
      cWindow (categoricalOptimalRate ratioC) capCoeff := by
  have hbin := eventually_optimal_binomial_layer_above_quarter_log_sq
    ratioC hC
  filter_upwards [h, hbin] with m hm hbm
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  exact ⟨D.toPathWitness hC hbm⟩

/-- The coded X-east atoms give the low-band candidate estimate. -/
theorem prop47Lemma410Prop48CodedPathWitness_xEast_lowBands
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalCodedPathWitnessXEastLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (xEastCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m (xIndex east) r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  let cBase := witnessRate / 8
  have hcBase : 0 < cBase := by
    dsimp [cBase]
    positivity
  have hgood := eventually_sourceProp48NumericalAt cWindow hcBase
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hbase := eventually_pathWitnessEquation447_error_absorb
    hwitnessRate (show (0 : ℝ) < 1 / 4 by norm_num)
  have hshift := eventually_prop48Rate_le_sourceBetaCandidateTail
    (rate := min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (d := 4 * d) (by positivity) (by
      dsimp [cBase] at hcompare ⊢
      nlinarith [hcompare])
  have habsorbParity :=
    eventually_two_mul_sourceBetaCandidateTail_two_mul_le
      (show 0 < 2 * d by positivity)
  have habsorbWinner :=
    eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  have hcover :=
    eventually_fullCandidateFailure_subset_smallWinnerFailures_xEast
      hCsmall.le hgap
  filter_upwards [h, hgood, hbase, hshift, habsorbParity,
      habsorbWinner, hcover] with m hm hgoodM hbaseM hshiftM
        habsorbParityM habsorbWinnerM hcoverM
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  have halpha : kappaOne ≤ sourceBeta (alphaValue a) j :=
    kappaOne_le_sourceBeta ha j
  have hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5 :=
    hj.trans (by norm_num)
  have hbaseM' :
      4 * (Real.exp (-witnessRate *
          ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)) *
        (1 - Real.exp (-witnessRate))⁻¹) ≤
          Real.exp (-cBase * Real.log (m : ℝ) ^ 2) := by
    have hraw := hbaseM
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) (le_refl _)
    dsimp [cBase]
    convert hraw using 1 <;> ring
  let tailFour := sourceBetaCandidateTail (4 * d) m
  let tailTwo := sourceBetaCandidateTail (2 * d) m
  have hbranches := D.measure_diff_le hgoodM hwitnessRate halpha hAlpha
    hbaseM' tailFour (by simpa only [tailFour] using hshiftM)
  rcases hbranches with ⟨heven, hodd, hrightOdd, hrightEven⟩
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m (xIndex east) r (alphaValue a)
  have habsorbParityM' : 2 * tailFour ≤ tailTwo := by
    dsimp [tailFour, tailTwo]
    have h4 : 2 * (2 * d) = 4 * d := by ring
    simpa only [h4] using habsorbParityM
  have hleft : simpleRandomWalkLaw
      (xEastLeftWinnerContextualFailure Csmall m r a j \ theta) ≤
        tailTwo := by
    calc
      simpleRandomWalkLaw
          (xEastLeftWinnerContextualFailure Csmall m r a j \ theta) ≤
        simpleRandomWalkLaw
          ((xEastLeftEvenWinnerContextualFailure Csmall m r a j \ theta) ∪
            (xEastLeftOddTerminalWinnerContextualFailure
              Csmall m r a j \ theta)) := by
          apply measure_mono
          intro omega homega
          rcases xEastLeftWinnerContextualFailure_subset_parity_union
              Csmall m r a j homega.1 with he | ho
          · exact Or.inl ⟨he, homega.2⟩
          · exact Or.inr ⟨ho, homega.2⟩
      _ ≤ simpleRandomWalkLaw
          (xEastLeftEvenWinnerContextualFailure Csmall m r a j \ theta) +
        simpleRandomWalkLaw
          (xEastLeftOddTerminalWinnerContextualFailure
            Csmall m r a j \ theta) := measure_union_le _ _
      _ ≤ tailFour + tailFour := add_le_add
        (by simpa only [theta] using heven)
        (by simpa only [theta] using hodd)
      _ = 2 * tailFour := by ring
      _ ≤ tailTwo := habsorbParityM'
  have hright : simpleRandomWalkLaw
      (xEastRightWinnerContextualFailure Csmall m r a j \ theta) ≤
        tailTwo := by
    calc
      simpleRandomWalkLaw
          (xEastRightWinnerContextualFailure Csmall m r a j \ theta) ≤
        simpleRandomWalkLaw
          ((xEastRightOddWinnerContextualFailure Csmall m r a j \ theta) ∪
            (xEastRightEvenTerminalWinnerContextualFailure
              Csmall m r a j \ theta)) := by
          apply measure_mono
          intro omega homega
          rcases xEastRightWinnerContextualFailure_subset_parity_union
              Csmall m r a j homega.1 with ho | he
          · exact Or.inl ⟨ho, homega.2⟩
          · exact Or.inr ⟨he, homega.2⟩
      _ ≤ simpleRandomWalkLaw
          (xEastRightOddWinnerContextualFailure Csmall m r a j \ theta) +
        simpleRandomWalkLaw
          (xEastRightEvenTerminalWinnerContextualFailure
            Csmall m r a j \ theta) := measure_union_le _ _
      _ ≤ tailFour + tailFour := add_le_add
        (by simpa only [theta] using hrightOdd)
        (by simpa only [theta] using hrightEven)
      _ = 2 * tailFour := by ring
      _ ≤ tailTwo := habsorbParityM'
  have hcontextCover : xEastCandidateContextualFailure Cfull m r a j ⊆
      xEastLeftWinnerContextualFailure Csmall m r a j ∪
        xEastRightWinnerContextualFailure Csmall m r a j := by
    intro omega homega
    have heast : xIndex east = (0 : Fin 6) := by
      apply Fin.ext
      rfl
    have hprefix : omega ∈
        hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1) := by
      refine ⟨homega.1, ?_⟩
      rw [← heast]
      exact homega.2.1.1
    rcases hcoverM r a ha j hprefix with hleft' | hright'
    · exact Or.inl ⟨hleft'.1, homega.2⟩
    · exact Or.inr ⟨hright'.1, homega.2⟩
  calc
    simpleRandomWalkLaw
        (xEastCandidateContextualFailure Cfull m r a j \ theta) ≤
      simpleRandomWalkLaw
        ((xEastLeftWinnerContextualFailure Csmall m r a j \ theta) ∪
          (xEastRightWinnerContextualFailure Csmall m r a j \ theta)) := by
        apply measure_mono
        intro omega homega
        rcases hcontextCover homega.1 with hleft' | hright'
        · exact Or.inl ⟨hleft', homega.2⟩
        · exact Or.inr ⟨hright', homega.2⟩
    _ ≤ simpleRandomWalkLaw
          (xEastLeftWinnerContextualFailure Csmall m r a j \ theta) +
        simpleRandomWalkLaw
          (xEastRightWinnerContextualFailure Csmall m r a j \ theta) :=
      measure_union_le _ _
    _ ≤ tailTwo + tailTwo := add_le_add hleft hright
    _ = 2 * tailTwo := by ring
    _ ≤ sourceBetaCandidateTail d m := by
      simpa only [tailTwo] using habsorbWinnerM

/-- High-band emptiness completes the coded X-east estimate. -/
theorem prop47Lemma410Prop48CodedPathWitness_xEast
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalCodedPathWitnessXEastLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      simpleRandomWalkLaw
          (xEastCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m (xIndex east) r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  have hlow := prop47Lemma410Prop48CodedPathWitness_xEast_lowBands
    cWindow hwitnessRate hCsmall hgap hd hcompare h
  have hCfull : 0 < Cfull := by linarith
  have hhigh :=
    eventually_hlozCandidateCapFailureEvent_eq_empty_highBands hCfull
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · exact hlowM r a ha j hj
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [xEastCandidateContextualFailure, hempty, empty_inter, empty_diff,
      measure_empty]
    exact bot_le

/-- Coded candidate tails feed the common beta-band/race assembly. -/
theorem prop47Lemma410CodedPathWitnessStretchedExponential_xEast
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalCodedPathWitnessXEastLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m (xIndex east) r (alphaValue a) \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m (xIndex east) r (alphaValue a)) ≤
        ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) := by
  apply prop47Lemma410ThetaFreeStretchedExponential_xEast_of_candidateTails
    (Cfull := Cfull) (d := d) (by linarith) hd
  exact prop47Lemma410Prop48CodedPathWitness_xEast cWindow
    hwitnessRate hCsmall hgap hd hcompare h

private theorem eventually_codedLemma410Absorption_le_exceptional
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) ≤
        sourceExceptionalRateWithPrefactor m 1 kappa := by
  have hc : 0 < sourceLemma410AbsorptionConstant d :=
    sourceLemma410AbsorptionConstant_pos hd
  have hreal := (tendsto_add_atTop_nat 1).eventually
    (eventually_exponential_error_absorbed (c :=
      sourceLemma410AbsorptionConstant d) hc)
  filter_upwards [hreal] with m hm
  have hm' :
      Real.exp (-sourceLemma410AbsorptionConstant d *
          Real.log ((m : ℝ) + 1) ^ 2) ≤
        ((m : ℝ) + 1) ^ (-(3 * kappa)) := by
    simpa [Nat.cast_add, Nat.cast_one] using hm
  rw [sourceExceptionalRateWithPrefactor]
  simp only [Nat.cast_one, one_mul]
  rw [sourceExceptionalRate]
  have hbase : ENNReal.ofReal ((m : ℝ) + 1) = (m : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp
  rw [← hbase, ENNReal.ofReal_rpow_of_pos (by positivity)]
  exact ENNReal.ofReal_le_ofReal hm'

/-- Proposition 4.5 pays the single theta event after the coded
Proposition-4.8 estimate. -/
theorem prop47Lemma410Estimate_xEast_of_codedPathWitness_inputs
    (cWindow prop45Coeff : ℕ)
    {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalCodedPathWitnessXEastLowBandInputs
      cWindow witnessRate Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m (xIndex east) r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
  have hdiff := prop47Lemma410CodedPathWitnessStretchedExponential_xEast
    cWindow hwitnessRate hCsmall hgap hd hcompare h
  have herror := eventually_codedLemma410Absorption_le_exceptional hd
  filter_upwards [hdiff, hProp45, herror] with m hdiffM hthetaM herrorM
  intro r a ha
  let E := lemma410FailureEvent m (xIndex east) r (alphaValue a)
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m (xIndex east) r (alphaValue a)
  have hsplit : E ⊆ theta ∪ (E \ theta) := by
    intro omega homega
    by_cases htheta : omega ∈ theta
    · exact Or.inl htheta
    · exact Or.inr ⟨homega, htheta⟩
  calc
    simpleRandomWalkLaw E ≤
        simpleRandomWalkLaw theta + simpleRandomWalkLaw (E \ theta) :=
      (measure_mono hsplit).trans (measure_union_le _ _)
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        sourceExceptionalRateWithPrefactor m 1 kappa :=
      add_le_add (hthetaM (xIndex east) r a ha)
        ((hdiffM r a ha).trans herrorM)
    _ = sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- Quarter-turn transport of the canonically coded X-east source input. -/
theorem prop47Lemma410EstimateXDirections_of_codedPathWitness_inputs
    (cWindow prop45Coeff : ℕ)
    {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 16 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalCodedPathWitnessXEastLowBandInputs
      cWindow witnessRate Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    Prop47Lemma410EstimateXDirections (prop45Coeff + 1) := by
  have heast := prop47Lemma410Estimate_xEast_of_codedPathWitness_inputs
    cWindow prop45Coeff hwitnessRate hCsmall hgap hd hcompare h hProp45
  filter_upwards [heast] with m hm
  intro d₀ r a ha
  rw [simpleRandomWalkLaw_lemma410FailureEvent_x_eq]
  exact hm r a ha

/-! ## The two literal temporal column phases -/

/-- Forward/tie-left terminal source data on nonempty code fibres. -/
structure ForwardColumnCodedGoodBandData
    (cWindow m : ℕ) (witnessRate capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (yLeftWinnerContextualFailure capCoeff m r a j) rawCode →
    ForwardColumnWinnerSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yLeftWinnerContextualFailure capCoeff m r a j)
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    yLeftWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (yLeftWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m yIndex r (alphaValue a)

namespace ForwardColumnCodedGoodBandData

variable {cWindow m : ℕ} {witnessRate capCoeff : ℝ}
  {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}

noncomputable def atom
    (D : ForwardColumnCodedGoodBandData
      cWindow m witnessRate capCoeff r a j)
    (eta : FailureCode
      (yLeftWinnerContextualFailure capCoeff m r a j) D.rawCode) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (yLeftWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.source eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yLeftWinnerContextualFailure capCoeff m r a j) (D.remaining eta)

@[simp] theorem atom_pathAtom
    (D : ForwardColumnCodedGoodBandData
      cWindow m witnessRate capCoeff r a j) (eta) :
    (D.atom eta).pathAtom = lemma410RawCodeFiber D.rawCode eta.1 :=
  D.pathAtom_eq eta

end ForwardColumnCodedGoodBandData

/-- Backward/strict-right terminal source data on nonempty code fibres. -/
structure PrimedColumnCodedGoodBandData
    (cWindow m : ℕ) (witnessRate capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (yRightWinnerContextualFailure capCoeff m r a j) rawCode →
    PrimedColumnWinnerSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447PathWitnessBranchRemainingData cWindow m witnessRate
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yRightWinnerContextualFailure capCoeff m r a j)
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    yRightWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (yRightWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m yIndex r (alphaValue a)

namespace PrimedColumnCodedGoodBandData

variable {cWindow m : ℕ} {witnessRate capCoeff : ℝ}
  {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}

noncomputable def atom
    (D : PrimedColumnCodedGoodBandData
      cWindow m witnessRate capCoeff r a j)
    (eta : FailureCode
      (yRightWinnerContextualFailure capCoeff m r a j) D.rawCode) :
    StoppedEquation447PathWitnessBranchAtom cWindow m witnessRate
      (yRightWinnerContextualFailure capCoeff m r a j)
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) :=
  (D.source eta).toStoppedEquation447PathWitnessBranchAtom
    cWindow witnessRate ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
    (yRightWinnerContextualFailure capCoeff m r a j) (D.remaining eta)

@[simp] theorem atom_pathAtom
    (D : PrimedColumnCodedGoodBandData
      cWindow m witnessRate capCoeff r a j) (eta) :
    (D.atom eta).pathAtom = lemma410RawCodeFiber D.rawCode eta.1 :=
  D.pathAtom_eq eta

end PrimedColumnCodedGoodBandData

/-- Both temporal column phases with canonical coded partitions. -/
structure YCanonicalCodedPathWitnessGoodBandData
    (cWindow m : ℕ) (witnessRate capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  forward : ForwardColumnCodedGoodBandData
    cWindow m witnessRate capCoeff r a j
  backward : PrimedColumnCodedGoodBandData
    cWindow m witnessRate capCoeff r a j

namespace YCanonicalCodedPathWitnessGoodBandData

theorem measure_diff_le
    {cWindow m : ℕ} {witnessRate capCoeff cBase : ℝ}
    {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}
    (D : YCanonicalCodedPathWitnessGoodBandData
      cWindow m witnessRate capCoeff r a j)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hwitnessRate : 0 < witnessRate)
    (halpha : kappaOne ≤ sourceBeta (alphaValue a) j)
    (hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      4 * (Real.exp (-witnessRate *
          ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)) *
        (1 - Real.exp (-witnessRate))⁻¹) ≤
          Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp
        (sourceAdjacentComparisonExponent cWindow))) / 2) *
          Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw
        (yLeftWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m yIndex r (alphaValue a)) ≤ tail ∧
      simpleRandomWalkLaw
        (yRightWinnerContextualFailure capCoeff m r a j \
          prop45FailureEvent sourceCanonicalProfiles canonicalCStar
            m yIndex r (alphaValue a)) ≤ tail := by
  have hrho : (1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2 ≤
      Real.log (m : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (m : ℝ))]
  constructor
  · exact measure_diff_le_of_coded_pathWitnessGoodBandAtoms
      D.forward.rawCode
      D.forward.atom D.forward.atom_pathAtom G hwitnessRate
      halpha hAlpha hrho D.forward.failure_subset D.forward.theta_subset
      hbaseAbsorb tail hshift
  · exact measure_diff_le_of_coded_pathWitnessGoodBandAtoms
      D.backward.rawCode
      D.backward.atom D.backward.atom_pathAtom G hwitnessRate
      halpha hAlpha hrho D.backward.failure_subset D.backward.theta_subset
      hbaseAbsorb tail hshift

end YCanonicalCodedPathWitnessGoodBandData

/-- Coded literal changed-path input for the two temporal column phases. -/
def Prop47Lemma410Prop48CanonicalCodedPathWitnessYTwoPhaseLowBandInputs
    (cWindow : ℕ) (witnessRate capCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (YCanonicalCodedPathWitnessGoodBandData
      cWindow m witnessRate capCoeff r a j)

/-! ## Strict rectangular temporal-column source cut -/

structure ForwardColumnCodedRectangularGoodBandData
    (cWindow m : ℕ) (ratioC capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (yLeftWinnerContextualFailure capCoeff m r a j) rawCode →
    ForwardColumnWinnerSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yLeftWinnerContextualFailure capCoeff m r a j)
      (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m yIndex r (alphaValue a))
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    yLeftWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).core.D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (yLeftWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m yIndex r (alphaValue a)

structure PrimedColumnCodedRectangularGoodBandData
    (cWindow m : ℕ) (ratioC capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  rawCode : Path → ℕ
  source : FailureCode
      (yRightWinnerContextualFailure capCoeff m r a j) rawCode →
    PrimedColumnWinnerSource m
  pathAtom_eq : ∀ eta, (source eta).pathAtom =
    lemma410RawCodeFiber rawCode eta.1
  remaining : ∀ eta,
    Equation447LengthSeparatedRectangularOptimalCategoricalPathWitnessBranchRemainingData
      cWindow m ratioC ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)
      (yRightWinnerContextualFailure capCoeff m r a j)
      (prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m yIndex r (alphaValue a))
      (source eta).pathAtom (source eta).profile
      (source eta).lazyVector (source eta).nextDirection
  failure_subset : ∀ eta,
    yRightWinnerContextualFailure capCoeff m r a j ∩
        (source eta).pathAtom ⊆
      (fun s ↦ ((source eta).lazyVector s,
        (source eta).nextDirection s)) ⁻¹'
        (((sourceProfileQEvent m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m
                (sourceBeta (alphaValue a) j))) ∩
              (remaining eta).core.D)) ×ˢ (Set.univ : Set Direction))
  theta_subset : ∀ eta,
    (yRightWinnerContextualFailure capCoeff m r a j ∩
      (source eta).pathAtom) ∩
        (fun s ↦ ((source eta).lazyVector s,
          (source eta).nextDirection s)) ⁻¹'
          (sourceProfileThetaUpTo cWindow m
            (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
            (source eta).profile ×ˢ (Set.univ : Set Direction)) ⊆
      prop45FailureEvent sourceCanonicalProfiles canonicalCStar
        m yIndex r (alphaValue a)

structure YCanonicalCodedRectangularGoodBandData
    (cWindow m : ℕ) (ratioC capCoeff : ℝ)
    (r : StageIndex) (a : AlphaIndex) (j : SourceBetaBandIndex) where
  forward : ForwardColumnCodedRectangularGoodBandData
    cWindow m ratioC capCoeff r a j
  backward : PrimedColumnCodedRectangularGoodBandData
    cWindow m ratioC capCoeff r a j

namespace YCanonicalCodedRectangularGoodBandData

variable {cWindow m : ℕ} {ratioC capCoeff : ℝ}
  {r : StageIndex} {a : AlphaIndex} {j : SourceBetaBandIndex}

noncomputable def toPathWitness
    (D : YCanonicalCodedRectangularGoodBandData
      cWindow m ratioC capCoeff r a j)
    (hC : 0 < ratioC)
    (hbinomial : ∀ q,
      Nat.ceil ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) ≤ q →
      ratioC ^ categoricalOptimalWitnessCount ratioC q ≤
        Real.exp (-categoricalOptimalRate ratioC * (q : ℝ)) *
          Nat.choose q (categoricalOptimalWitnessCount ratioC q)) :
    YCanonicalCodedPathWitnessGoodBandData cWindow m
      (categoricalOptimalRate ratioC) capCoeff r a j where
  forward :=
    { rawCode := D.forward.rawCode
      source := D.forward.source
      pathAtom_eq := D.forward.pathAtom_eq
      remaining := fun eta ↦ lemma410RectangularRemainingToPathWitness
        (D.forward.remaining eta) hC hbinomial
      failure_subset := by
        intro eta
        simpa only [lemma410RectangularRemainingToPathWitness_D] using
          D.forward.failure_subset eta
      theta_subset := D.forward.theta_subset }
  backward :=
    { rawCode := D.backward.rawCode
      source := D.backward.source
      pathAtom_eq := D.backward.pathAtom_eq
      remaining := fun eta ↦ lemma410RectangularRemainingToPathWitness
        (D.backward.remaining eta) hC hbinomial
      failure_subset := by
        intro eta
        simpa only [lemma410RectangularRemainingToPathWitness_D] using
          D.backward.failure_subset eta
      theta_subset := D.backward.theta_subset }

end YCanonicalCodedRectangularGoodBandData

def Prop47Lemma410Prop48CanonicalCodedRectangularYTwoPhaseLowBandInputs
    (cWindow : ℕ) (ratioC capCoeff : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (YCanonicalCodedRectangularGoodBandData
      cWindow m ratioC capCoeff r a j)

theorem codedPathWitnessYTwoPhaseLowBandInputs_of_rectangular
    (cWindow : ℕ) {ratioC capCoeff : ℝ} (hC : 0 < ratioC)
    (h : Prop47Lemma410Prop48CanonicalCodedRectangularYTwoPhaseLowBandInputs
      cWindow ratioC capCoeff) :
    Prop47Lemma410Prop48CanonicalCodedPathWitnessYTwoPhaseLowBandInputs
      cWindow (categoricalOptimalRate ratioC) capCoeff := by
  have hbin := eventually_optimal_binomial_layer_above_quarter_log_sq
    ratioC hC
  filter_upwards [h, hbin] with m hm hbm
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  exact ⟨D.toPathWitness hC hbm⟩

/-- The coded terminal phases give the low-band column candidate estimate. -/
theorem prop47Lemma410Prop48CodedPathWitness_y_lowBands
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalCodedPathWitnessYTwoPhaseLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (yCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  let cBase := witnessRate / 8
  have hcBase : 0 < cBase := by
    dsimp [cBase]
    positivity
  have hgood := eventually_sourceProp48NumericalAt cWindow hcBase
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num)
  have hbase := eventually_pathWitnessEquation447_error_absorb
    hwitnessRate (show (0 : ℝ) < 1 / 4 by norm_num)
  have hshift := eventually_prop48Rate_le_sourceBetaCandidateTail
    (rate := min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (d := 2 * d) (by positivity) (by
      dsimp [cBase] at hcompare ⊢
      nlinarith [hcompare])
  have habsorb := eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  have hcover :=
    eventually_fullCandidateFailure_subset_smallWinnerFailures_y
      hCsmall.le hgap
  filter_upwards [h, hgood, hbase, hshift, habsorb, hcover] with
      m hm hgoodM hbaseM hshiftM habsorbM hcoverM
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  have halpha : kappaOne ≤ sourceBeta (alphaValue a) j :=
    kappaOne_le_sourceBeta ha j
  have hAlpha : sourceBeta (alphaValue a) j ≤ (4 : ℝ) / 5 :=
    hj.trans (by norm_num)
  have hbaseM' :
      4 * (Real.exp (-witnessRate *
          ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2)) *
        (1 - Real.exp (-witnessRate))⁻¹) ≤
          Real.exp (-cBase * Real.log (m : ℝ) ^ 2) := by
    have hraw := hbaseM
      ((1 / 4 : ℝ) * Real.log (m : ℝ) ^ 2) (le_refl _)
    dsimp [cBase]
    convert hraw using 1 <;> ring
  let tailTwo := sourceBetaCandidateTail (2 * d) m
  have hbranches := D.measure_diff_le hgoodM hwitnessRate halpha hAlpha
    hbaseM' tailTwo (by simpa only [tailTwo] using hshiftM)
  rcases hbranches with ⟨hforward, hbackward⟩
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r (alphaValue a)
  have hcontextCover : yCandidateContextualFailure Cfull m r a j ⊆
      yLeftWinnerContextualFailure Csmall m r a j ∪
        yRightWinnerContextualFailure Csmall m r a j := by
    intro omega homega
    have hprefix : omega ∈
        hlozCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
            prefixPairingEvent m yIndex (stageNumber r + 1) :=
      ⟨homega.1, homega.2.1.1⟩
    rcases hcoverM r a ha j hprefix with hleft | hright
    · exact Or.inl ⟨hleft.1, homega.2⟩
    · exact Or.inr ⟨hright.1, homega.2⟩
  calc
    simpleRandomWalkLaw
        (yCandidateContextualFailure Cfull m r a j \ theta) ≤
      simpleRandomWalkLaw
        ((yLeftWinnerContextualFailure Csmall m r a j \ theta) ∪
          (yRightWinnerContextualFailure Csmall m r a j \ theta)) := by
        apply measure_mono
        intro omega homega
        rcases hcontextCover homega.1 with hleft | hright
        · exact Or.inl ⟨hleft, homega.2⟩
        · exact Or.inr ⟨hright, homega.2⟩
    _ ≤ simpleRandomWalkLaw
          (yLeftWinnerContextualFailure Csmall m r a j \ theta) +
        simpleRandomWalkLaw
          (yRightWinnerContextualFailure Csmall m r a j \ theta) :=
      measure_union_le _ _
    _ ≤ tailTwo + tailTwo := add_le_add
      (by simpa only [theta] using hforward)
      (by simpa only [theta] using hbackward)
    _ = 2 * sourceBetaCandidateTail (2 * d) m := by
      dsimp [tailTwo]
      ring
    _ ≤ sourceBetaCandidateTail d m := habsorbM

/-- High-band emptiness completes the coded column candidate estimate. -/
theorem prop47Lemma410Prop48CodedPathWitness_y
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalCodedPathWitnessYTwoPhaseLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      simpleRandomWalkLaw
          (yCandidateContextualFailure Cfull m r a j \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        sourceBetaCandidateTail d m := by
  have hlow := prop47Lemma410Prop48CodedPathWitness_y_lowBands cWindow
    hwitnessRate hCsmall hgap hd hcompare h
  have hCfull : 0 < Cfull := by linarith
  have hhigh :=
    eventually_hlozCandidateCapFailureEvent_eq_empty_highBands hCfull
  filter_upwards [hlow, hhigh] with m hlowM hhighM
  intro r a ha j
  by_cases hj : sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10
  · exact hlowM r a ha j hj
  · have hempty := hhighM r a ha j (lt_of_not_ge hj)
    rw [yCandidateContextualFailure, hempty, empty_inter, empty_diff,
      measure_empty]
    exact bot_le

/-- Coded column candidate tails and the planar post-hit race estimate give
the theta-free stretched-log bound. -/
theorem prop47Lemma410CodedPathWitnessStretchedExponential_y
    (cWindow : ℕ) {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalCodedPathWitnessYTwoPhaseLowBandInputs
      cWindow witnessRate Csmall) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m yIndex r (alphaValue a) \
            prop45FailureEvent sourceCanonicalProfiles canonicalCStar
              m yIndex r (alphaValue a)) ≤
        ENNReal.ofReal (Real.exp
          (-sourceLemma410AbsorptionConstant d *
            Real.log ((m : ℝ) + 1) ^ 2)) := by
  have htail := prop47Lemma410Prop48CodedPathWitness_y cWindow
    hwitnessRate hCsmall hgap hd hcompare h
  have hCfull : 0 < Cfull := by linarith
  have hsum := eventually_sourceBetaBand_sum_absorption hCfull.le hd
  filter_upwards [htail, eventually_sourceLemma410Radius_bounds, hsum,
      eventually_ge_atTop 2] with m htailM hRadius hsumM hm
  intro r a ha
  let alpha := alphaValue a
  let k := stageNumber r
  let window := sourceLemma410Window m alpha
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r alpha
  let P := yLemma410Context m r alpha \ theta
  have hk : 0 < k := by
    dsimp [k, stageNumber]
    omega
  have hcover : lemma410FailureEvent m yIndex r alpha \ theta ⊆
      ⋃ j : SourceBetaBandIndex,
        hlozLemma410BPrimeEvent window m k
          (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j) ∩ P := by
    intro omega homega
    have hraw := lemma410FailureEvent_subset_sourceBetaBand_cover
      m yIndex r (alphaValue a) hm ha homega.1
    rcases Set.mem_iUnion.mp hraw with ⟨j, hj⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, hj.1, ?_⟩
    refine ⟨?_, homega.2⟩
    exact ⟨⟨homega.1.1.1.1, homega.1.1.1.2⟩, homega.1.1.2⟩
  have hrace (j : SourceBetaBandIndex) :
      HasHLOZLemma410PostHitRaceEstimate simpleRandomWalkLaw window
        m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (fun _ ↦ sourceBetaRaceBound m alpha j) := by
    simpa only [sourceBetaRaceBound] using
      planar_hlozLemma410PostHitRaceEstimate_exp
        window m k (sourceBetaCandidateThreshold m alpha j)
          (sourceBetaRaceCount m alpha j)
          (sourceLemma410Radius m alpha) (hRadius a ha).1 (hRadius a ha).2
          (sourceLemma410Window_geometry m alpha)
  have hcap (j : SourceBetaBandIndex) :
      simpleRandomWalkLaw
          (hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap Cfull m alpha j) ∩ P) ≤
        sourceBetaCandidateTail d m := by
    have hj := htailM r a ha j
    have heq :
        hlozCandidateCapFailureEvent window m k
              (sourceBetaCandidateThreshold m alpha j)
              (sourceBetaCandidateCap Cfull m alpha j) ∩ P =
          yCandidateContextualFailure Cfull m r a j \ theta := by
      ext omega
      simp only [P, yCandidateContextualFailure, yLemma410Context,
        window, k, alpha, Set.mem_inter_iff, Set.mem_diff]
      tauto
    rw [heq]
    exact hj
  exact (measure_le_sum_candidateCapTail_add_race_of_band_cover
    simpleRandomWalkLaw
    (lemma410FailureEvent m yIndex r alpha \ theta) P
    (fun _ ↦ window) m k
    (sourceBetaCandidateThreshold m alpha)
    (sourceBetaRaceCount m alpha)
    (fun j ↦ sourceBetaCandidateCap Cfull m alpha j)
    (sourceBetaRaceBound m alpha)
    (fun _ ↦ sourceBetaCandidateTail d m)
    (by omega) hk hcover hrace hcap).trans (hsumM a ha)

/-- Proposition 4.5 pays the single column theta event after the coded
Proposition-4.8 estimate. -/
theorem prop47Lemma410Estimate_y_of_codedPathWitness_inputs
    (cWindow prop45Coeff : ℕ)
    {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalCodedPathWitnessYTwoPhaseLowBandInputs
      cWindow witnessRate Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo →
      simpleRandomWalkLaw
          (lemma410FailureEvent m yIndex r (alphaValue a)) ≤
        sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
  have hdiff := prop47Lemma410CodedPathWitnessStretchedExponential_y
    cWindow hwitnessRate hCsmall hgap hd hcompare h
  have herror := eventually_codedLemma410Absorption_le_exceptional hd
  filter_upwards [hdiff, hProp45, herror] with m hdiffM hthetaM herrorM
  intro r a ha
  let E := lemma410FailureEvent m yIndex r (alphaValue a)
  let theta := prop45FailureEvent sourceCanonicalProfiles canonicalCStar
    m yIndex r (alphaValue a)
  have hsplit : E ⊆ theta ∪ (E \ theta) := by
    intro omega homega
    by_cases htheta : omega ∈ theta
    · exact Or.inl htheta
    · exact Or.inr ⟨homega, htheta⟩
  calc
    simpleRandomWalkLaw E ≤
        simpleRandomWalkLaw theta + simpleRandomWalkLaw (E \ theta) :=
      (measure_mono hsplit).trans (measure_union_le _ _)
    _ ≤ sourceExceptionalRateWithPrefactor m prop45Coeff kappa +
        sourceExceptionalRateWithPrefactor m 1 kappa :=
      add_le_add (hthetaM yIndex r a ha) ((hdiffM r a ha).trans herrorM)
    _ = sourceExceptionalRateWithPrefactor m (prop45Coeff + 1) kappa := by
      simp only [sourceExceptionalRateWithPrefactor]
      push_cast
      ring

/-- The coded terminal source data supplies both column pairings after
reflection of the reunited `Y` event. -/
theorem prop47Lemma410EstimateYColumns_of_codedPathWitness_inputs
    (cWindow prop45Coeff : ℕ)
    {witnessRate Csmall Cfull d : ℝ}
    (hwitnessRate : 0 < witnessRate)
    (hCsmall : 0 < Csmall) (hgap : Csmall + 20 ≤ Cfull)
    (hd : 0 < d)
    (hcompare : 8 * d ≤
      min (witnessRate / 8)
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48CanonicalCodedPathWitnessYTwoPhaseLowBandInputs
      cWindow witnessRate Csmall)
    (hProp45 : Prop47Prop45Estimate sourceCanonicalProfiles canonicalCStar
      prop45Coeff) :
    Prop47Lemma410EstimateYColumns (prop45Coeff + 1) := by
  have hy := prop47Lemma410Estimate_y_of_codedPathWitness_inputs
    cWindow prop45Coeff hwitnessRate hCsmall hgap hd hcompare h hProp45
  filter_upwards [hy] with m hm
  intro i hi r a ha
  have hiCases : i = yIndex ∨ i = yIndex' := by
    fin_cases i <;> simp_all [yIndex, yIndex']
  rcases hiCases with rfl | rfl
  · exact hm r a ha
  · rw [simpleRandomWalkLaw_lemma410FailureEvent_yPrime_eq_y]
    exact hm r a ha

end Erdos1166.HLOZLemma410CodedAtoms
