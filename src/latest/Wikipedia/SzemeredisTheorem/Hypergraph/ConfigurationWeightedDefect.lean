import Wikipedia.SzemeredisTheorem.Hypergraph.CoarseConfigurationCounting

/-!
# Configuration-weighted defect estimates

The first coarse-configuration counting lemma bounds the square of a defect
contribution by the bare goodness threshold `β`.  Its Cauchy--Schwarz proof
actually retains the square mean of the remaining configuration weight.
Since every configuration factor is an atom indicator, that square mean is
exactly the remaining partial configuration count.

This file records the sharper estimate

```
defectContribution ^ 2 ≤ β * partialConfigurationCount (s.erase e).
```

It is useful for parameter hierarchies: a defect introduced while adjoining
a maximal face is charged relative to the already-counted lower
configuration, rather than against the ambient probability space.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Idempotence of configuration indicators -/

/-- A selected atom weight is idempotent. -/
theorem configurationFaceWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    configurationFaceWeight A e y ^ 2 =
      configurationFaceWeight A e y := by
  exact partitionAtomIndicator_sq _ _ _

/-- A product of selected atom indicators is itself idempotent. -/
theorem partialConfigurationWeight_sq
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) :
    partialConfigurationWeight A s x ^ 2 =
      partialConfigurationWeight A s x := by
  classical
  unfold partialConfigurationWeight
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro e he
  exact configurationFaceWeight_sq A e _

/-- The square mean of a partial configuration indicator is its partial
configuration count. -/
theorem mean_sq_partialConfigurationWeight_eq_count
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r)) :
    mean (fun x : Fin k → G =>
      partialConfigurationWeight A s x ^ 2) =
      partialConfigurationCount A s := by
  unfold partialConfigurationCount
  apply congrArg mean
  funext x
  exact partialConfigurationWeight_sq A s x

/-- Every partial configuration count is nonnegative. -/
theorem partialConfigurationCount_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r)) :
    0 ≤ partialConfigurationCount A s := by
  unfold partialConfigurationCount
  exact mean_nonneg
    (partialConfigurationWeight_nonneg A s)

/-! ## The mixed defect with its remaining-count factor -/

/-- Mixed goodness controls the localized square of a selected coarse
atom's boundary defect by `β`. -/
theorem mean_sq_mixedConfigurationDefect_localized_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (e : PositiveOrderedFace k r)
    (hβ : 0 ≤ β e.rank) :
    mean (fun x : Fin k → G =>
      (mixedConfigurationDefect P A e
          (orderedFaceTuple e.face x) *
        mixedConfigurationBoundaryIndicator P A e
          (orderedFaceTuple e.face x)) ^ 2) ≤
      β e.rank := by
  have hgoodLocal :=
    (hgood.atPositiveFace P A α β e).localized_defect
      (positiveFaceLowerLayer P.fine e)
      (positiveFaceLowerLayer P.coarse e)
      e.face
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face)
      (orderedFaceTuple e.face A.witness)
      (α e.rank) (β e.rank)
  have hmass :
      orderedBoundaryAtomMass
          (positiveFaceLowerLayer P.coarse e)
          e.face
          (orderedBoundaryAtomAt
            (positiveFaceLowerLayer P.coarse e)
            e.face
            (orderedFaceTuple e.face A.witness)) ≤
        1 :=
    orderedBoundaryAtomMass_le_one _ _ _
  calc
    mean (fun x : Fin k → G =>
        (mixedConfigurationDefect P A e
            (orderedFaceTuple e.face x) *
          mixedConfigurationBoundaryIndicator P A e
            (orderedFaceTuple e.face x)) ^ 2) =
        mean (fun y =>
          (mixedConfigurationDefect P A e y *
            mixedConfigurationBoundaryIndicator P A e y) ^ 2) := by
      exact mean_comp_orderedFaceTuple e.face
        (fun y =>
          (mixedConfigurationDefect P A e y *
            mixedConfigurationBoundaryIndicator P A e y) ^ 2)
    _ =
        orderedLocalizedAtomDefectSq
          (positiveFaceLowerLayer P.fine e)
          (positiveFaceLowerLayer P.coarse e)
          e.face
          (P.coarse.partition e.lowerRank.succ e.face)
          (A.atom e.lowerRank.succ e.face)
          (orderedBoundaryAtomAt
            (positiveFaceLowerLayer P.coarse e)
            e.face
            (orderedFaceTuple e.face A.witness)) :=
      mean_sq_mixedConfigurationDefect_mul_boundaryIndicator P A e
    _ ≤
        β e.rank *
          orderedBoundaryAtomMass
            (positiveFaceLowerLayer P.coarse e)
            e.face
            (orderedBoundaryAtomAt
              (positiveFaceLowerLayer P.coarse e)
              e.face
              (orderedFaceTuple e.face A.witness)) :=
      hgoodLocal
    _ ≤ β e.rank :=
      mul_le_of_le_one_right hβ hmass

/-- Sharpened mixed defect estimate retaining the exact count of the
remaining configuration. -/
theorem mixedConfigurationContribution_defect_sq_le_mul_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (hβ : 0 ≤ β e.rank) :
    configurationContribution A s e
        (mixedConfigurationDefect P A e) ^ 2 ≤
      β e.rank *
        partialConfigurationCount A (s.erase e) := by
  let u : (Fin k → G) → ℝ :=
    fun x =>
      mixedConfigurationDefect P A e
          (orderedFaceTuple e.face x) *
        mixedConfigurationBoundaryIndicator P A e
          (orderedFaceTuple e.face x)
  let v : (Fin k → G) → ℝ :=
    partialConfigurationWeight A (s.erase e)
  have hu :
      mean (fun x : Fin k → G => u x ^ 2) ≤
        β e.rank :=
    mean_sq_mixedConfigurationDefect_localized_le
      P A α β hgood e hβ
  have hv :
      mean (fun x : Fin k → G => v x ^ 2) =
        partialConfigurationCount A (s.erase e) :=
    mean_sq_partialConfigurationWeight_eq_count
      A (s.erase e)
  have hv0 :
      0 ≤ mean (fun x : Fin k → G => v x ^ 2) :=
    mean_nonneg fun x => sq_nonneg _
  calc
    configurationContribution A s e
        (mixedConfigurationDefect P A e) ^ 2 =
        mean (fun x : Fin k → G => u x * v x) ^ 2 := by
      rw [mixedConfigurationContribution_defect_eq_localized
        P A s hclosed e he]
    _ ≤
        mean (fun x : Fin k → G => u x ^ 2) *
          mean (fun x : Fin k → G => v x ^ 2) :=
      mean_mul_sq_le_product u v
    _ ≤
        β e.rank *
          mean (fun x : Fin k → G => v x ^ 2) :=
      mul_le_mul_of_nonneg_right hu hv0
    _ =
        β e.rank *
          partialConfigurationCount A (s.erase e) := by
      rw [hv]

/-- Square-root form of the configuration-weighted mixed defect estimate. -/
theorem abs_mixedConfigurationContribution_defect_le_sqrt_mul_count
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (hβ : 0 ≤ β e.rank) :
    |configurationContribution A s e
        (mixedConfigurationDefect P A e)| ≤
      Real.sqrt
        (β e.rank *
          partialConfigurationCount A (s.erase e)) := by
  have hcount :
      0 ≤ partialConfigurationCount A (s.erase e) :=
    partialConfigurationCount_nonneg A (s.erase e)
  have hproduct :
      0 ≤ β e.rank *
        partialConfigurationCount A (s.erase e) :=
    mul_nonneg hβ hcount
  apply
    (sq_le_sq₀
      (abs_nonneg
        (configurationContribution A s e
          (mixedConfigurationDefect P A e)))
      (Real.sqrt_nonneg _)).mp
  rw [sq_abs, Real.sq_sqrt hproduct]
  exact
    mixedConfigurationContribution_defect_sq_le_mul_count
      P A α β hgood s hclosed e he hβ

/-- The one-face mixed recurrence with its defect error scaled by the
already-counted remainder. -/
theorem abs_partialConfigurationCount_sub_mixedDensity_mul_le_sqrt
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsMixedGood P α β)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (s : Finset (PositiveOrderedFace k r))
    (hclosed : IsDownwardClosedPositiveFaces s)
    (e : PositiveOrderedFace k r) (he : e ∈ s)
    (hmax :
      ∀ f ∈ s.erase e, f.rank ≤ e.rank)
    (hβ : 0 ≤ β e.rank) :
    |partialConfigurationCount A s -
        mixedConfigurationCoarseDensity P A e *
          partialConfigurationCount A (s.erase e)| ≤
      Real.sqrt
          (β e.rank *
            partialConfigurationCount A (s.erase e)) +
        τ e.lowerRank := by
  have hdefect :
      |configurationContribution A s e
        (mixedConfigurationDefect P A e)| ≤
        Real.sqrt
          (β e.rank *
            partialConfigurationCount A (s.erase e)) :=
    abs_mixedConfigurationContribution_defect_le_sqrt_mul_count
      P A α β hgood s hclosed e he hβ
  have huniform :
      |configurationContribution A s e
        (mixedConfigurationUniform P A e)| ≤
          τ e.lowerRank :=
    abs_mixedConfigurationContribution_uniform_le
      P A τ hregular s e hmax
  rw [partialConfigurationCount_mixed_decompose
    P A s e he]
  calc
    |mixedConfigurationCoarseDensity P A e *
            partialConfigurationCount A (s.erase e) +
          configurationContribution A s e
            (mixedConfigurationDefect P A e) +
          configurationContribution A s e
            (mixedConfigurationUniform P A e) -
        mixedConfigurationCoarseDensity P A e *
          partialConfigurationCount A (s.erase e)| =
        |configurationContribution A s e
            (mixedConfigurationDefect P A e) +
          configurationContribution A s e
            (mixedConfigurationUniform P A e)| := by
      congr 1
      ring
    _ ≤
        |configurationContribution A s e
            (mixedConfigurationDefect P A e)| +
          |configurationContribution A s e
            (mixedConfigurationUniform P A e)| :=
      abs_add_le _ _
    _ ≤
        Real.sqrt
            (β e.rank *
              partialConfigurationCount A (s.erase e)) +
          τ e.lowerRank :=
      add_le_add hdefect huniform

end Wikipedia.SzemeredisTheorem
