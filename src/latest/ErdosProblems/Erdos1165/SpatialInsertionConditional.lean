import ErdosProblems.Erdos1165.SpatialInsertionFiber

open scoped BigOperators ENNReal

namespace Erdos1165

/-!
Finite probability laws supporting the spatial insertion fibre argument.

This file is deliberately separate from `SpatialInsertionFiber`: the latter is
the stable combinatorial core, while the results below identify its finite
weights with concrete cylinders of the canonical fair-step measure and then
normalize the away-from-the-distinguished-set domino totals.
-/

/-- The mass of a singleton under a finite fair increment block. -/
theorem fairBlock_singleton_mass (k : ℕ) (v : Fin k → Direction) :
    fairBlock k {v} = (1 / 4) ^ k := by
  rw [fairBlock, MeasureTheory.Measure.infinitePi_singleton_of_fintype]
  simp [fairStep_singleton]

/-- Every exact deterministic increment prefix is a cylinder of mass `4⁻ᵏ`. -/
theorem fairSteps_stepPrefix_singleton_mass (k : ℕ) (v : Fin k → Direction) :
    fairSteps { ω | stepPrefix k ω = v } = (1 / 4) ^ k := by
  calc
    fairSteps { ω | stepPrefix k ω = v } =
        (fairSteps.map (stepPrefix k)) {v} := by
      rw [MeasureTheory.Measure.map_apply (measurable_stepPrefix k)
        (MeasurableSet.singleton v)]
      rfl
    _ = fairBlock k {v} := by
      have heq : stepBlock 0 k = stepPrefix k := by
        funext ω j
        simp [stepBlock, stepPrefix]
      rw [← heq, fairSteps_map_stepBlock]
    _ = (1 / 4) ^ k := fairBlock_singleton_mass k v

end Erdos1165

namespace Erdos1165.SpatialInsertionFiber

open MeasureTheory
open LazyDecomposition PathInsertion

/-! ## A concrete cylinder realization under `fairSteps` -/

/-- Flatten adjacent two-step blocks back to their direction coordinates. -/
def flattenBlockVector {n : ℕ} (w : Fin n → Block) : Fin (2 * n) → Direction :=
  fun j ↦
    let k : Fin n := ⟨j.val / 2, by
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2
      omega⟩
    if j.val % 2 = 0 then (w k).1 else (w k).2

theorem flattenBlockVector_injective {n : ℕ} :
    Function.Injective (@flattenBlockVector n) := by
  intro u v huv
  funext k
  apply Prod.ext
  · have h := congrFun huv ⟨2 * k, by omega⟩
    simpa [flattenBlockVector] using h
  · have h := congrFun huv ⟨2 * k + 1, by omega⟩
    have hk : (2 * k.val + 1) / 2 = k.val := by omega
    simpa [flattenBlockVector, hk] using h

/-- The direction vector spelling an exact insertion code. -/
def insertionCodeDirections {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) : Fin (2 * (i + j)) → Direction :=
  flattenBlockVector fun k ↦
    (insertBlocks c).get ⟨k, by rw [insertBlocks_length]; exact k.isLt⟩

theorem insertionCodeDirections_injective (o : Orientation) (i j : ℕ) :
    Function.Injective (@insertionCodeDirections o i j) := by
  intro c d hcd
  apply insertBlocks_injective o i j
  apply List.ext_get
  · simp [insertBlocks_length]
  · intro n hn_c hn_d
    have hn : n < i + j := by simpa [insertBlocks_length] using hn_c
    have hv := flattenBlockVector_injective hcd
    exact congrFun hv ⟨n, hn⟩

/-- A single exact inserted-word cylinder has its expected mass under the
canonical fair-step measure. -/
theorem fairSteps_insertionCodeDirections_mass {o : Orientation} {i j : ℕ}
    (c : InsertionCode o i j) :
    fairSteps { ω | stepPrefix (2 * (i + j)) ω = insertionCodeDirections c } =
      (1 / 16 : ℝ≥0∞) ^ (i + j) := by
  rw [Erdos1165.fairSteps_stepPrefix_singleton_mass]
  rw [pow_mul]
  congr 1
  rw [one_div, one_div]
  exact (ENNReal.inv_pow (a := 4) (n := 2)).symm.trans (by norm_num)

/-- The finite union of insertion patterns with a fixed retained word and a
fixed total number of deleted blocks. -/
def fixedExternalTotalCylinder {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (j : ℕ) : Set StepPath :=
  ⋃ g : GapPattern i j,
    { ω | stepPrefix (2 * (i + j)) ω = insertionCodeDirections (g, r) }

/-- Direct evaluation of the fixed-external-word joint mass under
`fairSteps`. -/
theorem fairSteps_fixedExternalTotalCylinder
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (j : ℕ) :
    fairSteps (fixedExternalTotalCylinder r j) =
      (Fintype.card (GapPattern i j) : ℝ≥0∞) * (1 / 16 : ℝ≥0∞) ^ (i + j) := by
  classical
  let E : GapPattern i j → Set StepPath := fun g ↦
    { ω | stepPrefix (2 * (i + j)) ω = insertionCodeDirections (g, r) }
  have hmeas : ∀ g, MeasurableSet (E g) := fun g ↦
    measurableSet_eq_fun (measurable_stepPrefix _) measurable_const
  have hdis : Pairwise fun g h ↦ Disjoint (E g) (E h) := by
    intro g h hgh
    rw [Set.disjoint_left]
    intro ω hωg hωh
    apply hgh
    have hcode := insertionCodeDirections_injective o i j (hωg.symm.trans hωh)
    exact congrArg Prod.fst hcode
  change fairSteps (⋃ g, E g) = _
  rw [measure_iUnion hdis hmeas]
  simp_rw [show ∀ g, fairSteps (E g) = (1 / 16 : ℝ≥0∞) ^ (i + j) from
    fun g ↦ fairSteps_insertionCodeDirections_mass (g, r)]
  rw [tsum_fintype]
  simp

theorem fairSteps_fixedExternalTotalCylinder_eq_ofReal
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o) (j : ℕ) :
    fairSteps (fixedExternalTotalCylinder r j) =
      ENNReal.ofReal (fixedExternalJointMass i j) := by
  rw [fairSteps_fixedExternalTotalCylinder]
  unfold fixedExternalJointMass uniformBlockWordMass
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Fintype.card (GapPattern i j))]
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 16)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 16)]
  norm_num

/-! ## One-domino normalization -/

private theorem negBinomial_partialSum_ne_zero (a L : ℕ) (ha : 0 < a)
    (hL : 0 < L) :
    (∑ j ∈ Finset.range L,
      NegativeBinomial.mass (15 / 16 : ℝ) a j) ≠ 0 := by
  have hzero : 0 < NegativeBinomial.mass (15 / 16 : ℝ) a 0 :=
    NegativeBinomial.mass_pos (by norm_num) (by norm_num) ha 0
  have hle : NegativeBinomial.mass (15 / 16 : ℝ) a 0 ≤
      ∑ j ∈ Finset.range L, NegativeBinomial.mass (15 / 16 : ℝ) a j := by
    exact Finset.single_le_sum
      (fun j hj ↦ NegativeBinomial.mass_nonneg (by norm_num) (by norm_num) a j)
      (by simpa using hL)
  exact ne_of_gt (hzero.trans_le hle)

/-- Positivity of the finite conditioning event. -/
theorem fixedExternal_partialSum_ne_zero (a L : ℕ) (ha : 0 < a) (hL : 0 < L) :
    (∑ j ∈ Finset.range L, fixedExternalJointMass a j) ≠ 0 := by
  simp_rw [fixedExternalJointMass_factorization ha]
  rw [← Finset.mul_sum]
  exact mul_ne_zero (by simp [fixedExternalMarginalMass])
    (negBinomial_partialSum_ne_zero a L ha hL)

/-- Exact finite conditional law of one non-distinguished spatial domino. -/
theorem dominoTotal_truncatedConditionalMass
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (b : ExternalDomino x r)
    (ℓ : ℕ) (hℓ : ℓ < m - fixedExternalDominoMax x r b) :
    fixedExternalJointMass (dominoExternalMultiplicity x r b) ℓ /
        (∑ j ∈ Finset.range (m - fixedExternalDominoMax x r b),
          fixedExternalJointMass (dominoExternalMultiplicity x r b) j) =
      truncatedDominoMass x r m b ℓ := by
  let a := dominoExternalMultiplicity x r b
  let L := m - fixedExternalDominoMax x r b
  have ha : 0 < a := dominoExternalMultiplicity_pos x r b
  have hMarg : fixedExternalMarginalMass a ≠ 0 := by
    simp [fixedExternalMarginalMass]
  have hden :
      (∑ j ∈ Finset.range L, fixedExternalJointMass a j) =
        fixedExternalMarginalMass a *
          ∑ j ∈ Finset.range L, NegativeBinomial.mass (15 / 16 : ℝ) a j := by
    simp_rw [fixedExternalJointMass_factorization ha]
    rw [Finset.mul_sum]
  rw [fixedExternalJointMass_factorization ha, hden]
  rw [mul_div_mul_left _ _ hMarg]
  unfold truncatedDominoMass
  rw [if_pos hℓ]

/-- Indicator form of the one-domino conditional law. -/
theorem dominoTotal_truncatedConditionalMass_all
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (b : ExternalDomino x r)
    (ℓ : ℕ) :
    (if ℓ < m - fixedExternalDominoMax x r b then
        fixedExternalJointMass (dominoExternalMultiplicity x r b) ℓ
      else 0) /
        (∑ j ∈ Finset.range (m - fixedExternalDominoMax x r b),
          fixedExternalJointMass (dominoExternalMultiplicity x r b) j) =
      truncatedDominoMass x r m b ℓ := by
  by_cases hℓ : ℓ < m - fixedExternalDominoMax x r b
  · rw [if_pos hℓ]
    exact dominoTotal_truncatedConditionalMass x r m b ℓ hℓ
  · rw [if_neg hℓ]
    simp [truncatedDominoMass, hℓ]

/-! ## Finite product disintegration -/

/-- Spatial dominoes away from the distinguished set. -/
abbrev AwayDomino {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (D : Finset Point) :=
  {b : ExternalDomino x r // b.1 ∉ D}

/-- Each domino total is intrinsically bounded by its endpoint cutoff. -/
abbrev TruncatedDominoTotals {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point) :=
  (b : AwayDomino x r D) → Fin (m - fixedExternalDominoMax x r b.1)

/-- Joint fixed-external-word mass of the away-domino totals. -/
noncomputable def truncatedTotalsJointMass {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (ℓ : TruncatedDominoTotals x r m D) : ℝ :=
  ∏ b : AwayDomino x r D,
    fixedExternalJointMass (dominoExternalMultiplicity x r b.1) (ℓ b)

/-- The normalizing mass is nonzero whenever a truncated total vector exists. -/
theorem truncatedTotals_conditioningMass_ne_zero
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (ℓ : TruncatedDominoTotals x r m D) :
    (∑ z : TruncatedDominoTotals x r m D,
      truncatedTotalsJointMass x r m D z) ≠ 0 := by
  classical
  unfold truncatedTotalsJointMass
  have hden := Finset.prod_univ_sum
    (fun b : AwayDomino x r D ↦
      (Finset.univ : Finset (Fin (m - fixedExternalDominoMax x r b.1))))
    (fun b j ↦ fixedExternalJointMass
      (dominoExternalMultiplicity x r b.1) (j : ℕ))
  rw [Fintype.piFinset_univ] at hden
  rw [← hden]
  apply Finset.prod_ne_zero_iff.mpr
  intro b _
  have hL : 0 < m - fixedExternalDominoMax x r b.1 := by
    exact Nat.pos_of_ne_zero (by
      intro hzero
      have := (ℓ b).isLt
      omega)
  simpa only [Fin.sum_univ_eq_sum_range] using
    fixedExternal_partialSum_ne_zero
      (dominoExternalMultiplicity x r b.1)
      (m - fixedExternalDominoMax x r b.1)
      (dominoExternalMultiplicity_pos x r b.1) hL

/-- Exact finite disintegration after fixing the external trace and imposing
the endpoint cutoffs away from `D`: the spatial-domino totals are independent,
and each has exactly the HLOZ truncated negative-binomial mass. -/
theorem truncatedTotals_conditional_factorization
    {o : Orientation} {i : ℕ} (x : Point)
    (r : Fin i → RetainedBlock o) (m : ℕ) (D : Finset Point)
    (ℓ : TruncatedDominoTotals x r m D) :
    truncatedTotalsJointMass x r m D ℓ /
        (∑ z : TruncatedDominoTotals x r m D,
          truncatedTotalsJointMass x r m D z) =
      ∏ b : AwayDomino x r D, truncatedDominoMass x r m b.1 (ℓ b) := by
  classical
  unfold truncatedTotalsJointMass
  have hden := Finset.prod_univ_sum
    (fun b : AwayDomino x r D ↦
      (Finset.univ : Finset (Fin (m - fixedExternalDominoMax x r b.1))))
    (fun b j ↦ fixedExternalJointMass
      (dominoExternalMultiplicity x r b.1) (j : ℕ))
  rw [Fintype.piFinset_univ] at hden
  rw [hden.symm]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro b _
  simpa only [Fin.sum_univ_eq_sum_range] using
    dominoTotal_truncatedConditionalMass x r m b.1 (ℓ b) (ℓ b).isLt

end Erdos1165.SpatialInsertionFiber
