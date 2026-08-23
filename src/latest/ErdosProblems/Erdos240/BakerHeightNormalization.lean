/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.BakerParameters
import ErdosProblems.Erdos240.Kummer
import ErdosProblems.Erdos240.RationalPrimeBaker
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.NodupEquivFin
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Height normalization and distinguished-last reindexing

This file supplies the finite bookkeeping needed to apply the
van der Poorten--Loxton theorem to a fixed family of old rational primes and
one varying fresh prime.  The old indices are sorted by their normalized
heights, while the varying prime is kept literally in the final coordinate.
No constant introduced here depends on the varying prime.
-/

namespace Erdos240.BakerHeightNormalization

open scoped BigOperators

noncomputable section

universe u

variable {ι : Type u} [Fintype ι]

/-- Height floor used by van der Poorten--Loxton. -/
noncomputable def normalizedPrimeHeight (p : ℕ) : ℝ :=
  max (Real.exp (Real.exp 1)) ((p : ℝ) + 1)

/-- Product of the fixed old normalized heights.  Unlike
`VDPLParameters.fixedHeightProduct`, this definition visibly takes no varying
prime argument. -/
noncomputable def oldFamilyHeightProduct (old : ι → ℕ) : ℝ :=
  ∏ i, normalizedPrimeHeight (old i)

/-- A height-absorption constant depending only on the fixed old family. -/
noncomputable def oldFamilyHeightConstant (old : ι → ℕ) : ℝ :=
  4 + Real.log (oldFamilyHeightProduct old) / Real.log 2

theorem one_le_normalizedPrimeHeight (p : ℕ) :
    1 ≤ normalizedPrimeHeight p := by
  have hone : (1 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h := Real.exp_le_exp.mpr (Real.exp_pos 1).le
    simpa only [Real.exp_zero] using h
  exact hone.trans (le_max_left _ _)

theorem one_le_oldFamilyHeightProduct (old : ι → ℕ) :
    1 ≤ oldFamilyHeightProduct old := by
  unfold oldFamilyHeightProduct
  exact Finset.one_le_prod fun i _ ↦ one_le_normalizedPrimeHeight (old i)

theorem oldFamilyHeightConstant_pos (old : ι → ℕ) :
    0 < oldFamilyHeightConstant old := by
  unfold oldFamilyHeightConstant
  have hlog : 0 ≤ Real.log (oldFamilyHeightProduct old) :=
    Real.log_nonneg (one_le_oldFamilyHeightProduct old)
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

/-- The old indices, sorted by their normalized heights. -/
noncomputable abbrev oldIndexOrder (P : VDPLParameters ι) : LinearOrder ι :=
  LinearOrder.lift' P.old P.old_injective

/-- The old indices, sorted by the numerical values of their primes.  Since
`x ↦ max (exp (exp 1)) x` is monotone, this is also a nondecreasing-height
ordering. -/
noncomputable def sortedOldList (P : VDPLParameters ι) : List ι :=
  letI : LinearOrder ι := oldIndexOrder P
  Finset.univ.sort

@[simp] theorem length_sortedOldList (P : VDPLParameters ι) :
    (sortedOldList P).length = Fintype.card ι := by
  simp [sortedOldList]

theorem nodup_sortedOldList (P : VDPLParameters ι) :
    (sortedOldList P).Nodup := by
  exact Finset.sort_nodup _ _

theorem mem_sortedOldList (P : VDPLParameters ι) (i : ι) :
    i ∈ sortedOldList P := by
  simp [sortedOldList]

/-- The equivalence which enumerates the old indices in nondecreasing height
order. -/
noncomputable def sortedOldEquiv (P : VDPLParameters ι) :
    Fin (Fintype.card ι) ≃ ι := by
  classical
  exact (finCongr (length_sortedOldList P).symm).trans
    ((nodup_sortedOldList P).getEquivOfForallMemList _ (mem_sortedOldList P))

/-- The old primes in nondecreasing height order. -/
noncomputable def sortedOldPrime (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι)) : ℕ :=
  P.old (sortedOldEquiv P j)

/-- The old normalized heights in nondecreasing order. -/
noncomputable def sortedOldHeight (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι)) : ℝ :=
  P.oldHeight (sortedOldEquiv P j)

/-- The old coefficients reindexed compatibly with `sortedOldPrime`. -/
noncomputable def sortedOldCoeff (P : VDPLParameters ι) (c : ι → ℤ)
    (j : Fin (Fintype.card ι)) : ℤ :=
  c (sortedOldEquiv P j)

theorem monotone_sortedOldPrime (P : VDPLParameters ι) :
    Monotone (sortedOldPrime P) := by
  intro i j hij
  letI : LinearOrder ι := oldIndexOrder P
  let i' : Fin (sortedOldList P).length :=
    finCongr (length_sortedOldList P).symm i
  let j' : Fin (sortedOldList P).length :=
    finCongr (length_sortedOldList P).symm j
  have hij' : i' ≤ j' := by
    exact hij
  have hpair : List.Pairwise (fun x y : ι ↦ x ≤ y) (sortedOldList P) := by
    simpa [sortedOldList] using
      (Finset.pairwise_sort (Finset.univ : Finset ι) (fun x y : ι ↦ x ≤ y))
  have hget := hpair.rel_get_of_le hij'
  change P.old ((sortedOldList P).get i') ≤
    P.old ((sortedOldList P).get j') at hget
  change P.old (sortedOldEquiv P i) ≤ P.old (sortedOldEquiv P j)
  simpa [sortedOldEquiv, i', j'] using hget

theorem monotone_sortedOldHeight (P : VDPLParameters ι) :
    Monotone (sortedOldHeight P) := by
  intro i j hij
  unfold sortedOldHeight VDPLParameters.oldHeight
  apply max_le_max le_rfl
  have hcast : (P.old (sortedOldEquiv P i) : ℝ) ≤
      P.old (sortedOldEquiv P j) := by
    exact_mod_cast monotone_sortedOldPrime P hij
  simpa [add_comm] using add_le_add_right hcast 1

theorem sortedOldPrime_prime (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι)) : (sortedOldPrime P j).Prime :=
  P.old_prime (sortedOldEquiv P j)

theorem injective_sortedOldPrime (P : VDPLParameters ι) :
    Function.Injective (sortedOldPrime P) :=
  P.old_injective.comp (sortedOldEquiv P).injective

theorem sourceHeight_le_sortedOldHeight (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι)) :
    Real.exp (Real.exp 1) ≤ sortedOldHeight P j :=
  P.sourceHeight_le_oldHeight (sortedOldEquiv P j)

theorem one_le_log_log_sortedOldHeight (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι)) :
    1 ≤ Real.log (Real.log (sortedOldHeight P j)) :=
  P.one_le_log_log_oldHeight (sortedOldEquiv P j)

/-- The complete source family, with the varying prime literally in the last
coordinate. -/
noncomputable def sourcePrime (P : VDPLParameters ι) :
    Fin (Fintype.card ι + 1) → ℕ :=
  Fin.lastCases P.newPrime (sortedOldPrime P)

/-- Coefficients of the complete source family, with `d` literally in the
last coordinate. -/
noncomputable def sourceCoeff (P : VDPLParameters ι) (c : ι → ℤ) (d : ℤ) :
    Fin (Fintype.card ι + 1) → ℤ :=
  Fin.lastCases d (sortedOldCoeff P c)

/-- Source heights in the same order.  The final height is deliberately
`newHeight`, not merely `varyingHeight`, so that it dominates every fixed old
height while retaining a uniform logarithmic bound in the varying prime. -/
noncomputable def sourceHeight (P : VDPLParameters ι) :
    Fin (Fintype.card ι + 1) → ℝ :=
  Fin.lastCases P.newHeight (sortedOldHeight P)

@[simp] theorem sourcePrime_castSucc (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι)) :
    sourcePrime P j.castSucc = sortedOldPrime P j := by
  simp [sourcePrime]

@[simp] theorem sourcePrime_last (P : VDPLParameters ι) :
    sourcePrime P (Fin.last (Fintype.card ι)) = P.newPrime := by
  simp [sourcePrime]

@[simp] theorem sourceCoeff_castSucc (P : VDPLParameters ι) (c : ι → ℤ)
    (d : ℤ) (j : Fin (Fintype.card ι)) :
    sourceCoeff P c d j.castSucc = c (sortedOldEquiv P j) := by
  simp [sourceCoeff, sortedOldCoeff]

@[simp] theorem sourceCoeff_last (P : VDPLParameters ι) (c : ι → ℤ)
    (d : ℤ) :
    sourceCoeff P c d (Fin.last (Fintype.card ι)) = d := by
  simp [sourceCoeff]

@[simp] theorem sourceHeight_castSucc (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι)) :
    sourceHeight P j.castSucc = sortedOldHeight P j := by
  simp [sourceHeight]

@[simp] theorem sourceHeight_last (P : VDPLParameters ι) :
    sourceHeight P (Fin.last (Fintype.card ι)) = P.newHeight := by
  simp [sourceHeight]

theorem sourceHeight_last_eq_oldProduct_mul_normalizedPrimeHeight
    (P : VDPLParameters ι) :
    sourceHeight P (Fin.last (Fintype.card ι)) =
      oldFamilyHeightProduct P.old * normalizedPrimeHeight P.newPrime := by
  simp [VDPLParameters.newHeight, VDPLParameters.fixedHeightProduct,
    VDPLParameters.varyingHeight, VDPLParameters.oldHeight,
    oldFamilyHeightProduct, normalizedPrimeHeight]

theorem sourcePrime_prime (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι + 1)) : (sourcePrime P j).Prime := by
  refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
  · simpa using P.new_prime
  · simpa using sortedOldPrime_prime P j₀

/-- The source prime family is pairwise distinct; this includes distinctness
between every old prime and the varying final prime. -/
theorem injective_sourcePrime (P : VDPLParameters ι) :
    Function.Injective (sourcePrime P) := by
  intro i
  refine Fin.lastCases ?_ (fun i₀ ↦ ?_) i
  · intro j
    refine Fin.lastCases (fun _ ↦ rfl) (fun j₀ h ↦ ?_) j
    exfalso
    exact P.new_fresh (sortedOldEquiv P j₀) (by
      simpa [sortedOldPrime] using h.symm)
  · intro j
    refine Fin.lastCases (fun h ↦ ?_) (fun j₀ h ↦ ?_) j
    · exfalso
      exact P.new_fresh (sortedOldEquiv P i₀) (by
        simpa [sortedOldPrime] using h)
    · have hij : i₀ = j₀ := injective_sortedOldPrime P (by simpa using h)
      subst j₀
      rfl

theorem pairwise_ne_sourcePrime (P : VDPLParameters ι) :
    Pairwise fun i j : Fin (Fintype.card ι + 1) ↦
      sourcePrime P i ≠ sourcePrime P j :=
  (injective_sourcePrime P).pairwise_ne

theorem oldHeight_le_sourceLastHeight (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι)) :
    sourceHeight P j.castSucc ≤
      sourceHeight P (Fin.last (Fintype.card ι)) := by
  simp only [sourceHeight_castSucc, sourceHeight_last, sortedOldHeight]
  exact P.oldHeight_le_newHeight (sortedOldEquiv P j)

theorem sourceHeight_floor (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι + 1)) :
    Real.exp (Real.exp 1) ≤ sourceHeight P j := by
  refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
  · simpa using
      P.sourceHeight_le_varyingHeight.trans P.varyingHeight_le_newHeight
  · simpa using sourceHeight_le_sortedOldHeight P j₀

theorem one_le_log_log_sourceHeight (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι + 1)) :
    1 ≤ Real.log (Real.log (sourceHeight P j)) := by
  refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
  · simpa using P.one_le_log_log_newHeight
  · simpa using one_le_log_log_sortedOldHeight P j₀

theorem sourcePrime_cast_le_sourceHeight (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι + 1)) :
    (sourcePrime P j : ℝ) ≤ sourceHeight P j := by
  refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
  · simpa only [sourcePrime_last, sourceHeight_last] using
      (P.newPrime_cast_lt_varyingHeight.trans_le
        P.varyingHeight_le_newHeight).le
  · simp only [sourcePrime_castSucc, sourceHeight_castSucc, sortedOldPrime,
      sortedOldHeight]
    exact (P.old_cast_lt_oldHeight (sortedOldEquiv P j₀)).le

/-- The source-correct strict height inequality.  This is why the normalized
heights use `p + 1` rather than `p`: the corrigendum requires strict
`|log α_j| < log A_j`, not merely a weak upper bound. -/
theorem sourcePrime_cast_lt_sourceHeight (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι + 1)) :
    (sourcePrime P j : ℝ) < sourceHeight P j := by
  refine Fin.lastCases ?_ (fun j₀ ↦ ?_) j
  · simpa only [sourcePrime_last, sourceHeight_last] using
      P.newPrime_cast_lt_varyingHeight.trans_le P.varyingHeight_le_newHeight
  · simpa only [sourcePrime_castSucc, sourceHeight_castSucc, sortedOldPrime,
      sortedOldHeight] using P.old_cast_lt_oldHeight (sortedOldEquiv P j₀)

theorem log_sourcePrime_le_log_sourceHeight (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι + 1)) :
    Real.log (sourcePrime P j : ℝ) ≤ Real.log (sourceHeight P j) := by
  have hp : 0 < (sourcePrime P j : ℝ) := by
    exact_mod_cast (sourcePrime_prime P j).pos
  exact Real.log_le_log hp (sourcePrime_cast_le_sourceHeight P j)

theorem log_sourcePrime_lt_log_sourceHeight (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι + 1)) :
    Real.log (sourcePrime P j : ℝ) < Real.log (sourceHeight P j) := by
  have hp : 0 < (sourcePrime P j : ℝ) := by
    exact_mod_cast (sourcePrime_prime P j).pos
  have hA : 0 < sourceHeight P j :=
    (Real.exp_pos (Real.exp 1)).trans_le (sourceHeight_floor P j)
  exact Real.strictMonoOn_log hp hA (sourcePrime_cast_lt_sourceHeight P j)

theorem abs_log_sourcePrime_lt_log_sourceHeight (P : VDPLParameters ι)
    (j : Fin (Fintype.card ι + 1)) :
    |Real.log (sourcePrime P j : ℝ)| < Real.log (sourceHeight P j) := by
  have hlog : 0 < Real.log (sourcePrime P j : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (sourcePrime_prime P j).one_lt)
  rw [abs_of_pos hlog]
  exact log_sourcePrime_lt_log_sourceHeight P j

/-- The full source height family is nondecreasing and has its varying height
in the final coordinate. -/
theorem monotone_sourceHeight (P : VDPLParameters ι) :
    Monotone (sourceHeight P) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i₀, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨j₀, rfl⟩ | rfl
    · simpa using monotone_sortedOldHeight P (by simpa using hij)
    · exact oldHeight_le_sourceLastHeight P i₀
  · have hj : j = Fin.last (Fintype.card ι) :=
      le_antisymm (Fin.le_last j) hij
    subst j
    exact le_rfl

/-- The visible varying-height factor is bounded by a fixed-old-family
constant times `log p`.  The factor `heightConstant` depends only on the old
heights, never on the varying prime. -/
theorem log_sourceLastHeight_le_heightConstant_mul_log_newPrime
    (P : VDPLParameters ι) :
    Real.log (sourceHeight P (Fin.last (Fintype.card ι))) ≤
      P.heightConstant * Real.log (P.newPrime : ℝ) := by
  simpa using P.log_newHeight_le_heightConstant_mul_log_newPrime

theorem fixedHeightProduct_eq_oldFamilyHeightProduct (P : VDPLParameters ι) :
    P.fixedHeightProduct = oldFamilyHeightProduct P.old := by
  rfl

theorem heightConstant_eq_oldFamilyHeightConstant (P : VDPLParameters ι) :
    P.heightConstant = oldFamilyHeightConstant P.old := by
  rfl

/-- Uniform version of the final-height estimate: the displayed multiplier
is syntactically a function of the old family alone. -/
theorem log_sourceLastHeight_le_oldFamilyHeightConstant_mul_log_newPrime
    (P : VDPLParameters ι) :
    Real.log (sourceHeight P (Fin.last (Fintype.card ι))) ≤
      oldFamilyHeightConstant P.old * Real.log (P.newPrime : ℝ) := by
  rw [← heightConstant_eq_oldFamilyHeightConstant P]
  exact log_sourceLastHeight_le_heightConstant_mul_log_newPrime P

/-- The complete source logarithmic form. -/
noncomputable def sourceLogForm (P : VDPLParameters ι)
    (c : ι → ℤ) (d : ℤ) : ℝ :=
  ∑ j, (sourceCoeff P c d j : ℝ) * Real.log (sourcePrime P j : ℝ)

/-- Reindexing and adjoining the distinguished last coordinate preserve the
logarithmic form exactly. -/
theorem sourceLogForm_eq_indexedRationalLogForm (P : VDPLParameters ι)
    (c : ι → ℤ) (d : ℤ) :
    sourceLogForm P c d =
      RationalPrimeBaker.indexedRationalLogForm P.old P.newPrime c d := by
  rw [sourceLogForm, Fin.sum_univ_castSucc]
  simp only [sourceCoeff_castSucc, sourcePrime_castSucc, sourceCoeff_last,
    sourcePrime_last, RationalPrimeBaker.indexedRationalLogForm]
  congr 1
  exact Fintype.sum_equiv (sortedOldEquiv P)
    (fun j ↦ (c (sortedOldEquiv P j) : ℝ) *
      Real.log (P.old (sortedOldEquiv P j) : ℝ))
    (fun i ↦ (c i : ℝ) * Real.log (P.old i : ℝ))
    (fun _ ↦ rfl)

/-- The last source coefficient is exactly the distinguished coefficient. -/
theorem sourceCoeff_last_ne_zero (P : VDPLParameters ι) (c : ι → ℤ)
    {d : ℤ} (hd : d ≠ 0) :
    sourceCoeff P c d (Fin.last (Fintype.card ι)) ≠ 0 := by
  simpa using hd

section ReindexingInvariants

variable {κ R M Ω : Type*}

/-- Reindexing a family by an equivalence does not change its range. -/
theorem range_comp_equiv (e : κ ≃ ι) (v : ι → Ω) :
    Set.range (v ∘ e) = Set.range v := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨e j, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, by simp⟩

/-- Consequently, adjoining a reindexed radical family gives literally the
same intermediate field. -/
theorem adjoin_range_comp_equiv [Field R] [Field Ω] [Algebra R Ω]
    (e : κ ≃ ι) (v : ι → Ω) :
    IntermediateField.adjoin R (Set.range (v ∘ e)) =
      IntermediateField.adjoin R (Set.range v) := by
  rw [range_comp_equiv e v]

/-- The degree statement used by Kummer is invariant under any finite
reindexing. -/
theorem finrank_adjoin_range_comp_equiv [Fintype κ]
    [Field R] [Field Ω] [Algebra R Ω]
    (e : κ ≃ ι) (v : ι → Ω) :
    Module.finrank R (IntermediateField.adjoin R (Set.range (v ∘ e))) =
      Module.finrank R (IntermediateField.adjoin R (Set.range v)) := by
  rw [adjoin_range_comp_equiv e v]

/-- Linear independence is likewise unchanged by an equivalence of the
index type. -/
theorem linearIndependent_comp_equiv_iff [Semiring R] [AddCommMonoid M]
    [Module R M] (e : κ ≃ ι) (v : ι → M) :
    LinearIndependent R (v ∘ e) ↔ LinearIndependent R v :=
  linearIndependent_equiv e

end ReindexingInvariants

/-- Applying the checked rational-prime Kummer theorem after the
distinguished-last reindexing gives exactly the source radical degree.  Thus
the height ordering does not change the radical hypothesis of VDPL Theorem
1. -/
theorem finrank_adjoin_source_thirteenthRoots
    (P : VDPLParameters ι)
    {Ω : Type u} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (beta : Fin (Fintype.card ι + 1) → Ω)
    (hbeta : ∀ j, beta j ^ 13 =
      algebraMap ℚ Ω (sourcePrime P j : ℚ)) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (Set.range beta)) =
      13 ^ (Fintype.card ι + 1) := by
  simpa using Kummer.finrank_adjoin_thirteenthRoots_primes_rat
    (sourcePrime P) (sourcePrime_prime P) (injective_sourcePrime P) beta hbeta

#print axioms monotone_sourceHeight
#print axioms abs_log_sourcePrime_lt_log_sourceHeight
#print axioms log_sourceLastHeight_le_oldFamilyHeightConstant_mul_log_newPrime
#print axioms sourceLogForm_eq_indexedRationalLogForm
#print axioms finrank_adjoin_source_thirteenthRoots

end

end Erdos240.BakerHeightNormalization
