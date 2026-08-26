import ErdosProblems.Erdos1002.GaussUnmarkedFactorialLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Deterministic counting of chronological short-gap tuples

This module discharges the purely combinatorial `shortTupleFamily` input in
the unmarked factorial-moment theorem. A chronological tuple which is not
`gap`-separated has a pair of coordinates at distance less than `gap`.
After fixing that pair, delete the later coordinate and record only its
difference from the earlier coordinate. This injects the bad-pair family
into a type of cardinality `gap * L^(r-1)`.
-/

open Filter Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- Chronological tuples for which the fixed pair `(i,k)` violates the
prescribed separation. -/
def ChronologicalShortPair {r L : ℕ} (gap : ℕ) (i k : Fin r) :=
  {t : Fin r → Fin L //
    IsChronologicalTuple t ∧ i < k ∧ ¬(t i).1 + gap ≤ (t k).1}

noncomputable instance chronologicalShortPairFintype
    {r L gap : ℕ} {i k : Fin r} :
    Fintype (ChronologicalShortPair (L := L) gap i k) :=
  by
    classical
    unfold ChronologicalShortPair
    infer_instance

/-- Delete one coordinate from a finite tuple. -/
def tupleWithoutCoordinate {r L : ℕ} (k : Fin r) :=
  {j : Fin r // j ≠ k} → Fin L

noncomputable instance tupleWithoutCoordinateFintype
    {r L : ℕ} {k : Fin r} :
    Fintype (tupleWithoutCoordinate (L := L) k) := by
  classical
  unfold tupleWithoutCoordinate
  infer_instance

/-- Code a fixed bad pair by the short difference and all coordinates except
the later one. -/
def chronologicalShortPairCode {r L gap : ℕ} {i k : Fin r}
    (t : ChronologicalShortPair (L := L) gap i k) :
    Fin gap × tupleWithoutCoordinate (L := L) k :=
  (⟨(t.1 k).1 - (t.1 i).1, by
      have hlt : (t.1 k).1 < (t.1 i).1 + gap := Nat.lt_of_not_ge t.2.2.2
      have hchron := t.2.1 i k t.2.2.1
      omega⟩,
    fun j ↦ t.1 j.1)

theorem chronologicalShortPairCode_injective
    {r L gap : ℕ} {i k : Fin r} :
    Function.Injective
      (chronologicalShortPairCode (L := L) (gap := gap) (i := i) (k := k)) := by
  intro t u htu
  apply Subtype.ext
  funext j
  by_cases hj : j = k
  · subst j
    have hpairFirst := congrArg (fun z => z.1.1) htu
    have hpairSecond := congrArg (fun z => z.2) htu
    have hik : i ≠ k := ne_of_lt t.2.2.1
    have hi := congrFun hpairSecond ⟨i, hik⟩
    have htik := t.2.1 i k t.2.2.1
    have huik := u.2.1 i k u.2.2.1
    apply Fin.ext
    change (t.1 k).1 - (t.1 i).1 =
      (u.1 k).1 - (u.1 i).1 at hpairFirst
    change t.1 i = u.1 i at hi
    have hiVal : (t.1 i).1 = (u.1 i).1 := congrArg Fin.val hi
    omega
  · have hpairSecond := congrArg (fun z => z.2) htu
    exact congrFun hpairSecond ⟨j, hj⟩

/-- A fixed ordered short pair has at most `gap * L^(r-1)` realizations. -/
theorem card_chronologicalShortPair_le
    {r L : ℕ} (gap : ℕ) (i k : Fin r) :
    Fintype.card (ChronologicalShortPair (L := L) gap i k) ≤
      gap * L ^ (r - 1) := by
  classical
  have hcard := Fintype.card_le_of_injective
    (chronologicalShortPairCode (L := L) (gap := gap) (i := i) (k := k))
    chronologicalShortPairCode_injective
  simpa [tupleWithoutCoordinate, Fintype.card_prod, Fintype.card_fun,
    Set.card_ne_eq] using! hcard

/-- A failure of deterministic separation has a concrete ordered witnessing
pair.  Keeping this elementary quantifier step explicit makes the later
counting map independent of any implicit choice convention. -/
theorem exists_short_pair_of_not_separated
    {r L gap : ℕ} {t : Fin r → Fin L}
    (ht : ¬ IsSeparatedTuple gap t) :
    ∃ i k : Fin r, i < k ∧ ¬(t i).1 + gap ≤ (t k).1 := by
  by_contra h
  push_neg at h
  exact ht (fun i k hik ↦ h i k hik)

/-- A witness remembers a bad ordered pair together with the entire
chronological tuple. -/
def ChronologicalShortWitness (r L gap : ℕ) :=
  Σ i : Fin r, Σ k : Fin r, ChronologicalShortPair (L := L) gap i k

noncomputable instance chronologicalShortWitnessFintype
    {r L gap : ℕ} : Fintype (ChronologicalShortWitness r L gap) := by
  classical
  unfold ChronologicalShortWitness
  infer_instance

/-- Select one bad pair from a member of a chronological short family. -/
noncomputable def chronologicalShortWitnessOfMem
    {r L gap : ℕ} {tuples : Finset (Fin r → Fin L)}
    (hchronological : ∀ t ∈ tuples, IsChronologicalTuple t)
    (t : {t // t ∈ shortTupleFamily gap tuples}) :
    ChronologicalShortWitness r L gap := by
  classical
  have htmem := (mem_shortTupleFamily_iff.mp t.2).1
  have htshort := (mem_shortTupleFamily_iff.mp t.2).2
  have hex := exists_short_pair_of_not_separated htshort
  let i : Fin r := Classical.choose hex
  have hi : ∃ k : Fin r,
      i < k ∧ ¬(t.1 i).1 + gap ≤ (t.1 k).1 := Classical.choose_spec hex
  let k : Fin r := Classical.choose hi
  have hk : i < k ∧ ¬(t.1 i).1 + gap ≤ (t.1 k).1 := Classical.choose_spec hi
  have hik := hk.1
  have hbad := hk.2
  exact ⟨i, k, ⟨t.1, hchronological t.1 htmem, hik, hbad⟩⟩

@[simp] theorem chronologicalShortWitnessOfMem_tuple
    {r L gap : ℕ} {tuples : Finset (Fin r → Fin L)}
    (hchronological : ∀ t ∈ tuples, IsChronologicalTuple t)
    (t : {t // t ∈ shortTupleFamily gap tuples}) :
    (chronologicalShortWitnessOfMem (gap := gap) hchronological t).2.2.1 = t.1 := by
  classical
  simp [chronologicalShortWitnessOfMem]

theorem chronologicalShortWitnessOfMem_injective
    {r L gap : ℕ} {tuples : Finset (Fin r → Fin L)}
    (hchronological : ∀ t ∈ tuples, IsChronologicalTuple t) :
    Function.Injective
      (chronologicalShortWitnessOfMem (gap := gap) hchronological) := by
  intro t u htu
  apply Subtype.ext
  have h := congrArg (fun w : ChronologicalShortWitness r L gap ↦ w.2.2.1) htu
  simpa using! h

/-- Uniform deterministic short-gap bound.  No arithmetic information about
the ambient tuple family is used beyond chronologicality. -/
theorem card_shortTupleFamily_le
    {r L gap : ℕ} {tuples : Finset (Fin r → Fin L)}
    (hchronological : ∀ t ∈ tuples, IsChronologicalTuple t) :
    (shortTupleFamily gap tuples).card ≤
      r * r * (gap * L ^ (r - 1)) := by
  classical
  have hinj :
      Fintype.card {t // t ∈ shortTupleFamily gap tuples} ≤
        Fintype.card (ChronologicalShortWitness r L gap) :=
    Fintype.card_le_of_injective
      (chronologicalShortWitnessOfMem (gap := gap) hchronological)
      (chronologicalShortWitnessOfMem_injective hchronological)
  calc
    (shortTupleFamily gap tuples).card =
        Fintype.card {t // t ∈ shortTupleFamily gap tuples} := by
          simpa only using! (Fintype.card_coe (shortTupleFamily gap tuples)).symm
    _ ≤ Fintype.card (ChronologicalShortWitness r L gap) := hinj
    _ = ∑ i : Fin r, ∑ k : Fin r,
          Fintype.card (ChronologicalShortPair (L := L) gap i k) := by
            simp [ChronologicalShortWitness]
    _ ≤ ∑ _i : Fin r, ∑ _k : Fin r, gap * L ^ (r - 1) := by
          exact Finset.sum_le_sum fun i _ ↦
            Finset.sum_le_sum fun k _ ↦ card_chronologicalShortPair_le gap i k
    _ = r * r * (gap * L ^ (r - 1)) := by simp [mul_assoc]

/-- If the deterministic separation scale is `o(L)`, chronological short
tuples have zero normalized density.  This is the exact asymptotic hypothesis
consumed by the Gauss factorial-moment theorem. -/
theorem tendsto_shortTupleFamily_density_zero
    {r : ℕ} (hr : 0 < r) (gap : ℕ → ℕ)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (hchronological : ∀ L, ∀ t ∈ tuples L, IsChronologicalTuple t)
    (hgapRatio : Tendsto (fun L : ℕ ↦ (gap L : ℝ) / (L : ℝ))
      atTop (𝓝 0)) :
    Tendsto
      (fun L : ℕ ↦
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 0) := by
  let f : ℕ → ℝ := fun L ↦
    ((shortTupleFamily (gap L) (tuples L)).card : ℝ) / (L : ℝ) ^ r
  let g : ℕ → ℝ := fun L ↦
    ((r * r : ℕ) : ℝ) * ((gap L : ℝ) / (L : ℝ))
  have hg : Tendsto g atTop (𝓝 0) := by
    simpa only [g, mul_zero] using!
      (tendsto_const_nhds.mul hgapRatio)
  change Tendsto f atTop (𝓝 0)
  apply squeeze_zero'
  · exact Eventually.of_forall fun L ↦ by
      dsimp [f]
      positivity
  · filter_upwards [eventually_atTop.2 ⟨1, fun L hL ↦ hL⟩] with L hL
    have hLpos : 0 < L := by omega
    have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hLpos)
    have hcardNat := card_shortTupleFamily_le
      (gap := gap L) (tuples := tuples L) (hchronological L)
    have hcardReal :
        ((shortTupleFamily (gap L) (tuples L)).card : ℝ) ≤
          ((r * r * (gap L * L ^ (r - 1)) : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    have hdiv := div_le_div_of_nonneg_right hcardReal (by positivity : 0 ≤ (L : ℝ) ^ r)
    dsimp [f, g]
    calc
      ((shortTupleFamily (gap L) (tuples L)).card : ℝ) / (L : ℝ) ^ r
          ≤ ((r * r * (gap L * L ^ (r - 1)) : ℕ) : ℝ) /
              (L : ℝ) ^ r := hdiv
      _ = ((r * r : ℕ) : ℝ) * ((gap L : ℝ) / (L : ℝ)) := by
        rw [show r = (r - 1) + 1 by omega, pow_succ]
        push_cast
        field_simp
  · exact hg

/-- Closed chronological parity-box factorial limit with the short-family
density discharged by the deterministic `gap(L)=o(L)` estimate above. -/
theorem gaussApproximationTupleSum_chronologicalParityBoxes_limit_and_bound_of_gapRatio
    {r : ℕ} (hr : 0 < r) {lower upper density : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (parity : Fin r → Fin 2)
    (boxes : ∀ L : ℕ, Fin r → Finset (Fin L))
    (gap : ℕ → ℕ) (hgapTop : Tendsto gap atTop atTop)
    (hgapPos : ∀ᶠ L : ℕ in atTop, 0 < gap L)
    (hgapRatio : Tendsto (fun L : ℕ ↦ (gap L : ℝ) / (L : ℝ))
      atTop (𝓝 0))
    (htotalDensity : Tendsto
      (fun L : ℕ ↦
        ((chronologicalParityBoxTuples parity (boxes L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 density)) :
    Tendsto
        (fun L : ℕ ↦ gaussApproximationTupleSum lower upper
          (chronologicalParityBoxTuples parity (boxes L)))
        atTop
        (𝓝 (density * ((upper - lower) / Real.log 2) ^ r)) ∧
      ∃ C : ℝ, ∀ L : ℕ,
        |gaussApproximationTupleSum lower upper
          (chronologicalParityBoxTuples parity (boxes L))| ≤ C := by
  apply gaussApproximationTupleSum_chronologicalParityBoxes_limit_and_bound
    hr hlower hupper parity boxes gap hgapTop hgapPos htotalDensity
  apply tendsto_shortTupleFamily_density_zero hr gap
    (fun L ↦ chronologicalParityBoxTuples parity (boxes L))
  · intro L t ht
    exact chronologicalParityBoxTuples_isChronological parity (boxes L) t ht
  · exact hgapRatio

/-- The integer square root is an explicit deterministic separation scale
which diverges. -/
theorem tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [eventually_ge_atTop (b * b)] with L hL
  exact Nat.le_sqrt.2 hL

/-- The same square-root scale is sublinear after real normalization. -/
theorem tendsto_natSqrt_div_self_zero :
    Tendsto (fun L : ℕ ↦ (Nat.sqrt L : ℝ) / (L : ℝ))
      atTop (𝓝 0) := by
  have hrecip : Tendsto (fun L : ℕ ↦ (1 : ℝ) / (Nat.sqrt L : ℝ))
      atTop (𝓝 0) :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp tendsto_natSqrt_atTop
  refine squeeze_zero' (Eventually.of_forall fun L ↦ by positivity) ?_ hrecip
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hLpos : 0 < L := by omega
  have hspos : 0 < Nat.sqrt L := Nat.sqrt_pos.2 hLpos
  have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hsreal : (0 : ℝ) < (Nat.sqrt L : ℝ) := by exact_mod_cast hspos
  rw [div_le_div_iff₀ hLreal hsreal]
  norm_num only [one_mul]
  exact_mod_cast Nat.sqrt_le L

/-- Fully explicit square-root-gap version: no auxiliary short-density or
gap-asymptotic hypotheses remain. -/
theorem gaussApproximationTupleSum_chronologicalParityBoxes_limit_and_bound_sqrtGap
    {r : ℕ} (hr : 0 < r) {lower upper density : ℝ}
    (hlower : 0 < lower) (hupper : lower < upper)
    (parity : Fin r → Fin 2)
    (boxes : ∀ L : ℕ, Fin r → Finset (Fin L))
    (htotalDensity : Tendsto
      (fun L : ℕ ↦
        ((chronologicalParityBoxTuples parity (boxes L)).card : ℝ) /
          (L : ℝ) ^ r)
      atTop (𝓝 density)) :
    Tendsto
        (fun L : ℕ ↦ gaussApproximationTupleSum lower upper
          (chronologicalParityBoxTuples parity (boxes L)))
        atTop
        (𝓝 (density * ((upper - lower) / Real.log 2) ^ r)) ∧
      ∃ C : ℝ, ∀ L : ℕ,
        |gaussApproximationTupleSum lower upper
          (chronologicalParityBoxTuples parity (boxes L))| ≤ C := by
  apply gaussApproximationTupleSum_chronologicalParityBoxes_limit_and_bound_of_gapRatio
    hr hlower hupper parity boxes Nat.sqrt tendsto_natSqrt_atTop
  · filter_upwards [eventually_ge_atTop 1] with L hL
    exact Nat.sqrt_pos.2 (by omega)
  · exact tendsto_natSqrt_div_self_zero
  · exact htotalDensity

end

end Erdos1002
