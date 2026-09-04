import ErdosProblems.Erdos980.NaturalChebotarev.SplitTransfer.Algebra

/-!
# Counting prime ideals by residue degree

The prime ideals of norm at most `x` are partitioned into unramified
degree-one primes, ramified degree-one primes, and primes of residue degree at
least two.  The first part is exactly `[L : ℚ]` times the number of completely
split rational primes, while the last part is `O([L : ℚ] √ x)`.
-/

namespace Erdos980.NaturalChebotarev.SplitTransfer

open NumberField Chebotarev

noncomputable section

variable (L : Type*) [Field L] [NumberField L] [Algebra ℚ L] [IsGalois ℚ L]

/-- Nonzero prime ideals of `L` of absolute norm at most `x`. -/
def PrimeIdealsUpTo (x : ℕ) :=
  {P : Ideal (𝓞 L) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ x}

/-- Unramified degree-one prime ideals of norm at most `x`. -/
def UnramifiedDegreeOneUpTo (x : ℕ) :=
  {P : Ideal (𝓞 L) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ x ∧
    UnramifiedIn ℚ L (P.under (𝓞 ℚ)) ∧ residueDegree L P = 1}

/-- Ramified degree-one prime ideals of norm at most `x`. -/
def RamifiedDegreeOneUpTo (x : ℕ) :=
  {P : Ideal (𝓞 L) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ x ∧
    ¬ UnramifiedIn ℚ L (P.under (𝓞 ℚ)) ∧ residueDegree L P = 1}

/-- Prime ideals of norm at most `x` and residue degree at least two. -/
def HigherDegreeUpTo (x : ℕ) :=
  {P : Ideal (𝓞 L) // P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ x ∧
    2 ≤ residueDegree L P}

/-- Completely split rational primes at most `x`. -/
def SplitPrimesUpTo (x : ℕ) :=
  {p : ℕ // IsCompletelySplit L p ∧ p ≤ x}

def primeIdealCount (x : ℕ) : ℕ := Nat.card (PrimeIdealsUpTo L x)
def unramifiedDegreeOneCount (x : ℕ) : ℕ := Nat.card (UnramifiedDegreeOneUpTo L x)
def ramifiedDegreeOneCount (x : ℕ) : ℕ := Nat.card (RamifiedDegreeOneUpTo L x)
def higherDegreeCount (x : ℕ) : ℕ := Nat.card (HigherDegreeUpTo L x)
def splitPrimeCount (x : ℕ) : ℕ := Nat.card (SplitPrimesUpTo L x)

private instance finite_primeIdealsUpTo (x : ℕ) : Finite (PrimeIdealsUpTo L x) := by
  have : Finite {I : Ideal (𝓞 L) // Ideal.absNorm I ≤ x} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 L) x).to_subtype
  exact Finite.of_injective
    (fun P : PrimeIdealsUpTo L x ↦
      (⟨P.1, P.2.2.2⟩ : {I : Ideal (𝓞 L) // Ideal.absNorm I ≤ x}))
    (fun _ _ h ↦ Subtype.ext (by simpa using h))

private instance finite_unramifiedDegreeOneUpTo (x : ℕ) :
    Finite (UnramifiedDegreeOneUpTo L x) := by
  have : Finite {I : Ideal (𝓞 L) // Ideal.absNorm I ≤ x} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 L) x).to_subtype
  exact Finite.of_injective
    (fun P : UnramifiedDegreeOneUpTo L x ↦
      (⟨P.1, P.2.2.2.1⟩ : {I : Ideal (𝓞 L) // Ideal.absNorm I ≤ x}))
    (fun _ _ h ↦ Subtype.ext (by simpa using h))

private instance finite_ramifiedDegreeOneUpTo (x : ℕ) :
    Finite (RamifiedDegreeOneUpTo L x) := by
  have : Finite {I : Ideal (𝓞 L) // Ideal.absNorm I ≤ x} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 L) x).to_subtype
  exact Finite.of_injective
    (fun P : RamifiedDegreeOneUpTo L x ↦
      (⟨P.1, P.2.2.2.1⟩ : {I : Ideal (𝓞 L) // Ideal.absNorm I ≤ x}))
    (fun _ _ h ↦ Subtype.ext (by simpa using h))

private instance finite_higherDegreeUpTo (x : ℕ) : Finite (HigherDegreeUpTo L x) := by
  have : Finite {I : Ideal (𝓞 L) // Ideal.absNorm I ≤ x} :=
    (Ideal.finite_setOf_absNorm_le (S := 𝓞 L) x).to_subtype
  exact Finite.of_injective
    (fun P : HigherDegreeUpTo L x ↦
      (⟨P.1, P.2.2.2.1⟩ : {I : Ideal (𝓞 L) // Ideal.absNorm I ≤ x}))
    (fun _ _ h ↦ Subtype.ext (by simpa using h))

private instance finite_splitPrimesUpTo (x : ℕ) : Finite (SplitPrimesUpTo L x) :=
  Finite.of_injective
    (fun p : SplitPrimesUpTo L x ↦
      (⟨p.1, Nat.lt_succ_of_le p.2.2⟩ : Fin (x + 1)))
    (fun _ _ h ↦ Subtype.ext (by simpa using congrArg Fin.val h))

/-- The three-way partition map for bounded prime ideals. -/
private def primeIdealPartitionMap (x : ℕ) :
    PrimeIdealsUpTo L x →
      UnramifiedDegreeOneUpTo L x ⊕
        (RamifiedDegreeOneUpTo L x ⊕ HigherDegreeUpTo L x) := fun P ↦ by
    by_cases hdeg : residueDegree L P.1 = 1
    · by_cases hunr : UnramifiedIn ℚ L (P.1.under (𝓞 ℚ))
      · exact Sum.inl ⟨P.1, P.2.1, P.2.2.1, P.2.2.2, hunr, hdeg⟩
      · exact Sum.inr (Sum.inl ⟨P.1, P.2.1, P.2.2.1, P.2.2.2, hunr, hdeg⟩)
    · haveI : P.1.IsPrime := P.2.1
      haveI : P.1.LiesOver (P.1.under (𝓞 ℚ)) :=
        Ideal.over_under (A := 𝓞 ℚ) (P := P.1)
      have hpos : 0 < residueDegree L P.1 := Ideal.inertiaDeg_pos' _ _
      exact Sum.inr (Sum.inr ⟨P.1, P.2.1, P.2.2.1, P.2.2.2, by omega⟩)

private def partitionValue (x : ℕ) :
    UnramifiedDegreeOneUpTo L x ⊕
        (RamifiedDegreeOneUpTo L x ⊕ HigherDegreeUpTo L x) → Ideal (𝓞 L)
  | Sum.inl P => P.1
  | Sum.inr (Sum.inl P) => P.1
  | Sum.inr (Sum.inr P) => P.1

private theorem partitionValue_map (x : ℕ) (P : PrimeIdealsUpTo L x) :
    partitionValue L x (primeIdealPartitionMap L x P) = P.1 := by
  simp only [primeIdealPartitionMap]
  split <;> rename_i hdeg
  · split <;> rfl
  · rfl

private theorem primeIdealPartitionMap_bijective (x : ℕ) :
    Function.Bijective (primeIdealPartitionMap L x) := by
  constructor
  · intro P Q h
    apply Subtype.ext
    have hv := congrArg (partitionValue L x) h
    simpa only [partitionValue_map] using hv
  · intro P
    rcases P with P | P
    · let Q : PrimeIdealsUpTo L x := ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1⟩
      refine ⟨Q, ?_⟩
      have hdeg : residueDegree L Q.1 = 1 := P.2.2.2.2.2
      have hunr : UnramifiedIn ℚ L (Q.1.under (𝓞 ℚ)) := P.2.2.2.2.1
      simp only [primeIdealPartitionMap]
      rw [dif_pos hdeg, dif_pos hunr]
      apply congrArg Sum.inl
      apply Subtype.ext
      rfl
    · rcases P with P | P
      · let Q : PrimeIdealsUpTo L x := ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1⟩
        refine ⟨Q, ?_⟩
        have hdeg : residueDegree L Q.1 = 1 := P.2.2.2.2.2
        have hram : ¬ UnramifiedIn ℚ L (Q.1.under (𝓞 ℚ)) := P.2.2.2.2.1
        simp only [primeIdealPartitionMap]
        rw [dif_pos hdeg, dif_neg hram]
        apply congrArg (Sum.inr ∘ Sum.inl)
        apply Subtype.ext
        rfl
      · let Q : PrimeIdealsUpTo L x := ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.1⟩
        refine ⟨Q, ?_⟩
        have hhigh : 2 ≤ residueDegree L Q.1 := P.2.2.2.2
        have hne : residueDegree L Q.1 ≠ 1 := by omega
        simp only [primeIdealPartitionMap]
        rw [dif_neg hne]
        apply congrArg (Sum.inr ∘ Sum.inr)
        apply Subtype.ext
        rfl

/-- The three-way partition of bounded prime ideals. -/
private def primeIdealPartitionEquiv (x : ℕ) :
    PrimeIdealsUpTo L x ≃
      UnramifiedDegreeOneUpTo L x ⊕
        (RamifiedDegreeOneUpTo L x ⊕ HigherDegreeUpTo L x) :=
  Equiv.ofBijective (primeIdealPartitionMap L x) (primeIdealPartitionMap_bijective L x)

/-- Exact decomposition into degree one (unramified and ramified) and higher
residue degree. -/
theorem primeIdealCount_eq_parts (x : ℕ) :
    primeIdealCount L x = unramifiedDegreeOneCount L x +
      ramifiedDegreeOneCount L x + higherDegreeCount L x := by
  rw [primeIdealCount, unramifiedDegreeOneCount, ramifiedDegreeOneCount,
    higherDegreeCount, Nat.card_congr (primeIdealPartitionEquiv L x)]
  simp [add_assoc]

/-- Send a degree-one unramified prime ideal to the rational prime below it. -/
private def degreeOneToSplit (x : ℕ) :
    UnramifiedDegreeOneUpTo L x → SplitPrimesUpTo L x := fun P ↦ by
  have hsplit := isCompletelySplit_primeBelow_of_residueDegree_eq_one L
    P.2.1 P.2.2.1 P.2.2.2.2.1 P.2.2.2.2.2
  have hnorm := absNorm_eq_primeBelow_pow_residueDegree L P.2.1 P.2.2.1
  have hle : primeBelow L P.1 ≤ x := by
    rw [P.2.2.2.2.2, pow_one] at hnorm
    exact hnorm ▸ P.2.2.2.1
  exact ⟨primeBelow L P.1, hsplit, hle⟩

/-- A fibre of `degreeOneToSplit` is the set of primes above the corresponding
completely split rational prime. -/
private def degreeOneSplitFiberEquiv (x : ℕ) (p : SplitPrimesUpTo L x) :
    {P : UnramifiedDegreeOneUpTo L x // degreeOneToSplit L x P = p} ≃
      {Q : Ideal (𝓞 L) // Q.IsPrime ∧ Q.LiesOver (rationalIdeal p.1) ∧ Q ≠ ⊥} where
  toFun P := by
    have hpval : primeBelow L P.1.1 = p.1 := congrArg Subtype.val P.2
    have hunder := (under_eq_rationalIdeal_primeBelow L P.1.2.1 P.1.2.2.1).1
    refine ⟨P.1.1, P.1.2.1, ?_, P.1.2.2.1⟩
    exact ⟨by rw [← hpval, ← hunder]⟩
  invFun Q := by
    haveI : Q.1.IsPrime := Q.2.1
    haveI : Q.1.LiesOver (rationalIdeal p.1) := Q.2.2.1
    have hunder : Q.1.under (𝓞 ℚ) = rationalIdeal p.1 := Q.2.2.1.over.symm
    have hpbelow : primeBelow L Q.1 = p.1 := by
      rw [primeBelow, hunder, absNorm_rationalIdeal]
    have hdeg := residueDegree_eq_one_of_isCompletelySplit L p.2.1 Q.2.1 Q.2.2.2 Q.2.2.1
    have hnorm := absNorm_eq_primeBelow_pow_residueDegree L Q.2.1 Q.2.2.2
    have hnormp : Ideal.absNorm Q.1 = p.1 := by rw [hnorm, hpbelow, hdeg, pow_one]
    have hunr : UnramifiedIn ℚ L (Q.1.under (𝓞 ℚ)) := by
      rw [hunder]
      exact p.2.1.2.1
    let Q' : UnramifiedDegreeOneUpTo L x :=
      ⟨Q.1, Q.2.1, Q.2.2.2, hnormp.le.trans p.2.2, hunr, hdeg⟩
    refine ⟨Q', ?_⟩
    apply Subtype.ext
    exact hpbelow
  left_inv P := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv Q := by
    apply Subtype.ext
    rfl

private theorem card_degreeOneSplit_fiber (x : ℕ) (p : SplitPrimesUpTo L x) :
    Nat.card {P : UnramifiedDegreeOneUpTo L x // degreeOneToSplit L x P = p} =
      Module.finrank ℚ L := by
  rw [Nat.card_congr (degreeOneSplitFiberEquiv L x p)]
  exact card_primesAbove_of_isCompletelySplit L p.2.1

/-- The unramified degree-one prime ideals occur in fibres of exactly
`[L : ℚ]` above completely split rational primes. -/
theorem unramifiedDegreeOneCount_eq_degree_mul_splitPrimeCount (x : ℕ) :
    unramifiedDegreeOneCount L x = Module.finrank ℚ L * splitPrimeCount L x := by
  let : Fintype (SplitPrimesUpTo L x) := Fintype.ofFinite _
  rw [unramifiedDegreeOneCount, splitPrimeCount,
    ← Nat.card_congr (Equiv.sigmaFiberEquiv (degreeOneToSplit L x)), Nat.card_sigma]
  simp_rw [card_degreeOneSplit_fiber L x]
  rw [Finset.sum_const, Nat.card_eq_fintype_card]
  exact Nat.mul_comm _ _

/-! ## Bounds for the two error terms -/

/-- There are at most `[L : ℚ]` primes of `L` over a fixed rational prime. -/
theorem card_primesAbove_le_degree {p : ℕ} (hp : p.Prime) :
    Nat.card {P : Ideal (𝓞 L) // P.IsPrime ∧ P.LiesOver (rationalIdeal p)} ≤
      Module.finrank ℚ L := by
  have hp0 : rationalIdeal p ≠ ⊥ := by
    intro h
    have hnorm := congrArg Ideal.absNorm h
    rw [absNorm_rationalIdeal, Ideal.absNorm_bot] at hnorm
    exact hp.ne_zero hnorm
  have : NoZeroSMulDivisors (𝓞 ℚ) (𝓞 L) :=
    ⟨fun {c x} h ↦ by
      rw [Algebra.smul_def, mul_eq_zero] at h
      exact h.imp
        (fun hc ↦ RingOfIntegers.algebraMap.injective ℚ L (by rwa [map_zero])) id⟩
  let : (rationalIdeal p).IsPrime := rationalIdeal_isPrime hp
  let : (rationalIdeal p).IsMaximal := (rationalIdeal_isPrime hp).isMaximal hp0
  rw [show {P : Ideal (𝓞 L) // P.IsPrime ∧ P.LiesOver (rationalIdeal p)} =
      ↥((rationalIdeal p).primesOver (𝓞 L)) from rfl,
    Nat.card_coe_set_eq, ← IsDedekindDomain.coe_primesOverFinset hp0,
    Set.ncard_coe_finset]
  exact Ideal.card_primesOverFinset_le_finrank (R := 𝓞 ℚ) (S := 𝓞 L)
    (K := ℚ) (L := L) hp0

/-- A higher-degree prime ideal maps to the rational prime below it, which is
at most `√x`. -/
private def higherDegreeToSqrt (x : ℕ) : HigherDegreeUpTo L x → Fin (x.sqrt + 1) :=
    fun P ↦ by
  have hp := (under_eq_rationalIdeal_primeBelow L P.2.1 P.2.2.1).2
  have hnorm := absNorm_eq_primeBelow_pow_residueDegree L P.2.1 P.2.2.1
  have hp_sq : primeBelow L P.1 ^ 2 ≤ x := calc
    primeBelow L P.1 ^ 2 ≤ primeBelow L P.1 ^ residueDegree L P.1 :=
      Nat.pow_le_pow_right hp.pos P.2.2.2.2
    _ = Ideal.absNorm P.1 := hnorm.symm
    _ ≤ x := P.2.2.2.1
  exact ⟨primeBelow L P.1, Nat.lt_succ_of_le (Nat.le_sqrt'.mpr hp_sq)⟩

private theorem card_higherDegreeToSqrt_fiber_le (x : ℕ) (p : Fin (x.sqrt + 1)) :
    Nat.card {P : HigherDegreeUpTo L x // higherDegreeToSqrt L x P = p} ≤
      Module.finrank ℚ L := by
  classical
  by_cases hne : Nonempty {P : HigherDegreeUpTo L x // higherDegreeToSqrt L x P = p}
  · let P₀ := Classical.choice hne
    have hpval : primeBelow L P₀.1.1 = p.1 := congrArg Fin.val P₀.2
    have hp : p.1.Prime := by
      rw [← hpval]
      exact (under_eq_rationalIdeal_primeBelow L P₀.1.2.1 P₀.1.2.2.1).2
    have hp0 : rationalIdeal p.1 ≠ ⊥ := by
      intro h
      have hnorm := congrArg Ideal.absNorm h
      rw [absNorm_rationalIdeal, Ideal.absNorm_bot] at hnorm
      exact hp.ne_zero hnorm
    let : (rationalIdeal p.1).IsPrime := rationalIdeal_isPrime hp
    let : (rationalIdeal p.1).IsMaximal := (rationalIdeal_isPrime hp).isMaximal hp0
    have : Finite {Q : Ideal (𝓞 L) //
        Q.IsPrime ∧ Q.LiesOver (rationalIdeal p.1)} :=
      (IsDedekindDomain.primesOver_finite (rationalIdeal p.1) (𝓞 L)).to_subtype
    let f : {P : HigherDegreeUpTo L x // higherDegreeToSqrt L x P = p} →
        {Q : Ideal (𝓞 L) // Q.IsPrime ∧ Q.LiesOver (rationalIdeal p.1)} := fun P ↦ by
      have hbelow : primeBelow L P.1.1 = p.1 := congrArg Fin.val P.2
      have hunder := (under_eq_rationalIdeal_primeBelow L P.1.2.1 P.1.2.2.1).1
      refine ⟨P.1.1, P.1.2.1, ?_⟩
      exact ⟨by rw [← hbelow, ← hunder]⟩
    exact (Nat.card_le_card_of_injective f (fun P Q h ↦ by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {Q : Ideal (𝓞 L) //
        Q.IsPrime ∧ Q.LiesOver (rationalIdeal p.1)} ↦ z.1) h)).trans
          (card_primesAbove_le_degree L hp)
  · have : IsEmpty {P : HigherDegreeUpTo L x // higherDegreeToSqrt L x P = p} :=
      not_nonempty_iff.mp hne
    simp [Nat.card_eq_zero]

/-- Prime ideals of residue degree at least two contribute at most
`[L : ℚ](√x + 1)`. -/
theorem higherDegreeCount_le_degree_mul_sqrt_add_one (x : ℕ) :
    higherDegreeCount L x ≤ Module.finrank ℚ L * (x.sqrt + 1) := by
  let : Finite (HigherDegreeUpTo L x) := finite_higherDegreeUpTo L x
  rw [higherDegreeCount,
    ← Nat.card_congr (Equiv.sigmaFiberEquiv (higherDegreeToSqrt L x)), Nat.card_sigma]
  calc
    ∑ p : Fin (x.sqrt + 1),
        Nat.card {P : HigherDegreeUpTo L x // higherDegreeToSqrt L x P = p}
        ≤ ∑ _p : Fin (x.sqrt + 1), Module.finrank ℚ L :=
      Finset.sum_le_sum fun p _ ↦ card_higherDegreeToSqrt_fiber_le L x p
    _ = Module.finrank ℚ L * (x.sqrt + 1) := by simp [Nat.mul_comm]

/-- Nonzero prime ideals lying over ramified rational primes. -/
def RamifiedPrimeIdeals :=
  {P : Ideal (𝓞 L) // P.IsPrime ∧ P ≠ ⊥ ∧
    ¬ UnramifiedIn ℚ L (P.under (𝓞 ℚ))}

/-- Only finitely many prime ideals of `L` lie over ramified rational primes. -/
instance finite_ramifiedPrimeIdeals : Finite (RamifiedPrimeIdeals L) := by
  classical
  have : Finite {p : Ideal (𝓞 ℚ) //
      p.IsPrime ∧ p ≠ ⊥ ∧ ¬ UnramifiedIn ℚ L p} :=
    (finite_ramifiedIn ℚ L).to_subtype
  have : ∀ p : {p : Ideal (𝓞 ℚ) //
      p.IsPrime ∧ p ≠ ⊥ ∧ ¬ UnramifiedIn ℚ L p},
      Finite (p.1.primesOver (𝓞 L)) := fun p ↦ by
    let : p.1.IsPrime := p.2.1
    let : p.1.IsMaximal := p.2.1.isMaximal p.2.2.1
    exact (IsDedekindDomain.primesOver_finite p.1 (𝓞 L)).to_subtype
  refine Finite.of_injective
    (fun P : RamifiedPrimeIdeals L ↦
      (show Σ p : {p : Ideal (𝓞 ℚ) //
          p.IsPrime ∧ p ≠ ⊥ ∧ ¬ UnramifiedIn ℚ L p},
          p.1.primesOver (𝓞 L) by
        haveI : P.1.IsPrime := P.2.1
        exact ⟨⟨P.1.under (𝓞 ℚ), inferInstance,
          Ideal.under_ne_bot (A := 𝓞 ℚ) P.2.2.1, P.2.2.2⟩,
          ⟨P.1, P.2.1, Ideal.over_under (A := 𝓞 ℚ) (P := P.1)⟩⟩))
    (fun P Q h ↦ Subtype.ext (by
      simpa using congrArg (fun z ↦ (z.2 : Ideal (𝓞 L))) h))

def ramifiedPrimeIdealCount : ℕ := Nat.card (RamifiedPrimeIdeals L)

/-- The bounded ramified degree-one count is bounded by the fixed number of
ramified prime ideals. -/
theorem ramifiedDegreeOneCount_le_ramifiedPrimeIdealCount (x : ℕ) :
    ramifiedDegreeOneCount L x ≤ ramifiedPrimeIdealCount L := by
  let f : RamifiedDegreeOneUpTo L x → RamifiedPrimeIdeals L :=
    fun P ↦ ⟨P.1, P.2.1, P.2.2.1, P.2.2.2.2.1⟩
  exact Nat.card_le_card_of_injective f fun P Q h ↦ by
    apply Subtype.ext
    exact congrArg (fun z : RamifiedPrimeIdeals L ↦ z.1) h

/-- Prime-ideal count equals the completely-split count with the two explicit
error terms. -/
theorem primeIdealCount_eq_degree_mul_split_add_errors (x : ℕ) :
    primeIdealCount L x = Module.finrank ℚ L * splitPrimeCount L x +
      ramifiedDegreeOneCount L x + higherDegreeCount L x := by
  rw [primeIdealCount_eq_parts L x,
    unramifiedDegreeOneCount_eq_degree_mul_splitPrimeCount L x]

/-- Quantitative form of the transfer error. -/
theorem abs_primeIdealCount_sub_degree_mul_splitPrimeCount_le (x : ℕ) :
    |(primeIdealCount L x : ℝ) -
        Module.finrank ℚ L * splitPrimeCount L x| ≤
      ramifiedPrimeIdealCount L + Module.finrank ℚ L * (x.sqrt + 1) := by
  have heq := primeIdealCount_eq_degree_mul_split_add_errors L x
  have hram := ramifiedDegreeOneCount_le_ramifiedPrimeIdealCount L x
  have hhigh := higherDegreeCount_le_degree_mul_sqrt_add_one L x
  have heqR : (primeIdealCount L x : ℝ) =
      (Module.finrank ℚ L : ℝ) * splitPrimeCount L x +
        ramifiedDegreeOneCount L x + higherDegreeCount L x := by
    exact_mod_cast heq
  have hramR : (ramifiedDegreeOneCount L x : ℝ) ≤ ramifiedPrimeIdealCount L := by
    exact_mod_cast hram
  have hhighR : (higherDegreeCount L x : ℝ) ≤
      Module.finrank ℚ L * (x.sqrt + 1) := by
    exact_mod_cast hhigh
  have hnonneg : (0 : ℝ) ≤ (primeIdealCount L x : ℝ) -
      Module.finrank ℚ L * splitPrimeCount L x := by
    linarith
  rw [abs_of_nonneg hnonneg]
  norm_num at heqR ⊢
  linarith

end

end Erdos980.NaturalChebotarev.SplitTransfer
