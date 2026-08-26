import ErdosProblems.Erdos796.SplitNormalCounting
import ErdosProblems.Erdos796.SemiprimeFibers

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The low-multiplier small-prime budget

This file treats split normal forms

`a = s * q * r`,

for which `q ≠ r`, both canonical primes are at most `sqrt n`, and
`s < W`.  We put the elements into multiplier fibres indexed by the positive
integers below `W`.  Bonferroni pays once for the union of the fibres and
uses the `C₄`-free overlap graph for every pair of distinct multipliers.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

namespace SmallPrimeBudget

open PruningNormalForms PruningClassification PairwiseOverlap
  SemiprimeFibers SplitNormalCounting

/-- The part of the small-first-prime split piece whose residual multiplier
is below `W`. -/
noncomputable def lowMultiplierSmallPrimePiece
    (n Y Z W : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact (splitSmallPrimePiece n Y Z A).filter fun a => splitS a < W

@[simp] theorem mem_lowMultiplierSmallPrimePiece
    {n Y Z W a : ℕ} {A : Finset ℕ} :
    a ∈ lowMultiplierSmallPrimePiece n Y Z W A ↔
      a ∈ A ∧ IsSplitNormalForm Y Z a ∧
        splitQ a ≠ splitR a ∧ splitQ a ≤ n.sqrt ∧
          splitS a < W := by
  classical
  simp [lowMultiplierSmallPrimePiece, and_assoc]

/-- Possible first canonical primes in the small-prime piece. -/
def firstPrimeVertices (n Y : ℕ) : Finset ℕ :=
  (Nat.primesLE n.sqrt).filter fun q => Y < q

/-- Possible second canonical primes in the small-prime piece. -/
def secondPrimeVertices (n Z : ℕ) : Finset ℕ :=
  (Nat.primesLE n.sqrt).filter fun r => Z < r

@[simp] theorem mem_firstPrimeVertices {n Y q : ℕ} :
    q ∈ firstPrimeVertices n Y ↔ q.Prime ∧ q ≤ n.sqrt ∧ Y < q := by
  simp [firstPrimeVertices, Nat.mem_primesLE, and_left_comm,
    and_comm]

@[simp] theorem mem_secondPrimeVertices {n Z r : ℕ} :
    r ∈ secondPrimeVertices n Z ↔ r.Prime ∧ r ≤ n.sqrt ∧ Z < r := by
  simp [secondPrimeVertices, Nat.mem_primesLE, and_left_comm,
    and_comm]

/-- The oriented prime-pair fibre belonging to a residual multiplier. -/
def smallPrimeFiber (n Y Z : ℕ) (A : Finset ℕ) (s : ℕ) :
    Finset (ℕ × ℕ) :=
  semiprimeFiberEdges A s (firstPrimeVertices n Y)
    (secondPrimeVertices n Z)

@[simp] theorem mem_smallPrimeFiber
    {n Y Z s q r : ℕ} {A : Finset ℕ} :
    (q, r) ∈ smallPrimeFiber n Y Z A s ↔
      q.Prime ∧ q ≤ n.sqrt ∧ Y < q ∧
        r.Prime ∧ r ≤ n.sqrt ∧ Z < r ∧ r < q ∧
          multipliedPrimePair s q r ∈ A := by
  simp [smallPrimeFiber, and_assoc, and_left_comm, and_comm]

/-- Product image of all positive multiplier fibres below `W`. -/
noncomputable def smallPrimeProducts
    (n Y Z W : ℕ) (A : Finset ℕ) : Finset ℕ := by
  classical
  exact ((positiveIcc (W - 1)).sigma fun s =>
    smallPrimeFiber n Y Z A s).image fun p =>
      multipliedPrimePair p.1 p.2.1 p.2.2

/-- Every captured normal form occurs in its canonical multiplier fibre. -/
theorem lowMultiplierSmallPrimePiece_subset_products
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    lowMultiplierSmallPrimePiece n Y Z W A ⊆
      smallPrimeProducts n Y Z W A := by
  classical
  intro a ha
  have ha' := mem_lowMultiplierSmallPrimePiece.mp ha
  have hform := ha'.2.1
  have hqpd := splitQ_prime_dvd hform
  have hrp := splitR_prime_gt hform
  have hspos : 0 < splitS a := splitS_pos hA ha'.1 hform
  have hsM : splitS a ∈ positiveIcc (W - 1) := by
    exact mem_positiveIcc.mpr ⟨hspos, by omega⟩
  have hqY : Y < splitQ a := by
    simpa [splitQ, IsSplitNormalForm] using! hform.2.2.1
  have hapos : 0 < a := (mem_positiveIcc.mp (hA.1 ha'.1)).1
  have ha1 : 1 < a := by
    have hqle : splitQ a ≤ a := Nat.le_of_dvd hapos hqpd.2
    exact hqpd.1.one_lt.trans_le hqle
  have hrdvd : splitR a ∣ a := by
    refine ⟨splitS a * splitQ a, ?_⟩
    calc
      a = splitS a * splitQ a * splitR a := split_value_eq hform
      _ = splitR a * (splitS a * splitQ a) := by ring
  have hrleq : splitR a ≤ splitQ a := by
    simpa [splitQ] using!
      (prime_dvd_le_largestPrimeFactor ha1 hrp.1 hrdvd)
  have hrq : splitR a < splitQ a := by
    omega
  have hrsqrt : splitR a ≤ n.sqrt := hrq.le.trans ha'.2.2.2.1
  have hqmem : splitQ a ∈ firstPrimeVertices n Y :=
    mem_firstPrimeVertices.mpr ⟨hqpd.1, ha'.2.2.2.1, hqY⟩
  have hrmem : splitR a ∈ secondPrimeVertices n Z :=
    mem_secondPrimeVertices.mpr ⟨hrp.1, hrsqrt, hrp.2⟩
  have hedge : (splitQ a, splitR a) ∈
      smallPrimeFiber n Y Z A (splitS a) := by
    have hvalue : multipliedPrimePair (splitS a) (splitQ a) (splitR a) = a := by
      simpa [multipliedPrimePair] using! (split_value_eq hform).symm
    have hmembership :
        multipliedPrimePair (splitS a) (splitQ a) (splitR a) ∈ A := by
      rw [hvalue]
      exact ha'.1
    exact mem_semiprimeFiberEdges.mpr
      ⟨hqmem, hrmem, hqpd.1, hrp.1, hrq, hmembership⟩
  apply Finset.mem_image.mpr
  refine ⟨⟨splitS a, (splitQ a, splitR a)⟩,
    Finset.mem_sigma.mpr ⟨hsM, hedge⟩, ?_⟩
  simpa [multipliedPrimePair] using! (split_value_eq hform).symm

/-- Passing to the product image costs at most the sum of the fibre sizes. -/
theorem card_smallPrimeProducts_le_sum
    (n Y Z W : ℕ) (A : Finset ℕ) :
    (smallPrimeProducts n Y Z W A).card ≤
      ∑ s ∈ positiveIcc (W - 1),
        (smallPrimeFiber n Y Z A s).card := by
  classical
  calc
    (smallPrimeProducts n Y Z W A).card ≤
        ((positiveIcc (W - 1)).sigma fun s =>
          smallPrimeFiber n Y Z A s).card := Finset.card_image_le
    _ = ∑ s ∈ positiveIcc (W - 1),
        (smallPrimeFiber n Y Z A s).card := by simp

theorem card_lowMultiplierSmallPrimePiece_le_sum
    {n Y Z W : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    (lowMultiplierSmallPrimePiece n Y Z W A).card ≤
      ∑ s ∈ positiveIcc (W - 1),
        (smallPrimeFiber n Y Z A s).card :=
  (Finset.card_le_card
      (lowMultiplierSmallPrimePiece_subset_products hA)).trans
    (card_smallPrimeProducts_le_sum n Y Z W A)

/-! ## The common KST overlap bound -/

/-- A real KST majorant obtained by replacing both vertex cardinalities by
the ambient interval size `sqrt n`. -/
noncomputable def KsmallReal (n : ℕ) : ℝ :=
  (n.sqrt : ℝ) +
    Real.sqrt
      (2 * (n.sqrt : ℝ) * (Nat.choose n.sqrt 2 : ℝ))

theorem firstPrimeVertices_subset_positiveIcc (n Y : ℕ) :
    firstPrimeVertices n Y ⊆ positiveIcc n.sqrt := by
  intro q hq
  have hq' := mem_firstPrimeVertices.mp hq
  exact mem_positiveIcc.mpr ⟨hq'.1.one_le, hq'.2.1⟩

theorem secondPrimeVertices_subset_positiveIcc (n Z : ℕ) :
    secondPrimeVertices n Z ⊆ positiveIcc n.sqrt := by
  intro r hr
  have hr' := mem_secondPrimeVertices.mp hr
  exact mem_positiveIcc.mpr ⟨hr'.1.one_le, hr'.2.1⟩

theorem card_firstPrimeVertices_le_sqrt (n Y : ℕ) :
    (firstPrimeVertices n Y).card ≤ n.sqrt := by
  have h := Finset.card_le_card (firstPrimeVertices_subset_positiveIcc n Y)
  simpa [positiveIcc] using! h

theorem card_secondPrimeVertices_le_sqrt (n Z : ℕ) :
    (secondPrimeVertices n Z).card ≤ n.sqrt := by
  have h := Finset.card_le_card (secondPrimeVertices_subset_positiveIcc n Z)
  simpa [positiveIcc] using! h

/-- KST bounds every pairwise fibre overlap by the displayed common real
majorant. -/
theorem card_overlapGraph_cast_le_KsmallReal
    {n Y Z W s t : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (hs : 0 < s) (ht : 0 < t)
    (hst : s ≠ t) (hsW : s < W) (htW : t < W)
    (hWZ : W ≤ Z) (hZY : Z ≤ Y) :
    ((overlapGraph A s t (firstPrimeVertices n Y)
      (secondPrimeVertices n Z)).card : ℝ) ≤ KsmallReal n := by
  let Q := firstPrimeVertices n Y
  let R := secondPrimeVertices n Z
  have hQmult : ∀ q ∈ Q, s < q ∧ t < q := by
    intro q hq
    have hq' := mem_firstPrimeVertices.mp hq
    exact ⟨hsW.trans_le hWZ |>.trans_le hZY |>.trans hq'.2.2,
      htW.trans_le hWZ |>.trans_le hZY |>.trans hq'.2.2⟩
  have hRmult : ∀ r ∈ R, s < r ∧ t < r := by
    intro r hr
    have hr' := mem_secondPrimeVertices.mp hr
    exact ⟨hsW.trans_le hWZ |>.trans hr'.2.2,
      htW.trans_le hWZ |>.trans hr'.2.2⟩
  have hKST :
      ((overlapGraph A s t Q R).card : ℝ) ≤
        (R.card : ℝ) +
          Real.sqrt
            (2 * (R.card : ℝ) * (Nat.choose Q.card 2 : ℝ)) :=
    overlapGraph_card_le hA hs ht hst hQmult hRmult
  have hRnat : R.card ≤ n.sqrt := by
    simpa [R] using! card_secondPrimeVertices_le_sqrt n Z
  have hQnat : Q.card ≤ n.sqrt := by
    simpa [Q] using! card_firstPrimeVertices_le_sqrt n Y
  have hRreal : (R.card : ℝ) ≤ (n.sqrt : ℝ) := by
    exact_mod_cast hRnat
  have hChooseNat : Nat.choose Q.card 2 ≤ Nat.choose n.sqrt 2 :=
    Nat.choose_le_choose 2 hQnat
  have hChooseReal : (Nat.choose Q.card 2 : ℝ) ≤
      (Nat.choose n.sqrt 2 : ℝ) := by
    exact_mod_cast hChooseNat
  have hrad :
      2 * (R.card : ℝ) * (Nat.choose Q.card 2 : ℝ) ≤
        2 * (n.sqrt : ℝ) * (Nat.choose n.sqrt 2 : ℝ) := by
    have htwoR : 2 * (R.card : ℝ) ≤ 2 * (n.sqrt : ℝ) :=
      mul_le_mul_of_nonneg_left hRreal (by norm_num)
    exact mul_le_mul htwoR hChooseReal (by positivity) (by positivity)
  calc
    ((overlapGraph A s t (firstPrimeVertices n Y)
        (secondPrimeVertices n Z)).card : ℝ) =
        ((overlapGraph A s t Q R).card : ℝ) := rfl
    _ ≤ (R.card : ℝ) +
        Real.sqrt
          (2 * (R.card : ℝ) * (Nat.choose Q.card 2 : ℝ)) := hKST
    _ ≤ (n.sqrt : ℝ) +
        Real.sqrt
          (2 * (n.sqrt : ℝ) * (Nat.choose n.sqrt 2 : ℝ)) :=
      add_le_add hRreal (Real.sqrt_le_sqrt hrad)
    _ = KsmallReal n := rfl

/-- Natural ceiling form of the uniform overlap estimate. -/
theorem card_overlapGraph_le_ceil_KsmallReal
    {n Y Z W s t : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (hs : 0 < s) (ht : 0 < t)
    (hst : s ≠ t) (hsW : s < W) (htW : t < W)
    (hWZ : W ≤ Z) (hZY : Z ≤ Y) :
    (overlapGraph A s t (firstPrimeVertices n Y)
      (secondPrimeVertices n Z)).card ≤ Nat.ceil (KsmallReal n) := by
  have hreal := card_overlapGraph_cast_le_KsmallReal
    hA hs ht hst hsW htW hWZ hZY
  have hceil : KsmallReal n ≤ (Nat.ceil (KsmallReal n) : ℝ) := by
    simpa using! Nat.le_ceil (KsmallReal n)
  exact_mod_cast hreal.trans hceil

/-! ## Bonferroni and the final finite budget -/

/-- The union of the small-prime fibres is contained in the full ordered
prime-pair square below `sqrt n`. -/
theorem card_smallPrimeFiber_union_le_primeCounting_sq
    (n Y Z : ℕ) (A M : Finset ℕ) :
    (M.biUnion fun s => smallPrimeFiber n Y Z A s).card ≤
      Nat.primeCounting n.sqrt ^ 2 := by
  let P := Nat.primesLE n.sqrt
  have hsub : (M.biUnion fun s => smallPrimeFiber n Y Z A s) ⊆
      P ×ˢ P := by
    intro qr hqr
    rcases Finset.mem_biUnion.mp hqr with ⟨s, hs, hEdge⟩
    have hEdge' := mem_semiprimeFiberEdges.mp hEdge
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hEdge'.1).1,
        (Finset.mem_filter.mp hEdge'.2.1).1⟩
  calc
    (M.biUnion fun s => smallPrimeFiber n Y Z A s).card ≤
        (P ×ˢ P).card := Finset.card_le_card hsub
    _ = P.card ^ 2 := by simp [pow_two]
    _ = Nat.primeCounting n.sqrt ^ 2 := by
      dsimp [P]
      rw [Nat.primesLE_card_eq_primeCounting]

/-- Bonferroni plus KST gives the requested concrete finite budget. -/
theorem card_lowMultiplierSmallPrimePiece_le
    {n Y Z W : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (hWZ : W ≤ Z) (hZY : Z ≤ Y) :
    (lowMultiplierSmallPrimePiece n Y Z W A).card ≤
      Nat.primeCounting n.sqrt ^ 2 +
        W ^ 2 * Nat.ceil (KsmallReal n) := by
  let M := positiveIcc (W - 1)
  have hoverlap : ∀ s ∈ M, ∀ t ∈ M, s ≠ t →
      (overlapGraph A s t (firstPrimeVertices n Y)
        (secondPrimeVertices n Z)).card ≤ Nat.ceil (KsmallReal n) := by
    intro s hs t ht hst
    have hs' := mem_positiveIcc.mp hs
    have ht' := mem_positiveIcc.mp ht
    exact card_overlapGraph_le_ceil_KsmallReal hA hs'.1 ht'.1 hst
      (by omega) (by omega) hWZ hZY
  have hbonf :
      ∑ s ∈ M, (smallPrimeFiber n Y Z A s).card ≤
        (M.biUnion fun s => smallPrimeFiber n Y Z A s).card +
          M.card ^ 2 * Nat.ceil (KsmallReal n) := by
    simpa [smallPrimeFiber] using!
      (sum_card_semiprimeFibres_le_union_add A M
        (firstPrimeVertices n Y) (secondPrimeVertices n Z)
        (Nat.ceil (KsmallReal n)) hoverlap)
  have hunion :
      (M.biUnion fun s => smallPrimeFiber n Y Z A s).card ≤
        Nat.primeCounting n.sqrt ^ 2 :=
    card_smallPrimeFiber_union_le_primeCounting_sq n Y Z A M
  have hMcard : M.card ≤ W := by
    dsimp [M]
    simp [positiveIcc]
  have herror : M.card ^ 2 * Nat.ceil (KsmallReal n) ≤
      W ^ 2 * Nat.ceil (KsmallReal n) := by
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hMcard 2)
  calc
    (lowMultiplierSmallPrimePiece n Y Z W A).card ≤
        ∑ s ∈ M, (smallPrimeFiber n Y Z A s).card := by
      simpa [M] using! card_lowMultiplierSmallPrimePiece_le_sum hA
    _ ≤ (M.biUnion fun s => smallPrimeFiber n Y Z A s).card +
        M.card ^ 2 * Nat.ceil (KsmallReal n) := hbonf
    _ ≤ Nat.primeCounting n.sqrt ^ 2 +
        W ^ 2 * Nat.ceil (KsmallReal n) := Nat.add_le_add hunion herror

end SmallPrimeBudget

end Erdos796
