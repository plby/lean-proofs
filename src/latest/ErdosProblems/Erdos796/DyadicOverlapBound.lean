import ErdosProblems.Erdos796.DyadicBoxes
import ErdosProblems.Erdos796.SemiprimeTailBudget
import Mathlib.Algebra.Order.Floor.Ring

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A dyadic bound for semiprime-tail overlaps

The dependent prime-pair overlap is partitioned by the dyadic scale of its
second prime.  Each part is projected injectively to ordinary ordered pairs,
then enlarged only to the bipartite graph on its actual coordinate images.
This makes the multiplier inequalities needed by the existing C4 argument
automatic.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

namespace DyadicOverlapBound

open DyadicBoxes PairwiseOverlap SemiprimeTailBudget

/-- Scales which can contain a tail prime: the dyadic interval reaches above
`Z`, and its lower endpoint does not exceed `sqrt n`. -/
def tailScaleIndices (n Z : ℕ) : Finset ℕ :=
  (scaleIndices n).filter fun k =>
    Z < 2 ^ (k + 1) ∧ 2 ^ k ≤ n.sqrt

@[simp]
theorem mem_tailScaleIndices {n Z k : ℕ} :
    k ∈ tailScaleIndices n Z ↔
      k ∈ scaleIndices n ∧ Z < 2 ^ (k + 1) ∧
        2 ^ k ≤ n.sqrt := by
  simp [tailScaleIndices]

/-- The part of one overlap whose second prime has dyadic scale `k`. -/
def overlapScalePart
    (n Z : ℕ) (A : Finset ℕ) (s t k : ℕ) :
    Finset (Σ _Q : ℕ, ℕ) :=
  (multiplierOverlap n Z A s t).filter fun Qr =>
    dyadicScale Qr.2 = k

@[simp]
theorem mem_overlapScalePart
    {n Z s t k Q r : ℕ} {A : Finset ℕ} :
    (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈ overlapScalePart n Z A s t k ↔
      (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈ multiplierOverlap n Z A s t ∧
        dyadicScale r = k := by
  simp [overlapScalePart]

/-- Every overlap edge is indexed by one of the displayed tail scales. -/
theorem overlap_scale_mem_tailScaleIndices
    {n Z s t Q r : ℕ} {A : Finset ℕ}
    (hQr : (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈
      multiplierOverlap n Z A s t) :
    dyadicScale r ∈ tailScaleIndices n Z := by
  have hmem := mem_multiplierOverlap.mp hQr
  have hQ := mem_largePrimes.mp hmem.1
  have hr := mem_newPrimes.mp hmem.2.1
  have hrpos : 0 < r := hr.2.2.pos
  have hrleN : r ≤ n := hr.2.1.trans (Nat.div_le_self n Q)
  have hrIcc : r ∈ positiveIcc n :=
    mem_positiveIcc.mpr ⟨hrpos, hrleN⟩
  have hrScale := bounds_of_mem_scaleInterval (mem_own_scaleInterval hrIcc)
  have hrleSqrt : r ≤ n.sqrt :=
    hr.2.1.trans (div_le_sqrt_of_sqrt_lt hQ.1)
  exact mem_tailScaleIndices.mpr
    ⟨dyadicScale_mem_scaleIndices hrIcc,
      hr.1.trans hrScale.2, hrScale.1.trans hrleSqrt⟩

/-- Exact cardinal decomposition of an overlap into its dyadic second-prime
parts. -/
theorem card_multiplierOverlap_eq_sum_scaleParts
    (n Z : ℕ) (A : Finset ℕ) (s t : ℕ) :
    (multiplierOverlap n Z A s t).card =
      ∑ k ∈ tailScaleIndices n Z,
        (overlapScalePart n Z A s t k).card := by
  let H := multiplierOverlap n Z A s t
  let κ : (Σ _Q : ℕ, ℕ) → ℕ := fun Qr => dyadicScale Qr.2
  have hmap : Set.MapsTo κ (H : Set (Σ _Q : ℕ, ℕ))
      (tailScaleIndices n Z : Set ℕ) := by
    intro Qr hQr
    rcases Qr with ⟨Q, r⟩
    exact overlap_scale_mem_tailScaleIndices hQr
  simpa [H, κ, overlapScalePart] using!
    (Finset.card_eq_sum_card_fiberwise hmap)

/-- Forget the (constant) dependent type of a tail parameter. -/
def sigmaPairToProd : (Σ _Q : ℕ, ℕ) → ℕ × ℕ :=
  fun Qr => (Qr.1, Qr.2)

theorem sigmaPairToProd_injective : Function.Injective sigmaPairToProd := by
  rintro ⟨Q, r⟩ ⟨Q', r'⟩ h
  have hQ : Q = Q' := congrArg Prod.fst h
  have hr : r = r' := congrArg Prod.snd h
  subst Q'
  subst r'
  rfl

/-- Ordinary ordered-pair edges obtained from one dyadic part. -/
def scaleEdges
    (n Z : ℕ) (A : Finset ℕ) (s t k : ℕ) : Finset (ℕ × ℕ) :=
  (overlapScalePart n Z A s t k).image sigmaPairToProd

theorem card_scaleEdges
    (n Z : ℕ) (A : Finset ℕ) (s t k : ℕ) :
    (scaleEdges n Z A s t k).card =
      (overlapScalePart n Z A s t k).card := by
  rw [scaleEdges, Finset.card_image_of_injective]
  exact sigmaPairToProd_injective

@[simp]
theorem mem_scaleEdges
    {n Z s t k Q r : ℕ} {A : Finset ℕ} :
    (Q, r) ∈ scaleEdges n Z A s t k ↔
      (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈ multiplierOverlap n Z A s t ∧
        dyadicScale r = k := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨⟨Q', r'⟩, hpart, heq⟩
    have hQ : Q' = Q := congrArg Prod.fst heq
    have hr : r' = r := congrArg Prod.snd heq
    subst Q'
    subst r'
    exact mem_overlapScalePart.mp hpart
  · rintro ⟨hOverlap, hscale⟩
    exact Finset.mem_image.mpr
      ⟨⟨Q, r⟩, mem_overlapScalePart.mpr ⟨hOverlap, hscale⟩, rfl⟩

/-- Actual first-coordinate vertices of one scale part. -/
def leftVertices
    (n Z : ℕ) (A : Finset ℕ) (s t k : ℕ) : Finset ℕ :=
  (scaleEdges n Z A s t k).image Prod.fst

/-- Actual second-coordinate vertices of one scale part. -/
def rightVertices
    (n Z : ℕ) (A : Finset ℕ) (s t k : ℕ) : Finset ℕ :=
  (scaleEdges n Z A s t k).image Prod.snd

@[simp]
theorem mem_leftVertices
    {n Z s t k Q : ℕ} {A : Finset ℕ} :
    Q ∈ leftVertices n Z A s t k ↔
      ∃ r : ℕ, (Q, r) ∈ scaleEdges n Z A s t k := by
  simp [leftVertices]

@[simp]
theorem mem_rightVertices
    {n Z s t k r : ℕ} {A : Finset ℕ} :
    r ∈ rightVertices n Z A s t k ↔
      ∃ Q : ℕ, (Q, r) ∈ scaleEdges n Z A s t k := by
  simp [rightVertices]

/-- A scale edge is an edge of the ordinary overlap graph on its actual
coordinate images. -/
theorem scaleEdges_subset_overlapGraph
    (n Z : ℕ) (A : Finset ℕ) (s t k : ℕ) :
    scaleEdges n Z A s t k ⊆
      overlapGraph A s t (leftVertices n Z A s t k)
        (rightVertices n Z A s t k) := by
  rintro ⟨Q, r⟩ hEdge
  have hscale := mem_scaleEdges.mp hEdge
  have hmem := mem_multiplierOverlap.mp hscale.1
  have htail : (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈ tailParameters n Z :=
    mk_mem_tailParameters.mpr ⟨hmem.1, hmem.2.1⟩
  rcases tailParameter_spec htail with
    ⟨hroot, hQn, hQprime, hZr, hrquot, hrprime, hrQ, hQr⟩
  exact mem_overlapGraph.mpr
    ⟨mem_leftVertices.mpr ⟨r, hEdge⟩,
      mem_rightVertices.mpr ⟨Q, hEdge⟩,
      hQprime, hrprime, hrQ,
      hmem.2.2.2.2.1, hmem.2.2.2.2.2⟩

/-- On the actual left vertex image, both multipliers are smaller than every
vertex once they are below `Z`. -/
theorem multipliers_lt_leftVertices
    {n Z s t k : ℕ} {A : Finset ℕ}
    (hsZ : s < Z) (htZ : t < Z) :
    ∀ Q ∈ leftVertices n Z A s t k, s < Q ∧ t < Q := by
  intro Q hQ
  rcases mem_leftVertices.mp hQ with ⟨r, hEdge⟩
  have hmem := mem_multiplierOverlap.mp (mem_scaleEdges.mp hEdge).1
  have htail : (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈ tailParameters n Z :=
    mk_mem_tailParameters.mpr ⟨hmem.1, hmem.2.1⟩
  rcases tailParameter_spec htail with
    ⟨hroot, hQn, hQprime, hZr, hrquot, hrprime, hrQ, hQr⟩
  exact ⟨(hsZ.trans hZr).trans hrQ, (htZ.trans hZr).trans hrQ⟩

/-- The same multiplier inequalities hold on the actual right vertex image. -/
theorem multipliers_lt_rightVertices
    {n Z s t k : ℕ} {A : Finset ℕ}
    (hsZ : s < Z) (htZ : t < Z) :
    ∀ r ∈ rightVertices n Z A s t k, s < r ∧ t < r := by
  intro r hr
  rcases mem_rightVertices.mp hr with ⟨Q, hEdge⟩
  have hmem := mem_multiplierOverlap.mp (mem_scaleEdges.mp hEdge).1
  have hnew := mem_newPrimes.mp hmem.2.1
  exact ⟨hsZ.trans hnew.1, htZ.trans hnew.1⟩

/-- The right vertex image stays in its dyadic interval. -/
theorem rightVertices_subset_scaleInterval
    (n Z : ℕ) (A : Finset ℕ) (s t k : ℕ) :
    rightVertices n Z A s t k ⊆ scaleInterval n k := by
  intro r hr
  rcases mem_rightVertices.mp hr with ⟨Q, hEdge⟩
  have hscale := mem_scaleEdges.mp hEdge
  have hmem := mem_multiplierOverlap.mp hscale.1
  have hnew := mem_newPrimes.mp hmem.2.1
  have hrpos : 0 < r := hnew.2.2.pos
  have hrle : r ≤ n := hnew.2.1.trans (Nat.div_le_self n Q)
  exact mem_scaleInterval.mpr ⟨hrpos, hrle, hscale.2⟩

theorem card_rightVertices_le_pow
    (n Z : ℕ) (A : Finset ℕ) (s t k : ℕ) :
    (rightVertices n Z A s t k).card ≤ 2 ^ k :=
  (Finset.card_le_card
    (rightVertices_subset_scaleInterval n Z A s t k)).trans
      (card_scaleInterval_le_pow n k)

/-- If an edge has `r ≥ 2^k` and `Q r ≤ n`, then its left endpoint is
at most `n/2^k`. -/
theorem leftVertices_subset_positiveIcc_natDivPow
    (n Z : ℕ) (A : Finset ℕ) (s t k : ℕ) :
    leftVertices n Z A s t k ⊆ positiveIcc (n / 2 ^ k) := by
  intro Q hQ
  rcases mem_leftVertices.mp hQ with ⟨r, hEdge⟩
  have hscale := mem_scaleEdges.mp hEdge
  have hmem := mem_multiplierOverlap.mp hscale.1
  have htail : (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈ tailParameters n Z :=
    mk_mem_tailParameters.mpr ⟨hmem.1, hmem.2.1⟩
  rcases tailParameter_spec htail with
    ⟨hroot, hQn, hQprime, hZr, hrquot, hrprime, hrQ, hQr⟩
  have hrIcc : r ∈ scaleInterval n k :=
    rightVertices_subset_scaleInterval n Z A s t k
      (mem_rightVertices.mpr ⟨Q, hEdge⟩)
  have hpwr : 2 ^ k ≤ r := (bounds_of_mem_scaleInterval hrIcc).1
  have hQpow : Q * 2 ^ k ≤ n :=
    (Nat.mul_le_mul_left Q hpwr).trans hQr
  have hpowpos : 0 < 2 ^ k := pow_pos (by norm_num) _
  exact mem_positiveIcc.mpr
    ⟨hQprime.one_le, (Nat.le_div_iff_mul_le hpowpos).mpr hQpow⟩

theorem card_leftVertices_le_natDivPow
    (n Z : ℕ) (A : Finset ℕ) (s t k : ℕ) :
    (leftVertices n Z A s t k).card ≤ n / 2 ^ k := by
  have hcard := Finset.card_le_card
    (leftVertices_subset_positiveIcc_natDivPow n Z A s t k)
  simpa [positiveIcc] using! hcard

/-- Real KST majorant for one dyadic scale. -/
noncomputable def scaleKSTRealBound (n k : ℕ) : ℝ :=
  (2 ^ k : ℕ) +
    Real.sqrt
      (2 * (2 ^ k : ℕ) *
        (Nat.choose (n / 2 ^ k) 2 : ℝ))

/-- Natural ceiling of the one-scale KST majorant. -/
noncomputable def overlapScaleBound (n k : ℕ) : ℕ :=
  Nat.ceil (scaleKSTRealBound n k)

/-- Explicit total dyadic overlap budget. -/
noncomputable def overlapDyadicBound (n Z : ℕ) : ℕ :=
  ∑ k ∈ tailScaleIndices n Z, overlapScaleBound n k

/-- One scale part satisfies the KST bound after replacing its actual vertex
cardinalities by the dyadic interval bounds. -/
theorem card_overlapScalePart_cast_le_scaleKSTRealBound
    {n Z s t k : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (hs : 0 < s) (ht : 0 < t)
    (hst : s ≠ t) (hsZ : s < Z) (htZ : t < Z) :
    ((overlapScalePart n Z A s t k).card : ℝ) ≤
      scaleKSTRealBound n k := by
  let L := leftVertices n Z A s t k
  let R := rightVertices n Z A s t k
  have hsub : scaleEdges n Z A s t k ⊆ overlapGraph A s t L R := by
    simpa [L, R] using! scaleEdges_subset_overlapGraph n Z A s t k
  have hcard :
      ((scaleEdges n Z A s t k).card : ℝ) ≤
        ((overlapGraph A s t L R).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hKST :
      ((overlapGraph A s t L R).card : ℝ) ≤
        (R.card : ℝ) +
          Real.sqrt (2 * (R.card : ℝ) *
            (Nat.choose L.card 2 : ℝ)) := by
    exact overlapGraph_card_le hA hs ht hst
      (by simpa [L] using!
        (multipliers_lt_leftVertices
          (A := A) (k := k) hsZ htZ))
      (by simpa [R] using!
        (multipliers_lt_rightVertices
          (A := A) (k := k) hsZ htZ))
  have hRnat : R.card ≤ 2 ^ k := by
    simpa [R] using! card_rightVertices_le_pow n Z A s t k
  have hLnat : L.card ≤ n / 2 ^ k := by
    simpa [L] using! card_leftVertices_le_natDivPow n Z A s t k
  have hRreal : (R.card : ℝ) ≤ (2 ^ k : ℕ) := by
    exact_mod_cast hRnat
  have hChooseNat : Nat.choose L.card 2 ≤
      Nat.choose (n / 2 ^ k) 2 := Nat.choose_le_choose 2 hLnat
  have hChooseReal : (Nat.choose L.card 2 : ℝ) ≤
      (Nat.choose (n / 2 ^ k) 2 : ℝ) := by
    exact_mod_cast hChooseNat
  have hrad :
      2 * (R.card : ℝ) * (Nat.choose L.card 2 : ℝ) ≤
        2 * (2 ^ k : ℕ) *
          (Nat.choose (n / 2 ^ k) 2 : ℝ) := by
    have htwoR : 2 * (R.card : ℝ) ≤ 2 * (2 ^ k : ℕ) := by
      exact mul_le_mul_of_nonneg_left hRreal (by norm_num)
    exact mul_le_mul htwoR hChooseReal (by positivity) (by positivity)
  calc
    ((overlapScalePart n Z A s t k).card : ℝ) =
        ((scaleEdges n Z A s t k).card : ℝ) := by
      exact_mod_cast (card_scaleEdges n Z A s t k).symm
    _ ≤ ((overlapGraph A s t L R).card : ℝ) := hcard
    _ ≤ (R.card : ℝ) +
          Real.sqrt (2 * (R.card : ℝ) *
            (Nat.choose L.card 2 : ℝ)) := hKST
    _ ≤ (2 ^ k : ℕ) +
          Real.sqrt (2 * (2 ^ k : ℕ) *
            (Nat.choose (n / 2 ^ k) 2 : ℝ)) := by
      exact add_le_add hRreal (Real.sqrt_le_sqrt hrad)
    _ = scaleKSTRealBound n k := rfl

/-- Natural one-scale form of the KST bound. -/
theorem card_overlapScalePart_le_overlapScaleBound
    {n Z s t k : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (hs : 0 < s) (ht : 0 < t)
    (hst : s ≠ t) (hsZ : s < Z) (htZ : t < Z) :
    (overlapScalePart n Z A s t k).card ≤ overlapScaleBound n k := by
  have hreal := card_overlapScalePart_cast_le_scaleKSTRealBound
    hA hs ht hst hsZ htZ (k := k)
  have hceil : scaleKSTRealBound n k ≤
      (overlapScaleBound n k : ℝ) := by
    simpa [overlapScaleBound] using! Nat.le_ceil (scaleKSTRealBound n k)
  exact_mod_cast hreal.trans hceil

/-- Dyadic KST bound for the full dependent-pair multiplier overlap. -/
theorem card_multiplierOverlap_le_overlapDyadicBound
    {n Z s t : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (hs : 0 < s) (ht : 0 < t)
    (hst : s ≠ t) (hsZ : s < Z) (htZ : t < Z) :
    (multiplierOverlap n Z A s t).card ≤ overlapDyadicBound n Z := by
  rw [card_multiplierOverlap_eq_sum_scaleParts]
  rw [overlapDyadicBound]
  apply Finset.sum_le_sum
  intro k hk
  exact card_overlapScalePart_le_overlapScaleBound
    hA hs ht hst hsZ htZ

/-- A convenience form when the multipliers are known to lie below a smaller
cutoff `W ≤ Z`. -/
theorem card_multiplierOverlap_le_overlapDyadicBound_of_lt_of_le
    {n Z W s t : ℕ} {A : Finset ℕ}
    (hA : Admissible n A) (hs : 0 < s) (ht : 0 < t)
    (hst : s ≠ t) (hsW : s < W) (htW : t < W) (hWZ : W ≤ Z) :
    (multiplierOverlap n Z A s t).card ≤ overlapDyadicBound n Z :=
  card_multiplierOverlap_le_overlapDyadicBound
    hA hs ht hst (hsW.trans_le hWZ) (htW.trans_le hWZ)

/-! ## A coarse real estimate for the explicit budget -/

theorem cast_choose_two_le_sq_div_two (m : ℕ) :
    (Nat.choose m 2 : ℝ) ≤ (m : ℝ) ^ 2 / 2 := by
  rw [Nat.cast_choose_two]
  have hsub : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast Nat.sub_le m 1
  have hm : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsub hm
  nlinarith

/-- Every active one-scale real majorant is bounded by a square-root term
plus `2n/√Z`.  The constant `2` deliberately absorbs floor and dyadic
endpoint losses. -/
theorem scaleKSTRealBound_le
    {n Z k : ℕ} (hZ : 0 < Z) (hk : k ∈ tailScaleIndices n Z) :
    scaleKSTRealBound n k ≤
      (n.sqrt : ℝ) + 2 * (n : ℝ) / Real.sqrt (Z : ℝ) := by
  let P : ℕ := 2 ^ k
  let M : ℕ := n / P
  have hk' := mem_tailScaleIndices.mp hk
  have hPsqrtNat : P ≤ n.sqrt := by simpa [P] using! hk'.2.2
  have hZPNat : Z ≤ 2 * P := by
    have hreach := hk'.2.1
    dsimp [P]
    rw [pow_succ] at hreach
    omega
  have hPMNat : P * M ≤ n := by
    dsimp [M]
    simpa [Nat.mul_comm] using! Nat.div_mul_le_self n P
  have hPsqrt : (P : ℝ) ≤ (n.sqrt : ℝ) := by
    exact_mod_cast hPsqrtNat
  have hZP : (Z : ℝ) ≤ 2 * (P : ℝ) := by
    exact_mod_cast hZPNat
  have hPM : (P : ℝ) * (M : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hPMNat
  have hPMnonneg : 0 ≤ (P : ℝ) * (M : ℝ) := by positivity
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hPMsq : ((P : ℝ) * (M : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 :=
    (sq_le_sq₀ hPMnonneg hnnonneg).2 hPM
  have hchoose := cast_choose_two_le_sq_div_two M
  have hrad :
      2 * (P : ℝ) * (Nat.choose M 2 : ℝ) ≤
        (P : ℝ) * (M : ℝ) ^ 2 := by
    calc
      2 * (P : ℝ) * (Nat.choose M 2 : ℝ) ≤
          2 * (P : ℝ) * ((M : ℝ) ^ 2 / 2) := by
        exact mul_le_mul_of_nonneg_left hchoose (by positivity)
      _ = (P : ℝ) * (M : ℝ) ^ 2 := by ring
  have hcross :
      (P : ℝ) * (M : ℝ) ^ 2 * (Z : ℝ) ≤
        2 * (n : ℝ) ^ 2 := by
    calc
      (P : ℝ) * (M : ℝ) ^ 2 * (Z : ℝ) ≤
          (P : ℝ) * (M : ℝ) ^ 2 * (2 * (P : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hZP (by positivity)
      _ = 2 * ((P : ℝ) * (M : ℝ)) ^ 2 := by ring
      _ ≤ 2 * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hPMsq (by norm_num)
  have hradZ :
      (2 * (P : ℝ) * (Nat.choose M 2 : ℝ)) * (Z : ℝ) ≤
        2 * (n : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_right hrad (by positivity)).trans hcross
  have hZreal : (0 : ℝ) < (Z : ℝ) := by exact_mod_cast hZ
  have hsqrtZ : 0 < Real.sqrt (Z : ℝ) := Real.sqrt_pos.2 hZreal
  have hsqrtBound :
      Real.sqrt (2 * (P : ℝ) * (Nat.choose M 2 : ℝ)) ≤
        2 * (n : ℝ) / Real.sqrt (Z : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [div_pow, Real.sq_sqrt hZreal.le, le_div_iff₀ hZreal]
      nlinarith [hradZ]
  change (P : ℝ) +
      Real.sqrt (2 * (P : ℝ) * (Nat.choose M 2 : ℝ)) ≤ _
  exact add_le_add hPsqrt hsqrtBound

/-- There are at most `log₂ n + 1` active tail scales. -/
theorem card_tailScaleIndices_le (n Z : ℕ) :
    (tailScaleIndices n Z).card ≤ Nat.log 2 n + 1 := by
  calc
    (tailScaleIndices n Z).card ≤ (scaleIndices n).card :=
      Finset.card_filter_le _ _
    _ = Nat.log 2 n + 1 := card_scaleIndices n

/-- The ceiling of an active one-scale majorant loses at most one. -/
theorem overlapScaleBound_cast_le
    {n Z k : ℕ} (hZ : 0 < Z) (hk : k ∈ tailScaleIndices n Z) :
    (overlapScaleBound n k : ℝ) ≤
      (n.sqrt : ℝ) + 2 * (n : ℝ) / Real.sqrt (Z : ℝ) + 1 := by
  have hnonneg : 0 ≤ scaleKSTRealBound n k := by
    simp only [scaleKSTRealBound]
    positivity
  have hceil : (overlapScaleBound n k : ℝ) <
      scaleKSTRealBound n k + 1 := by
    simpa [overlapScaleBound] using!
      (Nat.ceil_lt_add_one hnonneg)
  have hadd : scaleKSTRealBound n k + 1 ≤
      (n.sqrt : ℝ) + 2 * (n : ℝ) / Real.sqrt (Z : ℝ) + 1 := by
    simpa only [add_comm] using!
      (add_le_add_right (scaleKSTRealBound_le hZ hk) 1)
  exact (le_of_lt hceil).trans hadd

/-- Coarse aggregate estimate for the explicit natural dyadic budget. -/
theorem overlapDyadicBound_cast_le_card_mul
    {n Z : ℕ} (hZ : 0 < Z) :
    (overlapDyadicBound n Z : ℝ) ≤
      ((tailScaleIndices n Z).card : ℝ) *
        ((n.sqrt : ℝ) + 2 * (n : ℝ) / Real.sqrt (Z : ℝ) + 1) := by
  rw [overlapDyadicBound, Nat.cast_sum]
  calc
    ∑ k ∈ tailScaleIndices n Z, (overlapScaleBound n k : ℝ) ≤
        ∑ _k ∈ tailScaleIndices n Z,
          ((n.sqrt : ℝ) + 2 * (n : ℝ) / Real.sqrt (Z : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      exact overlapScaleBound_cast_le hZ hk
    _ = ((tailScaleIndices n Z).card : ℝ) *
          ((n.sqrt : ℝ) + 2 * (n : ℝ) / Real.sqrt (Z : ℝ) + 1) := by
      simp
      ring

/-- A fully explicit logarithmic version of the coarse aggregate estimate. -/
theorem overlapDyadicBound_cast_le
    {n Z : ℕ} (hZ : 0 < Z) :
    (overlapDyadicBound n Z : ℝ) ≤
      (Nat.log 2 n + 1 : ℕ) *
        ((n.sqrt : ℝ) + 2 * (n : ℝ) / Real.sqrt (Z : ℝ) + 1) := by
  refine (overlapDyadicBound_cast_le_card_mul hZ).trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast card_tailScaleIndices_le n Z
  · positivity

end DyadicOverlapBound

end Erdos796
