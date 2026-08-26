import ErdosProblems.Erdos796.SmoothAugmentation
import ErdosProblems.Erdos796.SemiprimeFibers

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The exact finite semiprime-tail budget

The prime tail used to augment the smooth model has a direct parameter-space
interpretation.  Its elements are pairs `(Q,r)` with `Q` a large prime and
`r` a prime in `(Z,n/Q]`.  Multiplier fibres are filters of this one finite
space, so their union is paid for exactly once; a finite Bonferroni estimate
then adds only the supplied pairwise-overlap error.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

namespace SemiprimeTailBudget

open PairwiseOverlap

/-- The finite semiprime-tail parameter space.  A dependent pair is used so
that the second finset may depend on the first coordinate. -/
def tailParameters (n Z : ℕ) : Finset (Σ _Q : ℕ, ℕ) :=
  (largePrimes n).sigma fun Q => newPrimes Z (n / Q)

@[simp]
theorem mk_mem_tailParameters {n Z Q r : ℕ} :
    (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈ tailParameters n Z ↔
      Q ∈ largePrimes n ∧ r ∈ newPrimes Z (n / Q) := by
  simp [tailParameters]

/-- Expanded arithmetic specifications of a tail parameter. -/
theorem tailParameter_spec {n Z Q r : ℕ}
    (hQr : (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈ tailParameters n Z) :
    n.sqrt < Q ∧ Q ≤ n ∧ Q.Prime ∧
      Z < r ∧ r ≤ n / Q ∧ r.Prime ∧ r < Q ∧ Q * r ≤ n := by
  have hmem := mk_mem_tailParameters.mp hQr
  have hQ := mem_largePrimes.mp hmem.1
  have hr := mem_newPrimes.mp hmem.2
  have hquot : n / Q ≤ n.sqrt := div_le_sqrt_of_sqrt_lt hQ.1
  have hrQ : r < Q := (hr.2.1.trans hquot).trans_lt hQ.1
  have hQrle : Q * r ≤ n := by
    have hQpos : 0 < Q := hQ.2.2.pos
    simpa [Nat.mul_comm] using!
      (Nat.le_div_iff_mul_le hQpos).mp hr.2.1
  exact ⟨hQ.1, hQ.2.1, hQ.2.2, hr.1, hr.2.1, hr.2.2,
    hrQ, hQrle⟩

/-- The parameter-space cardinality is exactly the prime-tail score already
used by smooth augmentation. -/
theorem card_tailParameters (n Z : ℕ) :
    (tailParameters n Z).card =
      SmoothAugmentation.primeTailScore n Z := by
  rw [tailParameters, Finset.card_sigma]
  calc
    (∑ Q ∈ largePrimes n, (newPrimes Z (n / Q)).card) =
        modelScore n (fun j => newPrimes Z j) :=
      sum_primes_eq_modelScore n (fun j => newPrimes Z j)
    _ = SmoothAugmentation.primeTailScore n Z := by
      rfl

/-- The positive-multiplier fibre inside the tail budget. -/
def multiplierFiberEdges (n Z : ℕ) (A : Finset ℕ) (s : ℕ) :
    Finset (Σ _Q : ℕ, ℕ) :=
  (tailParameters n Z).filter fun Qr =>
    0 < s ∧ multipliedPrimePair s Qr.1 Qr.2 ∈ A

@[simp]
theorem mem_multiplierFiberEdges {n Z s Q r : ℕ} {A : Finset ℕ} :
    (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈ multiplierFiberEdges n Z A s ↔
      0 < s ∧ Q ∈ largePrimes n ∧
        r ∈ newPrimes Z (n / Q) ∧
        multipliedPrimePair s Q r ∈ A := by
  simp [multiplierFiberEdges, and_assoc, and_left_comm]

/-- The overlap of two multiplier fibres, expressed on the same dependent
prime-pair budget. -/
def multiplierOverlap (n Z : ℕ) (A : Finset ℕ) (s t : ℕ) :
    Finset (Σ _Q : ℕ, ℕ) :=
  (tailParameters n Z).filter fun Qr =>
    0 < s ∧ 0 < t ∧
      multipliedPrimePair s Qr.1 Qr.2 ∈ A ∧
      multipliedPrimePair t Qr.1 Qr.2 ∈ A

@[simp]
theorem mem_multiplierOverlap {n Z s t Q r : ℕ} {A : Finset ℕ} :
    (⟨Q, r⟩ : Σ _Q : ℕ, ℕ) ∈
        multiplierOverlap n Z A s t ↔
      Q ∈ largePrimes n ∧ r ∈ newPrimes Z (n / Q) ∧
        0 < s ∧ 0 < t ∧
        multipliedPrimePair s Q r ∈ A ∧
        multipliedPrimePair t Q r ∈ A := by
  simp [multiplierOverlap, and_assoc, and_left_comm, and_comm]

/-- Pairwise intersection is exactly the labelled variable-range overlap. -/
theorem inter_multiplierFiberEdges
    (n Z : ℕ) (A : Finset ℕ) (s t : ℕ) :
    multiplierFiberEdges n Z A s ∩ multiplierFiberEdges n Z A t =
      multiplierOverlap n Z A s t := by
  ext Qr
  rcases Qr with ⟨Q, r⟩
  simp only [Finset.mem_inter, mem_multiplierFiberEdges,
    mem_multiplierOverlap]
  tauto

/-- The union over any finite collection of multipliers.  Nonpositive
multiplier labels contribute the empty fibre by definition. -/
def multiplierUnion (n Z : ℕ) (A M : Finset ℕ) :
    Finset (Σ _Q : ℕ, ℕ) :=
  M.biUnion fun s => multiplierFiberEdges n Z A s

/-- Every edge in the multiplier union belongs to the single tail budget. -/
theorem multiplierUnion_subset_tailParameters
    (n Z : ℕ) (A M : Finset ℕ) :
    multiplierUnion n Z A M ⊆ tailParameters n Z := by
  intro Qr hQr
  rcases Finset.mem_biUnion.mp hQr with ⟨s, hs, hEdge⟩
  exact (Finset.mem_filter.mp hEdge).1

/-- Hence the union is charged at most once to `primeTailScore`. -/
theorem card_multiplierUnion_le_primeTailScore
    (n Z : ℕ) (A M : Finset ℕ) :
    (multiplierUnion n Z A M).card ≤
      SmoothAugmentation.primeTailScore n Z := by
  calc
    (multiplierUnion n Z A M).card ≤ (tailParameters n Z).card :=
      Finset.card_le_card (multiplierUnion_subset_tailParameters n Z A M)
    _ = SmoothAugmentation.primeTailScore n Z := card_tailParameters n Z

/-- Exact finite Bonferroni budget.  The hypothesis is the explicit
pairwise-overlap estimate required from the C4/KST argument; no asymptotic
input is used here. -/
theorem sum_card_multiplierFibres_le_primeTailScore_add
    {n Z K : ℕ} {A M : Finset ℕ}
    (hoverlap : ∀ s ∈ M, ∀ t ∈ M, s ≠ t →
      (multiplierOverlap n Z A s t).card ≤ K) :
    ∑ s ∈ M, (multiplierFiberEdges n Z A s).card ≤
      SmoothAugmentation.primeTailScore n Z + M.card ^ 2 * K := by
  have hbonf :
      ∑ s ∈ M, (multiplierFiberEdges n Z A s).card ≤
        (multiplierUnion n Z A M).card + M.card ^ 2 * K := by
    apply sum_card_le_card_biUnion_add_sq_mul
    intro s hs t ht hst
    rw [inter_multiplierFiberEdges]
    exact hoverlap s hs t ht hst
  exact hbonf.trans (Nat.add_le_add_right
    (card_multiplierUnion_le_primeTailScore n Z A M) _)

end SemiprimeTailBudget

end Erdos796
