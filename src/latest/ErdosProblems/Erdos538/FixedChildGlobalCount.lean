import ErdosProblems.Erdos538.SafeOutsideCount
import ErdosProblems.Erdos538.KernelDensityBounds

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

/-- Convert outside basis coordinates to the actual row/coefficient label. -/
def outsideActual
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (p : GoodParam K d) (z : (Fin d → K) × K) : (Fin d → K) × K :=
  (Fintype.linearCombination K p.2.1.1 z.1, z.2)

/-- Favorable child parameters together with safe assignments on `t` outside
vertices. -/
abbrev SafeGlobalParam
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] (d t : ℕ) :=
  Σ p : GoodParam K d, SafeOutside p t

/-- Forget the favorable parameterization to the actual fixed-child and
outside labels. -/
def safeGlobalParamToSample
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d t : ℕ} :
    SafeGlobalParam K d t →
      ChildSample K d × (Fin t → ((Fin d → K) × K)) := fun z =>
  (goodParamToSample z.1, fun i => outsideActual z.1 (z.2.1 i))

/-- The fixed-child safe parameterization does not overcount global label
assignments. -/
theorem safeGlobalParamToSample_injective
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d t : ℕ} :
    Function.Injective (@safeGlobalParamToSample K _ _ _ d t) := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩ heq
  have hpq : p = q := goodParamToSample_injective (congrArg Prod.fst heq)
  subst q
  have hh : hp = hq := by
    apply Subtype.ext
    funext i
    have hi := congrFun (congrArg Prod.snd heq) i
    apply Prod.ext
    · exact p.2.1.2.fintypeLinearCombination_injective (congrArg Prod.fst hi)
    · simpa [safeGlobalParamToSample, outsideActual] using congrArg Prod.snd hi
  subst hq
  rfl

/-- At least half of the outside assignments survive for every favorable
child, hence the safe global parameter space retains the same factor after
summing over all favorable children. -/
theorem safeGlobalParam_half
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d t : ℕ} (hd : 0 < d) (hq : 2 * t ≤ (Nat.card K) ^ 2) :
    Nat.card (GoodParam K d) * Nat.card (((Fin d → K) × K)) ^ t ≤
      2 * Nat.card (SafeGlobalParam K d t) := by
  letI : Fintype (GoodParam K d) := Fintype.ofFinite _
  letI safeFinite (p : GoodParam K d) : Finite (SafeOutside p t) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hsig : Nat.card (SafeGlobalParam K d t) =
      ∑ p : GoodParam K d, Nat.card (SafeOutside p t) := Nat.card_sigma
  calc
    Nat.card (GoodParam K d) * Nat.card (((Fin d → K) × K)) ^ t =
        ∑ _p : GoodParam K d, Nat.card (((Fin d → K) × K)) ^ t := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ ∑ p : GoodParam K d, 2 * Nat.card (SafeOutside p t) := by
      apply Finset.sum_le_sum
      intro p _
      exact half_outside_assignments_safe p hd hq
    _ = 2 * ∑ p : GoodParam K d, Nat.card (SafeOutside p t) := by
      rw [Finset.mul_sum]
    _ = 2 * Nat.card (SafeGlobalParam K d t) := by rw [hsig]

/-- Combining the `1/(8q)` favorable-child count and the one-half safety
survival gives a fixed-child safe density at least `1/(16q)`. -/
theorem sixteen_q_mul_safeGlobal_ge_all
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d t : ℕ} (hd : 0 < d)
    (hqsize : 2 * (d + 1) ≤ Fintype.card K)
    (houtside : 2 * t ≤ (Nat.card K) ^ 2) :
    Nat.card (ChildSample K d) * Nat.card (((Fin d → K) × K)) ^ t ≤
      16 * Fintype.card K * Nat.card (SafeGlobalParam K d t) := by
  have hgood := eight_q_mul_goodParam_ge_childSample d hd hqsize
  have hsafe := safeGlobalParam_half (K := K) hd houtside
  calc
    Nat.card (ChildSample K d) * Nat.card (((Fin d → K) × K)) ^ t ≤
        (8 * Fintype.card K * Nat.card (GoodParam K d)) *
          Nat.card (((Fin d → K) × K)) ^ t := Nat.mul_le_mul_right _ hgood
    _ ≤ 8 * Fintype.card K *
          (2 * Nat.card (SafeGlobalParam K d t)) := by
      calc
        (8 * Fintype.card K * Nat.card (GoodParam K d)) *
            Nat.card (((Fin d → K) × K)) ^ t =
          8 * Fintype.card K *
            (Nat.card (GoodParam K d) *
              Nat.card (((Fin d → K) × K)) ^ t) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hsafe
    _ = 16 * Fintype.card K * Nat.card (SafeGlobalParam K d t) := by ring

end Erdos538.IsotropicKernel
