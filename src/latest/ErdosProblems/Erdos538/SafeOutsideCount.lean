import ErdosProblems.Erdos538.FiniteUnionBound
import ErdosProblems.Erdos538.GoodParameterCount

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

/-- Bad outside coordinate/coefficient labels for a favorable child. -/
def BadOutside
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (p : GoodParam K d) : Set ((Fin d → K) × K) :=
  {z | (dotProductEquiv K (Fin d)) (crossVector p) z.1 = 0 ∧
    z.2 = -outsideQuad p z.1}

/-- Outside assignments avoiding every bad extension coordinate. -/
def SafeOutside
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (p : GoodParam K d) (t : ℕ) :=
  {f : Fin t → ((Fin d → K) × K) // ∀ i, f i ∉ BadOutside p}

@[simp] theorem natCard_outsideLabel
    {K : Type*} [Field K] [Fintype K] (d : ℕ) :
    Nat.card ((Fin d → K) × K) = Nat.card K ^ (d + 1) := by
  rw [Nat.card_prod, Nat.card_fun]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [pow_succ]

/-- The bad outside-label set has exactly `q^(d-1)` elements. -/
theorem natCard_badOutside
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] {d : ℕ}
    (p : GoodParam K d) :
    Nat.card (BadOutside p) = Nat.card K ^ (d - 1) := by
  exact natCard_badOutsideCoords p

/-- If `2t ≤ q²`, at least half of all `t`-tuples of outside labels avoid the
bad set. -/
theorem half_outside_assignments_safe
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {d t : ℕ} (p : GoodParam K d) (hd : 0 < d)
    (hq : 2 * t ≤ (Nat.card K) ^ 2) :
    Nat.card (((Fin d → K) × K)) ^ t ≤ 2 * Nat.card (SafeOutside p t) := by
  let L := (Fin d → K) × K
  let B : Set L := BadOutside p
  let U : Set (Fin t → L) := {f | ∃ i, f i ∈ B}
  have hU := ncard_exists_bad_le (I := Fin t) B
  have hI : Nat.card (Fin t) = t := by simp
  have hB : Nat.card B = Nat.card K ^ (d - 1) := natCard_badOutside p
  have hL : Nat.card L = Nat.card K ^ (d + 1) := natCard_outsideLabel d
  rw [hI, hB, hL] at hU
  have hUU : U.ncard ≤ t * Nat.card K ^ (d - 1) *
      (Nat.card K ^ (d + 1)) ^ (t - 1) := by
    simpa [U] using hU
  have htotal : Nat.card (Fin t → L) = (Nat.card K ^ (d + 1)) ^ t := by
    rw [Nat.card_fun, hI, hL]
  have hsafe : Nat.card (SafeOutside p t) = Nat.card (Fin t → L) - U.ncard := by
    change Nat.card (Set.Elem {f : Fin t → L | ∀ i, f i ∉ B}) = _
    rw [Nat.card_coe_set_eq]
    have hcompl : (Uᶜ : Set (Fin t → L)) =
        {f | ∀ i, f i ∉ B} := by
      ext f
      simp [U]
    rw [← hcompl, Set.ncard_compl U]
  have hbadhalf : 2 * U.ncard ≤ Nat.card (Fin t → L) := by
    calc
      2 * U.ncard ≤ 2 * (t * Nat.card K ^ (d - 1) *
          (Nat.card K ^ (d + 1)) ^ (t - 1)) := Nat.mul_le_mul_left 2 hUU
      _ ≤ (Nat.card K ^ (d + 1)) ^ t := by
        by_cases ht : t = 0
        · subst t
          simp
        · have htpos : 0 < t := Nat.pos_of_ne_zero ht
          have hexp : d + 1 = 2 + (d - 1) := by omega
          have hsplit : Nat.card K ^ (d + 1) =
              Nat.card K ^ 2 * Nat.card K ^ (d - 1) := by rw [hexp, pow_add]
          let P := (Nat.card K ^ (d + 1)) ^ (t - 1)
          have htpow : (Nat.card K ^ (d + 1)) ^ t =
              Nat.card K ^ (d + 1) * P := by
            calc
              (Nat.card K ^ (d + 1)) ^ t =
                  (Nat.card K ^ (d + 1)) ^ ((t - 1) + 1) :=
                congrArg ((Nat.card K ^ (d + 1)) ^ ·) (by omega)
              _ = P * Nat.card K ^ (d + 1) := by rw [pow_succ]
              _ = Nat.card K ^ (d + 1) * P := Nat.mul_comm _ _
          calc
            2 * (t * Nat.card K ^ (d - 1) * P) =
                (2 * t) * Nat.card K ^ (d - 1) * P := by ring
            _ ≤ Nat.card K ^ 2 * Nat.card K ^ (d - 1) * P := by
              gcongr
            _ = Nat.card K ^ (d + 1) * P := by rw [hsplit]
            _ = (Nat.card K ^ (d + 1)) ^ t := htpow.symm
      _ = Nat.card (Fin t → L) := htotal.symm
  have hUle : U.ncard ≤ Nat.card (Fin t → L) := by omega
  have hadd : U.ncard + Nat.card (SafeOutside p t) = Nat.card (Fin t → L) := by
    rw [hsafe, Nat.add_comm, Nat.sub_add_cancel hUle]
  have hlabel : Nat.card (((Fin d → K) × K)) ^ t = Nat.card (Fin t → L) := by
    rw [Nat.card_fun, hI]
  rw [hlabel]
  omega

end Erdos538.IsotropicKernel
