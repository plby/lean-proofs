import ErdosProblems.Erdos321.ModularFiber

namespace Erdos321

/-- Union of scaled cofactor fibres indexed by `P`. -/
def fiberUnion (P : Finset ℕ) (B : ℕ → Finset ℕ) : Finset ℕ :=
  P.biUnion fun p => scaleFinset p (B p)

/-- No prime indexing one fibre divides a denominator in any other fibre. -/
def CrossPrivate (P : Finset ℕ) (B : ℕ → Finset ℕ) : Prop :=
  ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ∀ b ∈ B q, ¬p ∣ q * b

/-- Pairwise cross-private, modularly separated prime fibres compose into one
valid denominator set. -/
theorem valid_fiberUnion
    {P : Finset ℕ} {B : ℕ → Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hmod : ∀ p ∈ P, ModularlySeparated p (B p))
    (hcross : CrossPrivate P B) : Valid (fiberUnion P B) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simp [fiberUnion, Valid]
  | @insert p P hpNotMem ih =>
      have hpPrime : p.Prime := hprime p (Finset.mem_insert_self p P)
      have hOldPrime : ∀ q ∈ P, q.Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hOldMod : ∀ q ∈ P, ModularlySeparated q (B q) := by
        intro q hq
        exact hmod q (Finset.mem_insert_of_mem hq)
      have hOldCross : CrossPrivate P B := by
        intro q hq r hr hqr b hb
        exact hcross q (Finset.mem_insert_of_mem hq)
          r (Finset.mem_insert_of_mem hr) hqr b hb
      have hOldValid : Valid (fiberUnion P B) :=
        ih hOldPrime hOldMod hOldCross
      have hpPrivateOld : ∀ a ∈ fiberUnion P B, ¬p ∣ a := by
        intro a ha
        rcases Finset.mem_biUnion.mp ha with ⟨q, hqP, haFiber⟩
        rcases Finset.mem_image.mp haFiber with ⟨b, hb, hab⟩
        have hpq : p ≠ q := fun h => hpNotMem (h ▸ hqP)
        rw [← hab]
        exact hcross p (Finset.mem_insert_self p P)
          q (Finset.mem_insert_of_mem hqP) hpq b hb
      have hNewValid : Valid (fiberUnion P B ∪ scaleFinset p (B p)) :=
        valid_union_scaleFinset_of_modularlySeparated hpPrime hOldValid
          hpPrivateOld (hmod p (Finset.mem_insert_self p P))
      simpa [fiberUnion, Finset.biUnion_insert, Finset.union_comm] using hNewValid

private theorem nat_mul_left_injective {p : ℕ} (hp0 : p ≠ 0) :
    Function.Injective (fun b : ℕ => p * b) := by
  intro a b h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) h

private theorem scaleFinset_card {p : ℕ} (hp0 : p ≠ 0) (B : Finset ℕ) :
    (scaleFinset p B).card = B.card := by
  rw [scaleFinset, Finset.card_image_iff]
  exact (nat_mul_left_injective hp0).injOn

/-- Under the same cross-private condition, different fibres are disjoint and
the union cardinality is the sum of the cofactor cardinalities. -/
theorem card_fiberUnion
    {P : Finset ℕ} {B : ℕ → Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hcross : CrossPrivate P B) :
    (fiberUnion P B).card = ∑ p ∈ P, (B p).card := by
  classical
  have hPairwise : (↑P : Set ℕ).PairwiseDisjoint
      (fun p => scaleFinset p (B p)) := by
    intro p hpP q hqP hpq
    change Disjoint (scaleFinset p (B p)) (scaleFinset q (B q))
    rw [Finset.disjoint_left]
    intro a haP haQ
    rcases Finset.mem_image.mp haP with ⟨b, hb, hab⟩
    rcases Finset.mem_image.mp haQ with ⟨c, hc, hac⟩
    apply hcross p hpP q hqP hpq c hc
    rw [hac, ← hab]
    exact dvd_mul_right p b
  rw [fiberUnion, Finset.card_biUnion hPairwise]
  apply Finset.sum_congr rfl
  intro p hpP
  exact scaleFinset_card (hprime p hpP).ne_zero (B p)

/-- If every fibre prime exceeds a common cofactor bound `T`, cross-privacy
is automatic. -/
theorem crossPrivate_of_large_primes
    {P : Finset ℕ} {B : ℕ → Finset ℕ} {T : ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, T < p)
    (hBsub : ∀ p ∈ P, B p ⊆ Finset.Icc 1 T) : CrossPrivate P B := by
  intro p hpP q hqP hpq b hb
  have hpPrime := hprime p hpP
  have hqPrime := hprime q hqP
  have hbIcc := Finset.mem_Icc.mp (hBsub q hqP hb)
  intro hpdvd
  rcases hpPrime.dvd_mul.mp hpdvd with hpqDvd | hpbDvd
  · exact hpq ((Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp hpqDvd)
  · have hpleb : p ≤ b := Nat.le_of_dvd hbIcc.1 hpbDvd
    exact (not_le_of_gt (hlarge p hpP)) (hpleb.trans hbIcc.2)

/-- Exact finite lower-bound schema for the multi-fibre construction. -/
theorem multiFiber_card_le_extremalSize
    {N T : ℕ} {P : Finset ℕ} {B : ℕ → Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hlarge : ∀ p ∈ P, T < p)
    (hBsub : ∀ p ∈ P, B p ⊆ Finset.Icc 1 T)
    (hmod : ∀ p ∈ P, ModularlySeparated p (B p))
    (hprod : ∀ p ∈ P, ∀ b ∈ B p, p * b ≤ N) :
    (∑ p ∈ P, (B p).card) ≤ extremalSize N := by
  have hcross := crossPrivate_of_large_primes hprime hlarge hBsub
  have hValid : Valid (fiberUnion P B) := valid_fiberUnion hprime hmod hcross
  have hSubset : fiberUnion P B ⊆ Finset.Icc 1 N := by
    intro n hn
    rcases Finset.mem_biUnion.mp hn with ⟨p, hpP, hnFiber⟩
    rcases Finset.mem_image.mp hnFiber with ⟨b, hb, rfl⟩
    have hpPos := (hprime p hpP).pos
    have hbPos := (Finset.mem_Icc.mp (hBsub p hpP hb)).1
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hpPos hbPos, hprod p hpP b hb⟩
  rw [← card_fiberUnion hprime hcross]
  exact card_le_extremalSize ⟨hSubset, hValid⟩

end Erdos321
