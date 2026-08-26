import ErdosProblems.Erdos327.Defs

namespace Erdos327

theorem conflictOne_comm (a b : ℕ) :
    ConflictOne a b ↔ ConflictOne b a := by
  simp only [ConflictOne]
  rw [add_comm, mul_comm]

theorem conflictTwo_comm (a b : ℕ) :
    ConflictTwo a b ↔ ConflictTwo b a := by
  simp only [ConflictTwo]
  constructor <;> intro h
  · simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h
  · simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using h

/-- Two odd natural numbers cannot conflict in the first variant. -/
theorem not_conflictOne_of_odd
    {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    ¬ ConflictOne a b := by
  intro h
  have hsumEven : Even (a + b) := ha.add_odd hb
  have hprodEven : Even (a * b) :=
    hsumEven.trans_dvd h
  have hprodOdd : Odd (a * b) := ha.mul hb
  exact (Nat.not_even_iff_odd.mpr hprodOdd) hprodEven

/-- Any finite set of odd naturals is one-admissible. -/
theorem oneAdmissible_of_forall_odd
    {A : Finset ℕ} (hodd : ∀ a ∈ A, Odd a) :
    OneAdmissible A := by
  intro a ha b hb _hne
  exact not_conflictOne_of_odd (hodd a ha) (hodd b hb)

/-- Doubling both endpoints converts a first-variant conflict into a
second-variant conflict before doubling. -/
theorem conflictOne_double_iff_conflictTwo (b d : ℕ) :
    ConflictOne (2 * b) (2 * d) ↔ ConflictTwo b d := by
  change 2 * b + 2 * d ∣ (2 * b) * (2 * d) ↔
    b + d ∣ 2 * b * d
  have htwo : (2 : ℕ) ≠ 0 := by norm_num
  calc
    2 * b + 2 * d ∣ (2 * b) * (2 * d) ↔
        2 * (b + d) ∣ 2 * (2 * b * d) := by ring_nf
    _ ↔ b + d ∣ 2 * b * d := mul_dvd_mul_iff_left htwo

/-- For an odd endpoint, the odd mixed divisor may cancel the factor `2`
from the product. -/
theorem mixed_conflict_iff
    {a b : ℕ} (ha : Odd a) :
    ConflictOne a (2 * b) ↔ a + 2 * b ∣ a * b := by
  have hdivisorOdd : Odd (a + 2 * b) :=
    ha.add_even (even_two_mul b)
  have hcop : Nat.Coprime (a + 2 * b) 2 :=
    hdivisorOdd.coprime_two_right
  change a + 2 * b ∣ a * (2 * b) ↔ a + 2 * b ∣ a * b
  rw [show a * (2 * b) = 2 * (a * b) by ring]
  exact hcop.dvd_mul_left

/-- The injective doubling map used to embed the two-admissible source. -/
def doubleEmbedding : ℕ ↪ ℕ where
  toFun n := 2 * n
  inj' := by
    intro a b h
    change 2 * a = 2 * b at h
    omega

@[simp] theorem doubleEmbedding_apply (n : ℕ) :
    doubleEmbedding n = 2 * n := rfl

/-- Pointwise doubling of a finite source. -/
def doubleSet (B : Finset ℕ) : Finset ℕ :=
  B.map doubleEmbedding

@[simp] theorem mem_doubleSet {B : Finset ℕ} {n : ℕ} :
    n ∈ doubleSet B ↔ ∃ b ∈ B, 2 * b = n := by
  constructor
  · intro h
    rcases Finset.mem_map.mp h with ⟨b, hb, hbn⟩
    change 2 * b = n at hbn
    exact ⟨b, hb, hbn⟩
  · rintro ⟨b, hb, rfl⟩
    exact Finset.mem_map.mpr ⟨b, hb, rfl⟩

@[simp] theorem card_doubleSet (B : Finset ℕ) :
    (doubleSet B).card = B.card := by
  simp [doubleSet]

/-- A two-admissible source becomes one-admissible after doubling. -/
theorem oneAdmissible_doubleSet
    {B : Finset ℕ} (hB : TwoAdmissible B) :
    OneAdmissible (doubleSet B) := by
  intro a ha d hd had
  rcases mem_doubleSet.mp ha with ⟨b, hb, rfl⟩
  rcases mem_doubleSet.mp hd with ⟨c, hc, hdc⟩
  subst hdc
  have hbc : b ≠ c := by
    intro h
    apply had
    simp [h]
  exact fun hconflict =>
    hB b hb c hc hbc ((conflictOne_double_iff_conflictTwo b c).mp hconflict)

end Erdos327
