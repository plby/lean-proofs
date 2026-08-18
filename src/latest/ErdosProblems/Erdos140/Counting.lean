import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Elementary counting and cyclic-embedding lemmas for Erdős Problem 140

This file contains only the finite combinatorial bookkeeping used when passing
between an interval of natural numbers and the odd cyclic group `ZMod (2 * N + 1)`.
-/

open Finset Function

namespace Erdos140

section ThreeAPCount

variable {α : Type*} [AddCommMonoid α] [DecidableEq α]

/-- The number of ordered triples `(a,b,c) ∈ A³` satisfying `a + c = b + b`. -/
def threeAPCount (A : Finset α) : ℕ :=
  #(((A ×ˢ A) ×ˢ A).filter fun x ↦ x.1.1 + x.2 = x.1.2 + x.1.2)

@[simp]
lemma mem_threeAPCountFinset {A : Finset α} {a b c : α} :
    ((a, b), c) ∈ (((A ×ˢ A) ×ˢ A).filter fun x ↦ x.1.1 + x.2 = x.1.2 + x.1.2) ↔
      a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a + c = b + b := by
  simp [and_assoc]

variable [IsCancelAdd α]

/-- A three-term-progression-free finite set has exactly its diagonal ordered
solutions to `a + c = b + b`. -/
theorem threeAPCount_eq_card {A : Finset α} (hA : ThreeAPFree (A : Set α)) :
    threeAPCount A = #A := by
  classical
  let D : Finset ((α × α) × α) := A.image fun a ↦ ((a, a), a)
  have hfilter :
      (((A ×ˢ A) ×ˢ A).filter fun x ↦ x.1.1 + x.2 = x.1.2 + x.1.2) = D := by
    ext x
    rcases x with ⟨⟨a, b⟩, c⟩
    simp only [mem_filter, mem_product, D, mem_image]
    constructor
    · rintro ⟨⟨⟨ha, hb⟩, hc⟩, habc⟩
      have hab : a = b := hA ha hb hc habc
      have hbc : b = c := hA.eq_right ha hb hc habc
      exact ⟨b, hb, by simp [hab, hbc]⟩
    · rintro ⟨d, hd, hdiag⟩
      have hda : d = a := congrArg (fun x ↦ x.1.1) hdiag
      have hdb : d = b := congrArg (fun x ↦ x.1.2) hdiag
      have hdc : d = c := congrArg (fun x ↦ x.2) hdiag
      subst a
      subst b
      subst c
      simp [hd]
  change #(((A ×ˢ A) ×ˢ A).filter fun x ↦ x.1.1 + x.2 = x.1.2 + x.1.2) = #A
  rw [hfilter]
  change #(A.image fun a ↦ ((a, a), a)) = #A
  rw [card_image_of_injective]
  intro a b hab
  exact congrArg (fun x ↦ x.1.1) hab

end ThreeAPCount

section CyclicEmbedding

/-- The odd modulus used to embed `[1,N]` without wraparound of two-term sums. -/
abbrev intervalModulus (N : ℕ) : ℕ := 2 * N + 1

/-- The standard embedding of natural numbers into the odd cyclic group of order `2N+1`. -/
abbrev intervalEmbedding (N : ℕ) (a : ℕ) : ZMod (intervalModulus N) := a

/-- Casting to `ZMod (2N+1)` is injective on numbers at most `N`. -/
theorem intervalEmbedding_injOn (N : ℕ) :
    Set.InjOn (intervalEmbedding N) (Set.Iic N) := by
  intro a ha b hb hab
  change a ≤ N at ha
  change b ≤ N at hb
  have ha_lt : a < intervalModulus N := by
    change a < 2 * N + 1
    omega
  have hb_lt : b < intervalModulus N := by
    change b < 2 * N + 1
    omega
  have hmod :=
    (ZMod.natCast_eq_natCast_iff' a b (intervalModulus N)).mp hab
  rwa [Nat.mod_eq_of_lt ha_lt, Nat.mod_eq_of_lt hb_lt] at hmod

/-- Equality of two sums in `ZMod (2N+1)` reflects equality in `ℕ` when all
four summands are at most `N`. -/
theorem intervalEmbedding_add_eq_add_iff {N a b c d : ℕ}
    (ha : a ≤ N) (hb : b ≤ N) (hc : c ≤ N) (hd : d ≤ N) :
    intervalEmbedding N a + intervalEmbedding N c =
        intervalEmbedding N b + intervalEmbedding N d ↔
      a + c = b + d := by
  constructor
  · intro h
    have hcast : ((a + c : ℕ) : ZMod (intervalModulus N)) =
        ((b + d : ℕ) : ZMod (intervalModulus N)) := by
      simpa only [Nat.cast_add] using h
    have hac_lt : a + c < intervalModulus N := by
      change a + c < 2 * N + 1
      omega
    have hbd_lt : b + d < intervalModulus N := by
      change b + d < 2 * N + 1
      omega
    have hmod :=
      (ZMod.natCast_eq_natCast_iff' (a + c) (b + d) (intervalModulus N)).mp hcast
    rwa [Nat.mod_eq_of_lt hac_lt, Nat.mod_eq_of_lt hbd_lt] at hmod
  · intro h
    simpa only [Nat.cast_add] using
      congrArg (fun n : ℕ ↦ (n : ZMod (intervalModulus N))) h

/-- The finite-set image of `A ⊆ ℕ` in `ZMod (2N+1)`. -/
def intervalImage (N : ℕ) (A : Finset ℕ) : Finset (ZMod (intervalModulus N)) :=
  A.image (intervalEmbedding N)

@[simp]
theorem mem_intervalImage {N : ℕ} {A : Finset ℕ} {x : ZMod (intervalModulus N)} :
    x ∈ intervalImage N A ↔ ∃ a ∈ A, intervalEmbedding N a = x := by
  simp [intervalImage]

/-- Embedding a set contained in `[0,N]` preserves its cardinality. -/
theorem card_intervalImage {N : ℕ} {A : Finset ℕ}
    (hA : ∀ a ∈ A, a ≤ N) : #(intervalImage N A) = #A := by
  rw [intervalImage, card_image_iff]
  exact fun a ha b hb h ↦ intervalEmbedding_injOn N (hA a ha) (hA b hb) h

/-- Embedding a subset of `[0,N]` into `ZMod (2N+1)` preserves and reflects
the property of containing a non-trivial three-term arithmetic progression. -/
theorem threeAPFree_intervalImage_iff {N : ℕ} {A : Finset ℕ}
    (hA : ∀ a ∈ A, a ≤ N) :
    ThreeAPFree (intervalImage N A : Set (ZMod (intervalModulus N))) ↔
      ThreeAPFree (A : Set ℕ) := by
  constructor
  · intro hImage a ha b hb c hc habc
    have ha' : intervalEmbedding N a ∈ intervalImage N A := by
      exact mem_intervalImage.mpr ⟨a, ha, rfl⟩
    have hb' : intervalEmbedding N b ∈ intervalImage N A := by
      exact mem_intervalImage.mpr ⟨b, hb, rfl⟩
    have hc' : intervalEmbedding N c ∈ intervalImage N A := by
      exact mem_intervalImage.mpr ⟨c, hc, rfl⟩
    have heq : intervalEmbedding N a + intervalEmbedding N c =
        intervalEmbedding N b + intervalEmbedding N b :=
      (intervalEmbedding_add_eq_add_iff (hA a ha) (hA b hb) (hA c hc) (hA b hb)).2 habc
    exact intervalEmbedding_injOn N (hA a ha) (hA b hb) (hImage ha' hb' hc' heq)
  · intro hNat x hx y hy z hz hxyz
    obtain ⟨a, ha, rfl⟩ := mem_intervalImage.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_intervalImage.mp hy
    obtain ⟨c, hc, rfl⟩ := mem_intervalImage.mp hz
    have habc : a + c = b + b :=
      (intervalEmbedding_add_eq_add_iff (hA a ha) (hA b hb) (hA c hc) (hA b hb)).1 hxyz
    exact congrArg (intervalEmbedding N) (hNat ha hb hc habc)

/-- The no-wrap embedding preserves the number of all ordered three-term
progressions, not only the diagonal count in an AP-free set. -/
theorem threeAPCount_intervalImage {N : ℕ} {A : Finset ℕ}
    (hA : ∀ a ∈ A, a ≤ N) :
    threeAPCount (intervalImage N A) = threeAPCount A := by
  classical
  let f : ((ℕ × ℕ) × ℕ) → ((ZMod (intervalModulus N) × ZMod (intervalModulus N)) ×
      ZMod (intervalModulus N)) := fun x ↦
    ((intervalEmbedding N x.1.1, intervalEmbedding N x.1.2), intervalEmbedding N x.2)
  let T : Finset ((ℕ × ℕ) × ℕ) :=
    ((A ×ˢ A) ×ˢ A).filter fun x ↦ x.1.1 + x.2 = x.1.2 + x.1.2
  let U : Finset ((ZMod (intervalModulus N) × ZMod (intervalModulus N)) ×
      ZMod (intervalModulus N)) :=
    (((intervalImage N A ×ˢ intervalImage N A) ×ˢ intervalImage N A).filter fun x ↦
      x.1.1 + x.2 = x.1.2 + x.1.2)
  have hUT : U = T.image f := by
    ext x
    rcases x with ⟨⟨x, y⟩, z⟩
    constructor
    · intro hxyz
      have hxyz' :
          x ∈ intervalImage N A ∧ y ∈ intervalImage N A ∧ z ∈ intervalImage N A ∧
            x + z = y + y := by
        simpa [U, and_assoc] using hxyz
      rcases hxyz' with ⟨hx, hy, hz, hrel⟩
      obtain ⟨a, ha, rfl⟩ := mem_intervalImage.mp hx
      obtain ⟨b, hb, rfl⟩ := mem_intervalImage.mp hy
      obtain ⟨c, hc, rfl⟩ := mem_intervalImage.mp hz
      refine mem_image.mpr ⟨((a, b), c), ?_, rfl⟩
      have habc : a + c = b + b :=
        (intervalEmbedding_add_eq_add_iff (hA a ha) (hA b hb) (hA c hc) (hA b hb)).1 hrel
      simp [T, ha, hb, hc, habc]
    · intro hxyz
      obtain ⟨⟨⟨a, b⟩, c⟩, habc_mem, habc_eq⟩ := mem_image.mp hxyz
      have habc' : a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a + c = b + b := by
        simpa [T, and_assoc] using habc_mem
      rcases habc' with ⟨ha, hb, hc, habc⟩
      have hx : intervalEmbedding N a ∈ intervalImage N A :=
        mem_intervalImage.mpr ⟨a, ha, rfl⟩
      have hy : intervalEmbedding N b ∈ intervalImage N A :=
        mem_intervalImage.mpr ⟨b, hb, rfl⟩
      have hz : intervalEmbedding N c ∈ intervalImage N A :=
        mem_intervalImage.mpr ⟨c, hc, rfl⟩
      have hrel : intervalEmbedding N a + intervalEmbedding N c =
          intervalEmbedding N b + intervalEmbedding N b :=
        (intervalEmbedding_add_eq_add_iff (hA a ha) (hA b hb) (hA c hc) (hA b hb)).2 habc
      rw [← habc_eq]
      simp [U, f, hx, hy, hz, hrel]
  have hf : Set.InjOn f T := by
    rintro ⟨⟨a, b⟩, c⟩ habc ⟨⟨a', b'⟩, c'⟩ habc' heq
    have habc_mem : a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a + c = b + b := by
      simpa [T, and_assoc] using habc
    have habc_mem' : a' ∈ A ∧ b' ∈ A ∧ c' ∈ A ∧ a' + c' = b' + b' := by
      simpa [T, and_assoc] using habc'
    rcases habc_mem with ⟨ha, hb, hc, -⟩
    rcases habc_mem' with ⟨ha', hb', hc', -⟩
    have haa : a = a' := intervalEmbedding_injOn N (hA a ha) (hA a' ha') <|
      congrArg (fun x ↦ x.1.1) heq
    have hbb : b = b' := intervalEmbedding_injOn N (hA b hb) (hA b' hb') <|
      congrArg (fun x ↦ x.1.2) heq
    have hcc : c = c' := intervalEmbedding_injOn N (hA c hc) (hA c' hc') <|
      congrArg (fun x ↦ x.2) heq
    simp [haa, hbb, hcc]
  change #U = #T
  rw [hUT, card_image_of_injOn hf]

/-- For an AP-free set in `[0,N]`, the cyclic image has exactly the diagonal
ordered three-term progressions. -/
theorem threeAPCount_intervalImage_eq_card {N : ℕ} {A : Finset ℕ}
    (hA : ∀ a ∈ A, a ≤ N) (hfree : ThreeAPFree (A : Set ℕ)) :
    threeAPCount (intervalImage N A) = #A := by
  rw [threeAPCount_intervalImage hA, threeAPCount_eq_card hfree]

/-- Two is coprime to the odd modulus `2N+1`. -/
theorem two_coprime_intervalModulus (N : ℕ) : Nat.Coprime 2 (intervalModulus N) := by
  rw [Nat.coprime_two_left]
  exact ⟨N, by
    change 2 * N + 1 = 2 * N + 1
    rfl⟩

/-- Doubling is injective in the odd cyclic group `ZMod (2N+1)`. -/
theorem interval_doubling_injective (N : ℕ) :
    Function.Injective (fun x : ZMod (intervalModulus N) ↦ x + x) := by
  intro x y h
  have hu : IsUnit (2 : ZMod (intervalModulus N)) :=
    (ZMod.isUnit_iff_coprime 2 (intervalModulus N)).2 (two_coprime_intervalModulus N)
  apply hu.mul_left_cancel
  simpa [two_mul] using h

/-- Doubling preserves the cardinality of every finite subset of the odd cyclic group. -/
theorem card_image_doubling (N : ℕ) (A : Finset (ZMod (intervalModulus N))) :
    #(A.image fun x ↦ x + x) = #A := by
  exact card_image_of_injective _ (interval_doubling_injective N)

end CyclicEmbedding

end Erdos140
