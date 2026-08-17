import Mathlib

/-!
# Uniform relational covers

This file isolates the finite double-counting argument used in the
Lagarias--Odlyzko--Shearer modular reduction for Erdős problem 438.  We use
relations rather than `SimpleGraph`, since the square-sum graph genuinely has
loops.
-/

open scoped BigOperators

namespace Erdos438

/-- The looped square-sum relation on `ZMod m`. -/
def SquareSumRel (m : ℕ) (x y : ZMod m) : Prop :=
  ∃ z : ZMod m, z ^ 2 = x + y

theorem squareSumRel_comm {m : ℕ} {x y : ZMod m} :
    SquareSumRel m x y ↔ SquareSumRel m y x := by
  simp only [SquareSumRel, add_comm]

/-- A homomorphism of (possibly looped) binary relations. -/
def RelHom {X Y : Type*} (R : X → X → Prop) (S : Y → Y → Prop)
    (f : X → Y) : Prop :=
  ∀ {x y}, R x y → S (f x) (f y)

/-- An independent finite set for a possibly looped relation. -/
def RelIndependent {X : Type*} (R : X → X → Prop) (A : Finset X) : Prop :=
  ∀ {x}, x ∈ A → ∀ {y}, y ∈ A → ¬ R x y

/-- The categorical product of two binary relations. -/
def RelProd {X Y : Type*} (R : X → X → Prop) (S : Y → Y → Prop) :
    X × Y → X × Y → Prop :=
  fun x y ↦ R x.1 y.1 ∧ S x.2 y.2

/-- The complete irreflexive relation on three vertices. -/
def K3Rel (i j : Fin 3) : Prop := i ≠ j

section FiniteCover

variable {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
  [DecidableEq U] [DecidableEq V] [DecidableEq W]

/-- The number of elements of the source sent to `v`. -/
def fiberCard (f : W → V) (v : V) : ℕ :=
  (Finset.univ.filter fun w : W ↦ f w = v).card

/-- Pull a subset of `U × V` back along `id × f`. -/
def coverPullback (f : W → V) (A : Finset (U × V)) : Finset (U × W) :=
  Finset.univ.filter fun p ↦ (p.1, f p.2) ∈ A

/-- Total preimage multiplicity of a vertex under a multiset of maps. -/
def coverMultiplicity (F : Multiset (W → V)) (v : V) : ℕ :=
  (F.map fun f ↦ fiberCard f v).sum

/-- A multiset of maps is `D`-uniform when every target vertex occurs exactly
`D` times, counting all preimages and all repetitions of maps. -/
def UniformCover (F : Multiset (W → V)) (D : ℕ) : Prop :=
  ∀ v, coverMultiplicity F v = D

/-- A multiset relational cover consists only of relation homomorphisms. -/
def IsRelCover (R : W → W → Prop) (S : V → V → Prop)
    (F : Multiset (W → V)) : Prop :=
  ∀ f ∈ F, RelHom R S f

theorem coverPullback_independent (RU : U → U → Prop) (RV : V → V → Prop)
    (RW : W → W → Prop) (f : W → V) (A : Finset (U × V))
    (hf : RelHom RW RV f) (hA : RelIndependent (RelProd RU RV) A) :
    RelIndependent (RelProd RU RW) (coverPullback f A) := by
  intro x hx y hy hxy
  rw [coverPullback, Finset.mem_filter] at hx hy
  exact hA hx.2 hy.2 ⟨hxy.1, hf hxy.2⟩

theorem card_coverPullback_eq_sum_fibers (f : W → V) (A : Finset (U × V)) :
    (coverPullback f A).card =
      ∑ v : V, fiberCard f v *
        (Finset.univ.filter fun u : U ↦ (u, v) ∈ A).card := by
  classical
  calc
    (coverPullback f A).card =
        ∑ u : U, ∑ w : W, if (u, f w) ∈ A then 1 else 0 := by
      rw [coverPullback, Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Fintype.sum_prod_type]
    _ = ∑ u : U, ∑ v : V,
        ∑ w ∈ (Finset.univ : Finset W) with f w = v,
          if (u, f w) ∈ A then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      exact (Finset.sum_fiberwise Finset.univ f
        (fun w ↦ if (u, f w) ∈ A then 1 else 0)).symm
    _ = ∑ v : V, fiberCard f v *
        (Finset.univ.filter fun u : U ↦ (u, v) ∈ A).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      calc
        (∑ u : U, ∑ w ∈ (Finset.univ : Finset W) with f w = v,
            if (u, f w) ∈ A then 1 else 0) =
            ∑ u : U, if (u, v) ∈ A then fiberCard f v else 0 := by
          apply Finset.sum_congr rfl
          intro u _
          by_cases hu : (u, v) ∈ A
          · rw [if_pos hu, fiberCard, Finset.card_eq_sum_ones]
            apply Finset.sum_congr rfl
            intro w hw
            simp only [Finset.mem_filter] at hw
            simp [hw.2, hu]
          · rw [if_neg hu]
            apply Finset.sum_eq_zero
            intro w hw
            simp only [Finset.mem_filter] at hw
            simp [hw.2, hu]
        _ = ∑ u ∈ (Finset.univ : Finset U) with (u, v) ∈ A,
            fiberCard f v := (Finset.sum_filter _ _).symm
        _ = fiberCard f v *
            (Finset.univ.filter fun u : U ↦ (u, v) ∈ A).card := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact Nat.mul_comm _ _

/-- Exact double counting for a multiset cover. -/
theorem sum_card_coverPullback (F : Multiset (W → V)) (A : Finset (U × V)) :
    (F.map fun f ↦ (coverPullback f A).card).sum =
      ∑ v : V, coverMultiplicity F v *
        (Finset.univ.filter fun u : U ↦ (u, v) ∈ A).card := by
  classical
  induction F using Multiset.induction_on with
  | empty => simp [coverMultiplicity]
  | @cons f F ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, ih, card_coverPullback_eq_sum_fibers]
      simp only [coverMultiplicity, Multiset.map_cons, Multiset.sum_cons]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v _
      exact (Nat.add_mul _ _ _).symm

/-- A `D`-uniform cover counts every subset exactly `D` times. -/
theorem sum_card_coverPullback_of_uniform {F : Multiset (W → V)} {D : ℕ}
    (hF : UniformCover F D) (A : Finset (U × V)) :
    (F.map fun f ↦ (coverPullback f A).card).sum = D * A.card := by
  rw [sum_card_coverPullback]
  unfold UniformCover at hF
  simp_rw [hF]
  rw [← Finset.mul_sum]
  congr 1
  calc
    (∑ v : V, (Finset.univ.filter fun u : U ↦ (u, v) ∈ A).card) =
        ∑ v : V, ∑ u : U, if (u, v) ∈ A then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p : U × V, if p ∈ A then 1 else 0 := by
      rw [Finset.sum_comm, Fintype.sum_prod_type]
    _ = A.card := by
      simpa using Finset.sum_boole (fun p : U × V ↦ p ∈ A) Finset.univ

/-- The total mass identity forced by a uniform cover. -/
theorem card_mul_of_uniform {F : Multiset (W → V)} {D : ℕ}
    (hF : UniformCover F D) :
    F.card * Fintype.card W = D * Fintype.card V := by
  classical
  have h := sum_card_coverPullback_of_uniform (U := Unit) (V := V) (W := W)
    hF (Finset.univ : Finset (Unit × V))
  simpa [coverPullback, mul_comm] using h

/-- The `K₃` specialization of the uniform-cover mass identity. -/
theorem three_mul_card_of_uniform {V : Type*} [Fintype V] [DecidableEq V]
    {F : Multiset (Fin 3 → V)} {D : ℕ} (hF : UniformCover F D) :
    3 * F.card = D * Fintype.card V := by
  simpa [mul_comm] using card_mul_of_uniform hF

/-- General fractional-cover transfer.  If every pullback along the cover has
at most `B` elements, then `D * |A| ≤ |F| * B`. -/
theorem uniform_cover_transfer {F : Multiset (W → V)} {D B : ℕ}
    (hF : UniformCover F D) (A : Finset (U × V))
    (hB : ∀ f ∈ F, (coverPullback f A).card ≤ B) :
    D * A.card ≤ F.card * B := by
  rw [← sum_card_coverPullback_of_uniform hF A]
  clear hF
  revert hB
  induction F using Multiset.induction_on with
  | empty => simp
  | @cons f F ih =>
      intro hB
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.succ_mul]
      rw [Nat.add_comm (F.card * B) B]
      exact Nat.add_le_add (hB f (by simp))
        (ih (fun g hg ↦ hB g (by simp [hg])))

/-- Relation-aware form of `uniform_cover_transfer`: homomorphism pullbacks
are independent, so any uniform bound for independent pullbacks transfers. -/
theorem uniform_relCover_transfer
    (RU : U → U → Prop) (RV : V → V → Prop) (RW : W → W → Prop)
    {F : Multiset (W → V)} {D B : ℕ}
    (hUniform : UniformCover F D) (hCover : IsRelCover RW RV F)
    (hBound : ∀ B' : Finset (U × W), RelIndependent (RelProd RU RW) B' → B'.card ≤ B)
    (A : Finset (U × V)) (hA : RelIndependent (RelProd RU RV) A) :
    D * A.card ≤ F.card * B := by
  apply uniform_cover_transfer hUniform A
  intro f hf
  exact hBound _ (coverPullback_independent RU RV RW f A (hCover f hf) hA)

/-- Specialized LOS transfer through a positive uniform `K₃`-cover.  The
cover degree cancels, leaving the particularly convenient denominator-free
inequality `3 * |A| ≤ |V| * B`. -/
theorem uniform_k3RelCover_transfer
    (RU : U → U → Prop) (RV : V → V → Prop)
    {F : Multiset (Fin 3 → V)} {D B : ℕ} (hD : 0 < D)
    (hUniform : UniformCover F D) (hCover : IsRelCover K3Rel RV F)
    (hBound : ∀ B' : Finset (U × Fin 3),
      RelIndependent (RelProd RU K3Rel) B' → B'.card ≤ B)
    (A : Finset (U × V)) (hA : RelIndependent (RelProd RU RV) A) :
    3 * A.card ≤ Fintype.card V * B := by
  have hTransfer : D * A.card ≤ F.card * B :=
    uniform_relCover_transfer RU RV K3Rel hUniform hCover hBound A hA
  have hMass : 3 * F.card = D * Fintype.card V :=
    three_mul_card_of_uniform hUniform
  apply Nat.le_of_mul_le_mul_left (c := D) _ hD
  calc
    D * (3 * A.card) = 3 * (D * A.card) := by ac_rfl
    _ ≤ 3 * (F.card * B) := Nat.mul_le_mul_left 3 hTransfer
    _ = (3 * F.card) * B := by ac_rfl
    _ = (D * Fintype.card V) * B := by rw [hMass]
    _ = D * (Fintype.card V * B) := by ac_rfl

end FiniteCover

section ChineseRemainder

/-- Under the Chinese remainder equivalence, the square-sum relation is the
categorical product of the corresponding relations. -/
theorem squareSumRel_chineseRemainder {m n : ℕ} (h : m.Coprime n) (x y : ZMod (m * n)) :
    SquareSumRel (m * n) x y ↔
      RelProd (SquareSumRel m) (SquareSumRel n)
        (ZMod.chineseRemainder h x) (ZMod.chineseRemainder h y) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨⟨(ZMod.chineseRemainder h z).1, ?_⟩,
      ⟨(ZMod.chineseRemainder h z).2, ?_⟩⟩
    · simpa using congrArg (fun w ↦ (ZMod.chineseRemainder h w).1) hz
    · simpa using congrArg (fun w ↦ (ZMod.chineseRemainder h w).2) hz
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    let z := (ZMod.chineseRemainder h).symm (a, b)
    refine ⟨z, (ZMod.chineseRemainder h).injective ?_⟩
    apply Prod.ext
    · simpa [z] using ha
    · simpa [z] using hb

end ChineseRemainder

end Erdos438
