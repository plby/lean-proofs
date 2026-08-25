import ErdosProblems.Erdos1141.QuadraticRealCharacter
import Mathlib.Algebra.Group.Prod

/-!
# Dirichlet-character structures for the reduced product characters
-/

namespace Pollack17

open scoped BigOperators

noncomputable def transportMulChar {R S T : Type*} [CommMonoid R] [CommMonoid S]
    [CommMonoidWithZero T] (χ : MulChar S T) (e : R ≃* S) : MulChar R T where
  toFun x := χ (e x)
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_nonunit' x hx := by
    apply χ.map_nonunit
    intro hu
    have h := hu.map e.symm
    exact hx (by simpa only [MulEquiv.symm_apply_apply] using h)

noncomputable def productMulChar {R S T : Type*} [CommMonoid R] [CommMonoid S]
    [CommMonoidWithZero T] (χ : MulChar R T) (ψ : MulChar S T) : MulChar (R × S) T where
  toFun x := χ x.1 * ψ x.2
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one, mul_one]
  map_mul' x y := by simp only [Prod.fst_mul, Prod.snd_mul, map_mul]; ac_rfl
  map_nonunit' x hx := by
    by_cases h₁ : IsUnit x.1
    · have h₂ : ¬IsUnit x.2 := fun h₂ => hx (Prod.isUnit_iff.mpr ⟨h₁, h₂⟩)
      rw [ψ.map_nonunit h₂, mul_zero]
    · rw [χ.map_nonunit h₁, zero_mul]

noncomputable def Burgess.productDirichletChar (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    DirichletCharacter ℝ (Burgess.primeModulus s) where
  toFun := Burgess.productChar s hs
  map_one' := by
    classical
    unfold Burgess.productChar
    apply Finset.prod_eq_one
    intro p _
    have : Fact (Nat.Prime (p : ℕ)) := ⟨hs p p.property⟩
    simp only [Burgess.localChar, Burgess.qchar, map_one, Pi.one_apply, Int.cast_one]
  map_mul' := Burgess.productChar_mul s hs
  map_nonunit' x hx := by
    classical
    have hni : ¬IsUnit (Burgess.primeCRT s hs x) := by
      intro hu
      have h := hu.map (Burgess.primeCRT s hs).symm
      exact hx (by simpa only [RingEquiv.symm_apply_apply] using h)
    have hex : ∃ p : s, ¬IsUnit (Burgess.primeCRT s hs x p) := by
      simpa only [Pi.isUnit_iff, not_forall] using hni
    obtain ⟨p, hp⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    have : Fact (Nat.Prime (p : ℕ)) := ⟨hs p p.property⟩
    simp only [Burgess.localChar, Burgess.qchar, (quadraticChar (ZMod (p : ℕ))).map_nonunit hp,
      Int.cast_zero]

theorem Burgess.productDirichletChar_apply (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime)
    (x : ZMod (Burgess.primeModulus s)) :
    Burgess.productDirichletChar s hs x = Burgess.productChar s hs x := rfl

noncomputable def tensorDirichletChar {a b : ℕ} (hab : a.Coprime b)
    (χ : DirichletCharacter ℝ a) (ψ : DirichletCharacter ℝ b) :
    DirichletCharacter ℝ (a * b) :=
  transportMulChar (productMulChar χ ψ) (ZMod.chineseRemainder hab).toMulEquiv

theorem tensorDirichletChar_natCast {a b : ℕ} (hab : a.Coprime b)
    (χ : DirichletCharacter ℝ a) (ψ : DirichletCharacter ℝ b) (n : ℕ) :
    tensorDirichletChar hab χ ψ (n : ZMod (a * b)) = χ (n : ZMod a) * ψ (n : ZMod b) := by
  simp [tensorDirichletChar, transportMulChar, productMulChar]

end Pollack17
