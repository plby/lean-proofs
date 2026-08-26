import ErdosProblems.Erdos421.VectorCharacters

/-! # Unit frequency changes in finite character sums -/

namespace Erdos421

variable {q k : ℕ} [NeZero q]

theorem norm_vectorCharacter (a v : Fin k → ZMod q) : ‖vectorCharacter a v‖ = 1 := by
  simp only [vectorCharacter, norm_prod, ZMod.stdAddChar_apply, Circle.norm_coe,
    Finset.prod_const_one]

theorem vectorCharacter_scale (a v : Fin k → ZMod q) (c : ZMod q) :
    vectorCharacter a (fun j ↦ c * v j) = vectorCharacter (fun j ↦ c * a j) v := by
  unfold vectorCharacter
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  ring

def scaleFrequencyEquiv (c : (ZMod q)ˣ) : (Fin k → ZMod q) ≃ (Fin k → ZMod q) where
  toFun a j := (c : ZMod q) * a j
  invFun a j := (↑c⁻¹ : ZMod q) * a j
  left_inv a := by funext j; simp only [← mul_assoc, Units.inv_mul, one_mul]
  right_inv a := by funext j; simp only [← mul_assoc, Units.mul_inv, one_mul]

theorem vectorCharacterSum_scale {X : Type*} (S : Finset X) (f : X → Fin k → ZMod q)
    (a : Fin k → ZMod q) (c : ZMod q) :
    vectorCharacterSum S (fun x j ↦ c * f x j) a =
      vectorCharacterSum S f (fun j ↦ c * a j) := by
  simp only [vectorCharacterSum, vectorCharacter_scale]

theorem sum_norm_vectorCharacterSum_scale {X : Type*} (S : Finset X)
    (f : X → Fin k → ZMod q) (c : (ZMod q)ˣ) (m : ℕ) :
    (∑ a : Fin k → ZMod q, ‖vectorCharacterSum S (fun x j ↦ (c : ZMod q) * f x j) a‖ ^ m) =
      ∑ a : Fin k → ZMod q, ‖vectorCharacterSum S f a‖ ^ m := by
  simp only [vectorCharacterSum_scale]
  exact Equiv.sum_comp (scaleFrequencyEquiv c) (fun a ↦ ‖vectorCharacterSum S f a‖ ^ m)

end Erdos421
