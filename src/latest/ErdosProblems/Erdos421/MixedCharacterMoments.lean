import ErdosProblems.Erdos421.CharacterCorrelation

/-! # Exact mixed finite moments with a restricted tuple block -/

namespace Erdos421

variable {q k : ℕ} [NeZero q]

theorem vectorCharacterSum_product {X Y : Type*} (S : Finset X) (T : Finset Y)
    (f : X → Fin k → ZMod q) (g : Y → Fin k → ZMod q) (a : Fin k → ZMod q) :
    vectorCharacterSum (S ×ˢ T) (fun p ↦ f p.1 + g p.2) a =
      vectorCharacterSum S f a * vectorCharacterSum T g a := by
  simp only [vectorCharacterSum, Finset.sum_product, vectorCharacter_add, Finset.sum_mul_sum]

theorem vectorCharacterSum_finset_power {Y : Type*} (T : Finset Y)
    (g : Y → Fin k → ZMod q) (a : Fin k → ZMod q) (s : ℕ) :
    vectorCharacterSum T g a ^ s =
      vectorCharacterSum (Fintype.piFinset (fun _ : Fin s ↦ T))
        (fun x ↦ ∑ i : Fin s, g (x i)) a := by
  simp only [vectorCharacterSum, Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro x _
  exact (vectorCharacter_sum Finset.univ a (fun i ↦ g (x i))).symm

def mixedCongruenceCount {X Y : Type*} (S : Finset X) (T : Finset Y)
    (f : X → Fin k → ZMod q) (g : Y → Fin k → ZMod q) (s : ℕ) : ℕ :=
  let D := S ×ˢ Fintype.piFinset (fun _ : Fin s ↦ T)
  ((D ×ˢ D).filter (fun p ↦ f p.1.1 + (∑ i : Fin s, g (p.1.2 i)) =
    f p.2.1 + ∑ i : Fin s, g (p.2.2 i))).card

theorem mixedCharacterMoment_eq_count {X Y : Type*} (S : Finset X) (T : Finset Y)
    (f : X → Fin k → ZMod q) (g : Y → Fin k → ZMod q) (s : ℕ) :
    (∑ a : Fin k → ZMod q, ‖vectorCharacterSum S f a‖ ^ 2 *
      ‖vectorCharacterSum T g a‖ ^ (2 * s)) =
        (q : ℝ) ^ k * (mixedCongruenceCount S T f g s : ℝ) := by
  have h := sum_norm_vectorCharacterSum_sq
    (S ×ˢ Fintype.piFinset (fun _ : Fin s ↦ T))
    (fun p ↦ f p.1 + ∑ i : Fin s, g (p.2 i))
  have hprod (a : Fin k → ZMod q) := vectorCharacterSum_product S
    (Fintype.piFinset (fun _ : Fin s ↦ T)) f (fun x ↦ ∑ i : Fin s, g (x i)) a
  simpa only [hprod, ← vectorCharacterSum_finset_power,
    norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm s 2, mixedCongruenceCount] using h

end Erdos421
