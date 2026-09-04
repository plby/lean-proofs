import ErdosProblems.Erdos941.KernelIteration
import ErdosProblems.Erdos941.WordPlaneLift
import ErdosProblems.Erdos941.RootHensel

/-! # Elementary lifting of a modular target height -/

namespace Erdos941

abbrev primeSquareReduce (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)

theorem primeSquare_reduce_zero_iff {p : ℕ} (x : ZMod (p ^ 2)) :
    primeSquareReduce p x = 0 ↔ ∃ y : ZMod (p ^ 2), x = (p : ZMod (p ^ 2)) * y := by
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
    rw [map_intCast] at hx
    obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hx
    refine ⟨b, ?_⟩
    rw [hb]
    push_cast
    rfl
  · rintro ⟨y, rfl⟩
    simp only [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem primeSquare_square_zero (p : ℕ) : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

theorem primeSquare_mul_zero {p : ℕ} {x : ZMod (p ^ 2)}
    (hx : primeSquareReduce p x = 0) : (p : ZMod (p ^ 2)) * x = 0 := by
  obtain ⟨y, rfl⟩ := (primeSquare_reduce_zero_iff x).mp hx
  rw [← mul_assoc, ← pow_two, primeSquare_square_zero, zero_mul]

theorem exists_primeSquare_kill {p : ℕ} [hp : Fact p.Prime] (x y : ZMod (p ^ 2))
    (hx : primeSquareReduce p x = 0) (hy : primeSquareReduce p y ≠ 0) :
    ∃ j : ℕ, x + (j : ZMod (p ^ 2)) * p * y = 0 := by
  let : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩
  obtain ⟨d, hd⟩ := (primeSquare_reduce_zero_iff x).mp hx
  have hu : IsUnit y := isUnit_of_prime_reduction (by decide : 0 < 2) y hy
  let z : ZMod (p ^ 2) := -d * ↑hu.unit⁻¹
  obtain ⟨j, hj⟩ := ZMod.natCast_zmod_surjective z
  refine ⟨j, ?_⟩
  have hinv : y * (↑hu.unit⁻¹ : ZMod (p ^ 2)) = 1 := by
    have h : (hu.unit : ZMod (p ^ 2)) * (↑hu.unit⁻¹ : ZMod (p ^ 2)) = 1 := by simp
    simpa only [hu.unit_spec] using h
  rw [hd, hj]
  calc
    (p : ZMod (p ^ 2)) * d + z * p * y = p * d - p * d * (y * ↑hu.unit⁻¹) := by
      dsimp [z]
      ring
    _ = 0 := by rw [hinv]; ring

theorem heightLinear_kernel {R : Type*} [CommRing R] (a b c p u j : R) (v : R × R × R) :
    heightLinear a b c (kernelLinear p (j * u) v) =
      heightLinear a b c v + j * p * (u * ((a - b) * v.2.2 + c * (v.2.1 - v.1))) := by
  dsimp [heightLinear, kernelLinear]
  ring

theorem exists_kernel_word_kill_height {p : ℕ} [Fact p.Prime]
    (t u a b c : ZMod (p ^ 2)) (w : List Axis)
    (hw : linearWord t w = kernelLinear (p : ZMod (p ^ 2)) u)
    (v : ZMod (p ^ 2) × ZMod (p ^ 2) × ZMod (p ^ 2))
    (hv : primeSquareReduce p (heightLinear a b c v) = 0)
    (hd : primeSquareReduce p (u * ((a - b) * v.2.2 + c * (v.2.1 - v.1))) ≠ 0) :
    ∃ j : ℕ, heightLinear a b c (linearWord t (List.replicate j w).flatten v) = 0 := by
  obtain ⟨j, hj⟩ := exists_primeSquare_kill (heightLinear a b c v)
    (u * ((a - b) * v.2.2 + c * (v.2.1 - v.1))) hv hd
  refine ⟨j, ?_⟩
  rw [linearWord_replicate_kernel (primeSquare_square_zero p) w hw, heightLinear_kernel]
  exact hj

end Erdos941
