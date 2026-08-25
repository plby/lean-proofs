import Util.Bernays.QuadraticOrder
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Uniform lattice-point bounds and finiteness of units

Completing the square sends each norm ball injectively into an integral
square of side `O(√N)`. This also handles the extra units of discriminants
`-3` and `-4` without any exceptional-case assumption.
-/

namespace Bernays

def QuadraticNormBall (d b : ℤ) (N : ℕ) :=
  {z : QuadraticAlgebra ℤ d b // z.norm.natAbs ≤ N}

theorem quadraticNormBall_sq_bounds {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {N : ℕ} (z : QuadraticNormBall d b N) :
    (2 * z.1.re + b * z.1.im) ^ 2 ≤ 4 * (N : ℤ) ∧ z.1.im ^ 2 ≤ 4 * (N : ℤ) := by
  have hn : z.1.norm ≤ (N : ℤ) := Int.le_natAbs.trans (by exact_mod_cast z.2)
  have hform := four_mul_quadraticNorm d b z.1
  have hD₁ : 1 ≤ -(b ^ 2 + 4 * d) := by omega
  have hmul := mul_le_mul_of_nonneg_right hD₁ (sq_nonneg z.1.im)
  constructor <;> nlinarith [sq_nonneg (2 * z.1.re + b * z.1.im), sq_nonneg z.1.im]

theorem quadraticNormBall_abs_bounds {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {N : ℕ} (z : QuadraticNormBall d b N) :
    |2 * z.1.re + b * z.1.im| ≤ ((4 * N).sqrt : ℤ) ∧
      |z.1.im| ≤ ((4 * N).sqrt : ℤ) := by
  have hb := quadraticNormBall_sq_bounds hD z
  have bound (a : ℤ) (ha : a ^ 2 ≤ 4 * (N : ℤ)) : |a| ≤ ((4 * N).sqrt : ℤ) := by
    have ha' : (a.natAbs : ℤ) ^ 2 ≤ 4 * N := by simpa only [Int.natCast_natAbs, sq_abs] using ha
    have hn : a.natAbs ^ 2 ≤ 4 * N := by exact_mod_cast ha'
    have hroot := Nat.le_sqrt'.mpr hn
    have hcast : (a.natAbs : ℤ) ≤ ((4 * N).sqrt : ℤ) := by exact_mod_cast hroot
    simpa only [Int.natCast_natAbs] using hcast
  exact ⟨bound _ hb.1, bound _ hb.2⟩

def quadraticNormBallEmbedding {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (N : ℕ) :
    QuadraticNormBall d b N ↪
      {a : ℤ // a ∈ Finset.Icc (-((4 * N).sqrt : ℤ)) ((4 * N).sqrt : ℤ)} ×
      {a : ℤ // a ∈ Finset.Icc (-((4 * N).sqrt : ℤ)) ((4 * N).sqrt : ℤ)} where
  toFun z := (⟨2 * z.1.re + b * z.1.im, Finset.mem_Icc.mpr
    (abs_le.mp (quadraticNormBall_abs_bounds hD z).1)⟩,
    ⟨z.1.im, Finset.mem_Icc.mpr (abs_le.mp (quadraticNormBall_abs_bounds hD z).2)⟩)
  inj' := by
    intro z w h
    have h₁ := congrArg (fun x => x.1.1) h
    have h₂ := congrArg (fun x => x.2.1) h
    apply Subtype.ext
    apply QuadraticAlgebra.ext
    · dsimp only at h₁ h₂
      rw [h₂] at h₁
      omega
    · exact h₂

theorem finite_quadraticNormBall {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (N : ℕ) :
    Finite (QuadraticNormBall d b N) :=
  Finite.of_injective (quadraticNormBallEmbedding hD N) (quadraticNormBallEmbedding hD N).injective

theorem natCard_quadraticNormBall_le {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (N : ℕ) :
    Nat.card (QuadraticNormBall d b N) ≤ 36 * (N + 1) := by
  let s := (4 * N).sqrt
  have hcard := Nat.card_le_card_of_injective (quadraticNormBallEmbedding hD N)
    (quadraticNormBallEmbedding hD N).injective
  have hinterval : Nat.card {a : ℤ // a ∈ Finset.Icc (-(s : ℤ)) (s : ℤ)} = 2 * s + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Int.card_Icc]
    omega
  rw [Nat.card_prod, hinterval] at hcard
  apply hcard.trans
  have hs : s * s ≤ 4 * N := Nat.sqrt_le _
  have hsN : s ≤ 4 * N := Nat.sqrt_le_self _
  nlinarith

theorem quadraticNorm_unit {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (u : (QuadraticAlgebra ℤ d b)ˣ) : (u : QuadraticAlgebra ℤ d b).norm = 1 := by
  have hu := u.isUnit.map (QuadraticAlgebra.norm : QuadraticAlgebra ℤ d b →* ℤ)
  have hn := quadraticNorm_nonneg hD (u : QuadraticAlgebra ℤ d b)
  rcases Int.isUnit_iff.mp hu with h | h
  · exact h
  · omega

theorem finite_quadraticOrder_units {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    Finite (QuadraticAlgebra ℤ d b)ˣ := by
  letI := finite_quadraticNormBall hD 1
  let f : (QuadraticAlgebra ℤ d b)ˣ → QuadraticNormBall d b 1 := fun u =>
    ⟨u, by rw [quadraticNorm_unit hD, Int.natAbs_one]⟩
  apply Finite.of_injective f
  intro u v h
  apply Units.ext
  exact congrArg Subtype.val h

end Bernays
