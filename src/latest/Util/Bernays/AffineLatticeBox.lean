import Util.Bernays.QuadraticNormBalls
import Mathlib.Data.ZMod.Basic

/-!
# Integral affine boxes with prescribed residue classes
-/

namespace Bernays

theorem quadraticNorm_natAbs_le {d b : ℤ} (z : QuadraticAlgebra ℤ d b) {R : ℕ}
    (hr : z.re.natAbs ≤ R) (hi : z.im.natAbs ≤ R) :
    z.norm.natAbs ≤ (1 + b.natAbs + d.natAbs) * R ^ 2 := by
  rw [QuadraticAlgebra.norm_def]
  calc
    _ ≤ (z.re * z.re + b * z.re * z.im).natAbs + (d * z.im * z.im).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ (z.re * z.re).natAbs + (b * z.re * z.im).natAbs + (d * z.im * z.im).natAbs :=
      Nat.add_le_add_right (Int.natAbs_add_le _ _) _
    _ = z.re.natAbs ^ 2 + b.natAbs * z.re.natAbs * z.im.natAbs + d.natAbs * z.im.natAbs ^ 2 := by
      simp only [Int.natAbs_mul]
      ring
    _ ≤ R ^ 2 + b.natAbs * R * R + d.natAbs * R ^ 2 := by gcongr
    _ = _ := by ring

theorem residueGrid_injective {Q : ℕ} (hQ : 0 < Q) {r s : ZMod Q} {i j : ℕ}
    (h : r.val + Q * i = s.val + Q * j) : r = s ∧ i = j := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hm := congrArg (fun n : ℕ => n % Q) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt r),
    Nat.mod_eq_of_lt (ZMod.val_lt s)] at hm
  have hrs : r = s := ZMod.val_injective Q hm
  refine ⟨hrs, ?_⟩
  rw [hm] at h
  exact Nat.mul_left_cancel hQ (Nat.add_left_cancel h)

def affineBoxPoint {d b : ℤ} (c : QuadraticAlgebra ℤ d b) (μ Q L : ℕ)
    (r : ZMod Q × ZMod Q) (i j : Fin L) : QuadraticAlgebra ℤ d b :=
  ⟨c.re + (μ : ℤ) * (r.1.val + Q * (L + i.val)),
    c.im + (μ : ℤ) * (r.2.val + Q * j.val)⟩

theorem affineBoxPoint_injective {d b : ℤ} (c : QuadraticAlgebra ℤ d b)
    {μ Q L : ℕ} (hμ : 0 < μ) (hQ : 0 < Q) :
    Function.Injective (fun x : (ZMod Q × ZMod Q) × Fin L × Fin L =>
      affineBoxPoint c μ Q L x.1 x.2.1 x.2.2) := by
  intro x y h
  have hre := congrArg QuadraticAlgebra.re h
  have him := congrArg QuadraticAlgebra.im h
  have hμZ : (μ : ℤ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hx : x.1.1.val + Q * (L + x.2.1.val) = y.1.1.val + Q * (L + y.2.1.val) := by
    exact_mod_cast (mul_left_cancel₀ hμZ (add_left_cancel hre))
  have hy : x.1.2.val + Q * x.2.2.val = y.1.2.val + Q * y.2.2.val := by
    exact_mod_cast (mul_left_cancel₀ hμZ (add_left_cancel him))
  obtain ⟨hr₁, hi⟩ := residueGrid_injective hQ hx
  obtain ⟨hr₂, hj⟩ := residueGrid_injective hQ hy
  exact Prod.ext (Prod.ext hr₁ hr₂) (Prod.ext (Fin.ext (Nat.add_left_cancel hi)) (Fin.ext hj))

theorem affineBoxPoint_re_pos {d b : ℤ} (c : QuadraticAlgebra ℤ d b)
    {μ Q L : ℕ} (hμ : 0 < μ) (hQ : 0 < Q) (hL : c.re.natAbs < L)
    (r : ZMod Q × ZMod Q) (i j : Fin L) :
    0 < (affineBoxPoint c μ Q L r i j).re := by
  have hlow : L ≤ μ * (r.1.val + Q * (L + i.val)) := by
    calc
      L ≤ L + i.val := Nat.le_add_right _ _
      _ ≤ Q * (L + i.val) := Nat.le_mul_of_pos_left _ hQ
      _ ≤ r.1.val + Q * (L + i.val) := Nat.le_add_left _ _
      _ ≤ μ * (r.1.val + Q * (L + i.val)) := Nat.le_mul_of_pos_left _ hμ
  have hlowZ : (L : ℤ) ≤ (μ : ℤ) * (r.1.val + Q * (L + i.val)) := by exact_mod_cast hlow
  have hLZ : (c.re.natAbs : ℤ) < L := by exact_mod_cast hL
  have hbase : -(c.re.natAbs : ℤ) ≤ c.re := by simp only [Int.natCast_natAbs]; exact neg_abs_le _
  change 0 < c.re + (μ : ℤ) * (r.1.val + Q * (L + i.val))
  omega

theorem affineBoxPoint_ne_zero {d b : ℤ} (c : QuadraticAlgebra ℤ d b)
    {μ Q L : ℕ} (hμ : 0 < μ) (hQ : 0 < Q) (hL : c.re.natAbs < L)
    (r : ZMod Q × ZMod Q) (i j : Fin L) : affineBoxPoint c μ Q L r i j ≠ 0 := by
  intro h
  have hp := affineBoxPoint_re_pos c hμ hQ hL r i j
  rw [h, QuadraticAlgebra.re_zero] at hp
  exact (lt_irrefl 0) hp

theorem affineBoxPoint_norm_le {d b : ℤ} (c : QuadraticAlgebra ℤ d b)
    {μ Q L : ℕ} (hQ : 0 < Q) (hrL : c.re.natAbs < L) (hiL : c.im.natAbs < L)
    (r : ZMod Q × ZMod Q) (i j : Fin L) :
    (affineBoxPoint c μ Q L r i j).norm.natAbs ≤
      (1 + b.natAbs + d.natAbs) * (2 * μ + 1) ^ 2 * Q ^ 2 * L ^ 2 := by
  letI : NeZero Q := ⟨hQ.ne'⟩
  have hr₁ := ZMod.val_lt r.1
  have hr₂ := ZMod.val_lt r.2
  have hi := i.isLt
  have hj := j.isLt
  have hx : r.1.val + Q * (L + i.val) ≤ 2 * Q * L := by nlinarith
  have hy : r.2.val + Q * j.val ≤ 2 * Q * L := by nlinarith
  have hLQ : L ≤ Q * L := Nat.le_mul_of_pos_left _ hQ
  have bound (a : ℤ) (n : ℕ) (ha : a.natAbs < L) (hn : n ≤ 2 * Q * L) :
      (a + (μ : ℤ) * n).natAbs ≤ (2 * μ + 1) * Q * L := by
    have h := Int.natAbs_add_le a (((μ * n : ℕ) : ℤ))
    have hab : (a + (μ : ℤ) * n).natAbs ≤ a.natAbs + μ * n := by
      simpa only [Nat.cast_mul, Int.natAbs_mul, Int.natAbs_natCast] using h
    have hm := Nat.mul_le_mul_left μ hn
    nlinarith
  have hre : (affineBoxPoint c μ Q L r i j).re.natAbs ≤ (2 * μ + 1) * Q * L := by
    simpa only [affineBoxPoint, Nat.cast_add, Nat.cast_mul] using bound c.re _ hrL hx
  have him : (affineBoxPoint c μ Q L r i j).im.natAbs ≤ (2 * μ + 1) * Q * L := by
    simpa only [affineBoxPoint, Nat.cast_add, Nat.cast_mul] using bound c.im _ hiL hy
  calc
    _ ≤ (1 + b.natAbs + d.natAbs) * ((2 * μ + 1) * Q * L) ^ 2 :=
      quadraticNorm_natAbs_le _ hre him
    _ = _ := by ring

theorem affineBoxPoint_sub_base {d b : ℤ} (c : QuadraticAlgebra ℤ d b) (μ Q L : ℕ)
    (r : ZMod Q × ZMod Q) (i j : Fin L) :
    affineBoxPoint c μ Q L r i j - c =
      (μ : QuadraticAlgebra ℤ d b) *
        ⟨(r.1.val + Q * (L + i.val) : ℕ), (r.2.val + Q * j.val : ℕ)⟩ := by
  ext <;> simp [affineBoxPoint, sub_eq_add_neg] <;> ring

end Bernays
