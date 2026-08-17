import Mathlib

namespace Erdos54

/-- The numerical estimate at the end of the cyclic-growth argument. -/
theorem cyclicGrowth_raw_count_scale
    (F M B q u v R x : ℕ)
    (hu : 0 < u) (hv : 0 < v) (_hR : 0 < R)
    (huq : u ≤ q) (hq : q ≤ 6 * u)
    (hraw : F ≤ q.choose u * (B ^ u * M ^ (q - u)))
    (hB : B * R ≤ 2 * x)
    (huR : u ≤ 16 * v * R)
    (hxM : x ≤ 16 * v * M)
    (hpow : 2 ^ 30 * v ^ 4 ≤ u) :
    u ^ (u / 2) * F ≤ M ^ q := by
  let c : ℕ := 2 ^ 15 * v ^ 2
  have hc_sq : c ^ 2 ≤ u := by
    dsimp [c]
    calc
      (2 ^ 15 * v ^ 2) ^ 2 = 2 ^ 30 * v ^ 4 := by ring
      _ ≤ u := hpow
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hc_le_u : c ≤ u := by
    exact (Nat.le_mul_self c).trans (by simpa [pow_two] using hc_sq)
  have hBu : 64 * B * u ≤ c * M := by
    calc
      64 * B * u ≤ 64 * B * (16 * v * R) :=
        Nat.mul_le_mul_left (64 * B) huR
      _ = 2 ^ 10 * v * (B * R) := by ring
      _ ≤ 2 ^ 10 * v * (2 * x) :=
        Nat.mul_le_mul_left (2 ^ 10 * v) hB
      _ ≤ 2 ^ 10 * v * (2 * (16 * v * M)) :=
        Nat.mul_le_mul_left (2 ^ 10 * v) (Nat.mul_le_mul_left 2 hxM)
      _ = c * M := by simp [c]; ring
  have hc_power : u ^ (u / 2) * c ^ u ≤ u ^ u := by
    have hc_mod : c ^ (u % 2) ≤ u ^ (u % 2) :=
      Nat.pow_le_pow_left hc_le_u (u % 2)
    have hc_pair : (c ^ 2) ^ (u / 2) ≤ u ^ (u / 2) :=
      Nat.pow_le_pow_left hc_sq (u / 2)
    calc
      u ^ (u / 2) * c ^ u =
          u ^ (u / 2) * ((c ^ 2) ^ (u / 2) * c ^ (u % 2)) := by
            congr 1
            calc
              c ^ u = c ^ (2 * (u / 2) + u % 2) :=
                congrArg (fun e : ℕ => c ^ e) (Nat.div_add_mod u 2).symm
              _ = (c ^ 2) ^ (u / 2) * c ^ (u % 2) := by
                rw [pow_add, pow_mul]
      _ ≤ u ^ (u / 2) * (u ^ (u / 2) * u ^ (u % 2)) := by
        gcongr
      _ = u ^ u := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
  have hscaled : u ^ (u / 2) * (64 * B) ^ u ≤ M ^ u := by
    have hpowBu : (64 * B * u) ^ u ≤ (c * M) ^ u :=
      Nat.pow_le_pow_left hBu u
    have hmul :
        (u ^ (u / 2) * (64 * B) ^ u) * u ^ u ≤ M ^ u * u ^ u := by
      calc
        (u ^ (u / 2) * (64 * B) ^ u) * u ^ u =
            u ^ (u / 2) * ((64 * B) ^ u * u ^ u) := by ac_rfl
        _ ≤ u ^ (u / 2) * (c ^ u * M ^ u) := by
          apply Nat.mul_le_mul_left
          simpa only [mul_pow] using hpowBu
        _ = (u ^ (u / 2) * c ^ u) * M ^ u := by ac_rfl
        _ ≤ u ^ u * M ^ u := Nat.mul_le_mul_right (M ^ u) hc_power
        _ = M ^ u * u ^ u := by ac_rfl
    exact Nat.le_of_mul_le_mul_right hmul (pow_pos hu u)
  calc
    u ^ (u / 2) * F ≤
        u ^ (u / 2) * (q.choose u * (B ^ u * M ^ (q - u))) :=
      Nat.mul_le_mul_left _ hraw
    _ ≤ u ^ (u / 2) * (2 ^ q * (B ^ u * M ^ (q - u))) := by
      gcongr
      exact Nat.choose_le_two_pow q u
    _ ≤ u ^ (u / 2) * ((2 ^ (6 * u)) * (B ^ u * M ^ (q - u))) := by
      gcongr
      norm_num
    _ = (u ^ (u / 2) * (64 * B) ^ u) * M ^ (q - u) := by
      rw [pow_mul]
      norm_num
      rw [mul_pow]
      ring
    _ ≤ M ^ u * M ^ (q - u) := Nat.mul_le_mul_right _ hscaled
    _ = M ^ q := by rw [← pow_add, Nat.add_sub_of_le huq]

end Erdos54
