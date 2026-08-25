import ErdosProblems.Erdos1141.BurgessDenominators

/-!
# Divisibility classes in translated intervals

The enumeration argument is extracted from `Erdos587.NVDevelopment`.
-/

namespace Pollack17.Burgess

open scoped BigOperators

def residueClassLength (H d a : ℕ) : ℕ :=
  if a < H then (H + d - 1 - a) / d else 0

lemma lt_residueClassLength_iff
    {H d a j : ℕ} (hd : 0 < d) (ha : a < H) :
    j < residueClassLength H d a ↔ a + d * j < H := by
  rw [residueClassLength, if_pos ha, Nat.lt_div_iff_mul_lt hd]
  have heq : H + d - 1 - a - (d - 1) = H - a := by omega
  rw [heq, Nat.mul_comm j d]
  omega

lemma residueClassLength_eq_zero_of_le
    {H d a : ℕ} (ha : H ≤ a) : residueClassLength H d a = 0 := by
  simp [residueClassLength, Nat.not_lt.mpr ha]

/-- Explicit enumeration of the indices in a fixed divisibility class. -/
lemma filter_range_dvd_add_eq_image_residueClass
    {M H d a : ℕ} (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    (Finset.range H).filter (fun i ↦ d ∣ M + i) =
      (Finset.range (residueClassLength H d a)).image (fun j ↦ a + d * j) := by
  ext i
  constructor
  · intro hi
    have hiH := (Finset.mem_filter.mp hi).1
    have hMi := (Finset.mem_filter.mp hi).2
    have hmod : i ≡ a [MOD d] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      have hMiz : ((M + i : ℕ) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff (M + i) d).mpr hMi
      have hMaz : ((M + a : ℕ) : ZMod d) = 0 :=
        (ZMod.natCast_eq_zero_iff (M + a) d).mpr hMa
      calc
        (i : ZMod d) = ((M + i : ℕ) : ZMod d) - (M : ZMod d) := by
          push_cast
          ring
        _ = -(M : ZMod d) := by rw [hMiz]; ring
        _ = ((M + a : ℕ) : ZMod d) - (M : ZMod d) := by rw [hMaz]; ring
        _ = (a : ZMod d) := by push_cast; ring
    have himod : i % d = a := Nat.mod_eq_of_modEq hmod ha
    let j := i / d
    have hij : i = a + d * j := by
      dsimp [j]
      calc
        i = d * (i / d) + i % d := (Nat.div_add_mod i d).symm
        _ = d * (i / d) + a := by rw [himod]
        _ = a + d * (i / d) := by omega
    have hai : a ≤ i := by rw [hij]; exact Nat.le_add_right _ _
    have haH : a < H := hai.trans_lt (Finset.mem_range.mp hiH)
    have hj : j < residueClassLength H d a :=
      (lt_residueClassLength_iff hd haH).mpr (by
        rw [← hij]
        exact Finset.mem_range.mp hiH)
    rw [Finset.mem_image]
    exact ⟨j, Finset.mem_range.mpr hj, hij.symm⟩
  · intro hi
    rw [Finset.mem_image] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    have haH : a < H := by
      by_contra h
      have hz := residueClassLength_eq_zero_of_le
        (d := d) (Nat.le_of_not_gt h)
      rw [Finset.mem_range, hz] at hj
      omega
    have hlt : a + d * j < H :=
      (lt_residueClassLength_iff hd haH).mp (Finset.mem_range.mp hj)
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr hlt
    · obtain ⟨c, hc⟩ := hMa
      refine ⟨c + j, ?_⟩
      calc
        M + (a + d * j) = (M + a) + d * j := by omega
        _ = d * c + d * j := by rw [hc]
        _ = d * (c + j) := by ring

lemma sum_ite_dvd_eq_residueClass
    (f : ℕ → ℝ) {M H d a : ℕ}
    (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    (∑ i ∈ Finset.range H, if d ∣ M + i then f (M + i) else 0) =
      ∑ j ∈ Finset.range (residueClassLength H d a),
        f (M + (a + d * j)) := by
  rw [← Finset.sum_filter]
  rw [filter_range_dvd_add_eq_image_residueClass hd ha hMa]
  rw [Finset.sum_image]
  intro x hx y hy hxy
  exact mul_left_cancel₀ hd.ne' (Nat.add_left_cancel hxy)

lemma residueClassLength_le
    {M H d a : ℕ} (hd : 0 < d) (ha : a < d) (hMa : d ∣ M + a) :
    residueClassLength H d a ≤ H := by
  have heq := filter_range_dvd_add_eq_image_residueClass
    (M := M) (H := H) hd ha hMa
  have hinj : Function.Injective (fun j : ℕ ↦ a + d * j) := by
    intro x y hxy
    exact mul_left_cancel₀ hd.ne' (Nat.add_left_cancel hxy)
  have hcard :
      residueClassLength H d a =
        ((Finset.range H).filter (fun i ↦ d ∣ M + i)).card := by
    rw [heq, Finset.card_image_of_injective _ hinj]
    simp
  rw [hcard]
  exact (Finset.card_filter_le _ _).trans_eq (by simp)

/-- A divisibility-restricted sum of a completely multiplicative real
function is, up to the constant factor at `d`, an ordinary consecutive sum
of length at most `H`. -/
lemma exists_divisible_sum_factorization
    (f : ℕ → ℝ) (hmul : ∀ a b, f (a * b) = f a * f b)
    (M H d : ℕ) (hd : 0 < d) :
    ∃ K L : ℕ, L ≤ H ∧
      (∑ i ∈ Finset.range H,
        if d ∣ M + i then f (M + i) else 0) =
        f d * ∑ j ∈ Finset.range L, f (K + j) := by
  have : NeZero d := ⟨hd.ne'⟩
  let a : ℕ := (-(M : ZMod d)).val
  let K : ℕ := (M + a) / d
  let L : ℕ := residueClassLength H d a
  have ha : a < d := ZMod.val_lt _
  have hMa : d ∣ M + a := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    change (M : ZMod d) + (a : ZMod d) = 0
    rw [show (a : ZMod d) = -(M : ZMod d) by
      exact ZMod.natCast_zmod_val _]
    ring
  have hK : d * K = M + a := Nat.mul_div_cancel' hMa
  refine ⟨K, L, residueClassLength_le hd ha hMa, ?_⟩
  rw [sum_ite_dvd_eq_residueClass f hd ha hMa]
  calc
    (∑ j ∈ Finset.range L, f (M + (a + d * j))) =
        ∑ j ∈ Finset.range L, f (d * (K + j)) := by
          apply Finset.sum_congr rfl
          intro j hj
          congr 2
          calc
            M + (a + d * j) = (M + a) + d * j := by omega
            _ = d * K + d * j := by rw [hK]
            _ = d * (K + j) := by ring
    _ = ∑ j ∈ Finset.range L, f d * f (K + j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hmul d (K + j)
    _ = f d * ∑ j ∈ Finset.range L, f (K + j) := by
      rw [Finset.mul_sum]

end Pollack17.Burgess
