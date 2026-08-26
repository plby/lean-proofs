import Mathlib.Tactic

/-! # Integer constants for dense-core rank windows -/

namespace Erdos19

theorem first_rank_tail_bound (n r h t : ℕ) (hh : 2 ≤ h) (hr : h ^ 4 ≤ r)
    (hb : (n - n / h ^ 4) * (r - 1) + t * (r / h ^ 2 + 1) ≤ r * n) :
    t * h ^ 2 ≤ 2 * n := by
  have hhpos : 0 < h := by omega
  have hpowpos : 0 < h ^ 4 := pow_pos hhpos _
  have hrpos : 1 ≤ r := (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpowpos)).trans hr
  have hmsplit := Nat.sub_add_cancel (Nat.div_le_self n (h ^ 4))
  have hrsplit : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
  have hmexpand := congrArg (fun x ↦ r * x) hmsplit
  have hrexpand := congrArg (fun x ↦ (n - n / h ^ 4) * x) hrsplit
  have htm : t * (r / h ^ 2 + 1) ≤ r * (n / h ^ 4) + n := by
    nlinarith only [hb, hmexpand, hrexpand, Nat.sub_le n (n / h ^ 4)]
  have hscaled := Nat.mul_le_mul_right (h ^ 4) htm
  have hquot := Nat.mul_le_mul_left r (Nat.div_mul_le_self n (h ^ 4))
  have hrn := Nat.mul_le_mul_left n hr
  have ht : t * (r / h ^ 2 + 1) * h ^ 4 ≤ 2 * r * n := by
    nlinarith only [hscaled, hquot, hrn]
  have hgap : r ≤ (r / h ^ 2 + 1) * h ^ 2 := by
    simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ r (pow_pos hhpos 2)).le
  have hgapmul := Nat.mul_le_mul_left (t * h ^ 2) hgap
  have hcancel : r * (t * h ^ 2) ≤ r * (2 * n) := by
    nlinarith only [ht, hgapmul]
  exact Nat.le_of_mul_le_mul_left hcancel (by omega)

theorem second_rank_tail_bound (n r h t : ℕ) (hh : 2 ≤ h) (hr : h ^ 4 ≤ r)
    (hb : (n - n / h ^ 4) * (r - 1) + t * (r / h + 1) ≤
      (r + r / h ^ 2) * n) :
    t * h ≤ 3 * n := by
  have hhpos : 0 < h := by omega
  have hh2 : 1 ≤ h ^ 2 := by nlinarith only [hh]
  have h24 : h ^ 2 ≤ h ^ 4 := by
    nlinarith only [Nat.mul_le_mul_left (h ^ 2) hh2]
  have hrpos : 1 ≤ r := hh2.trans (h24.trans hr)
  have hmsplit := Nat.sub_add_cancel (Nat.div_le_self n (h ^ 4))
  have hrsplit : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
  have hmexpand := congrArg (fun x ↦ r * x) hmsplit
  have hrexpand := congrArg (fun x ↦ (n - n / h ^ 4) * x) hrsplit
  have htm : t * (r / h + 1) ≤ r * (n / h ^ 4) + (r / h ^ 2) * n + n := by
    nlinarith only [hb, hmexpand, hrexpand, Nat.sub_le n (n / h ^ 4)]
  have hscaled := Nat.mul_le_mul_right (h ^ 2) htm
  have hquot₁ : (n / h ^ 4) * h ^ 2 ≤ n :=
    (Nat.mul_le_mul_left _ h24).trans (Nat.div_mul_le_self n _)
  have hquot₂ := Nat.div_mul_le_self r (h ^ 2)
  have hq₁ := Nat.mul_le_mul_left r hquot₁
  have hq₂ := Nat.mul_le_mul_left n hquot₂
  have hrn := Nat.mul_le_mul_left n (h24.trans hr)
  have ht : t * (r / h + 1) * h ^ 2 ≤ 3 * r * n := by
    nlinarith only [hscaled, hq₁, hq₂, hrn]
  have hgap : r ≤ (r / h + 1) * h := by
    simpa only [Nat.mul_comm] using (Nat.lt_mul_div_succ r hhpos).le
  have hgapmul := Nat.mul_le_mul_left (t * h) hgap
  have hcancel : r * (t * h) ≤ r * (3 * n) := by
    nlinarith only [ht, hgapmul]
  exact Nat.le_of_mul_le_mul_left hcancel (by omega)

#print axioms first_rank_tail_bound
#print axioms second_rank_tail_bound

/-- The explicit cardinality estimate yields all but a `10/h` fraction of
the global pair volume. The slightly stronger square `n^2` appears here. -/
theorem rank_window_pair_weight_bound (n r h t : ℕ) (hh : 16 ≤ h)
    (hr : h ^ 4 ≤ r) (hrn : r ≤ n)
    (hb : (n - n / h ^ 4 - 2 * n / h ^ 2) *
        (n - n / h ^ 4 - (3 * n / h + (n - 1) / (r - 1) + 1)) ≤
      t * (r * (r + r / h))) :
    (h - 10) * n ^ 2 ≤ h * t * r * (r - 1) := by
  let a := n - n / h ^ 4 - 2 * n / h ^ 2
  let b := n - n / h ^ 4 - (3 * n / h + (n - 1) / (r - 1) + 1)
  let R := r + r / h
  have hhpos : 0 < h := by omega
  have hh2 : h ≤ h ^ 2 := by nlinarith only [hh]
  have h24 : h ^ 2 ≤ h ^ 4 := by
    nlinarith only [Nat.mul_le_mul_left (h ^ 2) (show 1 ≤ h ^ 2 by omega)]
  have hhr : h ≤ r := hh2.trans (h24.trans hr)
  have hhn : h ≤ n := hhr.trans hrn
  have hhr' : h ≤ r - 1 := by
    have hx : h + 1 ≤ h ^ 2 := by nlinarith only [hh]
    omega
  have hq₀ : (n / h ^ 4) * h ≤ n :=
    (Nat.mul_le_mul_left _ (hh2.trans h24)).trans (Nat.div_mul_le_self n _)
  have hq₁ : (2 * n / h ^ 2) * h ≤ n := by
    have hx := Nat.div_mul_le_self (2 * n) (h ^ 2)
    have hy := Nat.mul_le_mul_left (2 * n / h ^ 2)
      (show 2 * h ≤ h ^ 2 by nlinarith only [hh])
    nlinarith only [hx, hy]
  have hq₂ : (3 * n / h) * h ≤ 3 * n := Nat.div_mul_le_self _ _
  have hq₃ : ((n - 1) / (r - 1)) * h ≤ n :=
    ((Nat.mul_le_mul_left _ hhr').trans (Nat.div_mul_le_self _ _)).trans (Nat.sub_le _ _)
  have hsuba : n ≤ a + n / h ^ 4 + 2 * n / h ^ 2 := by
    dsimp only [a]
    omega
  have hsubb : n ≤ b + n / h ^ 4 + 3 * n / h + (n - 1) / (r - 1) + 1 := by
    dsimp only [b]
    omega
  have ha : (h - 2) * n ≤ h * a := by
    have hm := Nat.mul_le_mul_right h hsuba
    have he := congrArg (fun x ↦ x * n) (Nat.sub_add_cancel (show 2 ≤ h by omega))
    nlinarith only [hm, he, hq₀, hq₁]
  have hb' : (h - 6) * n ≤ h * b := by
    have hm := Nat.mul_le_mul_right h hsubb
    have he := congrArg (fun x ↦ x * n) (Nat.sub_add_cancel (show 6 ≤ h by omega))
    nlinarith only [hm, he, hq₀, hq₂, hq₃, hhn]
  have hconst₁ : h * (h - 8) ≤ (h - 2) * (h - 6) := by
    have h2 := Nat.sub_add_cancel (show 2 ≤ h by omega)
    have h6 := Nat.sub_add_cancel (show 6 ≤ h by omega)
    have h8 := Nat.sub_add_cancel (show 8 ≤ h by omega)
    nlinarith only [h2, h6, h8]
  have hstep₁ : (h - 8) * n ^ 2 ≤ h * t * r * R := by
    apply Nat.le_of_mul_le_mul_left (c := h) _ hhpos
    calc
      h * ((h - 8) * n ^ 2) ≤ (h - 2) * (h - 6) * n ^ 2 := by
        nlinarith only [Nat.mul_le_mul_right (n ^ 2) hconst₁]
      _ ≤ (h * a) * (h * b) := by
        nlinarith only [Nat.mul_le_mul ha hb']
      _ = h ^ 2 * (a * b) := by ring
      _ ≤ h ^ 2 * (t * (r * R)) := Nat.mul_le_mul_left _ hb
      _ = h * (h * t * r * R) := by ring
  have hratio : (h - 2) * R ≤ h * (r - 1) := by
    have hq := Nat.div_mul_le_self r h
    have hqnonneg := Nat.zero_le (r / h)
    have hhsub := Nat.sub_add_cancel (show 2 ≤ h by omega)
    have hrsub := Nat.sub_add_cancel (show 1 ≤ r by omega)
    have hhexpand := congrArg (fun x ↦ x * (r + r / h)) hhsub
    have hrexpand := congrArg (fun x ↦ h * x) hrsub
    dsimp only [R]
    nlinarith only [hq, hqnonneg, hhexpand, hrexpand, hhr]
  have hconst₂ : h * (h - 10) ≤ (h - 2) * (h - 8) := by
    have h2 := Nat.sub_add_cancel (show 2 ≤ h by omega)
    have h8 := Nat.sub_add_cancel (show 8 ≤ h by omega)
    have h10 := Nat.sub_add_cancel (show 10 ≤ h by omega)
    nlinarith only [h2, h8, h10]
  apply Nat.le_of_mul_le_mul_left (c := h) _ hhpos
  calc
    h * ((h - 10) * n ^ 2) ≤ (h - 2) * ((h - 8) * n ^ 2) := by
      nlinarith only [Nat.mul_le_mul_right (n ^ 2) hconst₂]
    _ ≤ (h - 2) * (h * t * r * R) := Nat.mul_le_mul_left _ hstep₁
    _ = (h * t * r) * ((h - 2) * R) := by ring
    _ ≤ (h * t * r) * (h * (r - 1)) := Nat.mul_le_mul_left _ hratio
    _ = h * (h * t * r * (r - 1)) := by ring

#print axioms rank_window_pair_weight_bound

end Erdos19
