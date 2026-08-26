import ErdosProblems.Erdos327.Basic

namespace Erdos327

/-- A coordinate triple always produces a cancelled mixed conflict. -/
theorem mixedConflict_of_coordinates (t u w : ℕ) :
    MixedConflict
      (t * w * (2 * u + w))
      (t * u * (2 * u + w)) := by
  unfold MixedConflict
  refine ⟨t * w * u, ?_⟩
  ring

/-- In coprime coordinates, the common scale is exactly `gcd a b`. -/
theorem gcd_eq_coordinate_scale
    {a b t u w : ℕ}
    (hcop : Nat.Coprime u w)
    (ha : a = t * w * (2 * u + w))
    (hb : b = t * u * (2 * u + w)) :
    Nat.gcd a b = t * (2 * u + w) := by
  rw [ha, hb]
  calc
    Nat.gcd (t * w * (2 * u + w)) (t * u * (2 * u + w)) =
        Nat.gcd ((t * (2 * u + w)) * w)
          ((t * (2 * u + w)) * u) := by
            congr 1 <;> ring
    _ = (t * (2 * u + w)) * Nat.gcd w u :=
      Nat.gcd_mul_left (t * (2 * u + w)) w u
    _ = t * (2 * u + w) := by
      rw [hcop.symm.gcd_eq_one, mul_one]

/-- Every positive mixed conflict with an odd first endpoint has the
`t,w,u,2u+w` parametrization used in the analytic estimate. -/
theorem exists_mixed_coordinates
    {a b : ℕ} (ha : 0 < a) (_hb : 0 < b)
    (haodd : Odd a) (hconflict : MixedConflict a b) :
    ∃ t u w : ℕ,
      Nat.Coprime u w ∧
      a = t * w * (2 * u + w) ∧
      b = t * u * (2 * u + w) := by
  let g := Nat.gcd a b
  let u := b / g
  let w := a / g
  have hg : 0 < g := by
    exact Nat.gcd_pos_of_pos_left b ha
  have hga : g * w = a := by
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g * u = b := by
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hcopwu : Nat.Coprime w u := by
    simpa [g, u, w] using
      (Nat.coprime_div_gcd_div_gcd (m := a) (n := b) hg)
  have hcopuw : Nat.Coprime u w := hcopwu.symm
  have hoddw : Odd w := by
    have hoddgw : Odd (g * w) := by simpa [hga] using haodd
    exact Nat.Odd.of_mul_right hoddgw
  have hnormalized :
      g * (2 * u + w) ∣ g * (g * (w * u)) := by
    rw [← hga, ← hgb] at hconflict
    simpa [MixedConflict, mul_add, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      hconflict
  have hxdiv :
      2 * u + w ∣ g * (w * u) := by
    exact (mul_dvd_mul_iff_left hg.ne').mp hnormalized
  have hcopxw : Nat.Coprime (2 * u + w) w := by
    have hcop2w : Nat.Coprime 2 w :=
      hoddw.coprime_two_right.symm
    have hcop2uw : Nat.Coprime (2 * u) w :=
      Nat.Coprime.mul_left hcop2w hcopuw
    simpa [mul_one] using
      (Nat.coprime_add_mul_left_left (2 * u) w 1).mpr hcop2uw
  have hcopxu : Nat.Coprime (2 * u + w) u := by
    simpa using
      (Nat.coprime_mul_right_add_left w u 2).mpr hcopwu
  have hcopxwu : Nat.Coprime (2 * u + w) (w * u) :=
    Nat.Coprime.mul_right hcopxw hcopxu
  have hxg : 2 * u + w ∣ g :=
    hcopxwu.dvd_of_dvd_mul_right hxdiv
  let t := g / (2 * u + w)
  have ht : t * (2 * u + w) = g := by
    rw [mul_comm]
    exact Nat.mul_div_cancel' hxg
  refine ⟨t, u, w, hcopuw, ?_, ?_⟩
  · calc
      a = g * w := hga.symm
      _ = t * w * (2 * u + w) := by rw [← ht]; ring
  · calc
      b = g * u := hgb.symm
      _ = t * u * (2 * u + w) := by rw [← ht]; ring

/-- The coprime mixed coordinates are unique for positive endpoints. -/
theorem mixed_coordinates_unique
    {a b t u w t' u' w' : ℕ}
    (ha0 : 0 < a)
    (hcop : Nat.Coprime u w)
    (ha : a = t * w * (2 * u + w))
    (hb : b = t * u * (2 * u + w))
    (hcop' : Nat.Coprime u' w')
    (ha' : a = t' * w' * (2 * u' + w'))
    (hb' : b = t' * u' * (2 * u' + w')) :
    t = t' ∧ u = u' ∧ w = w' := by
  have hscale := gcd_eq_coordinate_scale hcop ha hb
  have hscale' := gcd_eq_coordinate_scale hcop' ha' hb'
  have hgpos : 0 < Nat.gcd a b :=
    Nat.gcd_pos_of_pos_left b ha0
  have hgw : Nat.gcd a b * w = a := by
    rw [hscale]
    calc
      t * (2 * u + w) * w =
          t * w * (2 * u + w) := by ring
      _ = a := ha.symm
  have hgw' : Nat.gcd a b * w' = a := by
    rw [hscale']
    calc
      t' * (2 * u' + w') * w' =
          t' * w' * (2 * u' + w') := by ring
      _ = a := ha'.symm
  have hgu : Nat.gcd a b * u = b := by
    rw [hscale]
    calc
      t * (2 * u + w) * u =
          t * u * (2 * u + w) := by ring
      _ = b := hb.symm
  have hgu' : Nat.gcd a b * u' = b := by
    rw [hscale']
    calc
      t' * (2 * u' + w') * u' =
          t' * u' * (2 * u' + w') := by ring
      _ = b := hb'.symm
  have hw : w = w' :=
    Nat.mul_left_cancel hgpos (hgw.trans hgw'.symm)
  have hu : u = u' :=
    Nat.mul_left_cancel hgpos (hgu.trans hgu'.symm)
  subst u'
  subst w'
  have hxpos : 0 < 2 * u + w := by
    have hxne : 2 * u + w ≠ 0 := by
      intro hx
      rw [hx, mul_zero] at ha
      omega
    exact Nat.pos_of_ne_zero hxne
  have ht : t = t' := by
    apply Nat.mul_left_cancel hxpos
    simpa [mul_comm] using hscale.symm.trans hscale'
  exact ⟨ht, rfl, rfl⟩

/-- For an odd endpoint, the original mixed conflict is equivalent to the
existence of the analytic coordinates. -/
theorem conflictOne_mixed_iff_exists_coordinates
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (haodd : Odd a) :
    ConflictOne a (2 * b) ↔
      ∃ t u w : ℕ,
        Nat.Coprime u w ∧
        a = t * w * (2 * u + w) ∧
        b = t * u * (2 * u + w) := by
  rw [mixed_conflict_iff haodd]
  constructor
  · exact exists_mixed_coordinates ha hb haodd
  · rintro ⟨t, u, w, _hcop, rfl, rfl⟩
    exact mixedConflict_of_coordinates t u w

end Erdos327
