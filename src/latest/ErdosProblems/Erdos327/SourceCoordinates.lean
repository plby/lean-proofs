import ErdosProblems.Erdos327.Basic

namespace Erdos327

/-- A second-variant conflict supplies the coprime reduced coordinates used
in the centered source estimate.  The coordinates are canonical quotients by
`gcd b c`, and their product satisfies Sawin's key divisibility relation. -/
theorem sawin_coordinates_of_conflictTwo
    {b c : ℕ} (hb : 0 < b)
    (hconflict : ConflictTwo b c) :
    ∃ g u v : ℕ,
      g = Nat.gcd b c ∧
      b = g * u ∧
      c = g * v ∧
      Nat.Coprime u v ∧
      u * (u + v) ∣ 2 * b := by
  let g := Nat.gcd b c
  let u := b / g
  let v := c / g
  have hg : 0 < g :=
    Nat.gcd_pos_of_pos_left c hb
  have hgb : g * u = b :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left b c)
  have hgc : g * v = c :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right b c)
  have hcop : Nat.Coprime u v := by
    simpa [g, u, v] using
      (Nat.coprime_div_gcd_div_gcd (m := b) (n := c) hg)
  have hnormalized :
      g * (u + v) ∣ g * (2 * g * (u * v)) := by
    rw [← hgb, ← hgc] at hconflict
    simpa [ConflictTwo, mul_add, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using hconflict
  have hsumDvdProduct :
      u + v ∣ 2 * g * (u * v) :=
    (mul_dvd_mul_iff_left hg.ne').mp hnormalized
  have hsumCopV : Nat.Coprime (u + v) v :=
    Nat.coprime_add_self_left.mpr hcop
  have hsumDvd : u + v ∣ 2 * b := by
    have : u + v ∣ (2 * g * u) * v := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hsumDvdProduct
    have : u + v ∣ 2 * g * u :=
      hsumCopV.dvd_of_dvd_mul_right this
    simpa [← hgb, mul_assoc, mul_left_comm, mul_comm] using this
  have huDvd : u ∣ 2 * b := by
    refine ⟨2 * g, ?_⟩
    rw [← hgb]
    ring
  have hcopUSum : Nat.Coprime u (u + v) :=
    Nat.coprime_self_add_right.mpr hcop
  have hproductDvd : u * (u + v) ∣ 2 * b :=
    hcopUSum.mul_dvd_of_dvd_of_dvd huDvd hsumDvd
  exact ⟨g, u, v, rfl, hgb.symm, hgc.symm, hcop, hproductDvd⟩

end Erdos327
