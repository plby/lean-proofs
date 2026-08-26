import ErdosProblems.Erdos327.Analytic.Regularity
import ErdosProblems.Erdos327.Assembly
import ErdosProblems.Erdos327.Coordinates

/-!
# Mixed-edge set and coordinate bounds

The analytic estimate counts mixed conflict edges, while the assembly
deletes their odd endpoints.  This file gives the exact finite-set
comparison and records the elementary coordinate bounds for the
canonical regular source and odd host.
-/

namespace Erdos327

open Finset

/-- Mixed conflict edges between an odd host `O` and a source `B`. -/
noncomputable def mixedEdges (O B : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (O ×ˢ B).filter fun e ↦ ConflictOne e.1 (2 * e.2)

@[simp] theorem mem_mixedEdges
    {O B : Finset ℕ} {a b : ℕ} :
    (a, b) ∈ mixedEdges O B ↔
      a ∈ O ∧ b ∈ B ∧ ConflictOne a (2 * b) := by
  classical
  simp [mixedEdges, and_assoc]

/-- The set of bad odd endpoints is the first-coordinate image of the
mixed-edge set. -/
theorem mixedBad_eq_image_mixedEdges
    (O B : Finset ℕ) :
    mixedBad O B = (mixedEdges O B).image Prod.fst := by
  classical
  ext a
  rw [mem_mixedBad]
  simp only [mem_image]
  constructor
  · rintro ⟨haO, b, hbB, hab⟩
    exact ⟨(a, b), mem_mixedEdges.mpr ⟨haO, hbB, hab⟩, rfl⟩
  · rintro ⟨e, he, hea⟩
    rcases mem_mixedEdges.mp he with ⟨heO, heB, heConflict⟩
    exact ⟨hea ▸ heO, e.2, heB, hea ▸ heConflict⟩

/-- Counting mixed edges bounds the number of odd vertices deleted by
the assembly. -/
theorem card_mixedBad_le_card_mixedEdges
    (O B : Finset ℕ) :
    (mixedBad O B).card ≤ (mixedEdges O B).card := by
  rw [mixedBad_eq_image_mixedEdges]
  exact card_image_le

/-- Coordinate data for one mixed edge between the canonical regular
odd host and regular rough source.  The bounds `w ≤ 5u` and
`2u+w ≤ 7u` again absorb the lower-endpoint floor. -/
theorem regularMixedEdge_coordinates
    {L N a b : ℕ} {Ab Kb Ao Ko : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N)
    (hedge :
      (a, b) ∈ mixedEdges
        (Analytic.regularOddHost L Ao Ko N)
        (Analytic.regularSource L Ab Kb N)) :
    ∃ t u w : ℕ,
      0 < t ∧ 0 < u ∧ 0 < w ∧
      Nat.Coprime u w ∧
      a = t * w * (2 * u + w) ∧
      b = t * u * (2 * u + w) ∧
      u ≤ N ∧ w ≤ 6 * u ∧ 2 * u + w ≤ 8 * u ∧
      Analytic.Rough L t ∧ Analytic.Rough L u ∧
      Analytic.Rough L (2 * u + w) ∧
      Odd t ∧ Odd u ∧ Odd w ∧ Odd (2 * u + w) ∧
      Analytic.CutoffRegular L Ab Kb b ∧
      Analytic.CutoffRegular L Ao Ko a := by
  rcases mem_mixedEdges.mp hedge with ⟨haHost, hbSource, hconflict⟩
  have haHostData := Analytic.mem_regularOddHost.mp haHost
  have hbSourceData := Analytic.mem_regularSource.mp hbSource
  have haBounds :=
    mem_upto.mp
      (Analytic.regularOddHost_subset_upto L Ao Ko N haHost)
  have haodd : Odd a :=
    Analytic.odd_of_mem_regularOddHost haHost
  have hbodd : Odd b :=
    Analytic.odd_of_rough (by omega : 2 < L) hbSourceData.2.2.1
  have hapos : 0 < a := by omega
  have hbpos : 0 < b := by omega
  rcases (conflictOne_mixed_iff_exists_coordinates
      hapos hbpos haodd).mp hconflict with
    ⟨t, u, w, hcop, hatuw, hbtuw⟩
  have ht : 0 < t := by
    by_contra h
    have : t = 0 := Nat.eq_zero_of_not_pos h
    rw [hatuw, this, zero_mul] at hapos
    omega
  have hu : 0 < u := by
    by_contra h
    have : u = 0 := Nat.eq_zero_of_not_pos h
    rw [hbtuw, this, mul_zero] at hbpos
    omega
  have hw : 0 < w := by
    by_contra h
    have : w = 0 := Nat.eq_zero_of_not_pos h
    rw [hatuw, this, mul_zero] at hapos
    omega
  have hx : 0 < 2 * u + w := by omega
  have huB : u ≤ b := by
    rw [hbtuw]
    have htx : 0 < t * (2 * u + w) := Nat.mul_pos ht hx
    calc
      u ≤ (t * (2 * u + w)) * u :=
        Nat.le_mul_of_pos_left u htx
      _ = t * u * (2 * u + w) := by ring
  have huN : u ≤ N := huB.trans hbSourceData.2.1
  have hNle3b : N ≤ 3 * b := by
    have hbLower := hbSourceData.1
    omega
  have ha6b : a ≤ 6 * b := by
    have ha2N := haBounds.2
    omega
  have htw_le : t * (2 * u + w) * w ≤
      t * (2 * u + w) * (6 * u) := by
    calc
      t * (2 * u + w) * w =
          t * w * (2 * u + w) := by ring
      _ = a := hatuw.symm
      _ ≤ 6 * b := ha6b
      _ = t * (2 * u + w) * (6 * u) := by rw [hbtuw]; ring
  have hscale : 0 < t * (2 * u + w) := Nat.mul_pos ht hx
  have hw6u : w ≤ 6 * u :=
    le_of_mul_le_mul_left htw_le (by exact_mod_cast hscale)
  have hx8u : 2 * u + w ≤ 8 * u := by omega
  have hroughFactor
      {r : ℕ} (hr : r ∣ b) : Analytic.Rough L r := by
    intro p hp hpL hpr
    exact hbSourceData.2.2.1 p hp hpL (hpr.trans hr)
  have htDvd : t ∣ b := by
    rw [hbtuw]
    simpa [mul_assoc] using dvd_mul_right t (u * (2 * u + w))
  have huDvd : u ∣ b := by
    rw [hbtuw]
    exact ⟨t * (2 * u + w), by ring⟩
  have hxDvd : 2 * u + w ∣ b := by
    rw [hbtuw]
    exact dvd_mul_left (2 * u + w) (t * u)
  have htRough := hroughFactor htDvd
  have huRough := hroughFactor huDvd
  have hxRough := hroughFactor hxDvd
  have htbuxOdd : Odd (t * u * (2 * u + w)) := by
    simpa [hbtuw] using hbodd
  have htbuxOdd' : Odd (t * (u * (2 * u + w))) := by
    simpa [mul_assoc] using htbuxOdd
  have htOdd : Odd t := Nat.Odd.of_mul_left htbuxOdd'
  have huxOdd : Odd (u * (2 * u + w)) :=
    Nat.Odd.of_mul_right htbuxOdd'
  have huOdd : Odd u := Nat.Odd.of_mul_left huxOdd
  have hxOdd : Odd (2 * u + w) := Nat.Odd.of_mul_right huxOdd
  have hwOdd : Odd w := by
    have : Odd (t * w * (2 * u + w)) := by
      simpa [hatuw] using haodd
    have this' : Odd (t * (w * (2 * u + w))) := by
      simpa [mul_assoc] using this
    have htwx : Odd (w * (2 * u + w)) :=
      Nat.Odd.of_mul_right this'
    exact Nat.Odd.of_mul_left htwx
  exact ⟨t, u, w, ht, hu, hw, hcop, hatuw, hbtuw,
    huN, hw6u, hx8u, htRough, huRough, hxRough,
    htOdd, huOdd, hwOdd, hxOdd, hbSourceData.2.2.2,
    haHostData.2⟩

end Erdos327
