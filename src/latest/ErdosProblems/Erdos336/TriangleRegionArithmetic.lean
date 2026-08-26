import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Arithmetic for lattice-triangle exclusion regions
-/

namespace Erdos336

/-- Number of lattice points in the inward triangle cut out by a boundary
segment of coordinate span `d`, when the anisotropy is `V`. -/
def triangleRegionCount (V d : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (d / V), (d - V * (k + 1) + 1)

private lemma two_mul_triangleLayerSum
    (V d q : ℕ) (hq : V * q ≤ d) :
    2 * (∑ k ∈ Finset.range q, (d - V * (k + 1) + 1)) =
      q * (2 * (d + 1) - V * (q + 1)) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hq' : V * q ≤ d := by nlinarith
      have hterm : V * (q + 1) ≤ d := by simpa using hq
      rw [Finset.sum_range_succ, Nat.mul_add, ih hq']
      have hVle : V ≤ d := by
        calc
          V = V * 1 := by omega
          _ ≤ V * (q + 1) := Nat.mul_le_mul_left V (by omega)
          _ ≤ d := hterm
      have hb₁ : V * (q + 1) ≤ 2 * (d + 1) := by nlinarith
      have hb₂ : V * (q + 1 + 1) ≤ 2 * (d + 1) := by nlinarith
      apply Nat.cast_injective (R := ℤ)
      push_cast [Nat.cast_sub hb₁, Nat.cast_sub hterm, Nat.cast_sub hb₂]
      ring

/-- Exact doubled cardinal formula for the inward triangle. -/
theorem two_mul_triangleRegionCount (V d : ℕ) (hV : 0 < V) :
    2 * triangleRegionCount V d =
      (d / V) * (2 * (d + 1) - V * (d / V + 1)) := by
  apply two_mul_triangleLayerSum
  exact Nat.mul_div_le d V

/-- The inward region has the sharp quadratic leading term, with only linear
boundary error: `d² ≤ 2VR + Vd`. -/
theorem triangleRegionCount_quadratic (V d : ℕ) (hV : 0 < V) :
    d ^ 2 ≤ 2 * V * triangleRegionCount V d + V * d := by
  let q := d / V
  let r := d % V
  have hdecomp : d = V * q + r := by
    exact (Nat.div_add_mod d V).symm
  have hr : r < V := by
    exact Nat.mod_lt d hV
  have hcount := two_mul_triangleRegionCount V d hV
  change 2 * triangleRegionCount V d =
    q * (2 * (d + 1) - V * (q + 1)) at hcount
  have hq : V * q ≤ d := by
    dsimp [q]
    exact Nat.mul_div_le d V
  by_cases hqzero : q = 0
  · have hdr : d = r := by simpa [hqzero] using hdecomp
    have hdV : d ≤ V := by omega
    have hsq : d * d ≤ V * d := Nat.mul_le_mul_right d hdV
    nlinarith
  have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hqzero
  have hVd : V ≤ d := by
    calc
      V = V * 1 := by omega
      _ ≤ V * q := Nat.mul_le_mul_left V hqpos
      _ ≤ d := hq
  have hsub : V * (q + 1) ≤ 2 * (d + 1) := by
    nlinarith
  have hcountSub :
      2 * triangleRegionCount V d =
        q * (2 * (d + 1)) - q * (V * (q + 1)) := by
    simpa only [Nat.mul_sub_left_distrib] using hcount
  have hmul : q * (V * (q + 1)) ≤ q * (2 * (d + 1)) :=
    Nat.mul_le_mul_left q hsub
  have hcountAdd :
      q * (2 * (d + 1)) =
        2 * triangleRegionCount V d + q * (V * (q + 1)) :=
    (Nat.sub_eq_iff_eq_add hmul).mp hcountSub.symm
  nlinarith

/-- Three boundary segments with total coordinate span `D` have enough
quadratic mass; this is the Cauchy--Schwarz part of the triangle-covering
argument. -/
theorem three_region_quadratic
    (V d₁ d₂ d₃ : ℕ) (hV : 0 < V) :
    (d₁ + d₂ + d₃) ^ 2 ≤
      6 * V * (triangleRegionCount V d₁ +
        triangleRegionCount V d₂ + triangleRegionCount V d₃) +
      3 * V * (d₁ + d₂ + d₃) := by
  have h1 := triangleRegionCount_quadratic V d₁ hV
  have h2 := triangleRegionCount_quadratic V d₂ hV
  have h3 := triangleRegionCount_quadratic V d₃ hV
  have hcs : (d₁ + d₂ + d₃) ^ 2 ≤ 3 * (d₁ ^ 2 + d₂ ^ 2 + d₃ ^ 2) := by
    nlinarith [two_mul_le_add_sq d₁ d₂, two_mul_le_add_sq d₁ d₃,
      two_mul_le_add_sq d₂ d₃]
  nlinarith

end Erdos336
