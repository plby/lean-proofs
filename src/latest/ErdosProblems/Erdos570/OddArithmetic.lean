/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-! # Discrete arithmetic for the strengthened odd-cycle induction -/

namespace Erdos570

/-- The square-root function grows by at most the change in its argument. -/
theorem sqrt_le_sqrt_add_sub {x m : ℕ} (hxm : x ≤ m) :
    Nat.sqrt m ≤ Nat.sqrt x + (m - x) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxm
  simp only [Nat.add_sub_cancel_left]
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        Nat.sqrt (x + d.succ) = Nat.sqrt ((x + d).succ) := by
          congr 1 <;> omega
        _ ≤ (Nat.sqrt (x + d)).succ := Nat.sqrt_succ_le_succ_sqrt _
        _ ≤ Nat.sqrt x + d.succ := by omega

/-- Removing at least two units changes a floor square root by at most one
less than the amount removed. -/
theorem sqrt_le_sqrt_sub_add_pred {m x : ℕ} (hx : 2 ≤ x) (hxm : x ≤ m) :
    Nat.sqrt m ≤ Nat.sqrt (m - x) + (x - 1) := by
  have hdecomp : m - x + x = m := Nat.sub_add_cancel hxm
  have hs := Nat.lt_succ_sqrt (m - x)
  have hsq : m < (Nat.sqrt (m - x) + x) * (Nat.sqrt (m - x) + x) := by
    nlinarith
  have hlt : Nat.sqrt m < Nat.sqrt (m - x) + (x - 1) + 1 := by
    apply Nat.sqrt_lt.mpr
    have heq : Nat.sqrt (m - x) + (x - 1) + 1 =
        Nat.sqrt (m - x) + x := by omega
    rw [heq]
    exact hsq
  omega

/-- Removing at least three units changes a floor square root by at most two
less than the amount removed.  The extra unit over
`sqrt_le_sqrt_sub_add_pred` is exactly the room needed by the exceptional
`C₄` vertex-deletion argument. -/
theorem sqrt_le_sqrt_sub_add_pred_pred {m x : ℕ} (hx : 3 ≤ x)
    (hxm : x ≤ m) :
    Nat.sqrt m ≤ Nat.sqrt (m - x) + (x - 2) := by
  have hdecomp : m - x + x = m := Nat.sub_add_cancel hxm
  have hs := Nat.lt_succ_sqrt (m - x)
  have hxone : x - 1 + 1 = x := by omega
  have hxtwo : x - 2 + 2 = x := by omega
  have hsq : m <
      (Nat.sqrt (m - x) + (x - 1)) *
        (Nat.sqrt (m - x) + (x - 1)) := by
    have haux :
        (Nat.sqrt (m - x) + 1) * (Nat.sqrt (m - x) + 1) + x ≤
          (Nat.sqrt (m - x) + (x - 1)) *
            (Nat.sqrt (m - x) + (x - 1)) := by
      nlinarith
    nlinarith
  have hlt : Nat.sqrt m < Nat.sqrt (m - x) + (x - 2) + 1 := by
    apply Nat.sqrt_lt.mpr
    have heq : Nat.sqrt (m - x) + (x - 2) + 1 =
        Nat.sqrt (m - x) + (x - 1) := by omega
    rw [heq]
    exact hsq
  omega

/-- The natural-number budget used by the Lean strengthened statement. -/
def oddBudget (B s m : ℕ) : ℕ :=
  2 * m + max (B - Nat.sqrt m) s

/-- The correction term can rise by at most `x-1` after deleting `x≥2`
edges. -/
theorem oddCorrection_sub_le {B s m x : ℕ} (hx : 2 ≤ x) (hxm : x ≤ m) :
    max (B - Nat.sqrt (m - x)) s ≤
      max (B - Nat.sqrt m) s + (x - 1) := by
  have hsqrt := sqrt_le_sqrt_sub_add_pred hx hxm
  simp only [max_def]
  split <;> split <;> omega

/-- For a deletion of at least three edges, the correction rises by at most
`x-2`. -/
theorem oddCorrection_sub_le_pred_pred {B s m x : ℕ} (hx : 3 ≤ x)
    (hxm : x ≤ m) :
    max (B - Nat.sqrt (m - x)) s ≤
      max (B - Nat.sqrt m) s + (x - 2) := by
  have hsqrt := sqrt_le_sqrt_sub_add_pred_pred hx hxm
  simp only [max_def]
  split <;> split <;> omega

/-- A deletion of `x ≥ 3` edges leaves enough of the strengthened budget
after reserving `x+2` host vertices. -/
theorem oddBudget_sub_add_two_more_le
    {B s m x : ℕ} (hx : 3 ≤ x) (hxm : x ≤ m) :
    oddBudget B s (m - x) + (x + 2) ≤ oddBudget B s m := by
  have hcorr := oddCorrection_sub_le_pred_pred (B := B) (s := s) hx hxm
  unfold oddBudget
  omega

/-- After reserving at most `x+1` vertices for a connected `x`-edge
component, the strengthened budget still contains the budget for the
remaining `m-x` edges. -/
theorem oddBudget_sub_add_component_order_le
    {B s m x c : ℕ} (hx : 2 ≤ x) (hxm : x ≤ m) (hc : c ≤ x + 1) :
    oddBudget B s (m - x) + c ≤ oddBudget B s m := by
  have hcorr := oddCorrection_sub_le (B := B) (s := s) hx hxm
  unfold oddBudget
  omega

/-- The strengthened budget is monotone in the edge count. -/
theorem oddBudget_mono {B s x m : ℕ} (hxm : x ≤ m) :
    oddBudget B s x ≤ oddBudget B s m := by
  have hsqrt := sqrt_le_sqrt_add_sub hxm
  unfold oddBudget
  simp only [max_def]
  split <;> split <;> omega

/-- Division-free form of the minimum-degree/pigeonhole calculation which
forces the large first red neighborhood in the middle-density case. -/
theorem large_degree_of_pigeonhole
    {D k q n m delta u N : ℕ}
    (hD : 2 ≤ D) (hdelta : 0 < delta) (hnm : n ≤ m)
    (hlarge : 2 * D * (k * q) ≤ n)
    (hdensity : D * n ≤ (D - 1) * m)
    (hdegree : n * delta ≤ 2 * m)
    (hhost : 2 * m ≤ N)
    (hpigeon : N - (n - 1) ≤ delta * u) :
    n / 2 + k * q ≤ u := by
  by_cases hnzero : n = 0
  · have hz : 2 * D * (k * q) = 0 := by omega
    have hkq : k * q = 0 := by
      rcases Nat.mul_eq_zero.mp hz with hzero | hzero
      · have : 0 < 2 * D := Nat.mul_pos (by omega) (by omega)
        exact (this.ne' hzero).elim
      · exact hzero
    simp [hnzero, hkq]
  have hn2m : n - 1 ≤ 2 * m := by omega
  have hlower : 2 * m - (n - 1) ≤ delta * u := by
    exact (Nat.sub_le_sub_right hhost (n - 1)).trans hpigeon
  have hlower' : 2 * m - n + 1 ≤ delta * u := by
    convert hlower using 1 <;> omega
  have hdecomp : m - n + n = m := Nat.sub_add_cancel hnm
  have hgap : m ≤ D * (m - n) := by
    have hDpred : D - 1 + 1 = D := Nat.sub_add_cancel (by omega)
    nlinarith
  by_contra hu
  have hu' : 2 * u < n + 2 * (k * q) := by omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
  have hmulLower := Nat.mul_le_mul_left (2 * n) hlower'
  have hmulUpper := Nat.mul_lt_mul_of_pos_left hu'
    (Nat.mul_pos hnpos hdelta)
  have hmulDegree := Nat.mul_le_mul_right (n + 2 * (k * q)) hdegree
  have hchain : 2 * n * (2 * m - n + 1) <
      2 * m * (n + 2 * (k * q)) := by
    calc
      2 * n * (2 * m - n + 1) ≤ 2 * n * (delta * u) := hmulLower
      _ = n * delta * (2 * u) := by ring
      _ < n * delta * (n + 2 * (k * q)) := hmulUpper
      _ ≤ 2 * m * (n + 2 * (k * q)) := hmulDegree
  have hkey : n * (m - n) < 2 * m * (k * q) := by
    have hrewrite : 2 * m - n + 1 = 2 * (m - n) + n + 1 := by omega
    rw [hrewrite] at hchain
    nlinarith [hchain]
  have hlargeMul := Nat.mul_le_mul_right (m - n) hlarge
  have hgapMul := Nat.mul_le_mul_left (2 * (k * q)) hgap
  have hcontra : 2 * m * (k * q) ≤ n * (m - n) := by
    calc
      2 * m * (k * q) = 2 * (k * q) * m := by ring
      _ ≤ 2 * (k * q) * (D * (m - n)) := hgapMul
      _ = (2 * D * (k * q)) * (m - n) := by ring
      _ ≤ n * (m - n) := hlargeMul
  exact (Nat.not_lt_of_ge hcontra hkey).elim

end Erdos570
