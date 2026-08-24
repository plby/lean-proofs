import ErdosProblems.Erdos587.NearbyMean

/-!
# Choosing the reciprocal Fourier block width

The rounded width `floor(R*L/v)+1` has the required sampling scale.
Simple global inequalities imply the reciprocal-counting hypotheses uniformly
over every gcd class and dyadic denominator block.
-/

namespace Erdos587

noncomputable def nearbyBlockWidth (R v : ℕ) (L : ℝ) : ℕ :=
  ⌊(R : ℝ) * L / v⌋₊ + 1

lemma nearbyBlockWidth_bounds (R v : ℕ) {L : ℝ} (hv : 0 < v) (hL : 0 < L)
    (hwidth : 2 ≤ (R : ℝ) * L / v) :
    3 ≤ nearbyBlockWidth R v L ∧
      (R : ℝ) * L / v ≤ nearbyBlockWidth R v L ∧
      (nearbyBlockWidth R v L : ℝ) * v ≤ 2 * R * L := by
  let X := (R : ℝ) * L / v
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hlo : 2 ≤ ⌊X⌋₊ := (Nat.le_floor_iff hX).mpr hwidth
  have hfloor := Nat.floor_le hX
  have hupper : (nearbyBlockWidth R v L : ℝ) ≤ 2 * X := by
    dsimp [nearbyBlockWidth]
    push_cast
    change (⌊X⌋₊ : ℝ) + 1 ≤ 2 * X
    linarith
  refine ⟨by dsimp [nearbyBlockWidth]; change 3 ≤ ⌊X⌋₊ + 1; omega, ?_, ?_⟩
  · simpa only [nearbyBlockWidth, X, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one X).le
  · have hh := mul_le_mul_of_nonneg_right hupper hvR.le
    have heq : (2 * X) * v = 2 * R * L := by dsimp [X]; field_simp
    simpa only [heq] using hh

lemma nearbyBlockWidth_profile_scale {R r v : ℕ} {L : ℝ}
    (hR : 0 < R) (hv : 0 < v) (hL : 0 < L) (hwidth : 2 ≤ (R : ℝ) * L / v)
    (hRr : R ≤ r) (hrR : r ≤ 2 * R) :
    1 / 2 ≤ ((v : ℝ) / (r * L)) * nearbyBlockWidth R v L ∧
      ((v : ℝ) / (r * L)) * nearbyBlockWidth R v L ≤ 2 := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hR.trans_le hRr
  have hRr' : (R : ℝ) ≤ r := by exact_mod_cast hRr
  have hrR' : (r : ℝ) ≤ 2 * R := by exact_mod_cast hrR
  obtain ⟨hK, hlo, hhi⟩ := nearbyBlockWidth_bounds R v hv hL hwidth
  have hlow : (R : ℝ) * L ≤ (nearbyBlockWidth R v L : ℝ) * v := by
    have hh := mul_le_mul_of_nonneg_right hlo hvR.le
    simpa only [div_mul_cancel₀ _ hvR.ne'] using hh
  have heq : ((v : ℝ) / (r * L)) * nearbyBlockWidth R v L =
      ((nearbyBlockWidth R v L : ℝ) * v) / (r * L) := by ring
  rw [heq]
  constructor
  · apply (le_div_iff₀ (mul_pos hrpos hL)).mpr
    have hrr := mul_le_mul_of_nonneg_right hrR' hL.le
    nlinarith
  · apply (div_le_iff₀ (mul_pos hrpos hL)).mpr
    have hrr := mul_le_mul_of_nonneg_right hRr' hL.le
    nlinarith

theorem nearbyBlockWidth_global_conditions (j u v M Y d q R : ℕ) {L : ℝ}
    (hd : 0 < d) (hq : 0 < q) (hv : 0 < v) (hY : 1 ≤ Y) (hL : 0 < L)
    (hdq : d * q = u) (hdR : d * R ≤ M)
    (hwidth : 2 ≤ (R : ℝ) * L / v)
    (hYv : 4 * (Y : ℝ) * L ≤ v) (hglobal : 64 * (M : ℝ) * L ≤ u * v)
    (hsize : 64 * ((u + v) * M + 1) ≤ Y ^ (4 ^ j)) :
    let K := nearbyBlockWidth R v L
    3 ≤ K ∧ K ≤ R ∧ 16 * K < q ∧
      64 * (q * R + v * K + 1) ≤ (R / K) ^ (4 ^ j) ∧
      (K : ℝ) * v ≤ 4 * R * L := by
  dsimp only
  let K := nearbyBlockWidth R v L
  obtain ⟨hK, hlow, hKv⟩ := nearbyBlockWidth_bounds R v hv hL hwidth
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hvreal : 0 < (v : ℝ) := by exact_mod_cast hv
  have hdqreal : (d : ℝ) * q = u := by exact_mod_cast hdq
  have hdRreal : (d : ℝ) * R ≤ M := by exact_mod_cast hdR
  have htwoY : 2 * (Y : ℝ) * L ≤ v := by
    have hYL : 0 ≤ (Y : ℝ) * L := by positivity
    linarith
  have hYKreal : (Y : ℝ) * K ≤ R := by
    apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2 * L)).mp
    calc
      ((Y : ℝ) * K) * (2 * L) = (2 * (Y : ℝ) * L) * K := by ring
      _ ≤ (v : ℝ) * K := mul_le_mul_of_nonneg_right htwoY (Nat.cast_nonneg K)
      _ = (K : ℝ) * v := mul_comm _ _
      _ ≤ 2 * R * L := hKv
      _ = (R : ℝ) * (2 * L) := by ring
  have hYK : Y * K ≤ R := by exact_mod_cast hYKreal
  have hKR : K ≤ R := (by nlinarith : K ≤ Y * K).trans hYK
  have hratio : Y ≤ R / K := (Nat.le_div_iff_mul_le (by omega : 0 < K)).mpr hYK
  have hprod : (32 * (K : ℝ)) * ((d : ℝ) * v) ≤ (q : ℝ) * ((d : ℝ) * v) := by
    calc
      _ = (32 * (d : ℝ)) * ((K : ℝ) * v) := by ring
      _ ≤ (32 * (d : ℝ)) * (2 * R * L) :=
        mul_le_mul_of_nonneg_left hKv (by positivity)
      _ = (64 * L) * ((d : ℝ) * R) := by ring
      _ ≤ (64 * L) * M := mul_le_mul_of_nonneg_left hdRreal (by positivity)
      _ = 64 * (M : ℝ) * L := by ring
      _ ≤ (u : ℝ) * v := hglobal
      _ = (q : ℝ) * ((d : ℝ) * v) := by rw [← hdqreal]; ring
  have h32real : 32 * (K : ℝ) ≤ q :=
    (mul_le_mul_iff_left₀ (mul_pos hdreal hvreal)).mp hprod
  have h32 : 32 * K ≤ q := by exact_mod_cast h32real
  have h16 : 16 * K < q := by omega
  have hRM : R ≤ M := by
    calc
      R = 1 * R := by omega
      _ ≤ d * R := Nat.mul_le_mul_right R (by omega : 1 ≤ d)
      _ ≤ M := hdR
  have hqu : q ≤ u := by
    calc
      q = 1 * q := by omega
      _ ≤ d * q := Nat.mul_le_mul_right q (by omega : 1 ≤ d)
      _ = u := hdq
  have hnum : q * R + v * K + 1 ≤ (u + v) * M + 1 := by
    have h₁ := Nat.mul_le_mul hqu hRM
    have h₂ := Nat.mul_le_mul_left v (hKR.trans hRM)
    nlinarith
  refine ⟨hK, hKR, h16, ?_, ?_⟩
  · exact (Nat.mul_le_mul_left 64 hnum).trans (hsize.trans (Nat.pow_le_pow_left hratio (4 ^ j)))
  · have hRL : 0 ≤ (R : ℝ) * L := by positivity
    linarith

end Erdos587
