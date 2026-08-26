import ErdosProblems.Erdos19.Core

/-! # Integer parameters for coloring with a small global coverage bound -/

namespace Erdos19

theorem capacity_load_mul_le (n D d c : ℕ) (hD : 0 < D) (hd : c * d ≤ D) :
    c * (n * d / D) ≤ n := by
  have hdiv := Nat.mul_div_le (n * d) D
  have hdiv' := Nat.mul_le_mul_left c hdiv
  have hbound := Nat.mul_le_mul_left n hd
  apply Nat.le_of_mul_le_mul_left (c := D) _ hD
  nlinarith only [hdiv', hbound]

theorem fractional_degree_load (n s a : ℕ) (hs : 0 < s) (ha : 0 < a)
    (hD : 0 < n / s) :
    16 * (n * (n / (16 * a * s)) / (n / s)) ≤ n / a := by
  have hdegree : (16 * a) * (n / (16 * a * s)) ≤ n / s := by
    apply (Nat.le_div_iff_mul_le hs).mpr
    have h := Nat.mul_div_le n (16 * a * s)
    nlinarith only [h]
  have hload := capacity_load_mul_le n (n / s) (n / (16 * a * s)) (16 * a) hD hdegree
  apply (Nat.le_div_iff_mul_le ha).mpr
  nlinarith only [hload]

theorem exists_codegree_parameter (delta : ℝ) (hdelta : 0 < delta) :
    ∃ M D₁ : ℕ, ∀ D : ℕ, D₁ ≤ D → 0 < D →
      ∃ L : ℕ, 0 < L ∧ (L : ℝ) < delta * D ∧ D ≤ L * M := by
  obtain ⟨M, hM⟩ := exists_nat_ge (4 / delta)
  refine ⟨M, M, ?_⟩
  intro D hD₁ hD
  have hdeltaD : 4 ≤ delta * (D : ℝ) := by
    have hratio : 4 / delta ≤ (D : ℝ) := hM.trans (by exact_mod_cast hD₁)
    have h := (div_le_iff₀ hdelta).mp hratio
    nlinarith only [h]
  let L := ⌊delta * (D : ℝ) / 2⌋₊
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hLhi : (L : ℝ) ≤ delta * D / 2 := Nat.floor_le (by positivity)
  have hLfloor : delta * (D : ℝ) / 2 < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLlo : delta * (D : ℝ) / 4 ≤ (L : ℝ) := by nlinarith only [hLfloor, hdeltaD]
  have hL : 0 < L := by
    have hpos : (0 : ℝ) < L := by nlinarith only [hLlo, hdeltaD]
    exact_mod_cast hpos
  have hLsmall : (L : ℝ) < delta * D := by
    nlinarith only [hLhi, hdeltaD]
  have hMdelta : 4 ≤ delta * (M : ℝ) := by
    have h := (div_le_iff₀ hdelta).mp hM
    nlinarith only [h]
  have hprod := mul_le_mul_of_nonneg_left hLlo (Nat.cast_nonneg M)
  have hprod' := mul_le_mul_of_nonneg_right hMdelta hDreal.le
  have hDM : (D : ℝ) ≤ L * M := by nlinarith only [hprod, hprod']
  exact ⟨L, hL, hLsmall, by exact_mod_cast hDM⟩

theorem capacity_pool_room (n s a r D L M : ℕ)
    (hs : 0 < s) (ha : 0 < a) (hD : D = n / s) (hDpos : 0 < D)
    (hDM : D ≤ L * M)
    (hp : 2 * (2 * r + (2 * r) * (2 * r * M)) + 2 ≤ n / a) :
    n * (n / (16 * a * s)) / D + 2 * r + (2 * r) * ((2 * r) * D / L) < n / a := by
  have hload := fractional_degree_load n s a hs ha (hD ▸ hDpos)
  rw [← hD] at hload
  have hdiv : (2 * r) * D / L ≤ 2 * r * M := by
    apply Nat.div_le_of_le_mul
    have h := Nat.mul_le_mul_left (2 * r) hDM
    nlinarith only [h]
  have hterm := Nat.mul_le_mul_left (2 * r) hdiv
  omega

#print axioms capacity_pool_room
#print axioms exists_codegree_parameter

end Erdos19
