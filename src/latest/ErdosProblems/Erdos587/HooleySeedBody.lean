import ErdosProblems.Erdos587.HooleyOneSidedCenter
import ErdosProblems.Erdos587.HooleyBodyDilate
import ErdosProblems.Erdos587.HooleyZonotopeMap

/-! # A centered zonotope with a rectangular seed cushion -/

open scoped BigOperators Pointwise

namespace Erdos587.GeneralizedAP

noncomputable def deltaSeedBody {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (R : Fin d → ℝ) : Set (Fin d → ℝ) :=
  CFP.deltaZonotope (fun i => intCastVec (v i)) + Set.Icc (-R) R

lemma deltaSeedBody_zero {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (R : Fin d → ℝ) (hR : ∀ i, 0 ≤ R i) :
    (0 : Fin d → ℝ) ∈ deltaSeedBody v R := by
  have hbox : (0 : Fin d → ℝ) ∈ Set.Icc (-R) R := by
    constructor <;> intro i
    · exact neg_nonpos.mpr (hR i)
    · exact hR i
  exact Set.mem_add.mpr ⟨0, CFP.deltaZonotope_zero _, 0, hbox, add_zero _⟩

lemma deltaSeedBody_compact {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (R : Fin d → ℝ) : IsCompact (deltaSeedBody v R) :=
  (CFP.deltaZonotope_compact _).add isCompact_Icc

lemma deltaSeedBody_convex {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (R : Fin d → ℝ) : Convex ℝ (deltaSeedBody v R) :=
  (CFP.deltaZonotope_convex _).add (convex_Icc _ _)

lemma deltaSeedBody_neg {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (R : Fin d → ℝ) :
    ∀ x ∈ deltaSeedBody v R, -x ∈ deltaSeedBody v R := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
  refine Set.mem_add.mpr ⟨-y, CFP.deltaZonotope_neg _ y hy, -z, ?_, by abel⟩
  constructor <;> intro i
  · have hh := hz.2 i
    change -(R i) ≤ -(z i)
    linarith
  · have hh := hz.1 i
    change -(z i) ≤ R i
    change -(R i) ≤ z i at hh
    linarith

lemma deltaSeedBody_box {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (R : Fin d → ℝ) : Set.Icc (-R) R ⊆ deltaSeedBody v R := by
  intro x hx
  exact Set.mem_add.mpr ⟨0, CFP.deltaZonotope_zero _, x, hx, zero_add _⟩

lemma deltaSeedBody_zonotope {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (R : Fin d → ℝ) (hR : ∀ i, 0 ≤ R i) :
    CFP.deltaZonotope (fun i => intCastVec (v i)) ⊆ deltaSeedBody v R := by
  intro x hx
  refine Set.mem_add.mpr ⟨x, hx, 0, ?_, add_zero _⟩
  constructor <;> intro i
  · exact neg_nonpos.mpr (hR i)
  · exact hR i

lemma deltaSeedBody_full {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (R : Fin d → ℝ) (hR : ∀ i, 1 ≤ R i) :
    ∀ x : Fin d → ℝ, ∃ c : ℝ, 0 < c ∧ c • x ∈ deltaSeedBody v R := by
  intro x
  let M : ℝ := ∑ i, |x i|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let c : ℝ := (1 + M)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, deltaSeedBody_box v R ?_⟩
  have habs (i : Fin d) : |c * x i| ≤ R i := by
    have hxi : |x i| ≤ M := Finset.single_le_sum (fun j _ => abs_nonneg (x j))
      (Finset.mem_univ i)
    calc
      _ = |x i| / (1 + M) := by rw [abs_mul, abs_of_pos hc]; exact inv_mul_eq_div _ _
      _ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      _ ≤ R i := hR i
  exact ⟨fun i => (abs_le.mp (habs i)).1, fun i => (abs_le.mp (habs i)).2⟩

lemma deltaSeedBody_small_cube {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (R : Fin d → ℝ)
    (hR : ∀ i, (4 : ℝ) ^ (d + 2) ≤ 2 * R i) :
    ∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
      e ∈ bodyDilate (1 / 4 ^ (d + 2)) (deltaSeedBody v R) := by
  intro e he
  refine ⟨((4 : ℝ) ^ (d + 2)) • e, deltaSeedBody_box v R ?_, ?_⟩
  · have hb (i : Fin d) : |((4 : ℝ) ^ (d + 2)) * e i| ≤ R i := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ (d + 2))]
      exact (mul_le_mul_of_nonneg_left (he i) (by positivity)).trans (by linarith [hR i])
    exact ⟨fun i => (abs_le.mp (hb i)).1, fun i => (abs_le.mp (hb i)).2⟩
  · rw [one_div, inv_smul_smul₀ (by positivity : (4 : ℝ) ^ (d + 2) ≠ 0)]

noncomputable def deltaSeedCenter {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) : Fin d → ℤ := fun j => round ((∑ i, (v i j : ℝ)) / 2)

theorem deltaSeedBody_lattice_decomposition_of_center {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (L R : Fin d → ℝ) (hL : ∀ i, 0 ≤ L i)
    (hv : ∀ i j, |(v i j : ℝ)| ≤ L j) (c z : Fin d → ℤ)
    (hc : ∀ j, |(c j : ℝ) - (∑ i, (v i j : ℝ)) / 2| ≤ (1 / 2 : ℝ))
    (hz : intCastVec (z - c) ∈ deltaSeedBody v R) :
    ∃ S : Finset ι, ∃ w : Fin d → ℤ,
      (∀ j, |(w j : ℝ)| ≤ R j + (d : ℝ) * L j + 1 / 2) ∧
      z = w + ∑ i ∈ S, v i := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_add.mp hz
  obtain ⟨θ, hθ, rfl⟩ := hx
  have hz' (j : Fin d) : |(z j : ℝ) - (c j : ℝ) -
      ∑ i, θ i * (v i j : ℝ)| ≤ R j := by
    have heq := congrFun hxy j
    simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.add_apply, intCastVec, Pi.sub_apply, Int.cast_sub] at heq
    have hdiff : (z j : ℝ) - (c j : ℝ) -
        ∑ i, θ i * (v i j : ℝ) = y j := by linarith
    rw [hdiff]
    exact abs_le.mpr ⟨hy.1 j, hy.2 j⟩
  obtain ⟨S, hS⟩ := CFP.delta_zonotope_subset_rounding_of_center v L R hL hv θ
    (fun i => ⟨hθ.1 i, hθ.2 i⟩) c z hc hz'
  refine ⟨S, z - ∑ i ∈ S, v i, ?_, by abel⟩
  intro j
  simpa only [Pi.sub_apply, Finset.sum_apply, Int.cast_sub, Int.cast_sum] using hS j

theorem deltaSeedBody_lattice_decomposition {ι : Type*} [Fintype ι] {d : ℕ}
    (v : ι → Fin d → ℤ) (L R : Fin d → ℝ) (hL : ∀ i, 0 ≤ L i)
    (hv : ∀ i j, |(v i j : ℝ)| ≤ L j) (z : Fin d → ℤ)
    (hz : intCastVec (z - deltaSeedCenter v) ∈ deltaSeedBody v R) :
    ∃ S : Finset ι, ∃ w : Fin d → ℤ,
      (∀ j, |(w j : ℝ)| ≤ R j + (d : ℝ) * L j + 1 / 2) ∧
      z = w + ∑ i ∈ S, v i := by
  apply deltaSeedBody_lattice_decomposition_of_center v L R hL hv (deltaSeedCenter v) z _ hz
  intro j
  simpa only [deltaSeedCenter, abs_sub_comm] using abs_sub_round ((∑ i, (v i j : ℝ)) / 2)

end Erdos587.GeneralizedAP
