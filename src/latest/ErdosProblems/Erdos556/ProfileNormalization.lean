import ErdosProblems.Erdos556.ProfileEnergyBound
import ErdosProblems.Erdos556.ProfileEdgeCap
import ErdosProblems.Erdos556.ApproxCubeWeights

/-! Normalized profile weights, with explicit error hypotheses. -/

namespace Erdos556

open SimpleGraph Finset

theorem cubeDisjointMass_div (w : CubeProfile → ℝ) (n : ℝ) :
    cubeDisjointMass (fun p => w p / n) = cubeDisjointMass w / n ^ 2 := by
  unfold cubeDisjointMass
  simp only [sum_div]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp [div_mul_div_comm, pow_two]

theorem cubeEnergy_div_identity (w : CubeProfile → ℝ) (n : ℝ) (hn : n ≠ 0) :
    cubeEnergy (fun p => w p / n) * n ^ 2 =
      (∑ p, w p) ^ 2 - cubeDisjointMass w - n * (∑ p, (profileDimension p : ℝ) * w p) := by
  rw [cubeEnergy_disjoint_identity, cubeDisjointMass_div, ← sum_div]
  have hsum : (∑ p, (profileDimension p : ℝ) * (w p / n)) =
      (∑ p, (profileDimension p : ℝ) * w p) / n := by
    simp only [sum_div, mul_div_assoc]
  rw [hsum]
  field_simp

noncomputable def ThreeColourDecomposition.profileWeight {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D)
    (n : ℝ) (p : CubeProfile) : ℝ := (h.profileClass p).card / n

theorem ThreeColourDecomposition.sum_profileWeight {V : Type*} [Fintype V] [DecidableEq V]
    {c : ThreeColouring V} {E D : ℝ} (h : ThreeColourDecomposition c E D) (n : ℝ) :
    (∑ p, h.profileWeight n p) = Fintype.card V / n := by
  unfold profileWeight
  rw [← sum_div]
  congr 1
  exact_mod_cast h.sum_profileClass_card

theorem ThreeColourDecomposition.profileWeight_energy_identity {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) (n : ℝ) (hn : n ≠ 0) :
    cubeEnergy (h.profileWeight n) * n ^ 2 = (Fintype.card V : ℝ) ^ 2 -
      cubeDisjointMass (fun p => ((h.profileClass p).card : ℝ)) -
      n * (∑ p, (profileDimension p : ℝ) * (h.profileClass p).card) := by
  unfold profileWeight
  rw [cubeEnergy_div_identity _ n hn]
  have hs : (∑ p, ((h.profileClass p).card : ℝ)) = Fintype.card V := by
    exact_mod_cast h.sum_profileClass_card
  rw [hs]

theorem ThreeColourDecomposition.approximate_profileWeight {V : Type*}
    [Fintype V] [DecidableEq V] {c : ThreeColouring V} {E D : ℝ}
    (h : ThreeColourDecomposition c E D) (n : ℕ) (hn : 8 ≤ n)
    (hno : ∀ i, ¬ cycleGraph n ⊑ c.graph i) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsize : |(Fintype.card V : ℝ) - 4 * n| ≤ δ * n)
    (hvertex : 6 * E + Fintype.card V ≤ δ ^ 2 * (n : ℝ) ^ 2)
    (hedge : 48 * E ≤ δ * (n : ℝ) ^ 2)
    (hpair : 6 * E + Fintype.card V ≤ δ * (n : ℝ) ^ 2)
    (henergy : (Fintype.card V : ℝ) + (2 * D - n) *
        (∑ p, (profileDimension p : ℝ) * (h.profileClass p).card) + 6 * E ≤ δ * (n : ℝ) ^ 2) :
    ApproxCubeWeight (h.profileWeight n) δ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnsq : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact div_nonneg (Nat.cast_nonneg _) hnpos.le
  · rw [h.sum_profileWeight]
    have hid : (Fintype.card V : ℝ) / n - 4 = (Fintype.card V - 4 * n) / n := by
      field_simp
    rw [hid, abs_div, abs_of_pos hnpos]
    exact (div_le_iff₀ hnpos).mpr hsize
  · intro p hp
    apply (div_le_iff₀ hnpos).mpr
    have hb := (h.vertex_profile_square_bound p hp).trans hvertex
    have hm : (0 : ℝ) ≤ (h.profileClass p).card := by positivity
    have hdn := mul_nonneg hδ hnpos.le
    nlinarith
  · intro p hp
    apply (div_le_iff₀ hnpos).mpr
    have hb := h.edge_profile_size_bound n hn hno p hp
    nlinarith
  · intro p q hpq
    dsimp only [profileWeight]
    rw [div_mul_div_comm, ← pow_two]
    apply (div_le_iff₀ hnsq).mpr
    exact (h.incompatible_profile_product_bound p q hpq).trans hpair
  · have he := h.profileWeight_energy_identity n hnpos.ne'
    have hb := (h.raw_profile_energy_bound n).trans henergy
    nlinarith

#print axioms ThreeColourDecomposition.approximate_profileWeight

end Erdos556
