import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A harmonic weight for the triangle-free Shearer induction

The weight is deliberately a factor `1 / 2`
below the sharp Shearer weight; in return its two required inequalities have
short elementary proofs.
-/

namespace Erdos788.AKSRoute

open Finset

universe u

/-- The weight used in the closed-neighborhood deletion induction. -/
noncomputable def shearerWeight (d : ℕ) : ℚ :=
  if d = 0 then 1 else harmonic d / (2 * (d : ℚ))

@[simp]
theorem shearerWeight_zero : shearerWeight 0 = 1 := by
  simp [shearerWeight]

theorem shearerWeight_of_pos {d : ℕ} (hd : 0 < d) :
    shearerWeight d = harmonic d / (2 * (d : ℚ)) := by
  simp [shearerWeight, hd.ne']

@[simp]
theorem shearerWeight_succ (d : ℕ) :
    shearerWeight (d + 1) = harmonic (d + 1) / (2 * ((d + 1 : ℕ) : ℚ)) := by
  exact shearerWeight_of_pos (Nat.zero_lt_succ d)

theorem harmonic_le_natCast (d : ℕ) : harmonic d ≤ (d : ℚ) := by
  rw [harmonic]
  calc
    ∑ i ∈ range d, ((i + 1 : ℕ) : ℚ)⁻¹ ≤ ∑ _i ∈ range d, (1 : ℚ) := by
      apply sum_le_sum
      intro i _hi
      exact (inv_le_one₀ (by positivity)).2 (by norm_num)
    _ = (d : ℚ) := by simp

theorem one_le_harmonic_succ (d : ℕ) : (1 : ℚ) ≤ harmonic (d + 1) := by
  induction d with
  | zero => norm_num [harmonic, Finset.sum_range_succ]
  | succ d ih =>
      rw [show d + 1 + 1 = (d + 1) + 1 by rfl, harmonic_succ]
      exact ih.trans (le_add_of_nonneg_right (by positivity))

theorem three_halves_le_harmonic {d : ℕ} (hd : 2 ≤ d) :
    (3 / 2 : ℚ) ≤ harmonic d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  clear hd
  induction k with
  | zero => norm_num [harmonic, Finset.sum_range_succ]
  | succ k ih =>
      rw [show 2 + (k + 1) = (2 + k) + 1 by omega, harmonic_succ]
      exact ih.trans (le_add_of_nonneg_right (by positivity))

/-- The local residual in the Shearer potential calculation is nonnegative.
For positive `d` it is exactly `(d - harmonic d) / (2*d)`. -/
theorem shearerWeight_residual_nonneg (d : ℕ) :
    0 ≤ 1 - ((d + 1 : ℕ) : ℚ) * shearerWeight d +
      (d : ℚ) * ((d - 1 : ℕ) : ℚ) *
        (shearerWeight (d - 1) - shearerWeight d) := by
  rcases d with (_ | d)
  · simp
  rcases d with (_ | d)
  · norm_num [shearerWeight, harmonic, Finset.sum_range_succ]
  have hdpos : 0 < d + 2 := by omega
  have hdpred : 0 < d + 2 - 1 := by omega
  rw [shearerWeight_of_pos hdpos, shearerWeight_of_pos hdpred]
  have hh : harmonic (d + 2) =
      harmonic (d + 2 - 1) + (((d + 2 : ℕ) : ℚ))⁻¹ := by
    have heq : d + 2 - 1 = d + 1 := by omega
    rw [heq]
    exact harmonic_succ (d + 1)
  have hid :
      1 - (((d + 2) + 1 : ℕ) : ℚ) *
          (harmonic (d + 2) / (2 * (((d + 2 : ℕ) : ℚ)))) +
          ((d + 2 : ℕ) : ℚ) * (((d + 2 - 1 : ℕ) : ℚ)) *
            (harmonic (d + 2 - 1) / (2 * (((d + 2 - 1 : ℕ) : ℚ))) -
              harmonic (d + 2) / (2 * (((d + 2 : ℕ) : ℚ)))) =
        (((d + 2 : ℕ) : ℚ) - harmonic (d + 2)) /
          (2 * (((d + 2 : ℕ) : ℚ))) := by
    rw [hh]
    push_cast
    field_simp
    ring
  rw [hid]
  apply div_nonneg
  · exact sub_nonneg.mpr (harmonic_le_natCast (d + 2))
  · positivity

/-- The successive drops of `shearerWeight` decrease.  This is the discrete
convexity input in the closed-neighborhood deletion proof. -/
theorem shearerWeight_drop_antitone (d : ℕ) :
    shearerWeight d - shearerWeight (d + 1) ≥
      shearerWeight (d + 1) - shearerWeight (d + 2) := by
  rcases d with (_ | d)
  · norm_num [shearerWeight, harmonic, Finset.sum_range_succ]
  let k : ℕ := d + 1
  have hk : 2 ≤ k + 1 := by omega
  have hkpos : 0 < k := by omega
  have hk1pos : 0 < k + 1 := by omega
  have hk2pos : 0 < k + 2 := by omega
  rw [show d + 1 = k by rfl, show d + 2 = k + 1 by omega]
  rw [shearerWeight_of_pos hkpos, shearerWeight_of_pos hk1pos,
    shearerWeight_of_pos hk2pos]
  have hh1 : harmonic (k + 1) = harmonic k + (((k + 1 : ℕ) : ℚ))⁻¹ :=
    harmonic_succ k
  have hh2 : harmonic (k + 2) =
      harmonic (k + 1) + (((k + 2 : ℕ) : ℚ))⁻¹ :=
    harmonic_succ (k + 1)
  have hh0 : harmonic k =
      harmonic (k + 1) - (((k + 1 : ℕ) : ℚ))⁻¹ := by
    linarith
  rw [hh0, hh2]
  have hH := three_halves_le_harmonic hk
  push_cast at hH ⊢
  field_simp
  nlinarith

theorem shearerWeight_drop_nonneg (d : ℕ) :
    0 ≤ shearerWeight d - shearerWeight (d + 1) := by
  rcases d with (_ | d)
  · norm_num [shearerWeight, harmonic, Finset.sum_range_succ]
  rw [shearerWeight_of_pos (by omega : 0 < d + 1),
    shearerWeight_of_pos (by omega : 0 < d + 2), harmonic_succ (d + 1)]
  have hH := one_le_harmonic_succ d
  push_cast at hH ⊢
  field_simp
  nlinarith

theorem shearerWeight_antitone : Antitone shearerWeight :=
  antitone_nat_of_succ_le fun d ↦ sub_nonneg.mp (shearerWeight_drop_nonneg d)

theorem shearerWeight_telescoping {d k : ℕ} (hk : k ≤ d) :
    (k : ℚ) * (shearerWeight (d - 1) - shearerWeight d) ≤
      shearerWeight (d - k) - shearerWeight d := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkd : k ≤ d := by omega
      have hpos : 0 < d - k := by omega
      have hidx : d - (k + 1) = d - k - 1 := by omega
      have hstep :
          shearerWeight (d - 1) - shearerWeight d ≤
            shearerWeight (d - k - 1) - shearerWeight (d - k) := by
        have hle : d - k - 1 ≤ d - 1 := by omega
        have hdrop : Antitone
            (fun n ↦ shearerWeight n - shearerWeight (n + 1)) :=
          antitone_nat_of_succ_le fun n ↦ by
            simpa [Nat.add_assoc] using! shearerWeight_drop_antitone n
        have hres := hdrop hle
        have h1 : d - 1 + 1 = d := by omega
        have h2 : d - k - 1 + 1 = d - k := by omega
        dsimp only at hres
        rw [h1, h2] at hres
        exact hres
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hidx]
      calc
        (k : ℚ) * (shearerWeight (d - 1) - shearerWeight d) +
            (shearerWeight (d - 1) - shearerWeight d) ≤
            (shearerWeight (d - k) - shearerWeight d) +
              (shearerWeight (d - k - 1) - shearerWeight (d - k)) :=
          add_le_add (ih hkd) hstep
        _ = shearerWeight (d - k - 1) - shearerWeight d := by ring

/-- The harmonic weight already contains the logarithmic factor needed in
the final analytic estimate. -/
theorem log_le_two_mul_nat_mul_shearerWeight {d : ℕ} (hd : 0 < d) :
    Real.log (d + 1 : ℝ) ≤
      (2 * d : ℝ) * (shearerWeight d : ℝ) := by
  rw [shearerWeight_of_pos hd]
  norm_cast
  field_simp
  exact_mod_cast log_add_one_le_harmonic d

section FiniteGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def closedNeighborFinset (x : V) : Finset V :=
  insert x (G.neighborFinset x)

def outsideClosedNeighborFinset (x : V) : Finset V :=
  Finset.univ \ closedNeighborFinset G x

def degreeOutsideClosed (x z : V) : ℕ :=
  (G.neighborFinset z \ closedNeighborFinset G x).card

@[simp]
theorem mem_closedNeighborFinset {x z : V} :
    z ∈ closedNeighborFinset G x ↔ z = x ∨ G.Adj x z := by
  simp [closedNeighborFinset]

@[simp]
theorem mem_outsideClosedNeighborFinset {x z : V} :
    z ∈ outsideClosedNeighborFinset G x ↔ z ≠ x ∧ ¬G.Adj x z := by
  simp [outsideClosedNeighborFinset]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem not_adj_endpoints_of_twoPath (htri : G.CliqueFree 3)
    {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : x ≠ z) :
    ¬G.Adj x z := by
  have hi := G.isIndepSet_neighborSet_of_triangleFree htri y
  exact hi hxy.symm hyz hxz

omit [DecidableEq V] in
/-- Swap the two ends of a sum over directed edges. -/
theorem sum_neighborFinset_swap (f : V → V → ℚ) :
    (∑ x : V, ∑ y ∈ G.neighborFinset x, f x y) =
      ∑ y : V, ∑ x ∈ G.neighborFinset y, f x y := by
  classical
  have hn (x : V) : G.neighborFinset x = Finset.univ.filter (G.Adj x) := by
    ext y
    simp
  simp_rw [hn, sum_filter]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro y _hy
  apply sum_congr rfl
  intro x _hx
  by_cases h : G.Adj x y
  · simp [h, h.symm]
  · have h' : ¬G.Adj y x := fun hyx ↦ h hyx.symm
    simp [h, h']

omit [Fintype V] in
/-- A function of the second coordinate is counted `|s|-1` times on the
ordered off-diagonal of `s`. -/
theorem sum_erase_second (s : Finset V) (f : V → ℚ) :
    (∑ x ∈ s, ∑ z ∈ s.erase x, f z) =
      ∑ z ∈ s, ((s.card - 1 : ℕ) : ℚ) * f z := by
  classical
  have he (x : V) : s.erase x = s.filter fun z ↦ z ≠ x := by
    ext z
    simp only [mem_erase, mem_filter]
    constructor <;> aesop
  calc
    (∑ x ∈ s, ∑ z ∈ s.erase x, f z) =
        ∑ x ∈ s, ∑ z ∈ s, if z ≠ x then f z else 0 := by
      simp_rw [he, sum_filter]
    _ = ∑ z ∈ s, ∑ x ∈ s, if z ≠ x then f z else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ z ∈ s, ∑ x ∈ s.erase z, f z := by
      apply sum_congr rfl
      intro z _hz
      rw [he, sum_filter]
      apply sum_congr rfl
      intro x _hx
      by_cases h : z = x
      · simp [h]
      · have h' : x ≠ z := fun hxz ↦ h hxz.symm
        simp [h, h']
    _ = ∑ z ∈ s, ((s.card - 1 : ℕ) : ℚ) * f z := by
      apply sum_congr rfl
      intro z hz
      rw [sum_const, nsmul_eq_mul, card_erase_of_mem hz]

def commonNeighborCount (x z : V) : ℕ :=
  (G.neighborFinset x ∩ G.neighborFinset z).card

noncomputable def vertexDrop (z : V) : ℚ :=
  shearerWeight (G.degree z - 1) - shearerWeight (G.degree z)

theorem degreeOutsideClosed_eq_sub_common {x z : V}
    (hz : z ∈ outsideClosedNeighborFinset G x) :
    degreeOutsideClosed G x z = G.degree z - commonNeighborCount G x z := by
  have hxz : ¬G.Adj x z := (mem_outsideClosedNeighborFinset G).mp hz |>.2
  have hxnot : x ∉ G.neighborFinset z := by
    simpa [G.adj_comm] using! hxz
  rw [degreeOutsideClosed, card_sdiff, SimpleGraph.card_neighborFinset_eq_degree,
    commonNeighborCount]
  congr 1
  apply congrArg Finset.card
  ext y
  simp [closedNeighborFinset, hxnot]

theorem commonNeighborCount_le_degree (x z : V) :
    commonNeighborCount G x z ≤ G.degree z := by
  rw [commonNeighborCount, ← SimpleGraph.card_neighborFinset_eq_degree]
  exact card_le_card inter_subset_right

theorem local_weight_change_lower {x z : V}
    (hz : z ∈ outsideClosedNeighborFinset G x) :
    (commonNeighborCount G x z : ℚ) * vertexDrop G z ≤
      shearerWeight (degreeOutsideClosed G x z) - shearerWeight (G.degree z) := by
  rw [degreeOutsideClosed_eq_sub_common G hz, vertexDrop]
  exact shearerWeight_telescoping (commonNeighborCount_le_degree G x z)

omit [DecidableEq V] in
theorem edge_pair_drop_ineq {y z : V} (hyz : G.Adj y z) :
    (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z +
        ((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G y) ≥
      (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G y +
        ((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G z) := by
  have hypos : 0 < G.degree y := hyz.degree_pos_left
  have hzpos : 0 < G.degree z := hyz.degree_pos_right
  by_cases hdeg : G.degree y ≤ G.degree z
  · have hidx : G.degree y - 1 ≤ G.degree z - 1 := by omega
    have hdrop : vertexDrop G z ≤ vertexDrop G y := by
      rw [vertexDrop, vertexDrop]
      have hanti : Antitone
          (fun n ↦ shearerWeight n - shearerWeight (n + 1)) :=
        antitone_nat_of_succ_le fun n ↦ by
          simpa [Nat.add_assoc] using! shearerWeight_drop_antitone n
      have h := hanti hidx
      have hy : G.degree y - 1 + 1 = G.degree y := by omega
      have hz : G.degree z - 1 + 1 = G.degree z := by omega
      dsimp only at h
      rw [hy, hz] at h
      exact h
    have hycast : (((G.degree y - 1 : ℕ) : ℚ)) = (G.degree y : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hzcast : (((G.degree z - 1 : ℕ) : ℚ)) = (G.degree z : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hdegq : (G.degree y : ℚ) ≤ (G.degree z : ℚ) := by exact_mod_cast hdeg
    rw [hycast, hzcast]
    nlinarith
  · have hzy : G.degree z ≤ G.degree y := by omega
    have hidx : G.degree z - 1 ≤ G.degree y - 1 := by omega
    have hdrop : vertexDrop G y ≤ vertexDrop G z := by
      rw [vertexDrop, vertexDrop]
      have hanti : Antitone
          (fun n ↦ shearerWeight n - shearerWeight (n + 1)) :=
        antitone_nat_of_succ_le fun n ↦ by
          simpa [Nat.add_assoc] using! shearerWeight_drop_antitone n
      have h := hanti hidx
      have hy : G.degree y - 1 + 1 = G.degree y := by omega
      have hz : G.degree z - 1 + 1 = G.degree z := by omega
      dsimp only at h
      rw [hy, hz] at h
      exact h
    have hycast : (((G.degree y - 1 : ℕ) : ℚ)) = (G.degree y : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hzcast : (((G.degree z - 1 : ℕ) : ℚ)) = (G.degree z : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hdegq : (G.degree z : ℚ) ≤ (G.degree y : ℚ) := by exact_mod_cast hzy
    rw [hycast, hzcast]
    nlinarith

noncomputable def pathDropSum : ℚ :=
  ∑ y : V, ∑ x ∈ G.neighborFinset y,
    ∑ z ∈ (G.neighborFinset y).erase x, vertexDrop G z

theorem pathDropSum_eq_oriented :
    pathDropSum G =
      ∑ z : V, ∑ y ∈ G.neighborFinset z,
        (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z) := by
  rw [pathDropSum]
  calc
    (∑ y : V, ∑ x ∈ G.neighborFinset y,
        ∑ z ∈ (G.neighborFinset y).erase x, vertexDrop G z) =
        ∑ y : V, ∑ z ∈ G.neighborFinset y,
          (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z) := by
      apply sum_congr rfl
      intro y _hy
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using!
        sum_erase_second (G.neighborFinset y) (vertexDrop G)
    _ = ∑ z : V, ∑ y ∈ G.neighborFinset z,
          (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z) :=
      sum_neighborFinset_swap G
        (fun y z ↦ (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z))

theorem pathDropSum_lower_degree_residual :
    pathDropSum G ≥
      ∑ z : V, (G.degree z : ℚ) * (((G.degree z - 1 : ℕ) : ℚ) *
        vertexDrop G z) := by
  let A : ℚ := ∑ z : V, ∑ y ∈ G.neighborFinset z,
    (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G z)
  let A' : ℚ := ∑ z : V, ∑ y ∈ G.neighborFinset z,
    (((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G y)
  let B : ℚ := ∑ z : V, ∑ y ∈ G.neighborFinset z,
    (((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G z)
  let B' : ℚ := ∑ z : V, ∑ y ∈ G.neighborFinset z,
    (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G y)
  have hAA' : A' = A := by
    exact sum_neighborFinset_swap G
      (fun z y ↦ (((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G y))
  have hBB' : B' = B := by
    exact sum_neighborFinset_swap G
      (fun z y ↦ (((G.degree y - 1 : ℕ) : ℚ) * vertexDrop G y))
  have hpairs : B + B' ≤ A + A' := by
    dsimp only [A, A', B, B']
    simp_rw [← sum_add_distrib]
    apply sum_le_sum
    intro z _hz
    apply sum_le_sum
    intro y hy
    simpa [add_comm] using! edge_pair_drop_ineq G
      ((SimpleGraph.mem_neighborFinset (G := G) (v := z) y).mp hy).symm
  have hB : B = ∑ z : V,
      (G.degree z : ℚ) * (((G.degree z - 1 : ℕ) : ℚ) * vertexDrop G z) := by
    dsimp only [B]
    apply sum_congr rfl
    intro z _hz
    rw [sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
  rw [pathDropSum_eq_oriented]
  change A ≥ _
  rw [← hB]
  linarith

abbrev VertexTriple (V : Type*) := Σ _x : V, Σ _z : V, V

def rotateVertexTriple : VertexTriple V ≃ VertexTriple V where
  toFun p := ⟨p.2.2, ⟨p.1, p.2.1⟩⟩
  invFun p := ⟨p.2.1, ⟨p.2.2, p.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def commonTriples : Finset (VertexTriple V) :=
  Finset.univ.sigma fun x ↦
    (outsideClosedNeighborFinset G x).sigma fun z ↦
      G.neighborFinset x ∩ G.neighborFinset z

def pathTriples : Finset (VertexTriple V) :=
  Finset.univ.sigma fun y ↦
    (G.neighborFinset y).sigma fun x ↦
      (G.neighborFinset y).erase x

noncomputable def commonDropSum : ℚ :=
  ∑ p ∈ commonTriples G, vertexDrop G p.2.1

theorem commonDropSum_eq_counted :
    commonDropSum G =
      ∑ x : V, ∑ z ∈ outsideClosedNeighborFinset G x,
        (commonNeighborCount G x z : ℚ) * vertexDrop G z := by
  rw [commonDropSum, commonTriples, Finset.sum_sigma]
  apply sum_congr rfl
  intro x _hx
  rw [Finset.sum_sigma]
  apply sum_congr rfl
  intro z _hz
  change (∑ _y ∈ G.neighborFinset x ∩ G.neighborFinset z, vertexDrop G z) = _
  rw [sum_const, nsmul_eq_mul, commonNeighborCount]

theorem pathDropSum_eq_triples :
    pathDropSum G = ∑ p ∈ pathTriples G, vertexDrop G p.2.2 := by
  rw [pathDropSum, pathTriples, Finset.sum_sigma]
  apply sum_congr rfl
  intro y _hy
  rw [Finset.sum_sigma]

theorem rotate_mem_pathTriples_iff_mem_commonTriples
    (htri : G.CliqueFree 3) (p : VertexTriple V) :
    rotateVertexTriple p ∈ pathTriples G ↔ p ∈ commonTriples G := by
  rcases p with ⟨x, ⟨z, y⟩⟩
  simp only [rotateVertexTriple, pathTriples, commonTriples, mem_sigma, mem_univ,
    true_and, mem_inter, mem_erase]
  constructor
  · rintro ⟨hyx, hzx, hzy⟩
    have hxy : G.Adj x y :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := y) x).mp hyx |>.symm
    have hyz : G.Adj y z :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := y) z).mp hzy
    have hxz : x ≠ z := hzx.symm
    have hnadj := not_adj_endpoints_of_twoPath G htri hxy hyz hxz
    refine ⟨(mem_outsideClosedNeighborFinset G).mpr ⟨hxz.symm, hnadj⟩, ?_, ?_⟩
    · exact (SimpleGraph.mem_neighborFinset (G := G) (v := x) y).mpr hxy
    · exact (SimpleGraph.mem_neighborFinset (G := G) (v := z) y).mpr hyz.symm
  · rintro ⟨hzout, hyx, hyz⟩
    have hout := (mem_outsideClosedNeighborFinset G).mp hzout
    refine ⟨?_, hout.1, ?_⟩
    · exact (SimpleGraph.mem_neighborFinset (G := G) (v := y) x).mpr
        ((SimpleGraph.mem_neighborFinset (G := G) (v := x) y).mp hyx).symm
    · exact (SimpleGraph.mem_neighborFinset (G := G) (v := y) z).mpr
        ((SimpleGraph.mem_neighborFinset (G := G) (v := z) y).mp hyz).symm

theorem commonDropSum_eq_pathDropSum (htri : G.CliqueFree 3) :
    commonDropSum G = pathDropSum G := by
  rw [pathDropSum_eq_triples]
  exact Finset.sum_equiv (rotateVertexTriple (V := V))
    (fun p ↦ (rotate_mem_pathTriples_iff_mem_commonTriples G htri p).symm)
    (fun _p _hp ↦ rfl)

noncomputable def graphWeight : ℚ :=
  ∑ v : V, shearerWeight (G.degree v)

noncomputable def baseDeletionTerm (x : V) : ℚ :=
  1 - shearerWeight (G.degree x) -
    ∑ y ∈ G.neighborFinset x, shearerWeight (G.degree y)

noncomputable def changeDeletionTerm (x : V) : ℚ :=
  ∑ z ∈ outsideClosedNeighborFinset G x,
    (shearerWeight (degreeOutsideClosed G x z) - shearerWeight (G.degree z))

noncomputable def closedDeletionGain (x : V) : ℚ :=
  baseDeletionTerm G x + changeDeletionTerm G x

omit [DecidableEq V] in
theorem sum_baseDeletionTerm :
    (∑ x : V, baseDeletionTerm G x) =
      ∑ x : V, (1 - (((G.degree x + 1 : ℕ) : ℚ) *
        shearerWeight (G.degree x))) := by
  have hneighbor :
      (∑ x : V, ∑ y ∈ G.neighborFinset x, shearerWeight (G.degree y)) =
        ∑ x : V, (G.degree x : ℚ) * shearerWeight (G.degree x) := by
    calc
      (∑ x : V, ∑ y ∈ G.neighborFinset x, shearerWeight (G.degree y)) =
          ∑ y : V, ∑ x ∈ G.neighborFinset y, shearerWeight (G.degree y) :=
        sum_neighborFinset_swap G
          (fun _x y ↦ shearerWeight (G.degree y))
      _ = ∑ y : V, (G.degree y : ℚ) * shearerWeight (G.degree y) := by
        apply sum_congr rfl
        intro y _hy
        rw [sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
  simp only [baseDeletionTerm]
  rw [Finset.sum_sub_distrib, hneighbor]
  rw [← Finset.sum_sub_distrib]
  apply sum_congr rfl
  intro x _hx
  push_cast
  ring

theorem commonDropSum_le_sum_changeDeletionTerm :
    commonDropSum G ≤ ∑ x : V, changeDeletionTerm G x := by
  rw [commonDropSum_eq_counted]
  apply sum_le_sum
  intro x _hx
  rw [changeDeletionTerm]
  apply sum_le_sum
  intro z hz
  exact local_weight_change_lower G hz

omit [DecidableEq V] in
theorem sum_pointwiseResidual_nonneg :
    0 ≤ ∑ x : V,
      (1 - (((G.degree x + 1 : ℕ) : ℚ) * shearerWeight (G.degree x)) +
        (G.degree x : ℚ) * (((G.degree x - 1 : ℕ) : ℚ) * vertexDrop G x)) := by
  apply sum_nonneg
  intro x _hx
  rw [vertexDrop]
  simpa only [mul_assoc] using! shearerWeight_residual_nonneg (G.degree x)

set_option maxHeartbeats 800000 in
theorem pointwiseResidualSum_le_base_add_common (htri : G.CliqueFree 3) :
    (∑ x : V,
      (1 - (((G.degree x + 1 : ℕ) : ℚ) * shearerWeight (G.degree x)) +
        (G.degree x : ℚ) * (((G.degree x - 1 : ℕ) : ℚ) * vertexDrop G x))) ≤
      (∑ x : V, baseDeletionTerm G x) + commonDropSum G := by
  rw [sum_add_distrib, sum_baseDeletionTerm,
    commonDropSum_eq_pathDropSum G htri]
  apply add_le_add_right
  exact pathDropSum_lower_degree_residual G

theorem sum_closedDeletionGain_nonneg (htri : G.CliqueFree 3) :
    0 ≤ ∑ x : V, closedDeletionGain G x := by
  have hchange := commonDropSum_le_sum_changeDeletionTerm G
  have hnonneg : 0 ≤ (∑ x : V, baseDeletionTerm G x) + commonDropSum G :=
    (sum_pointwiseResidual_nonneg G).trans
      (pointwiseResidualSum_le_base_add_common G htri)
  have hfinal : 0 ≤ (∑ x : V, baseDeletionTerm G x) +
      ∑ x : V, changeDeletionTerm G x :=
    hnonneg.trans (add_le_add_right hchange _)
  simpa only [closedDeletionGain, sum_add_distrib] using! hfinal

theorem exists_nonneg_closedDeletionGain [Nonempty V]
    (htri : G.CliqueFree 3) :
    ∃ x : V, 0 ≤ closedDeletionGain G x := by
  have hsum := sum_closedDeletionGain_nonneg G htri
  have huniv : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
  have hzsum : (∑ _x : V, (0 : ℚ)) ≤
      ∑ x : V, closedDeletionGain G x := by
    simpa only [sum_const_zero] using! hsum
  obtain ⟨x, _hx, hx⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset V)) (f := fun _x ↦ (0 : ℚ))
      (g := closedDeletionGain G) huniv hzsum
  exact ⟨x, hx⟩

abbrev outsideSet (x : V) : Set V :=
  (outsideClosedNeighborFinset G x : Set V)

abbrev OutsideVertex (x : V) :=
  outsideSet G x

abbrev outsideGraph (x : V) : SimpleGraph (OutsideVertex G x) :=
  G.induce (outsideSet G x)

set_option maxHeartbeats 800000 in
theorem degree_outsideGraph (x : V) (z : OutsideVertex G x) :
    (outsideGraph G x).degree z = degreeOutsideClosed G x z.1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, degreeOutsideClosed]
  calc
    ((outsideGraph G x).neighborFinset z).card =
        (((outsideGraph G x).neighborFinset z).map
          (Function.Embedding.subtype
            (outsideClosedNeighborFinset G x : Set V))).card :=
      (card_map _).symm
    _ = (G.neighborFinset z.1 ∩ outsideClosedNeighborFinset G x).card := by
      congr 1
      ext y
      constructor
      · intro hy
        rw [Finset.mem_map] at hy
        obtain ⟨w, hw, hwy⟩ := hy
        have hwy' : w.1 = y := by simpa using! hwy
        subst y
        exact Finset.mem_inter.mpr ⟨by simpa [outsideGraph] using! hw, w.property⟩
      · intro hy
        obtain ⟨hyN, hyout⟩ := Finset.mem_inter.mp hy
        let w : OutsideVertex G x := ⟨y, by simpa [outsideSet] using! hyout⟩
        rw [Finset.mem_map]
        exact ⟨w, by simpa [outsideGraph] using! hyN, rfl⟩
    _ = (G.neighborFinset z.1 \ closedNeighborFinset G x).card := by
      congr 1
      ext y
      simp [outsideClosedNeighborFinset]

set_option maxHeartbeats 800000 in
theorem graphWeight_outsideGraph (x : V) :
    graphWeight (outsideGraph G x) =
      ∑ z ∈ outsideClosedNeighborFinset G x,
        shearerWeight (degreeOutsideClosed G x z) := by
  rw [graphWeight]
  calc
    (∑ z : OutsideVertex G x, shearerWeight ((outsideGraph G x).degree z)) =
        ∑ z : OutsideVertex G x, shearerWeight (degreeOutsideClosed G x z.1) := by
      apply sum_congr rfl
      intro z _hz
      rw [degree_outsideGraph]
    _ = ∑ z ∈ outsideClosedNeighborFinset G x,
          shearerWeight (degreeOutsideClosed G x z) := by
      symm
      exact Finset.sum_subtype (outsideClosedNeighborFinset G x)
        (fun _z ↦ Iff.rfl) (fun z ↦ shearerWeight (degreeOutsideClosed G x z))

theorem closedDeletionGain_eq (x : V) :
    closedDeletionGain G x =
      1 + graphWeight (outsideGraph G x) - graphWeight G := by
  have hsubset : closedNeighborFinset G x ⊆ (Finset.univ : Finset V) := subset_univ _
  have hpartition :
      (∑ z ∈ (Finset.univ : Finset V) \ closedNeighborFinset G x,
          shearerWeight (G.degree z)) +
        ∑ z ∈ closedNeighborFinset G x, shearerWeight (G.degree z) =
          ∑ z : V, shearerWeight (G.degree z) :=
    Finset.sum_sdiff hsubset
  have hxnot : x ∉ G.neighborFinset x := G.notMem_neighborFinset_self x
  rw [closedDeletionGain, baseDeletionTerm, changeDeletionTerm,
    graphWeight_outsideGraph, graphWeight]
  simp only [outsideClosedNeighborFinset] at hpartition ⊢
  rw [closedNeighborFinset, sum_insert hxnot] at hpartition
  rw [Finset.sum_sub_distrib]
  simp only [closedNeighborFinset]
  linear_combination -hpartition

set_option maxHeartbeats 800000 in
/-- The harmonic graph weight is bounded by the independence number in every
triangle-free finite graph. -/
theorem graphWeight_le_indepNum (htri : G.CliqueFree 3) :
    graphWeight G ≤ (G.indepNum : ℚ) := by
  classical
  let P (α : Type u) [Fintype α] : Prop :=
    ∀ [DecidableEq α] (H : SimpleGraph α) [DecidableRel H.Adj],
      H.CliqueFree 3 → graphWeight H ≤ (H.indepNum : ℚ)
  refine Fintype.induction_subsingleton_or_nontrivial (P := P) V ?_ ?_ G htri
  · intro α _ _ _ H _ _htri
    have hind : H.IsIndepSet ((Finset.univ : Finset α) : Set α) := by
      intro a _ha b _hb hab
      exact (hab (Subsingleton.elim a b)).elim
    calc
      graphWeight H = (Fintype.card α : ℚ) := by
        simp [graphWeight, SimpleGraph.degree_eq_zero_of_subsingleton]
      _ ≤ (H.indepNum : ℚ) := by
        exact_mod_cast hind.card_le_indepNum
  · intro α _ _ ih _ H _ htriH
    obtain ⟨x, hxgain⟩ := exists_nonneg_closedDeletionGain H htriH
    have hcard : Fintype.card (OutsideVertex H x) < Fintype.card α := by
      have hproper : outsideClosedNeighborFinset H x ⊂ (Finset.univ : Finset α) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.subset_univ _, ?_⟩
        intro heq
        have hxmem : x ∈ outsideClosedNeighborFinset H x := by
          rw [heq]
          simp
        exact (mem_outsideClosedNeighborFinset (G := H).mp hxmem).1 rfl
      let ecard : OutsideVertex H x ≃ ↥(outsideClosedNeighborFinset H x) :=
        { toFun := fun z ↦ ⟨z.1, z.property⟩
          invFun := fun z ↦ ⟨z.1, z.property⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      calc
        Fintype.card (OutsideVertex H x) =
            Fintype.card ↥(outsideClosedNeighborFinset H x) :=
          Fintype.card_congr ecard
        _ = (outsideClosedNeighborFinset H x).card :=
          Fintype.card_coe _
        _ < Fintype.card α := by
          have hc := Finset.card_lt_card hproper
          rw [Finset.card_univ] at hc
          exact hc
    have htriOut : (outsideGraph H x).CliqueFree 3 :=
      htriH.comap (SimpleGraph.Embedding.induce (outsideSet H x)).isContained
    have ihOut : graphWeight (outsideGraph H x) ≤
        ((outsideGraph H x).indepNum : ℚ) :=
      ih (OutsideVertex H x) hcard (outsideGraph H x) htriOut
    obtain ⟨C, hC⟩ := (outsideGraph H x).exists_isNIndepSet_indepNum
    let e : OutsideVertex H x ↪ α := Function.Embedding.subtype _
    let D : Finset α := C.map e
    have hD : H.IsIndepSet (D : Set α) := by
      intro a ha b hb hab
      simp only [D, Finset.mem_coe, Finset.mem_map] at ha hb
      obtain ⟨a', ha'C, rfl⟩ := ha
      obtain ⟨b', hb'C, rfl⟩ := hb
      exact hC.isIndepSet ha'C hb'C (fun heq ↦ hab (congrArg Subtype.val heq))
    have hxD : x ∉ D := by
      intro hx
      change x ∈ C.map e at hx
      rw [Finset.mem_map] at hx
      obtain ⟨z, _hzC, hzx⟩ := hx
      exact (mem_outsideClosedNeighborFinset (G := H).mp z.property).1
        (by simpa [e] using! hzx)
    have hIns : H.IsIndepSet ((insert x D : Finset α) : Set α) := by
      rw [Finset.coe_insert]
      letI : Std.Symm (fun v w ↦ ¬H.Adj v w) :=
        ⟨fun _ _ h h' ↦ h h'.symm⟩
      apply hD.insert_of_symm
      intro b hb _hxb
      simp only [D, Finset.mem_coe, Finset.mem_map] at hb
      obtain ⟨z, _hzC, rfl⟩ := hb
      exact (mem_outsideClosedNeighborFinset (G := H).mp z.property).2
    have hnat : (outsideGraph H x).indepNum + 1 ≤ H.indepNum := by
      calc
        (outsideGraph H x).indepNum + 1 = C.card + 1 :=
          congrArg (· + 1) hC.card_eq.symm
        _ = D.card + 1 := by simp [D]
        _ = (insert x D).card := by rw [card_insert_of_notMem hxD]
        _ ≤ H.indepNum := hIns.card_le_indepNum
    have hdelete : graphWeight H ≤ 1 + graphWeight (outsideGraph H x) := by
      rw [closedDeletionGain_eq] at hxgain
      linarith
    calc
      graphWeight H ≤ 1 + graphWeight (outsideGraph H x) := hdelete
      _ ≤ 1 + ((outsideGraph H x).indepNum : ℚ) := by linarith
      _ = (((outsideGraph H x).indepNum + 1 : ℕ) : ℚ) := by push_cast; ring
      _ ≤ (H.indepNum : ℚ) := by exact_mod_cast hnat

end FiniteGraph

end Erdos788.AKSRoute
