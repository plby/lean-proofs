import Mathlib

/-!
# The unconditional FNV U4 path bounds

This file proves the finite Hölder inequality, closes the global
Blakley--Roy/Hoory step, and then deletes the walks with a repeated vertex.
Thus the two final statements have no analytic or graph-theoretic hypotheses
beyond finiteness (and the displayed bipartition in the second statement).
-/

namespace Erdos59

open scoped BigOperators

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## Finite Hölder -/

private lemma u4_sum_mul_mul_pow_three_le
    {I : Type*} (s : Finset I) (a b c : I → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∑ i ∈ s, a i * b i * c i) ^ 3 ≤
      (∑ i ∈ s, a i ^ 3) * (∑ i ∈ s, b i ^ 3) *
        (∑ i ∈ s, c i ^ 3) := by
  have hthree : (3 : ℝ).HolderConjugate (3 / 2 : ℝ) := by
    constructor <;> norm_num
  have htwo : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hA := Real.inner_le_Lp_mul_Lq_of_nonneg s hthree ha
    (fun i hi ↦ mul_nonneg (hb i hi) (hc i hi))
  have hBC := Real.inner_le_Lp_mul_Lq_of_nonneg s htwo
    (fun i hi ↦ Real.rpow_nonneg (hb i hi) _)
    (fun i hi ↦ Real.rpow_nonneg (hc i hi) _)
    (f := fun i ↦ b i ^ (3 / 2 : ℝ)) (g := fun i ↦ c i ^ (3 / 2 : ℝ))
  norm_num at hA hBC
  have hsum_nonneg : 0 ≤ ∑ i ∈ s, a i * b i * c i :=
    Finset.sum_nonneg fun i hi ↦
      mul_nonneg (mul_nonneg (ha i hi) (hb i hi)) (hc i hi)
  have hA3 : 0 ≤ ∑ i ∈ s, a i ^ 3 :=
    Finset.sum_nonneg fun i hi ↦ pow_nonneg (ha i hi) _
  have hB3 : 0 ≤ ∑ i ∈ s, b i ^ 3 :=
    Finset.sum_nonneg fun i hi ↦ pow_nonneg (hb i hi) _
  have hC3 : 0 ≤ ∑ i ∈ s, c i ^ 3 :=
    Finset.sum_nonneg fun i hi ↦ pow_nonneg (hc i hi) _
  have hBC' :
      ∑ i ∈ s, (b i * c i) ^ (3 / 2 : ℝ) ≤
        (∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ) *
          (∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ) := by
    have hbpow :
        ∑ i ∈ s, (b i ^ (3 / 2 : ℝ)) ^ 2 = ∑ i ∈ s, b i ^ 3 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hb i hi)]
      norm_num
    have hcpow :
        ∑ i ∈ s, (c i ^ (3 / 2 : ℝ)) ^ 2 = ∑ i ∈ s, c i ^ 3 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hc i hi)]
      norm_num
    calc
      _ = ∑ i ∈ s, b i ^ (3 / 2 : ℝ) * c i ^ (3 / 2 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Real.mul_rpow (hb i hi) (hc i hi)
      _ ≤ ((∑ i ∈ s, (b i ^ (3 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ)) *
          ((∑ i ∈ s, (c i ^ (3 / 2 : ℝ)) ^ 2) ^ (1 / 2 : ℝ)) := hBC
      _ = _ := by rw [hbpow, hcpow]
  have hA' :
      ∑ i ∈ s, a i * b i * c i ≤
        (∑ i ∈ s, a i ^ 3) ^ (1 / 3 : ℝ) *
          (∑ i ∈ s, (b i * c i) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
    simpa only [mul_assoc] using hA
  calc
    (∑ i ∈ s, a i * b i * c i) ^ 3 ≤
        ((∑ i ∈ s, a i ^ 3) ^ (1 / 3 : ℝ) *
          (∑ i ∈ s, (b i * c i) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ hsum_nonneg hA' 3
    _ ≤ ((∑ i ∈ s, a i ^ 3) ^ (1 / 3 : ℝ) *
          (((∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ) *
            (∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ))) ^ 3 := by
      apply pow_le_pow_left₀
      · exact mul_nonneg (Real.rpow_nonneg hA3 _)
          (Real.rpow_nonneg (Finset.sum_nonneg fun i hi ↦
            Real.rpow_nonneg (mul_nonneg (hb i hi) (hc i hi)) _) _)
      · apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow
            (Finset.sum_nonneg fun i hi ↦
              Real.rpow_nonneg (mul_nonneg (hb i hi) (hc i hi)) _)
            hBC' (by norm_num)
        · exact Real.rpow_nonneg hA3 _
    _ = (∑ i ∈ s, a i ^ 3) * (∑ i ∈ s, b i ^ 3) *
          (∑ i ∈ s, c i ^ 3) := by
      have hx : ((∑ i ∈ s, a i ^ 3) ^ (1 / 3 : ℝ)) ^ 3 =
          ∑ i ∈ s, a i ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hA3]
        norm_num
      have hy : ((∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) =
          ∑ i ∈ s, b i ^ 3 := by
        rw [← Real.rpow_mul hB3]
        norm_num
      have hz : ((∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) =
          ∑ i ∈ s, c i ^ 3 := by
        rw [← Real.rpow_mul hC3]
        norm_num
      have hyz :
          ((((∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ) *
            (∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 / 3 : ℝ))) ^ 3 =
              (∑ i ∈ s, b i ^ 3) * (∑ i ∈ s, c i ^ 3) := by
        have hrootB : 0 ≤ (∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ) :=
          Real.rpow_nonneg hB3 _
        have hrootC : 0 ≤ (∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ) :=
          Real.rpow_nonneg hC3 _
        calc
          _ = (((∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ) *
              (∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul
              (mul_nonneg hrootB hrootC)]
            norm_num
          _ = ((∑ i ∈ s, b i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) *
              ((∑ i ∈ s, c i ^ 3) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
            exact Real.mul_rpow hrootB hrootC
          _ = _ := by rw [hy, hz]
      rw [mul_pow, hx, hyz]
      ring

/-! ## Walk and path counts -/

def u4LocalPaths (u v : V) : Finset (V × V) :=
  (G.neighborFinset u ×ˢ G.neighborFinset v).filter fun p ↦
    p.1 ≠ v ∧ p.2 ≠ u ∧ p.1 ≠ p.2

def u4OrientedPathCount : ℕ :=
  ∑ u, ∑ v ∈ G.neighborFinset u, (u4LocalPaths G u v).card

def u4PathCount : ℝ := (u4OrientedPathCount G : ℝ) / 2

def u4OrientedWalkCount : ℕ :=
  ∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v

def u4OrientedEdgesBetween (A B : Finset V) : Finset (V × V) :=
  (A ×ˢ B).filter fun p ↦ G.Adj p.1 p.2

def u4WalkWeightBetween (A B : Finset V) : ℝ :=
  ∑ p ∈ u4OrientedEdgesBetween G A B,
    (G.degree p.1 : ℝ) * (G.degree p.2 : ℝ)

private lemma u4_rpow_third_mul_inv_thirds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x * y) ^ (1 / 3 : ℝ) * x ^ (-1 / 3 : ℝ) * y ^ (-1 / 3 : ℝ) = 1 := by
  rw [Real.mul_rpow hx.le hy.le]
  calc
    (x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ)) * x ^ (-1 / 3 : ℝ) *
        y ^ (-1 / 3 : ℝ) =
        (x ^ (1 / 3 : ℝ) * x ^ (-1 / 3 : ℝ)) *
          (y ^ (1 / 3 : ℝ) * y ^ (-1 / 3 : ℝ)) := by ring
    _ = x ^ ((1 / 3 : ℝ) + (-1 / 3 : ℝ)) *
          y ^ ((1 / 3 : ℝ) + (-1 / 3 : ℝ)) := by
      rw [Real.rpow_add hx, Real.rpow_add hy]
    _ = 1 := by norm_num

private lemma u4_rpow_third_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private lemma u4_rpow_neg_third_cube {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (-1 / 3 : ℝ)) ^ 3 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num [Real.rpow_neg_one]

private lemma u4_sum_inv_left_le (A B : Finset V) :
    ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.1 : ℝ)⁻¹ ≤
      (A.card : ℝ) := by
  have hinner : ∀ u : V,
      (∑ v ∈ B, if G.Adj u v then (G.degree u : ℝ)⁻¹ else 0) =
        ((B.filter fun v ↦ G.Adj u v).card : ℝ) * (G.degree u : ℝ)⁻¹ := by
    intro u
    calc
      _ = (∑ v ∈ B, if G.Adj u v then (1 : ℝ) else 0) *
          (G.degree u : ℝ)⁻¹ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        split <;> simp_all
      _ = _ := by rw [Finset.sum_boole]
  calc
    ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.1 : ℝ)⁻¹ =
        ∑ u ∈ A, ((B.filter fun v ↦ G.Adj u v).card : ℝ) *
          (G.degree u : ℝ)⁻¹ := by
      simp only [u4OrientedEdgesBetween, Finset.sum_filter, Finset.sum_product]
      exact Finset.sum_congr rfl fun u hu ↦ hinner u
    _ ≤ ∑ _u ∈ A, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro u hu
      have hcard : (B.filter fun v ↦ G.Adj u v).card ≤ G.degree u := by
        rw [← G.card_neighborFinset_eq_degree]
        apply Finset.card_le_card
        intro v hv
        exact (G.mem_neighborFinset u v).2 (Finset.mem_filter.mp hv).2
      by_cases hd : G.degree u = 0
      · have hz : (B.filter fun v ↦ G.Adj u v).card = 0 := by omega
        simp [hd, hz]
      · rw [mul_inv_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))]
        simpa only [one_mul] using (show
          ((B.filter fun v ↦ G.Adj u v).card : ℝ) ≤ G.degree u by
            exact_mod_cast hcard)
    _ = (A.card : ℝ) := by simp

private lemma u4_sum_inv_right_le (A B : Finset V) :
    ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.2 : ℝ)⁻¹ ≤
      (B.card : ℝ) := by
  have hinner : ∀ v : V,
      (∑ u ∈ A, if G.Adj u v then (G.degree v : ℝ)⁻¹ else 0) =
        ((A.filter fun u ↦ G.Adj u v).card : ℝ) * (G.degree v : ℝ)⁻¹ := by
    intro v
    calc
      _ = (∑ u ∈ A, if G.Adj u v then (1 : ℝ) else 0) *
          (G.degree v : ℝ)⁻¹ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u hu
        split <;> simp_all
      _ = _ := by rw [Finset.sum_boole]
  calc
    ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.2 : ℝ)⁻¹ =
        ∑ v ∈ B, ((A.filter fun u ↦ G.Adj u v).card : ℝ) *
          (G.degree v : ℝ)⁻¹ := by
      simp only [u4OrientedEdgesBetween, Finset.sum_filter, Finset.sum_product]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v hv
      exact hinner v
    _ ≤ ∑ _v ∈ B, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      have hcard : (A.filter fun u ↦ G.Adj u v).card ≤ G.degree v := by
        rw [← G.card_neighborFinset_eq_degree]
        apply Finset.card_le_card
        intro u hu
        exact (G.mem_neighborFinset v u).2 (Finset.mem_filter.mp hu).2.symm
      by_cases hd : G.degree v = 0
      · have hz : (A.filter fun u ↦ G.Adj u v).card = 0 := by omega
        simp [hd, hz]
      · rw [mul_inv_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))]
        simpa only [one_mul] using (show
          ((A.filter fun u ↦ G.Adj u v).card : ℝ) ≤ G.degree v by
            exact_mod_cast hcard)
    _ = (B.card : ℝ) := by simp

private theorem u4_walkWeight_lower_bound (A B : Finset V) :
    ((u4OrientedEdgesBetween G A B).card : ℝ) ^ 3 /
        ((A.card : ℝ) * (B.card : ℝ)) ≤
      u4WalkWeightBetween G A B := by
  let E := u4OrientedEdgesBetween G A B
  let a : V × V → ℝ := fun p ↦
    ((G.degree p.1 : ℝ) * (G.degree p.2 : ℝ)) ^ (1 / 3 : ℝ)
  let b : V × V → ℝ := fun p ↦ (G.degree p.1 : ℝ) ^ (-1 / 3 : ℝ)
  let c : V × V → ℝ := fun p ↦ (G.degree p.2 : ℝ) ^ (-1 / 3 : ℝ)
  have hH := u4_sum_mul_mul_pow_three_le E a b c
    (fun p hp ↦ Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)
    (fun p hp ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun p hp ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hprod : ∑ p ∈ E, a p * b p * c p = (E.card : ℝ) := by
    calc
      _ = ∑ _p ∈ E, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hadj : G.Adj p.1 p.2 := (Finset.mem_filter.mp hp).2
        exact u4_rpow_third_mul_inv_thirds
          (Nat.cast_pos.mpr hadj.degree_pos_left)
          (Nat.cast_pos.mpr hadj.degree_pos_right)
      _ = (E.card : ℝ) := by simp
  have ha3 : ∑ p ∈ E, a p ^ 3 = u4WalkWeightBetween G A B := by
    apply Finset.sum_congr rfl
    intro p hp
    exact u4_rpow_third_cube (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hb3 : ∑ p ∈ E, b p ^ 3 =
      ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.1 : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp
    exact u4_rpow_neg_third_cube (Nat.cast_nonneg _)
  have hc3 : ∑ p ∈ E, c p ^ 3 =
      ∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.2 : ℝ)⁻¹ := by
    apply Finset.sum_congr rfl
    intro p hp
    exact u4_rpow_neg_third_cube (Nat.cast_nonneg _)
  rw [hprod, ha3, hb3, hc3] at hH
  have hweight : 0 ≤ u4WalkWeightBetween G A B := by
    exact Finset.sum_nonneg fun p hp ↦
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmul : ((u4OrientedEdgesBetween G A B).card : ℝ) ^ 3 ≤
      u4WalkWeightBetween G A B * (A.card : ℝ) * (B.card : ℝ) := by
    calc
      _ ≤ u4WalkWeightBetween G A B *
          (∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.1 : ℝ)⁻¹) *
          (∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.2 : ℝ)⁻¹) := hH
      _ ≤ u4WalkWeightBetween G A B * (A.card : ℝ) *
          (∑ p ∈ u4OrientedEdgesBetween G A B, (G.degree p.2 : ℝ)⁻¹) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left (u4_sum_inv_left_le G A B) hweight
        · exact Finset.sum_nonneg fun p hp ↦ inv_nonneg.mpr (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (u4_sum_inv_right_le G A B)
        (mul_nonneg hweight (Nat.cast_nonneg _))
  by_cases hA : A.card = 0
  · simpa [hA, u4OrientedEdgesBetween] using hweight
  by_cases hB : B.card = 0
  · simpa [hB, u4OrientedEdgesBetween] using hweight
  rw [div_le_iff₀ (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hA))
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hB)))]
  simpa only [mul_assoc] using hmul

private lemma u4_orientedEdgesBetween_card_eq_sum (A B : Finset V) :
    (u4OrientedEdgesBetween G A B).card =
      ∑ u ∈ A, (B.filter fun v ↦ G.Adj u v).card := by
  calc
    _ = ∑ p ∈ u4OrientedEdgesBetween G A B, (1 : ℕ) := by simp
    _ = _ := by
      simp only [u4OrientedEdgesBetween, Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_boole (R := ℕ)]
      norm_num

private lemma u4_orientedEdgesBetween_univ_card :
    (u4OrientedEdgesBetween G Finset.univ Finset.univ).card =
      2 * G.edgeFinset.card := by
  rw [u4_orientedEdgesBetween_card_eq_sum]
  have hfilter : ∀ u : V,
      (Finset.univ.filter fun v ↦ G.Adj u v) = G.neighborFinset u := by
    intro u
    ext v
    simp [G.mem_neighborFinset]
  simp_rw [hfilter]
  simpa [G.card_neighborFinset_eq_degree] using G.sum_degrees_eq_twice_card_edges

private lemma u4_lengthThreeWalkWeightBetween_univ :
    u4WalkWeightBetween G Finset.univ Finset.univ =
      (u4OrientedWalkCount G : ℝ) := by
  have hfilter : ∀ u : V,
      (Finset.univ.filter fun v ↦ G.Adj u v) = G.neighborFinset u := by
    intro u
    ext v
    simp [G.mem_neighborFinset]
  have hinner : ∀ u : V,
      (∑ v, if G.Adj u v then
          (G.degree u : ℝ) * (G.degree v : ℝ) else 0) =
        ∑ v ∈ G.neighborFinset u,
          (G.degree u : ℝ) * (G.degree v : ℝ) := by
    intro u
    rw [← hfilter u, Finset.sum_filter]
  unfold u4WalkWeightBetween u4OrientedWalkCount
  push_cast
  simp only [u4OrientedEdgesBetween, Finset.sum_filter, Finset.sum_product,
    Finset.mem_univ, true_and]
  exact Finset.sum_congr rfl fun u hu ↦ hinner u

/-- The global Blakley--Roy inequality obtained from the finite three-factor
Hölder estimate, rather than assumed as an additional hypothesis. -/
theorem fnv_u4_oriented_walk_lower_bound :
    8 * (G.edgeFinset.card : ℝ) ^ 3 / (Fintype.card V : ℝ) ^ 2 ≤
      (u4OrientedWalkCount G : ℝ) := by
  have h := u4_walkWeight_lower_bound G
    (Finset.univ : Finset V) (Finset.univ : Finset V)
  rw [u4_orientedEdgesBetween_univ_card G,
    u4_lengthThreeWalkWeightBetween_univ G] at h
  norm_num [Nat.cast_mul, pow_two] at h ⊢
  convert h using 1 <;> ring

private lemma u4_orientedEdgesBetween_card_of_bipartite
    {A B : Finset V} (hG : G.IsBipartiteWith A B) :
    (u4OrientedEdgesBetween G A B).card = G.edgeFinset.card := by
  rw [u4_orientedEdgesBetween_card_eq_sum]
  have hneighbors : ∀ u ∈ A,
      (B.filter fun v ↦ G.Adj u v) = G.neighborFinset u := by
    intro u hu
    ext v
    simp only [Finset.mem_filter, G.mem_neighborFinset]
    constructor
    · exact fun hv ↦ hv.2
    · intro huv
      exact ⟨hG.mem_of_mem_adj hu huv, huv⟩
  calc
    ∑ u ∈ A, (B.filter fun v ↦ G.Adj u v).card =
        ∑ u ∈ A, G.degree u := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hneighbors u hu, G.card_neighborFinset_eq_degree]
    _ = G.edgeFinset.card := G.isBipartiteWith_sum_degrees_eq_card_edges hG

private lemma u4_lengthThreeWalkWeightBetween_bipartite
    {A B : Finset V} (hG : G.IsBipartiteWith A B) :
    (u4OrientedWalkCount G : ℝ) =
      2 * u4WalkWeightBetween G A B := by
  have hall : u4OrientedEdgesBetween G Finset.univ Finset.univ =
      u4OrientedEdgesBetween G A B ∪ u4OrientedEdgesBetween G B A := by
    ext p
    simp only [u4OrientedEdgesBetween, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and, Finset.mem_union, and_self]
    constructor
    · intro hp
      rcases hG.mem_of_adj hp with hpAB | hpBA
      · exact Or.inl ⟨⟨hpAB.1, hpAB.2⟩, hp⟩
      · exact Or.inr ⟨⟨hpBA.1, hpBA.2⟩, hp⟩
    · rintro (⟨_, hp⟩ | ⟨_, hp⟩) <;> exact hp
  have hdisj : Disjoint (u4OrientedEdgesBetween G A B)
      (u4OrientedEdgesBetween G B A) := by
    rw [Finset.disjoint_left]
    intro p hpAB hpBA
    have hpA := (Finset.mem_product.mp (Finset.mem_filter.mp hpAB).1).1
    have hpB := (Finset.mem_product.mp (Finset.mem_filter.mp hpBA).1).1
    exact (Set.disjoint_left.mp hG.disjoint hpA hpB)
  have hswap : u4OrientedEdgesBetween G B A =
      (u4OrientedEdgesBetween G A B).map ⟨Prod.swap, Prod.swap_injective⟩ := by
    ext p
    simp only [u4OrientedEdgesBetween, Finset.mem_map, Finset.mem_filter,
      Finset.mem_product]
    constructor
    · intro hp
      exact ⟨(p.2, p.1), ⟨⟨hp.1.2, hp.1.1⟩, hp.2.symm⟩, by simp⟩
    · rintro ⟨q, ⟨⟨hqA, hqB⟩, hqadj⟩, hqp⟩
      change (q.2, q.1) = p at hqp
      subst p
      exact ⟨⟨hqB, hqA⟩, hqadj.symm⟩
  rw [← u4_lengthThreeWalkWeightBetween_univ G]
  unfold u4WalkWeightBetween
  rw [hall, Finset.sum_union hdisj, hswap, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Prod.swap_prod_mk, Prod.fst_swap,
    Prod.snd_swap]
  rw [two_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The global bipartite Hoory/Sidorenko three-walk inequality, obtained
directly from finite Hölder on the oriented edges from `A` to `B`. -/
theorem fnv_u4_bipartite_oriented_walk_lower_bound
    {A B : Finset V} (hG : G.IsBipartiteWith A B) :
    2 * (G.edgeFinset.card : ℝ) ^ 3 /
      ((A.card : ℝ) * (B.card : ℝ)) ≤
      (u4OrientedWalkCount G : ℝ) := by
  have h := u4_walkWeight_lower_bound G A B
  rw [u4_orientedEdgesBetween_card_of_bipartite G hG] at h
  rw [u4_lengthThreeWalkWeightBetween_bipartite G hG]
  calc
    2 * (G.edgeFinset.card : ℝ) ^ 3 / ((A.card : ℝ) * (B.card : ℝ)) =
        2 * ((G.edgeFinset.card : ℝ) ^ 3 /
          ((A.card : ℝ) * (B.card : ℝ))) := by ring
    _ ≤ 2 * u4WalkWeightBetween G A B :=
      mul_le_mul_of_nonneg_left h (by norm_num)

/-! ## Deleting repeated-vertex walks -/

private def u4BadLeft (u v : V) : Finset (V × V) :=
  (G.neighborFinset u ×ˢ G.neighborFinset v).filter fun p ↦ p.1 = v

private def u4BadRight (u v : V) : Finset (V × V) :=
  (G.neighborFinset u ×ˢ G.neighborFinset v).filter fun p ↦ p.2 = u

private def u4BadRepeat (u v : V) : Finset (V × V) :=
  (G.neighborFinset u ×ˢ G.neighborFinset v).filter fun p ↦ p.1 = p.2

private def u4BadChoices (u v : V) : Finset (V × V) :=
  (G.neighborFinset u ×ˢ G.neighborFinset v).filter fun p ↦
    ¬ (p.1 ≠ v ∧ p.2 ≠ u ∧ p.1 ≠ p.2)

private lemma u4_card_badLeft_le (u v : V) :
    (u4BadLeft G u v).card ≤ G.degree v := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp q hq hpq
    apply Prod.ext
    · calc
        p.1 = v := (Finset.mem_filter.mp hp).2
        _ = q.1 := (Finset.mem_filter.mp hq).2.symm
    · exact hpq

private lemma u4_card_badRight_le (u v : V) :
    (u4BadRight G u v).card ≤ G.degree u := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq hpq
    apply Prod.ext
    · exact hpq
    · calc
        p.2 = u := (Finset.mem_filter.mp hp).2
        _ = q.2 := (Finset.mem_filter.mp hq).2.symm

private lemma u4_card_badRepeat_le (u v : V) :
    (u4BadRepeat G u v).card ≤ G.degree u := by
  rw [← G.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro p hp q hq hpq
    apply Prod.ext hpq
    calc
      p.2 = p.1 := (Finset.mem_filter.mp hp).2.symm
      _ = q.1 := hpq
      _ = q.2 := (Finset.mem_filter.mp hq).2

private lemma u4_badChoices_subset (u v : V) :
    u4BadChoices G u v ⊆
      u4BadLeft G u v ∪ u4BadRight G u v ∪ u4BadRepeat G u v := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  simp only [u4BadLeft, u4BadRight, u4BadRepeat, Finset.mem_union,
    Finset.mem_filter]
  by_cases h₁ : p.1 = v
  · exact Or.inl (Or.inl ⟨hp'.1, h₁⟩)
  by_cases h₂ : p.2 = u
  · exact Or.inl (Or.inr ⟨hp'.1, h₂⟩)
  have h₃ : p.1 = p.2 := by
    by_contra h₃
    exact hp'.2 ⟨h₁, h₂, h₃⟩
  exact Or.inr ⟨hp'.1, h₃⟩

private lemma u4_local_walk_le_path_add {u v : V} (huv : G.Adj u v) :
    G.degree u * G.degree v ≤
      (u4LocalPaths G u v).card + G.degree v + G.degree u + G.maxDegree := by
  have hpartition :
      (u4LocalPaths G u v).card + (u4BadChoices G u v).card =
        G.degree u * G.degree v := by
    simpa [u4LocalPaths, u4BadChoices, Finset.card_product,
      G.card_neighborFinset_eq_degree] using
      (Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset u ×ˢ G.neighborFinset v)
        (p := fun p : V × V ↦ p.1 ≠ v ∧ p.2 ≠ u ∧ p.1 ≠ p.2))
  have hbad : (u4BadChoices G u v).card ≤
      (u4BadLeft G u v).card + (u4BadRight G u v).card +
        (u4BadRepeat G u v).card := by
    exact (Finset.card_le_card (u4_badChoices_subset G u v)).trans
      ((Finset.card_union_le (u4BadLeft G u v ∪ u4BadRight G u v)
        (u4BadRepeat G u v)).trans (Nat.add_le_add_right
          (Finset.card_union_le (u4BadLeft G u v) (u4BadRight G u v)) _))
  have hrepeat := (u4_card_badRepeat_le G u v).trans (G.degree_le_maxDegree u)
  have hleft := u4_card_badLeft_le G u v
  have hright := u4_card_badRight_le G u v
  omega

private lemma u4_badRepeat_empty_of_bipartite
    {A B : Finset V} (hG : G.IsBipartiteWith A B) {u v : V}
    (huv : G.Adj u v) : u4BadRepeat G u v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hprod := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  have heq := (Finset.mem_filter.mp hp).2
  have hux : G.Adj u p.1 := (G.mem_neighborFinset u p.1).1 hprod.1
  have hvy : G.Adj v p.2 := (G.mem_neighborFinset v p.2).1 hprod.2
  rcases hG.mem_of_adj huv with huvAB | huvBA
  · have hxB := hG.mem_of_mem_adj huvAB.1 hux
    have hyA := hG.mem_of_mem_adj' huvAB.2 hvy.symm
    rw [← heq] at hyA
    exact Set.disjoint_left.mp hG.disjoint hyA hxB
  · have hxA := hG.mem_of_mem_adj' huvBA.1 hux.symm
    have hyB := hG.mem_of_mem_adj huvBA.2 hvy
    rw [← heq] at hyB
    exact Set.disjoint_left.mp hG.disjoint hxA hyB

private lemma u4_local_walk_le_path_add_bipartite
    {A B : Finset V} (hG : G.IsBipartiteWith A B) {u v : V}
    (huv : G.Adj u v) :
    G.degree u * G.degree v ≤
      (u4LocalPaths G u v).card + G.degree v + G.degree u := by
  have hpartition :
      (u4LocalPaths G u v).card + (u4BadChoices G u v).card =
        G.degree u * G.degree v := by
    simpa [u4LocalPaths, u4BadChoices, Finset.card_product,
      G.card_neighborFinset_eq_degree] using
      (Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset u ×ˢ G.neighborFinset v)
        (p := fun p : V × V ↦ p.1 ≠ v ∧ p.2 ≠ u ∧ p.1 ≠ p.2))
  have hrepeat : (u4BadRepeat G u v).card = 0 := by
    rw [u4_badRepeat_empty_of_bipartite G hG huv]
    simp
  have hbad : (u4BadChoices G u v).card ≤
      (u4BadLeft G u v).card + (u4BadRight G u v).card +
        (u4BadRepeat G u v).card := by
    exact (Finset.card_le_card (u4_badChoices_subset G u v)).trans
      ((Finset.card_union_le (u4BadLeft G u v ∪ u4BadRight G u v)
        (u4BadRepeat G u v)).trans (Nat.add_le_add_right
          (Finset.card_union_le (u4BadLeft G u v) (u4BadRight G u v)) _))
  have hleft := u4_card_badLeft_le G u v
  have hright := u4_card_badRight_le G u v
  omega

private lemma u4_walk_le_path_add_six :
    u4OrientedWalkCount G ≤
      u4OrientedPathCount G + 6 * G.maxDegree * G.edgeFinset.card := by
  have hconst :
      (∑ u, ∑ _v ∈ G.neighborFinset u, 3 * G.maxDegree) =
        6 * G.maxDegree * G.edgeFinset.card := by
    calc
      _ = ∑ u, G.degree u * (3 * G.maxDegree) := by
        apply Finset.sum_congr rfl
        intro u hu
        simp [G.card_neighborFinset_eq_degree]
      _ = (∑ u, G.degree u) * (3 * G.maxDegree) := by
        rw [Finset.sum_mul]
      _ = _ := by
        rw [G.sum_degrees_eq_twice_card_edges]
        ring
  unfold u4OrientedWalkCount u4OrientedPathCount
  calc
    (∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v) ≤
        ∑ u, ∑ v ∈ G.neighborFinset u,
          ((u4LocalPaths G u v).card + 3 * G.maxDegree) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      have huv := (G.mem_neighborFinset u v).1 hv
      have hlocal := u4_local_walk_le_path_add G huv
      have huD := G.degree_le_maxDegree u
      have hvD := G.degree_le_maxDegree v
      omega
    _ = (∑ u, ∑ v ∈ G.neighborFinset u,
          (u4LocalPaths G u v).card) +
          (∑ u, ∑ _v ∈ G.neighborFinset u, 3 * G.maxDegree) := by
      simp_rw [Finset.sum_add_distrib]
    _ = _ := by rw [hconst]

private lemma u4_walk_le_path_add_four
    {A B : Finset V} (hG : G.IsBipartiteWith A B) :
    u4OrientedWalkCount G ≤
      u4OrientedPathCount G + 4 * G.maxDegree * G.edgeFinset.card := by
  have hconst :
      (∑ u, ∑ _v ∈ G.neighborFinset u, 2 * G.maxDegree) =
        4 * G.maxDegree * G.edgeFinset.card := by
    calc
      _ = ∑ u, G.degree u * (2 * G.maxDegree) := by
        apply Finset.sum_congr rfl
        intro u hu
        simp [G.card_neighborFinset_eq_degree]
      _ = (∑ u, G.degree u) * (2 * G.maxDegree) := by
        rw [Finset.sum_mul]
      _ = _ := by
        rw [G.sum_degrees_eq_twice_card_edges]
        ring
  unfold u4OrientedWalkCount u4OrientedPathCount
  calc
    (∑ u, ∑ v ∈ G.neighborFinset u, G.degree u * G.degree v) ≤
        ∑ u, ∑ v ∈ G.neighborFinset u,
          ((u4LocalPaths G u v).card + 2 * G.maxDegree) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      have huv := (G.mem_neighborFinset u v).1 hv
      have hlocal := u4_local_walk_le_path_add_bipartite G hG huv
      have huD := G.degree_le_maxDegree u
      have hvD := G.degree_le_maxDegree v
      omega
    _ = (∑ u, ∑ v ∈ G.neighborFinset u,
          (u4LocalPaths G u v).card) +
          (∑ u, ∑ _v ∈ G.neighborFinset u, 2 * G.maxDegree) := by
      simp_rw [Finset.sum_add_distrib]
    _ = _ := by rw [hconst]

/-- FNV U4, general form: an `n`-vertex finite simple graph with `e` edges
and maximum degree `Δ` has at least `4e³/n² - 3Δe` unoriented
three-edge paths. -/
theorem fnv_u4_general :
    4 * (G.edgeFinset.card : ℝ) ^ 3 / (Fintype.card V : ℝ) ^ 2 -
        3 * (G.maxDegree : ℝ) * G.edgeFinset.card ≤
      u4PathCount G := by
  have hwalk := fnv_u4_oriented_walk_lower_bound G
  have hdeleteNat := u4_walk_le_path_add_six G
  have hdelete : (u4OrientedWalkCount G : ℝ) ≤
      u4OrientedPathCount G +
        6 * (G.maxDegree : ℝ) * G.edgeFinset.card := by
    exact_mod_cast hdeleteNat
  unfold u4PathCount
  calc
    4 * (G.edgeFinset.card : ℝ) ^ 3 / (Fintype.card V : ℝ) ^ 2 -
        3 * (G.maxDegree : ℝ) * G.edgeFinset.card ≤
        ((u4OrientedWalkCount G : ℝ) -
          6 * (G.maxDegree : ℝ) * G.edgeFinset.card) / 2 := by
      rw [show 4 * (G.edgeFinset.card : ℝ) ^ 3 /
          (Fintype.card V : ℝ) ^ 2 -
          3 * (G.maxDegree : ℝ) * G.edgeFinset.card =
          (8 * (G.edgeFinset.card : ℝ) ^ 3 /
            (Fintype.card V : ℝ) ^ 2 -
            6 * (G.maxDegree : ℝ) * G.edgeFinset.card) / 2 by ring]
      exact div_le_div_of_nonneg_right
        (sub_le_sub_right hwalk _) (by norm_num)
    _ ≤ (u4OrientedPathCount G : ℝ) / 2 := by linarith

/-- FNV U4, bipartite form: if the parts have sizes `m,n`, a finite
bipartite simple graph has at least `e³/(mn) - 2Δe` unoriented three-edge
paths. -/
theorem fnv_u4_bipartite {A B : Finset V} (hG : G.IsBipartiteWith A B) :
    (G.edgeFinset.card : ℝ) ^ 3 / ((A.card : ℝ) * (B.card : ℝ)) -
        2 * (G.maxDegree : ℝ) * G.edgeFinset.card ≤
      u4PathCount G := by
  have hwalk := fnv_u4_bipartite_oriented_walk_lower_bound G hG
  have hdeleteNat := u4_walk_le_path_add_four G hG
  have hdelete : (u4OrientedWalkCount G : ℝ) ≤
      u4OrientedPathCount G +
        4 * (G.maxDegree : ℝ) * G.edgeFinset.card := by
    exact_mod_cast hdeleteNat
  unfold u4PathCount
  calc
    (G.edgeFinset.card : ℝ) ^ 3 / ((A.card : ℝ) * (B.card : ℝ)) -
        2 * (G.maxDegree : ℝ) * G.edgeFinset.card ≤
        ((u4OrientedWalkCount G : ℝ) -
          4 * (G.maxDegree : ℝ) * G.edgeFinset.card) / 2 := by
      rw [show (G.edgeFinset.card : ℝ) ^ 3 /
          ((A.card : ℝ) * (B.card : ℝ)) -
          2 * (G.maxDegree : ℝ) * G.edgeFinset.card =
          (2 * (G.edgeFinset.card : ℝ) ^ 3 /
            ((A.card : ℝ) * (B.card : ℝ)) -
            4 * (G.maxDegree : ℝ) * G.edgeFinset.card) / 2 by ring]
      exact div_le_div_of_nonneg_right
        (sub_le_sub_right hwalk _) (by norm_num)
    _ ≤ (u4OrientedPathCount G : ℝ) / 2 := by linarith

end

end Erdos59
