import ErdosProblems.Erdos67.MRPerronProjectionErrorBound

/-!
# The Perron near kernel on a multiplicative progression

After the two generalized-Mangoldt variables in A.10 are fixed, the
remaining coefficient index runs through multiples of their product.  The
two multiples adjacent to the Perron endpoint cost at most one each; all
other multiples retain a reciprocal factor of the progression modulus.
-/

open scoped BigOperators
open Finset

namespace Erdos67.MRPerronNearProgression

noncomputable section

open BoundedGaps.Maynard

theorem dirichletPerronNearError_nonneg (x : ℕ) {T : ℝ}
    (hT : 0 < T) (n : ℕ) :
    0 ≤ dirichletPerronNearError x T n := by
  rw [dirichletPerronNearError]
  split_ifs
  · exact le_min (by norm_num) (by positivity)
  · rfl

theorem dirichletPerronNearError_le_one (x : ℕ) {T : ℝ}
    (hT : 0 < T) (n : ℕ) :
    dirichletPerronNearError x T n ≤ 1 := by
  rw [dirichletPerronNearError]
  split_ifs
  · exact min_le_left _ _
  · norm_num

/-- Away from the endpoint, the near kernel is bounded by its reciprocal
distance branch. -/
theorem dirichletPerronNearError_le_reciprocal
    {x n : ℕ} {T : ℝ} (hT : 0 < T) (hnx : n ≠ x) :
    dirichletPerronNearError x T n ≤
      2 * (x : ℝ) / (T * |(x : ℝ) - n|) := by
  rw [dirichletPerronNearError]
  split_ifs with hcentral
  · exact min_le_right _ _
  · have hright : 0 ≤ 2 * (x : ℝ) /
        (T * |(x : ℝ) - n|) := by
      by_cases hx : x = 0
      · simp [hx]
      · have hdist : 0 < |(x : ℝ) - n| := by
          apply abs_pos.mpr
          exact sub_ne_zero.mpr (by exact_mod_cast hnx.symm)
        positivity
    exact hright

/-- Reflection of the reciprocal sum on `[1,M]`. -/
theorem sum_Icc_reflect_inv (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M,
        (((M + 1 - k : ℕ) : ℝ))⁻¹) =
      ∑ k ∈ Finset.Icc 1 M, ((k : ℝ))⁻¹ := by
  apply Finset.sum_bij (fun k _ ↦ M + 1 - k)
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    omega
  · intro k₁ hk₁ k₂ hk₂ heq
    simp only [Finset.mem_Icc] at hk₁ hk₂
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨M + 1 - j, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro k hk
    rfl

/-- Translation of a reciprocal interval beginning at `m+2`. -/
theorem sum_Icc_sub_inv (m U : ℕ) :
    (∑ d ∈ Finset.Icc (m + 2) U,
        (((d - m - 1 : ℕ) : ℝ))⁻¹) =
      ∑ k ∈ Finset.Icc 1 (U - m - 1), ((k : ℝ))⁻¹ := by
  apply Finset.sum_bij (fun d _ ↦ d - m - 1)
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  · intro d₁ hd₁ d₂ hd₂ heq
    simp only [Finset.mem_Icc] at hd₁ hd₂
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨k + m + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro d hd
    rfl

theorem sum_Icc_inv_le_harmonic {M N : ℕ} (hMN : M ≤ N) :
    (∑ k ∈ Finset.Icc 1 M, ((k : ℝ))⁻¹) ≤ (harmonic N : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans hMN⟩
  · intro k hk hnot
    positivity

/-- The reciprocal distances of all non-adjacent multiples of `q` retain
the factor `q⁻¹`. -/
theorem sum_Icc_nonadjacent_reciprocal_le
    {x q : ℕ} (hq : 0 < q) :
    (∑ d ∈ (Finset.Icc 1 (2 * x)).filter
        (fun d ↦ d < x / q ∨ x / q + 1 < d),
        |(x : ℝ) - (d * q : ℕ)|⁻¹) ≤
      2 * (q : ℝ)⁻¹ * (harmonic (2 * x) : ℝ) := by
  let m := x / q
  have hxdiv : m * q ≤ x := Nat.div_mul_le_self x q
  have hmle : m ≤ x := by
    dsimp only [m]
    exact Nat.div_le_self _ _
  have hxlt : x < (m + 1) * q := by
    have h := Nat.lt_div_mul_add (a := x) hq
    simpa only [m, add_mul, one_mul] using h
  have hsplit :
      (Finset.Icc 1 (2 * x)).filter
          (fun d ↦ d < m ∨ m + 1 < d) =
        Finset.Icc 1 (m - 1) ∪ Finset.Icc (m + 2) (2 * x) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union]
    constructor
    · rintro ⟨hd, hleft | hright⟩
      · exact Or.inl ⟨hd.1, by omega⟩
      · exact Or.inr ⟨by omega, hd.2⟩
    · rintro (hleft | hright)
      · have hdle : d ≤ 2 * x :=
          hleft.2.trans (Nat.sub_le _ _ |>.trans (hmle.trans (by omega)))
        exact ⟨⟨hleft.1, hdle⟩, Or.inl (by omega)⟩
      · have hmone : 1 ≤ m + 2 :=
          Nat.succ_le_succ (Nat.zero_le (m + 1))
        have hdone : 1 ≤ d := hmone.trans hright.1
        have hmright : m + 1 < d :=
          (Nat.lt_succ_self (m + 1)).trans_le hright.1
        exact ⟨⟨hdone, hright.2⟩, Or.inr hmright⟩
  rw [show x / q = m by rfl, hsplit, Finset.sum_union]
  · have hleftPoint : ∀ d ∈ Finset.Icc 1 (m - 1),
        |(x : ℝ) - (d * q : ℕ)|⁻¹ ≤
          (q : ℝ)⁻¹ * (((m - d : ℕ) : ℝ))⁻¹ := by
      intro d hd
      have hdData := Finset.mem_Icc.mp hd
      have hdm : d < m := by omega
      have hdq : d * q ≤ x := (Nat.mul_le_mul_right q hdm.le).trans hxdiv
      have hdist : |(x : ℝ) - (d * q : ℕ)| = ((x - d * q : ℕ) : ℝ) := by
        rw [Nat.cast_sub hdq, abs_of_nonneg]
        exact_mod_cast Nat.zero_le (x - d * q)
      have hlower : (m - d) * q ≤ x - d * q := by
        rw [Nat.sub_mul]
        exact Nat.sub_le_sub_right hxdiv (d * q)
      rw [hdist]
      have hposNat : 0 < (m - d) * q :=
        Nat.mul_pos (Nat.sub_pos_of_lt hdm) hq
      have hpos : (0 : ℝ) < (((m - d) * q : ℕ) : ℝ) := by
        exact_mod_cast hposNat
      have hcast : (((m - d) * q : ℕ) : ℝ) ≤ (x - d * q : ℕ) := by
        exact_mod_cast hlower
      calc
        (((x - d * q : ℕ) : ℝ))⁻¹ ≤
            ((((m - d) * q : ℕ) : ℝ))⁻¹ :=
          by simpa only [one_div] using
            (one_div_le_one_div_of_le hpos hcast)
        _ = (q : ℝ)⁻¹ * (((m - d : ℕ) : ℝ))⁻¹ := by
          push_cast
          rw [mul_inv]
          ring
    have hrightPoint : ∀ d ∈ Finset.Icc (m + 2) (2 * x),
        |(x : ℝ) - (d * q : ℕ)|⁻¹ ≤
          (q : ℝ)⁻¹ * (((d - m - 1 : ℕ) : ℝ))⁻¹ := by
      intro d hd
      have hdData := Finset.mem_Icc.mp hd
      have hxdq : x ≤ d * q := by
        have : (m + 1) * q ≤ d * q := Nat.mul_le_mul_right q (by omega)
        exact hxlt.le.trans this
      have hdist : |(x : ℝ) - (d * q : ℕ)| = ((d * q - x : ℕ) : ℝ) := by
        rw [abs_sub_comm, Nat.cast_sub hxdq, abs_of_nonneg]
        exact_mod_cast Nat.zero_le (d * q - x)
      have hlower : (d - m - 1) * q ≤ d * q - x := by
        have hm1d : m + 1 ≤ d := by omega
        have heq : (d - m - 1) * q = d * q - (m + 1) * q := by
          rw [show d - m - 1 = d - (m + 1) by omega, Nat.sub_mul]
        rw [heq]
        exact Nat.sub_le_sub_left hxlt.le (d * q)
      rw [hdist]
      have hsubPos : 0 < d - m - 1 := by omega
      have hposNat : 0 < (d - m - 1) * q := Nat.mul_pos hsubPos hq
      have hpos : (0 : ℝ) < (((d - m - 1) * q : ℕ) : ℝ) := by
        exact_mod_cast hposNat
      have hcast : ((((d - m - 1) * q : ℕ) : ℝ)) ≤
          (d * q - x : ℕ) := by exact_mod_cast hlower
      calc
        (((d * q - x : ℕ) : ℝ))⁻¹ ≤
            ((((d - m - 1) * q : ℕ) : ℝ))⁻¹ :=
          by simpa only [one_div] using
            (one_div_le_one_div_of_le hpos hcast)
        _ = (q : ℝ)⁻¹ * (((d - m - 1 : ℕ) : ℝ))⁻¹ := by
          push_cast
          rw [mul_inv]
          ring
    have hleft := Finset.sum_le_sum hleftPoint
    have hright := Finset.sum_le_sum hrightPoint
    rw [← Finset.mul_sum] at hleft hright
    have hreflect :
        (∑ d ∈ Finset.Icc 1 (m - 1),
            (((m - d : ℕ) : ℝ))⁻¹) =
          ∑ k ∈ Finset.Icc 1 (m - 1), ((k : ℝ))⁻¹ := by
      by_cases hm : m = 0
      · simp [hm]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        calc
          (∑ d ∈ Finset.Icc 1 (m - 1),
              (((m - d : ℕ) : ℝ))⁻¹) =
              ∑ d ∈ Finset.Icc 1 (m - 1),
                ((((m - 1) + 1 - d : ℕ) : ℝ))⁻¹ := by
            apply Finset.sum_congr rfl
            intro d hd
            congr 3
            omega
          _ = _ := sum_Icc_reflect_inv (m - 1)
    rw [hreflect] at hleft
    rw [sum_Icc_sub_inv] at hright
    have hmle' : m - 1 ≤ 2 * x :=
      (Nat.sub_le _ _).trans (hmle.trans (by omega))
    have hrle : 2 * x - m - 1 ≤ 2 * x :=
      (Nat.sub_le _ _).trans (Nat.sub_le _ _)
    have hLH := sum_Icc_inv_le_harmonic hmle'
    have hRH := sum_Icc_inv_le_harmonic hrle
    calc
      (∑ d ∈ Finset.Icc 1 (m - 1),
          |(x : ℝ) - (d * q : ℕ)|⁻¹) +
          ∑ d ∈ Finset.Icc (m + 2) (2 * x),
            |(x : ℝ) - (d * q : ℕ)|⁻¹ ≤
        (q : ℝ)⁻¹ * (harmonic (2 * x) : ℝ) +
          (q : ℝ)⁻¹ * (harmonic (2 * x) : ℝ) :=
        add_le_add (hleft.trans (mul_le_mul_of_nonneg_left hLH (by positivity)))
          (hright.trans (mul_le_mul_of_nonneg_left hRH (by positivity)))
      _ = 2 * (q : ℝ)⁻¹ * (harmonic (2 * x) : ℝ) := by ring
  · apply Finset.disjoint_left.mpr
    intro d hdleft hdright
    simp only [Finset.mem_Icc] at hdleft hdright
    omega

/-- Summing the near kernel on the progression `q,2q,...` costs two
adjacent multiples plus a reciprocal harmonic tail. -/
theorem sum_Icc_dirichletPerronNearError_mul_le
    {x q : ℕ} (hq : 0 < q) {T : ℝ} (hT : 0 < T) :
    (∑ d ∈ Finset.Icc 1 (2 * x),
        dirichletPerronNearError x T (d * q)) ≤
      2 + (4 * (x : ℝ) / T) * (q : ℝ)⁻¹ *
        (harmonic (2 * x) : ℝ) := by
  let m := x / q
  let E : Finset ℕ := {m, m + 1} ∩ Finset.Icc 1 (2 * x)
  let R : Finset ℕ := (Finset.Icc 1 (2 * x)).filter
    (fun d ↦ d < m ∨ m + 1 < d)
  have hpartition : Finset.Icc 1 (2 * x) = E ∪ R := by
    ext d
    simp only [E, R, Finset.mem_Icc, Finset.mem_union, Finset.mem_inter,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter]
    omega
  have hdisj : Disjoint E R := by
    simp only [E, R, Finset.disjoint_left, Finset.mem_inter,
      Finset.mem_insert, Finset.mem_singleton, Finset.mem_Icc,
      Finset.mem_filter]
    omega
  rw [hpartition, Finset.sum_union hdisj]
  have hEcard : E.card ≤ 2 := by
    exact (Finset.card_le_card (Finset.inter_subset_left)).trans (by simp [E])
  have hE : (∑ d ∈ E, dirichletPerronNearError x T (d * q)) ≤ 2 := by
    calc
      (∑ d ∈ E, dirichletPerronNearError x T (d * q)) ≤
          ∑ _d ∈ E, (1 : ℝ) :=
        Finset.sum_le_sum fun d hd ↦ dirichletPerronNearError_le_one x hT _
      _ = E.card := by simp
      _ ≤ 2 := by exact_mod_cast hEcard
  have hRpoint : ∀ d ∈ R,
      dirichletPerronNearError x T (d * q) ≤
        (2 * (x : ℝ) / T) * |(x : ℝ) - (d * q : ℕ)|⁻¹ := by
    intro d hd
    have hdR := Finset.mem_filter.mp hd
    have hneq : d * q ≠ x := by
      intro heq
      have : d = m := by
        dsimp only [m]
        rw [← heq]
        simpa [mul_comm] using (Nat.mul_div_cancel_left d hq).symm
      omega
    have hbase := dirichletPerronNearError_le_reciprocal hT hneq
    calc
      dirichletPerronNearError x T (d * q) ≤
          2 * (x : ℝ) / (T * |(x : ℝ) - (d * q : ℕ)|) := hbase
      _ = (2 * (x : ℝ) / T) * |(x : ℝ) - (d * q : ℕ)|⁻¹ := by
        rw [div_eq_mul_inv, mul_inv]
        ring
  have hR := Finset.sum_le_sum hRpoint
  rw [← Finset.mul_sum] at hR
  have hrecip := sum_Icc_nonadjacent_reciprocal_le (x := x) hq
  have hR' : (∑ d ∈ R, dirichletPerronNearError x T (d * q)) ≤
      (4 * (x : ℝ) / T) * (q : ℝ)⁻¹ *
        (harmonic (2 * x) : ℝ) := by
    refine hR.trans ?_
    dsimp only [R, m]
    calc
      (2 * (x : ℝ) / T) *
          (∑ d ∈ (Finset.Icc 1 (2 * x)).filter
            (fun d ↦ d < x / q ∨ x / q + 1 < d),
            |(x : ℝ) - (d * q : ℕ)|⁻¹) ≤
        (2 * (x : ℝ) / T) *
          (2 * (q : ℝ)⁻¹ * (harmonic (2 * x) : ℝ)) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = (4 * (x : ℝ) / T) * (q : ℝ)⁻¹ *
          (harmonic (2 * x) : ℝ) := by ring
  exact (add_le_add hE hR').trans_eq (by ring)

end

end Erdos67.MRPerronNearProgression

#print axioms Erdos67.MRPerronNearProgression.sum_Icc_dirichletPerronNearError_mul_le
