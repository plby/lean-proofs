import ErdosProblems.Erdos489.CandidateAvoidance

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Erdos489

/-- Product density attached to a finite list of divisor moduli. -/
noncomputable def sieveDensity (l : List ℕ) : ℝ :=
  (l.map fun a => 1 - (a : ℝ)⁻¹).prod

lemma sieveFactor_nonneg {a : ℕ} (ha : 2 ≤ a) :
    0 ≤ 1 - (a : ℝ)⁻¹ := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hinv := inv_le_one_of_one_le₀ haR
  linarith

lemma sieveFactor_le_one (a : ℕ) : 1 - (a : ℝ)⁻¹ ≤ 1 := by
  have hinv : (0 : ℝ) ≤ (a : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg a)
  linarith

lemma sieveDensity_nonneg (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    0 ≤ sieveDensity l := by
  induction l with
  | nil => simp [sieveDensity]
  | cons a l ih =>
      unfold sieveDensity
      apply mul_nonneg
      · exact sieveFactor_nonneg (hl a (by simp))
      · apply ih
        intro b hb
        exact hl b (by simp [hb])

/-- Deleting factors from a finite sieve can only increase its density. -/
theorem sieveDensity_le_coprimePart
    (l : List ℕ) (Q : ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    sieveDensity l ≤ sieveDensity (coprimePart l Q) := by
  induction l with
  | nil => simp [sieveDensity, coprimePart]
  | cons a l ih =>
      have ha : 2 ≤ a := hl a (by simp)
      have htail : ∀ b ∈ l, 2 ≤ b := by
        intro b hb
        exact hl b (by simp [hb])
      have hih := ih htail
      have hfac0 := sieveFactor_nonneg ha
      have hfac1 := sieveFactor_le_one a
      have htail0 : 0 ≤ sieveDensity l := sieveDensity_nonneg l htail
      unfold sieveDensity
      unfold coprimePart
      rw [List.filter_cons]
      by_cases hcop : Nat.Coprime Q a
      · rw [if_pos (decide_eq_true hcop)]
        exact mul_le_mul_of_nonneg_left hih hfac0
      · have hd : decide (Nat.Coprime Q a) ≠ true :=
          fun h => hcop (of_decide_eq_true h)
        rw [if_neg hd]
        exact (mul_le_of_le_one_left htail0 hfac1).trans hih

/-- The integral product used by Heilbronn--Rohrbach divided by the modulus
product is exactly the real sieve density. -/
theorem cast_sub_prod_div_prod_eq_sieveDensity
    (l : List ℕ) (hl : ∀ a ∈ l, 2 ≤ a) :
    (((l.map fun a => a - 1).prod : ℕ) : ℝ) / (l.prod : ℝ) =
      sieveDensity l := by
  induction l with
  | nil => simp [sieveDensity]
  | cons a l ih =>
      have ha : 2 ≤ a := hl a (by simp)
      have htail : ∀ b ∈ l, 2 ≤ b := by
        intro b hb
        exact hl b (by simp [hb])
      have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
      have hlprodNat : 0 < l.prod := List.prod_pos (fun b hb => by
        have := htail b hb
        omega)
      have hlprod : (0 : ℝ) < l.prod := by exact_mod_cast hlprodNat
      rw [List.map_cons, List.prod_cons, List.prod_cons]
      norm_num only [Nat.cast_mul]
      rw [mul_div_mul_comm, ih htail]
      unfold sieveDensity
      congr 1
      rw [Nat.cast_sub (by omega)]
      field_simp [ne_of_gt hapos] <;> norm_num

/-- A positive lower bound for the full list density is also a cross-multiplied
lower bound for the integral density numerator of its coprime part. -/
theorem density_mul_coprimePart_prod_le_sub_prod
    (l : List ℕ) (Q : ℕ) (hl : ∀ a ∈ l, 2 ≤ a)
    (ρ : ℝ) (hρ : ρ ≤ sieveDensity l) :
    ρ * ((coprimePart l Q).prod : ℝ) ≤
      (((coprimePart l Q).map fun a => a - 1).prod : ℕ) := by
  let c := coprimePart l Q
  have hc : ∀ a ∈ c, 2 ≤ a := by
    intro a ha
    exact hl a (List.mem_of_mem_filter ha)
  have hprodposNat : 0 < c.prod := List.prod_pos (fun a ha => by
    have := hc a ha
    omega)
  have hprodpos : (0 : ℝ) < c.prod := by exact_mod_cast hprodposNat
  have hdens : ρ ≤ sieveDensity c :=
    hρ.trans (sieveDensity_le_coprimePart l Q hl)
  have hid := cast_sub_prod_div_prod_eq_sieveDensity c hc
  rw [← hid] at hdens
  exact (le_div_iff₀ hprodpos).mp hdens

/-- Once an interval contains at least five full candidate periods, a finite
sieve density lower bound `ρ` yields at least `ρ G/(2Q)` affine candidates. -/
theorem affineCandidates_coprimePart_linear_supply
    (l : List ℕ) (Q L G : ℕ) (hQ : 1 < Q)
    (hl : ∀ a ∈ l, 2 ≤ a) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ sieveDensity l)
    (hG : 5 * (Q * (coprimePart l Q).prod) ≤ G) :
    ρ * (G : ℝ) / (2 * (Q : ℝ)) ≤
      (((Finset.Icc L (L + G)).filter
        (affineCandidates (coprimePart l Q) Q)).card : ℝ) := by
  let c := coprimePart l Q
  let P := c.prod
  let M := Q * P
  let E := (c.map fun a => a - 1).prod
  let q := G / M
  have hc : ∀ a ∈ c, 1 < a := by
    intro a ha
    exact (hl a (List.mem_of_mem_filter ha))
  have hP : 0 < P := by
    dsimp [P]
    exact List.prod_pos (fun a ha => by
      have := hc a ha
      omega)
  have hM : 0 < M := Nat.mul_pos (by omega) hP
  have hbase := affineCandidates_interval_count_lower c Q L G hQ hc
    (by simpa [c] using coprime_coprimePart_prod l Q)
  have hG' : 5 * M ≤ G := by simpa [M, P, c] using hG
  have hq5 : 5 ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hM).2 hG'
  have hGlt : G < M * (q + 1) := by
    simpa [q] using Nat.lt_mul_div_succ G hM
  have hGbound : (G : ℝ) ≤ 2 * (M : ℝ) * ((q : ℝ) - 2) := by
    have hGltR : (G : ℝ) < ((M * (q + 1) : ℕ) : ℝ) := by exact_mod_cast hGlt
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hGltR
    have hqR : (5 : ℝ) ≤ q := by exact_mod_cast hq5
    have hMR : (0 : ℝ) ≤ M := by positivity
    nlinarith
  have hcross := density_mul_coprimePart_prod_le_sub_prod l Q hl ρ hρ
  change ρ * (P : ℝ) ≤ (E : ℕ) at hcross
  have hq2R : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hqsub : (0 : ℝ) ≤ (q : ℝ) - 2 := by linarith
  have hfirst := mul_le_mul_of_nonneg_left hGbound
    (show 0 ≤ ρ / (2 * (Q : ℝ)) by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hcross hqsub
  have htarget : ρ * (G : ℝ) / (2 * (Q : ℝ)) ≤
      ((q : ℝ) - 2) * (E : ℝ) := by
    have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
    dsimp [M] at hfirst
    norm_num only [Nat.cast_mul] at hfirst
    calc
      ρ * (G : ℝ) / (2 * (Q : ℝ)) =
          (ρ / (2 * (Q : ℝ))) * (G : ℝ) := by ring
      _ ≤ (ρ / (2 * (Q : ℝ))) *
          (2 * ((Q : ℝ) * (P : ℝ)) * ((q : ℝ) - 2)) := hfirst
      _ = (ρ * (P : ℝ)) * ((q : ℝ) - 2) := by field_simp <;> ring
      _ ≤ (E : ℝ) * ((q : ℝ) - 2) := hsecond
      _ = ((q : ℝ) - 2) * (E : ℝ) := by ring
  have hbaseR : ((((q - 2) * E : ℕ)) : ℝ) ≤
      (((Finset.Icc L (L + G)).filter
        (affineCandidates c Q)).card : ℝ) := by
    exact_mod_cast (by simpa [q, M, P, E] using hbase)
  norm_num only [Nat.cast_mul, Nat.cast_sub (show 2 ≤ q by omega)] at hbaseR
  exact htarget.trans (by simpa [c] using hbaseR)

end Erdos489
