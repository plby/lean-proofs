/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.TargetWeights
import ErdosProblems.Erdos163.PrunedEmbedding
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-!
# Numerical tools for the final assembly

The scale is the least positive integer whose eighth power covers the target
order.  This makes every fractional exponent in the paper an ordinary
natural power while losing only the fixed factor `256`.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace FinalTools

noncomputable def scale (n : ℕ) : ℕ :=
  Nat.find (show ∃ a : ℕ, 0 < a ∧ n ≤ a ^ 8 from
    ⟨n + 1, by omega, by
      have h : n ≤ n + 1 := by omega
      exact h.trans (Nat.le_pow (by omega : 0 < 8))⟩)

theorem scale_spec (n : ℕ) : 0 < scale n ∧ n ≤ (scale n) ^ 8 := by
  exact Nat.find_spec (show ∃ a : ℕ, 0 < a ∧ n ≤ a ^ 8 from
    ⟨n + 1, by omega, by
      have h : n ≤ n + 1 := by omega
      exact h.trans (Nat.le_pow (by omega : 0 < 8))⟩)

theorem scale_pos (n : ℕ) : 0 < scale n := (scale_spec n).1

theorem le_scale_pow (n : ℕ) : n ≤ (scale n) ^ 8 := (scale_spec n).2

theorem pred_scale_pow_lt {n : ℕ} (hn : 0 < n) :
    (scale n - 1) ^ 8 < n := by
  have hpos : 0 < scale n := scale_pos n
  by_contra hnot
  have hle : n ≤ (scale n - 1) ^ 8 := Nat.le_of_not_gt hnot
  have hpredPos : 0 < scale n - 1 ∨ scale n = 1 := by omega
  rcases hpredPos with hp | heq
  · have hmin := Nat.find_min'
      (show ∃ a : ℕ, 0 < a ∧ n ≤ a ^ 8 from
        ⟨n + 1, by omega, by
          have h : n ≤ n + 1 := by omega
          exact h.trans (Nat.le_pow (by omega : 0 < 8))⟩)
      ⟨hp, hle⟩
    change scale n ≤ scale n - 1 at hmin
    omega
  · simp [heq] at hle
    omega

theorem scale_pow_le {n : ℕ} (hn : 0 < n) :
    (scale n) ^ 8 ≤ 256 * n := by
  have hpos := scale_pos n
  have hpred := pred_scale_pow_lt hn
  by_cases hscale : scale n = 1
  · rw [hscale]
    norm_num
    omega
  · have htwo : scale n ≤ 2 * (scale n - 1) := by omega
    have hp := Nat.pow_le_pow_left htwo 8
    calc
      scale n ^ 8 ≤ (2 * (scale n - 1)) ^ 8 := hp
      _ = 256 * (scale n - 1) ^ 8 := by ring
      _ ≤ 256 * n := Nat.mul_le_mul_left 256 hpred.le

theorem scale_ge_of_pow_lt {a n : ℕ} (h : a ^ 8 < n) : a < scale n := by
  by_contra hnot
  have hs : scale n ≤ a := Nat.le_of_not_gt hnot
  have hp := Nat.pow_le_pow_left hs 8
  exact (not_lt_of_ge ((le_scale_pow n).trans hp)) h

/-- An occupied target part at layer `i` satisfies `2^i ≤ n`. -/
theorem pow_layer_le_order
    {n d : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (p : TargetParts.OccupiedPart layer c) :
    2 ^ TargetParts.layerOf p ≤ n := by
  obtain ⟨x, hx⟩ := p.property
  have hp : TargetParts.part layer c x = p := Subtype.ext hx
  rw [← hp, TargetParts.layerOf_part]
  have hz := TargetParts.pow_mul_partVertices_card_le
    H hd hdeg layer c hlayer x
  have hcard : 1 ≤ (RandomGreedy.partVertices
      (TargetParts.part layer c) x).card := by
    rw [Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
    exact ⟨x, by simp [RandomGreedy.partVertices]⟩
  calc
    2 ^ (layer x).1 = 2 ^ (layer x).1 * 1 := by simp
    _ ≤ 2 ^ (layer x).1 *
        (RandomGreedy.partVertices (TargetParts.part layer c) x).card :=
      Nat.mul_le_mul_left _ hcard
    _ ≤ n := hz

/-- With block length at least `16`, the square of the reciprocal geometric
factor of every occupied part is bounded by the eighth-root scale. -/
theorem sq_blockPow_le_scale
    {n d L : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (hL : 16 ≤ L) (p : TargetParts.OccupiedPart layer c) :
    (2 ^ (TargetParts.layerOf p / L)) ^ 2 ≤ scale n := by
  let b := TargetParts.layerOf p / L
  have hLb : L * b ≤ TargetParts.layerOf p := by
    exact Nat.mul_div_le _ _
  have h16b : 16 * b ≤ TargetParts.layerOf p :=
    (Nat.mul_le_mul_right b hL).trans (by simpa [Nat.mul_comm] using hLb)
  have hp16 : (2 ^ b) ^ 16 ≤ 2 ^ TargetParts.layerOf p := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by simpa [mul_comm] using h16b)
  have hpn : (2 ^ b) ^ 16 ≤ n :=
    hp16.trans (pow_layer_le_order H hd hdeg layer c hlayer p)
  by_contra hnot
  have hlt : scale n < (2 ^ b) ^ 2 := Nat.lt_of_not_ge hnot
  have hp8 := Nat.pow_le_pow_left hlt.le 8
  have hscaleN := le_scale_pow n
  have : scale n ^ 8 < (2 ^ b) ^ 16 := by
    calc
      scale n ^ 8 < ((2 ^ b) ^ 2) ^ 8 :=
        Nat.pow_lt_pow_left hlt (by omega)
      _ = (2 ^ b) ^ 16 := by ring
  omega

theorem mass_sq_mul_scale_ge
    {n d L Q : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (hL : 16 ≤ L) (hQ : 0 < Q)
    (p : TargetParts.OccupiedPart layer c) :
    (1 : ℝ) ≤ (Q : ℝ) ^ 2 * scale n * (TargetWeights.mass L Q p) ^ 2 := by
  have hb := sq_blockPow_le_scale H hd hdeg layer c hlayer hL p
  let B : ℝ := (2 : ℝ) ^ (TargetParts.layerOf p / L)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hbR : B ^ 2 ≤ (scale n : ℝ) := by
    dsimp [B]
    exact_mod_cast hb
  calc
    (1 : ℝ) ≤ (scale n : ℝ) / B ^ 2 :=
      (le_div_iff₀ (pow_pos hBpos 2)).2 (by simpa using hbR)
    _ = (Q : ℝ) ^ 2 * scale n * (TargetWeights.mass L Q p) ^ 2 := by
      unfold TargetWeights.mass
      dsimp [B]
      field_simp

/-- Collective form of the block estimate.  The crucial point is that the
block length is `16D`: for at most `D` coordinates, the whole reciprocal
mass loses only one square-root-scale factor, not one such factor per
coordinate. -/
theorem prod_mass_sq_mul_scale_ge
    {I : Type*} [Fintype I] {n d L Q D : ℕ}
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (hD : 0 < D) (hcard : Fintype.card I ≤ D) (hL : 16 * D ≤ L)
    (hQ : 0 < Q) (p : I → TargetParts.OccupiedPart layer c) :
    (1 : ℝ) ≤ (Q : ℝ) ^ (2 * D) * scale n *
      (∏ i, TargetWeights.mass L Q (p i)) ^ 2 := by
  by_cases hI : IsEmpty I
  · letI : IsEmpty I := hI
    have huniv : (Finset.univ : Finset I) = ∅ := by
      ext i
      exact isEmptyElim i
    change (1 : ℝ) ≤ (Q : ℝ) ^ (2 * D) * scale n *
      (∏ i ∈ (Finset.univ : Finset I), TargetWeights.mass L Q (p i)) ^ 2
    rw [huniv]
    simp only [Finset.prod_empty, one_pow, mul_one]
    have hp : 1 ≤ Q ^ (2 * D) * scale n := by
      have : 0 < Q ^ (2 * D) * scale n :=
        Nat.mul_pos (pow_pos hQ _) (scale_pos n)
      omega
    exact_mod_cast hp
  · haveI : Nonempty I := not_isEmpty_iff.mp hI
    have hn : 0 < n := by
      obtain ⟨i⟩ := ‹Nonempty I›
      obtain ⟨x, -⟩ := (p i).property
      exact x.pos
    let b : I → ℕ := fun i => TargetParts.layerOf (p i) / L
    let X : ℕ := ∏ i, 2 ^ b i
    have honeX : 1 ≤ X := by
      apply Finset.one_le_prod
      intro i hi
      exact one_le_pow₀ (by omega)
    have honeN : 1 ≤ n := hn
    have hterm : ∀ i, (2 ^ b i) ^ L ≤ n := by
      intro i
      have hmul : L * b i ≤ TargetParts.layerOf (p i) := by
        dsimp [b]
        exact Nat.mul_div_le _ _
      calc
        (2 ^ b i) ^ L = 2 ^ (b i * L) := by rw [pow_mul]
        _ ≤ 2 ^ TargetParts.layerOf (p i) :=
          Nat.pow_le_pow_right (by omega) (by simpa [mul_comm] using hmul)
        _ ≤ n := pow_layer_le_order H hd hdeg layer c hlayer (p i)
    have hXL : X ^ L ≤ n ^ Fintype.card I := by
      calc
        X ^ L = ∏ i, (2 ^ b i) ^ L := by simp [X, Finset.prod_pow]
        _ ≤ ∏ _i : I, n := Finset.prod_le_prod (fun _ _ => by omega)
          (fun i hi => hterm i)
        _ = n ^ Fintype.card I := by simp
    have hX16D : X ^ (16 * D) ≤ X ^ L :=
      Nat.pow_le_pow_right honeX hL
    have hncard : n ^ Fintype.card I ≤ n ^ D :=
      Nat.pow_le_pow_right honeN hcard
    have hX16 : X ^ 16 ≤ n := by
      apply (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hD)).1
      calc
        (X ^ 16) ^ D = X ^ (16 * D) := by rw [pow_mul]
        _ ≤ X ^ L := hX16D
        _ ≤ n ^ Fintype.card I := hXL
        _ ≤ n ^ D := hncard
    have hXsq : X ^ 2 ≤ scale n := by
      apply (Nat.pow_le_pow_iff_left (by omega : 8 ≠ 0)).1
      calc
        (X ^ 2) ^ 8 = X ^ 16 := by ring
        _ ≤ n := hX16
        _ ≤ scale n ^ 8 := le_scale_pow n
    have hQpow : Q ^ (2 * Fintype.card I) ≤ Q ^ (2 * D) := by
      exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 hcard)
    have hdenNat : (Q ^ Fintype.card I * X) ^ 2 ≤
        Q ^ (2 * D) * scale n := by
      calc
        (Q ^ Fintype.card I * X) ^ 2 =
            Q ^ (2 * Fintype.card I) * X ^ 2 := by ring
        _ ≤ Q ^ (2 * D) * scale n := Nat.mul_le_mul hQpow hXsq
    have hmass : (∏ i, TargetWeights.mass L Q (p i)) =
        1 / ((Q : ℝ) ^ Fintype.card I * (X : ℝ)) := by
      simp_rw [TargetWeights.mass, one_div]
      change (∏ i ∈ (Finset.univ : Finset I),
        ((Q : ℝ) * 2 ^ (TargetParts.layerOf (p i) / L))⁻¹) = _
      rw [Finset.prod_inv_distrib, Finset.prod_mul_distrib,
        Finset.prod_const]
      simp only [Finset.card_univ]
      congr 1
      congr 1
      exact_mod_cast (rfl : (∏ i, 2 ^ b i) = X)
    rw [hmass]
    have hdenPos : (0 : ℝ) < (Q : ℝ) ^ Fintype.card I * X := by
      positivity
    have hdenR : (((Q : ℝ) ^ Fintype.card I * X) ^ 2) ≤
        (Q : ℝ) ^ (2 * D) * scale n := by
      exact_mod_cast hdenNat
    rw [div_pow]
    have : (1 : ℝ) ≤
        ((Q : ℝ) ^ (2 * D) * scale n) /
          (((Q : ℝ) ^ Fintype.card I * X) ^ 2) :=
      (le_div_iff₀ (pow_pos hdenPos 2)).2 (by simpa using hdenR)
    convert this using 1 <;> field_simp <;> ring

/-- Exponential decay beats any fixed polynomial along natural numbers. -/
theorem eventually_const_mul_pow_mul_exp_neg_lt
    (K : ℝ) (p : ℕ) {c δ : ℝ} (hK : 0 ≤ K) (hc : 0 < c)
    (hδ : 0 < δ) :
    ∃ a₀ : ℕ, ∀ a : ℕ, a₀ ≤ a →
      K * (a : ℝ) ^ p * Real.exp (-c * a) < δ := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (p : ℝ) c hc
  have htNat := ht.comp tendsto_natCast_atTop_atTop
  have hevent : (∀ᶠ a : ℕ in Filter.atTop,
      K * (a : ℝ) ^ p * Real.exp (-c * a) < δ) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => K) Filter.atTop (nhds K) :=
      tendsto_const_nhds
    have hmul := hconst.mul htNat
    have hzero : K * 0 < δ := by simpa using hδ
    have := hmul.eventually (gt_mem_nhds hzero)
    filter_upwards [this] with a ha
    simpa [Real.rpow_natCast, mul_assoc] using ha
  exact Filter.eventually_atTop.1 hevent

theorem sum_exp_neg_le_card_mul {K : Type*} [Fintype K]
    (f : K → ℝ) (E : ℝ) (h : ∀ k, E ≤ f k) :
    ∑ k, Real.exp (-f k) ≤ Fintype.card K * Real.exp (-E) := by
  calc
    ∑ k, Real.exp (-f k) ≤ ∑ _k : K, Real.exp (-E) := by
      exact Finset.sum_le_sum fun k _ => Real.exp_le_exp.mpr (neg_le_neg (h k))
    _ = Fintype.card K * Real.exp (-E) := by simp

theorem card_samplingTest_le
    {N D : ℕ} {P X : Type*} [Fintype P] [Fintype X]
    (coord : X → Type*) [∀ x, Fintype (coord x)]
    [∀ x, DecidableEq (coord x)]
    (base : ∀ x, coord x → Finset (Fin N)) (hN : 1 ≤ N)
    (hcoord : ∀ x, Fintype.card (coord x) ≤ D) :
    Fintype.card (HostPartition.SamplingTest (P := P) X coord base) ≤
      Fintype.card P + Fintype.card X * N ^ D := by
  have hfamily : ∀ x,
      (FiniteDefect.familyTuples (base x)).card ≤ N ^ D := by
    intro x
    rw [FiniteDefect.card_familyTuples]
    calc
      ∏ i, (base x i).card ≤ ∏ _i : coord x, N := by
        exact Finset.prod_le_prod (fun _ _ => by omega) fun i _ =>
          by simpa using Finset.card_le_univ (base x i)
      _ = N ^ Fintype.card (coord x) := by simp
      _ ≤ N ^ D := Nat.pow_le_pow_right hN (hcoord x)
  rw [Fintype.card_sum, Fintype.card_sigma]
  gcongr
  calc
    ∑ x : X, Fintype.card {g // g ∈ FiniteDefect.familyTuples (base x)} ≤
        ∑ _x : X, N ^ D := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [Fintype.card_coe] using hfamily x
    _ = Fintype.card X * N ^ D := by simp

open scoped BigOperators

theorem main_term_le
    {D k C T a : ℕ} {ε μ : ℝ}
    (hk : k ≤ D) (hC : 1 ≤ C) (hT : 2 ≤ T) (ha : 0 < a)
    (hε : 0 ≤ ε) (hμ : 0 ≤ μ)
    (hsmall : 4 * ε * (C : ℝ) ^ D ≤ μ) :
    (((C * a ^ 8 : ℕ) : ℝ) ^ k * ε) ≤
      μ / 4 * ((((T * a ^ 8 : ℕ) : ℝ) / 2) ^ k) := by
  have hCpow : (C : ℝ) ^ k ≤ (C : ℝ) ^ D := by
    exact_mod_cast Nat.pow_le_pow_right hC hk
  have hsmall' : ε * (C : ℝ) ^ D ≤ μ / 4 := by linarith
  have hcoef : (1 : ℝ) ≤ (T : ℝ) / 2 := by
    exact (le_div_iff₀ (by norm_num)).2 (by exact_mod_cast hT)
  have hbase : (a : ℝ) ^ 8 ≤ ((T * a ^ 8 : ℕ) : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    push_cast
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hTR
      (show (0 : ℝ) ≤ (a : ℝ) ^ 8 by positivity)
  have hbasepow : (a : ℝ) ^ (8 * k) ≤
      (((T * a ^ 8 : ℕ) : ℝ) / 2) ^ k := by
    calc
      (a : ℝ) ^ (8 * k) = (a ^ 8) ^ k := by rw [pow_mul]
      _ ≤ (((T * a ^ 8 : ℕ) : ℝ) / 2) ^ k :=
        pow_le_pow_left₀ (by positivity) hbase k
  calc
    (((C * a ^ 8 : ℕ) : ℝ) ^ k * ε) =
        (ε * (C : ℝ) ^ k) * a ^ (8 * k) := by
      push_cast
      rw [mul_pow, ← pow_mul]
      ring
    _ ≤ (ε * (C : ℝ) ^ D) * a ^ (8 * k) := by
      gcongr
    _ ≤ (μ / 4) * a ^ (8 * k) := by gcongr
    _ ≤ μ / 4 * ((((T * a ^ 8 : ℕ) : ℝ) / 2) ^ k) := by
      exact mul_le_mul_of_nonneg_left hbasepow (div_nonneg hμ (by norm_num))

theorem diagonal_term_le
    {D k C T Q a : ℕ} {ε μ qprod : ℝ}
    (hk0 : 0 < k) (hk : k ≤ D) (hC : 1 ≤ C) (hT : 2 ≤ T)
    (hQ : 0 < Q) (ha : 0 < a) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hμ : 0 < μ) (hq : 0 < qprod)
    (hmass : (1 : ℝ) ≤ (Q : ℝ) ^ (2 * D) * a * qprod ^ 2)
    (hK : 16 * (D : ℝ) ^ 4 * (C : ℝ) ^ (2 * D) *
        (Q : ℝ) ^ (2 * D) / μ ^ 2 ≤ (a : ℝ) ^ 15) :
    (k : ℝ) ^ 2 *
        ((((C * a ^ 8 : ℕ) : ℝ) ^ (k - 1)) * ε) ≤
      μ / 4 * qprod * ((((T * a ^ 8 : ℕ) : ℝ) / 2) ^ k) := by
  let U : ℝ := (D : ℝ) ^ 2 * (C : ℝ) ^ D *
    (a : ℝ) ^ (8 * (k - 1))
  let V : ℝ := μ / 4 * qprod * (a : ℝ) ^ (8 * k)
  have hD0 : 0 < D := hk0.trans_le hk
  have hDsq : (k : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hk) 2
  have hCpow : (C : ℝ) ^ (k - 1) ≤ (C : ℝ) ^ D := by
    exact_mod_cast Nat.pow_le_pow_right hC (by omega : k - 1 ≤ D)
  have hdiagU : (k : ℝ) ^ 2 *
      ((((C * a ^ 8 : ℕ) : ℝ) ^ (k - 1)) * ε) ≤ U := by
    calc
      (k : ℝ) ^ 2 * ((((C * a ^ 8 : ℕ) : ℝ) ^ (k - 1)) * ε) =
          ((k : ℝ) ^ 2 * (C : ℝ) ^ (k - 1) * ε) *
            a ^ (8 * (k - 1)) := by
        push_cast
        rw [mul_pow, ← pow_mul]
        ring
      _ ≤ (((D : ℝ) ^ 2 * (C : ℝ) ^ D) * 1) *
          a ^ (8 * (k - 1)) := by gcongr
      _ = U := by simp [U]
  have hbase : (a : ℝ) ^ 8 ≤ ((T * a ^ 8 : ℕ) : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    push_cast
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hTR
      (show (0 : ℝ) ≤ (a : ℝ) ^ 8 by positivity)
  have hbasepow : (a : ℝ) ^ (8 * k) ≤
      (((T * a ^ 8 : ℕ) : ℝ) / 2) ^ k := by
    calc
      (a : ℝ) ^ (8 * k) = (a ^ 8) ^ k := by rw [pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase k
  have hK' : 16 * (D : ℝ) ^ 4 * (C : ℝ) ^ (2 * D) *
      (Q : ℝ) ^ (2 * D) ≤ (a : ℝ) ^ 15 * μ ^ 2 := by
    exact (div_le_iff₀ (sq_pos_of_pos hμ)).1 hK
  let S : ℝ := (a : ℝ) ^ (16 * (k - 1) + 1)
  have hKS := mul_le_mul_of_nonneg_right hK' (show 0 ≤ S by positivity)
  have hcore : 16 * (Q : ℝ) ^ (2 * D) * a * U ^ 2 ≤
      μ ^ 2 * (a : ℝ) ^ (16 * k) := by
    calc
      16 * (Q : ℝ) ^ (2 * D) * a * U ^ 2 =
          (16 * (D : ℝ) ^ 4 * (C : ℝ) ^ (2 * D) *
            (Q : ℝ) ^ (2 * D)) * S := by
        dsimp [U, S]
        rw [show ((D : ℝ) ^ 2 * C ^ D * a ^ (8 * (k - 1))) ^ 2 =
            D ^ 4 * C ^ (2 * D) * a ^ (16 * (k - 1)) by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
          ring]
        simp only [S, pow_succ]
        ring
      _ ≤ ((a : ℝ) ^ 15 * μ ^ 2) * S := hKS
      _ = μ ^ 2 * (a : ℝ) ^ (16 * k) := by
        dsimp [S]
        rw [show (a : ℝ) ^ 15 * μ ^ 2 * a ^ (16 * (k - 1) + 1) =
            μ ^ 2 * (a ^ 15 * a ^ (16 * (k - 1) + 1)) by ring,
          ← pow_add]
        have hexp : 15 + (16 * (k - 1) + 1) = 16 * k := by omega
        rw [hexp]
  have hQA : 0 < (Q : ℝ) ^ (2 * D) * a := by positivity
  have hbig :
      ((Q : ℝ) ^ (2 * D) * a) * (16 * U ^ 2) ≤
        ((Q : ℝ) ^ (2 * D) * a) *
          (μ ^ 2 * (a : ℝ) ^ (16 * k) * qprod ^ 2) := by
    calc
      ((Q : ℝ) ^ (2 * D) * a) * (16 * U ^ 2) =
          16 * (Q : ℝ) ^ (2 * D) * a * U ^ 2 := by ring
      _ ≤ μ ^ 2 * (a : ℝ) ^ (16 * k) := hcore
      _ ≤ μ ^ 2 * (a : ℝ) ^ (16 * k) *
          ((Q : ℝ) ^ (2 * D) * a * qprod ^ 2) := by
        exact le_mul_of_one_le_right (by positivity) hmass
      _ = ((Q : ℝ) ^ (2 * D) * a) *
          (μ ^ 2 * (a : ℝ) ^ (16 * k) * qprod ^ 2) := by ring
  have hcancel : 16 * U ^ 2 ≤
      μ ^ 2 * (a : ℝ) ^ (16 * k) * qprod ^ 2 :=
    (mul_le_mul_iff_of_pos_left hQA).mp hbig
  have hUVsq : U ^ 2 ≤ V ^ 2 := by
    have haPow : (a : ℝ) ^ (16 * k) = ((a : ℝ) ^ (8 * k)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    dsimp [V]
    rw [haPow] at hcancel
    nlinarith [hcancel]
  have hU0 : 0 ≤ U := by positivity
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hUV : U ≤ V := by nlinarith
  calc
    (k : ℝ) ^ 2 * ((((C * a ^ 8 : ℕ) : ℝ) ^ (k - 1)) * ε) ≤ U := hdiagU
    _ ≤ V := hUV
    _ ≤ μ / 4 * qprod * ((((T * a ^ 8 : ℕ) : ℝ) / 2) ^ k) := by
      exact mul_le_mul_of_nonneg_left hbasepow
        (mul_nonneg (div_nonneg hμ.le (by norm_num)) hq.le)

/-- The two all-direction moment contributions, together with half of the
available product budget, fit inside the product budget after pruning. -/
theorem normalized_estimate
    {I : Type*} [Fintype I]
    {D C T Q a N τ : ℕ} {ε μ : ℝ}
    (q : I → ℝ) (B : I → ℕ)
    (hk : Fintype.card I ≤ D) (hC : 1 ≤ C) (hT : 2 ≤ T)
    (hQ : 0 < Q) (ha : 0 < a) (hN : N = C * a ^ 8)
    (hτ : τ = T * a ^ 8) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hμ : 0 < μ) (hq : ∀ i, 0 < q i) (hB : ∀ i, τ ≤ B i)
    (hmainSmall : 4 * ε * (C : ℝ) ^ D ≤ μ)
    (hmass : (1 : ℝ) ≤ (Q : ℝ) ^ (2 * D) * a * (∏ i, q i) ^ 2)
    (hdiag : 16 * (D : ℝ) ^ 4 * (C : ℝ) ^ (2 * D) *
      (Q : ℝ) ^ (2 * D) / μ ^ 2 ≤ (a : ℝ) ^ 15) :
    (∏ i, q i) * ((N : ℝ) ^ Fintype.card I * ε) +
        (Fintype.card I : ℝ) ^ 2 *
          ((N : ℝ) ^ (Fintype.card I - 1) * ε) +
      μ / 2 * ∏ i, q i * (τ : ℝ) / 2 ≤
        μ * ∏ i, q i * (B i : ℝ) / 2 := by
  subst N
  subst τ
  let k := Fintype.card I
  let qprod : ℝ := ∏ i, q i
  let minProd : ℝ := ∏ i, q i * ((T * a ^ 8 : ℕ) : ℝ) / 2
  let actualProd : ℝ := ∏ i, q i * (B i : ℝ) / 2
  have hqprod : 0 < qprod := by
    dsimp [qprod]
    exact Finset.prod_pos fun i _ => hq i
  have hminEq : minProd = qprod *
      (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) := by
    dsimp [minProd, qprod, k]
    simp_rw [show ∀ i : I,
      q i * ((T * a ^ 8 : ℕ) : ℝ) / 2 =
        q i * ((((T * a ^ 8 : ℕ) : ℝ) / 2)) by
        intro i
        ring]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
  have hactual : minProd ≤ actualProd := by
    dsimp [minProd, actualProd]
    apply Finset.prod_le_prod
    · intro i hi
      exact div_nonneg (mul_nonneg (hq i).le (by positivity)) (by norm_num)
    · intro i hi
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hB i) (hq i).le
  have hmain : (((C * a ^ 8 : ℕ) : ℝ) ^ k * ε) ≤
      μ / 4 * (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) :=
    main_term_le hk hC hT ha hε hμ.le hmainSmall
  have hcollision : (k : ℝ) ^ 2 *
      ((((C * a ^ 8 : ℕ) : ℝ) ^ (k - 1)) * ε) ≤
      μ / 4 * qprod *
        (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) := by
    by_cases hk0 : k = 0
    · have hzero : (k : ℝ) ^ 2 = 0 := by rw [hk0]; norm_num
      have hone : (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) = 1 := by
        rw [hk0]
        simp
      rw [hzero, zero_mul, hone, mul_one]
      exact mul_nonneg (div_nonneg hμ.le (by norm_num)) hqprod.le
    · exact diagonal_term_le (Nat.pos_of_ne_zero hk0) hk hC hT hQ ha hε hε1
        hμ hqprod hmass hdiag
  have hmeanHalf : qprod *
        (((C * a ^ 8 : ℕ) : ℝ) ^ k * ε) +
      (k : ℝ) ^ 2 *
        ((((C * a ^ 8 : ℕ) : ℝ) ^ (k - 1)) * ε) ≤
      μ / 2 * minProd := by
    rw [hminEq]
    calc
      qprod * (((C * a ^ 8 : ℕ) : ℝ) ^ k * ε) +
          (k : ℝ) ^ 2 *
            ((((C * a ^ 8 : ℕ) : ℝ) ^ (k - 1)) * ε) ≤
          qprod * (μ / 4 * (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k)) +
            μ / 4 * qprod *
              (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) :=
        add_le_add (mul_le_mul_of_nonneg_left hmain hqprod.le) hcollision
      _ = μ / 2 * (qprod *
          (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k)) := by ring
  change qprod * (((C * a ^ 8 : ℕ) : ℝ) ^ k * ε) +
      (k : ℝ) ^ 2 * ((((C * a ^ 8 : ℕ) : ℝ) ^ (k - 1)) * ε) +
      μ / 2 * minProd ≤ μ * actualProd
  calc
    qprod * (((C * a ^ 8 : ℕ) : ℝ) ^ k * ε) +
        (k : ℝ) ^ 2 * ((((C * a ^ 8 : ℕ) : ℝ) ^ (k - 1)) * ε) +
        μ / 2 * minProd ≤
        μ / 2 * minProd + μ / 2 * minProd := add_le_add hmeanHalf le_rfl
    _ = μ * minProd := by ring
    _ ≤ μ * actualProd := mul_le_mul_of_nonneg_left hactual hμ.le

theorem active_exp_ge {Q a A : ℕ} {q : ℝ}
    (hQ : 0 < Q) (ha : 0 < a) (hq : 0 < q)
    (hmass : (1 : ℝ) ≤ (Q : ℝ) ^ 2 * a * q ^ 2)
    (hA : (a : ℝ) ^ 6 / 2 ≤ (A : ℝ)) :
    (1 / (4 * (Q : ℝ) ^ 2)) * a ≤
      2 * (q * (A : ℝ) / 2) ^ 2 / (A : ℝ) := by
  have hApos : (0 : ℝ) < A := by
    have : (0 : ℝ) < (a : ℝ) ^ 6 / 2 := by positivity
    linarith
  have hmass' : (1 : ℝ) / ((Q : ℝ) ^ 2 * a) ≤ q ^ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (Q : ℝ) ^ 2 * a)).2
    calc
      (1 : ℝ) ≤ (Q : ℝ) ^ 2 * a * q ^ 2 := hmass
      _ = q ^ 2 * ((Q : ℝ) ^ 2 * a) := by ring
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a from ha)
  have ha6 : (a : ℝ) ≤ (a : ℝ) ^ 6 := by
    simpa using (by exact_mod_cast
      (Nat.pow_le_pow_right (show 1 ≤ a from ha) (by omega : 1 ≤ 6)) :
        (a : ℝ) ^ 1 ≤ (a : ℝ) ^ 6)
  rw [show 2 * (q * (A : ℝ) / 2) ^ 2 / (A : ℝ) = q ^ 2 * A / 2 by
    field_simp]
  calc
    (1 / (4 * (Q : ℝ) ^ 2)) * a ≤
        (1 / ((Q : ℝ) ^ 2 * a)) * ((a : ℝ) ^ 6 / 2) / 2 := by
      field_simp
      nlinarith [sq_nonneg ((a : ℝ) ^ 2 - 1)]
    _ ≤ q ^ 2 * ((a : ℝ) ^ 6 / 2) / 2 := by gcongr
    _ ≤ q ^ 2 * A / 2 := by gcongr

theorem size_exp_ge {Q a N : ℕ} {q : ℝ}
    (hQ : 0 < Q) (ha : 0 < a) (hq : 0 < q)
    (hmass : (1 : ℝ) ≤ (Q : ℝ) ^ 2 * a * q ^ 2)
    (hN : (a : ℝ) ^ 8 ≤ (N : ℝ)) :
    (1 / (4 * (Q : ℝ) ^ 2)) * a ≤
      2 * (q * (N : ℝ)) ^ 2 / (N : ℝ) := by
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℝ) < (a : ℝ) ^ 8 := by positivity
    linarith
  have hmass' : (1 : ℝ) / ((Q : ℝ) ^ 2 * a) ≤ q ^ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (Q : ℝ) ^ 2 * a)).2
    calc
      (1 : ℝ) ≤ (Q : ℝ) ^ 2 * a * q ^ 2 := hmass
      _ = q ^ 2 * ((Q : ℝ) ^ 2 * a) := by ring
  have ha8 : (a : ℝ) ≤ (a : ℝ) ^ 8 := by
    simpa using (by exact_mod_cast
      (Nat.pow_le_pow_right (show 1 ≤ a from ha) (by omega : 1 ≤ 8)) :
        (a : ℝ) ^ 1 ≤ (a : ℝ) ^ 8)
  rw [show 2 * (q * (N : ℝ)) ^ 2 / (N : ℝ) = 2 * q ^ 2 * N by
    field_simp]
  have ha2 : (a : ℝ) ^ 2 ≤ (a : ℝ) ^ 8 :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ a from ha)) (by omega)
  have ha6one : (1 : ℝ) ≤ (a : ℝ) ^ 6 :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ a from ha))
  calc
    (1 / (4 * (Q : ℝ) ^ 2)) * a ≤
        2 * (1 / ((Q : ℝ) ^ 2 * a)) * (a : ℝ) ^ 8 := by
      field_simp
      nlinarith
    _ ≤ 2 * q ^ 2 * (a : ℝ) ^ 8 := by gcongr
    _ ≤ 2 * q ^ 2 * N := by gcongr

theorem tail_exp_ge
    {D k C T Q a lam : ℕ} {μ qprod : ℝ}
    (hk : k ≤ D) (hC : 0 < C) (hT : 2 ≤ T) (hQ : 0 < Q)
    (ha : 0 < a) (hlam : 0 < lam) (hμ : 0 < μ) (hq : 0 < qprod)
    (hmass : (1 : ℝ) ≤ (Q : ℝ) ^ (2 * D) * a * qprod ^ 2) :
    (μ ^ 2 / (2 * (C : ℝ) * (Q : ℝ) ^ (2 * D) *
        ((lam : ℝ) ^ 2 + 1))) * a ≤
      2 * (μ / 2 * qprod *
        (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k)) ^ 2 /
        (((C * a ^ 8 : ℕ) : ℝ) *
          (if k = 0 then ((a : ℝ)⁻¹ ^ 8)
            else (lam : ℝ) * a ^ (8 * k - 5)) ^ 2) := by
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hC
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hlampos : (0 : ℝ) < lam := by exact_mod_cast hlam
  have hmass' : (1 : ℝ) / ((Q : ℝ) ^ (2 * D) * a) ≤ qprod ^ 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (Q : ℝ) ^ (2 * D) * a)).2
    calc
      (1 : ℝ) ≤ (Q : ℝ) ^ (2 * D) * a * qprod ^ 2 := hmass
      _ = qprod ^ 2 * ((Q : ℝ) ^ (2 * D) * a) := by ring
  have hbase : (a : ℝ) ^ 8 ≤ ((T * a ^ 8 : ℕ) : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    push_cast
    have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT
    simpa [mul_comm] using mul_le_mul_of_nonneg_right hTR
      (show (0 : ℝ) ≤ (a : ℝ) ^ 8 by positivity)
  have hbasepow : (a : ℝ) ^ (8 * k) ≤
      (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) := by
    calc
      (a : ℝ) ^ (8 * k) = (a ^ 8) ^ k := by rw [pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hbase k
  by_cases hk0 : k = 0
  · subst k
    simp only [if_pos, pow_zero, mul_one]
    have ha8_14 : (a : ℝ) ^ 8 ≤ (a : ℝ) ^ 14 :=
      pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ a from ha)) (by omega)
    have hlamSq : (1 : ℝ) ≤ (lam : ℝ) ^ 2 + 1 := by
      nlinarith [sq_nonneg (lam : ℝ)]
    have hcross : (C : ℝ) * a ^ 8 ≤
        C * Q ^ (2 * D) * (lam ^ 2 + 1) * a ^ 15 * qprod ^ 2 := by
      calc
        (C : ℝ) * a ^ 8 ≤ C * a ^ 14 :=
          mul_le_mul_of_nonneg_left ha8_14 hCpos.le
        _ = C * 1 * a ^ 14 * 1 := by ring
        _ ≤ C * (lam ^ 2 + 1) * a ^ 14 *
            (Q ^ (2 * D) * a * qprod ^ 2) := by gcongr
        _ = C * Q ^ (2 * D) * (lam ^ 2 + 1) * a ^ 15 * qprod ^ 2 := by
          ring
    field_simp
    simpa only [Nat.cast_mul, Nat.cast_pow] using hcross
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    rw [if_neg hk0]
    have hlamSq : (lam : ℝ) ^ 2 ≤ (lam : ℝ) ^ 2 + 1 := by linarith
    have hpowRel : (a : ℝ) ^ (16 * k) =
        (a : ℝ) ^ 2 * (a : ℝ) ^ (2 * (8 * k - 5) + 8) := by
      rw [← pow_add]
      congr 1
      omega
    have hbaseSq : (a : ℝ) ^ (16 * k) ≤
        (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) ^ 2 := by
      calc
        (a : ℝ) ^ (16 * k) = (a ^ (8 * k)) ^ 2 := by
          rw [← pow_mul]
          congr 1
          omega
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hbasepow 2
    have hcombined : (a : ℝ) ^ (16 * k) ≤
        (Q ^ (2 * D) * a * qprod ^ 2) *
          (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) ^ 2 := by
      calc
        (a : ℝ) ^ (16 * k) ≤
            (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) ^ 2 := hbaseSq
        _ = 1 * (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) ^ 2 := by ring
        _ ≤ (Q ^ (2 * D) * a * qprod ^ 2) *
            (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) ^ 2 := by gcongr
    have hcombined' : (a : ℝ) ^ (16 * k) ≤
        (Q ^ (2 * D) * a * qprod ^ 2) *
          ((((T : ℝ) * a ^ 8 / 2) ^ k) ^ 2) := by
      simpa only [Nat.cast_mul, Nat.cast_pow] using hcombined
    have hcut : (a : ℝ) ^ 10 * (a ^ (8 * k - 5)) ^ 2 = a ^ (16 * k) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    have hcrossMul : (a : ℝ) *
        (lam ^ 2 * a * ((C * a ^ 8 : ℕ) : ℝ) * (a ^ (8 * k - 5)) ^ 2) ≤
        a * (C * Q ^ (2 * D) * (lam ^ 2 + 1) * qprod ^ 2 *
          (((((T * a ^ 8 : ℕ) : ℝ) / 2)) ^ k) ^ 2) := by
      push_cast
      calc
        (a : ℝ) * (lam ^ 2 * a * (C * a ^ 8) *
            (a ^ (8 * k - 5)) ^ 2) = C * lam ^ 2 * a ^ (16 * k) := by
          rw [show (a : ℝ) * (lam ^ 2 * a * (C * a ^ 8) *
              (a ^ (8 * k - 5)) ^ 2) =
              C * lam ^ 2 * (a ^ 10 * (a ^ (8 * k - 5)) ^ 2) by ring,
            hcut]
        _ ≤ C * (lam ^ 2 + 1) *
            ((Q ^ (2 * D) * a * qprod ^ 2) *
              ((((T : ℝ) * a ^ 8 / 2) ^ k) ^ 2)) := by gcongr
        _ = a * (C * Q ^ (2 * D) * (lam ^ 2 + 1) * qprod ^ 2 *
            ((((T : ℝ) * a ^ 8 / 2) ^ k) ^ 2)) := by ring
    have hcross := (mul_le_mul_iff_of_pos_left hapos).mp hcrossMul
    field_simp
    exact hcross


theorem three_exp_sums_lt_one
    {K P X : Type*} [Fintype K] [Fintype P] [Fintype X]
    (fK : K → ℝ) (fP : P → ℝ) (fX : X → ℝ)
    {a pow : ℕ} {c1 c3 A1 A2 A3 : ℝ}
    (hK : (Fintype.card K : ℝ) ≤ A1 * (a : ℝ) ^ pow)
    (hP : (Fintype.card P : ℝ) ≤ A2 * (a : ℝ) ^ pow)
    (hX : (Fintype.card X : ℝ) ≤ A3 * (a : ℝ) ^ pow)
    (hfK : ∀ k, c1 * a ≤ fK k)
    (hfP : ∀ p, c1 * a ≤ fP p)
    (hfX : ∀ x, c3 * a ≤ fX x)
    (ha1 : A1 * (a : ℝ) ^ pow * Real.exp (-c1 * a) < 1 / 3)
    (ha2 : A2 * (a : ℝ) ^ pow * Real.exp (-c1 * a) < 1 / 3)
    (ha3 : A3 * (a : ℝ) ^ pow * Real.exp (-c3 * a) < 1 / 3) :
    (∑ k, Real.exp (-fK k)) +
        (∑ p, Real.exp (-fP p)) +
      ∑ x, Real.exp (-fX x) < 1 := by
  have hsumK : ∑ k, Real.exp (-fK k) < 1 / 3 := by
    calc
      ∑ k, Real.exp (-fK k) ≤
          Fintype.card K * Real.exp (-(c1 * a)) :=
        sum_exp_neg_le_card_mul fK (c1 * a) hfK
      _ ≤ A1 * (a : ℝ) ^ pow * Real.exp (-(c1 * a)) := by
        exact mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
      _ < 1 / 3 := by simpa only [neg_mul] using ha1
  have hsumP : ∑ p, Real.exp (-fP p) < 1 / 3 := by
    calc
      ∑ p, Real.exp (-fP p) ≤
          Fintype.card P * Real.exp (-(c1 * a)) :=
        sum_exp_neg_le_card_mul fP (c1 * a) hfP
      _ ≤ A2 * (a : ℝ) ^ pow * Real.exp (-(c1 * a)) := by
        exact mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
      _ < 1 / 3 := by simpa only [neg_mul] using ha2
  have hsumX : ∑ x, Real.exp (-fX x) < 1 / 3 := by
    calc
      ∑ x, Real.exp (-fX x) ≤
          Fintype.card X * Real.exp (-(c3 * a)) :=
        sum_exp_neg_le_card_mul fX (c3 * a) hfX
      _ ≤ A3 * (a : ℝ) ^ pow * Real.exp (-(c3 * a)) := by
        exact mul_le_mul_of_nonneg_right hX (Real.exp_pos _).le
      _ < 1 / 3 := by simpa only [neg_mul] using ha3
  linarith


end FinalTools
end Erdos163
