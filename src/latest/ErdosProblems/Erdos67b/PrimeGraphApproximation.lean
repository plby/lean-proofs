import ErdosProblems.Erdos67b.PrimeGraphDecoupling

/-!
# Uniform finite approximation of bounded graph blocks

The finite alphabet is chosen before the input sequence. Explicit
perturbation estimates remove the finite-alphabet restriction from the
graph decoupling theorem.
-/

open scoped BigOperators ComplexConjugate
open Finset Filter

namespace Erdos67b

open FiniteEntropy

noncomputable section

theorem norm_primeGraphEdge_sub_le {H : ℕ} (b b' : Fin H → ℂ) (p h : ℕ)
    {B ζ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ)
    (hb : ∀ j, ‖b j‖ ≤ B) (hb' : ∀ j, ‖b' j‖ ≤ B)
    (hclose : ∀ j, ‖b j - b' j‖ ≤ ζ) (j : Fin H) :
    ‖primeGraphEdge b p h j - primeGraphEdge b' p h j‖ ≤ 2 * B * ζ := by
  unfold primeGraphEdge
  split_ifs with hj
  · let k : Fin H := ⟨j.1 + p * h, hj⟩
    have hid : b j * conj (b k) - b' j * conj (b' k) =
        (b j - b' j) * conj (b k) + b' j * conj (b k - b' k) := by
      rw [map_sub]
      ring
    change ‖b j * conj (b k) - b' j * conj (b' k)‖ ≤ _
    rw [hid]
    have hleft : ‖(b j - b' j) * conj (b k)‖ ≤ ζ * B := by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hclose j) (hb k) (norm_nonneg _) hζ
    have hright : ‖b' j * conj (b k - b' k)‖ ≤ B * ζ := by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hb' j) (hclose k) (norm_nonneg _) hB
    exact (norm_add_le _ _).trans (by linarith)
  · simp only [sub_self, norm_zero]
    positivity

theorem norm_primeGraphCoordinate_sub_le {H : ℕ} (b b' : Fin H → ℂ)
    (p h : ℕ) [NeZero p] {B ζ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ)
    (hb : ∀ j, ‖b j‖ ≤ B) (hb' : ∀ j, ‖b' j‖ ≤ B)
    (hclose : ∀ j, ‖b j - b' j‖ ≤ ζ) (z : ZMod p) :
    ‖primeGraphCoordinate b p h z - primeGraphCoordinate b' p h z‖ ≤
      (H / p + 1 : ℕ) * (2 * B * ζ) := by
  classical
  let s : Finset (Fin H) := Finset.univ.filter fun j ↦ z + (j.1 + 1 : ℕ) = 0
  have hs : s = Finset.univ.filter (fun j : Fin H ↦ (j.1 : ZMod p) = -z - 1) := by
    ext j
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_add, Nat.cast_one]
    constructor <;> intro h <;> linear_combination h
  have hcard : s.card ≤ H / p + 1 := by rw [hs]; exact card_fin_residue_le H p (-z - 1)
  have hsum : primeGraphCoordinate b p h z - primeGraphCoordinate b' p h z =
      ∑ j ∈ s, (primeGraphEdge b p h j - primeGraphEdge b' p h j) := by
    simp only [primeGraphCoordinate, s, Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hsum]
  calc
    ‖∑ j ∈ s, (primeGraphEdge b p h j - primeGraphEdge b' p h j)‖ ≤
        ∑ j ∈ s, ‖primeGraphEdge b p h j - primeGraphEdge b' p h j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ s, 2 * B * ζ := Finset.sum_le_sum
      (fun j _ ↦ norm_primeGraphEdge_sub_le b b' p h hB hζ hb hb' hclose j)
    _ = s.card * (2 * B * ζ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (H / p + 1 : ℕ) * (2 * B * ζ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

theorem norm_primeGraphObservable_sub_le {H : ℕ} (b b' : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    {B ζ δ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (hb : ∀ j, ‖b j‖ ≤ B) (hb' : ∀ j, ‖b' j‖ ≤ B) (hclose : ∀ j, ‖b j - b' j‖ ≤ ζ)
    (hs : ∀ p ∈ s, δ * H ≤ p) (p : PrimeGraphIndex H) (z : ZMod p.1) :
    ‖primeGraphObservable b h s p z - primeGraphObservable b' h s p z‖ ≤
      (1 / δ + 1) * (2 * B * ζ) := by
  unfold primeGraphObservable
  split_ifs with hp
  · have hpr : (0 : ℝ) < p.1 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne p.1))
    have hdiv : (H / p.1 : ℕ) ≤ (H : ℝ) / p.1 := by
      apply (le_div_iff₀ hpr).mpr
      exact_mod_cast Nat.div_mul_le_self H p.1
    have hratio : (H : ℝ) / p.1 ≤ 1 / δ := by
      apply (div_le_div_iff₀ hpr hδ).mpr
      nlinarith [hs p.1 hp]
    have hfloor : (H / p.1 + 1 : ℕ) ≤ 1 / δ + (1 : ℝ) := by push_cast; linarith
    exact (norm_primeGraphCoordinate_sub_le b b' p.1 h hB hζ hb hb' hclose z).trans
      (mul_le_mul_of_nonneg_right hfloor (by positivity))
  · simp only [sub_self, norm_zero]
    positivity

theorem norm_primeGraphSum_sub_le {H : ℕ} (b b' : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    {B ζ δ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (hb : ∀ j, ‖b j‖ ≤ B) (hb' : ∀ j, ‖b' j‖ ≤ B) (hclose : ∀ j, ‖b j - b' j‖ ≤ ζ)
    (hs : ∀ p ∈ s, δ * H ≤ p) (z : ZMod (primeGraphModulus H)) :
    ‖primeGraphSum b h s z - primeGraphSum b' h s z‖ ≤
      (Nat.primeCounting H : ℝ) * ((1 / δ + 1) * (2 * B * ζ)) := by
  unfold primeGraphSum crtComplexSum
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ p, (primeGraphObservable b h s p _ - primeGraphObservable b' h s p _)‖ ≤
        ∑ p, ‖primeGraphObservable b h s p _ - primeGraphObservable b' h s p _‖ := norm_sum_le _ _
    _ ≤ ∑ _p : PrimeGraphIndex H, (1 / δ + 1) * (2 * B * ζ) := Finset.sum_le_sum
      (fun p _ ↦ norm_primeGraphObservable_sub_le b b' h s hB hζ hδ hb hb' hclose hs p _)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul]

theorem norm_primeGraphMean_sub_le {H : ℕ} (b b' : Fin H → ℂ) (h : ℕ) (s : Finset ℕ)
    {B ζ δ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (hb : ∀ j, ‖b j‖ ≤ B) (hb' : ∀ j, ‖b' j‖ ≤ B) (hclose : ∀ j, ‖b j - b' j‖ ≤ ζ)
    (hs : ∀ p ∈ s, δ * H ≤ p) :
    ‖primeGraphMean b h s - primeGraphMean b' h s‖ ≤
      (Nat.primeCounting H : ℝ) * ((1 / δ + 1) * (2 * B * ζ)) := by
  rw [← crtComplexMean_primeGraphObservable, ← crtComplexMean_primeGraphObservable]
  unfold crtComplexMean
  rw [← Finset.sum_sub_distrib]
  have hcoord (p : PrimeGraphIndex H) :
      ‖(p.1 : ℝ)⁻¹ • (∑ x, primeGraphObservable b h s p x) -
        (p.1 : ℝ)⁻¹ • (∑ x, primeGraphObservable b' h s p x)‖ ≤
          (1 / δ + 1) * (2 * B * ζ) := by
    rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hsum : ‖∑ x, (primeGraphObservable b h s p x - primeGraphObservable b' h s p x)‖ ≤
        (p.1 : ℝ) * ((1 / δ + 1) * (2 * B * ζ)) := by
      apply (norm_sum_le _ _).trans
      have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) ↦
        norm_primeGraphObservable_sub_le b b' h s hB hζ hδ hb hb' hclose hs p x)
      simpa only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] using h
    have hp : (p.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p.1)
    have h := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ (p.1 : ℝ)⁻¹)
    simpa only [← mul_assoc, inv_mul_cancel₀ hp, one_mul] using h
  apply (norm_sum_le _ _).trans
  have h := Finset.sum_le_sum (fun p (_ : p ∈ Finset.univ) ↦ hcoord p)
  simpa only [Finset.sum_const, Finset.card_univ, card_primeGraphIndex, nsmul_eq_mul] using h

theorem norm_primeGraphDiscrepancy_sub_le (F G : ℕ → ℂ) (H h : ℕ) (s : Finset ℕ)
    {B ζ δ : ℝ} (hB : 0 ≤ B) (hζ : 0 ≤ ζ) (hδ : 0 < δ)
    (hF : ∀ n, ‖F n‖ ≤ B) (hG : ∀ n, ‖G n‖ ≤ B) (hclose : ∀ n, ‖F n - G n‖ ≤ ζ)
    (hs : ∀ p ∈ s, δ * H ≤ p) (n : ℕ) :
    ‖primeGraphDiscrepancy F H h s n - primeGraphDiscrepancy G H h s n‖ ≤
      4 * (Nat.primeCounting H : ℝ) * B * ζ * (1 / δ + 1) := by
  have hb : ∀ j, ‖finiteSequenceBlock F H n j‖ ≤ B := fun j ↦ hF _
  have hb' : ∀ j, ‖finiteSequenceBlock G H n j‖ ≤ B := fun j ↦ hG _
  have hblocks : ∀ j, ‖finiteSequenceBlock F H n j - finiteSequenceBlock G H n j‖ ≤ ζ := fun j ↦ hclose _
  have hsum := norm_primeGraphSum_sub_le (finiteSequenceBlock F H n) (finiteSequenceBlock G H n)
    h s hB hζ hδ hb hb' hblocks hs (n : ZMod (primeGraphModulus H))
  have hmean := norm_primeGraphMean_sub_le (finiteSequenceBlock F H n) (finiteSequenceBlock G H n)
    h s hB hζ hδ hb hb' hblocks hs
  have heq : primeGraphDiscrepancy F H h s n - primeGraphDiscrepancy G H h s n =
      (primeGraphSum (finiteSequenceBlock F H n) h s n - primeGraphSum (finiteSequenceBlock G H n) h s n) -
        (primeGraphMean (finiteSequenceBlock F H n) h s - primeGraphMean (finiteSequenceBlock G H n) h s) := by
    unfold primeGraphDiscrepancy
    abel
  rw [heq]
  exact (norm_sub_le _ _).trans (by nlinarith)

/-- A finite internal net in the closed unit disk. -/
theorem exists_finite_unitDisk_approximation {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ s : Finset ℂ, s.Nonempty ∧ (∀ z ∈ s, ‖z‖ ≤ 1) ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → ∃ w ∈ s, ‖z - w‖ ≤ ζ := by
  classical
  obtain ⟨t, ht, hfinite, hcover⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).finite_cover_balls hζ
  have happrox (z : ℂ) (hz : ‖z‖ ≤ 1) : ∃ w ∈ hfinite.toFinset, ‖z - w‖ ≤ ζ := by
    have hzball : z ∈ Metric.closedBall (0 : ℂ) 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    obtain ⟨w, hwt, hw⟩ := Set.mem_iUnion₂.mp (hcover hzball)
    exact ⟨w, hfinite.mem_toFinset.mpr hwt,
      (by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hw).le)⟩
  obtain ⟨w, hw, _⟩ := happrox 0 (by simp)
  refine ⟨hfinite.toFinset, ⟨w, hw⟩, ?_, happrox⟩
  intro z hz
  have h := ht (hfinite.mem_toFinset.mp hz)
  simpa only [Metric.mem_closedBall, dist_zero_right] using h

/-- Graph decoupling for every sequence in the complex unit disk, with
no finite-alphabet or multiplicativity restriction on the input. -/
theorem exists_logProb_bounded_primeGraph_decoupling
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (Hmin : ℕ) :
    ∃ H₀ J L₀ : ℕ, Hmin ≤ H₀ ∧ 2 ≤ H₀ ∧ 0 < J ∧ 0 < L₀ ∧
      ∀ (L U : ℕ) (_hL : 0 < L) (_hU : 2 * L ≤ U), L₀ ≤ L →
      ∀ F : ℕ → ℂ, (∀ n, ‖F n‖ ≤ 1) → ∃ j < J,
        ∀ (h : ℕ) (s : Finset ℕ), (∀ p ∈ s, δ * entropyScale H₀ j ≤ p) →
        ‖logProbExpectation L U (primeGraphDiscrepancy F (entropyScale H₀ j) h s)‖ ≤
          ε * entropyScale H₀ j / Real.log (entropyScale H₀ j) := by
  classical
  let D := 1 / δ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let ζ := ε / (32 * D)
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  have hbudget : 16 * ζ * D = ε / 2 := by
    dsimp [ζ]
    field_simp
    ring
  obtain ⟨net, hnet, hnetBound, hnetApprox⟩ := exists_finite_unitDisk_approximation hζ
  let α := ↥net
  obtain ⟨a₀, ha₀⟩ := hnet
  let : Nonempty α := ⟨⟨a₀, ha₀⟩⟩
  let decode : α → ℂ := Subtype.val
  have hdecode : ∀ a, ‖decode a‖ ≤ 1 := fun a ↦ hnetBound a.1 a.2
  obtain ⟨Hprime, hprime⟩ := eventually_atTop.mp eventually_primeCounting_le_four_mul_div_log
  obtain ⟨H₀, J, L₀, hmin, hH₀, hJ, hL₀, hselect⟩ :=
    exists_logProb_primeGraph_decoupling decode (by norm_num : (0 : ℝ) < 1) hδ
      (show 0 < ε / 2 by positivity) hdecode (max Hmin Hprime)
  refine ⟨H₀, J, L₀, (le_max_left _ _).trans hmin, hH₀, hJ, hL₀, ?_⟩
  intro L U hL hU hLL F hF
  have happ (n : ℕ) : ∃ a : α, ‖F n - decode a‖ ≤ ζ := by
    obtain ⟨a, ha, hclose⟩ := hnetApprox (F n) (hF n)
    exact ⟨⟨a, ha⟩, hclose⟩
  choose G hGclose using happ
  have hG : ∀ n, ‖(decode ∘ G) n‖ ≤ 1 := fun n ↦ hdecode (G n)
  obtain ⟨j, hj, hdec⟩ := hselect L U hL hU hLL G
  refine ⟨j, hj, ?_⟩
  intro h s hs
  let H := FiniteEntropy.entropyScale H₀ j
  have hHlower : H₀ ≤ H := FiniteEntropy.le_entropyScale H₀ j
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hlog : 0 < Real.log (H : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < H by omega))
  have hcount := hprime H (((le_max_right _ _).trans hmin).trans hHlower)
  have hdiff := norm_logProbExpectation_le hL (by omega : L ≤ U)
    (fun n ↦ primeGraphDiscrepancy F H h s n - primeGraphDiscrepancy (decode ∘ G) H h s n)
    (4 * (Nat.primeCounting H : ℝ) * ζ * D) (by
      intro n _
      have h := norm_primeGraphDiscrepancy_sub_le F (decode ∘ G) H h s zero_le_one hζ.le hδ
        hF hG hGclose hs n
      simpa only [mul_one, D] using h)
  have heq : logProbExpectation L U
      (fun n ↦ primeGraphDiscrepancy F H h s n - primeGraphDiscrepancy (decode ∘ G) H h s n) =
      logProbExpectation L U (primeGraphDiscrepancy F H h s) -
        logProbExpectation L U (primeGraphDiscrepancy (decode ∘ G) H h s) := by
    simp only [logProbExpectation, smul_sub, Finset.sum_sub_distrib]
  rw [heq] at hdiff
  have hdiffBudget : 4 * (Nat.primeCounting H : ℝ) * ζ * D ≤ (ε / 2) * ((H : ℝ) / Real.log H) := by
    have hmul := mul_le_mul_of_nonneg_right hcount (show 0 ≤ 4 * ζ * D by positivity)
    calc
      4 * (Nat.primeCounting H : ℝ) * ζ * D ≤ (16 * ζ * D) * ((H : ℝ) / Real.log H) := by nlinarith
      _ = _ := by rw [hbudget]
  have hdec' := hdec h s hs
  have hnorm := norm_add_le
    (logProbExpectation L U (primeGraphDiscrepancy F H h s) -
      logProbExpectation L U (primeGraphDiscrepancy (decode ∘ G) H h s))
    (logProbExpectation L U (primeGraphDiscrepancy (decode ∘ G) H h s))
  rw [sub_add_cancel] at hnorm
  have hfinal := hnorm.trans (add_le_add (hdiff.trans hdiffBudget) hdec')
  simp only [mul_div_assoc] at *
  linarith

end

end Erdos67b
