/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.FinalTools

/-!
# The finite failure estimate

This file isolates the deterministic lower bound for every active host set.
Keeping this pruning argument as a separate theorem also keeps the final
quantitative assembly within Lean's ordinary elaboration budget.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace FailureEstimate

noncomputable section

universe u v

theorem activeCard_lower_bound
    {X : Type u} {P : Type v}
    [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype P] [DecidableEq P]
    {N r D oldθ τ R M a : ℕ} {ε : ℝ}
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph X) [DecidableRel H.Adj]
    (part : X → P) (color : P → Fin r)
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ)
    (hr : 2 ≤ r) (hN : 1 ≤ N) (holdθ : 0 < oldθ)
    (hAcard : ∀ j, oldθ ≤ (A j).card)
    (hbad : (PrunedHost.allBadLevels (D := D) (θ := oldθ)
      (s := 4 * D) G A Λ).card ≤ R)
    (hM : 0 < M) (hMold : M < oldθ) (hRM : 2 * R < M)
    (hε : 0 ≤ ε)
    (hmoment : ∀ j, FiniteDefect.moment G oldθ (4 * D)
      (fun _ : Fin D => HostDirections.unionExcept A j) (A j) ≤ ε)
    (hcommonNumeric : (N : ℝ) ^ D * ε <
      ((oldθ : ℝ) / M) ^ (4 * D))
    (hcolor : ∀ ⦃x y⦄, H.Adj x y → color (part x) ≠ color (part y))
    (hforward : ∀ x, (RandomGreedy.forwardNeighbors H x).card ≤ D)
    (hBcard : ∀ j, τ ≤
      (PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
        G A Λ j).card)
    (ha6M : a ^ 6 ≤ M) (ha6τ : a ^ 6 ≤ τ) :
    let B : Fin r → Finset (Fin N) := fun j =>
      PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D) G A Λ j
    let coord : X → Type u := fun x => ↑(RandomGreedy.forwardNeighbors H x)
    let base := fun x : X =>
      fun y : RandomGreedy.forwardNeighbors H x => B (color (part y))
    let K := HostPartition.SamplingTest (P := P) X coord base
    let activeCard : K → ℕ
      | Sum.inl p => (B (color p)).card
      | Sum.inr z =>
          (FiniteDefect.commonNeighbors G z.2.1
            (B (color (part z.1)))).card
    ∀ z : K, (a : ℝ) ^ 6 / 2 ≤ (activeCard z : ℝ) := by
  dsimp only
  let B : Fin r → Finset (Fin N) := fun j =>
    PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D) G A Λ j
  have hU : ∀ j, (HostDirections.unionExcept A j).Nonempty := by
    intro j
    by_cases hj0 : j.1 = 0
    · let k : Fin r := ⟨1, hr⟩
      have hkj : k ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        simp [k, hj0] at hv
      have hk : (A k).Nonempty :=
        Finset.card_pos.mp (holdθ.trans_le (hAcard k))
      exact hk.mono (HostDirections.subset_unionExcept A hkj)
    · let k : Fin r := ⟨0, by omega⟩
      have hkj : k ≠ j := by
        intro h
        apply hj0
        exact (congrArg Fin.val h).symm
      have hk : (A k).Nonempty :=
        Finset.card_pos.mp (holdθ.trans_le (hAcard k))
      exact hk.mono (HostDirections.subset_unionExcept A hkj)
  have hbaseSubset : ∀ x (y : RandomGreedy.forwardNeighbors H x),
      B (color (part y)) ⊆ HostDirections.unionExcept A (color (part x)) := by
    intro x y
    have hyAdj : H.Adj x y := (Finset.mem_filter.mp y.property).2.1
    exact (PrunedHost.prunedLevels_subset
      (D := D) (θ := oldθ) (s := 4 * D) G A Λ (color (part y))).trans
      (HostDirections.subset_unionExcept A (hcolor hyAdj).symm)
  have hcommonM : ∀ x (g : RandomGreedy.forwardNeighbors H x → Fin N),
      g ∈ FiniteDefect.familyTuples
        (fun y : RandomGreedy.forwardNeighbors H x => B (color (part y))) →
      M < (FiniteDefect.commonNeighbors G g
        (A (color (part x)))).card := by
    intro x g hg
    have hdim : Fintype.card (RandomGreedy.forwardNeighbors H x) ≤ D := by
      simpa only [Fintype.card_coe] using hforward x
    exact PreparedHost.commonNeighbors_card_gt_of_all_direction G
      (fun y : RandomGreedy.forwardNeighbors H x => B (color (part y)))
      (HostDirections.unionExcept A (color (part x))) (A (color (part x)))
      hN (hU (color (part x))) hdim (fun y => hbaseSubset x y)
      hM hMold hε (hmoment (color (part x))) hcommonNumeric g hg
  have hlarge : ∀ x (g : RandomGreedy.forwardNeighbors H x → Fin N),
      g ∈ FiniteDefect.familyTuples
        (fun y : RandomGreedy.forwardNeighbors H x => B (color (part y))) →
      2 * R < (FiniteDefect.commonNeighbors G g
        (A (color (part x)))).card := by
    intro x g hg
    exact hRM.trans (hcommonM x g hg)
  intro z
  rcases z with p | z
  · have hτB : τ ≤ (B (color p)).card := by
      simpa only [B] using hBcard (color p)
    change (a : ℝ) ^ 6 / 2 ≤ ((B (color p)).card : ℝ)
    have haτcast : (a : ℝ) ^ 6 ≤ (τ : ℝ) := by exact_mod_cast ha6τ
    have hτBcast : (τ : ℝ) ≤ ((B (color p)).card : ℝ) := by
      exact_mod_cast hτB
    linarith
  · have hhalf := PrunedHost.half_commonNeighbors_lt_prunedLevels
        (D := D) (θ := oldθ) (s := 4 * D) G A Λ
        (color (part z.1)) z.2.1 hbad (hlarge z.1 z.2.1 z.2.2)
    have hMcommon := hcommonM z.1 z.2.1 z.2.2
    change (a : ℝ) ^ 6 / 2 ≤
      ((FiniteDefect.commonNeighbors G z.2.1
        (B (color (part z.1)))).card : ℝ)
    have haMcast : (a : ℝ) ^ 6 ≤ (M : ℝ) := by exact_mod_cast ha6M
    have hMcast : (M : ℝ) <
        ((FiniteDefect.commonNeighbors G z.2.1
          (A (color (part z.1)))).card : ℝ) := by
      exact_mod_cast hMcommon
    have hhalf' :
        ((FiniteDefect.commonNeighbors G z.2.1
          (A (color (part z.1)))).card : ℝ) / 2 <
        ((FiniteDefect.commonNeighbors G z.2.1
          (B (color (part z.1)))).card : ℝ) := by
      simpa only [B] using hhalf
    linarith

/-- The three McDiarmid tails in the final application have total mass below
one.  This statement packages the target-part count, the active-set lower
bound, and the two mass estimates at the exact polynomial scale used in the
large-order theorem. -/
theorem target_failureSum_lt_one
    {n d N r D L Q T oldθ τ R M a C lam : ℕ} {ε μ : ℝ}
    (H : SimpleGraph (Fin n)) [LinearOrder (Fin n)] [DecidableRel H.Adj]
    (hd : 1 ≤ d) (hdeg : IsDegenerateAtMost H d)
    (layer : Fin n → Fin (n + 1)) (c : Fin n → Fin (d + 1))
    (hlayer : ∀ x, (layer x).1 = Decomposition.layerIndex H d x)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (color : TargetParts.OccupiedPart layer c → Fin r)
    (A : Fin r → Finset (Fin N)) (Λ : ℕ → ℝ) (tail : Fin n → ℝ)
    (hr : 2 ≤ r) (hD : 0 < D) (hL16 : 16 ≤ L)
    (hL16D : 16 * D ≤ L) (hQ : 0 < Q) (hT : 2 ≤ T)
    (hC : 0 < C) (ha : 0 < a) (haScale : a = FinalTools.scale n)
    (hlam : 0 < lam) (hμ : 0 < μ)
    (hNdef : N = C * a ^ 8) (hτdef : τ = T * a ^ 8)
    (hΛdef : ∀ k, Λ k = if k = 0 then (a : ℝ)⁻¹ ^ 8
      else (lam : ℝ) * a ^ (8 * k - 5))
    (htailDef : ∀ x, tail x = μ / 2 *
      ∏ y : RandomGreedy.forwardNeighbors H x,
        (TargetWeights.mass L Q (TargetParts.part layer c y) * (τ : ℝ) / 2))
    (hnA : n ≤ a ^ 8) (hNpos : 1 ≤ N) (holdθ : 0 < oldθ)
    (hAcard : ∀ j, oldθ ≤ (A j).card)
    (hbad : (PrunedHost.allBadLevels (D := D) (θ := oldθ)
      (s := 4 * D) G A Λ).card ≤ R)
    (hM : 0 < M) (hMold : M < oldθ) (hRM : 2 * R < M)
    (hε : 0 ≤ ε)
    (hmoment : ∀ j, FiniteDefect.moment G oldθ (4 * D)
      (fun _ : Fin D => HostDirections.unionExcept A j) (A j) ≤ ε)
    (hcommonNumeric : (N : ℝ) ^ D * ε <
      ((oldθ : ℝ) / M) ^ (4 * D))
    (hcolor : ∀ ⦃x y⦄, H.Adj x y →
      color (TargetParts.part layer c x) ≠ color (TargetParts.part layer c y))
    (hforward : ∀ x, (RandomGreedy.forwardNeighbors H x).card ≤ D)
    (hBcard : ∀ j, τ ≤
      (PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D)
        G A Λ j).card)
    (ha6M : a ^ 6 ≤ M) (ha6τ : a ^ 6 ≤ τ)
    (ha1 : (2 * (r : ℝ) + (C : ℝ) ^ D) *
      (a : ℝ) ^ (8 * D + 8) *
        Real.exp (-(1 / (4 * (Q : ℝ) ^ 2)) * a) < 1 / 3)
    (ha2 : 2 * (r : ℝ) * (a : ℝ) ^ (8 * D + 8) *
      Real.exp (-(1 / (4 * (Q : ℝ) ^ 2)) * a) < 1 / 3)
    (ha3 : 1 * (a : ℝ) ^ (8 * D + 8) *
      Real.exp (-(μ ^ 2 / (2 * (C : ℝ) * (Q : ℝ) ^ (2 * D) *
        ((lam : ℝ) ^ 2 + 1))) * a) < 1 / 3) :
    PrunedEmbedding.failureSum G H (TargetParts.part layer c) color
      (fun j => PrunedHost.prunedLevels
        (D := D) (θ := oldθ) (s := 4 * D) G A Λ j)
      (TargetWeights.mass L Q)
      (fun p => TargetWeights.mass L Q p * N) Λ tail < 1 := by
  classical
  let part : Fin n → TargetParts.OccupiedPart layer c :=
    TargetParts.part layer c
  let q : TargetParts.OccupiedPart layer c → ℝ := TargetWeights.mass L Q
  let B : Fin r → Finset (Fin N) := fun j =>
    PrunedHost.prunedLevels (D := D) (θ := oldθ) (s := 4 * D) G A Λ j
  let coord : Fin n → Type := fun x => ↑(RandomGreedy.forwardNeighbors H x)
  let base : ∀ x, coord x → Finset (Fin N) := fun x y => B (color (part y))
  let P := TargetParts.OccupiedPart layer c
  let K := HostPartition.SamplingTest (P := P) (Fin n) coord base
  let activeCard : K → ℕ
    | Sum.inl p => (B (color p)).card
    | Sum.inr z =>
        (FiniteDefect.commonNeighbors G z.2.1
          (B (color (part z.1)))).card
  let which : K → P
    | Sum.inl p => p
    | Sum.inr z => part z.1
  let powE := 8 * D + 8
  let c1 : ℝ := 1 / (4 * Q ^ 2)
  let c3 : ℝ := μ ^ 2 /
    (2 * C * Q ^ (2 * D) * (lam ^ 2 + 1))
  have hpartSurj : Function.Surjective part := by
    intro p
    obtain ⟨x, hx⟩ := p.property
    refine ⟨x, Subtype.ext ?_⟩
    exact hx
  have hPcardRaw : Fintype.card P ≤ n := by
    simpa [P] using Fintype.card_le_of_surjective part hpartSurj
  have haPowMono : a ^ 8 ≤ a ^ powE := by
    exact Nat.pow_le_pow_right (show 1 ≤ a from ha) (by dsimp [powE]; omega)
  have hPcardNat : Fintype.card P ≤ 2 * r * a ^ powE := by
    calc
      Fintype.card P ≤ n := hPcardRaw
      _ ≤ a ^ 8 := hnA
      _ ≤ a ^ powE := haPowMono
      _ ≤ 2 * r * a ^ powE := Nat.le_mul_of_pos_left _ (by omega)
  have hXcardNat : n ≤ a ^ powE := hnA.trans haPowMono
  have hcoord : ∀ x, Fintype.card (coord x) ≤ D := by
    intro x
    simpa only [coord, Fintype.card_coe] using hforward x
  have hKraw : Fintype.card K ≤ Fintype.card P + n * N ^ D := by
    dsimp [K]
    simpa [P] using FinalTools.card_samplingTest_le (P := P)
      coord base hNpos hcoord
  have hND : N ^ D = C ^ D * a ^ (8 * D) := by
    rw [hNdef, mul_pow, ← pow_mul]
  have hnND : n * N ^ D ≤ C ^ D * a ^ powE := by
    calc
      n * N ^ D ≤ a ^ 8 * N ^ D := Nat.mul_le_mul_right _ hnA
      _ = a ^ 8 * (C ^ D * a ^ (8 * D)) := by rw [hND]
      _ = C ^ D * a ^ powE := by
        dsimp [powE]
        rw [show 8 * D + 8 = 8 + 8 * D by omega, pow_add]
        ring
  have hKcardNat : Fintype.card K ≤ (2 * r + C ^ D) * a ^ powE := by
    calc
      Fintype.card K ≤ Fintype.card P + n * N ^ D := hKraw
      _ ≤ 2 * r * a ^ powE + C ^ D * a ^ powE :=
        Nat.add_le_add hPcardNat hnND
      _ = (2 * r + C ^ D) * a ^ powE := by ring
  have hactive : ∀ z : K, (a : ℝ) ^ 6 / 2 ≤ (activeCard z : ℝ) := by
    have hz := activeCard_lower_bound
      (X := Fin n) (P := P) (N := N) (r := r) (D := D)
      (oldθ := oldθ) (τ := τ) (R := R) (M := M) (a := a)
      G H part color A Λ hr hNpos holdθ hAcard hbad hM hMold hRM
      hε hmoment hcommonNumeric hcolor hforward hBcard ha6M ha6τ
    intro z
    convert hz z using 1
    cases z <;> simp [activeCard, B]
  have hmassPart : ∀ p : P,
      (1 : ℝ) ≤ (Q : ℝ) ^ 2 * a * (q p) ^ 2 := by
    intro p
    have hm := FinalTools.mass_sq_mul_scale_ge
      H hd hdeg layer c hlayer hL16 hQ p
    rw [← haScale] at hm
    simpa only [q] using hm
  have hKexp : ∀ z : K, c1 * a ≤
      2 * (q (which z) * (activeCard z : ℝ) / 2) ^ 2 /
        (activeCard z : ℝ) := by
    intro z
    have hz := FinalTools.active_exp_ge hQ ha
      (TargetWeights.mass_pos hQ (which z))
      (hmassPart (which z)) (hactive z)
    simpa only [c1] using hz
  have hNscaleNat : a ^ 8 ≤ N := by
    rw [hNdef]
    exact Nat.le_mul_of_pos_left _ hC
  have hNscale : (a : ℝ) ^ 8 ≤ (N : ℝ) := by exact_mod_cast hNscaleNat
  have hPexp : ∀ p : P, c1 * a ≤
      2 * (q p * (N : ℝ)) ^ 2 / (N : ℝ) := by
    intro p
    have hp := FinalTools.size_exp_ge hQ ha
      (TargetWeights.mass_pos hQ p) (hmassPart p) hNscale
    simpa only [c1] using hp
  have hXexp : ∀ x : Fin n, c3 * a ≤
      2 * (tail x) ^ 2 /
        ∑ _i : Fin N,
          (Λ (Fintype.card (RandomGreedy.forwardNeighbors H x))) ^ 2 := by
    intro x
    let I := RandomGreedy.forwardNeighbors H x
    let k := Fintype.card I
    let qprod : ℝ := ∏ y : I, q (part y)
    have hk : k ≤ D := by
      simpa only [k, I, Fintype.card_coe] using hforward x
    have hqprod : 0 < qprod := by
      dsimp [qprod]
      exact Finset.prod_pos fun y _ => TargetWeights.mass_pos hQ (part y)
    have hmass : (1 : ℝ) ≤ (Q : ℝ) ^ (2 * D) * a * qprod ^ 2 := by
      have hm := FinalTools.prod_mass_sq_mul_scale_ge
        (I := I) H hd hdeg layer c hlayer hD hk hL16D hQ
          (fun y : I => part y)
      rw [← haScale] at hm
      simpa only [qprod, q] using hm
    have htailEq : tail x = μ / 2 * qprod * ((τ : ℝ) / 2) ^ k := by
      rw [htailDef x]
      dsimp [qprod, q, part, k, I]
      simp_rw [show ∀ y : RandomGreedy.forwardNeighbors H x,
        TargetWeights.mass L Q (TargetParts.part layer c y) * (τ : ℝ) / 2 =
          TargetWeights.mass L Q (TargetParts.part layer c y) * ((τ : ℝ) / 2) by
            intro y
            ring]
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Fintype.card_coe, Finset.card_attach]
      ring
    have hdenEq : (∑ _i : Fin N, (Λ k) ^ 2) =
        (N : ℝ) * (Λ k) ^ 2 := by simp
    have ht := FinalTools.tail_exp_ge hk hC hT hQ ha hlam hμ hqprod hmass
    change c3 * (a : ℝ) ≤ 2 * (tail x) ^ 2 / ∑ _i : Fin N, (Λ k) ^ 2
    rw [htailEq, hdenEq, hΛdef k]
    simpa only [c3, hNdef, hτdef] using ht
  have hKcardReal : (Fintype.card K : ℝ) ≤
      (2 * (r : ℝ) + (C : ℝ) ^ D) * (a : ℝ) ^ powE := by
    exact_mod_cast hKcardNat
  have hPcardReal : (Fintype.card P : ℝ) ≤
      2 * (r : ℝ) * (a : ℝ) ^ powE := by
    exact_mod_cast hPcardNat
  have hXcardReal : (Fintype.card (Fin n) : ℝ) ≤
      1 * (a : ℝ) ^ powE := by
    norm_num
    exact_mod_cast hXcardNat
  have hthree := FinalTools.three_exp_sums_lt_one
    (K := K) (P := P) (X := Fin n)
    (fun z => 2 * (q (which z) * (activeCard z : ℝ) / 2) ^ 2 /
      (activeCard z : ℝ))
    (fun p => 2 * (q p * (N : ℝ)) ^ 2 / (N : ℝ))
    (fun x => 2 * (tail x) ^ 2 /
      ∑ _i : Fin N,
        (Λ (Fintype.card (RandomGreedy.forwardNeighbors H x))) ^ 2)
    (a := a) (pow := powE) (c1 := c1) (c3 := c3)
    (A1 := 2 * (r : ℝ) + (C : ℝ) ^ D) (A2 := 2 * (r : ℝ)) (A3 := 1)
    hKcardReal hPcardReal hXcardReal hKexp hPexp hXexp
    (by simpa only [powE, c1] using ha1)
    (by simpa only [powE, c1] using ha2)
    (by simpa only [powE, c3] using ha3)
  simpa [PrunedEmbedding.failureSum, B, coord, base, K, activeCard,
    which, P, part, q, neg_div, neg_mul] using hthree

end
end FailureEstimate
end Erdos163
