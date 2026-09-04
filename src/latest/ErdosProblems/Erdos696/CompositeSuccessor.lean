/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import ErdosProblems.Erdos696.LowerBoundLittleH

namespace Erdos696

open scoped BigOperators Topology
open Real MeasureTheory

variable [sw : SiegelWalfisz]
include sw

-- === Inlined from Erdos696/CompositeSuccessor.lean ===
/-
# Composite-successor lemma

Mirrors §6.2 of `erdos_696_paper.tex` (Lemma 6.2 in paper numbering).

**Statement.**  There exist absolute constants `A > 10` and `c > 0` with
the following property.  Let `y ≥ y₀` be sufficiently large and
`1 ≤ d ≤ y`.  In the independent prime model, with probability at least
`1 - O(y^{-c})` there is a squarefree product `e` of selected primes in
`(exp y, exp(y^{A-1})]` with `e ≡ 1 (mod d)`, `e > d`, `e ≤ exp(y^A)`.

The proof is a 7-step argument: Mertens-window mass → block decomposition
→ good-block probability `e^{-1}` → Chernoff for the number `W` of good
blocks → conditional residue distribution → application of the abstract
subset-product lemma → assembly.

We give the formal statement and defer all seven steps.
-/



open scoped Topology
/-! ### Paper §6.2 finite product-model objects

The seven deferred steps below use an explicit finite prime-selection model on the
window `(exp y, exp(y^(A-1))]`.  Every model probability is a finite sum over subsets
of the finite prime window, with each prime `q` selected with weight `1/q`.
-/

private noncomputable def reciprocalPrimeMass (S : Finset ℕ) : ℝ :=
  ∑ q ∈ S, (1 : ℝ) / (q : ℝ)

private noncomputable def compositePrimeWindow (A y : ℝ) : Finset ℕ :=
  Finset.filter
    (fun q => q.Prime ∧ Real.exp y < (q : ℝ) ∧ (q : ℝ) ≤ Real.exp (y ^ (A - 1)))
    (Finset.Iic ⌊Real.exp (y ^ (A - 1))⌋₊)

/-- Paper §6.2 line 1536 sub-window for the `d = 1` case: primes in `(exp y, exp(y^2)]`.
The d=1 dispatch uses Mertens on this sub-window to get `∑ 1/q = log y + O(1/y)`. -/
private noncomputable def compositePrimeSubWindow_d_1 (y : ℝ) : Finset ℕ :=
  Finset.filter
    (fun q => q.Prime ∧ Real.exp y < (q : ℝ) ∧ (q : ℝ) ≤ Real.exp (y ^ (2 : ℝ)))
    (Finset.Iic ⌊Real.exp (y ^ (2 : ℝ))⌋₊)

/-- Sub-window is a subset of the full window: `(exp y, exp(y^2)] ⊆ (exp y, exp(y^{A-1})]`
since `y^2 ≤ y^{19}` for `y ≥ 1`.  Used in the paper §6.2 d=1 dispatch (line 1542-1548). -/
private lemma compositePrimeSubWindow_d_1_subset_window {y : ℝ} (hy : 1 ≤ y) :
    compositePrimeSubWindow_d_1 y ⊆ compositePrimeWindow 20 y := by
  intro q hq
  unfold compositePrimeSubWindow_d_1 at hq
  rw [Finset.mem_filter, Finset.mem_Iic] at hq
  obtain ⟨_hq_iic, hq_prime, hq_gt_exp_y, hq_le_exp_y2⟩ := hq
  unfold compositePrimeWindow
  rw [Finset.mem_filter, Finset.mem_Iic]
  have hy2_le_y19 : y ^ ((2 : ℝ)) ≤ y ^ ((20 : ℝ) - 1) :=
    Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  have hexp_le : Real.exp (y ^ ((2 : ℝ))) ≤ Real.exp (y ^ ((20 : ℝ) - 1)) :=
    Real.exp_le_exp.mpr hy2_le_y19
  refine ⟨?_, hq_prime, hq_gt_exp_y, ?_⟩
  · exact Nat.le_floor (hq_le_exp_y2.trans hexp_le)
  · exact hq_le_exp_y2.trans hexp_le

/-- The zero-indexed paper block endpoint: `β_k = exp (y * exp k)`. -/
private noncomputable def compositeBlockEndpoint (y : ℝ) (k : ℕ) : ℝ :=
  Real.exp (y * Real.exp (k : ℝ))

/-- The zero-indexed block `(β_k, β_{k+1}]` used in paper §6.2 Step 2. -/
private noncomputable def compositeBlock (y : ℝ) (k : ℕ) : Finset ℕ :=
  Finset.filter
    (fun q => q.Prime ∧ compositeBlockEndpoint y k < (q : ℝ) ∧
      (q : ℝ) ≤ compositeBlockEndpoint y (k + 1))
    (Finset.Iic ⌊compositeBlockEndpoint y (k + 1)⌋₊)

/-- The paper's choice `M = floor(γ log y)` with `γ = 15`. -/
private noncomputable def compositeBlockCount (y : ℝ) : ℕ :=
  ⌊15 * Real.log y⌋₊

/-- The paper's choice `K = ceil(κ log y)`, with `κ = ργ/2` and `ρ = e^{-1}`. -/
private noncomputable def compositeGoodBlockThreshold (y : ℝ) : ℕ :=
  ⌈((Real.exp (-1) * 15) / 2) * Real.log y⌉₊

/-- Probability that a finite block is good: exactly one prime in it is selected. -/
private noncomputable def blockGoodProbability (B : Finset ℕ) : ℝ :=
  ∑ q ∈ B, ((1 : ℝ) / (q : ℝ)) *
    ∏ r ∈ B.erase q, (1 - (1 : ℝ) / (r : ℝ))

/-- Count of good blocks under selection `S`: blocks `B_k` (`k < M`) such that
`B_k ∩ S` has exactly one element.  Used for step 4's Chernoff lower-tail bound. -/
private noncomputable def goodBlockCount (S : Finset ℕ) (y : ℝ) : ℕ :=
  ((Finset.range (compositeBlockCount y)).filter
    (fun k => (compositeBlock y k ∩ S).card = 1)).card

/-- The set of good block indices for selection `S` in window `y`: indices `k < M`
such that `B_k ∩ S` has exactly one element.  Paper §6.2 line 1606-1607: "good"
means exactly one prime in the block is selected.  `goodBlockCount = goodBlockIndices.card`. -/
private noncomputable def goodBlockIndices (S : Finset ℕ) (y : ℝ) : Finset ℕ :=
  (Finset.range (compositeBlockCount y)).filter
    (fun k => (compositeBlock y k ∩ S).card = 1)

private lemma goodBlockCount_eq_card_indices (S : Finset ℕ) (y : ℝ) :
    goodBlockCount S y = (goodBlockIndices S y).card := rfl

/-- Paper §6.2 line 1714-1715: "From each good block `B_{k_i}` we extract the unique
selected prime `q_{k_i}`."  When block `k` is good for `S` (i.e. `(B_k ∩ S).card = 1`),
returns the unique element via `Finset.min'`; otherwise returns `1` as a default sentinel. -/
private noncomputable def selectedPrimeInBlock (S : Finset ℕ) (y : ℝ) (k : ℕ) : ℕ := by
  classical
  exact
    if h : (compositeBlock y k ∩ S).card = 1 then
      (compositeBlock y k ∩ S).min' (Finset.card_pos.mp (by rw [h]; exact Nat.zero_lt_one))
    else
      1

/-- When block `k` is good for `S`, `selectedPrimeInBlock S y k ∈ compositeBlock y k ∩ S`. -/
private lemma selectedPrimeInBlock_mem {S : Finset ℕ} {y : ℝ} {k : ℕ}
    (h : (compositeBlock y k ∩ S).card = 1) :
    selectedPrimeInBlock S y k ∈ compositeBlock y k ∩ S := by
  classical
  unfold selectedPrimeInBlock
  rw [dif_pos h]
  exact Finset.min'_mem _ _

/-- Paper §6.2 line 1716: every prime in `compositeBlock y k` exceeds `exp y`. -/
private lemma compositeBlock_prime_gt_exp_y {y : ℝ} {k : ℕ} (hy : 0 ≤ y) {q : ℕ}
    (hq : q ∈ compositeBlock y k) : Real.exp y < (q : ℝ) := by
  unfold compositeBlock at hq
  rw [Finset.mem_filter] at hq
  obtain ⟨_, _, hq_gt, _⟩ := hq
  -- hq_gt : compositeBlockEndpoint y k < q
  -- Need: Real.exp y < q.  Since β_k = exp(y · e^k) ≥ exp(y · 1) = exp(y) for k ≥ 0.
  have hek : (1 : ℝ) ≤ Real.exp ((k : ℝ)) := Real.one_le_exp (Nat.cast_nonneg k)
  have hβk : Real.exp y ≤ compositeBlockEndpoint y k := by
    unfold compositeBlockEndpoint
    apply Real.exp_le_exp.mpr
    have hmul : y * 1 ≤ y * Real.exp ((k : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hek hy
    linarith
  exact hβk.trans_lt hq_gt

/-- Primes in `compositeBlock y k` are prime (from filter definition). -/
private lemma compositeBlock_prime {y : ℝ} {k : ℕ} {q : ℕ}
    (hq : q ∈ compositeBlock y k) : q.Prime := by
  unfold compositeBlock at hq
  rw [Finset.mem_filter] at hq
  exact hq.2.1


/-- Paper §6.2 line 1717: when block `k` is good for `S`, the selected prime is coprime
to `d` (since `q > exp y > y ≥ d` and `q` is prime). -/
private lemma selectedPrimeInBlock_coprime_d {S : Finset ℕ} {y : ℝ} {d : ℕ}
    (hy : 2 ≤ y) (hd_pos : 0 < d) (hd_le_y : (d : ℝ) ≤ y) {k : ℕ}
    (h_good : (compositeBlock y k ∩ S).card = 1) :
    Nat.Coprime (selectedPrimeInBlock S y k) d := by
  classical
  have hmem := selectedPrimeInBlock_mem h_good
  have hmem_block : selectedPrimeInBlock S y k ∈ compositeBlock y k := by
    rw [Finset.mem_inter] at hmem
    exact hmem.1
  have hq_prime : (selectedPrimeInBlock S y k).Prime := compositeBlock_prime hmem_block
  have hq_gt_exp_y : Real.exp y < (selectedPrimeInBlock S y k : ℝ) :=
    compositeBlock_prime_gt_exp_y (by linarith) hmem_block
  have hexp_y_gt_y : (y : ℝ) < Real.exp y := by
    have hy_ne : y ≠ 0 := ne_of_gt (by linarith)
    linarith [Real.add_one_lt_exp hy_ne]
  have hq_gt_y : (y : ℝ) < (selectedPrimeInBlock S y k : ℝ) := by linarith
  have hq_gt_d : (d : ℝ) < (selectedPrimeInBlock S y k : ℝ) := lt_of_le_of_lt hd_le_y hq_gt_y
  have hq_gt_d_nat : d < selectedPrimeInBlock S y k := by exact_mod_cast hq_gt_d
  -- q is prime and q > d > 0, so q does not divide d.
  apply (Nat.coprime_or_dvd_of_prime hq_prime d).resolve_right
  intro hq_dvd_d
  have hq_le_d : selectedPrimeInBlock S y k ≤ d := Nat.le_of_dvd hd_pos hq_dvd_d
  omega

/-- Paper §6.2 line 1717: `q_{k_i} mod d ∈ G` where `G = (ZMod d)ˣ`.  When block `k` is
good for `S` and the selected prime is coprime to `d`, returns the unit; otherwise `1`. -/
private noncomputable def residueOfSelectedPrime
    (S : Finset ℕ) (y : ℝ) (d : ℕ) (k : ℕ) : (ZMod d)ˣ := by
  classical
  exact
    if h : (compositeBlock y k ∩ S).card = 1 ∧
            Nat.Coprime (selectedPrimeInBlock S y k) d then
      ZMod.unitOfCoprime (selectedPrimeInBlock S y k) h.2
    else
      1

/-- Paper §6.2 line 1710-1712: "On the event W ≥ K, let k_1 < k_2 < ... < k_K be the
first K indices for which B_{k_i} is good".  When `K ≤ goodBlockCount S y`, this gives
the K smallest good block indices via `Finset.orderEmbOfFin`; otherwise defaults to 0. -/
private noncomputable def firstKGoodBlockIndices
    (S : Finset ℕ) (y : ℝ) (K : ℕ) : Fin K → ℕ := by
  classical
  exact fun i =>
    if h : K ≤ goodBlockCount S y then
      Finset.orderEmbOfFin (goodBlockIndices S y) rfl
        ⟨i.val, lt_of_lt_of_le i.isLt h⟩
    else
      0

/-- Paper §6.2 line 1746: `g_i := q_{k_i} mod d`.  The residue vector `Fin K → G`
extracted from the first K good blocks of selection `S`. -/
private noncomputable def firstKResidueVector
    (S : Finset ℕ) (y : ℝ) (d K : ℕ) : Fin K → (ZMod d)ˣ := fun i =>
  residueOfSelectedPrime S y d (firstKGoodBlockIndices S y K i)

/-- Conditional residue law of the unique selected prime, given that a block is good. -/
private noncomputable def blockConditionalResidueProbability
    (B : Finset ℕ) (d a : ℕ) : ℝ :=
  (∑ q ∈ B.filter (fun q => q % d = a % d),
      (1 : ℝ) / (((q - 1 : ℕ) : ℝ))) /
    (∑ q ∈ B, (1 : ℝ) / (((q - 1 : ℕ) : ℝ)))

/-- Weight of one selected subset in the independent finite prime model. -/
private noncomputable def selectionWeight (U S : Finset ℕ) : ℝ :=
  ∏ q ∈ U, if q ∈ S then (1 : ℝ) / (q : ℝ) else 1 - (1 : ℝ) / (q : ℝ)

/-- Algebraic identity relating per-block "good with specific selection" probability
to `blockGoodProbability` and `blockConditionalResidueProbability`:
for `q ∈ B` with `q ≥ 2`, `(1/q) · ∏_{r ∈ B \ {q}} (1 - 1/r) = ∏_{r ∈ B} (1 - 1/r) · 1/(q-1)`.
Foundational for mixture identity (paper line 1732). -/
private lemma reciprocal_block_identity {B : Finset ℕ} {q : ℕ}
    (hq_mem : q ∈ B) (hq_ge_two : 2 ≤ q) :
    ((1 : ℝ) / (q : ℝ)) * (∏ r ∈ B.erase q, (1 - (1 : ℝ) / (r : ℝ))) =
    (∏ r ∈ B, (1 - (1 : ℝ) / (r : ℝ))) * ((1 : ℝ) / (((q - 1 : ℕ) : ℝ))) := by
  have hq_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq_ne : (q : ℝ) ≠ 0 := hq_pos.ne'
  have hqm1_pos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
    have hnat : 1 ≤ q - 1 := by omega
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hnat)
  have hqm1_ne : ((q - 1 : ℕ) : ℝ) ≠ 0 := hqm1_pos.ne'
  have h_prod_split : (∏ r ∈ B, (1 - (1 : ℝ) / (r : ℝ))) =
      (1 - (1 : ℝ) / (q : ℝ)) * (∏ r ∈ B.erase q, (1 - (1 : ℝ) / (r : ℝ))) := by
    rw [← Finset.mul_prod_erase B _ hq_mem]
  rw [h_prod_split]
  have h1 : 1 ≤ q := by omega
  have h_cast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  have h_subst : (1 - (1 : ℝ) / (q : ℝ)) = ((q - 1 : ℕ) : ℝ) / (q : ℝ) := by
    rw [h_cast]; field_simp
  rw [h_subst]
  field_simp

/-- Per-block joint probability of "exactly one selected ∧ residue = a mod d":
equals `blockGoodProbability B · blockConditionalResidueProbability B d a` for B
consisting of primes.  This is the key per-block factorization underlying paper line 1732. -/
private lemma block_joint_good_residue_prob {B : Finset ℕ} {d a : ℕ}
    (h_prime : ∀ q ∈ B, q.Prime) :
    (∑ q ∈ B.filter (fun q => q % d = a % d),
        (1 : ℝ) / (q : ℝ) * ∏ r ∈ B.erase q, (1 - (1 : ℝ) / (r : ℝ))) =
    blockGoodProbability B * blockConditionalResidueProbability B d a := by
  classical
  -- Per-term application of reciprocal_block_identity.
  have h_lhs_eq :
      (∑ q ∈ B.filter (fun q => q % d = a % d),
          (1 : ℝ) / (q : ℝ) * ∏ r ∈ B.erase q, (1 - (1 : ℝ) / (r : ℝ))) =
      ∑ q ∈ B.filter (fun q => q % d = a % d),
          (∏ r ∈ B, (1 - (1 : ℝ) / (r : ℝ))) * (1 / ((q - 1 : ℕ) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro q hq_filter
    have hq_mem : q ∈ B := (Finset.mem_filter.mp hq_filter).1
    have hq_ge_two : 2 ≤ q := (h_prime q hq_mem).two_le
    exact reciprocal_block_identity hq_mem hq_ge_two
  have h_good_eq : blockGoodProbability B =
      (∏ r ∈ B, (1 - (1 : ℝ) / (r : ℝ))) *
        ∑ q ∈ B, (1 : ℝ) / (((q - 1 : ℕ) : ℝ)) := by
    unfold blockGoodProbability
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq_mem
    have hq_ge_two : 2 ≤ q := (h_prime q hq_mem).two_le
    exact reciprocal_block_identity hq_mem hq_ge_two
  rw [h_lhs_eq, h_good_eq]
  rw [← Finset.mul_sum]
  unfold blockConditionalResidueProbability
  -- Goal: R * DA = R * D * (DA / D), where R = ∏(1-1/r), D = ∑(1/(q-1)), DA = ∑_filter (1/(q-1))
  by_cases hD : (∑ q ∈ B, (1 : ℝ) / (((q - 1 : ℕ) : ℝ))) = 0
  · -- D = 0: each 1/(q-1) > 0 so B must be empty.
    have hB_empty : B = ∅ := by
      by_contra hB_ne
      rcases Finset.nonempty_of_ne_empty hB_ne with ⟨q, hq⟩
      have hq_ge_two : 2 ≤ q := (h_prime q hq).two_le
      have h_pos : 0 < ((q - 1 : ℕ) : ℝ) := by
        have hnat : 1 ≤ q - 1 := by omega
        exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hnat
      have h_term_pos : 0 < (1 : ℝ) / (((q - 1 : ℕ) : ℝ)) := by positivity
      have h_sum_pos : 0 < ∑ q ∈ B, (1 : ℝ) / (((q - 1 : ℕ) : ℝ)) :=
        Finset.sum_pos' (fun _ _ => by positivity) ⟨q, hq, h_term_pos⟩
      exact h_sum_pos.ne' hD
    rw [hB_empty]
    simp
  · field_simp

/-- Independent finite prime-model probability of a predicate on selected subsets. -/
private noncomputable def finitePrimeModelProb
    (U : Finset ℕ) (Q : Finset ℕ → Prop) : ℝ := by
  classical
  exact ∑ S ∈ U.powerset.filter Q, selectionWeight U S

/-- Paper §6.2 line 1732: the conditional joint distribution of residues.
`μ(g) := P(firstKResidueVector S = g ∧ K ≤ #good blocks) / P(K ≤ #good blocks)`.
This is the conditional probability of the residue pattern given `W ≥ K`. -/
private noncomputable def conditionalResidueMeasure
    (y : ℝ) (d K : ℕ) (g : Fin K → (ZMod d)ˣ) : ℝ :=
  finitePrimeModelProb (compositePrimeWindow 20 y)
      (fun S => K ≤ goodBlockCount S y ∧ firstKResidueVector S y d K = g) /
    finitePrimeModelProb (compositePrimeWindow 20 y)
      (fun S => K ≤ goodBlockCount S y)


private def blockEvents (F : ℕ → Finset ℕ) (A B : Finset ℕ) (S : Finset ℕ) :
    Prop :=
  (∀ k ∈ A, (F k ∩ S).card = 1) ∧ ∀ k ∈ B, (F k ∩ S).card ≠ 1

private lemma selectionWeight_eq_prod_sdiff (U S : Finset ℕ) (hS : S ⊆ U) :
    selectionWeight U S =
      (∏ q ∈ S, (1 : ℝ) / (q : ℝ)) *
        ∏ q ∈ U \ S, (1 - (1 : ℝ) / (q : ℝ)) := by
  classical
  dsimp [selectionWeight]
  calc
    (∏ q ∈ U, if q ∈ S then (1 : ℝ) / (q : ℝ) else 1 - (1 : ℝ) / (q : ℝ)) =
        (∏ q ∈ U \ S,
            if q ∈ S then (1 : ℝ) / (q : ℝ) else 1 - (1 : ℝ) / (q : ℝ)) *
          ∏ q ∈ S, if q ∈ S then (1 : ℝ) / (q : ℝ) else 1 - (1 : ℝ) / (q : ℝ) := by
      exact (Finset.prod_sdiff hS).symm
    _ = (∏ q ∈ U \ S, (1 - (1 : ℝ) / (q : ℝ))) *
          ∏ q ∈ S, (1 : ℝ) / (q : ℝ) := by
      congr 1
      · apply Finset.prod_congr rfl
        intro q hq
        have hqS : q ∉ S := (Finset.mem_sdiff.mp hq).2
        simp [hqS]
      · apply Finset.prod_congr rfl
        intro q hq
        simp [hq]
    _ = (∏ q ∈ S, (1 : ℝ) / (q : ℝ)) *
          ∏ q ∈ U \ S, (1 - (1 : ℝ) / (q : ℝ)) := by
      ring

private lemma finitePrimeModelProb_true (U : Finset ℕ) :
    finitePrimeModelProb U (fun _S => True) = 1 := by
  classical
  dsimp [finitePrimeModelProb]
  simp only [Finset.filter_true]
  calc
    (∑ S ∈ U.powerset, selectionWeight U S) =
        ∑ S ∈ U.powerset,
          (∏ q ∈ S, (1 : ℝ) / (q : ℝ)) *
            ∏ q ∈ U \ S, (1 - (1 : ℝ) / (q : ℝ)) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact selectionWeight_eq_prod_sdiff U S (Finset.mem_powerset.mp hS)
    _ = ∏ q ∈ U, ((1 : ℝ) / (q : ℝ) + (1 - (1 : ℝ) / (q : ℝ))) := by
      exact (Finset.prod_add (fun q : ℕ => (1 : ℝ) / (q : ℝ))
        (fun q : ℕ => 1 - (1 : ℝ) / (q : ℝ)) U).symm
    _ = 1 := by
      simp

private lemma finitePrimeModelProb_compl (U : Finset ℕ) (Q : Finset ℕ → Prop) :
    finitePrimeModelProb U (fun S => ¬ Q S) = 1 - finitePrimeModelProb U Q := by
  classical
  let : DecidablePred Q := fun _ => Classical.propDecidable _
  let : DecidablePred (fun S : Finset ℕ => ¬ Q S) := fun _ => Classical.propDecidable _
  have hsum := Finset.sum_filter_add_sum_filter_not (s := U.powerset) (p := Q)
    (f := selectionWeight U)
  dsimp [finitePrimeModelProb] at hsum ⊢
  have htrue : (∑ x ∈ U.powerset, selectionWeight U x) = 1 := by
    simpa [finitePrimeModelProb] using finitePrimeModelProb_true U
  rw [htrue] at hsum
  linarith

private lemma selectionWeight_singleton (C : Finset ℕ) {q : ℕ} (hq : q ∈ C) :
    selectionWeight C {q} =
      ((1 : ℝ) / (q : ℝ)) * ∏ r ∈ C.erase q, (1 - (1 : ℝ) / (r : ℝ)) := by
  classical
  dsimp [selectionWeight]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton q _ (fun hn => (hn hq).elim)]
  rw [Finset.sdiff_singleton_eq_erase]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro r hr
    have hrne : r ≠ q := Finset.ne_of_mem_erase hr
    simp [hrne]

private lemma finitePrimeModelProb_block_good (C : Finset ℕ) :
    finitePrimeModelProb C (fun S => (C ∩ S).card = 1) = blockGoodProbability C := by
  classical
  let : DecidablePred (fun S : Finset ℕ => (C ∩ S).card = 1) :=
    fun _ => Classical.propDecidable _
  dsimp [finitePrimeModelProb, blockGoodProbability]
  symm
  refine Finset.sum_bij (fun q _hq => ({q} : Finset ℕ)) ?hi ?inj ?surj ?h
  · intro q hq
    simp [hq]
  · intro q hq r hr hqr
    simpa using congrArg (fun T : Finset ℕ => q ∈ T) hqr
  · intro S hS
    have hSpow : S ∈ C.powerset := (Finset.mem_filter.mp hS).1
    have hcard_inter : (C ∩ S).card = 1 := (Finset.mem_filter.mp hS).2
    have hsub : S ⊆ C := Finset.mem_powerset.mp hSpow
    have hinter : C ∩ S = S := Finset.inter_eq_right.mpr hsub
    rw [hinter] at hcard_inter
    rcases Finset.card_eq_one.mp hcard_inter with ⟨q, rfl⟩
    have hq : q ∈ C := by
      have hsingle : ({q} : Finset ℕ) ⊆ C := hsub
      exact Finset.singleton_subset_iff.mp hsingle
    exact ⟨q, hq, by simp⟩
  · intro q hq
    exact (selectionWeight_singleton C hq).symm

private lemma finitePrimeModelProb_block_bad (C : Finset ℕ) :
    finitePrimeModelProb C (fun S => (C ∩ S).card ≠ 1) =
      1 - blockGoodProbability C := by
  rw [finitePrimeModelProb_compl C (fun S => (C ∩ S).card = 1),
    finitePrimeModelProb_block_good]

/-- Per-block good-with-residue probability: for B consisting of primes,
the pmodel of "exactly one selected ∧ that one has residue ≡ a mod d" equals
`blockGoodProbability B · blockConditionalResidueProbability B d a`.
Paper §6.2 line 1732 conditional probability factorization at the per-block level. -/
private lemma finitePrimeModelProb_block_good_with_residue {B : Finset ℕ} {d a : ℕ}
    (h_prime : ∀ q ∈ B, q.Prime) :
    finitePrimeModelProb B
        (fun S => ∃ q ∈ B, q % d = a % d ∧ S = ({q} : Finset ℕ)) =
      blockGoodProbability B * blockConditionalResidueProbability B d a := by
  classical
  rw [← block_joint_good_residue_prob h_prime]
  let : DecidablePred (fun S : Finset ℕ =>
    ∃ q ∈ B, q % d = a % d ∧ S = ({q} : Finset ℕ)) :=
    fun _ => Classical.propDecidable _
  unfold finitePrimeModelProb
  -- Goal: ∑ S ∈ B.powerset.filter (...), selectionWeight B S =
  --       ∑ q ∈ B.filter (q%d=a%d), (1/q) · ∏_{B.erase q} (1 - 1/r)
  symm
  refine Finset.sum_bij (fun (q : ℕ) (_hq) => ({q} : Finset ℕ)) ?hi ?inj ?surj ?h
  · -- {q} ∈ B.powerset.filter (...)
    intro q hq_filter
    rw [Finset.mem_filter] at hq_filter
    have hq_mem : q ∈ B := hq_filter.1
    have hq_res : q % d = a % d := hq_filter.2
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_powerset]; exact Finset.singleton_subset_iff.mpr hq_mem
    · exact ⟨q, hq_mem, hq_res, rfl⟩
  · -- Injectivity: {q} = {r} ⟹ q = r
    intro q _ r _ hqr
    exact Finset.singleton_injective hqr
  · -- Surjectivity
    intro S hS
    rw [Finset.mem_filter] at hS
    rcases hS.2 with ⟨q, hq_mem, hq_res, hSq⟩
    refine ⟨q, ?_, hSq.symm⟩
    rw [Finset.mem_filter]
    exact ⟨hq_mem, hq_res⟩
  · -- Per-element: selectionWeight B {q} = (1/q) · ∏_{B.erase q} (1 - 1/r)
    intro q hq_filter
    rw [Finset.mem_filter] at hq_filter
    have hq_mem : q ∈ B := hq_filter.1
    exact (selectionWeight_singleton B hq_mem).symm

private lemma selectionWeight_union {U V S T : Finset ℕ} (hUV : Disjoint U V)
    (hS : S ⊆ U) (hT : T ⊆ V) :
    selectionWeight (U ∪ V) (S ∪ T) = selectionWeight U S * selectionWeight V T := by
  classical
  dsimp [selectionWeight]
  rw [Finset.prod_union hUV]
  congr 1
  · apply Finset.prod_congr rfl
    intro q hqU
    have hqT : q ∉ T := by
      intro hqT
      exact (Finset.disjoint_left.mp hUV) hqU (hT hqT)
    by_cases hqS : q ∈ S <;> simp [hqS, hqT]
  · apply Finset.prod_congr rfl
    intro q hqV
    have hqS : q ∉ S := by
      intro hqS
      exact (Finset.disjoint_left.mp hUV) (hS hqS) hqV
    by_cases hqT : q ∈ T <;> simp [hqS, hqT]

private lemma sum_powerset_union_disjoint {U V : Finset ℕ} (hUV : Disjoint U V)
    (F : Finset ℕ → Finset ℕ → ℝ) :
    (∑ X ∈ (U ∪ V).powerset, F (X ∩ U) (X ∩ V)) =
      ∑ p ∈ U.powerset ×ˢ V.powerset, F p.1 p.2 := by
  classical
  refine Finset.sum_bij'
    (fun X _hX => (X ∩ U, X ∩ V)) (fun p _hp => p.1 ∪ p.2)
    ?hi ?hj ?left ?right ?h
  · intro X hX
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hpU, hpV⟩
    exact Finset.mem_powerset.mpr (Finset.union_subset_union (Finset.mem_powerset.mp hpU)
      (Finset.mem_powerset.mp hpV))
  · intro X hX
    have hsub : X ⊆ U ∪ V := Finset.mem_powerset.mp hX
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro h
      rcases h with h | h <;> exact h.1
    · intro hx
      have hxUV := hsub hx
      simp only [Finset.mem_union] at hxUV
      rcases hxUV with hxU | hxV
      · exact Or.inl ⟨hx, hxU⟩
      · exact Or.inr ⟨hx, hxV⟩
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hpU, hpV⟩
    have hS : p.1 ⊆ U := Finset.mem_powerset.mp hpU
    have hT : p.2 ⊆ V := Finset.mem_powerset.mp hpV
    apply Prod.ext
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · intro h
        rcases h.1 with hxS | hxT
        · exact hxS
        · exact False.elim ((Finset.disjoint_left.mp hUV) h.2 (hT hxT))
      · intro hxS
        exact ⟨Or.inl hxS, hS hxS⟩
    · ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · intro h
        rcases h.1 with hxS | hxT
        · exact False.elim ((Finset.disjoint_left.mp hUV) (hS hxS) h.2)
        · exact hxT
      · intro hxT
        exact ⟨Or.inr hxT, hT hxT⟩
  · intro X hX
    rfl

private lemma finitePrimeModelProb_union_inter {U V : Finset ℕ} (hUV : Disjoint U V)
    (P Q : Finset ℕ → Prop) :
    finitePrimeModelProb (U ∪ V) (fun X => P (X ∩ U) ∧ Q (X ∩ V)) =
      finitePrimeModelProb U P * finitePrimeModelProb V Q := by
  classical
  let : DecidablePred P := fun _ => Classical.propDecidable _
  let : DecidablePred Q := fun _ => Classical.propDecidable _
  let : DecidablePred (fun X : Finset ℕ => P (X ∩ U) ∧ Q (X ∩ V)) :=
    fun _ => Classical.propDecidable _
  let W : Finset ℕ → Finset ℕ → ℝ := fun S T =>
    if P S ∧ Q T then selectionWeight U S * selectionWeight V T else 0
  dsimp [finitePrimeModelProb]
  rw [Finset.sum_filter]
  calc
    (∑ X ∈ (U ∪ V).powerset,
        if P (X ∩ U) ∧ Q (X ∩ V) then selectionWeight (U ∪ V) X else 0) =
      ∑ X ∈ (U ∪ V).powerset, W (X ∩ U) (X ∩ V) := by
      apply Finset.sum_congr rfl
      intro X hX
      dsimp [W]
      by_cases hPQ : P (X ∩ U) ∧ Q (X ∩ V)
      · simp [hPQ]
        have hsub : X ⊆ U ∪ V := Finset.mem_powerset.mp hX
        have hsplit : (X ∩ U) ∪ (X ∩ V) = X := by
          ext x
          simp only [Finset.mem_union, Finset.mem_inter]
          constructor
          · intro h
            rcases h with h | h <;> exact h.1
          · intro hx
            have hxUV := hsub hx
            simp only [Finset.mem_union] at hxUV
            rcases hxUV with hxU | hxV
            · exact Or.inl ⟨hx, hxU⟩
            · exact Or.inr ⟨hx, hxV⟩
        calc
          selectionWeight (U ∪ V) X =
              selectionWeight (U ∪ V) ((X ∩ U) ∪ (X ∩ V)) := by rw [hsplit]
          _ = selectionWeight U (X ∩ U) * selectionWeight V (X ∩ V) :=
            selectionWeight_union hUV Finset.inter_subset_right Finset.inter_subset_right
      · simp [hPQ]
    _ = ∑ p ∈ U.powerset ×ˢ V.powerset, W p.1 p.2 := by
      exact sum_powerset_union_disjoint hUV W
    _ = ∑ S ∈ U.powerset, (if P S then selectionWeight U S else 0) *
          ∑ T ∈ V.powerset, if Q T then selectionWeight V T else 0 := by
      dsimp [W]
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hP : P S
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        by_cases hQ : Q T <;> simp [hP, hQ]
      · simp [hP]
    _ = (∑ S ∈ U.powerset, if P S then selectionWeight U S else 0) *
          ∑ T ∈ V.powerset, if Q T then selectionWeight V T else 0 := by
      exact (Finset.sum_mul U.powerset (fun S => if P S then selectionWeight U S else 0)
        (∑ T ∈ V.powerset, if Q T then selectionWeight V T else 0)).symm
    _ = (∑ S ∈ U.powerset.filter P, selectionWeight U S) *
          ∑ T ∈ V.powerset.filter Q, selectionWeight V T := by
      rw [Finset.sum_filter, Finset.sum_filter]

private lemma finitePrimeModelProb_congr {U : Finset ℕ} {Q R : Finset ℕ → Prop}
    (h : ∀ S, S ⊆ U → (Q S ↔ R S)) :
    finitePrimeModelProb U Q = finitePrimeModelProb U R := by
  classical
  let : DecidablePred Q := fun _ => Classical.propDecidable _
  let : DecidablePred R := fun _ => Classical.propDecidable _
  dsimp [finitePrimeModelProb]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · intro hS
    exact ⟨hS.1, (h S hS.1).mp hS.2⟩
  · intro hS
    exact ⟨hS.1, (h S hS.1).mpr hS.2⟩

private lemma inter_inter_of_subset_right {D S R : Finset ℕ} (hD : D ⊆ R) :
    D ∩ (S ∩ R) = D ∩ S := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · intro h
    exact ⟨h.1, h.2.1⟩
  · intro h
    exact ⟨h.1, h.2, hD h.1⟩

private lemma subset_sdiff_of_subset_of_disjoint {D C U : Finset ℕ} (hDU : D ⊆ U)
    (hdisj : Disjoint D C) : D ⊆ U \ C := by
  intro x hx
  exact Finset.mem_sdiff.mpr ⟨hDU hx, fun hxC => (Finset.disjoint_left.mp hdisj) hx hxC⟩

private lemma finitePrimeModelProb_badEvents (U : Finset ℕ) (F : ℕ → Finset ℕ)
    (B : Finset ℕ)
    (hBU : ∀ k ∈ B, F k ⊆ U)
    (hpair : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (F i) (F j)) :
    finitePrimeModelProb U (fun S => ∀ k ∈ B, (F k ∩ S).card ≠ 1) =
      ∏ k ∈ B, (1 - blockGoodProbability (F k)) := by
  classical
  revert U hBU hpair
  refine Finset.induction_on B ?base ?step
  · intro U hBU hpair
    simp [finitePrimeModelProb_true]
  · intro k B hkB ih U hBU hpair
    let C := F k
    let R := U \ C
    have hCsub : C ⊆ U := hBU k (Finset.mem_insert_self k B)
    have hUeq : C ∪ R = U := by
      dsimp [R]
      exact Finset.union_sdiff_of_subset hCsub
    have hdisjCR : Disjoint C R := by
      dsimp [R]
      exact disjoint_sdiff_self_right
    have hBU_R : ∀ i ∈ B, F i ⊆ R := by
      intro i hi
      have hiU : F i ⊆ U := hBU i (Finset.mem_insert_of_mem hi)
      have hidisj : Disjoint (F i) C := by
        dsimp [C]
        exact hpair i (Finset.mem_insert_of_mem hi) k (Finset.mem_insert_self k B) (by
          intro hik
          exact hkB (by simpa [hik] using hi))
      exact subset_sdiff_of_subset_of_disjoint hiU hidisj
    have hpair_B : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (F i) (F j) := by
      intro i hi j hj hij
      exact hpair i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    calc
      finitePrimeModelProb U (fun S => ∀ i ∈ insert k B, (F i ∩ S).card ≠ 1) =
          finitePrimeModelProb (C ∪ R)
            (fun S => ∀ i ∈ insert k B, (F i ∩ S).card ≠ 1) := by
        rw [hUeq]
      _ = finitePrimeModelProb (C ∪ R)
            (fun S => (C ∩ (S ∩ C)).card ≠ 1 ∧
              ∀ i ∈ B, (F i ∩ (S ∩ R)).card ≠ 1) := by
        apply finitePrimeModelProb_congr
        intro S hS
        constructor
        · intro h
          constructor
          · have hk : (F k ∩ S).card ≠ 1 := h k (Finset.mem_insert_self k B)
            dsimp [C]
            rwa [show F k ∩ (S ∩ F k) = F k ∩ S by
              ext x
              simp [and_comm]]
          · intro i hi
            have hbad : (F i ∩ S).card ≠ 1 := h i (Finset.mem_insert_of_mem hi)
            rwa [inter_inter_of_subset_right (hBU_R i hi)]
        · intro h i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · have hk : (C ∩ (S ∩ C)).card ≠ 1 := h.1
            rwa [show C ∩ (S ∩ C) = C ∩ S by
              ext x
              simp [and_comm]] at hk
          · have hbad : (F i ∩ (S ∩ R)).card ≠ 1 := h.2 i hi
            rwa [inter_inter_of_subset_right (hBU_R i hi)] at hbad
      _ = finitePrimeModelProb C (fun T => (C ∩ T).card ≠ 1) *
            finitePrimeModelProb R (fun T => ∀ i ∈ B, (F i ∩ T).card ≠ 1) := by
        exact finitePrimeModelProb_union_inter hdisjCR
          (fun T => (C ∩ T).card ≠ 1)
          (fun T => ∀ i ∈ B, (F i ∩ T).card ≠ 1)
      _ = (1 - blockGoodProbability C) * ∏ i ∈ B, (1 - blockGoodProbability (F i)) := by
        rw [finitePrimeModelProb_block_bad, ih R hBU_R hpair_B]
      _ = ∏ i ∈ insert k B, (1 - blockGoodProbability (F i)) := by
        dsimp [C]
        rw [Finset.prod_insert hkB]

private lemma finitePrimeModelProb_blockEvents (U : Finset ℕ) (F : ℕ → Finset ℕ)
    (A B : Finset ℕ)
    (hsub : ∀ k ∈ A ∪ B, F k ⊆ U)
    (hpair : ∀ i ∈ A ∪ B, ∀ j ∈ A ∪ B, i ≠ j → Disjoint (F i) (F j))
    (hAB : Disjoint A B) :
    finitePrimeModelProb U (blockEvents F A B) =
      (∏ k ∈ A, blockGoodProbability (F k)) *
        ∏ k ∈ B, (1 - blockGoodProbability (F k)) := by
  classical
  revert U B
  refine Finset.induction_on A ?base ?step
  · intro U B hsub hpair hAB
    have hBU : ∀ k ∈ B, F k ⊆ U := by
      intro k hk
      exact hsub k (Finset.mem_union_right _ hk)
    have hpair_B : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (F i) (F j) := by
      intro i hi j hj hij
      exact hpair i (Finset.mem_union_right _ hi) j (Finset.mem_union_right _ hj) hij
    calc
      finitePrimeModelProb U (blockEvents F ∅ B) =
          finitePrimeModelProb U (fun S => ∀ k ∈ B, (F k ∩ S).card ≠ 1) := by
        apply finitePrimeModelProb_congr
        intro S hS
        simp [blockEvents]
      _ = ∏ k ∈ B, (1 - blockGoodProbability (F k)) :=
        finitePrimeModelProb_badEvents U F B hBU hpair_B
      _ = (∏ k ∈ (∅ : Finset ℕ), blockGoodProbability (F k)) *
            ∏ k ∈ B, (1 - blockGoodProbability (F k)) := by
        simp
  · intro k A hkA ih U B hsub hpair hAB
    let C := F k
    let R := U \ C
    have hCsub : C ⊆ U := hsub k (Finset.mem_union_left _ (Finset.mem_insert_self k A))
    have hUeq : C ∪ R = U := by
      dsimp [R]
      exact Finset.union_sdiff_of_subset hCsub
    have hdisjCR : Disjoint C R := by
      dsimp [R]
      exact disjoint_sdiff_self_right
    have hk_not_B : k ∉ B := by
      intro hkB
      exact (Finset.disjoint_left.mp hAB) (Finset.mem_insert_self k A) hkB
    have hsub_R : ∀ i ∈ A ∪ B, F i ⊆ R := by
      intro i hi
      have hi_full : i ∈ insert k A ∪ B := by
        rcases Finset.mem_union.mp hi with hiA | hiB
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hiA)
        · exact Finset.mem_union_right _ hiB
      have hiU : F i ⊆ U := hsub i hi_full
      have hne : i ≠ k := by
        intro hik
        rcases Finset.mem_union.mp hi with hiA | hiB
        · exact hkA (by simpa [hik] using hiA)
        · exact hk_not_B (by simpa [hik] using hiB)
      have hidisj : Disjoint (F i) C := by
        dsimp [C]
        exact hpair i hi_full k
          (Finset.mem_union_left _ (Finset.mem_insert_self k A)) hne
      exact subset_sdiff_of_subset_of_disjoint hiU hidisj
    have hpair_R :
        ∀ i ∈ A ∪ B, ∀ j ∈ A ∪ B, i ≠ j → Disjoint (F i) (F j) := by
      intro i hi j hj hij
      have hi_full : i ∈ insert k A ∪ B := by
        rcases Finset.mem_union.mp hi with hiA | hiB
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hiA)
        · exact Finset.mem_union_right _ hiB
      have hj_full : j ∈ insert k A ∪ B := by
        rcases Finset.mem_union.mp hj with hjA | hjB
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hjA)
        · exact Finset.mem_union_right _ hjB
      exact hpair i hi_full j hj_full hij
    have hAB_R : Disjoint A B :=
      hAB.mono_left (by intro i hi; exact Finset.mem_insert_of_mem hi)
    calc
      finitePrimeModelProb U (blockEvents F (insert k A) B) =
          finitePrimeModelProb (C ∪ R) (blockEvents F (insert k A) B) := by
        rw [hUeq]
      _ = finitePrimeModelProb (C ∪ R)
            (fun S => (C ∩ (S ∩ C)).card = 1 ∧ blockEvents F A B (S ∩ R)) := by
        apply finitePrimeModelProb_congr
        intro S hS
        constructor
        · intro h
          constructor
          · have hk_good : (F k ∩ S).card = 1 := h.1 k (Finset.mem_insert_self k A)
            dsimp [C]
            rwa [show F k ∩ (S ∩ F k) = F k ∩ S by
              ext x
              simp [and_comm]]
          · constructor
            · intro i hi
              have hgood : (F i ∩ S).card = 1 := h.1 i (Finset.mem_insert_of_mem hi)
              rwa [inter_inter_of_subset_right (hsub_R i (Finset.mem_union_left _ hi))]
            · intro i hi
              have hbad : (F i ∩ S).card ≠ 1 := h.2 i hi
              rwa [inter_inter_of_subset_right (hsub_R i (Finset.mem_union_right _ hi))]
        · intro h
          constructor
          · intro i hi
            rw [Finset.mem_insert] at hi
            rcases hi with rfl | hi
            · have hk_good : (C ∩ (S ∩ C)).card = 1 := h.1
              rwa [show C ∩ (S ∩ C) = C ∩ S by
                ext x
                simp [and_comm]] at hk_good
            · have hgood : (F i ∩ (S ∩ R)).card = 1 := h.2.1 i hi
              rwa [inter_inter_of_subset_right (hsub_R i (Finset.mem_union_left _ hi))]
                at hgood
          · intro i hi
            have hbad : (F i ∩ (S ∩ R)).card ≠ 1 := h.2.2 i hi
            rwa [inter_inter_of_subset_right (hsub_R i (Finset.mem_union_right _ hi))]
              at hbad
      _ = finitePrimeModelProb C (fun T => (C ∩ T).card = 1) *
            finitePrimeModelProb R (blockEvents F A B) := by
        exact finitePrimeModelProb_union_inter hdisjCR
          (fun T => (C ∩ T).card = 1) (blockEvents F A B)
      _ = blockGoodProbability C *
            ((∏ i ∈ A, blockGoodProbability (F i)) *
              ∏ i ∈ B, (1 - blockGoodProbability (F i))) := by
        rw [finitePrimeModelProb_block_good, ih R B hsub_R hpair_R hAB_R]
      _ = (∏ i ∈ insert k A, blockGoodProbability (F i)) *
            ∏ i ∈ B, (1 - blockGoodProbability (F i)) := by
        dsimp [C]
        rw [Finset.prod_insert hkA]
        ring

/-- Residue-extended `blockEvents` factorization (paper §6.2 line 1722-1735).
For good blocks (in A), include both "good" and "specific residue" conditions;
for bad blocks (in B), only "not good".  The factorization includes residue
probabilities at A blocks. -/
private lemma finitePrimeModelProb_blockEvents_with_residues (U : Finset ℕ)
    (F : ℕ → Finset ℕ) (A B : Finset ℕ) (d : ℕ) (resvec : ℕ → ℕ)
    (hsub : ∀ k ∈ A ∪ B, F k ⊆ U)
    (hpair : ∀ i ∈ A ∪ B, ∀ j ∈ A ∪ B, i ≠ j → Disjoint (F i) (F j))
    (hAB : Disjoint A B)
    (hF_prime : ∀ k ∈ A, ∀ q ∈ F k, q.Prime) :
    finitePrimeModelProb U
      (fun S =>
        (∀ k ∈ A, ∃ q ∈ F k, F k ∩ S = ({q} : Finset ℕ) ∧ q % d = (resvec k) % d) ∧
        (∀ k ∈ B, (F k ∩ S).card ≠ 1)) =
      (∏ k ∈ A, blockGoodProbability (F k) *
                blockConditionalResidueProbability (F k) d (resvec k)) *
      ∏ k ∈ B, (1 - blockGoodProbability (F k)) := by
  classical
  revert U B hF_prime
  refine Finset.induction_on A ?base ?step
  · -- Base case: A = ∅
    intro U B hsub hpair hAB hF_prime
    rw [Finset.prod_empty, one_mul]
    have hBU : ∀ k ∈ B, F k ⊆ U :=
      fun k hk => hsub k (Finset.mem_union_right _ hk)
    have hpair_B : ∀ i ∈ B, ∀ j ∈ B, i ≠ j → Disjoint (F i) (F j) := by
      intro i hi j hj hij
      exact hpair i (Finset.mem_union_right _ hi) j (Finset.mem_union_right _ hj) hij
    rw [show (fun S : Finset ℕ =>
        (∀ k ∈ (∅ : Finset ℕ), ∃ q ∈ F k, F k ∩ S = ({q} : Finset ℕ) ∧
          q % d = (resvec k) % d) ∧ (∀ k ∈ B, (F k ∩ S).card ≠ 1)) =
        (fun S => ∀ k ∈ B, (F k ∩ S).card ≠ 1) from by funext S; simp]
    exact finitePrimeModelProb_badEvents U F B hBU hpair_B
  · -- Inductive step: A → insert k A.
    intro k A hkA ih U B hsub hpair hAB hF_prime
    let C := F k
    let R := U \ C
    have hCsub : C ⊆ U := hsub k (Finset.mem_union_left _ (Finset.mem_insert_self k A))
    have hUeq : C ∪ R = U := by dsimp [R]; exact Finset.union_sdiff_of_subset hCsub
    have hdisjCR : Disjoint C R := by dsimp [R]; exact disjoint_sdiff_self_right
    have hk_not_B : k ∉ B := fun hkB =>
      (Finset.disjoint_left.mp hAB) (Finset.mem_insert_self k A) hkB
    have hC_prime : ∀ q ∈ C, q.Prime :=
      hF_prime k (Finset.mem_insert_self k A)
    have hsub_R : ∀ i ∈ A ∪ B, F i ⊆ R := by
      intro i hi
      have hi_full : i ∈ insert k A ∪ B := by
        rcases Finset.mem_union.mp hi with hiA | hiB
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hiA)
        · exact Finset.mem_union_right _ hiB
      have hiU : F i ⊆ U := hsub i hi_full
      have hne : i ≠ k := by
        intro hik
        rcases Finset.mem_union.mp hi with hiA | hiB
        · exact hkA (by simpa [hik] using hiA)
        · exact hk_not_B (by simpa [hik] using hiB)
      have hidisj : Disjoint (F i) C :=
        hpair i hi_full k (Finset.mem_union_left _ (Finset.mem_insert_self k A)) hne
      exact subset_sdiff_of_subset_of_disjoint hiU hidisj
    have hpair_R : ∀ i ∈ A ∪ B, ∀ j ∈ A ∪ B, i ≠ j → Disjoint (F i) (F j) := by
      intro i hi j hj hij
      have hi_full : i ∈ insert k A ∪ B := by
        rcases Finset.mem_union.mp hi with hiA | hiB
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hiA)
        · exact Finset.mem_union_right _ hiB
      have hj_full : j ∈ insert k A ∪ B := by
        rcases Finset.mem_union.mp hj with hjA | hjB
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hjA)
        · exact Finset.mem_union_right _ hjB
      exact hpair i hi_full j hj_full hij
    have hAB_R : Disjoint A B :=
      hAB.mono_left (fun i hi => Finset.mem_insert_of_mem hi)
    have hF_prime_R : ∀ k ∈ A, ∀ q ∈ F k, q.Prime :=
      fun k hk => hF_prime k (Finset.mem_insert_of_mem hk)
    set pred_orig : Finset ℕ → Prop := fun S =>
      (∀ k' ∈ insert k A, ∃ q ∈ F k', F k' ∩ S = ({q} : Finset ℕ) ∧
        q % d = (resvec k') % d) ∧
      (∀ k' ∈ B, (F k' ∩ S).card ≠ 1) with hpred_orig
    set P_C : Finset ℕ → Prop := fun T =>
      ∃ q ∈ C, C ∩ T = ({q} : Finset ℕ) ∧ q % d = (resvec k) % d with hP_C
    set Q_R : Finset ℕ → Prop := fun T =>
      (∀ k' ∈ A, ∃ q ∈ F k', F k' ∩ T = ({q} : Finset ℕ) ∧
        q % d = (resvec k') % d) ∧
      (∀ k' ∈ B, (F k' ∩ T).card ≠ 1) with hQ_R
    calc finitePrimeModelProb U pred_orig
        = finitePrimeModelProb (C ∪ R) pred_orig := by rw [hUeq]
      _ = finitePrimeModelProb (C ∪ R)
            (fun S => P_C (S ∩ C) ∧ Q_R (S ∩ R)) := by
        apply finitePrimeModelProb_congr
        intro S _hS
        constructor
        · rintro ⟨h_A, h_B⟩
          refine ⟨?_, ?_, ?_⟩
          · -- good-with-residue at k
            have hk_good := h_A k (Finset.mem_insert_self k A)
            rcases hk_good with ⟨q, hq_mem, hq_eq, hq_res⟩
            refine ⟨q, hq_mem, ?_, hq_res⟩
            -- C ∩ (S ∩ C) = F k ∩ S
            have : C ∩ (S ∩ C) = F k ∩ S := by
              ext x; simp [C, and_comm, and_left_comm]
            rw [this]; exact hq_eq
          · -- A side residue conditions
            intro i hi
            have hi_full : i ∈ insert k A := Finset.mem_insert_of_mem hi
            rcases h_A i hi_full with ⟨q, hq_mem, hq_eq, hq_res⟩
            refine ⟨q, hq_mem, ?_, hq_res⟩
            -- F i ∩ (S ∩ R) = F i ∩ S since F i ⊆ R
            have hFi_R : F i ⊆ R :=
              hsub_R i (Finset.mem_union_left _ hi)
            have : F i ∩ (S ∩ R) = F i ∩ S := by
              ext x; simp only [Finset.mem_inter]
              exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩,
                     fun ⟨h1, h2⟩ => ⟨h1, h2, hFi_R h1⟩⟩
            rw [this]; exact hq_eq
          · -- B side bad conditions
            intro i hi
            have hbad := h_B i hi
            have hFi_R : F i ⊆ R :=
              hsub_R i (Finset.mem_union_right _ hi)
            have : F i ∩ (S ∩ R) = F i ∩ S := by
              ext x; simp only [Finset.mem_inter]
              exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩,
                     fun ⟨h1, h2⟩ => ⟨h1, h2, hFi_R h1⟩⟩
            rw [this]; exact hbad
        · rintro ⟨h_k, h_A_rest, h_B_rest⟩
          refine ⟨?_, ?_⟩
          · intro k' hk'_full
            rw [Finset.mem_insert] at hk'_full
            rcases hk'_full with rfl | hk'_A
            · -- k' = k (substituted)
              rcases h_k with ⟨q, hq_mem, hq_eq, hq_res⟩
              refine ⟨q, hq_mem, ?_, hq_res⟩
              have h_inter_eq : F k' ∩ (S ∩ F k') = F k' ∩ S := by
                ext x; simp only [Finset.mem_inter]; tauto
              show F k' ∩ S = ({q} : Finset ℕ)
              rw [← h_inter_eq]; exact hq_eq
            · -- k' ∈ A
              rcases h_A_rest k' hk'_A with ⟨q, hq_mem, hq_eq, hq_res⟩
              refine ⟨q, hq_mem, ?_, hq_res⟩
              have hFk'_R : F k' ⊆ R :=
                hsub_R k' (Finset.mem_union_left _ hk'_A)
              have : F k' ∩ (S ∩ R) = F k' ∩ S := by
                ext x; simp only [Finset.mem_inter]
                exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩,
                       fun ⟨h1, h2⟩ => ⟨h1, h2, hFk'_R h1⟩⟩
              rw [this] at hq_eq; exact hq_eq
          · intro k' hk'_B
            have h_bad := h_B_rest k' hk'_B
            have hFk'_R : F k' ⊆ R :=
              hsub_R k' (Finset.mem_union_right _ hk'_B)
            have : F k' ∩ (S ∩ R) = F k' ∩ S := by
              ext x; simp only [Finset.mem_inter]
              exact ⟨fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩,
                     fun ⟨h1, h2⟩ => ⟨h1, h2, hFk'_R h1⟩⟩
            rw [this] at h_bad; exact h_bad
      _ = finitePrimeModelProb C P_C * finitePrimeModelProb R Q_R := by
        exact finitePrimeModelProb_union_inter hdisjCR P_C Q_R
      _ = (blockGoodProbability C * blockConditionalResidueProbability C d (resvec k)) *
          ((∏ i ∈ A, blockGoodProbability (F i) *
              blockConditionalResidueProbability (F i) d (resvec i)) *
           ∏ i ∈ B, (1 - blockGoodProbability (F i))) := by
        congr 1
        · -- C side: pmodel C P_C = blockGoodProb C * blockCondResProb C d (resvec k)
          -- P_C T = ∃ q ∈ C, C ∩ T = {q} ∧ q%d = (resvec k)%d.
          -- finitePrimeModelProb_block_good_with_residue uses ∃ q ∈ B, q%d=a%d ∧ S = {q}.
          -- For T ⊆ C (which holds in pmodel context), C ∩ T = T, so the predicates match.
          show finitePrimeModelProb C P_C =
            blockGoodProbability C * blockConditionalResidueProbability C d (resvec k)
          have h_eq : finitePrimeModelProb C P_C =
              finitePrimeModelProb C
                (fun S => ∃ q ∈ C, q % d = (resvec k) % d ∧ S = ({q} : Finset ℕ)) := by
            apply finitePrimeModelProb_congr
            intro S hS
            show P_C S ↔ _
            rw [hP_C]
            have h_inter : C ∩ S = S := Finset.inter_eq_right.mpr hS
            constructor
            · rintro ⟨q, hq_mem, h_inter_eq, h_res⟩
              refine ⟨q, hq_mem, h_res, ?_⟩
              rw [h_inter] at h_inter_eq
              exact h_inter_eq
            · rintro ⟨q, hq_mem, h_res, h_eq_sing⟩
              refine ⟨q, hq_mem, ?_, h_res⟩
              rw [h_inter, h_eq_sing]
          rw [h_eq]
          exact finitePrimeModelProb_block_good_with_residue hC_prime
        · show finitePrimeModelProb R Q_R =
            (∏ i ∈ A, blockGoodProbability (F i) *
              blockConditionalResidueProbability (F i) d (resvec i)) *
            ∏ i ∈ B, (1 - blockGoodProbability (F i))
          rw [hQ_R]
          exact ih R B hsub_R hpair_R hAB_R hF_prime_R
      _ = (∏ i ∈ insert k A, blockGoodProbability (F i) *
            blockConditionalResidueProbability (F i) d (resvec i)) *
          ∏ i ∈ B, (1 - blockGoodProbability (F i)) := by
        dsimp [C]
        rw [Finset.prod_insert hkA]
        ring

/-- A subset product satisfying the composite-successor congruence and size bounds. -/
def AdmissibleCompositeProduct (A y : ℝ) (d : ℕ) (T : Finset ℕ) : Prop :=
  T.Nonempty ∧
    (∀ q ∈ T, q.Prime ∧ Real.exp y < (q : ℝ) ∧ (q : ℝ) ≤ Real.exp (y ^ (A - 1))) ∧
      let e : ℕ := ∏ q ∈ T, q
      e ≡ 1 [MOD d] ∧ d < e ∧ (e : ℝ) ≤ Real.exp (y ^ A)

/-- Success event in the finite product model: some selected subproduct is admissible. -/
private def CompositeProductExists (A y : ℝ) (d : ℕ) (S : Finset ℕ) : Prop :=
  ∃ T : Finset ℕ, T ⊆ S ∧ AdmissibleCompositeProduct A y d T

/-- Failure event in the finite product model. -/
private def CompositeProductFailure (A y : ℝ) (d : ℕ) (S : Finset ℕ) : Prop :=
  ¬ CompositeProductExists A y d S

/-- A usable composite successor divisor matching paper §6.2 line 1521-1525
verbatim: there exists a squarefree product `e = ∏_{q ∈ T} q` of selected primes
`q ∈ (exp y, exp(y^{A-1})]` such that `e ≡ 1 (mod d)`, `e > d`, `e ≤ exp(y^A)`,
and `e ∣ n`.

Refactored 2026-04-29 to be paper-faithful: previously this allowed any divisor
`e ≤ exp(y^A)` (lenient), but the paper §6.2 explicitly requires `e` to be a
squarefree product of selected primes from the window. The lenient form forced
a factorial CRT period; the paper-faithful form uses the standard primorial. -/
def GoodCompositeSuccessor (A y : ℝ) (d n : ℕ) : Prop :=
  ∃ T : Finset ℕ, AdmissibleCompositeProduct A y d T ∧ (∏ q ∈ T, q) ∣ n

/-- The finite bad set counted in `composite_successor`, packaged so the direct
integer-counting helper lemmas can share exactly the same target.

Made non-private so that downstream consumers (e.g., `LowerBoundH`) can refer
to the paper-faithful bad set definition by name. -/
def CompositeSuccessorBadSet (A y : ℝ) (d : ℕ) (x : ℝ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ n ≤ ⌊x⌋₊ ∧ d ∣ n ∧ ¬ GoodCompositeSuccessor A y d n}

/-- The periodic core of `CompositeSuccessorBadSet`, with the finite `x` cutoff and
the positive-integer guard removed. -/
def CompositeSuccessorCoreBad (A y : ℝ) (d n : ℕ) : Prop :=
  d ∣ n ∧ ¬ GoodCompositeSuccessor A y d n

/-- Divisor cutoff appearing in the direct CRT bookkeeping for
`GoodCompositeSuccessor`. -/
noncomputable def compositeSuccessorCutoff (A y : ℝ) : ℕ :=
  ⌊Real.exp (y ^ A)⌋₊

/-- A concrete period for the direct integer predicate, matching paper §7.4 line
1182's `M := ∏_{p ≤ y_R} p` (primorial cutoff). Refactored 2026-04-29 to use
primorial since `GoodCompositeSuccessor` is now paper-faithfully restricted to
squarefree products of primes from the window. -/
noncomputable def compositeSuccessorCRTPeriod (A y : ℝ) (d : ℕ) : ℕ :=
  d * primorial (compositeSuccessorCutoff A y)

lemma compositeSuccessorCRTPeriod_pos {A y : ℝ} {d : ℕ} (hd : 1 ≤ d) :
    0 < compositeSuccessorCRTPeriod A y d := by
  dsimp [compositeSuccessorCRTPeriod]
  exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hd) (primorial_pos _)

private lemma d_dvd_compositeSuccessorCRTPeriod (A y : ℝ) (d : ℕ) :
    d ∣ compositeSuccessorCRTPeriod A y d := by
  dsimp [compositeSuccessorCRTPeriod]
  exact dvd_mul_right d (primorial (compositeSuccessorCutoff A y))

private lemma finset_prod_dvd_of_forall_prime_dvd {T : Finset ℕ} {n : ℕ}
    (hprime : ∀ q ∈ T, q.Prime) (hdiv : ∀ q ∈ T, q ∣ n) :
    (∏ q ∈ T, q) ∣ n := by
  classical
  revert hprime hdiv
  refine Finset.induction_on T ?base ?step
  · intro _hprime _hdiv
    simp
  · intro q T hqT ih hprime hdiv
    rw [Finset.prod_insert hqT]
    have hqdiv : q ∣ n := hdiv q (Finset.mem_insert_self q T)
    have hTdiv : (∏ r ∈ T, r) ∣ n := by
      apply ih
      · intro r hr
        exact hprime r (Finset.mem_insert_of_mem hr)
      · intro r hr
        exact hdiv r (Finset.mem_insert_of_mem hr)
    have hcop : Nat.Coprime q (∏ r ∈ T, r) := by
      apply Nat.Coprime.prod_right
      intro r hr
      have hqr : q ≠ r := by
        intro h
        exact hqT (by simpa [← h] using hr)
      exact (Nat.coprime_primes (hprime q (Finset.mem_insert_self q T))
        (hprime r (Finset.mem_insert_of_mem hr))).mpr hqr
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hqdiv hTdiv

/-- Product of admissible primes from window divides the primorial CRT period.
Each prime `q ∈ T` lies in `(exp y, exp(y^{A-1})]` so `q ≤ exp(y^A) = cutoff`,
hence `q ∣ primorial(cutoff)`, and the product is squarefree so `∏T ∣ primorial`. -/
private lemma prod_dvd_compositeSuccessorCRTPeriod_of_admissible {A y : ℝ} {d : ℕ}
    {T : Finset ℕ} (hy : 1 ≤ y) (hadm : AdmissibleCompositeProduct A y d T) :
    (∏ q ∈ T, q) ∣ compositeSuccessorCRTPeriod A y d := by
  classical
  have hwindow : ∀ q ∈ T, q.Prime ∧ Real.exp y < (q : ℝ) ∧
      (q : ℝ) ≤ Real.exp (y ^ (A - 1)) := hadm.2.1
  have hle_e : (∏ q ∈ T, q : ℝ) ≤ Real.exp (y ^ A) := by
    -- The admissible bound: ∏T = e and e ≤ exp(y^A) per AdmissibleCompositeProduct.
    have hT_le : ((∏ q ∈ T, q : ℕ) : ℝ) ≤ Real.exp (y ^ A) := by
      have := hadm.2.2.2.2
      exact_mod_cast this
    convert hT_le using 1
    push_cast
    rfl
  have hprod_dvd_primorial : (∏ q ∈ T, q) ∣ primorial (compositeSuccessorCutoff A y) := by
    apply finset_prod_dvd_of_forall_prime_dvd (T := T) (n := primorial _)
    · intro q hq
      exact (hwindow q hq).1
    · intro q hq
      have hqle : (q : ℝ) ≤ Real.exp (y ^ (A - 1)) := (hwindow q hq).2.2
      have hpow : y ^ ((A - 1) : ℝ) ≤ y ^ (A : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hy (by linarith : (A - 1 : ℝ) ≤ A)
      have hqA : (q : ℝ) ≤ Real.exp (y ^ A) := hqle.trans (Real.exp_le_exp.mpr hpow)
      have hq_le_cutoff : q ≤ compositeSuccessorCutoff A y := by
        dsimp [compositeSuccessorCutoff]
        exact Nat.le_floor hqA
      exact prime_dvd_primorial_of_le (hwindow q hq).1 hq_le_cutoff
  dsimp [compositeSuccessorCRTPeriod]
  exact dvd_mul_of_dvd_right hprod_dvd_primorial d

private lemma dvd_iff_of_mod_compositeSuccessorCRTPeriod_eq {A y : ℝ} {d e n n' : ℕ}
    (heM : e ∣ compositeSuccessorCRTPeriod A y d)
    (hmod : n % compositeSuccessorCRTPeriod A y d =
      n' % compositeSuccessorCRTPeriod A y d) :
    e ∣ n ↔ e ∣ n' := by
  have hmodeq : n ≡ n' [MOD compositeSuccessorCRTPeriod A y d] := by
    simpa [Nat.ModEq] using hmod
  exact hmodeq.dvd_iff heM

private lemma GoodCompositeSuccessor_iff_of_mod {A y : ℝ} {d n n' : ℕ}
    (_hd : 1 ≤ d) (hy : 1 ≤ y)
    (hmod : n % compositeSuccessorCRTPeriod A y d =
      n' % compositeSuccessorCRTPeriod A y d) :
    GoodCompositeSuccessor A y d n ↔ GoodCompositeSuccessor A y d n' := by
  constructor
  · rintro ⟨T, hadm, hTdvd⟩
    have heM := prod_dvd_compositeSuccessorCRTPeriod_of_admissible (A := A) (y := y)
      (d := d) hy hadm
    exact ⟨T, hadm, (dvd_iff_of_mod_compositeSuccessorCRTPeriod_eq heM hmod).mp hTdvd⟩
  · rintro ⟨T, hadm, hTdvd⟩
    have heM := prod_dvd_compositeSuccessorCRTPeriod_of_admissible (A := A) (y := y)
      (d := d) hy hadm
    exact ⟨T, hadm, (dvd_iff_of_mod_compositeSuccessorCRTPeriod_eq heM hmod).mpr hTdvd⟩

lemma CompositeSuccessorCoreBad_iff_of_mod_eq {A y : ℝ} {d n n' : ℕ}
    (hd : 1 ≤ d) (hy : 1 ≤ y)
    (hmod : n % compositeSuccessorCRTPeriod A y d =
      n' % compositeSuccessorCRTPeriod A y d) :
    CompositeSuccessorCoreBad A y d n ↔ CompositeSuccessorCoreBad A y d n' := by
  constructor
  · rintro ⟨hdvd, hgood⟩
    refine ⟨?_, ?_⟩
    · exact (dvd_iff_of_mod_compositeSuccessorCRTPeriod_eq
        (d_dvd_compositeSuccessorCRTPeriod A y d) hmod).mp hdvd
    · intro hgood'
      exact hgood ((GoodCompositeSuccessor_iff_of_mod (A := A) (y := y) hd hy hmod).mpr
        hgood')
  · rintro ⟨hdvd, hgood⟩
    refine ⟨?_, ?_⟩
    · exact (dvd_iff_of_mod_compositeSuccessorCRTPeriod_eq
        (d_dvd_compositeSuccessorCRTPeriod A y d) hmod).mpr hdvd
    · intro hgood'
      exact hgood ((GoodCompositeSuccessor_iff_of_mod (A := A) (y := y) hd hy hmod).mp
        hgood')

lemma CompositeSuccessorCoreBad_iff_of_mod {A y : ℝ} {d n : ℕ}
    (hd : 1 ≤ d) (hy : 1 ≤ y) :
    CompositeSuccessorCoreBad A y d n ↔
      CompositeSuccessorCoreBad A y d (n % compositeSuccessorCRTPeriod A y d) := by
  apply CompositeSuccessorCoreBad_iff_of_mod_eq (A := A) (y := y) hd hy
  have hMpos := compositeSuccessorCRTPeriod_pos (A := A) (y := y) hd
  rw [Nat.mod_eq_of_lt (Nat.mod_lt n hMpos)]

lemma composite_successor_bad_count_le_periodic {A y : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hy : 1 ≤ y) {x : ℝ} (hx : 0 ≤ x) :
    (Nat.card (CompositeSuccessorBadSet A y d x) : ℝ) ≤
      ((Nat.card {r : Fin (compositeSuccessorCRTPeriod A y d) //
          CompositeSuccessorCoreBad A y d r.val} : ℝ) /
        (compositeSuccessorCRTPeriod A y d : ℝ)) * x +
      (compositeSuccessorCRTPeriod A y d : ℝ) := by
  classical
  let M := compositeSuccessorCRTPeriod A y d
  let P : ℕ → Prop := fun n => CompositeSuccessorCoreBad A y d n
  have hMpos : 0 < M := by
    dsimp [M]
    exact compositeSuccessorCRTPeriod_pos (A := A) (y := y) hd
  have hperiod : ∀ n, P n ↔ P (n % M) := by
    intro n
    dsimp [P, M]
    exact CompositeSuccessorCoreBad_iff_of_mod (A := A) (y := y) (d := d) hd hy
  have hfiniteP : ({n : ℕ | n ≤ ⌊x⌋₊ ∧ P n} : Set ℕ).Finite :=
    (Set.finite_Iic ⌊x⌋₊).subset (by intro n hn; exact hn.1)
  have hsub : CompositeSuccessorBadSet A y d x ⊆ {n : ℕ | n ≤ ⌊x⌋₊ ∧ P n} := by
    intro n hn
    rcases hn with ⟨_hnpos, hnle, hdvd, hnotgood⟩
    exact ⟨hnle, hdvd, hnotgood⟩
  have hcard_subset :
      Nat.card (CompositeSuccessorBadSet A y d x) ≤
        Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ P n} :=
    Nat.card_mono hfiniteP hsub
  have hcard_subsetR :
      (Nat.card (CompositeSuccessorBadSet A y d x) : ℝ) ≤
        (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ P n} : ℝ) := by
    exact_mod_cast hcard_subset
  have hcount := periodic_count_le (P := P) (M := M) (N := ⌊x⌋₊) hMpos hperiod
  have hfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hratio_nonneg :
      0 ≤ ((Nat.card {r : Fin M // P r.val} : ℝ) / (M : ℝ)) := by
    exact div_nonneg (by positivity) (by exact_mod_cast hMpos.le)
  calc
    (Nat.card (CompositeSuccessorBadSet A y d x) : ℝ)
        ≤ (Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ P n} : ℝ) := hcard_subsetR
    _ ≤ ((Nat.card {r : Fin M // P r.val} : ℝ) / (M : ℝ)) * (⌊x⌋₊ : ℝ) +
          (M : ℝ) := hcount
    _ ≤ ((Nat.card {r : Fin M // P r.val} : ℝ) / (M : ℝ)) * x + (M : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hfloor_le hratio_nonneg
      linarith

private lemma compositeBlock_mem_cumulative_sdiff (y : ℝ) (k q : ℕ) :
    q ∈ compositeBlock y k ↔
      q ∈ (Finset.filter Nat.Prime
          (Finset.Iic ⌊compositeBlockEndpoint y (k + 1)⌋₊) \
        Finset.filter Nat.Prime (Finset.Iic ⌊compositeBlockEndpoint y k⌋₊)) := by
  have ha_nonneg : 0 ≤ compositeBlockEndpoint y k := Real.exp_nonneg _
  have hb_nonneg : 0 ≤ compositeBlockEndpoint y (k + 1) := Real.exp_nonneg _
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqIic, hqprime, hqgt, _hqle⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hqIic, hqprime⟩
    · intro hqA
      rcases Finset.mem_filter.mp hqA with ⟨hqAIic, _hqprimeA⟩
      have hq_le_a : (q : ℝ) ≤ compositeBlockEndpoint y k :=
        (Nat.le_floor_iff ha_nonneg).mp (Finset.mem_Iic.mp hqAIic)
      linarith
  · intro hq
    rcases Finset.mem_sdiff.mp hq with ⟨hqB, hqnotA⟩
    rcases Finset.mem_filter.mp hqB with ⟨hqBIic, hqprime⟩
    have hqle : (q : ℝ) ≤ compositeBlockEndpoint y (k + 1) :=
      (Nat.le_floor_iff hb_nonneg).mp (Finset.mem_Iic.mp hqBIic)
    have hqgt : compositeBlockEndpoint y k < (q : ℝ) := by
      by_contra hnot
      have hq_le_a : (q : ℝ) ≤ compositeBlockEndpoint y k := le_of_not_gt hnot
      have hqAIic : q ∈ Finset.Iic ⌊compositeBlockEndpoint y k⌋₊ :=
        Finset.mem_Iic.mpr ((Nat.le_floor_iff ha_nonneg).mpr hq_le_a)
      exact hqnotA (Finset.mem_filter.mpr ⟨hqAIic, hqprime⟩)
    exact Finset.mem_filter.mpr ⟨hqBIic, hqprime, hqgt, hqle⟩

private lemma reciprocalPrimeMass_compositeBlock_eq_sub (y : ℝ) (k : ℕ)
    (hy : 0 ≤ y) :
    reciprocalPrimeMass (compositeBlock y k) =
      (∑ p ∈ Finset.filter Nat.Prime
          (Finset.Iic ⌊compositeBlockEndpoint y (k + 1)⌋₊),
        (1 : ℝ) / (p : ℝ)) -
        (∑ p ∈ Finset.filter Nat.Prime
            (Finset.Iic ⌊compositeBlockEndpoint y k⌋₊),
          (1 : ℝ) / (p : ℝ)) := by
  classical
  let B := Finset.filter Nat.Prime (Finset.Iic ⌊compositeBlockEndpoint y (k + 1)⌋₊)
  let A := Finset.filter Nat.Prime (Finset.Iic ⌊compositeBlockEndpoint y k⌋₊)
  have hBA : A ⊆ B := by
    intro q hq
    have ha_nonneg : 0 ≤ compositeBlockEndpoint y k := Real.exp_nonneg _
    have hb_nonneg : 0 ≤ compositeBlockEndpoint y (k + 1) := Real.exp_nonneg _
    have hqA := Finset.mem_filter.mp hq
    have hqle_a : (q : ℝ) ≤ compositeBlockEndpoint y k :=
      (Nat.le_floor_iff ha_nonneg).mp (Finset.mem_Iic.mp hqA.1)
    have hendpoint_mono : compositeBlockEndpoint y k ≤ compositeBlockEndpoint y (k + 1) := by
      dsimp [compositeBlockEndpoint]
      apply Real.exp_le_exp.mpr
      have hkexp : Real.exp (k : ℝ) ≤ Real.exp ((k + 1 : ℕ) : ℝ) := by
        apply Real.exp_le_exp.mpr
        norm_num
      exact mul_le_mul_of_nonneg_left hkexp hy
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Iic.mpr ((Nat.le_floor_iff hb_nonneg).mpr
        (hqle_a.trans hendpoint_mono)), hqA.2⟩
  have hsdiff : compositeBlock y k = B \ A := by
    ext q
    simpa [B, A] using compositeBlock_mem_cumulative_sdiff y k q
  rw [hsdiff, reciprocalPrimeMass]
  have hsum := Finset.sum_sdiff_eq_sub
    (s₁ := A) (s₂ := B) (f := fun p => (1 : ℝ) / (p : ℝ)) hBA
  dsimp [B, A] at hsum ⊢
  exact hsum

/-! ### Paper §6.2 Step 1--7 decomposition for the `A = 20` core. -/

private lemma reciprocalPrimeMass_prime_window_eq_sub (L U : ℝ)
    (hL : 0 ≤ L) (hU : 0 ≤ U) (hLU : L ≤ U) :
    (∑ q ∈ Finset.filter
        (fun q : ℕ => q.Prime ∧ L < (q : ℝ) ∧ (q : ℝ) ≤ U)
        (Finset.Iic ⌊U⌋₊),
      (1 : ℝ) / (q : ℝ)) =
      (∑ q ∈ Finset.filter Nat.Prime (Finset.Iic ⌊U⌋₊), (1 : ℝ) / (q : ℝ)) -
        ∑ q ∈ Finset.filter Nat.Prime (Finset.Iic ⌊L⌋₊), (1 : ℝ) / (q : ℝ) := by
  let sL := Finset.filter Nat.Prime (Finset.Iic ⌊L⌋₊)
  let sU := Finset.filter Nat.Prime (Finset.Iic ⌊U⌋₊)
  have hset :
      Finset.filter (fun q : ℕ => q.Prime ∧ L < (q : ℝ) ∧ (q : ℝ) ≤ U)
          (Finset.Iic ⌊U⌋₊) = sU \ sL := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_sdiff]
    intro hp hqU
    constructor
    · intro h hqL _hp'
      exact (not_le_of_gt h.1 hqL).elim
    · intro h
      constructor
      · by_contra hn
        exact h (le_of_not_gt hn) hp
      · exact hqU
  have hsub : sL ⊆ sU := by
    intro q hq
    simp only [sL, sU, Finset.mem_filter, Finset.mem_Iic] at hq ⊢
    exact ⟨Nat.le_trans hq.1 (Nat.floor_le_floor hLU), hq.2⟩
  rw [hset]
  exact Finset.sum_sdiff_eq_sub hsub

/-- Paper §6.2 line 1534-1540 (d=1 dispatch): Mertens reciprocal mass on the d=1 sub-window
`(exp y, exp(y^2)]` equals `log y + O(1)`. -/
private lemma step1_mertens_subwindow_d_1_mass :
    ∃ C : ℝ, 0 < C ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          |reciprocalPrimeMass (compositePrimeSubWindow_d_1 y) - Real.log y| ≤ C := by
  rcases mertens with ⟨M, Cm, hCm, hmertens⟩
  refine ⟨2 * Cm, by positivity, 2, by norm_num, ?_⟩
  intro y hy
  let L : ℝ := Real.exp y
  let U : ℝ := Real.exp (y ^ ((2 : ℝ)))
  let primeSum : ℝ → ℝ :=
    fun t => ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), (1 : ℝ) / (p : ℝ)
  have hy_ge1 : (1 : ℝ) ≤ y := by linarith
  have hy_le_y2 : y ≤ y ^ ((2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_le hy_ge1 (by norm_num : (1 : ℝ) ≤ 2)
    simpa [Real.rpow_one] using h
  have hL_nonneg : 0 ≤ L := le_of_lt (Real.exp_pos y)
  have hU_nonneg : 0 ≤ U := le_of_lt (Real.exp_pos _)
  have hLU : L ≤ U := by
    dsimp [L, U]
    exact Real.exp_le_exp.mpr hy_le_y2
  have h2exp1 : (2 : ℝ) ≤ Real.exp 1 := by
    simpa using (Real.two_mul_le_exp (x := 1))
  have hL_ge2 : 2 ≤ L := by
    dsimp [L]
    exact h2exp1.trans (Real.exp_le_exp.mpr hy_ge1)
  have hU_ge2 : 2 ≤ U := hL_ge2.trans hLU
  have hwindow : reciprocalPrimeMass (compositePrimeSubWindow_d_1 y) =
      primeSum U - primeSum L := by
    dsimp [reciprocalPrimeMass, compositePrimeSubWindow_d_1, primeSum, L, U]
    change
      (∑ q ∈ Finset.filter
          (fun q : ℕ =>
            q.Prime ∧ Real.exp y < (q : ℝ) ∧
              (q : ℝ) ≤ Real.exp (y ^ ((2 : ℝ))))
          (Finset.Iic ⌊Real.exp (y ^ ((2 : ℝ)))⌋₊),
        (1 : ℝ) / (q : ℝ)) =
        (∑ q ∈ Finset.filter Nat.Prime
            (Finset.Iic ⌊Real.exp (y ^ ((2 : ℝ)))⌋₊),
          (1 : ℝ) / (q : ℝ)) -
          ∑ q ∈ Finset.filter Nat.Prime (Finset.Iic ⌊Real.exp y⌋₊),
            (1 : ℝ) / (q : ℝ)
    exact reciprocalPrimeMass_prime_window_eq_sub L U hL_nonneg hU_nonneg hLU
  have hLm : |primeSum L - Real.log (Real.log L) - M| ≤ Cm / Real.log L := by
    simpa [primeSum] using hmertens L hL_ge2
  have hUm : |primeSum U - Real.log (Real.log U) - M| ≤ Cm / Real.log U := by
    simpa [primeSum] using hmertens U hU_ge2
  have hy_pos : (0 : ℝ) < y := by linarith
  have hlogU : Real.log (Real.log U) = 2 * Real.log y := by
    dsimp [U]
    rw [Real.log_exp, Real.log_rpow hy_pos]
  have hlogL : Real.log (Real.log L) = Real.log y := by
    dsimp [L]
    rw [Real.log_exp]
  have hmainlog : Real.log (Real.log U) - Real.log (Real.log L) = Real.log y := by
    rw [hlogU, hlogL]; ring
  have htri : |(primeSum U - primeSum L) -
      (Real.log (Real.log U) - Real.log (Real.log L))| ≤
      |primeSum L - Real.log (Real.log L) - M| +
        |primeSum U - Real.log (Real.log U) - M| := by
    have hident : (primeSum U - primeSum L) -
        (Real.log (Real.log U) - Real.log (Real.log L)) =
        -(primeSum L - Real.log (Real.log L) - M) +
          (primeSum U - Real.log (Real.log U) - M) := by ring
    rw [hident]
    simpa only [abs_neg] using
      (abs_add_le (-(primeSum L - Real.log (Real.log L) - M))
        (primeSum U - Real.log (Real.log U) - M))
  have hbound : |(primeSum U - primeSum L) -
      (Real.log (Real.log U) - Real.log (Real.log L))| ≤
      Cm / Real.log L + Cm / Real.log U :=
    htri.trans (add_le_add hLm hUm)
  have hy2_ge1 : (1 : ℝ) ≤ y ^ ((2 : ℝ)) := by
    have h := Real.one_le_rpow hy_ge1 (by norm_num : (0 : ℝ) ≤ 2)
    exact h
  have hdivU_le : Cm / Real.log U ≤ Cm := by
    dsimp [U]
    rw [Real.log_exp, div_eq_mul_inv]
    exact mul_le_of_le_one_right (le_of_lt hCm) (inv_le_one_of_one_le₀ hy2_ge1)
  have hdivL_le : Cm / Real.log L ≤ Cm := by
    dsimp [L]
    rw [Real.log_exp, div_eq_mul_inv]
    exact mul_le_of_le_one_right (le_of_lt hCm) (inv_le_one_of_one_le₀ hy_ge1)
  rw [hwindow, ← hmainlog]
  exact hbound.trans (by linarith)

/-- Step 2: block decomposition with `γ = 15`.

The first `M = floor(15 log y)` blocks `(exp(y e^k), exp(y e^(k+1))]` lie in
the `A = 20` window, and each has reciprocal mass `1 + O(1/y)`. -/
private lemma step2_block_decomposition :
    ∃ C : ℝ, 0 < C ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          let M := compositeBlockCount y
          1 ≤ M ∧
            (M : ℝ) ≤ 15 * Real.log y ∧
              ∀ k : ℕ, k < M →
                compositeBlock y k ⊆ compositePrimeWindow 20 y ∧
                  |reciprocalPrimeMass (compositeBlock y k) - 1| ≤ C / y := by
  -- Paper §6.2 Step 2.  Mertens gives the unit block mass; Chebyshev controls
  -- the harmless endpoint/primorial bookkeeping needed when the blocks are later
  -- passed through CRT transfer.
  classical
  rcases mertens with ⟨m₀, C₀, hC₀pos, hmertens⟩
  refine ⟨2 * C₀, by positivity, Real.exp 1, ?_, ?_⟩
  · simpa using Real.two_mul_le_exp (x := 1)
  · intro y hy
    let M : ℕ := compositeBlockCount y
    have htwo_le_exp_one_global : (2 : ℝ) ≤ Real.exp 1 := by
      simpa using Real.two_mul_le_exp (x := 1)
    have hy_ge2 : (2 : ℝ) ≤ y := htwo_le_exp_one_global.trans hy
    have hy_pos : 0 < y := by linarith
    have hy_nonneg : 0 ≤ y := hy_pos.le
    have hy_ge1 : (1 : ℝ) ≤ y := by linarith
    have hlog_y_ge_one : (1 : ℝ) ≤ Real.log y :=
      (Real.le_log_iff_exp_le hy_pos).2 hy
    have hlog_y_pos : 0 < Real.log y := by linarith
    have hM_one : 1 ≤ M := by
      dsimp [M, compositeBlockCount]
      exact (Nat.one_le_floor_iff (15 * Real.log y)).mpr (by nlinarith)
    have hM_le : (M : ℝ) ≤ 15 * Real.log y := by
      dsimp [M, compositeBlockCount]
      exact Nat.floor_le (by nlinarith : 0 ≤ 15 * Real.log y)
    change 1 ≤ M ∧ (M : ℝ) ≤ 15 * Real.log y ∧
      ∀ k : ℕ, k < M →
        compositeBlock y k ⊆ compositePrimeWindow 20 y ∧
          |reciprocalPrimeMass (compositeBlock y k) - 1| ≤ (2 * C₀) / y
    refine ⟨hM_one, hM_le, ?_⟩
    intro k hk
    have hExp_nat_ge_one (n : ℕ) : (1 : ℝ) ≤ Real.exp (n : ℝ) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (n : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast Nat.zero_le n)
    have hendpoint_lower (n : ℕ) : Real.exp y ≤ compositeBlockEndpoint y n := by
      dsimp [compositeBlockEndpoint]
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left (hExp_nat_ge_one n) hy_nonneg
      simpa using hmul
    have hendpoint_upper :
        compositeBlockEndpoint y (k + 1) ≤ Real.exp (y ^ ((20 : ℝ) - 1)) := by
      dsimp [compositeBlockEndpoint]
      apply Real.exp_le_exp.mpr
      have hk_succ_le_M : k + 1 ≤ M := Nat.succ_le_iff.mpr hk
      have hkR : ((k + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hk_succ_le_M
      have hklog : ((k + 1 : ℕ) : ℝ) ≤ 15 * Real.log y := hkR.trans hM_le
      have hexp_le_pow15 : Real.exp ((k + 1 : ℕ) : ℝ) ≤ y ^ (15 : ℕ) := by
        calc
          Real.exp ((k + 1 : ℕ) : ℝ) ≤ Real.exp (15 * Real.log y) :=
            Real.exp_le_exp.mpr hklog
          _ = y ^ (15 : ℕ) := by
            rw [show (15 : ℝ) * Real.log y = (15 : ℕ) * Real.log y by norm_num,
              Real.exp_nat_mul, Real.exp_log hy_pos]
      have hmul : y * Real.exp ((k + 1 : ℕ) : ℝ) ≤ y * y ^ (15 : ℕ) :=
        mul_le_mul_of_nonneg_left hexp_le_pow15 hy_nonneg
      calc
        y * Real.exp ((k + 1 : ℕ) : ℝ) ≤ y * y ^ (15 : ℕ) := hmul
        _ = y ^ (16 : ℕ) := by ring
        _ ≤ y ^ (19 : ℕ) := pow_le_pow_right₀ hy_ge1 (by norm_num)
        _ = y ^ ((20 : ℝ) - 1) := by norm_num [Real.rpow_natCast]
    constructor
    · intro q hq
      rcases Finset.mem_filter.mp hq with ⟨_hqIic, hqprime, hqgt, hqle⟩
      have hq_lower : Real.exp y < (q : ℝ) := (hendpoint_lower k).trans_lt hqgt
      have hq_upper : (q : ℝ) ≤ Real.exp (y ^ ((20 : ℝ) - 1)) :=
        hqle.trans hendpoint_upper
      have hqIic : q ∈ Finset.Iic ⌊Real.exp (y ^ ((20 : ℝ) - 1))⌋₊ :=
        Finset.mem_Iic.mpr ((Nat.le_floor_iff (Real.exp_nonneg _)).mpr hq_upper)
      exact Finset.mem_filter.mpr ⟨hqIic, hqprime, hq_lower, hq_upper⟩
    · let a : ℝ := compositeBlockEndpoint y k
      let b : ℝ := compositeBlockEndpoint y (k + 1)
      let P : ℝ → ℝ := fun t =>
        ∑ p ∈ Finset.filter Nat.Prime (Finset.Iic ⌊t⌋₊), (1 : ℝ) / (p : ℝ)
      have hblock : reciprocalPrimeMass (compositeBlock y k) = P b - P a := by
        simpa [P, a, b] using reciprocalPrimeMass_compositeBlock_eq_sub y k hy_nonneg
      have hloga : Real.log a = y * Real.exp (k : ℝ) := by
        simp [a, compositeBlockEndpoint]
      have hlogb : Real.log b = y * Real.exp ((k + 1 : ℕ) : ℝ) := by
        simp [b, compositeBlockEndpoint]
      have hlogloga : Real.log (Real.log a) = Real.log y + (k : ℝ) := by
        rw [hloga, Real.log_mul (ne_of_gt hy_pos) (Real.exp_ne_zero _), Real.log_exp]
      have hloglogb :
          Real.log (Real.log b) = Real.log y + ((k + 1 : ℕ) : ℝ) := by
        rw [hlogb, Real.log_mul (ne_of_gt hy_pos) (Real.exp_ne_zero _), Real.log_exp]
      have hloga_ge_y : y ≤ Real.log a := by
        rw [hloga]
        have hmul := mul_le_mul_of_nonneg_left (hExp_nat_ge_one k) hy_nonneg
        simpa using hmul
      have hlogb_ge_y : y ≤ Real.log b := by
        rw [hlogb]
        have hmul := mul_le_mul_of_nonneg_left (hExp_nat_ge_one (k + 1)) hy_nonneg
        simpa using hmul
      have hloga_pos : 0 < Real.log a := hy_pos.trans_le hloga_ge_y
      have hlogb_pos : 0 < Real.log b := hy_pos.trans_le hlogb_ge_y
      have htwo_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
        simpa using Real.two_mul_le_exp (x := 1)
      have ha_ge2 : (2 : ℝ) ≤ a := by
        have harg_ge_one : (1 : ℝ) ≤ y * Real.exp (k : ℝ) := by
          have hmul := mul_le_mul hy_ge1 (hExp_nat_ge_one k) (by norm_num) hy_nonneg
          simpa using hmul
        calc
          (2 : ℝ) ≤ Real.exp 1 := htwo_le_exp_one
          _ ≤ a := by
            dsimp [a, compositeBlockEndpoint]
            exact Real.exp_le_exp.mpr harg_ge_one
      have hb_ge2 : (2 : ℝ) ≤ b := by
        have harg_ge_one : (1 : ℝ) ≤ y * Real.exp ((k + 1 : ℕ) : ℝ) := by
          have hmul :=
            mul_le_mul hy_ge1 (hExp_nat_ge_one (k + 1)) (by norm_num) hy_nonneg
          simpa using hmul
        calc
          (2 : ℝ) ≤ Real.exp 1 := htwo_le_exp_one
          _ ≤ b := by
            dsimp [b, compositeBlockEndpoint]
            exact Real.exp_le_exp.mpr harg_ge_one
      have hMa : |P a - Real.log (Real.log a) - m₀| ≤ C₀ / Real.log a := by
        simpa [P] using hmertens a ha_ge2
      have hMb : |P b - Real.log (Real.log b) - m₀| ≤ C₀ / Real.log b := by
        simpa [P] using hmertens b hb_ge2
      have hCa : C₀ / Real.log a ≤ C₀ / y := by
        have hinv : (1 : ℝ) / Real.log a ≤ 1 / y :=
          one_div_le_one_div_of_le hy_pos hloga_ge_y
        calc
          C₀ / Real.log a = C₀ * (1 / Real.log a) := by ring
          _ ≤ C₀ * (1 / y) := mul_le_mul_of_nonneg_left hinv hC₀pos.le
          _ = C₀ / y := by ring
      have hCb : C₀ / Real.log b ≤ C₀ / y := by
        have hinv : (1 : ℝ) / Real.log b ≤ 1 / y :=
          one_div_le_one_div_of_le hy_pos hlogb_ge_y
        calc
          C₀ / Real.log b = C₀ * (1 / Real.log b) := by ring
          _ ≤ C₀ * (1 / y) := mul_le_mul_of_nonneg_left hinv hC₀pos.le
          _ = C₀ / y := by ring
      have herr_eq : reciprocalPrimeMass (compositeBlock y k) - 1 =
          (P b - Real.log (Real.log b) - m₀) -
            (P a - Real.log (Real.log a) - m₀) := by
        rw [hblock, hlogloga, hloglogb]
        norm_num
        ring
      calc
        |reciprocalPrimeMass (compositeBlock y k) - 1| =
            |(P b - Real.log (Real.log b) - m₀) -
              (P a - Real.log (Real.log a) - m₀)| := by rw [herr_eq]
        _ ≤ |P b - Real.log (Real.log b) - m₀| +
              |-(P a - Real.log (Real.log a) - m₀)| := by
          simpa [sub_eq_add_neg] using
            (abs_add_le (P b - Real.log (Real.log b) - m₀)
              (-(P a - Real.log (Real.log a) - m₀)))
        _ = |P b - Real.log (Real.log b) - m₀| +
              |P a - Real.log (Real.log a) - m₀| := by rw [abs_neg]
        _ ≤ C₀ / Real.log b + C₀ / Real.log a := add_le_add hMb hMa
        _ ≤ C₀ / y + C₀ / y := add_le_add hCb hCa
        _ = (2 * C₀) / y := by ring

private lemma log_prod_one_sub_inv (B : Finset ℕ) (hgt : ∀ q ∈ B, 1 < q) :
    Real.log (∏ q ∈ B, (1 - (1 : ℝ) / (q : ℝ))) =
      ∑ q ∈ B, Real.log (1 - (1 : ℝ) / (q : ℝ)) := by
  classical
  revert hgt
  refine Finset.induction_on B ?base ?step
  · intro _hgt
    simp
  · intro a s has ih hgt
    have hgt_s : ∀ q ∈ s, 1 < q := by
      intro q hq
      exact hgt q (Finset.mem_insert_of_mem hq)
    have hpos : ∀ q ∈ insert a s, 0 < 1 - (1 : ℝ) / (q : ℝ) := by
      intro q hq
      have hqgt1 : (1 : ℝ) < q := by exact_mod_cast hgt q hq
      have hqpos : (0 : ℝ) < q := by linarith
      have hone_div_lt_one : (1 : ℝ) / (q : ℝ) < 1 := by
        rw [div_lt_iff₀ hqpos]
        linarith
      linarith
    have ha : 1 - (1 : ℝ) / (a : ℝ) ≠ 0 :=
      ne_of_gt (hpos a (Finset.mem_insert_self a s))
    have hspos : 0 < ∏ q ∈ s, (1 - (1 : ℝ) / (q : ℝ)) := by
      apply Finset.prod_pos
      intro q hq
      exact hpos q (Finset.mem_insert_of_mem hq)
    have hsne : (∏ q ∈ s, (1 - (1 : ℝ) / (q : ℝ))) ≠ 0 := ne_of_gt hspos
    rw [Finset.prod_insert has, Finset.sum_insert has, Real.log_mul ha hsne, ih hgt_s]

private lemma abs_log_one_sub_inv_add_inv_le {q : ℕ} (hq : 1 < q) :
    |Real.log (1 - (1 : ℝ) / (q : ℝ)) + (1 : ℝ) / (q : ℝ)| ≤
      2 * ((1 : ℝ) / (q : ℝ)) ^ 2 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one hq)
  have hqge2R : (2 : ℝ) ≤ q := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have hp_nonneg : 0 ≤ (1 : ℝ) / (q : ℝ) := div_nonneg zero_le_one hqpos.le
  have hp_le_half : (1 : ℝ) / (q : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hqge2R
  have hp_lt_one : |(1 : ℝ) / (q : ℝ)| < 1 := by
    rw [abs_of_nonneg hp_nonneg]
    linarith
  have hmain := Real.abs_log_sub_add_sum_range_le
    (x := (1 : ℝ) / (q : ℝ)) hp_lt_one 1
  have hsum : (∑ i ∈ Finset.range 1,
        ((1 : ℝ) / (q : ℝ)) ^ (i + 1) / ((i : ℝ) + 1)) =
      (1 : ℝ) / (q : ℝ) := by norm_num
  rw [hsum] at hmain
  have hden : 1 - |(1 : ℝ) / (q : ℝ)| = 1 - (1 : ℝ) / (q : ℝ) := by
    rw [abs_of_nonneg hp_nonneg]
  rw [hden] at hmain
  have hden_ge : 1 / 2 ≤ 1 - (1 : ℝ) / (q : ℝ) := by linarith
  have hdiv_le : |(1 : ℝ) / (q : ℝ)| ^ (1 + 1) /
        (1 - (1 : ℝ) / (q : ℝ)) ≤
      2 * ((1 : ℝ) / (q : ℝ)) ^ 2 := by
    rw [abs_of_nonneg hp_nonneg]
    have hsq_nonneg : 0 ≤ ((1 : ℝ) / (q : ℝ)) ^ 2 := sq_nonneg _
    have h_inv : (1 : ℝ) / (1 - (1 : ℝ) / (q : ℝ)) ≤ 2 := by
      have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hden_ge
      norm_num at this ⊢
      exact this
    calc
      ((1 : ℝ) / (q : ℝ)) ^ (1 + 1) / (1 - (1 : ℝ) / (q : ℝ)) =
          ((1 : ℝ) / (q : ℝ)) ^ 2 * (1 / (1 - (1 : ℝ) / (q : ℝ))) := by
        ring
      _ ≤ ((1 : ℝ) / (q : ℝ)) ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left h_inv hsq_nonneg
      _ = 2 * ((1 : ℝ) / (q : ℝ)) ^ 2 := by ring
  simpa [add_comm] using hmain.trans hdiv_le

private lemma blockGoodProbability_eq_prod_sum_inv_sub_one
    (B : Finset ℕ) (hgt : ∀ q ∈ B, 1 < q) :
    blockGoodProbability B =
      (∏ r ∈ B, (1 - (1 : ℝ) / (r : ℝ))) *
        ∑ q ∈ B, (1 : ℝ) / (((q - 1 : ℕ) : ℝ)) := by
  classical
  dsimp [blockGoodProbability]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro q hq
  rw [Finset.prod_eq_mul_prod_sdiff_singleton q _ (fun hn => (hn hq).elim)]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one (hgt q hq))
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hqgt1 : (1 : ℝ) < q := by exact_mod_cast hgt q hq
  have hqm1ne : (q : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hqgt1)
  have hqsub : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.le_of_lt (hgt q hq))]
    norm_num
  rw [Finset.sdiff_singleton_eq_erase]
  rw [hqsub]
  field_simp [hqne, hqm1ne]

private lemma sum_inv_sq_le_exp_neg_mul_reciprocalPrimeMass
    (y : ℝ) (B : Finset ℕ) (hlower : ∀ q ∈ B, Real.exp y < (q : ℝ)) :
    (∑ q ∈ B, ((1 : ℝ) / (q : ℝ)) ^ 2) ≤
      Real.exp (-y) * reciprocalPrimeMass B := by
  rw [reciprocalPrimeMass, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have hqpos : 0 < (q : ℝ) := (Real.exp_pos y).trans (hlower q hq)
  have hle : (1 : ℝ) / (q : ℝ) ≤ Real.exp (-y) := by
    have hle' : (1 : ℝ) / (q : ℝ) ≤ 1 / Real.exp y :=
      one_div_le_one_div_of_le (Real.exp_pos y) (le_of_lt (hlower q hq))
    simpa [Real.exp_neg] using hle'
  have hnon : 0 ≤ (1 : ℝ) / (q : ℝ) := div_nonneg zero_le_one hqpos.le
  calc
    ((1 : ℝ) / (q : ℝ)) ^ 2 = ((1 : ℝ) / (q : ℝ)) * ((1 : ℝ) / (q : ℝ)) := by
      ring
    _ ≤ Real.exp (-y) * ((1 : ℝ) / (q : ℝ)) :=
      mul_le_mul_of_nonneg_right hle hnon

private lemma blockGoodProbability_close_to_mass_exp
    (B : Finset ℕ) (hgt : ∀ q ∈ B, 1 < q)
    (hmu_le_two : reciprocalPrimeMass B ≤ 2)
    (hnu_le_quarter : (∑ q ∈ B, ((1 : ℝ) / (q : ℝ)) ^ 2) ≤ 1 / 4) :
    |blockGoodProbability B -
        reciprocalPrimeMass B * Real.exp (-(reciprocalPrimeMass B))| ≤
      10 * (∑ q ∈ B, ((1 : ℝ) / (q : ℝ)) ^ 2) := by
  classical
  let μ : ℝ := reciprocalPrimeMass B
  let ν : ℝ := ∑ q ∈ B, ((1 : ℝ) / (q : ℝ)) ^ 2
  let Pprod : ℝ := ∏ q ∈ B, (1 - (1 : ℝ) / (q : ℝ))
  let sigma : ℝ := ∑ q ∈ B, (1 : ℝ) / (((q - 1 : ℕ) : ℝ))
  have hmu_nonneg : 0 ≤ μ := by
    dsimp [μ, reciprocalPrimeMass]
    apply Finset.sum_nonneg
    intro q hq
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one (hgt q hq))
    exact div_nonneg zero_le_one hqpos.le
  have hnu_nonneg : 0 ≤ ν := by
    dsimp [ν]
    apply Finset.sum_nonneg
    intro q _hq
    exact sq_nonneg _
  have hnu_le_quarter' : ν ≤ 1 / 4 := by simpa [ν] using hnu_le_quarter
  have hmu_le_two' : μ ≤ 2 := by simpa [μ] using hmu_le_two
  have hfac_pos : ∀ q ∈ B, 0 < 1 - (1 : ℝ) / (q : ℝ) := by
    intro q hq
    have hqgt1 : (1 : ℝ) < q := by exact_mod_cast hgt q hq
    have hqpos : (0 : ℝ) < q := by linarith
    have hone_div_lt_one : (1 : ℝ) / (q : ℝ) < 1 := by
      rw [div_lt_iff₀ hqpos]
      linarith
    linarith
  have hPprod_nonneg : 0 ≤ Pprod := by
    dsimp [Pprod]
    exact le_of_lt (Finset.prod_pos hfac_pos)
  have hPprod_le_one : Pprod ≤ 1 := by
    dsimp [Pprod]
    calc
      (∏ q ∈ B, (1 - (1 : ℝ) / (q : ℝ))) ≤ ∏ q ∈ B, (1 : ℝ) := by
        apply Finset.prod_le_prod
        · intro q hq
          exact le_of_lt (hfac_pos q hq)
        · intro q hq
          have hqpos : (0 : ℝ) < q := by
            exact_mod_cast (Nat.lt_trans Nat.zero_lt_one (hgt q hq))
          have hnon : 0 ≤ (1 : ℝ) / (q : ℝ) := div_nonneg zero_le_one hqpos.le
          linarith
      _ = 1 := by simp
  have hsigma_ge_mu : μ ≤ sigma := by
    dsimp [μ, sigma, reciprocalPrimeMass]
    apply Finset.sum_le_sum
    intro q hq
    have hqsubpos : (0 : ℝ) < (((q - 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.sub_pos_of_lt (hgt q hq)
    have hle : (((q - 1 : ℕ) : ℝ)) ≤ (q : ℝ) := by exact_mod_cast Nat.sub_le q 1
    exact one_div_le_one_div_of_le hqsubpos hle
  have hsigma_le : sigma ≤ μ + 2 * ν := by
    dsimp [μ, sigma, ν, reciprocalPrimeMass]
    calc
      (∑ q ∈ B, (1 : ℝ) / (((q - 1 : ℕ) : ℝ))) ≤
          ∑ q ∈ B, ((1 : ℝ) / (q : ℝ) + 2 * ((1 : ℝ) / (q : ℝ)) ^ 2) := by
        apply Finset.sum_le_sum
        intro q hq
        have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.lt_trans Nat.zero_lt_one (hgt q hq))
        have hqgt1 : (1 : ℝ) < q := by exact_mod_cast hgt q hq
        have hqge2 : (2 : ℝ) ≤ q := by exact_mod_cast Nat.succ_le_of_lt (hgt q hq)
        have hqsubpos : 0 < (q : ℝ) - 1 := by linarith
        have hqsub : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
          rw [Nat.cast_sub (Nat.le_of_lt (hgt q hq))]
          norm_num
        rw [hqsub]
        rw [div_le_iff₀ hqsubpos]
        field_simp [ne_of_gt hqpos]
        ring_nf
        nlinarith [hqge2]
      _ = (∑ q ∈ B, (1 : ℝ) / (q : ℝ)) +
            2 * ∑ q ∈ B, ((1 : ℝ) / (q : ℝ)) ^ 2 := by
        rw [Finset.sum_add_distrib]
        rw [Finset.mul_sum]
  have hsigma_sub_abs : |sigma - μ| ≤ 2 * ν := by
    have hnon : 0 ≤ sigma - μ := sub_nonneg.mpr hsigma_ge_mu
    rw [abs_of_nonneg hnon]
    linarith
  let eps : ℝ := ∑ q ∈ B, (Real.log (1 - (1 : ℝ) / (q : ℝ)) + (1 : ℝ) / (q : ℝ))
  have heps_abs : |eps| ≤ 2 * ν := by
    dsimp [eps, ν]
    calc
      |∑ q ∈ B, (Real.log (1 - (1 : ℝ) / (q : ℝ)) + (1 : ℝ) / (q : ℝ))| ≤
          ∑ q ∈ B, |Real.log (1 - (1 : ℝ) / (q : ℝ)) + (1 : ℝ) / (q : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ B, 2 * ((1 : ℝ) / (q : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        exact abs_log_one_sub_inv_add_inv_le (hgt q hq)
      _ = 2 * ∑ q ∈ B, ((1 : ℝ) / (q : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
  have hlogPprod : Real.log Pprod = -μ + eps := by
    dsimp [Pprod, μ, eps, reciprocalPrimeMass]
    rw [log_prod_one_sub_inv B hgt]
    rw [Finset.sum_add_distrib]
    ring
  have hPprod_eq : Pprod = Real.exp (-μ) * Real.exp eps := by
    have hPprod_pos : 0 < Pprod := by
      dsimp [Pprod]
      exact Finset.prod_pos hfac_pos
    calc
      Pprod = Real.exp (Real.log Pprod) := by rw [Real.exp_log hPprod_pos]
      _ = Real.exp (-μ + eps) := by rw [hlogPprod]
      _ = Real.exp (-μ) * Real.exp eps := by rw [Real.exp_add]
  have hPprod_close : |Pprod - Real.exp (-μ)| ≤ 4 * ν := by
    rw [hPprod_eq]
    have hexp_mu_nonneg : 0 ≤ Real.exp (-μ) := le_of_lt (Real.exp_pos _)
    have hexp_mu_le_one : Real.exp (-μ) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have heps_le_one : |eps| ≤ 1 := by linarith
    have hexp_eps : |Real.exp eps - 1| ≤ 2 * |eps| :=
      Real.abs_exp_sub_one_le heps_le_one
    calc
      |Real.exp (-μ) * Real.exp eps - Real.exp (-μ)| =
          |Real.exp (-μ) * (Real.exp eps - 1)| := by ring_nf
      _ = Real.exp (-μ) * |Real.exp eps - 1| := by
        rw [abs_mul, abs_of_nonneg hexp_mu_nonneg]
      _ ≤ 1 * (2 * |eps|) :=
        mul_le_mul hexp_mu_le_one hexp_eps (abs_nonneg _) zero_le_one
      _ ≤ 1 * (2 * (2 * ν)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left heps_abs (by norm_num)) (by norm_num)
      _ = 4 * ν := by ring
  have hprob_eq : blockGoodProbability B = Pprod * sigma := by
    simpa [Pprod, sigma] using blockGoodProbability_eq_prod_sum_inv_sub_one B hgt
  have hmain : |Pprod * sigma - Real.exp (-μ) * μ| ≤ 10 * ν := by
    have hdecomp : Pprod * sigma - Real.exp (-μ) * μ =
        Pprod * (sigma - μ) + μ * (Pprod - Real.exp (-μ)) := by ring
    rw [hdecomp]
    calc
      |Pprod * (sigma - μ) + μ * (Pprod - Real.exp (-μ))| ≤
          |Pprod * (sigma - μ)| + |μ * (Pprod - Real.exp (-μ))| := abs_add_le _ _
      _ = |Pprod| * |sigma - μ| + |μ| * |Pprod - Real.exp (-μ)| := by
        rw [abs_mul, abs_mul]
      _ ≤ 1 * (2 * ν) + 2 * (4 * ν) := by
        have hPprod_abs_le : |Pprod| ≤ 1 := by rwa [abs_of_nonneg hPprod_nonneg]
        have hmu_abs_le : |μ| ≤ 2 := by rwa [abs_of_nonneg hmu_nonneg]
        exact add_le_add
          (mul_le_mul hPprod_abs_le hsigma_sub_abs (abs_nonneg _) (by norm_num))
          (mul_le_mul hmu_abs_le hPprod_close (abs_nonneg _) (by norm_num))
      _ = 10 * ν := by ring
  simpa [hprob_eq, μ, ν, mul_comm, mul_left_comm, mul_assoc] using hmain

private lemma mass_exp_close_exp_neg_one {μ : ℝ}
    (hmu_nonneg : 0 ≤ μ) (hclose : |μ - 1| ≤ 1) :
    |μ * Real.exp (-μ) - Real.exp (-1)| ≤ 5 * |μ - 1| := by
  let t : ℝ := μ - 1
  have hμ : μ = 1 + t := by dsimp [t]; ring
  have ht_abs : |t| ≤ 1 := by simpa [t] using hclose
  have hrewrite : μ * Real.exp (-μ) - Real.exp (-1) =
      Real.exp (-1) * ((1 + t) * Real.exp (-t) - 1) := by
    rw [hμ]
    rw [show -(1 + t) = -1 + -t by ring]
    rw [Real.exp_add]
    ring
  rw [hrewrite]
  have hexp_nonneg : 0 ≤ Real.exp (-1) := le_of_lt (Real.exp_pos _)
  have hexp_le_one : Real.exp (-1) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    norm_num
  calc
    |Real.exp (-1) * ((1 + t) * Real.exp (-t) - 1)| =
        Real.exp (-1) * |(1 + t) * Real.exp (-t) - 1| := by
      rw [abs_mul, abs_of_nonneg hexp_nonneg]
    _ ≤ 1 * |(1 + t) * Real.exp (-t) - 1| :=
      mul_le_mul hexp_le_one le_rfl (abs_nonneg _) zero_le_one
    _ ≤ 1 * (5 * |t|) := by
      apply mul_le_mul_of_nonneg_left _ zero_le_one
      have hsplit : (1 + t) * Real.exp (-t) - 1 =
          (1 + t) * (Real.exp (-t) - 1) + t := by ring
      rw [hsplit]
      calc
        |(1 + t) * (Real.exp (-t) - 1) + t| ≤
            |(1 + t) * (Real.exp (-t) - 1)| + |t| := abs_add_le _ _
        _ = |1 + t| * |Real.exp (-t) - 1| + |t| := by rw [abs_mul]
        _ ≤ 2 * (2 * |t|) + |t| := by
          have ht_lower : -1 ≤ t := by
            have := abs_le.mp ht_abs
            linarith
          have ht_upper : t ≤ 1 := by
            have := abs_le.mp ht_abs
            linarith
          have hone_abs : |1 + t| ≤ 2 := by
            rw [abs_le]
            constructor <;> linarith
          have hexp : |Real.exp (-t) - 1| ≤ 2 * |-t| := by
            apply Real.abs_exp_sub_one_le
            simpa using ht_abs
          rw [abs_neg] at hexp
          exact add_le_add (mul_le_mul hone_abs hexp (abs_nonneg _) (by norm_num)) le_rfl
        _ = 5 * |t| := by ring
    _ = 5 * |μ - 1| := by simp [t]

/-- Step 3: good-block probability.

For every block from Step 2, the probability of selecting exactly one prime is
`e^{-1} + O(1/y)`, uniformly in the block. -/
private lemma step3_good_block_probability :
    ∃ C : ℝ, 0 < C ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          let M := compositeBlockCount y
          ∀ k : ℕ, k < M →
            |blockGoodProbability (compositeBlock y k) - Real.exp (-1)| ≤ C / y := by
  -- Paper §6.2 Step 3, using the block mass from Steps 1--2 and
  -- `∑_{q > exp y} q^{-2} = O(exp(-y))`.
  classical
  rcases step2_block_decomposition with ⟨C₂, hC₂pos, y₂, hy₂_ge2, hstep2⟩
  refine ⟨5 * C₂ + 20, by positivity, max y₂ (max (2 * C₂) 8), ?_, ?_⟩
  · exact hy₂_ge2.trans (le_max_left _ _)
  · intro y hy
    have hy_y₂ : y₂ ≤ y := (le_max_left y₂ (max (2 * C₂) 8)).trans hy
    have hy_C₂ : 2 * C₂ ≤ y := by
      exact ((le_max_left (2 * C₂) (8 : ℝ)).trans
        (le_max_right y₂ (max (2 * C₂) 8))).trans hy
    have hy_8 : (8 : ℝ) ≤ y := by
      exact ((le_max_right (2 * C₂) (8 : ℝ)).trans
        (le_max_right y₂ (max (2 * C₂) 8))).trans hy
    have hy_pos : 0 < y := by linarith
    have hC₂_div_le_half : C₂ / y ≤ 1 / 2 := by
      rw [div_le_iff₀ hy_pos]
      nlinarith
    have hexp_neg_le_inv : Real.exp (-y) ≤ 1 / y := by
      have hy_le_exp : y ≤ Real.exp y := by
        have := Real.add_one_le_exp y
        linarith
      have hle : (1 : ℝ) / Real.exp y ≤ 1 / y :=
        one_div_le_one_div_of_le hy_pos hy_le_exp
      simpa [Real.exp_neg] using hle
    have hstep2_y := hstep2 y hy_y₂
    change ∀ k : ℕ, k < compositeBlockCount y →
      |blockGoodProbability (compositeBlock y k) - Real.exp (-1)| ≤ (5 * C₂ + 20) / y
    intro k hk
    let B : Finset ℕ := compositeBlock y k
    let μ : ℝ := reciprocalPrimeMass B
    let ν : ℝ := ∑ q ∈ B, ((1 : ℝ) / (q : ℝ)) ^ 2
    have hblock_info := hstep2_y.2.2 k hk
    have hmass_abs : |μ - 1| ≤ C₂ / y := by
      simpa [μ, B] using hblock_info.2
    have hmu_nonneg : 0 ≤ μ := by
      dsimp [μ, B, reciprocalPrimeMass]
      apply Finset.sum_nonneg
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨_hqIic, hqprime, _hqgt, _hqle⟩
      have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hqprime.ne_zero
      exact div_nonneg zero_le_one hqpos.le
    have hmu_le_two : μ ≤ 2 := by
      have hupper := (abs_le.mp hmass_abs).2
      linarith
    have hgt : ∀ q ∈ B, 1 < q := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨_hqIic, hqprime, _hqgt, _hqle⟩
      exact hqprime.one_lt
    have hendpoint_lower : Real.exp y ≤ compositeBlockEndpoint y k := by
      dsimp [compositeBlockEndpoint]
      apply Real.exp_le_exp.mpr
      have hExp_nat_ge_one : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
        calc
          (1 : ℝ) = Real.exp 0 := by simp
          _ ≤ Real.exp (k : ℝ) :=
            Real.exp_le_exp.mpr (by exact_mod_cast Nat.zero_le k)
      have hmul := mul_le_mul_of_nonneg_left hExp_nat_ge_one hy_pos.le
      simpa using hmul
    have hblock_lower : ∀ q ∈ B, Real.exp y < (q : ℝ) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨_hqIic, _hqprime, hqgt, _hqle⟩
      exact hendpoint_lower.trans_lt hqgt
    have hν_exp : ν ≤ Real.exp (-y) * μ := by
      simpa [ν, μ, B] using sum_inv_sq_le_exp_neg_mul_reciprocalPrimeMass y B hblock_lower
    have hν_le_two_div_y : ν ≤ 2 / y := by
      calc
        ν ≤ Real.exp (-y) * μ := hν_exp
        _ ≤ Real.exp (-y) * 2 := mul_le_mul_of_nonneg_left hmu_le_two (by positivity)
        _ ≤ (1 / y) * 2 := mul_le_mul_of_nonneg_right hexp_neg_le_inv (by norm_num)
        _ = 2 / y := by ring
    have hν_le_quarter : ν ≤ 1 / 4 := by
      have htwo_div : 2 / y ≤ 1 / 4 := by
        rw [div_le_iff₀ hy_pos]
        nlinarith
      exact hν_le_two_div_y.trans htwo_div
    have hprob_close :
        |blockGoodProbability B - μ * Real.exp (-μ)| ≤ 10 * ν := by
      simpa [μ, ν] using
        blockGoodProbability_close_to_mass_exp B hgt (by simpa [μ] using hmu_le_two)
          (by simpa [ν] using hν_le_quarter)
    have hmass_exp_close : |μ * Real.exp (-μ) - Real.exp (-1)| ≤ 5 * |μ - 1| := by
      apply mass_exp_close_exp_neg_one hmu_nonneg
      exact hmass_abs.trans (by linarith)
    have hcombine :
        |blockGoodProbability B - Real.exp (-1)| ≤ 10 * ν + 5 * |μ - 1| := by
      have hdecomp : blockGoodProbability B - Real.exp (-1) =
          (blockGoodProbability B - μ * Real.exp (-μ)) +
            (μ * Real.exp (-μ) - Real.exp (-1)) := by ring
      rw [hdecomp]
      exact (abs_add_le _ _).trans (add_le_add hprob_close hmass_exp_close)
    calc
      |blockGoodProbability (compositeBlock y k) - Real.exp (-1)| =
          |blockGoodProbability B - Real.exp (-1)| := by rfl
      _ ≤ 10 * ν + 5 * |μ - 1| := hcombine
      _ ≤ 10 * (2 / y) + 5 * (C₂ / y) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hν_le_two_div_y (by norm_num))
          (mul_le_mul_of_nonneg_left hmass_abs (by norm_num))
      _ = (5 * C₂ + 20) / y := by ring

private lemma compositeBlockEndpoint_mono {y : ℝ} (hy : 0 ≤ y) {i j : ℕ}
    (hij : i ≤ j) :
    compositeBlockEndpoint y i ≤ compositeBlockEndpoint y j := by
  dsimp [compositeBlockEndpoint]
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by exact_mod_cast hij)) hy

private lemma compositeBlock_disjoint {y : ℝ} (hy : 0 ≤ y) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (compositeBlock y i) (compositeBlock y j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hqi hqj
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · have hsucc : i + 1 ≤ j := Nat.succ_le_iff.mpr hij_lt
    have hend : compositeBlockEndpoint y (i + 1) ≤ compositeBlockEndpoint y j :=
      compositeBlockEndpoint_mono hy hsucc
    rcases Finset.mem_filter.mp hqi with ⟨_hIic_i, _hprime_i, _hgt_i, hle_i⟩
    rcases Finset.mem_filter.mp hqj with ⟨_hIic_j, _hprime_j, hgt_j, _hle_j⟩
    linarith
  · have hsucc : j + 1 ≤ i := Nat.succ_le_iff.mpr hji_lt
    have hend : compositeBlockEndpoint y (j + 1) ≤ compositeBlockEndpoint y i :=
      compositeBlockEndpoint_mono hy hsucc
    rcases Finset.mem_filter.mp hqi with ⟨_hIic_i, _hprime_i, hgt_i, _hle_i⟩
    rcases Finset.mem_filter.mp hqj with ⟨_hIic_j, _hprime_j, _hgt_j, hle_j⟩
    linarith

/-- Step 4 independence bridge: block-good indicators are mutually independent in the
finite prime model because distinct blocks depend on disjoint prime sets.  The form with
two disjoint index sets records the joint law of prescribed good and bad block outcomes. -/
private lemma step4_independence_lemma :
    ∃ y₀ : ℝ, 2 ≤ y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        let M := compositeBlockCount y
        ∀ A B : Finset ℕ,
          A ⊆ Finset.range M →
          B ⊆ Finset.range M →
          Disjoint A B →
            finitePrimeModelProb (compositePrimeWindow 20 y)
                (fun S =>
                  (∀ k ∈ A, (compositeBlock y k ∩ S).card = 1) ∧
                    ∀ k ∈ B, (compositeBlock y k ∩ S).card ≠ 1) =
              (∏ k ∈ A, blockGoodProbability (compositeBlock y k)) *
                ∏ k ∈ B, (1 - blockGoodProbability (compositeBlock y k)) := by
  -- Paper §6.2 lines 1657-1658: different block indicators depend on disjoint
  -- prime subsets, so the finite product weights factor block-by-block.
  classical
  rcases step2_block_decomposition with ⟨C₂, _hC₂pos, y₂, hy₂_ge2, hstep2⟩
  refine ⟨y₂, hy₂_ge2, ?_⟩
  intro y hy
  dsimp
  let M := compositeBlockCount y
  have hstep2_y := hstep2 y hy
  have hy_nonneg : 0 ≤ y := by
    exact (by norm_num : (0 : ℝ) ≤ 2).trans (hy₂_ge2.trans hy)
  intro A B hA hB hAB
  let U := compositePrimeWindow 20 y
  let F : ℕ → Finset ℕ := fun k => compositeBlock y k
  have hsub : ∀ k ∈ A ∪ B, F k ⊆ U := by
    intro k hk
    have hkM : k < M := by
      rcases Finset.mem_union.mp hk with hkA | hkB
      · exact Finset.mem_range.mp (hA hkA)
      · exact Finset.mem_range.mp (hB hkB)
    exact (hstep2_y.2.2 k hkM).1
  have hpair : ∀ i ∈ A ∪ B, ∀ j ∈ A ∪ B, i ≠ j → Disjoint (F i) (F j) := by
    intro i _hi j _hj hij
    exact compositeBlock_disjoint hy_nonneg hij
  convert! finitePrimeModelProb_blockEvents U F A B hsub hpair hAB using 1

/-- Step 4 expectation bridge: Step 3 gives an expected number of good blocks of order
`e^{-1} M`, which dominates the paper threshold `K = ceil(e^{-1}15 log y / 2)`. -/
private lemma step4_expectation_lower_bound
    (_hstep3 :
      ∃ C : ℝ, 0 < C ∧
        ∃ y₀ : ℝ, 2 ≤ y₀ ∧
          ∀ y : ℝ, y₀ ≤ y →
            let M := compositeBlockCount y
            ∀ k : ℕ, k < M →
              |blockGoodProbability (compositeBlock y k) - Real.exp (-1)| ≤ C / y) :
    ∃ y₀ : ℝ, 2 ≤ y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        let M := compositeBlockCount y
        let EW := ∑ k ∈ Finset.range M, blockGoodProbability (compositeBlock y k)
        (compositeGoodBlockThreshold y : ℝ) ≤ (2 / 3 : ℝ) * EW ∧
          ((Real.exp (-1) * 15) / 2) * Real.log y ≤ EW := by
  -- Paper §6.2 lines 1668-1675: sum the Step 3 block probabilities and absorb
  -- the floor/ceiling and `O(1/y)` losses for sufficiently large `y`.
  classical
  rcases _hstep3 with ⟨C, hCpos, y3, hy3_ge2, hstep3⟩
  let ρ : ℝ := Real.exp (-1)
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρle_one : ρ ≤ 1 := by
    dsimp [ρ]
    rw [Real.exp_le_one_iff]
    norm_num
  refine ⟨max y3 (max ((10 * C) / ρ) (Real.exp (4 / ρ))), ?_, ?_⟩
  · exact hy3_ge2.trans (le_max_left _ _)
  · intro y hy
    let M : ℕ := compositeBlockCount y
    let EW : ℝ := ∑ k ∈ Finset.range M, blockGoodProbability (compositeBlock y k)
    let L : ℝ := Real.log y
    let T : ℝ := ((ρ * 15) / 2) * L
    have hy_step : y3 ≤ y :=
      (le_max_left y3 (max ((10 * C) / ρ) (Real.exp (4 / ρ)))).trans hy
    have hy_err : (10 * C) / ρ ≤ y := by
      exact ((le_max_left ((10 * C) / ρ) (Real.exp (4 / ρ))).trans
        (le_max_right y3 (max ((10 * C) / ρ) (Real.exp (4 / ρ))))).trans hy
    have hy_exp : Real.exp (4 / ρ) ≤ y := by
      exact ((le_max_right ((10 * C) / ρ) (Real.exp (4 / ρ))).trans
        (le_max_right y3 (max ((10 * C) / ρ) (Real.exp (4 / ρ))))).trans hy
    have hy_ge2 : (2 : ℝ) ≤ y := hy3_ge2.trans hy_step
    have hy_pos : 0 < y := by linarith
    have hlog_ge : 4 / ρ ≤ L := by
      dsimp [L]
      exact (Real.le_log_iff_exp_le hy_pos).2 hy_exp
    have hρL_ge_four : 4 ≤ ρ * L := by
      have hmul := mul_le_mul_of_nonneg_left hlog_ge hρpos.le
      have hs : ρ * (4 / ρ) = 4 := by field_simp [ne_of_gt hρpos]
      rw [hs] at hmul
      simpa [L] using hmul
    have hL_nonneg : 0 ≤ L := by
      have hfour_div_pos : 0 < 4 / ρ := div_pos (by norm_num) hρpos
      exact (hfour_div_pos.trans_le hlog_ge).le
    have hCdiv : C / y ≤ ρ / 10 := by
      rw [div_le_iff₀ hy_pos]
      have hmul := mul_le_mul_of_nonneg_left hy_err hρpos.le
      have hs : ρ * ((10 * C) / ρ) = 10 * C := by field_simp [ne_of_gt hρpos]
      rw [hs] at hmul
      nlinarith
    have hstep3_y := hstep3 y hy_step
    change
      (compositeGoodBlockThreshold y : ℝ) ≤ (2 / 3 : ℝ) * EW ∧ T ≤ EW
    have hp_lower : ∀ k ∈ Finset.range M,
        (9 / 10 : ℝ) * ρ ≤ blockGoodProbability (compositeBlock y k) := by
      intro k hk
      have hkM : k < compositeBlockCount y := by
        simpa [M] using Finset.mem_range.mp hk
      have hclose := hstep3_y k hkM
      have hlower : -(C / y) ≤ blockGoodProbability (compositeBlock y k) - ρ := by
        simpa [ρ] using (abs_le.mp hclose).1
      nlinarith [hCdiv]
    have hsum_lower : (M : ℝ) * ((9 / 10 : ℝ) * ρ) ≤ EW := by
      calc
        (M : ℝ) * ((9 / 10 : ℝ) * ρ) =
            ∑ k ∈ Finset.range M, ((9 / 10 : ℝ) * ρ) := by simp
        _ ≤ ∑ k ∈ Finset.range M, blockGoodProbability (compositeBlock y k) := by
          exact Finset.sum_le_sum (fun k hk => hp_lower k hk)
        _ = EW := by rfl
    have hfloor_lt : (15 : ℝ) * L < (M : ℝ) + 1 := by
      dsimp [M, compositeBlockCount, L]
      simpa using (Nat.lt_floor_add_one ((15 : ℝ) * Real.log y))
    have hM_lower : (15 : ℝ) * L - 1 ≤ (M : ℝ) := by linarith
    have hcoef_nonneg : 0 ≤ (9 / 10 : ℝ) * ρ := by positivity
    have hEW_lower : ((9 / 10 : ℝ) * ρ) * ((15 : ℝ) * L - 1) ≤ EW := by
      calc
        ((9 / 10 : ℝ) * ρ) * ((15 : ℝ) * L - 1) ≤
            ((9 / 10 : ℝ) * ρ) * (M : ℝ) :=
          mul_le_mul_of_nonneg_left hM_lower hcoef_nonneg
        _ = (M : ℝ) * ((9 / 10 : ℝ) * ρ) := by ring
        _ ≤ EW := hsum_lower
    have hT_nonneg : 0 ≤ T := by
      dsimp [T]
      apply mul_nonneg
      · apply div_nonneg
        · exact mul_nonneg hρpos.le (by norm_num)
        · norm_num
      · exact hL_nonneg
    have hceil_lt : (compositeGoodBlockThreshold y : ℝ) < T + 1 := by
      have hceilT : (⌈T⌉₊ : ℝ) < T + 1 := Nat.ceil_lt_add_one hT_nonneg
      simpa [compositeGoodBlockThreshold, T, L, ρ] using hceilT
    have hfirst_aux :
        T + 1 ≤ (2 / 3 : ℝ) * (((9 / 10 : ℝ) * ρ) * ((15 : ℝ) * L - 1)) := by
      dsimp [T]
      nlinarith [hρL_ge_four, hρle_one]
    have hsecond_aux : T ≤ ((9 / 10 : ℝ) * ρ) * ((15 : ℝ) * L - 1) := by
      dsimp [T]
      nlinarith [hρL_ge_four, hρle_one]
    have htwo_thirds_EW :
        (2 / 3 : ℝ) * (((9 / 10 : ℝ) * ρ) * ((15 : ℝ) * L - 1)) ≤
          (2 / 3 : ℝ) * EW :=
      mul_le_mul_of_nonneg_left hEW_lower (by norm_num)
    exact ⟨(le_of_lt hceil_lt).trans (hfirst_aux.trans htwo_thirds_EW),
      hsecond_aux.trans hEW_lower⟩

private lemma selectionWeight_nonneg {U S : Finset ℕ} (hU : ∀ q ∈ U, 1 ≤ q) :
    0 ≤ selectionWeight U S := by
  classical
  dsimp [selectionWeight]
  apply Finset.prod_nonneg
  intro q hq
  by_cases hqS : q ∈ S
  · simp [hqS]
  · simp only [hqS, if_false]
    rw [sub_nonneg]
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (Nat.zero_lt_one.trans_le (hU q hq))
    exact (div_le_one hq_pos).mpr (by exact_mod_cast hU q hq)

private lemma finitePrimeModelProb_nonneg {U : Finset ℕ} (hU : ∀ q ∈ U, 1 ≤ q)
    (Q : Finset ℕ → Prop) :
    0 ≤ finitePrimeModelProb U Q := by
  classical
  dsimp [finitePrimeModelProb]
  exact Finset.sum_nonneg (fun _S _hS => selectionWeight_nonneg hU)

private lemma compositePrimeWindow_one_le {A y : ℝ} {q : ℕ}
    (hq : q ∈ compositePrimeWindow A y) :
    1 ≤ q := by
  rcases Finset.mem_filter.mp hq with ⟨_hqIic, hqprime, _hqgt, _hqle⟩
  exact hqprime.one_lt.le

/-- `conditionalResidueMeasure` is nonneg.  Both numerator and denominator are
finite-prime-model probabilities, hence nonneg. -/
private lemma conditionalResidueMeasure_nonneg {y : ℝ} {d K : ℕ}
    (g : Fin K → (ZMod d)ˣ) : 0 ≤ conditionalResidueMeasure y d K g := by
  unfold conditionalResidueMeasure
  apply div_nonneg
  · exact finitePrimeModelProb_nonneg (fun _q hq => compositePrimeWindow_one_le hq) _
  · exact finitePrimeModelProb_nonneg (fun _q hq => compositePrimeWindow_one_le hq) _

/-- Helper: partition `finitePrimeModelProb U P` by the value of an extraction map
`extract : Finset ℕ → α` (with `α` finite).  Paper §6.2 line 1732-1735 framework: for
each `S` with `P S`, the extraction takes exactly one value `g`, so summing over `g`
recovers the original probability. -/
private lemma finitePrimeModelProb_sum_partition {U : Finset ℕ} {α : Type*}
    [Fintype α] [DecidableEq α] (P : Finset ℕ → Prop)
    (extract : Finset ℕ → α) :
    (∑ g : α, finitePrimeModelProb U (fun S => P S ∧ extract S = g)) =
      finitePrimeModelProb U P := by
  classical
  unfold finitePrimeModelProb
  -- All filters use Classical.propDecidable.  Rewrite filter set equality first.
  trans (∑ g : α, ∑ S ∈ (U.powerset.filter P).filter (fun S => extract S = g),
          selectionWeight U S)
  · apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr ?_ (fun _ _ => rfl)
    ext S
    simp only [Finset.mem_filter]
    tauto
  · exact Finset.sum_fiberwise_of_maps_to
      (s := U.powerset.filter P) (t := (Finset.univ : Finset α))
      (g := extract) (fun S _hS => Finset.mem_univ (extract S)) (selectionWeight U)

/-- Paper §6.2 line 1722-1735: μ as a conditional probability sums to 1 when
the conditioning event has positive probability. -/
private lemma conditionalResidueMeasure_sum_eq_one {y : ℝ} {d K : ℕ} [NeZero d]
    (hpos : finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y) ≠ 0) :
    (∑ g : Fin K → (ZMod d)ˣ, conditionalResidueMeasure y d K g) = 1 := by
  classical
  unfold conditionalResidueMeasure
  rw [← Finset.sum_div]
  rw [finitePrimeModelProb_sum_partition (fun S => K ≤ goodBlockCount S y)
        (fun S => firstKResidueVector S y d K)]
  exact div_self hpos

/-- Paper §6.2 line 1796-1815 connection: when `S ⊆ window` has `K` good blocks and
`CompositeProductFailure d S` (no admissible product), the residue vector
`firstKResidueVector S y d K` is in the "bad" set: no nonempty `T ⊆ Fin K` with
`subsetProd T (g_i) = 1`.  Reason: such a `T` would give an admissible product
`e = ∏_{i ∈ T} q_{k_i}` (size + congruence + squarefree by paper line 1799-1810), but
`failure d S` says no such product exists. -/
private lemma failure_implies_bad_residue
    {y : ℝ} (hy : 2 ≤ y) (hy_log : 15 * Real.log y ≤ y)
    {d : ℕ} (hd_ge_2 : 2 ≤ d) (hd_le_y : (d : ℝ) ≤ y)
    {K : ℕ} (_hK_pos : 0 < K)
    (hK_eq : K = compositeGoodBlockThreshold y)
    {S : Finset ℕ} (_hSsub : S ⊆ compositePrimeWindow 20 y)
    (hKle : K ≤ goodBlockCount S y)
    (hfail : CompositeProductFailure 20 y d S) :
    ∀ T : Finset (Fin K), T.Nonempty →
      subsetProd T (firstKResidueVector S y d K) ≠ 1 := by
  classical
  intro T hT_ne hsubsetprod_one
  -- Construction (paper line 1796-1797):
  -- T_actual := image of T under (i ↦ q_{k_i}) gives the set of selected primes.
  set extract_idx : Fin K → ℕ := firstKGoodBlockIndices S y K with hex_idx
  set T_actual : Finset ℕ := T.image (fun i => selectedPrimeInBlock S y (extract_idx i))
    with hT_actual
  -- Strategy: Show T_actual is admissible, contradicting failure.
  apply hfail
  refine ⟨T_actual, ?_, ?_⟩
  · -- T_actual ⊆ S: each selected prime is in the corresponding good block ∩ S (paper line 1715).
    intro q hq
    rw [hT_actual, Finset.mem_image] at hq
    obtain ⟨i, _hi, rfl⟩ := hq
    -- q = selectedPrimeInBlock S y (extract_idx i).  The block extract_idx i is good for S.
    -- By selectedPrimeInBlock_mem, q ∈ compositeBlock y (extract_idx i) ∩ S.
    set k : ℕ := extract_idx i with hk_def
    -- k ∈ goodBlockIndices S y (i.e. (compositeBlock y k ∩ S).card = 1).
    have hk_mem : k ∈ goodBlockIndices S y := by
      rw [hk_def, hex_idx]
      unfold firstKGoodBlockIndices
      rw [dif_pos hKle]
      exact Finset.orderEmbOfFin_mem _ _ ⟨i.val, lt_of_lt_of_le i.isLt hKle⟩
    rw [goodBlockIndices, Finset.mem_filter] at hk_mem
    obtain ⟨_, hk_good⟩ := hk_mem
    have hmem := selectedPrimeInBlock_mem hk_good
    rw [Finset.mem_inter] at hmem
    exact hmem.2
  · -- AdmissibleCompositeProduct 20 y d T_actual.
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- (1) T_actual.Nonempty (from T.Nonempty + image is nonempty).
      rw [hT_actual]
      exact hT_ne.image _
    · -- (2) Each q ∈ T_actual is prime in window (paper line 1716).
      intro q hq
      rw [hT_actual, Finset.mem_image] at hq
      obtain ⟨i, _hi, rfl⟩ := hq
      set k : ℕ := extract_idx i with hk_def
      have hk_mem : k ∈ goodBlockIndices S y := by
        rw [hk_def, hex_idx]
        unfold firstKGoodBlockIndices
        rw [dif_pos hKle]
        exact Finset.orderEmbOfFin_mem _ _ ⟨i.val, lt_of_lt_of_le i.isLt hKle⟩
      have hk_mem_filter := hk_mem
      rw [goodBlockIndices, Finset.mem_filter] at hk_mem_filter
      obtain ⟨hk_lt_M, hk_good⟩ := hk_mem_filter
      have hmem := selectedPrimeInBlock_mem hk_good
      rw [Finset.mem_inter] at hmem
      have hq_in_block := hmem.1
      -- q is in compositeBlock y k.  By compositeBlock_prime, q is prime.
      -- By compositeBlock_prime_gt_exp_y, q > exp y.
      -- For the upper bound: q ≤ compositeBlockEndpoint y (k+1), and we need q ≤ exp(y^{A-1}).
      -- Since the block is in the window range (paper line 1588), bound holds.
      refine ⟨compositeBlock_prime hq_in_block,
        compositeBlock_prime_gt_exp_y (by linarith) hq_in_block, ?_⟩
      -- q ≤ exp(y^{A-1}): for k < M = ⌊15 log y⌋, k+1 ≤ M, so e^{k+1} ≤ e^M ≤ y^15,
      -- hence y · e^{k+1} ≤ y^16 ≤ y^19 = y^{20-1} = y^{A-1}.
      -- Membership: q ∈ compositeBlock y k means q ≤ compositeBlockEndpoint y (k+1).
      rw [compositeBlock, Finset.mem_filter] at hq_in_block
      obtain ⟨_, _, _, hq_le_endpoint⟩ := hq_in_block
      -- hq_le_endpoint : (q : ℝ) ≤ compositeBlockEndpoint y (k+1) = exp(y · e^{k+1}).
      have hk_lt_M' : k < compositeBlockCount y := by
        rw [Finset.mem_range] at hk_lt_M
        exact hk_lt_M
      have hy_pos : 0 < y := by linarith
      have hy_ge1 : (1 : ℝ) ≤ y := by linarith
      have hlog_y_nn : 0 ≤ Real.log y := Real.log_nonneg hy_ge1
      have hM_le : (compositeBlockCount y : ℝ) ≤ 15 * Real.log y := by
        unfold compositeBlockCount
        exact Nat.floor_le (by nlinarith)
      have hk1_le_logy : ((k + 1 : ℕ) : ℝ) ≤ 15 * Real.log y := by
        have : ((k + 1 : ℕ) : ℝ) ≤ (compositeBlockCount y : ℝ) := by
          exact_mod_cast (Nat.succ_le_iff.mpr hk_lt_M')
        linarith
      have hexp_le_y15 : Real.exp ((k + 1 : ℕ) : ℝ) ≤ y ^ (15 : ℕ) := by
        calc Real.exp ((k + 1 : ℕ) : ℝ)
            ≤ Real.exp (15 * Real.log y) := Real.exp_le_exp.mpr hk1_le_logy
          _ = y ^ (15 : ℕ) := by
              rw [show (15 : ℝ) * Real.log y = (15 : ℕ) * Real.log y by norm_num,
                Real.exp_nat_mul, Real.exp_log hy_pos]
      have hbound : y * Real.exp ((k + 1 : ℕ) : ℝ) ≤ y ^ ((20 : ℝ) - 1) := by
        calc y * Real.exp ((k + 1 : ℕ) : ℝ)
            ≤ y * y ^ (15 : ℕ) := mul_le_mul_of_nonneg_left hexp_le_y15 hy_pos.le
          _ = y ^ (16 : ℕ) := by ring
          _ ≤ y ^ (19 : ℕ) := pow_le_pow_right₀ hy_ge1 (by norm_num)
          _ = y ^ ((20 : ℝ) - 1) := by norm_num [Real.rpow_natCast]
      calc (selectedPrimeInBlock S y k : ℝ)
          ≤ compositeBlockEndpoint y (k + 1) := hq_le_endpoint
        _ = Real.exp (y * Real.exp ((k + 1 : ℕ) : ℝ)) := by
            unfold compositeBlockEndpoint; norm_num
        _ ≤ Real.exp (y ^ ((20 : ℝ) - 1)) := Real.exp_le_exp.mpr hbound
    · -- (3) ∏ T_actual ≡ 1 [MOD d] (paper line 1814: subset-product condition).
      -- (a) InjOn: distinct good blocks give distinct selected primes (paper line 1813).
      have h_extract_idx_mem : ∀ i : Fin K, extract_idx i ∈ goodBlockIndices S y := by
        intro i
        rw [hex_idx]
        unfold firstKGoodBlockIndices
        rw [dif_pos hKle]
        exact Finset.orderEmbOfFin_mem _ _ ⟨i.val, lt_of_lt_of_le i.isLt hKle⟩
      have h_extract_idx_inj : Function.Injective extract_idx := by
        intros i j hij
        rw [hex_idx] at hij
        unfold firstKGoodBlockIndices at hij
        rw [dif_pos hKle, dif_pos hKle] at hij
        have h_inj := (Finset.orderEmbOfFin (goodBlockIndices S y) rfl).injective
        have hij' := h_inj hij
        exact Fin.ext (Fin.mk.inj_iff.mp hij')
      have h_inj_on : Set.InjOn (fun i => selectedPrimeInBlock S y (extract_idx i))
          (T : Set (Fin K)) := by
        intros i₁ hi₁ i₂ hi₂ heq
        by_contra hi_ne
        have hk_ne : extract_idx i₁ ≠ extract_idx i₂ := fun h_eq => hi_ne (h_extract_idx_inj h_eq)
        have hmem₁ := selectedPrimeInBlock_mem
          (Finset.mem_filter.mp (h_extract_idx_mem i₁)).2
        have hmem₂ := selectedPrimeInBlock_mem
          (Finset.mem_filter.mp (h_extract_idx_mem i₂)).2
        rw [Finset.mem_inter] at hmem₁ hmem₂
        have hy_nonneg : (0 : ℝ) ≤ y := by linarith
        have hdisjoint := compositeBlock_disjoint hy_nonneg hk_ne
        rw [Finset.disjoint_left] at hdisjoint
        apply hdisjoint hmem₁.1
        have heq' : selectedPrimeInBlock S y (extract_idx i₁) =
            selectedPrimeInBlock S y (extract_idx i₂) := heq
        exact heq' ▸ hmem₂.1
      -- (b) ∏ T_actual = ∏_{i ∈ T} (selectedPrimeInBlock S y (extract_idx i)) via prod_image.
      have h_prod_image : ∏ q ∈ T_actual, q =
          ∏ i ∈ T, selectedPrimeInBlock S y (extract_idx i) := by
        rw [hT_actual]
        exact Finset.prod_image h_inj_on
      -- (c) Cast each prime's residue in ZMod d.  When block k is good ∧ coprime to d,
      --     residueOfSelectedPrime S y d k = ZMod.unitOfCoprime (selectedPrimeInBlock S y k) _.
      --     So ((firstKResidueVector S y d K i) : ZMod d) = (selectedPrimeInBlock S y (extract_idx i) : ZMod d).
      have hd_pos : 0 < d := by omega
      have h_residue_cast : ∀ i ∈ T,
          ((firstKResidueVector S y d K i : (ZMod d)ˣ) : ZMod d) =
          ((selectedPrimeInBlock S y (extract_idx i) : ℕ) : ZMod d) := by
        intro i _hi
        unfold firstKResidueVector residueOfSelectedPrime
        have hk_good := (Finset.mem_filter.mp (h_extract_idx_mem i)).2
        have hcop := selectedPrimeInBlock_coprime_d hy hd_pos hd_le_y hk_good
        rw [dif_pos ⟨hk_good, hcop⟩]
        exact ZMod.coe_unitOfCoprime _ hcop
      -- (d) hsubsetprod_one gives ∏ (firstKResidueVector i) = 1 in (ZMod d)ˣ.
      -- (e) Combine via h_residue_cast + h_prod_image to show ∏ T_actual ≡ 1 [MOD d].
      change (∏ q ∈ T_actual, q : ℕ) ≡ 1 [MOD d]
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [hT_actual, Finset.prod_image h_inj_on]
      -- Goal: ∏ i ∈ T, ((selectedPrimeInBlock... : ℕ) : ZMod d) = 1.
      -- Use h_residue_cast: each factor = ((firstKResidueVector ... : (ZMod d)ˣ) : ZMod d).
      rw [show ∏ i ∈ T, ((selectedPrimeInBlock S y (extract_idx i) : ℕ) : ZMod d) =
          ∏ i ∈ T, ((firstKResidueVector S y d K i : (ZMod d)ˣ) : ZMod d) from
        Finset.prod_congr rfl (fun i hi => (h_residue_cast i hi).symm)]
      rw [← Units.coe_prod]
      -- Goal: ((∏ i ∈ T, firstKResidueVector S y d K i : (ZMod d)ˣ) : ZMod d) = 1.
      change ((subsetProd T (firstKResidueVector S y d K) : (ZMod d)ˣ) : ZMod d) = 1
      rw [hsubsetprod_one]
      rfl
    · -- (4) d < ∏ T_actual (paper line 1811: each prime > exp y > d).
      -- Pick any q in T_actual.  Since T_actual is the image of T (nonempty), T_actual nonempty.
      -- q ∈ compositeBlock for some good block, so q > exp y > y ≥ d (paper line 1811).
      -- ∏ T_actual ≥ q (Finset.single_le_prod') > d.
      have hT_actual_ne : T_actual.Nonempty := by rw [hT_actual]; exact hT_ne.image _
      obtain ⟨q₀, hq₀⟩ := hT_actual_ne
      rw [hT_actual, Finset.mem_image] at hq₀
      obtain ⟨i₀, _hi₀, rfl⟩ := hq₀
      set k₀ : ℕ := extract_idx i₀ with hk₀_def
      have hk₀_mem : k₀ ∈ goodBlockIndices S y := by
        rw [hk₀_def, hex_idx]
        unfold firstKGoodBlockIndices
        rw [dif_pos hKle]
        exact Finset.orderEmbOfFin_mem _ _ ⟨i₀.val, lt_of_lt_of_le i₀.isLt hKle⟩
      rw [goodBlockIndices, Finset.mem_filter] at hk₀_mem
      obtain ⟨_, hk₀_good⟩ := hk₀_mem
      have hmem₀ := selectedPrimeInBlock_mem hk₀_good
      rw [Finset.mem_inter] at hmem₀
      have hq₀_in_block : selectedPrimeInBlock S y k₀ ∈ compositeBlock y k₀ := hmem₀.1
      have hq₀_gt_exp_y : Real.exp y < (selectedPrimeInBlock S y k₀ : ℝ) :=
        compositeBlock_prime_gt_exp_y (by linarith) hq₀_in_block
      have hexp_y_gt_y : (y : ℝ) < Real.exp y := by
        have hy_ne : y ≠ 0 := ne_of_gt (by linarith)
        linarith [Real.add_one_lt_exp hy_ne]
      have hq₀_gt_d : (d : ℝ) < (selectedPrimeInBlock S y k₀ : ℝ) := by
        linarith
      have hq₀_gt_d_nat : d < selectedPrimeInBlock S y k₀ := by exact_mod_cast hq₀_gt_d
      -- All primes in T_actual are ≥ 1 (prime ≥ 2 ≥ 1).
      have hT_actual_one_le : ∀ q ∈ T_actual, 1 ≤ q := by
        intro q hq
        rw [hT_actual, Finset.mem_image] at hq
        obtain ⟨j, _hj, rfl⟩ := hq
        set k := extract_idx j with hk_def
        have hk_mem : k ∈ goodBlockIndices S y := by
          rw [hk_def, hex_idx]
          unfold firstKGoodBlockIndices
          rw [dif_pos hKle]
          exact Finset.orderEmbOfFin_mem _ _ ⟨j.val, lt_of_lt_of_le j.isLt hKle⟩
        rw [goodBlockIndices, Finset.mem_filter] at hk_mem
        obtain ⟨_, hk_good⟩ := hk_mem
        have hmem_j := selectedPrimeInBlock_mem hk_good
        rw [Finset.mem_inter] at hmem_j
        exact (compositeBlock_prime hmem_j.1).one_lt.le
      have hq₀_le_prod : selectedPrimeInBlock S y k₀ ≤ ∏ q ∈ T_actual, q := by
        have hmem_in_T : (fun i => selectedPrimeInBlock S y (extract_idx i)) i₀ ∈ T_actual := by
          rw [hT_actual]; exact Finset.mem_image_of_mem _ _hi₀
        exact Finset.single_le_prod' hT_actual_one_le hmem_in_T
      -- Combine: d < q₀ ≤ ∏ T_actual.
      change d < ∏ q ∈ T_actual, q
      omega
    · -- (5) (∏ T_actual : ℝ) ≤ Real.exp (y^A) (paper line 1799-1810).
      -- Each q ∈ T_actual ≤ exp(y^{A-1}). |T_actual| ≤ |T| ≤ K ≤ 15 log y ≤ y (hy_log).
      -- ∏ T_actual ≤ exp(|T_actual| · y^{A-1}) ≤ exp(y · y^{A-1}) = exp(y^A).
      have h_each_le : ∀ q ∈ T_actual, (q : ℝ) ≤ Real.exp (y ^ ((20 : ℝ) - 1)) := by
        intro q hq
        rw [hT_actual, Finset.mem_image] at hq
        obtain ⟨i, _hi, rfl⟩ := hq
        set k : ℕ := extract_idx i with hk_def
        have hk_mem : k ∈ goodBlockIndices S y := by
          rw [hk_def, hex_idx]
          unfold firstKGoodBlockIndices
          rw [dif_pos hKle]
          exact Finset.orderEmbOfFin_mem _ _ ⟨i.val, lt_of_lt_of_le i.isLt hKle⟩
        rw [goodBlockIndices, Finset.mem_filter] at hk_mem
        obtain ⟨hk_lt_M, hk_good⟩ := hk_mem
        have hmem := selectedPrimeInBlock_mem hk_good
        rw [Finset.mem_inter] at hmem
        have hq_in_block := hmem.1
        rw [compositeBlock, Finset.mem_filter] at hq_in_block
        obtain ⟨_, _, _, hq_le_endpoint⟩ := hq_in_block
        have hk_lt_M' : k < compositeBlockCount y := by
          rw [Finset.mem_range] at hk_lt_M
          exact hk_lt_M
        have hy_pos : 0 < y := by linarith
        have hy_ge1 : (1 : ℝ) ≤ y := by linarith
        have hlog_y_nn : 0 ≤ Real.log y := Real.log_nonneg hy_ge1
        have hM_le : (compositeBlockCount y : ℝ) ≤ 15 * Real.log y := by
          unfold compositeBlockCount
          exact Nat.floor_le (by nlinarith)
        have hk1_le_logy : ((k + 1 : ℕ) : ℝ) ≤ 15 * Real.log y := by
          have : ((k + 1 : ℕ) : ℝ) ≤ (compositeBlockCount y : ℝ) := by
            exact_mod_cast (Nat.succ_le_iff.mpr hk_lt_M')
          linarith
        have hexp_le_y15 : Real.exp ((k + 1 : ℕ) : ℝ) ≤ y ^ (15 : ℕ) := by
          calc Real.exp ((k + 1 : ℕ) : ℝ)
              ≤ Real.exp (15 * Real.log y) := Real.exp_le_exp.mpr hk1_le_logy
            _ = y ^ (15 : ℕ) := by
                rw [show (15 : ℝ) * Real.log y = (15 : ℕ) * Real.log y by norm_num,
                  Real.exp_nat_mul, Real.exp_log hy_pos]
        have hbound : y * Real.exp ((k + 1 : ℕ) : ℝ) ≤ y ^ ((20 : ℝ) - 1) := by
          calc y * Real.exp ((k + 1 : ℕ) : ℝ)
              ≤ y * y ^ (15 : ℕ) := mul_le_mul_of_nonneg_left hexp_le_y15 hy_pos.le
            _ = y ^ (16 : ℕ) := by ring
            _ ≤ y ^ (19 : ℕ) := pow_le_pow_right₀ hy_ge1 (by norm_num)
            _ = y ^ ((20 : ℝ) - 1) := by norm_num [Real.rpow_natCast]
        calc (selectedPrimeInBlock S y k : ℝ)
            ≤ compositeBlockEndpoint y (k + 1) := hq_le_endpoint
          _ = Real.exp (y * Real.exp ((k + 1 : ℕ) : ℝ)) := by
              unfold compositeBlockEndpoint; norm_num
          _ ≤ Real.exp (y ^ ((20 : ℝ) - 1)) := Real.exp_le_exp.mpr hbound
      -- Now bound the product.
      -- |T_actual| ≤ |T| via Finset.card_image_le.
      -- |T| ≤ K (since T : Finset (Fin K), |T| ≤ Fin K.card = K).
      have hT_actual_card : T_actual.card ≤ K := by
        rw [hT_actual]
        have h1 := Finset.card_image_le (s := T)
          (f := fun i => selectedPrimeInBlock S y (extract_idx i))
        have h2 : T.card ≤ K := by
          have := Finset.card_le_univ T
          rwa [Fintype.card_fin] at this
        linarith
      have hT_actual_R : (T_actual.card : ℝ) ≤ y := by
        -- T_actual.card ≤ K ≤ 15 log y ≤ y (using hy_log + κ < 15).
        have h1 : (T_actual.card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hT_actual_card
        have h2 : (K : ℝ) ≤ 15 * Real.log y := by
          rw [hK_eq]
          unfold compositeGoodBlockThreshold
          have hpos : 0 ≤ ((Real.exp (-1) * 15) / 2) * Real.log y := by
            apply mul_nonneg (by positivity)
            exact Real.log_nonneg (by linarith)
          have hceil := Nat.ceil_lt_add_one hpos
          -- ⌈((e⁻¹·15)/2) log y⌉ < ((e⁻¹·15)/2) log y + 1.
          -- ((e⁻¹·15)/2) ≈ 2.76, so κ log y + 1 ≤ 15 log y when 14 log y ≥ 1, i.e., log y ≥ 1/14.
          have hexp_le : Real.exp (-1) ≤ 1 := by
            rw [Real.exp_neg]
            exact inv_le_one_of_one_le₀ (Real.one_le_exp (by norm_num))
          have h_kappa_le_half : ((Real.exp (-1) * 15) / 2) ≤ 15 / 2 := by
            have h1 : Real.exp (-1) * 15 ≤ 15 := by
              have := mul_le_mul_of_nonneg_right hexp_le (by norm_num : (0 : ℝ) ≤ 15)
              linarith
            linarith
          have hlog_pos : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
          have h_kappa_log_le : ((Real.exp (-1) * 15) / 2) * Real.log y ≤ (15 / 2) * Real.log y :=
            mul_le_mul_of_nonneg_right h_kappa_le_half hlog_pos
          -- κ log y + 1 ≤ (15/2) log y + 1.  We need ≤ 15 log y.
          -- I.e., 1 ≤ (15/2) log y, i.e., log y ≥ 2/15 ≈ 0.133.
          -- For y ≥ 2, log y ≥ log 2 ≈ 0.693 > 0.133. ✓
          have hlog_ge_log2 : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
          have hlog2_lower : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
          have h_one_le : (1 : ℝ) ≤ (15 / 2) * Real.log y := by nlinarith
          have hceil_R : (⌈((Real.exp (-1) * 15) / 2) * Real.log y⌉₊ : ℝ) ≤
              ((Real.exp (-1) * 15) / 2) * Real.log y + 1 := by
            have := Nat.ceil_lt_add_one hpos
            linarith
          linarith
        linarith
      -- Now log (∏ T_actual) ≤ ∑ y^{A-1} = T_actual.card * y^{A-1} ≤ y * y^{A-1} = y^A.
      have h_each_pos : ∀ q ∈ T_actual, (0 : ℝ) < q := by
        intro q hq
        rw [hT_actual, Finset.mem_image] at hq
        obtain ⟨i, _, rfl⟩ := hq
        set k : ℕ := extract_idx i with hk_def_p
        have hk_mem_p : k ∈ goodBlockIndices S y := by
          rw [hk_def_p, hex_idx]
          unfold firstKGoodBlockIndices
          rw [dif_pos hKle]
          exact Finset.orderEmbOfFin_mem _ _ ⟨i.val, lt_of_lt_of_le i.isLt hKle⟩
        rw [goodBlockIndices, Finset.mem_filter] at hk_mem_p
        have hmem := selectedPrimeInBlock_mem hk_mem_p.2
        rw [Finset.mem_inter] at hmem
        exact_mod_cast (compositeBlock_prime hmem.1).pos
      have h_prod_eq_cast : ((∏ q ∈ T_actual, q : ℕ) : ℝ) = ∏ q ∈ T_actual, (q : ℝ) := by
        push_cast; rfl
      rw [h_prod_eq_cast]
      have h_prod_le_exp_sum : (∏ q ∈ T_actual, (q : ℝ)) ≤
          ∏ q ∈ T_actual, Real.exp (y ^ ((20 : ℝ) - 1)) := by
        apply Finset.prod_le_prod
        · intro q hq; exact (h_each_pos q hq).le
        · exact h_each_le
      have h_prod_const : (∏ _q ∈ T_actual, Real.exp (y ^ ((20 : ℝ) - 1))) =
          Real.exp ((T_actual.card : ℝ) * y ^ ((20 : ℝ) - 1)) := by
        rw [Finset.prod_const, ← Real.exp_nat_mul]
      rw [h_prod_const] at h_prod_le_exp_sum
      have hy_pos : 0 < y := by linarith
      have hyA_minus_1_pos : (0 : ℝ) ≤ y ^ ((20 : ℝ) - 1) := Real.rpow_nonneg hy_pos.le _
      have h_card_yA1_le : (T_actual.card : ℝ) * y ^ ((20 : ℝ) - 1) ≤ y ^ (20 : ℝ) := by
        have h1 : (T_actual.card : ℝ) * y ^ ((20 : ℝ) - 1) ≤ y * y ^ ((20 : ℝ) - 1) :=
          mul_le_mul_of_nonneg_right hT_actual_R hyA_minus_1_pos
        have h2 : y * y ^ ((20 : ℝ) - 1) = y ^ ((20 : ℝ)) := by
          rw [mul_comm, ← Real.rpow_add_one (ne_of_gt hy_pos) ((20 : ℝ) - 1)]
          ring_nf
        linarith
      calc ∏ q ∈ T_actual, (q : ℝ)
          ≤ Real.exp ((T_actual.card : ℝ) * y ^ ((20 : ℝ) - 1)) := h_prod_le_exp_sum
        _ ≤ Real.exp (y ^ (20 : ℝ)) := Real.exp_le_exp.mpr h_card_yA1_le

/-- Triangle inequality for product measures (paper §6.2 line 1748-1750 standard fact).
For any two product measures `∏_i f_i` and `∏_i u_i` on `G^K` with each f_i, u_i a probability,
the L1 distance is at most the sum of marginal L1 distances. -/
private lemma prod_tv_le_sum_tv {G : Type*} [Fintype G] [DecidableEq G]
    {K : ℕ} (f : Fin K → G → ℝ) (u : G → ℝ)
    (hu_nn : ∀ g, 0 ≤ u g)
    (hu_sum : (∑ g, u g) = 1)
    (hf_nn : ∀ i g, 0 ≤ f i g)
    (hf_sum : ∀ i, (∑ g, f i g) = 1)
    (ε : ℝ)
    (h_tv : ∀ i, (∑ g, |f i g - u g|) ≤ ε) :
    (∑ gvec : Fin K → G, |(∏ i, f i (gvec i)) - (∏ i, u (gvec i))|) ≤ K * ε := by
  induction K with
  | zero =>
    -- K = 0: both products are 1 (empty product), sum over Fin 0 → G has one element.
    simp [Finset.prod_empty, sub_self, abs_zero]
  | succ K ih =>
    -- Step 1: Sum split via Fin.consEquiv.
    have h_sum_split : (∑ gvec : Fin (K+1) → G,
        |(∏ i, f i (gvec i)) - (∏ i, u (gvec i))|) =
      ∑ p : G × (Fin K → G),
        |(∏ i : Fin (K+1), f i ((Fin.cons p.1 p.2 : Fin (K+1) → G) i)) -
         (∏ i : Fin (K+1), u ((Fin.cons p.1 p.2 : Fin (K+1) → G) i))| := by
      apply Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (K+1) => G)).symm
      intro gvec
      have h_eq : (Fin.cons ((Fin.consEquiv (fun _ : Fin (K+1) => G)).symm gvec).1
            ((Fin.consEquiv (fun _ : Fin (K+1) => G)).symm gvec).2 : Fin (K+1) → G) =
            gvec := by
        ext i
        simp [Fin.consEquiv, Fin.cons_self_tail]
      rw [h_eq]
    rw [h_sum_split]
    -- Step 2: Expand each product via Fin.prod_univ_succ.
    have h_prod_expand : ∀ p : G × (Fin K → G),
        (∏ i : Fin (K+1), f i ((Fin.cons p.1 p.2 : Fin (K+1) → G) i)) =
        f 0 p.1 * ∏ i : Fin K, f i.succ (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ]
    have h_prod_expand_u : ∀ p : G × (Fin K → G),
        (∏ i : Fin (K+1), u ((Fin.cons p.1 p.2 : Fin (K+1) → G) i)) =
        u p.1 * ∏ i : Fin K, u (p.2 i) := by
      intro p
      rw [Fin.prod_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ]
    -- Step 3: Apply triangle inequality |a·c - b·d| ≤ |a-b|·d + a·|c-d|.
    have h_pointwise : ∀ p : G × (Fin K → G),
        |(∏ i : Fin (K+1), f i ((Fin.cons p.1 p.2 : Fin (K+1) → G) i)) -
         (∏ i : Fin (K+1), u ((Fin.cons p.1 p.2 : Fin (K+1) → G) i))| ≤
        |f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i)) +
        f 0 p.1 * |(∏ i : Fin K, f i.succ (p.2 i)) - (∏ i : Fin K, u (p.2 i))| := by
      intro p
      rw [h_prod_expand p, h_prod_expand_u p]
      have ha_nn : 0 ≤ f 0 p.1 := hf_nn 0 p.1
      have hd_nn : 0 ≤ ∏ i : Fin K, u (p.2 i) :=
        Finset.prod_nonneg (fun i _ => hu_nn (p.2 i))
      calc |f 0 p.1 * (∏ i : Fin K, f i.succ (p.2 i)) -
            u p.1 * (∏ i : Fin K, u (p.2 i))|
          = |f 0 p.1 * ((∏ i : Fin K, f i.succ (p.2 i)) - (∏ i : Fin K, u (p.2 i))) +
             (f 0 p.1 - u p.1) * (∏ i : Fin K, u (p.2 i))| := by ring_nf
        _ ≤ |f 0 p.1 * ((∏ i : Fin K, f i.succ (p.2 i)) - (∏ i : Fin K, u (p.2 i)))| +
            |(f 0 p.1 - u p.1) * (∏ i : Fin K, u (p.2 i))| := abs_add_le _ _
        _ = f 0 p.1 * |(∏ i : Fin K, f i.succ (p.2 i)) - (∏ i : Fin K, u (p.2 i))| +
            |f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i)) := by
            rw [abs_mul, abs_of_nonneg ha_nn, abs_mul, abs_of_nonneg hd_nn]
        _ = |f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i)) +
            f 0 p.1 * |(∏ i : Fin K, f i.succ (p.2 i)) - (∏ i : Fin K, u (p.2 i))| := by ring
    -- Step 4: Sum the pointwise bound.
    have h_sum_le : (∑ p : G × (Fin K → G),
        |(∏ i : Fin (K+1), f i ((Fin.cons p.1 p.2 : Fin (K+1) → G) i)) -
         (∏ i : Fin (K+1), u ((Fin.cons p.1 p.2 : Fin (K+1) → G) i))|) ≤
        (∑ p : G × (Fin K → G),
          (|f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i)) +
           f 0 p.1 * |(∏ i : Fin K, f i.succ (p.2 i)) - (∏ i : Fin K, u (p.2 i))|)) :=
      Finset.sum_le_sum (fun p _ => h_pointwise p)
    refine le_trans h_sum_le ?_
    rw [Finset.sum_add_distrib]
    -- Helper: ∑ tail : Fin K → G, ∏ i, u (tail i) = 1 (sum-product swap, ∑u = 1).
    have h_sum_prod_u : (∑ tail : Fin K → G, ∏ i : Fin K, u (tail i)) = 1 := by
      rw [← Fintype.piFinset_univ]
      rw [← Finset.prod_univ_sum (fun _ : Fin K => (Finset.univ : Finset G))
        (fun _ x => u x)]
      simp [hu_sum]
    -- Bound term1: ∑ p, |f 0 p.1 - u p.1| · (∏ u (p.2 i))
    -- = ∑_{g₀,tail} |f 0 g₀ - u g₀| · ∏ u (tail i)
    -- = (∑_{g₀} |f 0 g₀ - u g₀|) · (∑_{tail} ∏ u (tail i))   [Fubini]
    -- = (∑ |f 0 - u|) · 1 ≤ ε.
    have h_term1_split : (∑ p : G × (Fin K → G),
        |f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i))) =
        (∑ g₀ : G, |f 0 g₀ - u g₀|) * (∑ tail : Fin K → G, ∏ i : Fin K, u (tail i)) := by
      rw [Finset.sum_mul_sum]
      exact Fintype.sum_prod_type'
        (fun (g₀ : G) (tail : Fin K → G) =>
          |f 0 g₀ - u g₀| * ∏ i : Fin K, u (tail i))
    have h_term1_le : (∑ p : G × (Fin K → G),
        |f 0 p.1 - u p.1| * (∏ i : Fin K, u (p.2 i))) ≤ ε := by
      rw [h_term1_split, h_sum_prod_u, mul_one]
      exact h_tv 0
    -- Bound term2: ∑ p, f 0 p.1 · |∏ f.succ - ∏ u|
    -- = (∑_{g₀} f 0 g₀) · ∑_{tail} |∏ f.succ - ∏ u|   [Fubini]
    -- = 1 · ∑ |...| ≤ K · ε   [hf_sum 0; ih on f.succ].
    have h_term2_split : (∑ p : G × (Fin K → G),
        f 0 p.1 * |(∏ i : Fin K, f i.succ (p.2 i)) - (∏ i : Fin K, u (p.2 i))|) =
        (∑ g₀ : G, f 0 g₀) * (∑ tail : Fin K → G,
          |(∏ i : Fin K, f i.succ (tail i)) - (∏ i : Fin K, u (tail i))|) := by
      rw [Finset.sum_mul_sum]
      exact Fintype.sum_prod_type'
        (fun (g₀ : G) (tail : Fin K → G) =>
          f 0 g₀ * |(∏ i : Fin K, f i.succ (tail i)) - (∏ i : Fin K, u (tail i))|)
    have h_ih_applied : (∑ tail : Fin K → G,
        |(∏ i : Fin K, f i.succ (tail i)) - (∏ i : Fin K, u (tail i))|) ≤ K * ε :=
      ih (fun i => f i.succ) (fun i g => hf_nn i.succ g)
        (fun i => hf_sum i.succ) (fun i => h_tv i.succ)
    have h_term2_le : (∑ p : G × (Fin K → G),
        f 0 p.1 * |(∏ i : Fin K, f i.succ (p.2 i)) - (∏ i : Fin K, u (p.2 i))|) ≤ K * ε := by
      rw [h_term2_split, hf_sum 0, one_mul]
      exact h_ih_applied
    -- Combine.
    have hKε_succ : (K : ℝ) * ε + ε = (↑(K + 1)) * ε := by push_cast; ring
    linarith

/-- Top-level `extractKVec`: when `K ≤ goodBlockCount S y`, projects `firstKGoodBlockIndices`
to `Fin K → Fin (compositeBlockCount y)`.  Otherwise defaults to constant 0 (requires `M > 0`).
This avoids inline `Fin.mk` placeholders in subsequent proofs. -/
private noncomputable def extractKVec {y : ℝ} (hM_pos : 0 < compositeBlockCount y)
    (S : Finset ℕ) (K : ℕ) : Fin K → Fin (compositeBlockCount y) := fun i =>
  if h : K ≤ goodBlockCount S y then
    ⟨firstKGoodBlockIndices S y K i, by
      unfold firstKGoodBlockIndices
      rw [dif_pos h]
      have hmem : Finset.orderEmbOfFin (goodBlockIndices S y) rfl
          ⟨i.val, lt_of_lt_of_le i.isLt h⟩ ∈ goodBlockIndices S y :=
        Finset.orderEmbOfFin_mem _ _ _
      have hsubset : goodBlockIndices S y ⊆ Finset.range (compositeBlockCount y) :=
        Finset.filter_subset _ _
      exact Finset.mem_range.mp (hsubset hmem)⟩
  else
    ⟨0, hM_pos⟩

/-- When `K ≤ #good`, `extractKVec` exposes `firstKGoodBlockIndices` directly. -/
private lemma extractKVec_val_of_le {y : ℝ} {hM_pos : 0 < compositeBlockCount y}
    {S : Finset ℕ} {K : ℕ} (hKle : K ≤ goodBlockCount S y) (i : Fin K) :
    (extractKVec hM_pos S K i).val = firstKGoodBlockIndices S y K i := by
  unfold extractKVec
  rw [dif_pos hKle]

/-- Under "K ≤ #good ∧ extractKVec = kvec", the residue vector `firstKResidueVector` equals
the per-block-selected-prime residue at `(kvec i).val`.  Direct from
`firstKResidueVector` def + `extractKVec_val_of_le`. -/
private lemma firstKResidueVector_eq_via_extractKVec
    {y : ℝ} {hM_pos : 0 < compositeBlockCount y}
    {S : Finset ℕ} {d K : ℕ} {kvec : Fin K → Fin (compositeBlockCount y)}
    (hKle : K ≤ goodBlockCount S y) (hext : extractKVec hM_pos S K = kvec) (i : Fin K) :
    firstKResidueVector S y d K i = residueOfSelectedPrime S y d (kvec i).val := by
  unfold firstKResidueVector
  have h_eq : firstKGoodBlockIndices S y K i = (kvec i).val := by
    rw [← extractKVec_val_of_le (hM_pos := hM_pos) hKle i, hext]
  rw [h_eq]

/-- Function-level version of `firstKResidueVector_eq_via_extractKVec`: residue vector
equality reduces to per-block-selected-prime residue equality at kvec indices. -/
private lemma firstKResidueVector_eq_iff_per_block
    {y : ℝ} {hM_pos : 0 < compositeBlockCount y}
    {S : Finset ℕ} {d K : ℕ} {kvec : Fin K → Fin (compositeBlockCount y)}
    {g : Fin K → (ZMod d)ˣ}
    (hKle : K ≤ goodBlockCount S y) (hext : extractKVec hM_pos S K = kvec) :
    firstKResidueVector S y d K = g ↔
    ∀ i : Fin K, residueOfSelectedPrime S y d (kvec i).val = g i := by
  constructor
  · intro h_vec_eq i
    rw [← firstKResidueVector_eq_via_extractKVec (hM_pos := hM_pos) hKle hext i, h_vec_eq]
  · intro h_per_i
    funext i
    rw [firstKResidueVector_eq_via_extractKVec (hM_pos := hM_pos) hKle hext i]
    exact h_per_i i

/-- Paper §6.2 line 1722-1735: mixture decomposition of `conditionalResidueMeasure`.
For each realized index vector `kvec : Fin K → Fin M`, the joint conditional residue
distribution factorizes as a product (paper line 1722-1726: "blocks are disjoint →
independent").  Averaging over realized index vectors gives the mixture identity:

`μ(g) = ∑ kvec, π(kvec) · ∏_i p_{kvec_i}(g_i)`

where:
* `kvec : Fin K → Fin M` ranges over `Fintype.piFinset` (full product) with `π(kvec) = 0`
  outside the `ValidKVec` (strictly increasing, all blocks good) sub-event.
* `π(kvec) := finitePrimeModelProb(...firstKGoodBlockIndices = kvec...) / pmodel_K_good`.
* `p_k(g) := blockConditionalResidueProbability (compositeBlock y k) d g.val`.

This identity is paper line 1722-1735 verbatim: "condition on any possible value of
the index vector ... since the blocks are disjoint, ... the law inside each such block
is the law of the unique selected prime conditional on that block being good."

Proof requires ~150 LOC of pmodel sum manipulation. -/
private lemma conditionalResidueMeasure_mixture_identity
    {y : ℝ} {d K : ℕ} [NeZero d]
    (_hy : 2 ≤ y) (_hd_ge_2 : 2 ≤ d) (_hd_le_y : (d : ℝ) ≤ y)
    (hsub_block : ∀ k : ℕ, k < compositeBlockCount y →
      compositeBlock y k ⊆ compositePrimeWindow 20 y)
    (hpos : finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y) ≠ 0) :
    ∃ pdist : (Fin K → Fin (compositeBlockCount y)) → ℝ,
      (∀ kvec, 0 ≤ pdist kvec) ∧
      (∑ kvec : Fin K → Fin (compositeBlockCount y), pdist kvec) = 1 ∧
      ∀ g : Fin K → (ZMod d)ˣ,
        conditionalResidueMeasure y d K g =
          ∑ kvec : Fin K → Fin (compositeBlockCount y),
            pdist kvec *
              ∏ i : Fin K,
                blockConditionalResidueProbability
                  (compositeBlock y (kvec i).val) d ((g i : ZMod d).val) := by
  classical
  -- Paper §6.2 line 1722-1735: build pdist by partitioning {S : ≥K good} according to
  -- the realized firstKGoodBlockIndices.
  -- pdist(kvec) = pmodel(K ≤ #good ∧ ∀ i, firstKGoodBlockIndices S y K i = (kvec i).val) / pmodel_K_good.
  set pmodel_K_good : ℝ := finitePrimeModelProb (compositePrimeWindow 20 y)
    (fun S => K ≤ goodBlockCount S y) with hpmodel_K_good_def
  let pdist : (Fin K → Fin (compositeBlockCount y)) → ℝ := fun kvec =>
    finitePrimeModelProb (compositePrimeWindow 20 y)
        (fun S => K ≤ goodBlockCount S y ∧
          ∀ i : Fin K, firstKGoodBlockIndices S y K i = (kvec i).val) /
      pmodel_K_good
  refine ⟨pdist, ?_, ?_, ?_⟩
  · -- (1) 0 ≤ pdist kvec
    intro kvec
    apply div_nonneg
    · exact finitePrimeModelProb_nonneg
        (fun _q hq => compositePrimeWindow_one_le hq) _
    · exact finitePrimeModelProb_nonneg
        (fun _q hq => compositePrimeWindow_one_le hq) _
  · -- (2) ∑ pdist = 1: case split K = 0 vs K > 0.
    classical
    by_cases hK_zero : K = 0
    · -- K = 0: Fin 0 → α has unique element (empty fn).  pdist(empty) = pmodel(0≤#good)/pmodel_K_good.
      subst hK_zero
      -- Show univ = {empty fn}
      have h_univ_singleton :
          (Finset.univ : Finset (Fin 0 → Fin (compositeBlockCount y))) =
          ({fun i : Fin 0 => (Fin.elim0 i : Fin (compositeBlockCount y))} :
            Finset (Fin 0 → Fin (compositeBlockCount y))) := by
        ext kvec
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        funext i; exact i.elim0
      rw [h_univ_singleton, Finset.sum_singleton]
      -- Goal: pdist (empty fn) = 1
      -- Predicate simplifies: 0 ≤ x always, ∀ i : Fin 0 vacuous.
      have h_K_good : pmodel_K_good = 1 := by
        show finitePrimeModelProb (compositePrimeWindow 20 y)
          (fun S => 0 ≤ goodBlockCount S y) = 1
        have h_eq : (fun S : Finset ℕ => 0 ≤ goodBlockCount S y) = (fun _ => True) := by
          funext S
          exact propext (iff_true_intro (Nat.zero_le _))
        rw [h_eq]
        exact finitePrimeModelProb_true _
      -- pdist (empty fn) = pmodel(0 ≤ #good ∧ vacuous) / pmodel_K_good = pmodel(0 ≤ #good) / 1 = 1
      have h_pi : pdist (fun i : Fin 0 => (Fin.elim0 i : Fin (compositeBlockCount y))) = 1 := by
        show finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => 0 ≤ goodBlockCount S y ∧ ∀ i : Fin 0, _) /
          pmodel_K_good = 1
        rw [show (fun S : Finset ℕ => 0 ≤ goodBlockCount S y ∧
                ∀ i : Fin 0, firstKGoodBlockIndices S y 0 i =
                  ((fun i : Fin 0 => (Fin.elim0 i : Fin (compositeBlockCount y))) i).val) =
              (fun _ : Finset ℕ => True) from ?_]
        · rw [finitePrimeModelProb_true, h_K_good, div_one]
        · funext S
          refine propext ⟨fun _ => trivial, fun _ => ⟨Nat.zero_le _, fun i => i.elim0⟩⟩
      exact h_pi
    · -- K > 0 case: partition argument using top-level `extractKVec`.
      have hK_pos : 0 < K := Nat.pos_of_ne_zero hK_zero
      -- Derive M ≥ K from hpos.
      have hM_ge_K : K ≤ compositeBlockCount y := by
        by_contra h_lt
        push_neg at h_lt
        apply hpos
        show finitePrimeModelProb (compositePrimeWindow 20 y)
          (fun S => K ≤ goodBlockCount S y) = 0
        have h_good_le_M : ∀ S, goodBlockCount S y ≤ compositeBlockCount y := by
          intro S
          rw [goodBlockCount_eq_card_indices]
          calc (goodBlockIndices S y).card
              ≤ (Finset.range (compositeBlockCount y)).card := by
                apply Finset.card_le_card
                show (Finset.range (compositeBlockCount y)).filter _ ⊆ _
                exact Finset.filter_subset _ _
            _ = compositeBlockCount y := Finset.card_range _
        have h_pred_false : (fun S : Finset ℕ => K ≤ goodBlockCount S y) = (fun _ => False) := by
          funext S
          simp only [eq_iff_iff, iff_false]
          have := h_good_le_M S
          omega
        rw [h_pred_false]
        unfold finitePrimeModelProb
        simp [Finset.filter_false]
      have hM_pos : 0 < compositeBlockCount y := lt_of_lt_of_le hK_pos hM_ge_K
      -- Apply finitePrimeModelProb_sum_partition with extractKVec.
      have h_partition := finitePrimeModelProb_sum_partition
        (U := compositePrimeWindow 20 y)
        (P := fun S => K ≤ goodBlockCount S y)
        (α := Fin K → Fin (compositeBlockCount y))
        (extractKVec hM_pos · K)
      -- Match predicates: under K ≤ #good, (∀ i, firstKGood... = (kvec i).val) ↔ extractKVec = kvec.
      have h_pi_pred : ∀ kvec : Fin K → Fin (compositeBlockCount y),
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧
                ∀ i, firstKGoodBlockIndices S y K i = (kvec i).val) =
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧ extractKVec hM_pos S K = kvec) := by
        intro kvec
        unfold finitePrimeModelProb
        congr 1
        ext S
        simp only [Finset.mem_filter, and_congr_right_iff]
        intro _ hKle
        constructor
        · intro hfk
          funext i
          apply Fin.ext
          rw [extractKVec_val_of_le hKle]
          exact hfk i
        · intro hext i
          have h_extract_i := congr_fun hext i
          rw [← h_extract_i, extractKVec_val_of_le hKle]
      -- Final: ∑ pdist = ∑ pmodel(P_kvec) / pmodel_K_good = pmodel_K_good / pmodel_K_good = 1.
      show ∑ kvec, finitePrimeModelProb (compositePrimeWindow 20 y) _ / pmodel_K_good = 1
      rw [← Finset.sum_div]
      rw [show (∑ kvec : Fin K → Fin (compositeBlockCount y),
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧
                ∀ i, firstKGoodBlockIndices S y K i = (kvec i).val)) =
          pmodel_K_good from ?_]
      · exact div_self hpos
      rw [show (fun kvec : Fin K → Fin (compositeBlockCount y) =>
            finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧
                ∀ i, firstKGoodBlockIndices S y K i = (kvec i).val)) =
          (fun kvec => finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => K ≤ goodBlockCount S y ∧ extractKVec hM_pos S K = kvec))
        from funext h_pi_pred]
      exact h_partition
  · -- (3) Mixture identity (paper line 1722-1735, conditional independence).
    intro g
    classical
    by_cases hK_zero : K = 0
    · -- K = 0: μ(empty fn) = 1, ∑_kvec pdist · ∏(empty) = pdist(empty) · 1 = 1.  Both sides = 1.
      subst hK_zero
      have h_univ_singleton :
          (Finset.univ : Finset (Fin 0 → Fin (compositeBlockCount y))) =
          ({fun i : Fin 0 => (Fin.elim0 i : Fin (compositeBlockCount y))} :
            Finset (Fin 0 → Fin (compositeBlockCount y))) := by
        ext kvec
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        funext i; exact i.elim0
      rw [h_univ_singleton, Finset.sum_singleton]
      -- RHS = pdist(empty) · ∏_{i : Fin 0} ... = pdist(empty) · 1.
      rw [show (∏ i : Fin 0,
            blockConditionalResidueProbability
              (compositeBlock y _) d _) = 1 from Finset.prod_empty.trans rfl]
      rw [mul_one]
      -- Goal: μ g = pdist (empty fn).  For K = 0, both predicates are equivalent (vacuous).
      show finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => 0 ≤ goodBlockCount S y ∧ firstKResidueVector S y d 0 = g) /
          pmodel_K_good =
          finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => 0 ≤ goodBlockCount S y ∧
              ∀ i : Fin 0, firstKGoodBlockIndices S y 0 i =
                ((fun i : Fin 0 => (Fin.elim0 i : Fin (compositeBlockCount y))) i).val) /
          pmodel_K_good
      congr 1
      unfold finitePrimeModelProb
      congr 1
      ext S
      simp only [Finset.mem_filter]
      refine and_congr_right_iff.mpr (fun _ => ?_)
      refine and_congr_right_iff.mpr (fun _ => ?_)
      constructor
      · intro _ i; exact i.elim0
      · intro _
        funext i; exact i.elim0
    · -- K > 0 case: paper line 1722-1735 conditional independence over disjoint blocks.
      have hK_pos : 0 < K := Nat.pos_of_ne_zero hK_zero
      -- Derive M ≥ K from hpos.
      have hM_ge_K : K ≤ compositeBlockCount y := by
        by_contra h_lt
        push_neg at h_lt
        apply hpos
        show finitePrimeModelProb (compositePrimeWindow 20 y)
          (fun S => K ≤ goodBlockCount S y) = 0
        have h_good_le_M : ∀ S, goodBlockCount S y ≤ compositeBlockCount y := by
          intro S
          rw [goodBlockCount_eq_card_indices]
          calc (goodBlockIndices S y).card
              ≤ (Finset.range (compositeBlockCount y)).card := by
                apply Finset.card_le_card
                show (Finset.range (compositeBlockCount y)).filter _ ⊆ _
                exact Finset.filter_subset _ _
            _ = compositeBlockCount y := Finset.card_range _
        have h_pred_false : (fun S : Finset ℕ => K ≤ goodBlockCount S y) = (fun _ => False) := by
          funext S
          simp only [eq_iff_iff, iff_false]
          have := h_good_le_M S
          omega
        rw [h_pred_false]
        unfold finitePrimeModelProb
        simp [Finset.filter_false]
      have hM_pos : 0 < compositeBlockCount y := lt_of_lt_of_le hK_pos hM_ge_K
      -- (Step 2 deep sub-claim) Per-kvec product factorization (paper line 1722-1735).
      -- For each kvec, the joint pmodel factors as (pmodel of "kvec realized") · ∏ residue probs.
      have h_step2_factor : ∀ kvec : Fin K → Fin (compositeBlockCount y),
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧
                firstKResidueVector S y d K = g ∧ extractKVec hM_pos S K = kvec) =
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧ extractKVec hM_pos S K = kvec) *
          ∏ i : Fin K,
            blockConditionalResidueProbability
              (compositeBlock y (kvec i).val) d ((g i : ZMod d).val) := by
        intro kvec
        classical
        -- Paper §6.2 lines 1722-1735, conditional independence over disjoint blocks:
        -- "condition on any possible value of the index vector ... since the blocks are
        --  disjoint, the selected prime in each conditioned-good block is independent ..."
        -- Case split on whether kvec is strictly monotone in val.  If not, the predicate
        -- "extractKVec = kvec" is unsatisfiable since firstKGoodBlockIndices is strictly
        -- monotone (orderEmbOfFin), so both pmodels are 0.
        by_cases h_mono : StrictMono (fun i : Fin K => (kvec i).val)
        · -- Strictly monotone case: predicate equivalence with blockEvents_with_residues form.
          -- kvec strictly monotone ⟹ kvec injective.
          have h_kvec_inj : Function.Injective fun i : Fin K => (kvec i).val := h_mono.injective
          have h_kvec_inj_full : Function.Injective kvec := by
            intro i j hij
            have hi_val : (kvec i).val = (kvec j).val := congrArg Fin.val hij
            have h_eq : i = j := h_kvec_inj hi_val
            exact h_eq
          -- Define A_kvec = image of kvec.val.
          set A_kvec : Finset ℕ := Finset.image (fun i : Fin K => (kvec i).val) Finset.univ
            with hA_kvec_def
          have hA_card : A_kvec.card = K := by
            rw [hA_kvec_def, Finset.card_image_of_injective _ h_kvec_inj]
            exact Finset.card_univ.trans (Fintype.card_fin K)
          -- Each (kvec i).val < M.
          have h_kvec_lt_M : ∀ i : Fin K, (kvec i).val < compositeBlockCount y :=
            fun i => (kvec i).isLt
          -- A_kvec ⊆ Finset.range M.
          have hA_sub_range : A_kvec ⊆ Finset.range (compositeBlockCount y) := by
            intro k hk
            rw [hA_kvec_def, Finset.mem_image] at hk
            rcases hk with ⟨i, _, rfl⟩
            exact Finset.mem_range.mpr (h_kvec_lt_M i)
          -- Max of A_kvec is (kvec ⟨K-1, hK_pos⟩).val.
          set kvec_last_val : ℕ := (kvec ⟨K - 1, by omega⟩).val with hklv
          -- Define B_kvec = (Finset.range (kvec_last_val + 1)) \ A_kvec.
          -- These are the "must be bad" intervening indices.
          set B_kvec : Finset ℕ := (Finset.range (kvec_last_val + 1)) \ A_kvec with hB_kvec_def
          -- B_kvec is disjoint from A_kvec.
          have hAB_disj : Disjoint A_kvec B_kvec := by
            rw [hB_kvec_def]
            exact Finset.disjoint_sdiff
          -- B_kvec ⊆ Finset.range M.
          have hkvec_last_lt_M : kvec_last_val < compositeBlockCount y := by
            rw [hklv]; exact h_kvec_lt_M _
          have hB_sub_range : B_kvec ⊆ Finset.range (compositeBlockCount y) := by
            intro k hk
            rw [hB_kvec_def, Finset.mem_sdiff] at hk
            have h_in_range : k ∈ Finset.range (kvec_last_val + 1) := hk.1
            rw [Finset.mem_range] at h_in_range ⊢
            omega
          -- F: ℕ → Finset ℕ as compositeBlock y.
          set F : ℕ → Finset ℕ := fun k => compositeBlock y k with hF_def
          -- hsub: for k ∈ A_kvec ∪ B_kvec, F k ⊆ compositePrimeWindow 20 y.
          have hsub_AB : ∀ k ∈ A_kvec ∪ B_kvec, F k ⊆ compositePrimeWindow 20 y := by
            intro k hk
            have hkM : k < compositeBlockCount y := by
              rcases Finset.mem_union.mp hk with hkA | hkB
              · exact Finset.mem_range.mp (hA_sub_range hkA)
              · exact Finset.mem_range.mp (hB_sub_range hkB)
            exact hsub_block k hkM
          -- hpair: pairwise disjoint blocks.
          have hy_nonneg : (0 : ℝ) ≤ y := by linarith [_hy]
          have hpair_AB : ∀ i ∈ A_kvec ∪ B_kvec, ∀ j ∈ A_kvec ∪ B_kvec,
              i ≠ j → Disjoint (F i) (F j) := by
            intro i _hi j _hj hij
            exact compositeBlock_disjoint hy_nonneg hij
          -- hF_prime: blocks contain primes.
          have hF_prime_AB : ∀ k ∈ A_kvec, ∀ q ∈ F k, q.Prime :=
            fun _k _hk _q hq => compositeBlock_prime hq
          -- Define resvec: A_kvec → ℕ giving the desired residue.
          -- For k = (kvec i).val, resvec k = (g i : ZMod d).val.
          let resvec : ℕ → ℕ := fun k =>
            if h : k ∈ A_kvec then
              let i := Classical.choose ((Finset.mem_image.mp (hA_kvec_def ▸ h)))
              (g i : ZMod d).val
            else 0
          -- Apply blockEvents_with_residues to LHS via predicate equivalence.
          -- LHS predicate ⟺ blockEvents_with_residues form on (A_kvec, B_kvec, F, resvec).
          -- This equivalence captures paper §6.2 lines 1722-1735 verbatim.
          --
          -- Predicate equivalence (no residues): used for both LHS and RHS_first proofs.
          have h_pred_eq : ∀ S : Finset ℕ, S ⊆ compositePrimeWindow 20 y →
              ((K ≤ goodBlockCount S y ∧ extractKVec hM_pos S K = kvec) ↔
                blockEvents F A_kvec B_kvec S) := by
            intro S _hS_sub
            constructor
            · -- Forward.
              rintro ⟨hKle, hext⟩
              refine ⟨?_, ?_⟩
              · intro k hk_in_A
                rw [hA_kvec_def] at hk_in_A
                rcases Finset.mem_image.mp hk_in_A with ⟨i, _, hi_eq⟩
                have h_extract_i := extractKVec_val_of_le (hM_pos := hM_pos) hKle i
                have h_extract_eq := congrArg Fin.val (congrFun hext i)
                rw [h_extract_i] at h_extract_eq
                have h_in_good : firstKGoodBlockIndices S y K i ∈ goodBlockIndices S y := by
                  unfold firstKGoodBlockIndices
                  rw [dif_pos hKle]
                  exact Finset.orderEmbOfFin_mem _ _ _
                rw [h_extract_eq] at h_in_good
                rw [← hi_eq]
                show (F (kvec i).val ∩ S).card = 1
                show (compositeBlock y (kvec i).val ∩ S).card = 1
                exact (Finset.mem_filter.mp h_in_good).2
              · intro k hk_in_B
                rw [hB_kvec_def, Finset.mem_sdiff] at hk_in_B
                obtain ⟨hk_in_range, hk_not_A⟩ := hk_in_B
                intro hk_good
                have hk_in_GBI : k ∈ goodBlockIndices S y := by
                  show k ∈ (Finset.range (compositeBlockCount y)).filter _
                  rw [Finset.mem_filter]
                  refine ⟨?_, hk_good⟩
                  rw [Finset.mem_range]
                  have hk_le_max : k ≤ kvec_last_val := by
                    rw [Finset.mem_range] at hk_in_range; omega
                  exact lt_of_le_of_lt hk_le_max hkvec_last_lt_M
                have hk_le_max : k ≤ kvec_last_val := by
                  rw [Finset.mem_range] at hk_in_range; omega
                apply hk_not_A
                have h_range := Finset.range_orderEmbOfFin (goodBlockIndices S y)
                  (k := goodBlockCount S y) rfl
                have hk_in_range' : (k : ℕ) ∈ Set.range
                    (Finset.orderEmbOfFin (goodBlockIndices S y)
                      (k := goodBlockCount S y) rfl) := by
                  rw [h_range]; exact_mod_cast hk_in_GBI
                rcases hk_in_range' with ⟨l, hl_eq⟩
                have hj_lt_K : l.val < K := by
                  by_contra hj_ge
                  push_neg at hj_ge
                  have hKm1_lt_good : K - 1 < goodBlockCount S y := by
                    have : 1 ≤ K := hK_pos; omega
                  let Km1_fin : Fin (goodBlockCount S y) := ⟨K - 1, hKm1_lt_good⟩
                  have hKm1_lt_l : Km1_fin < l := by
                    show (K - 1) < l.val
                    have : 1 ≤ K := hK_pos; omega
                  have h_strict :=
                    (Finset.orderEmbOfFin (goodBlockIndices S y) rfl).strictMono hKm1_lt_l
                  have h_orderEmb_Km1 :
                      Finset.orderEmbOfFin (goodBlockIndices S y) rfl Km1_fin = kvec_last_val := by
                    have h_eq_firstK :
                        Finset.orderEmbOfFin (goodBlockIndices S y) rfl Km1_fin =
                        firstKGoodBlockIndices S y K (⟨K - 1, by omega⟩ : Fin K) := by
                      unfold firstKGoodBlockIndices
                      rw [dif_pos hKle]
                      rfl
                    rw [h_eq_firstK]
                    have h_extract_Km1 := extractKVec_val_of_le (hM_pos := hM_pos) hKle
                      (⟨K - 1, by omega⟩ : Fin K)
                    rw [hext] at h_extract_Km1
                    rw [hklv]
                    exact h_extract_Km1.symm
                  rw [h_orderEmb_Km1] at h_strict
                  have h_orderEmb_l_eq :
                      Finset.orderEmbOfFin (goodBlockIndices S y) rfl l = k := hl_eq
                  rw [h_orderEmb_l_eq] at h_strict
                  omega
                rw [hA_kvec_def, Finset.mem_image]
                refine ⟨⟨l.val, hj_lt_K⟩, Finset.mem_univ _, ?_⟩
                have h_extract_j := extractKVec_val_of_le (hM_pos := hM_pos) hKle
                  ⟨l.val, hj_lt_K⟩
                rw [hext] at h_extract_j
                rw [h_extract_j]
                unfold firstKGoodBlockIndices
                rw [dif_pos hKle]
                convert! hl_eq using 1
            · -- Backward.
              rintro ⟨hA_good, hB_bad⟩
              have hA_sub_GBI : A_kvec ⊆ goodBlockIndices S y := by
                intro k hk
                show k ∈ (Finset.range (compositeBlockCount y)).filter _
                rw [Finset.mem_filter]
                refine ⟨hA_sub_range hk, ?_⟩
                exact hA_good k hk
              have hKle : K ≤ goodBlockCount S y := by
                rw [goodBlockCount_eq_card_indices, ← hA_card]
                exact Finset.card_le_card hA_sub_GBI
              refine ⟨hKle, ?_⟩
              have hA_eq : ∀ k, k ∈ A_kvec ↔ k ∈ goodBlockIndices S y ∧ k ≤ kvec_last_val := by
                intro k
                constructor
                · intro hk
                  refine ⟨hA_sub_GBI hk, ?_⟩
                  rw [hA_kvec_def, Finset.mem_image] at hk
                  rcases hk with ⟨i, _, hi_eq⟩
                  rw [← hi_eq, hklv]
                  have hKm1_lt_K : K - 1 < K := by omega
                  let i_K_target : Fin K := ⟨K - 1, hKm1_lt_K⟩
                  have hi_le_target : i ≤ i_K_target := by
                    show i.val ≤ K - 1; omega
                  exact h_mono.monotone hi_le_target
                · rintro ⟨hk_GBI, hk_le⟩
                  by_contra hk_not_A
                  have hk_in_B : k ∈ B_kvec := by
                    rw [hB_kvec_def, Finset.mem_sdiff]
                    refine ⟨?_, hk_not_A⟩
                    rw [Finset.mem_range]; omega
                  apply hB_bad k hk_in_B
                  show (compositeBlock y k ∩ S).card = 1
                  exact (Finset.mem_filter.mp hk_GBI).2
              have hf_orderEmb : (fun i : Fin K => (kvec i).val) =
                  Finset.orderEmbOfFin A_kvec hA_card := by
                apply Finset.orderEmbOfFin_unique hA_card
                · intro i
                  rw [hA_kvec_def, Finset.mem_image]
                  exact ⟨i, Finset.mem_univ _, rfl⟩
                · exact h_mono
              funext i
              apply Fin.ext_iff.mpr
              show (extractKVec hM_pos S K i).val = (kvec i).val
              rw [extractKVec_val_of_le hKle]
              unfold firstKGoodBlockIndices
              rw [dif_pos hKle]
              set g_oeb : Fin K → ℕ := fun (j : Fin K) =>
                Finset.orderEmbOfFin (goodBlockIndices S y) (k := goodBlockCount S y) rfl
                  ⟨j.val, lt_of_lt_of_le j.isLt hKle⟩
              have hg_mono : StrictMono g_oeb := by
                intro a b hab
                show Finset.orderEmbOfFin _ rfl ⟨a.val, _⟩ <
                  Finset.orderEmbOfFin _ rfl ⟨b.val, _⟩
                apply (Finset.orderEmbOfFin _ rfl).strictMono
                exact hab
              have hg_in_A : ∀ j : Fin K, g_oeb j ∈ A_kvec := by
                intro j
                rw [hA_eq]
                refine ⟨Finset.orderEmbOfFin_mem _ _ _, ?_⟩
                by_contra h_gt
                push_neg at h_gt
                have h_filter_card_K : (Finset.univ.filter
                    (fun l : Fin (goodBlockCount S y) =>
                      Finset.orderEmbOfFin (goodBlockIndices S y) rfl l ≤ kvec_last_val)).card =
                    K := by
                  have h_image : (Finset.univ.filter
                      (fun l : Fin (goodBlockCount S y) =>
                        Finset.orderEmbOfFin (goodBlockIndices S y) rfl l ≤ kvec_last_val)).image
                        (Finset.orderEmbOfFin (goodBlockIndices S y) rfl) = A_kvec := by
                    let : DecidablePred (fun l : Fin (goodBlockCount S y) =>
                        Finset.orderEmbOfFin (goodBlockIndices S y) rfl l ≤ kvec_last_val) :=
                      fun _ => Classical.propDecidable _
                    apply Finset.ext
                    intro x
                    constructor
                    · intro hx
                      rcases Finset.mem_image.mp hx with ⟨l, hl, rfl⟩
                      exact (hA_eq _).mpr ⟨Finset.orderEmbOfFin_mem _ _ _,
                        ((@Finset.mem_filter _ (fun l : Fin (goodBlockCount S y) => Finset.orderEmbOfFin (goodBlockIndices S y) rfl l ≤ kvec_last_val) (fun _ => Classical.propDecidable _) _ _).mp hl).2⟩
                    · intro hx
                      obtain ⟨hx_GBI, hx_le⟩ := (hA_eq x).mp hx
                      have h_range := Finset.range_orderEmbOfFin (goodBlockIndices S y)
                        (k := goodBlockCount S y) rfl
                      have hx_range : x ∈ Set.range
                          (Finset.orderEmbOfFin (goodBlockIndices S y)
                            (k := goodBlockCount S y) rfl) := by
                        rw [h_range]
                        exact hx_GBI
                      obtain ⟨l, hl_eq⟩ := hx_range
                      exact Finset.mem_image.mpr ⟨l,
                        (@Finset.mem_filter _ (fun l : Fin (goodBlockCount S y) => Finset.orderEmbOfFin (goodBlockIndices S y) rfl l ≤ kvec_last_val) (fun _ => Classical.propDecidable _) _ _).mpr ⟨Finset.mem_univ _, hl_eq.symm ▸ hx_le⟩, hl_eq⟩
                  have h_card_image := Finset.card_image_of_injective
                    (Finset.univ.filter (fun l : Fin (goodBlockCount S y) =>
                      Finset.orderEmbOfFin (goodBlockIndices S y) rfl l ≤ kvec_last_val))
                    ((Finset.orderEmbOfFin (goodBlockIndices S y)
                      (k := goodBlockCount S y) rfl).injective)
                  calc (Finset.univ.filter (fun l : Fin (goodBlockCount S y) =>
                          Finset.orderEmbOfFin (goodBlockIndices S y) rfl l ≤
                            kvec_last_val)).card
                      = ((Finset.univ.filter (fun l : Fin (goodBlockCount S y) =>
                          Finset.orderEmbOfFin (goodBlockIndices S y) rfl l ≤
                            kvec_last_val)).image
                          (Finset.orderEmbOfFin (goodBlockIndices S y) rfl)).card :=
                        h_card_image.symm
                    _ = A_kvec.card := by rw [h_image]
                    _ = K := hA_card
                have h_filter_subset : (Finset.univ.filter
                    (fun l : Fin (goodBlockCount S y) =>
                      Finset.orderEmbOfFin (goodBlockIndices S y) rfl l ≤ kvec_last_val)) ⊆
                    Finset.univ.filter (fun l : Fin (goodBlockCount S y) => l.val < j.val) := by
                  intro l hl
                  rw [Finset.mem_filter] at hl ⊢
                  refine ⟨Finset.mem_univ _, ?_⟩
                  by_contra h_l_ge
                  push_neg at h_l_ge
                  have h_j_le_l :
                      (⟨j.val, lt_of_lt_of_le j.isLt hKle⟩ : Fin (goodBlockCount S y)) ≤ l := by
                    show j.val ≤ l.val; exact h_l_ge
                  have h_mono_le := (Finset.orderEmbOfFin (goodBlockIndices S y) rfl).monotone
                    h_j_le_l
                  have : g_oeb j ≤ kvec_last_val := h_mono_le.trans hl.2
                  omega
                have h_RHS_card_le : (Finset.univ.filter
                    (fun l : Fin (goodBlockCount S y) => l.val < j.val)).card ≤ j.val := by
                  let h_f : Fin j.val → Fin (goodBlockCount S y) := fun i =>
                    ⟨i.val, lt_of_lt_of_le i.isLt
                      (le_trans (le_of_lt j.isLt) hKle)⟩
                  have h_subset : Finset.univ.filter
                      (fun l : Fin (goodBlockCount S y) => l.val < j.val) ⊆
                      (Finset.univ : Finset (Fin j.val)).image h_f := by
                    intro l hl
                    rw [Finset.mem_filter] at hl
                    rw [Finset.mem_image]
                    refine ⟨⟨l.val, hl.2⟩, Finset.mem_univ _, ?_⟩
                    rfl
                  calc (Finset.univ.filter
                          (fun l : Fin (goodBlockCount S y) => l.val < j.val)).card
                      ≤ ((Finset.univ : Finset (Fin j.val)).image h_f).card :=
                        Finset.card_le_card h_subset
                    _ ≤ (Finset.univ : Finset (Fin j.val)).card := Finset.card_image_le
                    _ = j.val := by rw [Finset.card_univ]; exact Fintype.card_fin _
                have h_K_le_j : K ≤ j.val := by
                  have h2 := Finset.card_le_card h_filter_subset
                  omega
                exact absurd h_K_le_j (not_le.mpr j.isLt)
              have hg_eq : g_oeb = Finset.orderEmbOfFin A_kvec hA_card :=
                Finset.orderEmbOfFin_unique hA_card hg_in_A hg_mono
              show g_oeb i = (kvec i).val
              rw [hg_eq]
              exact (congrFun hf_orderEmb i).symm
          -- Helper: resvec at (kvec i).val equals (g i).val.
          have h_resvec_at_kvec : ∀ i : Fin K, resvec ((kvec i).val) = (g i : ZMod d).val := by
            intro i
            show resvec ((kvec i).val) = (g i : ZMod d).val
            have h_in : (kvec i).val ∈ A_kvec := hA_kvec_def ▸
              Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
            simp only [resvec, dif_pos h_in]
            generalize h_choose : Classical.choose
                (Finset.mem_image.mp (hA_kvec_def ▸ h_in)) = j
            have h_spec := Classical.choose_spec (Finset.mem_image.mp (hA_kvec_def ▸ h_in))
            rw [h_choose] at h_spec
            have h_val_eq : (kvec j).val = (kvec i).val := h_spec.2
            have h_eq : j = i := h_kvec_inj h_val_eq
            rw [h_eq]
          -- LHS predicate equivalence with blockEvents_with_residues form.
          have h_LHS_pred_eq : ∀ S : Finset ℕ, S ⊆ compositePrimeWindow 20 y →
              ((K ≤ goodBlockCount S y ∧ firstKResidueVector S y d K = g ∧
                extractKVec hM_pos S K = kvec) ↔
              ((∀ k ∈ A_kvec, ∃ q ∈ F k, F k ∩ S = ({q} : Finset ℕ) ∧
                  q % d = (resvec k) % d) ∧
              (∀ k ∈ B_kvec, (F k ∩ S).card ≠ 1))) := by
            intro S hS_sub
            constructor
            · -- Forward direction.
              rintro ⟨hKle, hres_eq, hext⟩
              have h_block := (h_pred_eq S hS_sub).mp ⟨hKle, hext⟩
              have hres_per := (firstKResidueVector_eq_iff_per_block
                (hM_pos := hM_pos) hKle hext).mp hres_eq
              refine ⟨?_, h_block.2⟩
              intro k hk_in_A
              -- Extract i with (kvec i).val = k, then substitute.
              rw [hA_kvec_def, Finset.mem_image] at hk_in_A
              rcases hk_in_A with ⟨i, _, rfl⟩
              -- Now k is replaced with (kvec i).val.
              have hkvec_in_A : (kvec i).val ∈ A_kvec :=
                hA_kvec_def ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
              have h_card_1 : (F (kvec i).val ∩ S).card = 1 := h_block.1 _ hkvec_in_A
              rcases Finset.card_eq_one.mp h_card_1 with ⟨q, hq_eq⟩
              have hq_in : q ∈ F (kvec i).val := by
                have h_q_in_inter : q ∈ F (kvec i).val ∩ S :=
                  hq_eq ▸ Finset.mem_singleton.mpr rfl
                exact (Finset.mem_inter.mp h_q_in_inter).1
              refine ⟨q, hq_in, hq_eq, ?_⟩
              -- Goal: q % d = resvec ((kvec i).val) % d.
              -- residueOfSelectedPrime S y d (kvec i).val = g i (from hres_per).
              -- The selected prime in F (kvec i).val with card 1 = q.  So (q : ZMod d) = g i.
              -- Hence q % d = (g i).val.  And resvec ((kvec i).val) = (g i).val.
              have hq_prime : q.Prime := compositeBlock_prime hq_in
              have h_q_in_S : q ∈ S := by
                have h_q_in_inter : q ∈ F (kvec i).val ∩ S :=
                  hq_eq ▸ Finset.mem_singleton.mpr rfl
                exact (Finset.mem_inter.mp h_q_in_inter).2
              have hy_pos_local : 0 < y := by linarith [_hy]
              -- Coprime q d (q > exp y > d).
              have hq_gt_exp : Real.exp y < (q : ℝ) :=
                compositeBlock_prime_gt_exp_y (le_of_lt hy_pos_local) hq_in
              have hexp_gt_y : y < Real.exp y := by
                have h := Real.add_one_lt_exp (x := y) (by linarith : y ≠ 0)
                linarith
              have hd_lt_q : (d : ℝ) < (q : ℝ) := by linarith [_hd_le_y]
              have hd_lt_q_nat : d < q := by exact_mod_cast hd_lt_q
              have hd_pos : 0 < d := by omega
              have hnot_dvd : ¬ q ∣ d :=
                fun hdvd => absurd (Nat.le_of_dvd hd_pos hdvd) (not_le.mpr hd_lt_q_nat)
              have hq_coprime : Nat.Coprime q d := (hq_prime.coprime_iff_not_dvd).mpr hnot_dvd
              -- selectedPrimeInBlock S y (kvec i).val = q (via membership in singleton).
              have h_sel_eq : selectedPrimeInBlock S y (kvec i).val = q := by
                have h_sel_in_inter : selectedPrimeInBlock S y (kvec i).val ∈
                    compositeBlock y (kvec i).val ∩ S :=
                  selectedPrimeInBlock_mem h_card_1
                rw [hq_eq] at h_sel_in_inter
                exact Finset.mem_singleton.mp h_sel_in_inter
              have hsel_coprime : Nat.Coprime (selectedPrimeInBlock S y (kvec i).val) d := by
                rw [h_sel_eq]; exact hq_coprime
              -- residueOfSelectedPrime = ZMod.unitOfCoprime selected hsel_coprime.
              -- Hence (g i : ZMod d) = (q : ZMod d) via coe_unitOfCoprime + h_sel_eq.
              have hres_at_i_eq : residueOfSelectedPrime S y d (kvec i).val =
                  ZMod.unitOfCoprime (selectedPrimeInBlock S y (kvec i).val) hsel_coprime := by
                unfold residueOfSelectedPrime
                rw [dif_pos ⟨h_card_1, hsel_coprime⟩]
              -- (g i : (ZMod d)ˣ) = ZMod.unitOfCoprime selected hsel_coprime.
              have hg_unit : g i = ZMod.unitOfCoprime (selectedPrimeInBlock S y (kvec i).val)
                  hsel_coprime := by
                rw [← hres_at_i_eq]; exact (hres_per i).symm
              -- (g i : ZMod d) = (selected : ZMod d) = (q : ZMod d).
              have hg_q : (g i : ZMod d) = (q : ZMod d) := by
                rw [hg_unit, ZMod.coe_unitOfCoprime, h_sel_eq]
              -- Convert to mod equality.
              have h_q_mod : q % d = (g i : ZMod d).val := by
                rw [hg_q, ZMod.val_natCast]
              rw [h_q_mod, h_resvec_at_kvec]
              -- Goal: (g i : ZMod d).val = (g i : ZMod d).val % d.
              exact (Nat.mod_eq_of_lt (ZMod.val_lt _)).symm
            · -- Backward direction.
              rintro ⟨hres, hbad⟩
              have h_A_card_1 : ∀ k ∈ A_kvec, (compositeBlock y k ∩ S).card = 1 := by
                intro k hk
                rcases hres k hk with ⟨q, _, h_eq, _⟩
                rw [h_eq]; simp
              have h_K_extract := (h_pred_eq S hS_sub).mpr ⟨h_A_card_1, hbad⟩
              refine ⟨h_K_extract.1, ?_, h_K_extract.2⟩
              rw [firstKResidueVector_eq_iff_per_block
                (hM_pos := hM_pos) h_K_extract.1 h_K_extract.2]
              intro i
              have hkvec_in_A : (kvec i).val ∈ A_kvec :=
                hA_kvec_def ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
              rcases hres (kvec i).val hkvec_in_A with ⟨q, hq_in, h_inter, h_res_q⟩
              -- q % d = resvec ((kvec i).val) % d = (g i : ZMod d).val % d.
              have h_resvec_kvec := h_resvec_at_kvec i
              -- Need: residueOfSelectedPrime S y d (kvec i).val = g i.
              have hcard1 : (compositeBlock y (kvec i).val ∩ S).card = 1 := by
                rw [h_inter]; simp
              -- selectedPrimeInBlock = q (via membership in singleton).
              have hsel_eq : selectedPrimeInBlock S y (kvec i).val = q := by
                have h_sel_in_inter : selectedPrimeInBlock S y (kvec i).val ∈
                    compositeBlock y (kvec i).val ∩ S :=
                  selectedPrimeInBlock_mem hcard1
                rw [h_inter] at h_sel_in_inter
                exact Finset.mem_singleton.mp h_sel_in_inter
              have hq_prime : q.Prime := compositeBlock_prime hq_in
              have hy_pos_local : 0 < y := by linarith [_hy]
              have hsel_coprime : Nat.Coprime (selectedPrimeInBlock S y (kvec i).val) d := by
                rw [hsel_eq]
                have hq_gt_exp : Real.exp y < (q : ℝ) :=
                  compositeBlock_prime_gt_exp_y (le_of_lt hy_pos_local) hq_in
                have hexp_gt_y : y < Real.exp y := by
                  have h := Real.add_one_lt_exp (x := y) (by linarith : y ≠ 0)
                  linarith
                have hd_lt_q : (d : ℝ) < (q : ℝ) := by linarith [_hd_le_y]
                have hd_lt_q_nat : d < q := by exact_mod_cast hd_lt_q
                have hd_pos : 0 < d := by omega
                have hnot_dvd : ¬ q ∣ d :=
                  fun hdvd => absurd (Nat.le_of_dvd hd_pos hdvd) (not_le.mpr hd_lt_q_nat)
                exact (hq_prime.coprime_iff_not_dvd).mpr hnot_dvd
              -- Have q % d = (g i : ZMod d).val (from h_res_q + h_resvec_kvec).
              have h_q_mod : q % d = (g i : ZMod d).val := by
                rw [h_res_q, h_resvec_kvec]
                have : ((g i : ZMod d).val) < d := ZMod.val_lt _
                exact Nat.mod_eq_of_lt this
              -- Now show residueOfSelectedPrime S y d (kvec i).val = g i.
              -- residueOfSelectedPrime = ZMod.unitOfCoprime selected hsel_coprime (under cond).
              have hres_eq_unit : residueOfSelectedPrime S y d (kvec i).val =
                  ZMod.unitOfCoprime (selectedPrimeInBlock S y (kvec i).val) hsel_coprime := by
                unfold residueOfSelectedPrime
                rw [dif_pos ⟨hcard1, hsel_coprime⟩]
              rw [hres_eq_unit]
              -- Goal: ZMod.unitOfCoprime selected hsel_coprime = g i.
              -- Show via Units.ext: (LHS : ZMod d) = (g i : ZMod d).
              apply Units.ext
              rw [ZMod.coe_unitOfCoprime]
              -- Goal: (selected : ZMod d) = (g i : ZMod d).
              rw [hsel_eq]
              -- Goal: (q : ZMod d) = (g i : ZMod d).  Use val equality.
              have h_val_eq : ((q : ZMod d)).val = ((g i : ZMod d)).val := by
                rw [ZMod.val_natCast, h_q_mod]
              exact ZMod.val_injective d h_val_eq
          -- Apply finitePrimeModelProb_congr + finitePrimeModelProb_blockEvents_with_residues.
          have h_LHS_pmodel :
              finitePrimeModelProb (compositePrimeWindow 20 y)
                (fun S => K ≤ goodBlockCount S y ∧
                  firstKResidueVector S y d K = g ∧ extractKVec hM_pos S K = kvec) =
              (∏ k ∈ A_kvec, blockGoodProbability (F k) *
                  blockConditionalResidueProbability (F k) d (resvec k)) *
              ∏ k ∈ B_kvec, (1 - blockGoodProbability (F k)) := by
            rw [finitePrimeModelProb_congr h_LHS_pred_eq]
            exact finitePrimeModelProb_blockEvents_with_residues (compositePrimeWindow 20 y)
              F A_kvec B_kvec d resvec hsub_AB hpair_AB hAB_disj hF_prime_AB
          -- Apply blockEvents (no residues) to RHS_first via predicate equivalence.
          have h_RHS_first_pmodel :
              finitePrimeModelProb (compositePrimeWindow 20 y)
                (fun S => K ≤ goodBlockCount S y ∧ extractKVec hM_pos S K = kvec) =
              (∏ k ∈ A_kvec, blockGoodProbability (F k)) *
              ∏ k ∈ B_kvec, (1 - blockGoodProbability (F k)) := by
            -- Use the outer h_pred_eq (defined earlier above h_LHS_pmodel).
            rw [finitePrimeModelProb_congr h_pred_eq]
            exact finitePrimeModelProb_blockEvents (compositePrimeWindow 20 y) F A_kvec B_kvec
              hsub_AB hpair_AB hAB_disj
          -- Connect ∏ over A_kvec to ∏ over Fin K via Finset.prod_image (kvec injective).
          have h_prod_AK : (∏ k ∈ A_kvec, blockConditionalResidueProbability (F k) d (resvec k)) =
              ∏ i : Fin K, blockConditionalResidueProbability (compositeBlock y (kvec i).val)
                d ((g i : ZMod d).val) := by
            rw [hA_kvec_def]
            rw [Finset.prod_image (fun i _ j _ h => h_kvec_inj h)]
            apply Finset.prod_congr rfl
            intro i _
            congr 1
            -- resvec ((kvec i).val) = (g i : ZMod d).val
            show resvec ((kvec i).val) = (g i : ZMod d).val
            simp only [resvec]
            have h_in : (kvec i).val ∈ A_kvec := by
              rw [hA_kvec_def]
              exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
            rw [dif_pos h_in]
            -- The Classical.choose returns SOME j with (kvec j).val = (kvec i).val.
            -- By injectivity, j = i.
            generalize h_choose : Classical.choose
                (Finset.mem_image.mp (hA_kvec_def ▸ h_in)) = j
            have h_spec := Classical.choose_spec
                (Finset.mem_image.mp (hA_kvec_def ▸ h_in))
            rw [h_choose] at h_spec
            have h_val_eq : (kvec j).val = (kvec i).val := h_spec.2
            have h_eq : j = i := h_kvec_inj h_val_eq
            rw [h_eq]
          -- Final: divide.
          rw [h_LHS_pmodel, h_RHS_first_pmodel, ← h_prod_AK]
          rw [Finset.prod_mul_distrib]
          ring
        · -- Non-monotone case: pmodel(P_LHS) = 0 = pmodel(P_RHS_first).  0 = 0 · anything.
          have h_extract_impossible : ∀ S : Finset ℕ,
              ¬ (K ≤ goodBlockCount S y ∧ extractKVec hM_pos S K = kvec) := by
            intro S ⟨hK, hext⟩
            apply h_mono
            intro i j hij
            show (kvec i).val < (kvec j).val
            have h_extract_i : (extractKVec hM_pos S K i).val = firstKGoodBlockIndices S y K i :=
              extractKVec_val_of_le hK i
            have h_extract_j : (extractKVec hM_pos S K j).val = firstKGoodBlockIndices S y K j :=
              extractKVec_val_of_le hK j
            have hi_eq : (kvec i).val = firstKGoodBlockIndices S y K i := by
              rw [← h_extract_i, hext]
            have hj_eq : (kvec j).val = firstKGoodBlockIndices S y K j := by
              rw [← h_extract_j, hext]
            rw [hi_eq, hj_eq]
            -- firstKGoodBlockIndices is strictly monotone via orderEmbOfFin.
            unfold firstKGoodBlockIndices
            rw [dif_pos hK, dif_pos hK]
            apply (Finset.orderEmbOfFin _ rfl).strictMono
            exact Fin.mk_lt_mk.mpr hij
          -- LHS pmodel = 0 (no S satisfies the predicate which subsumes extractKVec = kvec).
          have h_LHS_zero : finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧
                firstKResidueVector S y d K = g ∧ extractKVec hM_pos S K = kvec) = 0 := by
            unfold finitePrimeModelProb
            apply Finset.sum_eq_zero
            intro S hS
            simp only [Finset.mem_filter] at hS
            exact absurd ⟨hS.2.1, hS.2.2.2⟩ (h_extract_impossible S)
          -- RHS_first pmodel = 0.
          have h_RHS_first_zero : finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧ extractKVec hM_pos S K = kvec) = 0 := by
            unfold finitePrimeModelProb
            apply Finset.sum_eq_zero
            intro S hS
            simp only [Finset.mem_filter] at hS
            exact absurd hS.2 (h_extract_impossible S)
          rw [h_LHS_zero, h_RHS_first_zero]
          ring
      -- (Step 1) Partition by extractKVec via finitePrimeModelProb_sum_partition.
      have h_step1_partition :
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧ firstKResidueVector S y d K = g) =
          ∑ kvec : Fin K → Fin (compositeBlockCount y),
            finitePrimeModelProb (compositePrimeWindow 20 y)
                (fun S => K ≤ goodBlockCount S y ∧
                  firstKResidueVector S y d K = g ∧ extractKVec hM_pos S K = kvec) := by
        rw [(finitePrimeModelProb_sum_partition
          (P := fun S => K ≤ goodBlockCount S y ∧ firstKResidueVector S y d K = g)
          (extract := fun S => extractKVec hM_pos S K)).symm]
        apply Finset.sum_congr rfl
        intro kvec _
        unfold finitePrimeModelProb
        congr 1
        ext S
        simp only [Finset.mem_filter, and_assoc]
      -- (Step 3) Combine: μ(g) = ∑_kvec pdist(kvec) · ∏ p.
      -- pdist(kvec) := pmodel(... ∧ ∀ i, firstKGood... = (kvec i).val) / pmodel_K_good
      -- Need to relate pdist's predicate to "extractKVec = kvec" for K ≤ #good.
      show finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => K ≤ goodBlockCount S y ∧ firstKResidueVector S y d K = g) /
          pmodel_K_good = _
      rw [h_step1_partition]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro kvec _
      rw [h_step2_factor kvec]
      -- Goal: pmodel(... ∧ extractKVec = kvec) * ∏ p / pmodel_K_good = pdist kvec * ∏ p
      -- pdist kvec uses predicate "∀ i, firstKGood... = (kvec i).val".  Show equivalence
      -- with "extractKVec = kvec" (under K ≤ #good).
      have h_pi_pred :
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧ extractKVec hM_pos S K = kvec) =
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧
                ∀ i, firstKGoodBlockIndices S y K i = (kvec i).val) := by
        unfold finitePrimeModelProb
        congr 1
        ext S
        simp only [Finset.mem_filter, and_congr_right_iff]
        intro _ hKle
        constructor
        · intro hext i
          have h_extract_i := congr_fun hext i
          rw [← h_extract_i, extractKVec_val_of_le hKle]
        · intro hfk
          funext i
          apply Fin.ext
          rw [extractKVec_val_of_le hKle]
          exact hfk i
      rw [h_pi_pred]
      ring

/-- Paper §6.2 line 1741-1753: μ is `K · ε_y`-close to uniform on `(Fin K → G)`,
where `G = (ZMod d)ˣ`.  Follows from step5 (per-block ε_y-uniformity) + independence
of disjoint blocks (Remark `block-uniformity`).

**Hypothesis form (paper-faithful):** `hstep5_l1` is the L1 (= 2·TV) bound on the
per-block conditional residue distribution, paper line 1741's "TV-close to uniform".
This corresponds to paper's `ε_y = O(y^{-1/2})` TV bound, NOT the weaker pointwise
bound that earlier code extracted.  The L1 bound is needed to apply `prod_tv_le_sum_tv`
correctly (which requires per-coord L1 bound, not pointwise). -/
private lemma conditionalResidueMeasure_near_uniform {y : ℝ} {d K : ℕ} [NeZero d]
    (_hy : 2 ≤ y) (_hd_ge_2 : 2 ≤ d) (_hd_le_y : (d : ℝ) ≤ y)
    (hsub_block : ∀ k : ℕ, k < compositeBlockCount y →
      compositeBlock y k ⊆ compositePrimeWindow 20 y)
    (_hpos : finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y) ≠ 0)
    (C_step5 : ℝ) (_hC_step5_pos : 0 < C_step5)
    (hstep5_l1 :
      ∀ k : ℕ, k < compositeBlockCount y →
        (∑ a : (ZMod d)ˣ,
            |blockConditionalResidueProbability (compositeBlock y k) d ((a : ZMod d).val) -
                (1 : ℝ) / (d.totient : ℝ)|) ≤ C_step5 * y ^ (-(1 : ℝ) / 2))
    (hcondprob_nn :
      ∀ k : ℕ, k < compositeBlockCount y → ∀ a : (ZMod d)ˣ,
        0 ≤ blockConditionalResidueProbability (compositeBlock y k) d ((a : ZMod d).val))
    (hcondprob_sum :
      ∀ k : ℕ, k < compositeBlockCount y →
        (∑ a : (ZMod d)ˣ,
          blockConditionalResidueProbability (compositeBlock y k) d ((a : ZMod d).val)) = 1) :
    (∑ g : Fin K → (ZMod d)ˣ,
        |conditionalResidueMeasure y d K g - 1 / ((d.totient : ℝ) ^ K)|) ≤
      (K : ℝ) * (C_step5 * y ^ (-(1 : ℝ) / 2)) := by
  -- Paper §6.2 Step 5 (lines 1719-1753).  Three-step proof:
  -- (a) **Conditional independence** (paper line 1732):
  --     For any realized index vector (k_1, ..., k_K), the joint conditional
  --     P(g_1, ..., g_K | first K good = (k_1, ..., k_K)) factors as
  --     ∏_i P(g_i | block k_i good) (since blocks are disjoint).
  -- (b) **Per-block ε_y-uniformity** (paper lines 1741-1742, given by `hstep5`):
  --     For each block k_i, |P(g_i | block k_i good) - 1/N| ≤ ε_y where ε_y = C_step5 · y^{-1/2}.
  -- (c) **TV triangle inequality** (paper line 1748: "ε_y-close to uniform"):
  --     If marginals are ε_y-close to uniform, then product is K · ε_y-close to product-uniform.
  --     Standard probability fact: TV(∏ μ_i, ∏ U_i) ≤ ∑ TV(μ_i, U_i).
  -- (d) **Mixture preservation**: μ is a mixture over realized vectors, each component
  --     ε_y-close to product-uniform.  TV is convex, so mixture's TV ≤ avg ε_y = K · ε_y.
  --
  -- Implementation strategy:
  -- - Sub-step (a): build product measure `productMeasure` from per-block `blockConditionalResidueProbability`,
  --   show conditionalResidueMeasure equals an average of product measures over realized vectors.
  --   ~80 LOC of pmodel sum manipulation.
  -- - Sub-step (b)-(d): triangle/convexity argument.  ~60 LOC.
  --
  -- TWO STRUCTURAL CLAIMS:
  -- (P1) Mixture decomposition (paper line 1732 + 1722-1735):
  --      μ(g) = ∑_kvec pdist(kvec) · ∏_i blockConditionalResidueProbability (compositeBlock y (kvec i)) d (g i).val
  --      where pdist(kvec) = pmodel(firstKGoodBlockIndices = kvec | ≥K good).
  -- (P2) Triangle inequality + prod_tv_le_sum_tv:
  --      For each kvec, ∑_g |∏_i p_i(g_i) - 1/N^K| ≤ K · ε_y by prod_tv_le_sum_tv.
  --      Then mixture preservation: ∑_g |μ(g) - U(g)| ≤ ∑_kvec pdist(kvec) · K·ε_y = K·ε_y · ∑_kvec pdist(kvec) = K·ε_y.
  --
  -- PROOF SKELETON:
  -- Set ε_y := C_step5 * y^(-1/2).
  set ε_y : ℝ := C_step5 * y ^ (-(1 : ℝ) / 2) with hε_y_def
  -- (Step 1) Get the mixture decomposition (paper line 1722-1735):
  --   μ(g) = ∑_kvec pdist(kvec) · ∏_i p_{kvec_i}(g_i.val).
  rcases conditionalResidueMeasure_mixture_identity _hy _hd_ge_2 _hd_le_y hsub_block _hpos
    with ⟨pdist, hπ_nn, hπ_sum, hμ_eq⟩
  -- (Step 2) For each kvec, the fiber sum is bounded by K · ε_y (paper line 1748-1750
  -- applied per kvec, using prod_tv_le_sum_tv on the product fiber).
  have htotient_pos : 0 < (d.totient : ℝ) := by
    have hd_pos : 0 < d := by omega
    have : 0 < d.totient := Nat.totient_pos.mpr hd_pos
    exact_mod_cast this
  have htotient_ne : (d.totient : ℝ) ≠ 0 := htotient_pos.ne'
  have hu_sum_units : (∑ _g : (ZMod d)ˣ, (1 : ℝ) / (d.totient : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient, nsmul_eq_mul,
      mul_one_div]
    exact div_self htotient_ne
  have h_fiber_bound : ∀ kvec : Fin K → Fin (compositeBlockCount y),
      (∑ g : Fin K → (ZMod d)ˣ,
         |(∏ i : Fin K,
             blockConditionalResidueProbability
               (compositeBlock y (kvec i).val) d ((g i : ZMod d).val)) -
           (1 : ℝ) / ((d.totient : ℝ) ^ K)|) ≤ K * ε_y := by
    intro kvec
    -- Apply prod_tv_le_sum_tv with f, u, ε set up.
    have h := prod_tv_le_sum_tv
      (f := fun (i : Fin K) (g : (ZMod d)ˣ) =>
        blockConditionalResidueProbability (compositeBlock y (kvec i).val) d ((g : ZMod d).val))
      (u := fun (_ : (ZMod d)ˣ) => (1 : ℝ) / (d.totient : ℝ))
      (hu_nn := fun _ => by positivity)
      hu_sum_units
      (hf_nn := fun i g => hcondprob_nn (kvec i).val (kvec i).isLt g)
      (hf_sum := fun i => hcondprob_sum (kvec i).val (kvec i).isLt)
      ε_y
      (h_tv := fun i => hstep5_l1 (kvec i).val (kvec i).isLt)
    -- The conclusion has ∏_i (1/N) = 1/N^K.  Convert.
    have h_prod_u_eq : (∏ _i : Fin K, (1 : ℝ) / (d.totient : ℝ)) =
        (1 : ℝ) / ((d.totient : ℝ) ^ K) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow, one_pow]
    have h_lhs_eq : (∑ gvec : Fin K → (ZMod d)ˣ,
        |(∏ i : Fin K, blockConditionalResidueProbability
            (compositeBlock y (kvec i).val) d ((gvec i : ZMod d).val)) -
          (1 : ℝ) / ((d.totient : ℝ) ^ K)|) =
        (∑ gvec : Fin K → (ZMod d)ˣ,
          |(∏ i : Fin K, blockConditionalResidueProbability
              (compositeBlock y (kvec i).val) d ((gvec i : ZMod d).val)) -
            (∏ _i : Fin K, (1 : ℝ) / (d.totient : ℝ))|) := by
      apply Finset.sum_congr rfl
      intro gvec _
      rw [h_prod_u_eq]
    rw [h_lhs_eq]
    exact h
  -- (Step 3) Apply mixture identity + triangle inequality + Fubini.
  -- For each g: μ(g) - 1/N^K = ∑_kvec pdist · ∏ p - ∑_kvec pdist · 1/N^K  (since ∑ pdist = 1)
  --                           = ∑_kvec pdist · (∏ p - 1/N^K)
  -- |μ(g) - 1/N^K| ≤ ∑_kvec pdist · |∏ p - 1/N^K|.
  -- Sum over g + Fubini: ∑_g |μ - 1/N^K| ≤ ∑_kvec pdist · ∑_g |∏ p - 1/N^K|.
  have h_pointwise : ∀ g : Fin K → (ZMod d)ˣ,
      |conditionalResidueMeasure y d K g - 1 / ((d.totient : ℝ) ^ K)| ≤
        ∑ kvec : Fin K → Fin (compositeBlockCount y), pdist kvec *
          |(∏ i : Fin K,
              blockConditionalResidueProbability
                (compositeBlock y (kvec i).val) d ((g i : ZMod d).val)) -
            (1 : ℝ) / ((d.totient : ℝ) ^ K)| := by
    intro g
    set p_term : (Fin K → Fin (compositeBlockCount y)) → ℝ := fun kvec =>
      ∏ i : Fin K,
        blockConditionalResidueProbability
          (compositeBlock y (kvec i).val) d ((g i : ZMod d).val)
    set U : ℝ := (1 : ℝ) / ((d.totient : ℝ) ^ K)
    -- Rewrite μ(g) using the mixture identity:
    rw [hμ_eq g]
    -- Now the LHS is |∑ kvec, pdist · p_term - U|.  Use ∑ pdist = 1 to rewrite U as ∑ pdist · U.
    have h_U_eq : U = ∑ kvec : Fin K → Fin (compositeBlockCount y), pdist kvec * U := by
      rw [← Finset.sum_mul, hπ_sum, one_mul]
    calc |(∑ kvec, pdist kvec * p_term kvec) - U|
        = |(∑ kvec, pdist kvec * p_term kvec) - ∑ kvec, pdist kvec * U| := by rw [← h_U_eq]
      _ = |∑ kvec, (pdist kvec * p_term kvec - pdist kvec * U)| := by rw [Finset.sum_sub_distrib]
      _ = |∑ kvec, pdist kvec * (p_term kvec - U)| := by
            congr 1; refine Finset.sum_congr rfl (fun kvec _ => ?_); ring
      _ ≤ ∑ kvec, |pdist kvec * (p_term kvec - U)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ kvec, pdist kvec * |p_term kvec - U| := by
            refine Finset.sum_congr rfl (fun kvec _ => ?_)
            rw [abs_mul, abs_of_nonneg (hπ_nn kvec)]
  -- (Step 4) Sum over g, swap sums, apply h_fiber_bound, use ∑ pdist = 1.
  calc (∑ g : Fin K → (ZMod d)ˣ, |conditionalResidueMeasure y d K g - 1 / ((d.totient : ℝ) ^ K)|)
      ≤ ∑ g : Fin K → (ZMod d)ˣ,
          ∑ kvec : Fin K → Fin (compositeBlockCount y), pdist kvec *
            |(∏ i : Fin K,
                blockConditionalResidueProbability
                  (compositeBlock y (kvec i).val) d ((g i : ZMod d).val)) -
              (1 : ℝ) / ((d.totient : ℝ) ^ K)| :=
        Finset.sum_le_sum (fun g _ => h_pointwise g)
    _ = ∑ kvec : Fin K → Fin (compositeBlockCount y), pdist kvec *
          (∑ g : Fin K → (ZMod d)ˣ,
            |(∏ i : Fin K,
                blockConditionalResidueProbability
                  (compositeBlock y (kvec i).val) d ((g i : ZMod d).val)) -
              (1 : ℝ) / ((d.totient : ℝ) ^ K)|) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun kvec _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ kvec : Fin K → Fin (compositeBlockCount y), pdist kvec * (K * ε_y) :=
        Finset.sum_le_sum (fun kvec _ =>
          mul_le_mul_of_nonneg_left (h_fiber_bound kvec) (hπ_nn kvec))
    _ = (K * ε_y) * ∑ kvec : Fin K → Fin (compositeBlockCount y), pdist kvec := by
        rw [← Finset.sum_mul, mul_comm]
    _ = (K * ε_y) * 1 := by rw [hπ_sum]
    _ = (K : ℝ) * (C_step5 * y ^ (-(1 : ℝ) / 2)) := by rw [mul_one, hε_y_def]

private lemma sum_filter_pattern_eq_sum_fibers {α ι : Type*} [DecidableEq α]
    [DecidableEq ι] (U : Finset α) (s : Finset ι) (E : ι → α → Prop)
    [DecidableRel E] (w : α → ℝ) (K : ℕ) :
    (∑ a ∈ U.filter (fun a => ((s.filter (fun i => E i a)).card < K)), w a) =
      ∑ T ∈ s.powerset.filter (fun T => T.card < K),
        ∑ a ∈ U.filter (fun a => s.filter (fun i => E i a) = T), w a := by
  classical
  let pattern : α → Finset ι := fun a => s.filter (fun i => E i a)
  let pats : Finset (Finset ι) := s.powerset.filter (fun T => T.card < K)
  let fiber : Finset ι → Finset α := fun T => U.filter (fun a => pattern a = T)
  have htail_eq : U.filter (fun a => (pattern a).card < K) = pats.biUnion fiber := by
    ext a
    constructor
    · intro ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_biUnion]
      refine ⟨pattern a, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ha.2⟩
      · rw [Finset.mem_filter]
        exact ⟨ha.1, rfl⟩
    · intro ha
      rw [Finset.mem_biUnion] at ha
      rcases ha with ⟨T, hTpats, haT⟩
      rw [Finset.mem_filter] at hTpats haT ⊢
      exact ⟨haT.1, by simpa [pattern] using congrArg Finset.card haT.2 ▸ hTpats.2⟩
  have hdisj : (pats : Set (Finset ι)).PairwiseDisjoint fiber := by
    intro A _hA B _hB hAB
    change Disjoint (fiber A) (fiber B)
    rw [Finset.disjoint_left]
    intro a haA haB
    rw [Finset.mem_filter] at haA haB
    exact hAB (haA.2.symm.trans haB.2)
  calc
    (∑ a ∈ U.filter (fun a => ((s.filter (fun i => E i a)).card < K)), w a)
        = ∑ a ∈ U.filter (fun a => (pattern a).card < K), w a := by rfl
    _ = ∑ a ∈ pats.biUnion fiber, w a := by rw [htail_eq]
    _ = ∑ T ∈ pats, ∑ a ∈ fiber T, w a := by
      rw [Finset.sum_biUnion hdisj]
    _ =
      ∑ T ∈ s.powerset.filter (fun T => T.card < K),
        ∑ a ∈ U.filter (fun a => s.filter (fun i => E i a) = T), w a := by rfl

private lemma filter_eq_iff_forall_and_forall_sdiff {ι α : Type*} [DecidableEq ι]
    (s T : Finset ι) (E : ι → α → Prop) [DecidableRel E] (a : α) (hT : T ⊆ s) :
    s.filter (fun i => E i a) = T ↔
      (∀ i ∈ T, E i a) ∧ ∀ i ∈ s \ T, ¬ E i a := by
  classical
  constructor
  · intro h
    constructor
    · intro i hiT
      have hi_filter : i ∈ s.filter (fun j => E j a) := by simpa [h] using hiT
      exact (Finset.mem_filter.mp hi_filter).2
    · intro i hi hEi
      have his : i ∈ s := (Finset.mem_sdiff.mp hi).1
      have hiT : i ∉ T := (Finset.mem_sdiff.mp hi).2
      have hi_filter : i ∈ s.filter (fun j => E j a) :=
        Finset.mem_filter.mpr ⟨his, hEi⟩
      exact hiT (by simpa [h] using hi_filter)
  · rintro ⟨hgood, hbad⟩
    ext i
    constructor
    · intro hi
      rcases Finset.mem_filter.mp hi with ⟨his, hEi⟩
      by_contra hiT
      exact hbad i (Finset.mem_sdiff.mpr ⟨his, hiT⟩) hEi
    · intro hiT
      exact Finset.mem_filter.mpr ⟨hT hiT, hgood i hiT⟩

private lemma bernoulli_lower_tail_chernoff_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1)
    {K : ℕ} {EW : ℝ} (hEW : EW = ∑ i ∈ s, p i)
    (hK : (K : ℝ) ≤ (2 / 3 : ℝ) * EW) :
    (∑ T ∈ s.powerset.filter (fun T => T.card < K),
        (∏ i ∈ T, p i) * ∏ i ∈ s \ T, (1 - p i)) ≤ Real.exp (-EW / 18) := by
  classical
  let t : ℝ := (1 / 3 : ℝ)
  let a : ℝ := Real.exp (-t)
  let w : Finset ι → ℝ := fun T => (∏ i ∈ T, p i) * ∏ i ∈ s \ T, (1 - p i)
  have ht_pos : 0 < t := by norm_num [t]
  have ha_pos : 0 < a := by positivity
  have ha_nonneg : 0 ≤ a := ha_pos.le
  have hw_nonneg : ∀ T ∈ s.powerset, 0 ≤ w T := by
    intro T hT
    have hsub : T ⊆ s := Finset.mem_powerset.mp hT
    dsimp [w]
    exact mul_nonneg
      (Finset.prod_nonneg (fun i hi => hp0 i (hsub hi)))
      (Finset.prod_nonneg (fun i hi => by
        have his : i ∈ s := (Finset.mem_sdiff.mp hi).1
        linarith [hp1 i his]))
  have ha_le : a ≤ (18 / 25 : ℝ) := by
    have hquad : (1 : ℝ) + t + t ^ 2 / 2 ≤ Real.exp t :=
      Real.quadratic_le_exp_of_nonneg (by positivity)
    have hval : (25 / 18 : ℝ) ≤ Real.exp t := by
      norm_num [t] at hquad ⊢
      exact hquad
    have h : (Real.exp t)⁻¹ ≤ ((25 / 18 : ℝ))⁻¹ :=
      inv_anti₀ (by norm_num : (0 : ℝ) < 25 / 18) hval
    simpa [a, Real.exp_neg] using h
  have hfactor_nonneg : ∀ i ∈ s, 0 ≤ (1 - p i) + p i * a := by
    intro i hi
    have hp0i := hp0 i hi
    have hp1i := hp1 i hi
    nlinarith [mul_nonneg hp0i ha_nonneg]
  have hfactor_le : ∀ i ∈ s, (1 - p i) + p i * a ≤
      Real.exp (-(7 / 25 : ℝ) * p i) := by
    intro i hi
    have hpa : p i * a ≤ p i * (18 / 25 : ℝ) :=
      mul_le_mul_of_nonneg_left ha_le (hp0 i hi)
    calc
      (1 - p i) + p i * a ≤ (1 - p i) + p i * (18 / 25 : ℝ) := by linarith
      _ = 1 + (-(7 / 25 : ℝ) * p i) := by ring
      _ = (-(7 / 25 : ℝ) * p i) + 1 := by ring
      _ ≤ Real.exp (-(7 / 25 : ℝ) * p i) := Real.add_one_le_exp _
  have hgen_le :
      (∑ T ∈ s.powerset, (a ^ T.card) * w T) ≤
        Real.exp (-(7 / 25 : ℝ) * EW) := by
    have hsum_eq : (∑ T ∈ s.powerset, (a ^ T.card) * w T) =
        ∏ i ∈ s, ((p i * a) + (1 - p i)) := by
      dsimp [w]
      rw [Finset.prod_add]
      apply Finset.sum_congr rfl
      intro T _hT
      have hprod_mul : (∏ i ∈ T, p i * a) = (∏ i ∈ T, p i) * a ^ T.card := by
        rw [Finset.prod_mul_distrib]
        simp [Finset.prod_const]
      rw [hprod_mul]
      ring
    rw [hsum_eq]
    calc
      ∏ i ∈ s, (p i * a + (1 - p i)) = ∏ i ∈ s, ((1 - p i) + p i * a) := by
        simp_rw [add_comm (p _ * a)]
      _ ≤ ∏ i ∈ s, Real.exp (-(7 / 25 : ℝ) * p i) := by
        exact Finset.prod_le_prod hfactor_nonneg hfactor_le
      _ = Real.exp (-(7 / 25 : ℝ) * EW) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.mul_sum]
        rw [hEW]
  have htail_le_gen :
      (∑ T ∈ s.powerset.filter (fun T => T.card < K), w T) ≤
        Real.exp ((1 / 3 : ℝ) * (K : ℝ)) *
          (∑ T ∈ s.powerset, (a ^ T.card) * w T) := by
    calc
      (∑ T ∈ s.powerset.filter (fun T => T.card < K), w T) ≤
          ∑ T ∈ s.powerset.filter (fun T => T.card < K),
            Real.exp ((1 / 3 : ℝ) * (K : ℝ)) * ((a ^ T.card) * w T) := by
        apply Finset.sum_le_sum
        intro T hT
        have hTpowerset : T ∈ s.powerset := (Finset.mem_filter.mp hT).1
        have hTcard_lt : T.card < K := (Finset.mem_filter.mp hT).2
        have hTcard_le : T.card ≤ K := Nat.le_of_lt hTcard_lt
        have hscale : 1 ≤ Real.exp (t * (K : ℝ)) * a ^ T.card := by
          dsimp [a]
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          apply Real.one_le_exp
          have hcard : (T.card : ℝ) ≤ K := by exact_mod_cast hTcard_le
          nlinarith
        have hwT : 0 ≤ w T := hw_nonneg T hTpowerset
        calc
          w T ≤ (Real.exp (t * (K : ℝ)) * a ^ T.card) * w T :=
            le_mul_of_one_le_left hwT hscale
          _ = Real.exp ((1 / 3 : ℝ) * (K : ℝ)) * (a ^ T.card * w T) := by
            dsimp [t]
            ring
      _ = Real.exp ((1 / 3 : ℝ) * (K : ℝ)) *
            (∑ T ∈ s.powerset.filter (fun T => T.card < K), (a ^ T.card) * w T) := by
        rw [Finset.mul_sum]
      _ ≤ Real.exp ((1 / 3 : ℝ) * (K : ℝ)) *
            (∑ T ∈ s.powerset, (a ^ T.card) * w T) := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro T hT
            exact (Finset.mem_filter.mp hT).1
          · intro T hTpowerset _hTnot
            exact mul_nonneg (pow_nonneg ha_nonneg _) (hw_nonneg T hTpowerset)
        · positivity
  calc
    (∑ T ∈ s.powerset.filter (fun T => T.card < K),
        (∏ i ∈ T, p i) * ∏ i ∈ s \ T, (1 - p i)) =
        ∑ T ∈ s.powerset.filter (fun T => T.card < K), w T := by rfl
    _ ≤ Real.exp ((1 / 3 : ℝ) * (K : ℝ)) *
          (∑ T ∈ s.powerset, (a ^ T.card) * w T) := htail_le_gen
    _ ≤ Real.exp ((1 / 3 : ℝ) * (K : ℝ)) * Real.exp (-(7 / 25 : ℝ) * EW) := by
      exact mul_le_mul_of_nonneg_left hgen_le (by positivity)
    _ = Real.exp ((1 / 3 : ℝ) * (K : ℝ) + (-(7 / 25 : ℝ) * EW)) := by
      rw [Real.exp_add]
    _ ≤ Real.exp (-EW / 18) := by
      apply Real.exp_le_exp.mpr
      have hK' : (1 / 3 : ℝ) * (K : ℝ) ≤ (2 / 9 : ℝ) * EW := by nlinarith
      calc
        (1 / 3 : ℝ) * (K : ℝ) + (-(7 / 25 : ℝ) * EW) ≤
            (2 / 9 : ℝ) * EW + (-(7 / 25 : ℝ) * EW) := by linarith
        _ = -(13 / 225 : ℝ) * EW := by ring
        _ ≤ -EW / 18 := by
          have hEW_nonneg : 0 ≤ EW := by
            rw [hEW]
            exact Finset.sum_nonneg (fun i hi => hp0 i hi)
          nlinarith

private lemma finitePrimeModelProb_goodBlockCount_lt_eq_bernoulli_sum {y : ℝ}
    (hind_y :
      let M := compositeBlockCount y
      ∀ A B : Finset ℕ,
        A ⊆ Finset.range M →
        B ⊆ Finset.range M →
        Disjoint A B →
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S =>
                (∀ k ∈ A, (compositeBlock y k ∩ S).card = 1) ∧
                  ∀ k ∈ B, (compositeBlock y k ∩ S).card ≠ 1) =
            (∏ k ∈ A, blockGoodProbability (compositeBlock y k)) *
              ∏ k ∈ B, (1 - blockGoodProbability (compositeBlock y k))) :
    let M := compositeBlockCount y
    let s := Finset.range M
    finitePrimeModelProb (compositePrimeWindow 20 y)
        (fun S => goodBlockCount S y < compositeGoodBlockThreshold y) =
      ∑ T ∈ s.powerset.filter (fun T => T.card < compositeGoodBlockThreshold y),
        (∏ k ∈ T, blockGoodProbability (compositeBlock y k)) *
          ∏ k ∈ s \ T, (1 - blockGoodProbability (compositeBlock y k)) := by
  classical
  dsimp [finitePrimeModelProb, goodBlockCount]
  trans
    ∑ T ∈ (Finset.range (compositeBlockCount y)).powerset.filter
        (fun T => T.card < compositeGoodBlockThreshold y),
      ∑ S ∈ (compositePrimeWindow 20 y).powerset.filter
          (fun S =>
            (Finset.range (compositeBlockCount y)).filter
                (fun k => (compositeBlock y k ∩ S).card = 1) = T),
        selectionWeight (compositePrimeWindow 20 y) S
  · convert
      (sum_filter_pattern_eq_sum_fibers
        ((compositePrimeWindow 20 y).powerset)
        (Finset.range (compositeBlockCount y))
        (fun k S => (compositeBlock y k ∩ S).card = 1)
        (selectionWeight (compositePrimeWindow 20 y))
        (compositeGoodBlockThreshold y)) using 1
    · apply Finset.sum_congr
      · ext S
        simp only [Finset.mem_filter]
      · intro S _hS
        rfl
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.mem_filter] at hT
  have hTsub : T ⊆ Finset.range (compositeBlockCount y) := Finset.mem_powerset.mp hT.1
  have hsdiffsub : Finset.range (compositeBlockCount y) \ T ⊆
      Finset.range (compositeBlockCount y) :=
    Finset.sdiff_subset
  have hdisj : Disjoint T (Finset.range (compositeBlockCount y) \ T) :=
    Finset.disjoint_sdiff
  have hprob := hind_y T (Finset.range (compositeBlockCount y) \ T) hTsub hsdiffsub hdisj
  have hpred :
      (fun S : Finset ℕ =>
          (Finset.range (compositeBlockCount y)).filter
              (fun i => (compositeBlock y i ∩ S).card = 1) = T) =
        (fun S =>
          (∀ k ∈ T, (compositeBlock y k ∩ S).card = 1) ∧
            ∀ k ∈ Finset.range (compositeBlockCount y) \ T,
              (compositeBlock y k ∩ S).card ≠ 1) := by
    funext S
    exact propext
      (filter_eq_iff_forall_and_forall_sdiff
        (Finset.range (compositeBlockCount y)) T
        (fun k S => (compositeBlock y k ∩ S).card = 1) S hTsub)
  simpa [finitePrimeModelProb, hpred] using hprob

/-- Step 4 Chernoff bridge: independence plus the expectation lower bound imply the
polynomial lower-tail estimate for having fewer than `K` good blocks. -/
private lemma step4_chernoff_combined
    (_hind :
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          let M := compositeBlockCount y
          ∀ A B : Finset ℕ,
            A ⊆ Finset.range M →
            B ⊆ Finset.range M →
            Disjoint A B →
              finitePrimeModelProb (compositePrimeWindow 20 y)
                  (fun S =>
                    (∀ k ∈ A, (compositeBlock y k ∩ S).card = 1) ∧
                      ∀ k ∈ B, (compositeBlock y k ∩ S).card ≠ 1) =
                (∏ k ∈ A, blockGoodProbability (compositeBlock y k)) *
                  ∏ k ∈ B, (1 - blockGoodProbability (compositeBlock y k)))
    (_hexp :
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          let M := compositeBlockCount y
          let EW := ∑ k ∈ Finset.range M, blockGoodProbability (compositeBlock y k)
          (compositeGoodBlockThreshold y : ℝ) ≤ (2 / 3 : ℝ) * EW ∧
            ((Real.exp (-1) * 15) / 2) * Real.log y ≤ EW) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => goodBlockCount S y < compositeGoodBlockThreshold y) ≤
            y ^ (-c₁) := by
  -- Paper Lemma 2.5: for independent Bernoulli indicators,
  -- `P(W < (2/3) E W) ≤ exp (-E W / 18)`.  The displayed lower bound on `EW`
  -- converts this to `O(y^{-c₁})`.
  classical
  rcases _hind with ⟨yind, hyind_ge2, hind⟩
  rcases _hexp with ⟨yexp, hyexp_ge2, hexp⟩
  let c₁ : ℝ := (Real.exp (-1) * 15) / 36
  refine ⟨c₁, ?_, max yind yexp, ?_, ?_⟩
  · dsimp [c₁]
    positivity
  · exact hyind_ge2.trans (le_max_left _ _)
  · intro y hy
    let M : ℕ := compositeBlockCount y
    let s : Finset ℕ := Finset.range M
    let p : ℕ → ℝ := fun k => blockGoodProbability (compositeBlock y k)
    let EW : ℝ := ∑ k ∈ s, p k
    have hyind_y : yind ≤ y := (le_max_left yind yexp).trans hy
    have hyexp_y : yexp ≤ y := (le_max_right yind yexp).trans hy
    have hy_ge2 : (2 : ℝ) ≤ y := hyind_ge2.trans hyind_y
    have hy_pos : 0 < y := by linarith
    have hind_y := hind y hyind_y
    have hexp_y := hexp y hyexp_y
    have hU_one : ∀ q ∈ compositePrimeWindow 20 y, 1 ≤ q :=
      fun _q hq => compositePrimeWindow_one_le hq
    have hp0 : ∀ k ∈ s, 0 ≤ p k := by
      intro k hk
      have hA_sub : ({k} : Finset ℕ) ⊆ s := by
        intro j hj
        rw [Finset.mem_singleton] at hj
        simpa [s, hj] using hk
      have hEq := hind_y ({k} : Finset ℕ) ∅ hA_sub (by simp) (by simp)
      have hnonneg :
          0 ≤ finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S =>
              (∀ j ∈ ({k} : Finset ℕ), (compositeBlock y j ∩ S).card = 1) ∧
                ∀ j ∈ (∅ : Finset ℕ), (compositeBlock y j ∩ S).card ≠ 1) :=
        finitePrimeModelProb_nonneg hU_one _
      rw [hEq] at hnonneg
      simpa [p] using hnonneg
    have hp1 : ∀ k ∈ s, p k ≤ 1 := by
      intro k hk
      have hB_sub : ({k} : Finset ℕ) ⊆ s := by
        intro j hj
        rw [Finset.mem_singleton] at hj
        simpa [s, hj] using hk
      have hEq := hind_y ∅ ({k} : Finset ℕ) (by simp) hB_sub (by simp)
      have hnonneg :
          0 ≤ finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S =>
              (∀ j ∈ (∅ : Finset ℕ), (compositeBlock y j ∩ S).card = 1) ∧
                ∀ j ∈ ({k} : Finset ℕ), (compositeBlock y j ∩ S).card ≠ 1) :=
        finitePrimeModelProb_nonneg hU_one _
      rw [hEq] at hnonneg
      have hnonneg' : 0 ≤ 1 - p k := by simpa [p] using hnonneg
      linarith
    have htail_eq :
        finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => goodBlockCount S y < compositeGoodBlockThreshold y) =
          ∑ T ∈ s.powerset.filter (fun T => T.card < compositeGoodBlockThreshold y),
            (∏ k ∈ T, p k) * ∏ k ∈ s \ T, (1 - p k) := by
      simpa [M, s, p] using finitePrimeModelProb_goodBlockCount_lt_eq_bernoulli_sum
        (y := y) hind_y
    have hK : (compositeGoodBlockThreshold y : ℝ) ≤ (2 / 3 : ℝ) * EW := by
      simpa [M, s, p, EW] using hexp_y.1
    have htail_exp :
        finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => goodBlockCount S y < compositeGoodBlockThreshold y) ≤
          Real.exp (-EW / 18) := by
      rw [htail_eq]
      exact bernoulli_lower_tail_chernoff_sum s p hp0 hp1 (by rfl) hK
    have hEW_lower : ((Real.exp (-1) * 15) / 2) * Real.log y ≤ EW := by
      simpa [M, s, p, EW] using hexp_y.2
    have hpow_decay : Real.exp (-EW / 18) ≤ y ^ (-c₁) := by
      have hcoef : c₁ * Real.log y ≤ EW / 18 := by
        dsimp [c₁]
        nlinarith [hEW_lower]
      calc
        Real.exp (-EW / 18) ≤ Real.exp (-c₁ * Real.log y) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        _ = y ^ (-c₁) := by
          rw [Real.rpow_def_of_pos hy_pos]
          ring_nf
    exact htail_exp.trans hpow_decay

/-- Analytic core of Step 4: the finite-product-model Chernoff bound for good blocks.

This isolates the remaining probability-theory obligation from the wrapper lemma below.
It uses Step 3 to identify the expectations of the good-block indicators and then applies
the paper's non-iid Bernoulli Chernoff lower-tail estimate to the custom finite prime model. -/
private lemma step4_chernoff_good_blocks_core
    (_hstep3 :
      ∃ C : ℝ, 0 < C ∧
        ∃ y₀ : ℝ, 2 ≤ y₀ ∧
          ∀ y : ℝ, y₀ ≤ y →
            let M := compositeBlockCount y
            ∀ k : ℕ, k < M →
              |blockGoodProbability (compositeBlock y k) - Real.exp (-1)| ≤ C / y) :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => goodBlockCount S y < compositeGoodBlockThreshold y) ≤
            y ^ (-c₁) := by
  -- Paper §6.2 Step 4, including the finite-model independence bookkeeping and
  -- the lower-tail Chernoff inequality `P(W < (2/3) E W) ≤ exp (-E W / 18)`.
  exact step4_chernoff_combined step4_independence_lemma
    (step4_expectation_lower_bound _hstep3)

/-- Step 4: Chernoff lower-tail estimate for the number of good blocks.

**Paper §6.2 Step 4 (lines 1690-1697):** in the independent prime-selection
model on `compositePrimeWindow 20 y`, the probability that fewer than `K`
blocks are good is `O(y^{-c₁})`, where `K = compositeGoodBlockThreshold y` and
the Chernoff inequality (paper Lemma 2.5) gives `P(W < (2/3) E W) ≤ exp(-EW/18)
= O(y^{-c₁})`.

This statement is the **actual probability bound** (not a tautological algebraic
conversion).  No vacuous existential witness escapes — `finitePrimeModelProb`
evaluates to a specific real determined by the predicate `goodBlockCount S y < K`.

Refactored 2026-04-28 (audit fix): the previous formulation
`∀ lowerTailProb, lowerTailProb ≤ exp(-EW/18) → lowerTailProb ≤ y^{-c₁}` was a
tautological algebraic conversion that did not capture the Chernoff probability
bound the paper actually proves.  The current form is paper-faithful. -/
private lemma step4_chernoff_good_blocks :
    ∃ c₁ : ℝ, 0 < c₁ ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => goodBlockCount S y < compositeGoodBlockThreshold y) ≤
            Real.exp (-c₁ * Real.log y) := by
  -- Paper §6.2 Step 4 + paper Lemma 2.5 (Chernoff for independent Bernoulli).
  -- Step 3 gives expectation `e^{-1} M + O(1)` and the indicator independence,
  -- and Chernoff gives `exp(-E W / 18) = O(y^{-c₁})`.  The proof requires
  -- formalizing Chernoff for non-iid Bernoulli over the finite product model;
  -- this is the only remaining analytic content of step 4.
  have hstep3 := step3_good_block_probability
  rcases step4_chernoff_good_blocks_core hstep3 with ⟨c₁, hc₁, y₀, hy₀, htail⟩
  refine ⟨c₁, hc₁, y₀, hy₀, ?_⟩
  intro y hy
  have hy_pos : 0 < y := (by norm_num : (0 : ℝ) < 2).trans_le (hy₀.trans hy)
  calc
    finitePrimeModelProb (compositePrimeWindow 20 y)
        (fun S => goodBlockCount S y < compositeGoodBlockThreshold y) ≤ y ^ (-c₁) :=
      htail y hy
    _ = Real.exp (-c₁ * Real.log y) := by
      rw [Real.rpow_def_of_pos hy_pos]
      ring_nf

private lemma integral_compositeBlockEndpoint {y : ℝ} (hy : 0 < y) (k : ℕ) :
    (∫ t in compositeBlockEndpoint y k..compositeBlockEndpoint y (k + 1),
      1 / (t * Real.log t)) = 1 := by
  have ha : 1 < compositeBlockEndpoint y k := by
    dsimp [compositeBlockEndpoint]
    exact Real.one_lt_exp_iff.mpr (mul_pos hy (Real.exp_pos _))
  have hab : compositeBlockEndpoint y k ≤ compositeBlockEndpoint y (k + 1) := by
    dsimp [compositeBlockEndpoint]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hy.le
    exact Real.exp_le_exp.mpr (by norm_num)
  rw [integral_one_div_mul_log_of_one_lt ha hab]
  have hlogk :
      Real.log (Real.log (compositeBlockEndpoint y k)) = Real.log y + (k : ℝ) := by
    rw [show Real.log (compositeBlockEndpoint y k) = y * Real.exp (k : ℝ) by
        simp [compositeBlockEndpoint],
      Real.log_mul (ne_of_gt hy) (Real.exp_ne_zero _), Real.log_exp]
  have hlogsk :
      Real.log (Real.log (compositeBlockEndpoint y (k + 1))) =
        Real.log y + ((k + 1 : ℕ) : ℝ) := by
    rw [show Real.log (compositeBlockEndpoint y (k + 1)) =
        y * Real.exp ((k + 1 : ℕ) : ℝ) by simp [compositeBlockEndpoint],
      Real.log_mul (ne_of_gt hy) (Real.exp_ne_zero _), Real.log_exp]
  rw [hlogk, hlogsk]
  norm_num

/-- `C · y · exp(-c·√y) ≤ y^{-1/2}` eventually.  Used to convert L1 sums over `(ZMod d)ˣ`
of super-poly per-residue bounds (multiplied by `φ(d) ≤ d ≤ y` factor) to polynomial
`y^{-1/2}` L1 bounds.  Paper §6.2 line 1741: TV bound. -/
private lemma poly_times_exp_sqrt_decay_eventually_le_rpow {C c : ℝ} (_hC : 0 < C) (hc : 0 < c) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
      C * y * Real.exp (-c * Real.sqrt y) ≤ y ^ (-(1 : ℝ) / 2) := by
  have htend0 :
      Filter.Tendsto (fun x : ℝ => C * (x ^ (3 : ℝ) * Real.exp (-c * x)))
        Filter.atTop (nhds 0) := by
    simpa [mul_assoc] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (3 : ℝ) c hc).const_mul C)
  have htend :
      Filter.Tendsto
        (fun y : ℝ => C * (Real.sqrt y ^ (3 : ℝ) * Real.exp (-c * Real.sqrt y)))
        Filter.atTop (nhds 0) := htend0.comp Real.tendsto_sqrt_atTop
  rw [Metric.tendsto_atTop] at htend
  rcases htend 1 (by norm_num) with ⟨Y, hY⟩
  refine ⟨max 1 Y, ?_⟩
  intro y hy
  have hy1 : (1 : ℝ) ≤ y := le_trans (le_max_left 1 Y) hy
  have hYle : Y ≤ y := le_trans (le_max_right 1 Y) hy
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hsqrt_pos : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hdist := hY y hYle
  have hsmall : C * (Real.sqrt y ^ (3 : ℝ) * Real.exp (-c * Real.sqrt y)) ≤ 1 := by
    have habs : |C * (Real.sqrt y ^ (3 : ℝ) * Real.exp (-c * Real.sqrt y))| < 1 := by
      simpa [Real.dist_eq] using hdist
    exact (abs_lt.mp habs).2.le
  have hsqrt_cube : Real.sqrt y ^ (3 : ℝ) = y * Real.sqrt y := by
    have h2 : Real.sqrt y ^ (2 : ℝ) = y := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact Real.sq_sqrt hypos.le
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.rpow_add hsqrt_pos, Real.rpow_one, h2]
  rw [hsqrt_cube] at hsmall
  have hmul : (C * y * Real.exp (-c * Real.sqrt y)) * Real.sqrt y ≤ 1 := by
    have heq : C * (y * Real.sqrt y * Real.exp (-c * Real.sqrt y)) =
        (C * y * Real.exp (-c * Real.sqrt y)) * Real.sqrt y := by ring
    linarith
  have hdiv : C * y * Real.exp (-c * Real.sqrt y) ≤ 1 / Real.sqrt y := by
    rw [le_div_iff₀ hsqrt_pos]
    exact hmul
  have hrpow : y ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt y := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring]
    rw [Real.rpow_neg hypos.le]
    rw [← Real.sqrt_eq_rpow]
    ring
  simpa [hrpow] using hdiv

private lemma exp_sqrt_decay_eventually_le_rpow {C c : ℝ} (_hC : 0 < C) (hc : 0 < c) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
      C * Real.exp (-c * Real.sqrt y) ≤ y ^ (-(1 : ℝ) / 2) := by
  have htend0 :
      Filter.Tendsto (fun x : ℝ => C * (x ^ (1 : ℝ) * Real.exp (-c * x)))
        Filter.atTop (nhds 0) := by
    simpa [mul_assoc] using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) c hc).const_mul C)
  have htend :
      Filter.Tendsto
        (fun y : ℝ => C * (Real.sqrt y ^ (1 : ℝ) * Real.exp (-c * Real.sqrt y)))
        Filter.atTop (nhds 0) := htend0.comp Real.tendsto_sqrt_atTop
  rw [Metric.tendsto_atTop] at htend
  rcases htend 1 (by norm_num) with ⟨Y, hY⟩
  refine ⟨max 1 Y, ?_⟩
  intro y hy
  have hy1 : (1 : ℝ) ≤ y := le_trans (le_max_left 1 Y) hy
  have hYle : Y ≤ y := le_trans (le_max_right 1 Y) hy
  have hdist := hY y hYle
  have hsmall : C * (Real.sqrt y ^ (1 : ℝ) * Real.exp (-c * Real.sqrt y)) ≤ 1 := by
    have habs : |C * (Real.sqrt y ^ (1 : ℝ) * Real.exp (-c * Real.sqrt y))| < 1 := by
      simpa [Real.dist_eq] using hdist
    exact (abs_lt.mp habs).2.le
  have hsqrt_pos : 0 < Real.sqrt y := Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hy1)
  have hmul : (C * Real.exp (-c * Real.sqrt y)) * Real.sqrt y ≤ 1 := by
    simpa [Real.rpow_one, mul_assoc, mul_comm, mul_left_comm] using hsmall
  have hdiv : C * Real.exp (-c * Real.sqrt y) ≤ 1 / Real.sqrt y := by
    rw [le_div_iff₀ hsqrt_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hrpow : y ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt y := by
    have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring]
    rw [Real.rpow_neg hypos.le]
    rw [← Real.sqrt_eq_rpow]
    ring
  simpa [hrpow] using hdiv

private lemma block_residue_reciprocal_prime_uniform :
    ∃ C : ℝ, 0 < C ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ y →
            let M := compositeBlockCount y
            ∀ k : ℕ, k < M →
              ∀ a : ℕ, Nat.Coprime a d →
                |(∑ q ∈ (compositeBlock y k).filter (fun q => q % d = a % d),
                    (1 : ℝ) / (q : ℝ)) - (1 : ℝ) / (d.totient : ℝ)| ≤
                  C * y ^ (-(1 : ℝ) / 2) := by
  classical
  rcases sw_reciprocal_AP 1 (by norm_num : (0 : ℝ) < 1) with
    ⟨c, hc, Csw, hCsw, hSW⟩
  rcases exp_sqrt_decay_eventually_le_rpow hCsw hc with ⟨Ydecay, hYdecay⟩
  refine ⟨1, by norm_num, max 2 Ydecay, ?_, ?_⟩
  · exact le_max_left 2 Ydecay
  intro y hy d hd hdy
  dsimp
  intro k _hk a ha
  let X : ℝ := compositeBlockEndpoint y k
  let Y : ℝ := compositeBlockEndpoint y (k + 1)
  have hy_ge2 : (2 : ℝ) ≤ y := le_trans (le_max_left 2 Ydecay) hy
  have hy_pos : 0 < y := by linarith
  have hy_nonneg : 0 ≤ y := hy_pos.le
  have hy_decay : Ydecay ≤ y := le_trans (le_max_right 2 Ydecay) hy
  have hX_ge_three : 3 ≤ X := by
    have harg_ge_two : (2 : ℝ) ≤ y * Real.exp (k : ℝ) := by
      have hexp_ge_one : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
        calc
          (1 : ℝ) = Real.exp 0 := by simp
          _ ≤ Real.exp (k : ℝ) :=
            Real.exp_le_exp.mpr (by exact_mod_cast Nat.zero_le k)
      calc
        (2 : ℝ) ≤ y := hy_ge2
        _ ≤ y * Real.exp (k : ℝ) := by
          have h := mul_le_mul_of_nonneg_left hexp_ge_one hy_nonneg
          simpa using h
    calc
      (3 : ℝ) ≤ Real.exp 2 := by
        have h := Real.add_one_le_exp (2 : ℝ)
        norm_num at h ⊢
        exact h
      _ ≤ X := by
        dsimp [X, compositeBlockEndpoint]
        exact Real.exp_le_exp.mpr harg_ge_two
  have hX_le_Y : X ≤ Y := by
    dsimp [X, Y, compositeBlockEndpoint]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hy_nonneg
    exact Real.exp_le_exp.mpr (by norm_num)
  have hd_one : 1 ≤ d := by omega
  have hlogX : Real.log X = y * Real.exp (k : ℝ) := by
    simp [X, compositeBlockEndpoint]
  have hlogX_ge_y : y ≤ Real.log X := by
    rw [hlogX]
    have hexp_ge_one : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (k : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast Nat.zero_le k)
    have h := mul_le_mul_of_nonneg_left hexp_ge_one hy_nonneg
    simpa using h
  have hd_log : (d : ℝ) ≤ (Real.log X) ^ (1 : ℝ) := by
    calc
      (d : ℝ) ≤ y := hdy
      _ ≤ Real.log X := hlogX_ge_y
      _ = (Real.log X) ^ (1 : ℝ) := by rw [Real.rpow_one]
  have hsw := hSW X Y hX_ge_three hX_le_Y d hd_one hd_log a ha
  have hI : (∫ t in X..Y, 1 / (t * Real.log t)) = 1 := by
    simpa [X, Y] using integral_compositeBlockEndpoint (y := y) hy_pos k
  have hsum_eq :
      (∑ q ∈ (compositeBlock y k).filter (fun q => q % d = a % d),
          (1 : ℝ) / (q : ℝ)) =
        (∑ q ∈ Finset.filter
          (fun q => q.Prime ∧ q % d = a % d ∧ X < (q : ℝ) ∧ (q : ℝ) ≤ Y)
          (Finset.Iic ⌊Y⌋₊), (1 : ℝ) / (q : ℝ)) := by
    simp [X, Y, compositeBlock, Finset.filter_filter, and_comm, and_left_comm]
  have hsw' :
      |(∑ q ∈ (compositeBlock y k).filter (fun q => q % d = a % d),
          (1 : ℝ) / (q : ℝ)) - (1 : ℝ) / (d.totient : ℝ)| ≤
        Csw * Real.exp (-c * Real.sqrt (Real.log X)) := by
    rw [hsum_eq]
    rw [hI] at hsw
    simpa [one_div] using hsw
  have hdecay_mono :
      Csw * Real.exp (-c * Real.sqrt (Real.log X)) ≤
        Csw * Real.exp (-c * Real.sqrt y) := by
    have hsqrt_le : Real.sqrt y ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hlogX_ge_y
    have hneg_le : -c * Real.sqrt (Real.log X) ≤ -c * Real.sqrt y := by
      nlinarith [hc]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg_le) hCsw.le
  have hdecay := hYdecay y hy_decay
  calc
    |(∑ q ∈ (compositeBlock y k).filter (fun q => q % d = a % d),
        (1 : ℝ) / (q : ℝ)) - 1 / (d.totient : ℝ)|
        ≤ Csw * Real.exp (-c * Real.sqrt (Real.log X)) := hsw'
    _ ≤ Csw * Real.exp (-c * Real.sqrt y) := hdecay_mono
    _ ≤ y ^ (-(1 : ℝ) / 2) := hdecay
    _ = 1 * y ^ (-(1 : ℝ) / 2) := by ring

/-- L1 version of `block_residue_reciprocal_prime_uniform`: the sum over coprime
residues of pointwise residue-density deviations is `O(y^{-1/2})`.
Paper §6.2 line 1741: TV-close.

Proof: SW super-poly per residue × at most `d ≤ y` coprime residues
= `y · super-poly ≤ y^{-1/2}`. -/
private lemma block_residue_reciprocal_prime_uniform_l1 :
    ∃ C : ℝ, 0 < C ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ y →
            let M := compositeBlockCount y
            ∀ k : ℕ, k < M →
              (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
                  |(∑ q ∈ (compositeBlock y k).filter
                      (fun q => q % d = a % d),
                      (1 : ℝ) / (q : ℝ)) - (1 : ℝ) / (d.totient : ℝ)|) ≤
                C * y ^ (-(1 : ℝ) / 2) := by
  classical
  rcases sw_reciprocal_AP 1 (by norm_num : (0 : ℝ) < 1) with
    ⟨c, hc, Csw, hCsw, hSW⟩
  rcases poly_times_exp_sqrt_decay_eventually_le_rpow hCsw hc with ⟨Ydecay, hYdecay⟩
  refine ⟨1, by norm_num, max 2 Ydecay, ?_, ?_⟩
  · exact le_max_left 2 Ydecay
  intro y hy d hd hdy
  dsimp
  intro k _hk
  let X : ℝ := compositeBlockEndpoint y k
  let Y : ℝ := compositeBlockEndpoint y (k + 1)
  have hy_ge2 : (2 : ℝ) ≤ y := le_trans (le_max_left 2 Ydecay) hy
  have hy_pos : 0 < y := by linarith
  have hy_nonneg : 0 ≤ y := hy_pos.le
  have hy_decay : Ydecay ≤ y := le_trans (le_max_right 2 Ydecay) hy
  have hX_ge_three : 3 ≤ X := by
    have harg_ge_two : (2 : ℝ) ≤ y * Real.exp (k : ℝ) := by
      have hexp_ge_one : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
        calc
          (1 : ℝ) = Real.exp 0 := by simp
          _ ≤ Real.exp (k : ℝ) :=
            Real.exp_le_exp.mpr (by exact_mod_cast Nat.zero_le k)
      calc
        (2 : ℝ) ≤ y := hy_ge2
        _ ≤ y * Real.exp (k : ℝ) := by
          have h := mul_le_mul_of_nonneg_left hexp_ge_one hy_nonneg
          simpa using h
    calc
      (3 : ℝ) ≤ Real.exp 2 := by
        have h := Real.add_one_le_exp (2 : ℝ)
        norm_num at h ⊢
        exact h
      _ ≤ X := by
        dsimp [X, compositeBlockEndpoint]
        exact Real.exp_le_exp.mpr harg_ge_two
  have hX_le_Y : X ≤ Y := by
    dsimp [X, Y, compositeBlockEndpoint]
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hy_nonneg
    exact Real.exp_le_exp.mpr (by norm_num)
  have hd_one : 1 ≤ d := by omega
  have hlogX : Real.log X = y * Real.exp (k : ℝ) := by
    simp [X, compositeBlockEndpoint]
  have hlogX_ge_y : y ≤ Real.log X := by
    rw [hlogX]
    have hexp_ge_one : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (k : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast Nat.zero_le k)
    have h := mul_le_mul_of_nonneg_left hexp_ge_one hy_nonneg
    simpa using h
  have hd_log : (d : ℝ) ≤ (Real.log X) ^ (1 : ℝ) := by
    calc
      (d : ℝ) ≤ y := hdy
      _ ≤ Real.log X := hlogX_ge_y
      _ = (Real.log X) ^ (1 : ℝ) := by rw [Real.rpow_one]
  have hI : (∫ t in X..Y, 1 / (t * Real.log t)) = 1 := by
    simpa [X, Y] using integral_compositeBlockEndpoint (y := y) hy_pos k
  -- Pointwise super-poly bound, per a ∈ Finset.range d coprime to d.
  have hpw : ∀ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
      |(∑ q ∈ (compositeBlock y k).filter
          (fun q => q % d = a % d),
          (1 : ℝ) / (q : ℝ)) - (1 : ℝ) / (d.totient : ℝ)| ≤
        Csw * Real.exp (-c * Real.sqrt y) := by
    intro a ha_filter
    have ha_cop : Nat.Coprime a d := (Finset.mem_filter.mp ha_filter).2
    have hsw := hSW X Y hX_ge_three hX_le_Y d hd_one hd_log _ ha_cop
    have hsum_eq :
        (∑ q ∈ (compositeBlock y k).filter
            (fun q => q % d = a % d),
            (1 : ℝ) / (q : ℝ)) =
          (∑ q ∈ Finset.filter
            (fun q => q.Prime ∧ q % d = a % d ∧
              X < (q : ℝ) ∧ (q : ℝ) ≤ Y)
            (Finset.Iic ⌊Y⌋₊), (1 : ℝ) / (q : ℝ)) := by
      simp [X, Y, compositeBlock, Finset.filter_filter, and_comm, and_left_comm]
    have hsw' :
        |(∑ q ∈ (compositeBlock y k).filter
            (fun q => q % d = a % d),
            (1 : ℝ) / (q : ℝ)) - (1 : ℝ) / (d.totient : ℝ)| ≤
          Csw * Real.exp (-c * Real.sqrt (Real.log X)) := by
      rw [hsum_eq]
      rw [hI] at hsw
      simpa [one_div] using hsw
    have hdecay_mono :
        Csw * Real.exp (-c * Real.sqrt (Real.log X)) ≤
          Csw * Real.exp (-c * Real.sqrt y) := by
      have hsqrt_le : Real.sqrt y ≤ Real.sqrt (Real.log X) := Real.sqrt_le_sqrt hlogX_ge_y
      have hneg_le : -c * Real.sqrt (Real.log X) ≤ -c * Real.sqrt y := by
        nlinarith [hc]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg_le) hCsw.le
    linarith
  -- Sum the pointwise super-poly bound over coprime residues.
  -- Card of filtered Finset = totient by Mathlib's Nat.totient_eq_card_lt_and_coprime (or similar).
  have hcard : (((Finset.range d).filter (fun a => Nat.Coprime a d)).card : ℝ) = (d.totient : ℝ) := by
    rw [Nat.totient]
    have hset : (Finset.range d).filter (fun a => Nat.Coprime a d) =
        (Finset.range d).filter (fun a => Nat.Coprime d a) := by
      apply Finset.filter_congr
      intro a _
      exact ⟨Nat.Coprime.symm, Nat.Coprime.symm⟩
    rw [hset]
  have hphi_pos_nat : 0 < d.totient := Nat.totient_pos.mpr (by omega : 0 < d)
  have hphi_le_d : (d.totient : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.totient_le d
  have hphi_le_y : (d.totient : ℝ) ≤ y := le_trans hphi_le_d hdy
  have hsum_le : (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
      |(∑ q ∈ (compositeBlock y k).filter
          (fun q => q % d = a % d),
          (1 : ℝ) / (q : ℝ)) - (1 : ℝ) / (d.totient : ℝ)|) ≤
      (d.totient : ℝ) * (Csw * Real.exp (-c * Real.sqrt y)) := by
    calc (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
          |(∑ q ∈ (compositeBlock y k).filter
              (fun q => q % d = a % d),
              (1 : ℝ) / (q : ℝ)) - (1 : ℝ) / (d.totient : ℝ)|)
        ≤ ∑ _a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
            Csw * Real.exp (-c * Real.sqrt y) := Finset.sum_le_sum hpw
      _ = (((Finset.range d).filter (fun a => Nat.Coprime a d)).card : ℝ) *
            (Csw * Real.exp (-c * Real.sqrt y)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (d.totient : ℝ) * (Csw * Real.exp (-c * Real.sqrt y)) := by rw [hcard]
  have h_y_bound : (d.totient : ℝ) * (Csw * Real.exp (-c * Real.sqrt y)) ≤
      Csw * y * Real.exp (-c * Real.sqrt y) := by
    have h1 : (d.totient : ℝ) * (Csw * Real.exp (-c * Real.sqrt y)) =
        Csw * ((d.totient : ℝ) * Real.exp (-c * Real.sqrt y)) := by ring
    have h2 : Csw * y * Real.exp (-c * Real.sqrt y) =
        Csw * (y * Real.exp (-c * Real.sqrt y)) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hphi_le_y (Real.exp_nonneg _)) hCsw.le
  have hdecay := hYdecay y hy_decay
  calc (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
        |(∑ q ∈ (compositeBlock y k).filter
            (fun q => q % d = a % d),
            (1 : ℝ) / (q : ℝ)) - (1 : ℝ) / (d.totient : ℝ)|)
      ≤ (d.totient : ℝ) * (Csw * Real.exp (-c * Real.sqrt y)) := hsum_le
    _ ≤ Csw * y * Real.exp (-c * Real.sqrt y) := h_y_bound
    _ ≤ y ^ (-(1 : ℝ) / 2) := hdecay
    _ = 1 * y ^ (-(1 : ℝ) / 2) := by ring

private lemma inv_sub_one_sub_inv_le_exp {y : ℝ} {q : ℕ} (hy2 : (2 : ℝ) ≤ y)
    (hqgt : Real.exp y < (q : ℝ)) :
    0 ≤ (1 : ℝ) / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ) ∧
      (1 : ℝ) / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ) ≤
        (2 * Real.exp (-y)) * ((1 : ℝ) / (q : ℝ)) := by
  have hq_gt_two : (2 : ℝ) < (q : ℝ) := by
    have hy_lt_exp : y < Real.exp y := by nlinarith [Real.add_one_le_exp y]
    exact lt_of_le_of_lt hy2 (lt_trans hy_lt_exp hqgt)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hq_nat_pos : 0 < q := by exact_mod_cast hq_pos
  have hq_nat_gt_two : 2 < q := by exact_mod_cast hq_gt_two
  have hq_sub_pos_nat : 0 < q - 1 := by omega
  have hq_sub_pos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast hq_sub_pos_nat
  have hq_sub_cast : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq_nat_pos]
    norm_num
  have hdiff_eq : (1 : ℝ) / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ) =
      1 / (((q - 1 : ℕ) : ℝ) * (q : ℝ)) := by
    field_simp [ne_of_gt hq_sub_pos, ne_of_gt hq_pos]
    rw [hq_sub_cast]
    ring
  constructor
  · rw [hdiff_eq]
    positivity
  · have hsub_ge_half : (q : ℝ) / 2 ≤ ((q - 1 : ℕ) : ℝ) := by
      rw [hq_sub_cast]
      linarith
    have hinv_sub_le : (1 : ℝ) / ((q - 1 : ℕ) : ℝ) ≤ 2 / (q : ℝ) := by
      have hhalf_pos : 0 < (q : ℝ) / 2 := by positivity
      have h := one_div_le_one_div_of_le hhalf_pos hsub_ge_half
      calc
        (1 : ℝ) / ((q - 1 : ℕ) : ℝ) ≤ 1 / ((q : ℝ) / 2) := h
        _ = 2 / (q : ℝ) := by field_simp [ne_of_gt hq_pos]
    have hinv_q_le_exp : (1 : ℝ) / (q : ℝ) ≤ Real.exp (-y) := by
      have hexp_pos : 0 < Real.exp y := Real.exp_pos y
      have h := one_div_le_one_div_of_le hexp_pos hqgt.le
      simpa [Real.exp_neg, one_div] using h
    have htwo_inv_le : 2 / (q : ℝ) ≤ 2 * Real.exp (-y) := by
      calc
        2 / (q : ℝ) = 2 * (1 / (q : ℝ)) := by ring
        _ ≤ 2 * Real.exp (-y) := mul_le_mul_of_nonneg_left hinv_q_le_exp (by norm_num)
    calc
      (1 : ℝ) / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ)
          = (1 / (q : ℝ)) * (1 / ((q - 1 : ℕ) : ℝ)) := by
            rw [hdiff_eq]
            field_simp [ne_of_gt hq_sub_pos, ne_of_gt hq_pos]
      _ ≤ (1 / (q : ℝ)) * (2 / (q : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hinv_sub_le (by positivity)
      _ ≤ (1 / (q : ℝ)) * (2 * Real.exp (-y)) := by
        exact mul_le_mul_of_nonneg_left htwo_inv_le (by positivity)
      _ = (2 * Real.exp (-y)) * (1 / (q : ℝ)) := by ring

private lemma compositeBlock_inv_sub_one_sum_sub_inv_sum_le {y : ℝ} {k : ℕ}
    {S : Finset ℕ} (hy2 : (2 : ℝ) ≤ y) (hS : S ⊆ compositeBlock y k)
    (hT : reciprocalPrimeMass (compositeBlock y k) ≤ 2) :
    |(∑ q ∈ S, (1 : ℝ) / ((q - 1 : ℕ) : ℝ)) -
        (∑ q ∈ S, (1 : ℝ) / (q : ℝ))| ≤ 4 * Real.exp (-y) := by
  classical
  have hendpoint_lower : Real.exp y ≤ compositeBlockEndpoint y k := by
    dsimp [compositeBlockEndpoint]
    apply Real.exp_le_exp.mpr
    have hy_nonneg : 0 ≤ y := by linarith
    have hexp_ge_one : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (k : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast Nat.zero_le k)
    have h := mul_le_mul_of_nonneg_left hexp_ge_one hy_nonneg
    simpa using h
  have hterm_nonneg : ∀ q ∈ S,
      0 ≤ (1 : ℝ) / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ) := by
    intro q hq
    have hqB := hS hq
    rcases Finset.mem_filter.mp hqB with ⟨_hqIic, _hqprime, hqgt, _hqle⟩
    exact (inv_sub_one_sub_inv_le_exp hy2 (lt_of_le_of_lt hendpoint_lower hqgt)).1
  have hterm_le : ∀ q ∈ S,
      (1 : ℝ) / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ) ≤
        (2 * Real.exp (-y)) * ((1 : ℝ) / (q : ℝ)) := by
    intro q hq
    have hqB := hS hq
    rcases Finset.mem_filter.mp hqB with ⟨_hqIic, _hqprime, hqgt, _hqle⟩
    exact (inv_sub_one_sub_inv_le_exp hy2 (lt_of_le_of_lt hendpoint_lower hqgt)).2
  have hsum_nonneg : 0 ≤ ∑ q ∈ S,
      ((1 : ℝ) / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ)) :=
    Finset.sum_nonneg hterm_nonneg
  have hSsum_le_B :
      (∑ q ∈ S, (1 : ℝ) / (q : ℝ)) ≤ reciprocalPrimeMass (compositeBlock y k) := by
    dsimp [reciprocalPrimeMass]
    exact Finset.sum_le_sum_of_subset_of_nonneg hS (by intro q _ _; positivity)
  have hfactor_nonneg : 0 ≤ 2 * Real.exp (-y) := by positivity
  calc
    |(∑ q ∈ S, (1 : ℝ) / ((q - 1 : ℕ) : ℝ)) - (∑ q ∈ S, (1 : ℝ) / (q : ℝ))|
        = |∑ q ∈ S, ((1 : ℝ) / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ))| := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ q ∈ S, ((1 : ℝ) / ((q - 1 : ℕ) : ℝ) - 1 / (q : ℝ)) :=
      abs_of_nonneg hsum_nonneg
    _ ≤ ∑ q ∈ S, (2 * Real.exp (-y)) * ((1 : ℝ) / (q : ℝ)) :=
      Finset.sum_le_sum hterm_le
    _ = (2 * Real.exp (-y)) * (∑ q ∈ S, (1 : ℝ) / (q : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * Real.exp (-y)) * reciprocalPrimeMass (compositeBlock y k) :=
      mul_le_mul_of_nonneg_left hSsum_le_B hfactor_nonneg
    _ ≤ (2 * Real.exp (-y)) * 2 := mul_le_mul_of_nonneg_left hT hfactor_nonneg
    _ = 4 * Real.exp (-y) := by ring

private lemma compositeBlock_reciprocalPrimeMass_le_sub_one_sum {y : ℝ} {k : ℕ}
    (hy2 : (2 : ℝ) ≤ y) :
    reciprocalPrimeMass (compositeBlock y k) ≤
      ∑ q ∈ compositeBlock y k, (1 : ℝ) / ((q - 1 : ℕ) : ℝ) := by
  classical
  have hendpoint_lower : Real.exp y ≤ compositeBlockEndpoint y k := by
    dsimp [compositeBlockEndpoint]
    apply Real.exp_le_exp.mpr
    have hy_nonneg : 0 ≤ y := by linarith
    have hexp_ge_one : (1 : ℝ) ≤ Real.exp (k : ℝ) := by
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (k : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast Nat.zero_le k)
    have h := mul_le_mul_of_nonneg_left hexp_ge_one hy_nonneg
    simpa using h
  dsimp [reciprocalPrimeMass]
  apply Finset.sum_le_sum
  intro q hqB
  rcases Finset.mem_filter.mp hqB with ⟨_hqIic, _hqprime, hqgt, _hqle⟩
  have hnonneg := (inv_sub_one_sub_inv_le_exp hy2 (lt_of_le_of_lt hendpoint_lower hqgt)).1
  linarith

private lemma one_div_le_rpow_neg_half {y : ℝ} (hy1 : (1 : ℝ) ≤ y) :
    (1 : ℝ) / y ≤ y ^ (-(1 : ℝ) / 2) := by
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hsqrt_le_y : Real.sqrt y ≤ y := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hypos.le
    · have hy_nonneg : 0 ≤ y := by linarith
      have hy_le_sq : y ≤ y ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hy1) hy_nonneg]
      exact hy_le_sq
  have hinv : (1 : ℝ) / y ≤ 1 / Real.sqrt y :=
    one_div_le_one_div_of_le (Real.sqrt_pos.2 hypos) hsqrt_le_y
  have hrpow : y ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt y := by
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring]
    rw [Real.rpow_neg hypos.le]
    rw [← Real.sqrt_eq_rpow]
    ring
  simpa [hrpow] using hinv

private lemma ratio_close {N D u EN ED : ℝ}
    (hDpos : (1 / 2 : ℝ) ≤ D) (hu_nonneg : 0 ≤ u) (hu_le_one : u ≤ 1)
    (hN : |N - u| ≤ EN) (hD : |D - 1| ≤ ED) :
    |N / D - u| ≤ 2 * (EN + ED) := by
  have hD_pos : 0 < D := by linarith
  have hD_abs : |D| = D := abs_of_nonneg hD_pos.le
  have hD_inv_le : 1 / D ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hDpos
    norm_num at h
    simpa [one_div] using h
  have hmain : N / D - u = (N - u + u * (1 - D)) / D := by
    field_simp [ne_of_gt hD_pos]
    ring
  calc
    |N / D - u| = |(N - u + u * (1 - D)) / D| := by rw [hmain]
    _ = |N - u + u * (1 - D)| / D := by rw [abs_div, hD_abs]
    _ ≤ (|N - u| + |u * (1 - D)|) / D := by
      exact div_le_div_of_nonneg_right (abs_add_le (N - u) (u * (1 - D))) hD_pos.le
    _ ≤ (EN + ED) / D := by
      apply div_le_div_of_nonneg_right _ hD_pos.le
      calc
        |N - u| + |u * (1 - D)| ≤ EN + |u * (1 - D)| :=
          add_le_add hN le_rfl
        _ = EN + |u| * |1 - D| := by rw [abs_mul]
        _ ≤ EN + 1 * ED := by
          have habs_u : |u| ≤ 1 := by rwa [abs_of_nonneg hu_nonneg]
          have hDabs : |1 - D| ≤ ED := by
            simpa [abs_sub_comm] using hD
          have hmul_le : |u| * |1 - D| ≤ 1 * ED :=
            mul_le_mul habs_u hDabs (abs_nonneg _) (by norm_num)
          linarith
        _ = EN + ED := by ring
    _ = (EN + ED) * (1 / D) := by ring
    _ ≤ (EN + ED) * 2 := by
      apply mul_le_mul_of_nonneg_left hD_inv_le
      have hEN_nonneg : 0 ≤ EN := le_trans (abs_nonneg _) hN
      have hED_nonneg : 0 ≤ ED := le_trans (abs_nonneg _) hD
      positivity
    _ = 2 * (EN + ED) := by ring

private lemma exp_neg_eventually_le_rpow_neg_half :
    ∃ Y : ℝ, 1 ≤ Y ∧
      ∀ y : ℝ, Y ≤ y → 4 * Real.exp (-y) ≤ y ^ (-(1 : ℝ) / 2) := by
  rcases exp_sqrt_decay_eventually_le_rpow (C := 4) (c := 1) (by norm_num) (by norm_num)
    with ⟨Y, hY⟩
  refine ⟨max 1 Y, le_max_left 1 Y, ?_⟩
  intro y hy
  have hy1 : (1 : ℝ) ≤ y := le_trans (le_max_left 1 Y) hy
  have hYle : Y ≤ y := le_trans (le_max_right 1 Y) hy
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  have hsqrt_le_y : Real.sqrt y ≤ y := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hypos.le
    · have hy_le_sq : y ≤ y ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hy1) hypos.le]
      exact hy_le_sq
  have hneg_le : -y ≤ -Real.sqrt y := by linarith
  calc
    4 * Real.exp (-y) ≤ 4 * Real.exp (-Real.sqrt y) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hneg_le) (by norm_num)
    _ ≤ y ^ (-(1 : ℝ) / 2) := by simpa using hY y hYle

private lemma block_residue_via_sw :
    ∃ C : ℝ, 0 < C ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ y →
            let M := compositeBlockCount y
            ∀ k : ℕ, k < M →
              ∀ a : ℕ, Nat.Coprime a d →
                |(∑ q ∈ (compositeBlock y k).filter (fun q => q % d = a % d),
                    (1 : ℝ) / (((q - 1 : ℕ) : ℝ))) -
                    (1 : ℝ) / (d.totient : ℝ)| ≤
                  C * y ^ (-(1 : ℝ) / 2) := by
  classical
  rcases block_residue_reciprocal_prime_uniform with ⟨Cap, hCap, yap, hyap2, hAP⟩
  rcases step2_block_decomposition with ⟨Cmass, hCmass, ymass, hymass2, hmass⟩
  rcases exp_neg_eventually_le_rpow_neg_half with ⟨Yexp, hYexp1, hExp⟩
  refine ⟨Cap + 1, by positivity,
    max yap (max ymass (max (2 * Cmass) Yexp)), ?_, ?_⟩
  · exact hyap2.trans (le_max_left yap (max ymass (max (2 * Cmass) Yexp)))
  intro y hy d hd hdy
  dsimp
  intro k hk a ha
  let B : Finset ℕ := compositeBlock y k
  let S : Finset ℕ := B.filter (fun q => q % d = a % d)
  let A : ℝ := ∑ q ∈ S, (1 : ℝ) / (((q - 1 : ℕ) : ℝ))
  let P : ℝ := ∑ q ∈ S, (1 : ℝ) / (q : ℝ)
  let u : ℝ := (1 : ℝ) / (d.totient : ℝ)
  let r : ℝ := y ^ (-(1 : ℝ) / 2)
  have hy_ap : yap ≤ y := (le_max_left yap (max ymass (max (2 * Cmass) Yexp))).trans hy
  have hy_mass : ymass ≤ y :=
    (le_trans (le_max_left ymass (max (2 * Cmass) Yexp))
      (le_max_right yap (max ymass (max (2 * Cmass) Yexp)))).trans hy
  have hy_2C : 2 * Cmass ≤ y :=
    (le_trans (le_trans (le_max_left (2 * Cmass) Yexp)
      (le_max_right ymass (max (2 * Cmass) Yexp)))
      (le_max_right yap (max ymass (max (2 * Cmass) Yexp)))).trans hy
  have hy_exp : Yexp ≤ y :=
    (le_trans (le_trans (le_max_right (2 * Cmass) Yexp)
      (le_max_right ymass (max (2 * Cmass) Yexp)))
      (le_max_right yap (max ymass (max (2 * Cmass) Yexp)))).trans hy
  have hy_ge2 : (2 : ℝ) ≤ y := hyap2.trans hy_ap
  have hy_pos : 0 < y := by linarith
  have hmass_k :
      |reciprocalPrimeMass B - 1| ≤ Cmass / y := by
    have hdata := hmass y hy_mass
    dsimp [B] at hdata ⊢
    exact (hdata.2.2 k hk).2
  have hCmass_div_le_one : Cmass / y ≤ 1 := by
    rw [div_le_iff₀ hy_pos]
    nlinarith [hCmass, hy_2C]
  have hBmass_le_two : reciprocalPrimeMass B ≤ 2 := by
    have hright := (abs_le.mp hmass_k).2
    linarith
  have hSsub : S ⊆ B := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hdiff : |A - P| ≤ 4 * Real.exp (-y) := by
    simpa [A, P, S, B] using
      (compositeBlock_inv_sub_one_sum_sub_inv_sum_le (y := y) (k := k)
        (S := S) hy_ge2 hSsub hBmass_le_two)
  have hAP' : |P - u| ≤ Cap * r := by
    simpa [P, S, B, u, r] using hAP y hy_ap d hd hdy k hk a ha
  have hExp' : 4 * Real.exp (-y) ≤ r := by
    simpa [r] using hExp y hy_exp
  calc
    |A - u| = |(A - P) + (P - u)| := by ring_nf
    _ ≤ |A - P| + |P - u| := abs_add_le (A - P) (P - u)
    _ ≤ 4 * Real.exp (-y) + Cap * r := add_le_add hdiff hAP'
    _ ≤ r + Cap * r := add_le_add hExp' le_rfl
    _ = (Cap + 1) * r := by ring

private lemma block_uniform_total_variation_bound :
    ∃ C : ℝ, 0 < C ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ y →
            let M := compositeBlockCount y
            ∀ k : ℕ, k < M →
              ∀ a : ℕ, Nat.Coprime a d →
                |blockConditionalResidueProbability (compositeBlock y k) d a -
                    (1 : ℝ) / (d.totient : ℝ)| ≤
                  C * y ^ (-(1 : ℝ) / 2) := by
  classical
  rcases block_residue_via_sw with ⟨Cnum, hCnum, ynum, hynum2, hnum⟩
  rcases step2_block_decomposition with ⟨Cmass, hCmass, ymass, hymass2, hmass⟩
  rcases exp_neg_eventually_le_rpow_neg_half with ⟨Yexp, hYexp1, hExp⟩
  let Cden : ℝ := Cmass + 1
  let C : ℝ := 2 * (Cnum + Cden)
  refine ⟨C, by positivity, max ynum (max ymass (max (2 * Cmass) Yexp)), ?_, ?_⟩
  · exact hynum2.trans (le_max_left ynum (max ymass (max (2 * Cmass) Yexp)))
  intro y hy d hd hdy
  dsimp
  intro k hk a ha
  let B : Finset ℕ := compositeBlock y k
  let S : Finset ℕ := B.filter (fun q => q % d = a % d)
  let N : ℝ := ∑ q ∈ S, (1 : ℝ) / (((q - 1 : ℕ) : ℝ))
  let D : ℝ := ∑ q ∈ B, (1 : ℝ) / (((q - 1 : ℕ) : ℝ))
  let μ : ℝ := reciprocalPrimeMass B
  let u : ℝ := (1 : ℝ) / (d.totient : ℝ)
  let r : ℝ := y ^ (-(1 : ℝ) / 2)
  have hy_num : ynum ≤ y := (le_max_left ynum (max ymass (max (2 * Cmass) Yexp))).trans hy
  have hy_mass : ymass ≤ y :=
    (le_trans (le_max_left ymass (max (2 * Cmass) Yexp))
      (le_max_right ynum (max ymass (max (2 * Cmass) Yexp)))).trans hy
  have hy_2C : 2 * Cmass ≤ y :=
    (le_trans (le_trans (le_max_left (2 * Cmass) Yexp)
      (le_max_right ymass (max (2 * Cmass) Yexp)))
      (le_max_right ynum (max ymass (max (2 * Cmass) Yexp)))).trans hy
  have hy_exp : Yexp ≤ y :=
    (le_trans (le_trans (le_max_right (2 * Cmass) Yexp)
      (le_max_right ymass (max (2 * Cmass) Yexp)))
      (le_max_right ynum (max ymass (max (2 * Cmass) Yexp)))).trans hy
  have hy_ge2 : (2 : ℝ) ≤ y := hynum2.trans hy_num
  have hy_pos : 0 < y := by linarith
  have hy_ge1 : (1 : ℝ) ≤ y := by linarith
  have hmass_k : |μ - 1| ≤ Cmass / y := by
    have hdata := hmass y hy_mass
    dsimp [μ, B] at hdata ⊢
    exact (hdata.2.2 k hk).2
  have hCmass_div_le_one : Cmass / y ≤ 1 := by
    rw [div_le_iff₀ hy_pos]
    nlinarith [hCmass, hy_2C]
  have hCmass_div_le_half : Cmass / y ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hy_pos]
    nlinarith [hCmass, hy_2C]
  have hBmass_le_two : μ ≤ 2 := by
    have hright := (abs_le.mp hmass_k).2
    linarith
  have hnum' : |N - u| ≤ Cnum * r := by
    simpa [N, S, B, u, r] using hnum y hy_num d hd hdy k hk a ha
  have hDdiff : |D - μ| ≤ 4 * Real.exp (-y) := by
    simpa [D, μ, B, reciprocalPrimeMass] using
      (compositeBlock_inv_sub_one_sum_sub_inv_sum_le (y := y) (k := k)
        (S := B) hy_ge2 (by intro q hq; exact hq) hBmass_le_two)
  have hExp' : 4 * Real.exp (-y) ≤ r := by
    simpa [r] using hExp y hy_exp
  have hone_div_le : (1 : ℝ) / y ≤ r := one_div_le_rpow_neg_half hy_ge1
  have hmass_r : Cmass / y ≤ Cmass * r := by
    calc
      Cmass / y = Cmass * ((1 : ℝ) / y) := by ring
      _ ≤ Cmass * r := mul_le_mul_of_nonneg_left hone_div_le hCmass.le
  have hDclose : |D - 1| ≤ Cden * r := by
    calc
      |D - 1| = |(D - μ) + (μ - 1)| := by ring_nf
      _ ≤ |D - μ| + |μ - 1| := abs_add_le (D - μ) (μ - 1)
      _ ≤ 4 * Real.exp (-y) + Cmass / y := add_le_add hDdiff hmass_k
      _ ≤ r + Cmass * r := add_le_add hExp' hmass_r
      _ = Cden * r := by
        dsimp [Cden]
        ring
  have hD_lower : μ ≤ D := by
    simpa [D, μ, B] using compositeBlock_reciprocalPrimeMass_le_sub_one_sum
      (y := y) (k := k) hy_ge2
  have hmu_ge_half : (1 / 2 : ℝ) ≤ μ := by
    have hleft := (abs_le.mp hmass_k).1
    linarith
  have hDpos : (1 / 2 : ℝ) ≤ D := hmu_ge_half.trans hD_lower
  have hd_pos : 0 < d := by omega
  have hphi_pos_nat : 0 < d.totient := Nat.totient_pos.mpr hd_pos
  have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := by exact_mod_cast hphi_pos_nat
  have hphi_ge_one : (1 : ℝ) ≤ (d.totient : ℝ) := by exact_mod_cast hphi_pos_nat
  have hu_nonneg : 0 ≤ u := by
    dsimp [u]
    positivity
  have hu_le_one : u ≤ 1 := by
    dsimp [u]
    rw [div_le_iff₀ hphi_pos]
    nlinarith
  have hratio := ratio_close (N := N) (D := D) (u := u) (EN := Cnum * r)
    (ED := Cden * r) hDpos hu_nonneg hu_le_one hnum' hDclose
  calc
    |blockConditionalResidueProbability (compositeBlock y k) d a - u| = |N / D - u| := by
      simp [blockConditionalResidueProbability, N, D, S, B, u]
    _ ≤ 2 * (Cnum * r + Cden * r) := hratio
    _ = C * r := by
      dsimp [C]
      ring

/-- Absorb the exponentially small block error into the common power scale. -/
private lemma block_l1_error_absorb (Cnum Cden y φ r : ℝ)
    (hy : 1 ≤ y) (hφ : φ ≤ y)
    (hbound : 8 * y * Real.exp (-Real.sqrt y) ≤ r) (hr : 0 ≤ r) :
    2 * ((φ * (4 * Real.exp (-y)) + Cnum * r) + Cden * r) ≤
      (2 * (Cnum + 1 + Cden + 1)) * r := by
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hroot : Real.sqrt y ≤ y :=
    Real.sqrt_le_iff.mpr ⟨hy0, by nlinarith only [hy]⟩
  have hexp : Real.exp (-y) ≤ Real.exp (-Real.sqrt y) :=
    Real.exp_monotone (neg_le_neg hroot)
  have hsmall : 8 * φ * Real.exp (-y) ≤ r := by
    calc
      _ ≤ 8 * y * Real.exp (-y) := by gcongr
      _ ≤ 8 * y * Real.exp (-Real.sqrt y) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ r := hbound
  nlinarith only [hsmall, hr]

/-- L1 version of `block_uniform_total_variation_bound`: sum over coprime residues
of pointwise residue-density deviations is `O(y^{-1/2})`.  Paper §6.2 line 1741: TV-close.

Proof: combine super-poly L1 bound on `1/q`-sum (`block_residue_reciprocal_prime_uniform_l1`),
the `|A - P| ≤ 4·exp(-y)` collapse (every q in B is coprime to d), and step2's `|D - 1|`
to bound `∑_a |A_a/D - u|` by `O(y^{-1/2})`. -/
private lemma block_uniform_total_variation_bound_l1 :
    ∃ C : ℝ, 0 < C ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ y →
            let M := compositeBlockCount y
            ∀ k : ℕ, k < M →
              (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
                  |blockConditionalResidueProbability (compositeBlock y k) d a -
                      (1 : ℝ) / (d.totient : ℝ)|) ≤
                C * y ^ (-(1 : ℝ) / 2) := by
  classical
  rcases block_residue_reciprocal_prime_uniform_l1 with ⟨Cnum, hCnum, ynum, hynum2, hnum⟩
  rcases step2_block_decomposition with ⟨Cmass, hCmass, ymass, hymass2, hmass⟩
  rcases exp_neg_eventually_le_rpow_neg_half with ⟨Yexp, hYexp1, hExp⟩
  -- Helper for y·exp(-y) ≤ r/something: use poly_times_exp_sqrt_decay with c=1.
  -- Gives: 8·y·exp(-√y) ≤ y^{-1/2} for y ≥ Y8.  For y ≥ 1, exp(-y) ≤ exp(-√y), so
  -- 8·y·exp(-y) ≤ 8·y·exp(-√y) ≤ y^{-1/2} for y ≥ Y8.
  rcases poly_times_exp_sqrt_decay_eventually_le_rpow (C := 8) (c := 1) (by norm_num) (by norm_num)
    with ⟨Y8, hY8⟩
  let Cden : ℝ := Cmass + 1
  -- Final constant: 2 · (Cnum + 1 + Cden + 1)
  let C : ℝ := 2 * (Cnum + 1 + Cden + 1)
  refine ⟨C, by positivity, max ynum (max ymass (max (2 * Cmass) (max Yexp Y8))), ?_, ?_⟩
  · exact hynum2.trans (le_max_left ynum (max ymass (max (2 * Cmass) (max Yexp Y8))))
  intro y hy d hd hdy
  dsimp
  intro k hk
  let B : Finset ℕ := compositeBlock y k
  let D : ℝ := ∑ q ∈ B, (1 : ℝ) / (((q - 1 : ℕ) : ℝ))
  let u : ℝ := (1 : ℝ) / (d.totient : ℝ)
  let r : ℝ := y ^ (-(1 : ℝ) / 2)
  have hy_num : ynum ≤ y :=
    (le_max_left ynum (max ymass (max (2 * Cmass) (max Yexp Y8)))).trans hy
  have hy_mass : ymass ≤ y :=
    (le_trans (le_max_left ymass (max (2 * Cmass) (max Yexp Y8)))
      (le_max_right ynum (max ymass (max (2 * Cmass) (max Yexp Y8))))).trans hy
  have hy_2C : 2 * Cmass ≤ y :=
    (le_trans (le_trans (le_max_left (2 * Cmass) (max Yexp Y8))
      (le_max_right ymass (max (2 * Cmass) (max Yexp Y8))))
      (le_max_right ynum (max ymass (max (2 * Cmass) (max Yexp Y8))))).trans hy
  have hy_Y8 : Y8 ≤ y := by
    have : max Yexp Y8 ≤ max (2 * Cmass) (max Yexp Y8) := le_max_right _ _
    have := this.trans (le_max_right ymass (max (2 * Cmass) (max Yexp Y8)))
    have := this.trans (le_max_right ynum (max ymass (max (2 * Cmass) (max Yexp Y8))))
    have := this.trans hy
    exact (le_max_right Yexp Y8).trans this
  have hy_exp : Yexp ≤ y := by
    have h1 : Yexp ≤ max Yexp Y8 := le_max_left _ _
    have h2 : max Yexp Y8 ≤ max (2 * Cmass) (max Yexp Y8) := le_max_right _ _
    have h3 : max (2 * Cmass) (max Yexp Y8) ≤ max ymass (max (2 * Cmass) (max Yexp Y8)) :=
      le_max_right _ _
    have h4 : max ymass (max (2 * Cmass) (max Yexp Y8)) ≤
        max ynum (max ymass (max (2 * Cmass) (max Yexp Y8))) := le_max_right _ _
    exact (h1.trans h2).trans (h3.trans (h4.trans hy))
  have hy_ge2 : (2 : ℝ) ≤ y := hynum2.trans hy_num
  have hy_pos : 0 < y := by linarith
  have hy_ge1 : (1 : ℝ) ≤ y := by linarith
  have hmass_k : |reciprocalPrimeMass B - 1| ≤ Cmass / y := by
    have hdata := hmass y hy_mass
    dsimp [B] at hdata ⊢
    exact (hdata.2.2 k hk).2
  have hCmass_div_le_one : Cmass / y ≤ 1 := by
    rw [div_le_iff₀ hy_pos]
    nlinarith [hCmass, hy_2C]
  have hCmass_div_le_half : Cmass / y ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hy_pos]
    nlinarith [hCmass, hy_2C]
  have hBmass_le_two : reciprocalPrimeMass B ≤ 2 := by
    have hright := (abs_le.mp hmass_k).2
    linarith
  have hExp' : 4 * Real.exp (-y) ≤ r := by
    simpa [r] using hExp y hy_exp
  have hone_div_le : (1 : ℝ) / y ≤ r := one_div_le_rpow_neg_half hy_ge1
  have hmass_r : Cmass / y ≤ Cmass * r := by
    calc
      Cmass / y = Cmass * ((1 : ℝ) / y) := by ring
      _ ≤ Cmass * r := mul_le_mul_of_nonneg_left hone_div_le hCmass.le
  have hDdiff : |D - reciprocalPrimeMass B| ≤ 4 * Real.exp (-y) := by
    simpa [D, B, reciprocalPrimeMass] using
      (compositeBlock_inv_sub_one_sum_sub_inv_sum_le (y := y) (k := k)
        (S := B) hy_ge2 (by intro q hq; exact hq) hBmass_le_two)
  have hDclose : |D - 1| ≤ Cden * r := by
    calc
      |D - 1| = |(D - reciprocalPrimeMass B) + (reciprocalPrimeMass B - 1)| := by ring_nf
      _ ≤ |D - reciprocalPrimeMass B| + |reciprocalPrimeMass B - 1| :=
        abs_add_le _ _
      _ ≤ 4 * Real.exp (-y) + Cmass / y := add_le_add hDdiff hmass_k
      _ ≤ r + Cmass * r := add_le_add hExp' hmass_r
      _ = Cden * r := by dsimp [Cden]; ring
  have hD_lower : reciprocalPrimeMass B ≤ D := by
    simpa [D, B] using compositeBlock_reciprocalPrimeMass_le_sub_one_sum
      (y := y) (k := k) hy_ge2
  have hmu_ge_half : (1 / 2 : ℝ) ≤ reciprocalPrimeMass B := by
    have hleft := (abs_le.mp hmass_k).1
    linarith
  have hDpos : (1 / 2 : ℝ) ≤ D := hmu_ge_half.trans hD_lower
  have hD_pos : 0 < D := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hDpos
  have hd_pos : 0 < d := by omega
  have hphi_pos_nat : 0 < d.totient := Nat.totient_pos.mpr hd_pos
  have hphi_pos : (0 : ℝ) < (d.totient : ℝ) := by exact_mod_cast hphi_pos_nat
  -- L1 bound on ∑_a |P_a - u|.
  have hl1_P : (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
      |(∑ q ∈ B.filter (fun q => q % d = a % d), (1 : ℝ) / (q : ℝ)) - u|) ≤
      Cnum * r := by
    simpa [B, u, r] using hnum y hy_num d hd hdy k hk
  -- Bound on ∑_a |A_a - P_a| ≤ 4·exp(-y) (uses fact that all q ∈ B are coprime to d
  -- once y ≥ exp(d), which follows from compositeBlock_prime_gt_exp_y).
  -- For each q ∈ B, q is coprime to d (q > exp y ≥ exp d > d, so q ∤ d).
  -- So the sum over a (coprime, in range d) of A_a (= ∑_{q∈B, q≡a%d} 1/(q-1)) collapses
  -- to ∑_{q∈B} 1/(q-1) since each q appears in exactly one a's sum.
  -- Same for P_a.
  have hcoprime_q : ∀ q ∈ B, Nat.Coprime q d := by
    intro q hq
    have hq_prime : q.Prime := compositeBlock_prime hq
    have hy_nn : (0 : ℝ) ≤ y := hy_pos.le
    have hq_gt_exp : Real.exp y < (q : ℝ) := compositeBlock_prime_gt_exp_y hy_nn hq
    have hexp_gt_y : y < Real.exp y := by
      have h := Real.add_one_lt_exp (x := y) (by linarith : y ≠ 0)
      linarith
    have hd_lt_q : (d : ℝ) < (q : ℝ) := by linarith
    have hd_lt_q_nat : d < q := by exact_mod_cast hd_lt_q
    have hnot_dvd : ¬ q ∣ d := fun hdvd =>
      absurd (Nat.le_of_dvd hd_pos hdvd) (not_le.mpr hd_lt_q_nat)
    exact (hq_prime.coprime_iff_not_dvd).mpr hnot_dvd
  -- For each q ∈ B, q % d ∈ Finset.range d AND coprime.
  -- The fiber containing q is {a = q % d}, single-valued.
  -- So ∑_a [filter q%d=a%d] = ∑_q [over q in B, since each q is in exactly one a-fiber].
  -- Per-a bound: |A_a - P_a| ≤ 4·exp(-y), via compositeBlock_inv_sub_one_sum_sub_inv_sum_le
  -- on filtered set (filter ⊆ B).  Then sum over a (φ(d) ≤ y values).
  -- Total: φ(d)·4·exp(-y) ≤ 4·y·exp(-y).
  -- Convert to y^{-1/2} via poly_times_exp_sqrt_decay (since exp(-y) ≤ exp(-√y)).
  have hphi_le_d : (d.totient : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
  have hphi_le_y : (d.totient : ℝ) ≤ y := le_trans hphi_le_d hdy
  have hcoprime_card : (((Finset.range d).filter (fun a => Nat.Coprime a d)).card : ℝ) =
      (d.totient : ℝ) := by
    rw [Nat.totient]
    have hset : (Finset.range d).filter (fun a => Nat.Coprime a d) =
        (Finset.range d).filter (fun a => Nat.Coprime d a) := by
      apply Finset.filter_congr
      intro a _
      exact ⟨Nat.Coprime.symm, Nat.Coprime.symm⟩
    rw [hset]
  have hl1_A_sub_P : (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
      |∑ q ∈ B.filter (fun q => q % d = a % d),
        ((1 : ℝ) / (((q - 1 : ℕ) : ℝ)) - 1 / (q : ℝ))|) ≤
      (d.totient : ℝ) * (4 * Real.exp (-y)) := by
    -- Per-a bound from compositeBlock_inv_sub_one_sum_sub_inv_sum_le.
    have hpw_a : ∀ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
        |∑ q ∈ B.filter (fun q => q % d = a % d),
          ((1 : ℝ) / (((q - 1 : ℕ) : ℝ)) - 1 / (q : ℝ))| ≤ 4 * Real.exp (-y) := by
      intro a _
      have hSsub : B.filter (fun q => q % d = a % d) ⊆ B := Finset.filter_subset _ _
      have h_diff_eq :
          (∑ q ∈ B.filter (fun q => q % d = a % d),
            ((1 : ℝ) / (((q - 1 : ℕ) : ℝ)) - 1 / (q : ℝ))) =
          (∑ q ∈ B.filter (fun q => q % d = a % d),
            (1 : ℝ) / (((q - 1 : ℕ) : ℝ))) -
          ∑ q ∈ B.filter (fun q => q % d = a % d), (1 : ℝ) / (q : ℝ) := by
        rw [← Finset.sum_sub_distrib]
      rw [h_diff_eq]
      simpa using compositeBlock_inv_sub_one_sum_sub_inv_sum_le
        (y := y) (k := k) (S := B.filter (fun q => q % d = a % d))
        hy_ge2 hSsub hBmass_le_two
    calc (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
            |∑ q ∈ B.filter (fun q => q % d = a % d),
              ((1 : ℝ) / (((q - 1 : ℕ) : ℝ)) - 1 / (q : ℝ))|)
        ≤ ∑ _a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
            4 * Real.exp (-y) := Finset.sum_le_sum hpw_a
      _ = (((Finset.range d).filter (fun a => Nat.Coprime a d)).card : ℝ) *
            (4 * Real.exp (-y)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (d.totient : ℝ) * (4 * Real.exp (-y)) := by rw [hcoprime_card]
  -- Combine: ∑_a |A_a - 1/φ(d)| ≤ ∑_a |A_a - P_a| + ∑_a |P_a - 1/φ(d)|
  -- ≤ φ(d)·4·exp(-y) + Cnum·r ≤ 4·y·exp(-y) + Cnum·r.
  -- Then ∑_a |blockCondResProb_a - 1/φ(d)| ≤ 2·(∑_a |A_a - 1/φ(d)| + |D-1|).
  set A_a : ℕ → ℝ := fun a => ∑ q ∈ B.filter (fun q => q % d = a % d),
    (1 : ℝ) / (((q - 1 : ℕ) : ℝ)) with hA_a_def
  set P_a : ℕ → ℝ := fun a => ∑ q ∈ B.filter (fun q => q % d = a % d),
    (1 : ℝ) / (q : ℝ) with hP_a_def
  -- ∑_a |A_a - 1/φ(d)| ≤ ∑_a |A_a - P_a| + ∑_a |P_a - 1/φ(d)|
  have hl1_A : (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
      |A_a a - u|) ≤
      (d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r := by
    calc (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a - u|)
        ≤ ∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
            (|A_a a - P_a a| + |P_a a - u|) := by
          apply Finset.sum_le_sum
          intro a _
          calc |A_a a - u| = |(A_a a - P_a a) + (P_a a - u)| := by ring_nf
            _ ≤ |A_a a - P_a a| + |P_a a - u| := abs_add_le _ _
      _ = (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a - P_a a|) +
          (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |P_a a - u|) := by
          rw [Finset.sum_add_distrib]
      _ ≤ (d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r := by
          have h1 : (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
              |A_a a - P_a a|) ≤ (d.totient : ℝ) * (4 * Real.exp (-y)) := by
            simpa [A_a, P_a] using hl1_A_sub_P
          have h2 : (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
              |P_a a - u|) ≤ Cnum * r := by
            simpa [P_a, u, r] using hl1_P
          linarith
  -- Now ∑_a |blockCondResProb_a - 1/φ(d)|: blockCondResProb_a = A_a/D.
  -- |A_a/D - u| = |A_a - u·D|/D ≤ 2·|A_a - u·D| (using D ≥ 1/2).
  -- |A_a - u·D| ≤ |A_a - u| + u·|D-1|.
  -- ∑_a |A_a/D - u| ≤ 2·(∑_a |A_a - u| + u·φ(d)·|D-1|) = 2·(∑_a |A_a - u| + |D-1|)
  --                ≤ 2·(d.totient · 4·exp(-y) + Cnum·r + Cden·r)
  --                ≤ 2·(y·4·exp(-y) + (Cnum + Cden)·r) ≤ 2·((Cnum + Cden + 1)·r) (for y large).
  have hD_inv_le_two : (1 : ℝ) / D ≤ 2 := by
    rw [div_le_iff₀ hD_pos]
    linarith
  -- u·φ(d) = (1/φ(d))·φ(d) = 1.
  have hu_phi : u * (d.totient : ℝ) = 1 := by
    dsimp [u]
    field_simp
  -- Bound on ∑_a |A_a - u·D|.
  have hl1_A_uD : (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
      |A_a a - u * D|) ≤
      ((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r := by
    calc (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a - u * D|)
        ≤ ∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
            (|A_a a - u| + u * |D - 1|) := by
          apply Finset.sum_le_sum
          intro a _
          calc |A_a a - u * D| = |(A_a a - u) - u * (D - 1)| := by ring_nf
            _ ≤ |A_a a - u| + |u * (D - 1)| := abs_sub _ _
            _ = |A_a a - u| + u * |D - 1| := by
                rw [abs_mul]
                rw [show |u| = u from abs_of_nonneg (by dsimp [u]; positivity)]
      _ = (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a - u|) +
          (((Finset.range d).filter (fun a => Nat.Coprime a d)).card : ℝ) *
            (u * |D - 1|) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      _ = (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a - u|) +
          (d.totient : ℝ) * (u * |D - 1|) := by rw [hcoprime_card]
      _ = (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a - u|) +
          (u * (d.totient : ℝ)) * |D - 1| := by ring
      _ = (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a - u|) +
          1 * |D - 1| := by rw [hu_phi]
      _ = (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a - u|) +
          |D - 1| := by ring
      _ ≤ ((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r := by
          have := hl1_A
          linarith [hDclose]
  -- ∑_a |A_a/D - u| ≤ 2·∑_a |A_a - u·D|.
  have hl1_ratio : (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
      |A_a a / D - u|) ≤
      2 * (((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r) := by
    calc (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a / D - u|)
        = ∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a - u * D| / D := by
          apply Finset.sum_congr rfl
          intro a _
          rw [show A_a a / D - u = (A_a a - u * D) / D by field_simp]
          rw [abs_div]
          rw [show |D| = D from abs_of_pos hD_pos]
      _ = (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a - u * D|) / D := by
          rw [Finset.sum_div]
      _ ≤ (((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r) / D := by
          exact div_le_div_of_nonneg_right hl1_A_uD hD_pos.le
      _ ≤ 2 * (((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r) := by
          rw [div_le_iff₀ hD_pos]
          have hsum_nn : 0 ≤ ((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r := by
            have hr_nn : 0 ≤ r := by dsimp [r]; positivity
            have h1 : 0 ≤ (d.totient : ℝ) * (4 * Real.exp (-y)) := by
              apply mul_nonneg
              · exact_mod_cast Nat.zero_le _
              · positivity
            have h2 : 0 ≤ Cnum * r := mul_nonneg hCnum.le hr_nn
            have h3 : 0 ≤ Cden * r := mul_nonneg (by dsimp [Cden]; linarith) hr_nn
            linarith
          calc (((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r) ≤
              (((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r) * 1 := by linarith
            _ ≤ 2 * (((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r) * D := by
              have h_2D : 1 ≤ 2 * D := by linarith
              nlinarith [hsum_nn, h_2D]
            _ = 2 * (((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r) * D := by ring
  have h8 : 8 * y * Real.exp (-Real.sqrt y) ≤ r := by
    simpa only [neg_one_mul] using hY8 y hy_Y8
  calc (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
        |blockConditionalResidueProbability (compositeBlock y k) d a -
            (1 : ℝ) / (d.totient : ℝ)|)
      = ∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d), |A_a a / D - u| := by
        apply Finset.sum_congr rfl
        intro a _
        unfold blockConditionalResidueProbability
        rfl
    _ ≤ 2 * (((d.totient : ℝ) * (4 * Real.exp (-y)) + Cnum * r) + Cden * r) := hl1_ratio
    _ ≤ C * r := block_l1_error_absorb Cnum Cden y d.totient r
      hy_ge1 hphi_le_y h8 (by dsimp [r]; positivity)


private lemma step5_combined :
    ∃ C : ℝ, 0 < C ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ y →
            let M := compositeBlockCount y
            ∀ k : ℕ, k < M →
              ∀ a : ℕ, Nat.Coprime a d →
                |blockConditionalResidueProbability (compositeBlock y k) d a -
                    (1 : ℝ) / (d.totient : ℝ)| ≤
                  C * y ^ (-(1 : ℝ) / 2) :=
  block_uniform_total_variation_bound


/-- Step 6: application of the subset-product lemma.

Conditioned on having the first `K` good blocks, the near-uniform independent
residue classes from Step 5 fail to contain a nonempty subproduct equal to `1`
with probability at most `N / (2^K - 1) + K ε_y`, where
`N = φ(d) = |(Z/dZ)ˣ| ≤ y`. -/
private lemma step6_subset_product_application
    {K : ℕ} (hK : 1 ≤ K) {y : ℝ} {d : ℕ} [NeZero d]
    (_hd : 2 ≤ d) (hdy : (d : ℝ) ≤ y)
    (ε_y : ℝ) (hε_y : 0 ≤ ε_y)
    (μ : (Fin K → (ZMod d)ˣ) → ℝ)
    (hμ_nonneg : ∀ g, 0 ≤ μ g)
    (hμ_sum : (∑ g : Fin K → (ZMod d)ˣ, μ g) = 1)
    (hμ_near :
      (∑ g : Fin K → (ZMod d)ˣ,
        |μ g - 1 / ((d.totient : ℝ) ^ K)|) ≤ (K : ℝ) * ε_y) :
    let N := d.totient
    (∑ g ∈ Finset.univ.filter
        (fun g : Fin K → (ZMod d)ˣ =>
          ∀ S : Finset (Fin K), S.Nonempty → subsetProd S g ≠ 1),
        μ g) ≤
      (N : ℝ) / ((2 : ℝ) ^ K - 1) + (K : ℝ) * ε_y ∧
    (N : ℝ) ≤ y := by
  classical
  -- Paper §6.2 Step 6, using the near-uniform corollary of
  -- `subset_product_main` on the finite unit group `(Z/dZ)ˣ`.
  dsimp
  constructor
  · have hcard : Fintype.card (ZMod d)ˣ = d.totient := ZMod.card_units_eq_totient d
    have hμ_near' :
        (∑ g : Fin K → (ZMod d)ˣ,
          |μ g - 1 / ((Fintype.card (ZMod d)ˣ : ℝ) ^ K)|) ≤ (K : ℝ) * ε_y := by
      simpa [hcard] using hμ_near
    simpa [hcard] using
      (subset_product_near_uniform (G := (ZMod d)ˣ) hK ε_y hε_y μ hμ_nonneg hμ_sum
        hμ_near')
  · have htotient_le_d : (d.totient : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast Nat.totient_le d
    exact htotient_le_d.trans hdy

/-! ### Step 7: residue-density form (Paper §6.2 Step 7).

**Paper §6.2 Lemma 6.2 (Composite Successor Lemma) — residue-density form.**

This is the central technical result of paper §6.2.  The product-model statement
(paper line 1517-1525): for absolute constants `A > 10`, `c > 0`, and `y₀ ≥ 2`,
all `y ≥ y₀`, and `1 ≤ d ≤ y`, the probability in the independent prime model
that no admissible squarefree product `e ≡ 1 (mod d)` of selected window primes
exists is `O(y^{-c})`.

The proof in paper §6.2 is the seven-step argument:
  Step 1 (Mertens-window mass) — proved (`step1_mertens_window_mass`).
  Step 2 (block decomposition) — proved (`step2_block_decomposition`).
  Step 3 (good-block probability ≈ e^{-1}) — proved (`step3_good_block_probability`).
  Step 4 (Chernoff for good-block count) — proved (`step4_chernoff_good_blocks`).
  Step 5 (conditional residue uniformity) — proved (`step5_conditional_residue`).
  Step 6 (subset-product application) — proved (`step6_subset_product_application`).
  Step 7 (combine with `K = ⌈(e⁻¹·15/2) log y⌉`, residue-density form).

Steps 1-6 are all formally proven inside this file.  Step 7 (assembly) is
also formally proven via `step7_residue_density_bound` and
`step7_combine_and_crt_transfer` below.  These bridge `finitePrimeModelProb`
to the residue-density form via `pmodel_composite_product_failure_bound`
(the d=1 and d≥2 sub-cases) and the existing periodicity infrastructure
(`composite_successor_bad_count_le_periodic`).

Constant `1/2` factor on the RHS makes the `M`-period bookkeeping in
`step7_combine_and_crt_transfer` work without further loss. -/
/-! #### Sub-claims for the residue-density bound

The bound is reduced to three named sub-claims that together capture paper §6.2
Step 7 combined with the residue-density bridge.  Each sub-claim is paper-faithful
and self-contained. -/

-- Helper: window primes are coprime to d, since each prime q ∈ window satisfies
-- q > exp y ≥ y ≥ d, so q > d, hence (since q is prime) q ∤ d, hence Coprime.
private lemma compositePrimeWindow_coprime_d {y : ℝ} (hy : 2 ≤ y)
    {d : ℕ} (hd : 1 ≤ d) (hd_le_y : (d : ℝ) ≤ y)
    {q : ℕ} (hq : q ∈ compositePrimeWindow 20 y) :
    Nat.Coprime q d := by
  unfold compositePrimeWindow at hq
  rw [Finset.mem_filter] at hq
  obtain ⟨_, hq_prime, hq_gt_exp_y, _⟩ := hq
  have hy_ne : y ≠ 0 := by linarith
  have h_y_lt_exp_y : y < Real.exp y := by
    have h := Real.add_one_lt_exp hy_ne
    linarith
  have hq_gt_d_real : (d : ℝ) < q := by
    calc (d : ℝ) ≤ y := hd_le_y
      _ < Real.exp y := h_y_lt_exp_y
      _ < (q : ℝ) := hq_gt_exp_y
  have hd_pos : 0 < d := hd
  have hq_not_dvd : ¬ q ∣ d := by
    intro hq_dvd_d
    have hq_le_d := Nat.le_of_dvd hd_pos hq_dvd_d
    have : (q : ℝ) ≤ (d : ℝ) := by exact_mod_cast hq_le_d
    linarith
  exact (Nat.Prime.coprime_iff_not_dvd hq_prime).mpr hq_not_dvd

-- Helper: for a window prime q (coprime to d), q ∣ (d * r') iff q ∣ r'.
-- This is the key fact for the CRT bridge: window-prime divisibility of r = d · r'
-- is determined entirely by r'.
private lemma admissible_subset_window {y : ℝ} {d : ℕ} {T : Finset ℕ}
    (hT : AdmissibleCompositeProduct 20 y d T) :
    T ⊆ compositePrimeWindow 20 y := by
  intro q hqT
  obtain ⟨_hT_ne, hprimes, _⟩ := hT
  obtain ⟨hq_prime, hq_gt, hq_le⟩ := hprimes q hqT
  rw [compositePrimeWindow, Finset.mem_filter, Finset.mem_Iic]
  refine ⟨?_, hq_prime, hq_gt, hq_le⟩
  exact Nat.le_floor hq_le

-- Helper: for an admissible product T (whose primes lie in the window) and d coprime to those primes,
-- ∏T is coprime to d.  Used to show ∏T ∣ (d · r') ↔ ∏T ∣ r'.
private lemma admissibleProduct_coprime_d {y : ℝ} (hy : 2 ≤ y)
    {d : ℕ} (hd : 1 ≤ d) (hd_le_y : (d : ℝ) ≤ y)
    {T : Finset ℕ} (hT : AdmissibleCompositeProduct 20 y d T) :
    Nat.Coprime (∏ q ∈ T, q) d := by
  apply Nat.Coprime.prod_left
  intro q hq
  exact compositePrimeWindow_coprime_d hy hd hd_le_y (admissible_subset_window hT hq)

-- Helper: for a finset T of primes, ∏T divides n iff each prime q ∈ T divides n.
-- Forward: q ∣ ∏T (since q ∈ T) and ∏T ∣ n.  Backward: Finset.prod_primes_dvd.
private lemma finset_primes_prod_dvd_iff (T : Finset ℕ) (n : ℕ)
    (hT_prime : ∀ q ∈ T, q.Prime) :
    (∏ q ∈ T, q) ∣ n ↔ ∀ q ∈ T, q ∣ n := by
  constructor
  · intro hprod q hqT
    exact dvd_trans (Finset.dvd_prod_of_mem _ hqT) hprod
  · intro hall
    apply Finset.prod_primes_dvd
    · intro a ha
      exact (hT_prime a ha).prime
    · exact hall

-- Helper: GoodCompositeSuccessor 20 y d (d * r') iff GoodCompositeSuccessor 20 y d r'.
-- Since admissible products consist of window primes (all coprime to d), divisibility
-- of d · r' by ∏T equals divisibility of r' by ∏T.
private lemma goodCompositeSuccessor_mul_d_iff {y : ℝ} (hy : 2 ≤ y)
    {d : ℕ} (hd : 1 ≤ d) (hd_le_y : (d : ℝ) ≤ y) (r' : ℕ) :
    GoodCompositeSuccessor 20 y d (d * r') ↔ GoodCompositeSuccessor 20 y d r' := by
  unfold GoodCompositeSuccessor
  constructor
  · rintro ⟨T, hT_admissible, hT_dvd⟩
    refine ⟨T, hT_admissible, ?_⟩
    have hcop := admissibleProduct_coprime_d hy hd hd_le_y hT_admissible
    exact hcop.dvd_mul_left.mp hT_dvd
  · rintro ⟨T, hT_admissible, hT_dvd⟩
    refine ⟨T, hT_admissible, ?_⟩
    have hcop := admissibleProduct_coprime_d hy hd hd_le_y hT_admissible
    exact hcop.dvd_mul_left.mpr hT_dvd

-- Helper: GoodCompositeSuccessor 20 y d r' iff CompositeProductExists 20 y d S
-- where S = {q ∈ window : q ∣ r'}.  Encodes that "good successor for r'" means
-- the selected window primes (those dividing r') form an admissible product.
private lemma goodCompositeSuccessor_iff_productExists_filter (y : ℝ) (d r' : ℕ) :
    GoodCompositeSuccessor 20 y d r' ↔
    CompositeProductExists 20 y d ((compositePrimeWindow 20 y).filter (fun q => q ∣ r')) := by
  unfold GoodCompositeSuccessor CompositeProductExists
  constructor
  · rintro ⟨T, hT_admissible, hT_dvd⟩
    refine ⟨T, ?_, hT_admissible⟩
    intro q hqT
    rw [Finset.mem_filter]
    refine ⟨admissible_subset_window hT_admissible hqT, ?_⟩
    exact dvd_trans (Finset.dvd_prod_of_mem _ hqT) hT_dvd
  · rintro ⟨T, hT_sub_filter, hT_admissible⟩
    refine ⟨T, hT_admissible, ?_⟩
    obtain ⟨_hT_ne, hprimes, _⟩ := hT_admissible
    have hT_all_dvd : ∀ q ∈ T, q ∣ r' := by
      intro q hqT
      have := hT_sub_filter hqT
      rw [Finset.mem_filter] at this
      exact this.2
    have hT_all_prime : ∀ q ∈ T, q.Prime := fun q hqT => (hprimes q hqT).1
    exact (finset_primes_prod_dvd_iff T r' hT_all_prime).mpr hT_all_dvd

-- Bridge moved below after `coreBad_card_eq_no_good_quotient` (at ~line 3858+) since it
-- depends on that helper.  See `residue_density_le_pmodel_bridge` below.

-- Helper: bridge between `Nat.card {r : Fin M // P r.val}` and Finset filter card.
-- (LBL has `fin_card_subtype_eq_range_filter_card` which is private; re-prove for CS.)
private lemma cs_fin_card_subtype_eq_range_filter_card {M : ℕ} (P : ℕ → Prop)
    [DecidablePred P] :
    Nat.card {r : Fin M // P r.val} =
      ((Finset.range M).filter P).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.subtype_card]
  apply Finset.card_bij (fun (r : Fin M) (_ : r ∈ (Finset.univ : Finset (Fin M)).filter
        (fun r : Fin M => P r.val)) => r.val)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨r.isLt, hr⟩
  · intro r _hr r' _hr' h
    exact Fin.ext h
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv
    refine ⟨⟨v, hv.1⟩, ?_, rfl⟩
    simp [Finset.mem_filter, hv.2]

-- Helper: count of multiples of d in [0, d*P) = P.
-- Standard counting fact, used in Step A of the CRT bridge:
-- {r ∈ Fin (d * P) : d ∣ r} ≃ Fin P via r ↦ r/d.
lemma card_filter_dvd_range_mul {d P : ℕ} (hd_pos : 0 < d) (Q : ℕ → Prop)
    [DecidablePred Q] :
    ((Finset.range (d * P)).filter (fun r => d ∣ r ∧ Q r)).card =
    ((Finset.range P).filter (fun k => Q (d * k))).card := by
  classical
  apply Finset.card_bij (fun r _ => r / d)
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr ⊢
    obtain ⟨hr_lt, hd_dvd_r, hQr⟩ := hr
    refine ⟨?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hd_pos]; linarith
    · rw [Nat.mul_div_cancel' hd_dvd_r]; exact hQr
  · intro r₁ hr₁ r₂ hr₂ heq
    rw [Finset.mem_filter] at hr₁ hr₂
    have hd_dvd_r₁ := hr₁.2.1
    have hd_dvd_r₂ := hr₂.2.1
    rw [show r₁ = d * (r₁ / d) from (Nat.mul_div_cancel' hd_dvd_r₁).symm,
        show r₂ = d * (r₂ / d) from (Nat.mul_div_cancel' hd_dvd_r₂).symm, heq]
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk_lt, hQ⟩ := hk
    refine ⟨d * k, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mul_lt_mul_of_pos_left hk_lt hd_pos, dvd_mul_right d k, hQ⟩
    · exact Nat.mul_div_cancel_left k hd_pos

-- Helper: primorial P > 0 (LBL has private version; re-prove for CS).
private lemma cs_primorial_pos (P : ℕ) : 0 < primorial P := by
  unfold primorial
  exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)

-- Helper: distinct primes in a finset are pairwise coprime.
-- Used in primorial CRT decomposition (`ZMod.prodEquivPi`).
private lemma compositePrimeWindow_subset_primesIic_cutoff {y : ℝ} (hy : 1 ≤ y) :
    compositePrimeWindow 20 y ⊆
      (Finset.Iic (compositeSuccessorCutoff 20 y)).filter Nat.Prime := by
  intro q hq
  unfold compositePrimeWindow at hq
  rw [Finset.mem_filter, Finset.mem_Iic] at hq
  obtain ⟨_, hq_prime, _, hq_le_exp_y19⟩ := hq
  rw [Finset.mem_filter, Finset.mem_Iic]
  refine ⟨?_, hq_prime⟩
  -- Need: q ≤ ⌊exp(y^20)⌋₊.  We have (q : ℝ) ≤ exp(y^(A-1)) = exp(y^19) ≤ exp(y^20).
  unfold compositeSuccessorCutoff
  have hy19_le_y20 : y ^ ((20 : ℝ) - 1) ≤ y ^ ((20 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  have hexp_le : Real.exp (y ^ ((20 : ℝ) - 1)) ≤ Real.exp (y ^ ((20 : ℝ))) :=
    Real.exp_le_exp.mpr hy19_le_y20
  have hq_le_exp_y20 : (q : ℝ) ≤ Real.exp (y ^ ((20 : ℝ))) :=
    hq_le_exp_y19.trans hexp_le
  exact Nat.le_floor hq_le_exp_y20

-- Helper: combine card_filter_dvd_range_mul + goodCompositeSuccessor_mul_d_iff.
-- The count of CoreBad residues in [0, d * P) equals the count of "no good successor" in [0, P).
open Classical in
lemma coreBad_card_eq_no_good_quotient {y : ℝ} (hy : 2 ≤ y)
    {d P : ℕ} (hd : 1 ≤ d) (hd_le_y : (d : ℝ) ≤ y) :
    ((Finset.range (d * P)).filter
        (fun r => CompositeSuccessorCoreBad 20 y d r)).card =
    ((Finset.range P).filter
        (fun k => ¬ GoodCompositeSuccessor 20 y d k)).card := by
  -- Direct bijection: r ↦ r/d sends {r : CoreBad} to {k : ¬ GoodCompositeSuccessor}.
  apply Finset.card_bij (fun r _ => r / d)
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hr_lt, hd_dvd_r, hngood⟩ := hr
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨(Nat.div_lt_iff_lt_mul hd).mpr (by linarith), ?_⟩
    rw [show r = d * (r / d) from (Nat.mul_div_cancel' hd_dvd_r).symm] at hngood
    rwa [goodCompositeSuccessor_mul_d_iff hy hd hd_le_y] at hngood
  · intro r₁ hr₁ r₂ hr₂ heq
    rw [Finset.mem_filter] at hr₁ hr₂
    have hd_dvd_r₁ := hr₁.2.1
    have hd_dvd_r₂ := hr₂.2.1
    rw [show r₁ = d * (r₁ / d) from (Nat.mul_div_cancel' hd_dvd_r₁).symm,
        show r₂ = d * (r₂ / d) from (Nat.mul_div_cancel' hd_dvd_r₂).symm, heq]
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk_lt, hngood_k⟩ := hk
    refine ⟨d * k, ?_, Nat.mul_div_cancel_left k hd⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mul_lt_mul_of_pos_left hk_lt hd, dvd_mul_right d k, ?_⟩
    rwa [goodCompositeSuccessor_mul_d_iff hy hd hd_le_y]

-- step_b and bridge moved AFTER `compositeProductFailure_d_1_iff_empty` since they need it.

-- Helper: pmodel probability of "S is empty" equals product of (1 - 1/q).
private lemma finitePrimeModelProb_eq_empty (U : Finset ℕ) :
    finitePrimeModelProb U (fun S => S = ∅) =
      ∏ q ∈ U, (1 - (1 : ℝ) / (q : ℝ)) := by
  classical
  unfold finitePrimeModelProb
  rw [Finset.sum_filter]
  rw [Finset.sum_eq_single (∅ : Finset ℕ)]
  · rw [if_pos rfl]
    unfold selectionWeight
    apply Finset.prod_congr rfl
    intro q _hq
    simp
  · intros S _hS hSne
    rw [if_neg hSne]
  · intro hne
    exact absurd (Finset.empty_mem_powerset U) hne

-- Helper: For d=1, CompositeProductFailure iff S = ∅ (paper §6.2 line 1551-1552).
-- Any single window prime q satisfies all admissibility conditions for T := {q}.
private lemma compositeProductFailure_d_1_iff_empty {y : ℝ} (hy : 1 ≤ y)
    {S : Finset ℕ} (hS : S ⊆ compositePrimeWindow 20 y) :
    CompositeProductFailure 20 y 1 S ↔ S = ∅ := by
  unfold CompositeProductFailure CompositeProductExists
  constructor
  · intro hfail
    by_contra hSne
    have hSnonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSne
    obtain ⟨q, hqS⟩ := hSnonempty
    apply hfail
    have hq_window : q ∈ compositePrimeWindow 20 y := hS hqS
    unfold compositePrimeWindow at hq_window
    rw [Finset.mem_filter] at hq_window
    obtain ⟨_, hq_prime, hq_gt_exp_y, hq_le_exp_y19⟩ := hq_window
    refine ⟨{q}, Finset.singleton_subset_iff.mpr hqS, ?_⟩
    refine ⟨Finset.singleton_nonempty q, ?_, ?_, ?_, ?_⟩
    · intro q' hq'
      rw [Finset.mem_singleton] at hq'
      subst hq'
      exact ⟨hq_prime, hq_gt_exp_y, hq_le_exp_y19⟩
    · simp [Nat.ModEq, Nat.mod_one]
    · rw [Finset.prod_singleton]; exact hq_prime.one_lt
    · rw [Finset.prod_singleton]
      have hy19_le_y20 : y ^ ((20 : ℝ) - 1) ≤ y ^ ((20 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
      exact hq_le_exp_y19.trans (Real.exp_le_exp.mpr hy19_le_y20)
  · rintro hS_empty ⟨T, hT_sub, hT_admissible⟩
    rw [hS_empty, Finset.subset_empty] at hT_sub
    have hT_nonempty := hT_admissible.1
    rw [hT_sub] at hT_nonempty
    exact hT_nonempty.ne_empty rfl

-- Helper A: pattern equivalence — `Q.filter (· ∣ r) = S` iff every prime in `S` divides `r`
-- and no prime in `Q \ S` divides `r`.  Used in the CRT count formula below.
private lemma cs_pattern_iff_dvd_and_avoid {Q : Finset ℕ} {S : Finset ℕ} (hSQ : S ⊆ Q)
    (r : ℕ) :
    Q.filter (fun q => q ∣ r) = S ↔
      (∀ q ∈ S, q ∣ r) ∧ (∀ q ∈ Q \ S, ¬ q ∣ r) := by
  classical
  constructor
  · intro hpat
    refine ⟨fun q hqS => ?_, fun q hqdiff hqdvd => ?_⟩
    · have : q ∈ Q.filter (fun q => q ∣ r) := hpat ▸ hqS
      rw [Finset.mem_filter] at this
      exact this.2
    · rw [Finset.mem_sdiff] at hqdiff
      have : q ∈ Q.filter (fun q => q ∣ r) := by
        rw [Finset.mem_filter]; exact ⟨hqdiff.1, hqdvd⟩
      rw [hpat] at this
      exact hqdiff.2 this
  · rintro ⟨hS_dvd, hSc_ndvd⟩
    ext q
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hqQ, hqdvd⟩
      by_contra hqS
      exact hSc_ndvd q (Finset.mem_sdiff.mpr ⟨hqQ, hqS⟩) hqdvd
    · intro hqS
      exact ⟨hSQ hqS, hS_dvd q hqS⟩

-- Helper B: CRT count formula (per-S equality).  For `Q` a set of distinct primes
-- with `∏Q ∣ M`, and `S ⊆ Q`:
-- count of `r ∈ Fin M` with `Q.filter (· ∣ r) = S` equals `M · selectionWeight Q S`.
-- This is the d-general analog of `pmodel_count_avoid_primes_eq` (which is the `S = ∅` case).
private lemma cs_count_pattern_eq_M_selectionWeight
    {Q : Finset ℕ} (hQ_prime : ∀ q ∈ Q, q.Prime)
    {M : ℕ} (hMpos : 0 < M)
    (hprodQ_dvd : (∏ q ∈ Q, q) ∣ M)
    {S : Finset ℕ} (hSQ : S ⊆ Q) :
    (((Finset.range M).filter
        (fun r => Q.filter (fun q => q ∣ r) = S)).card : ℝ) =
      (M : ℝ) * selectionWeight Q S := by
  classical
  set N : ℕ := ∏ q ∈ S, q with hN_def
  have hS_prime : ∀ q ∈ S, q.Prime := fun q hq => hQ_prime q (hSQ hq)
  have hQS_prime : ∀ q ∈ Q \ S, q.Prime := fun q hq => hQ_prime q (Finset.mem_sdiff.mp hq).1
  have hN_pos : 0 < N := Finset.prod_pos (fun q hq => (hS_prime q hq).pos)
  have hN_dvd_M : N ∣ M :=
    dvd_trans (Finset.prod_dvd_prod_of_subset S Q (fun q => q) hSQ) hprodQ_dvd
  obtain ⟨K, hM_eq⟩ := hN_dvd_M
  have hK_pos : 0 < K := by
    by_contra hKne
    push_neg at hKne
    interval_cases K
    rw [hM_eq] at hMpos
    simp at hMpos
  -- Step 1: rewrite the filter condition using helper A and `finset_primes_prod_dvd_iff`.
  have hfilter_eq :
      (Finset.range M).filter (fun r => Q.filter (fun q => q ∣ r) = S) =
        (Finset.range M).filter (fun r => N ∣ r ∧ ∀ q ∈ Q \ S, ¬ q ∣ r) := by
    apply Finset.filter_congr
    intro r _hr
    rw [cs_pattern_iff_dvd_and_avoid hSQ]
    have h1 : (∀ q ∈ S, q ∣ r) ↔ N ∣ r :=
      (finset_primes_prod_dvd_iff S r hS_prime).symm
    rw [h1]
  rw [hfilter_eq, hM_eq]
  -- Step 2: Bijection `r ↔ r/N` between {r ∈ Fin (N · K) : N ∣ r ∧ avoid} and
  -- {r' ∈ Fin K : avoid (N · r')} via `card_filter_dvd_range_mul`.
  rw [card_filter_dvd_range_mul hN_pos]
  -- Step 3: For `q ∈ Q \ S`, `q ∣ (N * r') ↔ q ∣ r'` since `q` is coprime to `N`.
  have hN_factored : ∀ q ∈ Q \ S, Nat.Coprime q N := by
    intro q hq
    rw [Finset.mem_sdiff] at hq
    have hq_prime : q.Prime := hQ_prime q hq.1
    rw [hN_def]
    apply Nat.Coprime.prod_right
    intro p hp
    have hp_prime : p.Prime := hS_prime p hp
    have hpq : q ≠ p := fun hpq_eq => hq.2 (hpq_eq ▸ hp)
    exact (Nat.coprime_primes hq_prime hp_prime).mpr hpq
  have hfilter_eq2 :
      (Finset.range K).filter (fun k => ∀ q ∈ Q \ S, ¬ q ∣ (N * k)) =
        (Finset.range K).filter (fun k => ∀ q ∈ Q \ S, ¬ q ∣ k) := by
    apply Finset.filter_congr
    intro k _hk
    have h_each : ∀ q ∈ Q \ S, q ∣ (N * k) ↔ q ∣ k := by
      intro q hq
      have hq_cop_N : Nat.Coprime q N := hN_factored q hq
      constructor
      · intro h
        exact (Nat.Coprime.dvd_of_dvd_mul_left hq_cop_N h)
      · intro h
        exact h.mul_left N
    constructor
    · intro h q hq; rw [← h_each q hq]; exact h q hq
    · intro h q hq; rw [h_each q hq]; exact h q hq
  rw [hfilter_eq2]
  -- Step 4: Apply `pmodel_count_avoid_primes_eq` on `Q \ S` with modulus `K`.
  have hPQS_dvd_K : (∏ q ∈ Q \ S, q) ∣ K := by
    have hSdQ_eq : S ∪ (Q \ S) = Q := by
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hx | hx)
        · exact hSQ hx
        · exact hx.1
      · intro hx
        by_cases hxS : x ∈ S
        · exact Or.inl hxS
        · exact Or.inr ⟨hx, hxS⟩
    have hSdQ_disj : Disjoint S (Q \ S) := Finset.disjoint_sdiff
    have hProdQ_split : (∏ q ∈ Q, q) = N * ∏ q ∈ Q \ S, q := by
      rw [hN_def]
      conv_lhs => rw [show Q = S ∪ (Q \ S) from hSdQ_eq.symm]
      rw [Finset.prod_union hSdQ_disj]
    have : N * (∏ q ∈ Q \ S, q) ∣ M := hProdQ_split ▸ hprodQ_dvd
    rw [hM_eq] at this
    exact (Nat.mul_dvd_mul_iff_left hN_pos).mp this
  rw [pmodel_count_avoid_primes_eq hQS_prime hK_pos hPQS_dvd_K]
  -- Step 5: Algebraic equality.  K · ∏_{Q\S}(1-1/q) = M · selectionWeight Q S,
  -- using M = N · K and N · ∏_S (1/q) = 1.
  rw [selectionWeight_eq_prod_sdiff Q S hSQ]
  have hN_prod_inv :
      (N : ℝ) * (∏ q ∈ S, (1 : ℝ) / (q : ℝ)) = 1 := by
    rw [hN_def]
    push_cast
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro q hq
    have hq_pos : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast (hS_prime q hq).pos
    field_simp
  push_cast
  -- Goal: (↑K) * ∏_{Q\S}(1-1/q) = (↑N * ↑K) * ((∏_S 1/q) * ∏_{Q\S}(1-1/q))
  -- Reassociate so (↑N * ∏_S 1/q) appears, then rewrite to 1.
  have heq : ((N : ℝ) * (K : ℝ)) *
      ((∏ q ∈ S, (1 : ℝ) / (q : ℝ)) * ∏ q ∈ Q \ S, (1 - (1 : ℝ) / (q : ℝ))) =
      ((N : ℝ) * ∏ q ∈ S, (1 : ℝ) / (q : ℝ)) *
        ((K : ℝ) * ∏ q ∈ Q \ S, (1 - (1 : ℝ) / (q : ℝ))) := by ring
  rw [heq, hN_prod_inv, one_mul]

-- d ≥ 2 sub-claim of Step B (paper §6.2 lines 1556-1816).
-- Proof: rewrite ¬Good d r' as Failure d (window.filter (· ∣ r'))
-- (`goodCompositeSuccessor_iff_productExists_filter`), partition count by pattern S,
-- apply per-pattern CRT count `cs_count_pattern_eq_M_selectionWeight`, sum to obtain
-- M · ∑_{S : Failure d S} selectionWeight Q S = M · finitePrimeModelProb.
-- This gives EQUALITY (stronger than the required ≤).
open Classical in
private lemma step_b_count_no_good_le_primorial_pmodel_d_ge_2 {y : ℝ} (hy : 2 ≤ y)
    {d : ℕ} (_hd_ge_2 : 2 ≤ d) (_hd_le_y : (d : ℝ) ≤ y) :
    (((Finset.range (primorial (compositeSuccessorCutoff 20 y))).filter
        (fun r' => ¬ GoodCompositeSuccessor 20 y d r')).card : ℝ) ≤
      (primorial (compositeSuccessorCutoff 20 y) : ℝ) *
        finitePrimeModelProb (compositePrimeWindow 20 y)
          (CompositeProductFailure 20 y d) := by
  classical
  set Q : Finset ℕ := compositePrimeWindow 20 y with hQ_def
  set M : ℕ := primorial (compositeSuccessorCutoff 20 y) with hM_def
  have hM_pos : 0 < M := cs_primorial_pos _
  have hQ_prime : ∀ q ∈ Q, q.Prime := by
    intro q hq
    rw [hQ_def] at hq
    unfold compositePrimeWindow at hq
    rw [Finset.mem_filter] at hq
    exact hq.2.1
  have hprodQ_dvd_M : (∏ q ∈ Q, q) ∣ M := by
    rw [hQ_def, hM_def]
    unfold primorial
    exact Finset.prod_dvd_prod_of_subset _ _ (fun q => q)
      (compositePrimeWindow_subset_primesIic_cutoff (by linarith))
  -- Step 1: rewrite ¬Good as Failure on the pattern (window.filter (· ∣ r')).
  have hfilter_ngood :
      (Finset.range M).filter (fun r' => ¬ GoodCompositeSuccessor 20 y d r') =
      (Finset.range M).filter (fun r' =>
        CompositeProductFailure 20 y d (Q.filter (fun q => q ∣ r'))) := by
    apply Finset.filter_congr
    intro r' _hr'
    rw [hQ_def]
    have h := goodCompositeSuccessor_iff_productExists_filter y d r'
    unfold CompositeProductFailure
    constructor
    · intro h_neg h_pos
      exact h_neg (h.mpr h_pos)
    · intro h_pos h_neg
      exact h_pos (h.mp h_neg)
  rw [hfilter_ngood]
  -- Step 2: partition count by pattern S = Q.filter (· ∣ r').
  set s : Finset ℕ := (Finset.range M).filter (fun r' =>
    CompositeProductFailure 20 y d (Q.filter (fun q => q ∣ r'))) with hs_def
  set t : Finset (Finset ℕ) :=
    Q.powerset.filter (CompositeProductFailure 20 y d) with ht_def
  have hMaps : (s : Set ℕ).MapsTo (fun r' => Q.filter (fun q => q ∣ r')) t := by
    intro r' hr'
    rw [Finset.mem_coe] at hr'
    show Q.filter (fun q => q ∣ r') ∈ (t : Finset (Finset ℕ))
    rw [hs_def, Finset.mem_filter] at hr'
    rw [ht_def, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ Q, hr'.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hMaps]
  push_cast
  -- Step 3: each fiber `{r' ∈ s : pattern r' = S}` equals `{r' ∈ range M : pattern r' = S}`,
  -- since for S ∈ t we have Failure d S.
  have hfiber_eq : ∀ S ∈ t,
      ((s.filter (fun r' => Q.filter (fun q => q ∣ r') = S)).card : ℝ) =
        ((Finset.range M).filter (fun r' => Q.filter (fun q => q ∣ r') = S)).card := by
    intro S hS
    rw [ht_def, Finset.mem_filter] at hS
    have hfilt :
        s.filter (fun r' => Q.filter (fun q => q ∣ r') = S) =
        (Finset.range M).filter (fun r' => Q.filter (fun q => q ∣ r') = S) := by
      ext r'
      simp only [hs_def, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨hr_lt, _⟩, hpat⟩; exact ⟨hr_lt, hpat⟩
      · rintro ⟨hr_lt, hpat⟩
        refine ⟨⟨hr_lt, ?_⟩, hpat⟩
        rw [hpat]; exact hS.2
    rw [hfilt]
  rw [Finset.sum_congr rfl hfiber_eq]
  -- Step 4: apply Helper B `cs_count_pattern_eq_M_selectionWeight` per pattern.
  have hbound_pat : ∀ S ∈ t,
      (((Finset.range M).filter (fun r' => Q.filter (fun q => q ∣ r') = S)).card : ℝ) =
      (M : ℝ) * selectionWeight Q S := by
    intro S hS
    rw [ht_def, Finset.mem_filter, Finset.mem_powerset] at hS
    exact cs_count_pattern_eq_M_selectionWeight hQ_prime hM_pos hprodQ_dvd_M hS.1
  rw [Finset.sum_congr rfl hbound_pat]
  -- Step 5: factor out M.  ∑_{S ∈ t} M · selectionWeight Q S = M · ∑_{S ∈ t} selectionWeight Q S
  -- = M · finitePrimeModelProb Q (Failure d).
  rw [← Finset.mul_sum]
  rfl

-- Step B: count of "no good successor" in Fin (primorial cutoff) ≤ primorial · pmodel_prob.
-- d=1 case: closed via `pmodel_count_avoid_primes_eq` (LBL) since ¬ Good iff S=∅ iff
--           ∀ q ∈ window, ¬ q ∣ r' (paper §6.2 line 1551-1552).
-- d ≥ 2 case: deferred to `step_b_count_no_good_le_primorial_pmodel_d_ge_2`.
open Classical in
private lemma step_b_count_no_good_le_primorial_pmodel {y : ℝ} (hy : 2 ≤ y)
    {d : ℕ} (hd : 1 ≤ d) (hd_le_y : (d : ℝ) ≤ y) :
    (((Finset.range (primorial (compositeSuccessorCutoff 20 y))).filter
        (fun r' => ¬ GoodCompositeSuccessor 20 y d r')).card : ℝ) ≤
      (primorial (compositeSuccessorCutoff 20 y) : ℝ) *
        finitePrimeModelProb (compositePrimeWindow 20 y)
          (CompositeProductFailure 20 y d) := by
  by_cases hd1 : d = 1
  · subst hd1
    -- d=1 case: ¬ GoodCompositeSuccessor 20 y 1 r' ↔ ∀ q ∈ window, ¬ q ∣ r' (paper line 1551-1552).
    have hwindow_prime : ∀ q ∈ compositePrimeWindow 20 y, q.Prime := by
      intro q hq
      unfold compositePrimeWindow at hq
      rw [Finset.mem_filter] at hq
      exact hq.2.1
    have hwindow_dvd_primorial :
        (∏ q ∈ compositePrimeWindow 20 y, q) ∣ primorial (compositeSuccessorCutoff 20 y) := by
      unfold primorial
      apply Finset.prod_dvd_prod_of_subset
      exact compositePrimeWindow_subset_primesIic_cutoff (by linarith)
    have hprimorial_pos : 0 < primorial (compositeSuccessorCutoff 20 y) := cs_primorial_pos _
    -- Rewrite filter using the d=1 equivalence: ¬ Good 1 r' iff ∀ q ∈ window, ¬ q ∣ r'.
    have hfilter_eq :
        ((Finset.range (primorial (compositeSuccessorCutoff 20 y))).filter
            (fun r' => ¬ GoodCompositeSuccessor 20 y 1 r')) =
        ((Finset.range (primorial (compositeSuccessorCutoff 20 y))).filter
            (fun r' => ∀ q ∈ compositePrimeWindow 20 y, ¬ q ∣ r')) := by
      apply Finset.filter_congr
      intro r' _hr'
      rw [goodCompositeSuccessor_iff_productExists_filter]
      have hfilter_sub : ((compositePrimeWindow 20 y).filter (fun q => q ∣ r')) ⊆
          compositePrimeWindow 20 y := Finset.filter_subset _ _
      change CompositeProductFailure 20 y 1 _ ↔ _
      rw [compositeProductFailure_d_1_iff_empty (by linarith) hfilter_sub]
      constructor
      · intro h_empty q hq h_div
        have : q ∈ (compositePrimeWindow 20 y).filter (fun q => q ∣ r') := by
          rw [Finset.mem_filter]; exact ⟨hq, h_div⟩
        rw [h_empty] at this
        exact absurd this (Finset.notMem_empty q)
      · intro h_no_dvd
        rw [Finset.eq_empty_iff_forall_notMem]
        intro q hq
        rw [Finset.mem_filter] at hq
        exact h_no_dvd q hq.1 hq.2
    rw [hfilter_eq]
    -- Apply pmodel_count_avoid_primes_eq (LBL, now non-private).
    have hcount_eq := pmodel_count_avoid_primes_eq (Q := compositePrimeWindow 20 y)
      hwindow_prime hprimorial_pos hwindow_dvd_primorial
    rw [hcount_eq]
    -- pmodel_prob (d=1) = ∏(1-1/q) by `finitePrimeModelProb_eq_empty` + `compositeProductFailure_d_1_iff_empty`.
    have hpmodel_eq :
        finitePrimeModelProb (compositePrimeWindow 20 y) (CompositeProductFailure 20 y 1) =
        ∏ q ∈ compositePrimeWindow 20 y, (1 - (1 : ℝ) / (q : ℝ)) := by
      have hempty := finitePrimeModelProb_eq_empty (compositePrimeWindow 20 y)
      have hcong := finitePrimeModelProb_congr (U := compositePrimeWindow 20 y)
        (Q := CompositeProductFailure 20 y 1) (R := fun S => S = ∅)
        (fun S hS => compositeProductFailure_d_1_iff_empty (by linarith) hS)
      rw [hcong, hempty]
    rw [hpmodel_eq]
  · -- d ≥ 2 case.
    have hd_ge_2 : 2 ≤ d := by omega
    exact step_b_count_no_good_le_primorial_pmodel_d_ge_2 hy hd_ge_2 hd_le_y

/-- **A1: Residue-density-to-pmodel bridge.**

For `r ∈ Fin M` with `M := compositeSuccessorCRTPeriod 20 y d = d · primorial(⌊exp(y^20)⌋)`:
- `d ∣ r` selects a `1/d` fraction.
- For `r = d · r'`, `GoodCompositeSuccessor 20 y d r ↔ GoodCompositeSuccessor 20 y d r'`
  (since window primes `> exp y > d`, so `gcd(window prime, d) = 1`).
- For `r'` uniform on `Fin (primorial cutoff)`, the indicator vector
  `(p ∣ r' : p ∈ compositePrimeWindow 20 y)` is distributed exactly as the
  selection model `selectionWeight` over `compositePrimeWindow 20 y`.

Proven via Step A (`coreBad_card_eq_no_good_quotient`) + Step B (`step_b_count_no_good_le_primorial_pmodel`). -/
private lemma residue_density_le_pmodel_bridge {y : ℝ} (hy : 2 ≤ y)
    {d : ℕ} (hd : 1 ≤ d) (hd_le_y : (d : ℝ) ≤ y) :
    (Nat.card {r : Fin (compositeSuccessorCRTPeriod 20 y d) //
        CompositeSuccessorCoreBad 20 y d r.val} : ℝ) /
      (compositeSuccessorCRTPeriod 20 y d : ℝ) ≤
      finitePrimeModelProb (compositePrimeWindow 20 y)
        (CompositeProductFailure 20 y d) := by
  classical
  rw [cs_fin_card_subtype_eq_range_filter_card]
  unfold compositeSuccessorCRTPeriod
  rw [coreBad_card_eq_no_good_quotient hy hd hd_le_y]
  have hStepB := step_b_count_no_good_le_primorial_pmodel hy hd hd_le_y
  have hd_pos_R : (0 : ℝ) < d := by exact_mod_cast hd
  have hprimorial_pos_R :
      (0 : ℝ) < (primorial (compositeSuccessorCutoff 20 y) : ℝ) := by
    exact_mod_cast cs_primorial_pos _
  have hd_primorial_pos_R :
      (0 : ℝ) < (d : ℝ) * (primorial (compositeSuccessorCutoff 20 y) : ℝ) := by positivity
  have hcast :
      ((d * primorial (compositeSuccessorCutoff 20 y) : ℕ) : ℝ) =
        (d : ℝ) * (primorial (compositeSuccessorCutoff 20 y) : ℝ) := by push_cast; ring
  rw [hcast]
  rw [div_le_iff₀ hd_primorial_pos_R]
  have hpmodel_nonneg :
      0 ≤ finitePrimeModelProb (compositePrimeWindow 20 y)
        (CompositeProductFailure 20 y d) := by
    apply finitePrimeModelProb_nonneg
    intro q hq; exact compositePrimeWindow_one_le hq
  have hd_ge_one_R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  calc ((((Finset.range (primorial (compositeSuccessorCutoff 20 y))).filter
            (fun k => ¬ GoodCompositeSuccessor 20 y d k)).card : ℝ))
      ≤ (primorial (compositeSuccessorCutoff 20 y) : ℝ) *
          finitePrimeModelProb (compositePrimeWindow 20 y)
            (CompositeProductFailure 20 y d) := hStepB
    _ ≤ finitePrimeModelProb (compositePrimeWindow 20 y)
            (CompositeProductFailure 20 y d) *
          ((d : ℝ) * (primorial (compositeSuccessorCutoff 20 y) : ℝ)) := by
        nlinarith [hpmodel_nonneg, hprimorial_pos_R, hd_pos_R, hd_ge_one_R]

-- Paper §6.2 lines 1533-1554 (case d=1, Mertens on sub-window `(exp y, exp(y^2)]`).
-- pmodel(failure d=1) = ∏_FULL (1-1/q) ≤ ∏_SUB (1-1/q) ≤ exp(-(log y - C)) ≤ y^{-1/2}.
private lemma pmodel_failure_d_1_bound :
    ∃ y₀ : ℝ, 2 ≤ y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        finitePrimeModelProb (compositePrimeWindow 20 y)
            (CompositeProductFailure 20 y 1) ≤
          Real.exp (-(1/2) * Real.log y) := by
  rcases step1_mertens_subwindow_d_1_mass with ⟨C, hC_pos, y0_step1, hy0_step1, hmertens_sub⟩
  refine ⟨max y0_step1 (Real.exp (2 * C)), ?_, ?_⟩
  · exact le_trans hy0_step1 (le_max_left _ _)
  intro y hy
  have hy_step1 : y0_step1 ≤ y := le_trans (le_max_left _ _) hy
  have hy_exp2C : Real.exp (2 * C) ≤ y := le_trans (le_max_right _ _) hy
  have h2C_pos : 0 ≤ 2 * C := by linarith
  have hy_pos : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy_exp2C
  have hy_one : 1 ≤ y := by
    have h1 : (1 : ℝ) ≤ Real.exp (2 * C) := Real.one_le_exp h2C_pos
    linarith
  have h2C_le_logy : 2 * C ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos _) hy_exp2C
    rwa [Real.log_exp] at h
  -- Step 1: pmodel(failure d=1) = pmodel(S = ∅) = ∏_FULL (1-1/q).
  have hcong := finitePrimeModelProb_congr (U := compositePrimeWindow 20 y)
    (Q := CompositeProductFailure 20 y 1) (R := fun S => S = ∅)
    (fun S hS => compositeProductFailure_d_1_iff_empty hy_one hS)
  rw [hcong, finitePrimeModelProb_eq_empty]
  -- Helpers: window primes are positive and 0 ≤ (1-1/q) ≤ 1.
  have hwindow_pos : ∀ q ∈ compositePrimeWindow 20 y, 0 < q := by
    intro q hq
    unfold compositePrimeWindow at hq
    rw [Finset.mem_filter] at hq
    exact hq.2.1.pos
  have hwindow_one_le : ∀ q ∈ compositePrimeWindow 20 y, (1 : ℝ) ≤ (q : ℝ) := by
    intro q hq
    exact_mod_cast Nat.succ_le_of_lt (hwindow_pos q hq)
  have h_factor_in_01 :
      ∀ q ∈ compositePrimeWindow 20 y,
        0 ≤ (1 - (1 : ℝ) / (q : ℝ)) ∧ (1 - (1 : ℝ) / (q : ℝ)) ≤ 1 := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := hwindow_one_le q hq
    have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
    refine ⟨?_, ?_⟩
    · have : (1 : ℝ) / (q : ℝ) ≤ 1 := (div_le_one hq_pos).mpr hq1
      linarith
    · have : 0 ≤ (1 : ℝ) / (q : ℝ) := by positivity
      linarith
  -- Step 2: ∏_FULL (1-1/q) ≤ ∏_SUB (1-1/q) (paper line 1535: dropping FULL\SUB factors ≤ 1).
  have hsub_subset : compositePrimeSubWindow_d_1 y ⊆ compositePrimeWindow 20 y :=
    compositePrimeSubWindow_d_1_subset_window hy_one
  have hprod_FULL_le_SUB :
      (∏ q ∈ compositePrimeWindow 20 y, (1 - (1 : ℝ) / (q : ℝ))) ≤
        (∏ q ∈ compositePrimeSubWindow_d_1 y, (1 - (1 : ℝ) / (q : ℝ))) := by
    have hsplit :
        (∏ q ∈ compositePrimeWindow 20 y, (1 - (1 : ℝ) / (q : ℝ))) =
          (∏ q ∈ compositePrimeWindow 20 y \ compositePrimeSubWindow_d_1 y,
            (1 - (1 : ℝ) / (q : ℝ))) *
            (∏ q ∈ compositePrimeSubWindow_d_1 y, (1 - (1 : ℝ) / (q : ℝ))) := by
      rw [Finset.prod_sdiff hsub_subset]
    rw [hsplit]
    have hsub_nonneg :
        0 ≤ ∏ q ∈ compositePrimeSubWindow_d_1 y, (1 - (1 : ℝ) / (q : ℝ)) := by
      apply Finset.prod_nonneg
      intro q hq
      exact (h_factor_in_01 q (hsub_subset hq)).1
    have hsdiff_le_one :
        (∏ q ∈ compositePrimeWindow 20 y \ compositePrimeSubWindow_d_1 y,
          (1 - (1 : ℝ) / (q : ℝ))) ≤ 1 := by
      apply Finset.prod_le_one
      · intro q hq
        rw [Finset.mem_sdiff] at hq
        exact (h_factor_in_01 q hq.1).1
      · intro q hq
        rw [Finset.mem_sdiff] at hq
        exact (h_factor_in_01 q hq.1).2
    have := mul_le_mul_of_nonneg_right hsdiff_le_one hsub_nonneg
    linarith [this]
  -- Step 3: ∏_SUB (1-1/q) ≤ exp(-∑_SUB 1/q) (paper line 1539, `Real.one_sub_le_exp_neg`).
  have hsub_one_le : ∀ q ∈ compositePrimeSubWindow_d_1 y, (1 : ℝ) ≤ (q : ℝ) :=
    fun q hq => hwindow_one_le q (hsub_subset hq)
  have hprod_le_exp :
      (∏ q ∈ compositePrimeSubWindow_d_1 y, (1 - (1 : ℝ) / (q : ℝ))) ≤
        Real.exp (-(∑ q ∈ compositePrimeSubWindow_d_1 y, (1 : ℝ) / (q : ℝ))) := by
    calc (∏ q ∈ compositePrimeSubWindow_d_1 y, (1 - (1 : ℝ) / (q : ℝ)))
        ≤ ∏ q ∈ compositePrimeSubWindow_d_1 y, Real.exp (-((1 : ℝ) / (q : ℝ))) := by
          apply Finset.prod_le_prod
          · intro q hq
            have hq1 : (1 : ℝ) ≤ (q : ℝ) := hsub_one_le q hq
            have hle : (1 : ℝ) / (q : ℝ) ≤ 1 :=
              (div_le_one (by linarith : (0 : ℝ) < (q : ℝ))).mpr hq1
            linarith
          · intro q _hq
            simpa [sub_eq_add_neg, neg_div] using Real.one_sub_le_exp_neg ((1 : ℝ) / (q : ℝ))
      _ = Real.exp (∑ q ∈ compositePrimeSubWindow_d_1 y, -((1 : ℝ) / (q : ℝ))) := by
          rw [← Real.exp_sum]
      _ = Real.exp (-(∑ q ∈ compositePrimeSubWindow_d_1 y, (1 : ℝ) / (q : ℝ))) := by
          congr 1
          rw [← Finset.sum_neg_distrib]
  -- Step 4: ∑_SUB 1/q ≥ log y - C (paper line 1540, Mertens on sub-window).
  have hmertens_y := hmertens_sub y hy_step1
  have hsum_eq : reciprocalPrimeMass (compositePrimeSubWindow_d_1 y) =
      ∑ q ∈ compositePrimeSubWindow_d_1 y, (1 : ℝ) / (q : ℝ) := rfl
  rw [hsum_eq] at hmertens_y
  have hsum_lower : Real.log y - C ≤
      ∑ q ∈ compositePrimeSubWindow_d_1 y, (1 : ℝ) / (q : ℝ) := by
    have habs := abs_le.mp hmertens_y
    linarith [habs.1]
  -- Step 5: exp(-∑) ≤ exp(-(log y - C)) ≤ exp(-(1/2) log y) for y ≥ exp(2C).
  have hexp_neg_le :
      Real.exp (-(∑ q ∈ compositePrimeSubWindow_d_1 y, (1 : ℝ) / (q : ℝ))) ≤
        Real.exp (-(Real.log y - C)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hbound : Real.exp (-(Real.log y - C)) ≤ Real.exp (-(1/2) * Real.log y) := by
    apply Real.exp_le_exp.mpr
    linarith
  exact hprod_FULL_le_SUB.trans (hprod_le_exp.trans (hexp_neg_le.trans hbound))

/-- **A2: Product-model failure bound.**

In the finite prime selection model on `compositePrimeWindow 20 y`, the probability
that no admissible squarefree product exists is `O(y^{-c})`.  This combines:
* `step4_chernoff_good_blocks`: `P(< K good blocks) ≤ y^{-c₁}` for `K := compositeGoodBlockThreshold y`.
* `step5_conditional_residue`: conditional residue distribution is `O(y^{-1/2})`-uniform.
* `step6_subset_product_application`: given `K` good blocks with near-uniform residues,
  `P(no admissible subproduct) ≤ φ(d)/(2^K - 1) + K · ε_y`. -/
-- General union-bound helper: P(Q) ≤ P(B) + P(Q ∧ ¬B), for any propositions Q, B.
private lemma finitePrimeModelProb_le_split {U : Finset ℕ}
    (hU : ∀ q ∈ U, 1 ≤ q) (Q B : Finset ℕ → Prop) :
    finitePrimeModelProb U Q ≤
      finitePrimeModelProb U B + finitePrimeModelProb U (fun S => Q S ∧ ¬ B S) := by
  classical
  unfold finitePrimeModelProb
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _hS
  have h_nonneg := selectionWeight_nonneg (S := S) hU
  by_cases hQ : Q S
  · by_cases hB : B S
    · simp [hQ, hB]
    · simp [hQ, hB]
  · by_cases hB : B S
    · simp only [ge_iff_le]; exact h_nonneg
    · simp [hQ, hB]

-- Numerical helper: paper §6.2 line 1683 ("Numerically ρ=e⁻¹≈0.368, 1/log2≈1.443,
-- so it suffices to take γ≥14"). Concretely κ := ρ γ / 2 with ρ = e⁻¹, γ = 15 gives
-- κ · log 2 = 15 · log 2 / (2e) ≈ 1.913 > 1.  Used in the Step 6 algebraic bound.
-- Paper line 1679: chooses κ so κ > 1/log 2 + 1, equivalent to κ·log 2 > 1 + log 2.
private lemma kappa_log_two_gt_one :
    ((Real.exp (-1) * 15) / 2) * Real.log 2 > 1 := by
  -- Need: (e⁻¹ · 15 / 2) · log 2 > 1.
  -- e⁻¹ ≥ 0.36 (since e ≤ 2.778), log 2 ≥ 0.693.
  -- (0.36 · 15) / 2 · 0.693 = 2.7 · 0.693 ≈ 1.871 > 1.  ✓
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have he_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hexp_neg_eq : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
  have hexp_neg_lower : (0.36 : ℝ) < Real.exp (-1) := by
    rw [hexp_neg_eq]
    rw [show (0.36 : ℝ) = 0.36 from rfl]
    rw [lt_inv_comm₀ (by norm_num : (0:ℝ) < 0.36) he_pos]
    linarith
  -- (Real.exp (-1) * 15 / 2) * Real.log 2 ≥ (0.36 · 15 / 2) · 0.6931471803.
  nlinarith [hlog2, hexp_neg_lower]

-- Helper: `(κ log y + 1) · C · y^{-1/2}` decays faster than `y^{-c}` for any `c < 1/2`.
-- Used in the Step 6 parent algebra to bound term `K · ε_y`.
-- Proof: log y ≤ y^ε/ε for any ε > 0 (Mathlib `Real.log_le_rpow_div`).  Pick ε = (1/2-c)/2.
-- Then (κ log y + 1) · C · y^{-1/2} ≤ A · y^{ε - 1/2} ≤ y^ε · y^{ε - 1/2} = y^{2ε - 1/2} = y^{-c}.
private lemma kappa_logy_eps_decays (C : ℝ) (hC : 0 < C) {c : ℝ} (hc : 0 < c) (hc_lt : c < 1/2) :
    ∃ y₀ : ℝ, 2 ≤ y₀ ∧
      ∀ y : ℝ, y₀ ≤ y →
        (((Real.exp (-1) * 15) / 2) * Real.log y + 1) * (C * y ^ (-(1:ℝ)/2)) ≤
          Real.exp (-c * Real.log y) := by
  set κ : ℝ := (Real.exp (-1) * 15) / 2 with hκ_def
  have hκ_pos : 0 < κ := by rw [hκ_def]; positivity
  set ε : ℝ := (1/2 - c) / 2 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; linarith
  have h2ε_eq : 2 * ε = 1/2 - c := by rw [hε_def]; ring
  -- A := (κ/ε + 1) · C: combined coefficient.
  set A : ℝ := (κ/ε + 1) * C with hA_def
  have hA_pos : 0 < A := by
    rw [hA_def]
    exact mul_pos (by positivity) hC
  -- y₀ chosen so that y ≥ A^{1/ε} + 1, ensuring y^ε ≥ A + ... ≥ A.
  set y₀ : ℝ := max 2 (A ^ ((1:ℝ) / ε) + 1) with hy₀_def
  refine ⟨y₀, le_max_left _ _, ?_⟩
  intro y hy
  have hy_2 : 2 ≤ y := le_trans (le_max_left _ _) hy
  have hy_root : A ^ ((1:ℝ) / ε) + 1 ≤ y := le_trans (le_max_right _ _) hy
  have hy_pos : 0 < y := by linarith
  have hy_one : 1 ≤ y := by linarith
  -- Step 1: log y ≤ y^ε / ε (Mathlib).
  have hlog_le : Real.log y ≤ y ^ ε / ε := Real.log_le_rpow_div hy_pos.le hε_pos
  -- Step 2: y^ε ≥ 1 (since y ≥ 1, ε > 0).
  have hyε_pos : 0 < y ^ ε := Real.rpow_pos_of_pos hy_pos ε
  have hyε_ge_one : 1 ≤ y ^ ε := Real.one_le_rpow hy_one hε_pos.le
  -- Step 3: κ log y + 1 ≤ (κ/ε + 1) · y^ε.
  have h2 : κ * Real.log y + 1 ≤ (κ/ε + 1) * y^ε := by
    have hh1 : κ * Real.log y ≤ (κ/ε) * y^ε := by
      have h := mul_le_mul_of_nonneg_left hlog_le hκ_pos.le
      have heq : κ * (y^ε / ε) = (κ/ε) * y^ε := by field_simp
      linarith [heq ▸ h]
    nlinarith [hh1, hyε_ge_one]
  -- Step 4: A ≤ y^ε from y ≥ A^{1/ε} + 1.
  have hA_le_yε : A ≤ y ^ ε := by
    have hA_root_le_y : A ^ ((1:ℝ) / ε) ≤ y := by linarith
    have hroot_pos : 0 ≤ A ^ ((1:ℝ) / ε) :=
      (Real.rpow_pos_of_pos hA_pos _).le
    have h_pow : (A ^ ((1:ℝ) / ε)) ^ ε ≤ y ^ ε :=
      Real.rpow_le_rpow hroot_pos hA_root_le_y hε_pos.le
    have h_simplify : (A ^ ((1:ℝ) / ε)) ^ ε = A := by
      rw [← Real.rpow_mul hA_pos.le]
      have : (1 : ℝ) / ε * ε = 1 := by field_simp
      rw [this, Real.rpow_one]
    linarith [h_simplify ▸ h_pow]
  -- Step 5: combine.
  -- (κ log y + 1) · C ≤ (κ/ε + 1) · y^ε · C = A · y^ε ≤ y^ε · y^ε = y^{2ε}.
  -- Multiply by y^{-1/2}: ≤ y^{2ε - 1/2} = y^{-c} = exp(-c log y).
  have hyhalf_pos : 0 < y ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hy_pos _
  have hLHS_bound : (κ * Real.log y + 1) * C ≤ A * y^ε := by
    have h := mul_le_mul_of_nonneg_right h2 hC.le
    have heq : (κ/ε + 1) * y^ε * C = A * y^ε := by rw [hA_def]; ring
    linarith [heq ▸ h]
  have hLHS_bound2 : (κ * Real.log y + 1) * C * y^(-(1:ℝ)/2) ≤
      A * y^ε * y^(-(1:ℝ)/2) :=
    mul_le_mul_of_nonneg_right hLHS_bound hyhalf_pos.le
  -- A · y^ε ≤ y^ε · y^ε.
  have hAy_le_y2ε : A * y^ε ≤ y^ε * y^ε :=
    mul_le_mul_of_nonneg_right hA_le_yε (Real.rpow_nonneg hy_pos.le _)
  have hAyhalf : A * y^ε * y^(-(1:ℝ)/2) ≤ y^ε * y^ε * y^(-(1:ℝ)/2) :=
    mul_le_mul_of_nonneg_right hAy_le_y2ε hyhalf_pos.le
  -- y^ε · y^ε · y^{-1/2} = y^{2ε - 1/2} = y^{-c}.
  have heq_combine : y^ε * y^ε * y^(-(1:ℝ)/2) = Real.exp (-c * Real.log y) := by
    rw [show y^ε * y^ε * y^(-(1:ℝ)/2) = y ^ (ε + ε + (-(1:ℝ)/2)) by
      rw [← Real.rpow_add hy_pos, ← Real.rpow_add hy_pos]]
    rw [Real.rpow_def_of_pos hy_pos]
    congr 1
    have : ε + ε + (-(1:ℝ)/2) = 2 * ε - 1/2 := by ring
    rw [this, h2ε_eq]; ring
  -- Now rearrange: goal is (κ * log y + 1) * (C * y^{-1/2}) ≤ exp(-c log y).
  -- Have: (κ * log y + 1) * C * y^{-1/2} ≤ y^ε · y^ε · y^{-1/2} = exp(-c log y).
  -- By associativity: (κ * log y + 1) * (C * y^{-1/2}) = (κ * log y + 1) * C * y^{-1/2}.
  rw [show (κ * Real.log y + 1) * (C * y^(-(1:ℝ)/2)) =
      (κ * Real.log y + 1) * C * y^(-(1:ℝ)/2) by ring]
  linarith [hLHS_bound2, hAyhalf, heq_combine]

-- Paper §6.2 Step 6 (lines 1756-1788): construction of conditional measure
-- on (Fin K → (ZMod d)ˣ) from the pmodel + application of subset-product lemma.
-- The bound `N/(2^K - 1) + K · ε_y` matches paper line 1773 exactly.
-- This sub-claim isolates the conditional measure construction (paper lines 1719-1753).
private lemma step6_pmodel_bound :
    ∃ C_step5 : ℝ, 0 < C_step5 ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ y →
            finitePrimeModelProb (compositePrimeWindow 20 y)
                (fun S => CompositeProductFailure 20 y d S ∧
                  ¬ (goodBlockCount S y < compositeGoodBlockThreshold y)) ≤
              (d.totient : ℝ) / ((2:ℝ)^(compositeGoodBlockThreshold y) - 1) +
                (compositeGoodBlockThreshold y : ℝ) * (C_step5 * y ^ (-(1:ℝ)/2)) := by
  -- Paper §6.2 Step 5 + Step 6 (lines 1706-1788).
  -- Strategy:
  -- (1) Extract C_step5 from `step5_combined` (gives ε_y = C_step5 · y^{-1/2} per-block uniformity).
  -- (2) Construct μ : (Fin K → (ZMod d)ˣ) → ℝ as the joint distribution of residues from
  --     the first K good blocks, conditional on ≥K good blocks (paper lines 1719-1753).
  -- (3) Verify μ has K·ε_y near-uniform property (paper line 1751).
  -- (4) Apply `step6_subset_product_application` (paper lines 1769-1773) to get bound.
  -- (5) Connect: pmodel(failure ∧ ≥K good) ≤ μ-mass on bad g via paper line 1799-1814 admissibility.
  rcases step5_combined with ⟨C_step5_pw, hC_step5_pw_pos, y₀_step5_pw, hy₀_step5_pw, hstep5_pw⟩
  -- Also extract L1 version for hstep5_l1 (paper §6.2 line 1741: TV-close).
  rcases block_uniform_total_variation_bound_l1 with
    ⟨C_step5_l1, hC_step5_l1_pos, y₀_step5_l1, hy₀_step5_l1, hstep5_l1_lemma⟩
  -- Unified constant: max of pointwise and L1 constants (both ε_y = O(y^{-1/2})).
  let C_step5 : ℝ := max C_step5_pw C_step5_l1
  have hC_step5_pos : 0 < C_step5 := lt_of_lt_of_le hC_step5_pw_pos (le_max_left _ _)
  let y₀_step5 : ℝ := max y₀_step5_pw y₀_step5_l1
  have hy₀_step5 : 2 ≤ y₀_step5 := le_trans hy₀_step5_pw (le_max_left _ _)
  -- Pointwise bound with unified constant.
  have hstep5 : ∀ y : ℝ, y₀_step5 ≤ y → ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ y →
      ∀ k : ℕ, k < compositeBlockCount y → ∀ a : ℕ, Nat.Coprime a d →
        |blockConditionalResidueProbability (compositeBlock y k) d a -
            (1 : ℝ) / (d.totient : ℝ)| ≤ C_step5 * y ^ (-(1 : ℝ) / 2) := by
    intro y hy d hd hdy k hk a ha
    have hy_pw : y₀_step5_pw ≤ y := le_trans (le_max_left _ _) hy
    have hpw := hstep5_pw y hy_pw d hd hdy k hk a ha
    have hC_le : C_step5_pw ≤ C_step5 := le_max_left _ _
    have hr_nn : 0 ≤ y ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by linarith [hy_pw, hy₀_step5_pw]) _
    calc |blockConditionalResidueProbability (compositeBlock y k) d a -
          (1 : ℝ) / (d.totient : ℝ)|
        ≤ C_step5_pw * y ^ (-(1 : ℝ) / 2) := hpw
      _ ≤ C_step5 * y ^ (-(1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hC_le hr_nn
  -- Extract step2 for block nonemptyness (paper line 1574-1590: blocks have positive
  -- prime mass via Mertens, hence nonempty for y large enough).
  rcases step2_block_decomposition with ⟨C₂, hC₂_pos, y₂, hy₂_ge2, hstep2⟩
  -- Strengthen y₀ to ensure:
  --   (i) `15 log y ≤ y` (paper line 1810): y ≥ 900.
  --   (ii) y ≥ y₂ (step2 threshold).
  --   (iii) y ≥ 2 * C₂ + 1 (so |reciprocalPrimeMass - 1| ≤ C₂/y < 1, hence mass > 0).
  refine ⟨C_step5, hC_step5_pos,
    max y₀_step5 (max 900 (max y₂ (2 * C₂ + 1))), ?_, ?_⟩
  · exact le_max_of_le_left hy₀_step5
  intro y hy_max d hd_ge_2 hd_le_y
  have hy : y₀_step5 ≤ y := le_trans (le_max_left _ _) hy_max
  have hy_other : max 900 (max y₂ (2 * C₂ + 1)) ≤ y := le_trans (le_max_right _ _) hy_max
  have hy_900 : (900 : ℝ) ≤ y := le_trans (le_max_left _ _) hy_other
  have hy_step2 : y₂ ≤ y := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hy_other)
  have hy_2C₂ : 2 * C₂ + 1 ≤ y := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hy_other)
  classical
  have : NeZero d := ⟨by omega⟩
  -- K := ⌈κ log y⌉, paper line 1708.
  set K : ℕ := compositeGoodBlockThreshold y with hK_def
  have hy_pos : 0 < y := by
    have : (2 : ℝ) ≤ y₀_step5 := hy₀_step5
    linarith
  have hlog_y_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hK_pos : 0 < K := by
    rw [hK_def]
    unfold compositeGoodBlockThreshold
    apply Nat.ceil_pos.mpr
    exact mul_pos (by positivity) hlog_y_pos
  -- ε_y := C_step5 · y^{-1/2}, per-block residue uniformity scale (paper line 1750).
  set ε_y : ℝ := C_step5 * y ^ (-(1:ℝ)/2) with hε_y_def
  have hε_y_nonneg : 0 ≤ ε_y := by
    rw [hε_y_def]
    exact mul_nonneg hC_step5_pos.le (Real.rpow_nonneg hy_pos.le _)
  -- Steps (2)-(5): Construct μ + apply step6_subset_product_application + connection.
  -- Paper §6.2 lines 1719-1773.
  -- Case split: pmodel(≥K good) = 0 vs > 0.
  set pmodel_K_good : ℝ := finitePrimeModelProb (compositePrimeWindow 20 y)
      (fun S => K ≤ goodBlockCount S y) with hpmodel_K_good_def
  have hpmodel_K_good_nonneg : 0 ≤ pmodel_K_good := by
    rw [hpmodel_K_good_def]
    exact finitePrimeModelProb_nonneg
      (fun _q hq => compositePrimeWindow_one_le hq) _
  -- RHS is nonneg (used in trivial case).
  have hRHS_nonneg : 0 ≤ (d.totient : ℝ) / ((2:ℝ)^K - 1) + (K : ℝ) * ε_y := by
    apply add_nonneg
    · apply div_nonneg
      · exact_mod_cast Nat.zero_le _
      · have h2K_ge_2 : (2 : ℝ) ≤ (2:ℝ)^K := by
          calc (2 : ℝ) = (2:ℝ)^1 := by norm_num
            _ ≤ (2:ℝ)^K := by
              apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
              exact hK_pos
        linarith
    · exact mul_nonneg (by exact_mod_cast Nat.zero_le _) hε_y_nonneg
  by_cases hpos : pmodel_K_good = 0
  · -- denominator = 0: pmodel(failure ∧ ≥K) ≤ pmodel(≥K) = 0 ≤ RHS.
    -- pmodel(failure ∧ ≥K good) is bounded by pmodel(≥K good) since the event is a sub-event.
    -- Specifically: failure ∧ ≥K good → ≥K good (drop the failure condition).
    have h_le : finitePrimeModelProb (compositePrimeWindow 20 y)
                  (fun S => CompositeProductFailure 20 y d S ∧
                    ¬ (goodBlockCount S y < compositeGoodBlockThreshold y)) ≤
                pmodel_K_good := by
      rw [hpmodel_K_good_def]
      -- Use congr to align decidability instances, then monotonicity of sum over filter.
      have hmono : ∀ S, (CompositeProductFailure 20 y d S ∧
          ¬ (goodBlockCount S y < compositeGoodBlockThreshold y)) →
          K ≤ goodBlockCount S y := by
        intro S hSfail
        rw [hK_def]; omega
      -- finitePrimeModelProb is monotone in the predicate when implication holds.
      unfold finitePrimeModelProb
      have hweight_nn : ∀ S, 0 ≤ selectionWeight (compositePrimeWindow 20 y) S := by
        intro S
        exact selectionWeight_nonneg
          (fun _q hq => compositePrimeWindow_one_le hq)
      -- Sum over a smaller filter ≤ sum over a larger filter (with nonneg terms).
      classical
      have hsubset : (compositePrimeWindow 20 y).powerset.filter
          (fun S => CompositeProductFailure 20 y d S ∧
            ¬ (goodBlockCount S y < compositeGoodBlockThreshold y)) ⊆
          (compositePrimeWindow 20 y).powerset.filter
            (fun S => K ≤ goodBlockCount S y) := by
        intro S hS
        simp only [Finset.mem_filter] at hS ⊢
        exact ⟨hS.1, hmono S hS.2⟩
      convert! Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun S _ _ => hweight_nn S)
    rw [hpos] at h_le
    linarith
  · -- denominator > 0: apply step6_subset_product_application + paper line 1796-1815 connection.
    -- Strategy:
    -- (a) failure ∧ ≥K good → extract S ∈ bad (via failure_implies_bad_residue).
    -- (b) pmodel(failure ∧ ≥K good) ≤ ∑_{g ∈ bad} pmodel(extract = g ∧ ≥K good).
    -- (c) ∑_{g ∈ bad} pmodel(extract = g ∧ ≥K good) = pmodel_K_good · ∑_{g ∈ bad} μ(g).
    -- (d) ≤ ∑_{g ∈ bad} μ(g) [since pmodel_K_good ≤ 1].
    -- (e) ≤ N/(2^K - 1) + K · ε_y [step6_subset_product_application].
    -- Paper §6.2 line 1810: γ log y ≤ y for y large.  Use y ≥ 900 + log_le_rpow_div.
    have hy_log_le_y : 15 * Real.log y ≤ y := by
      have h1 : Real.log y ≤ y ^ ((1 : ℝ)/2) / ((1 : ℝ)/2) :=
        Real.log_le_rpow_div hy_pos.le (by norm_num)
      have h2 : 15 * Real.log y ≤ 30 * y ^ ((1 : ℝ)/2) := by
        have heq : y ^ ((1 : ℝ)/2) / ((1 : ℝ)/2) = 2 * y ^ ((1 : ℝ)/2) := by ring
        linarith [heq ▸ h1]
      have h_30_le : (30 : ℝ) ≤ y ^ ((1 : ℝ)/2) := by
        have h900eq : (900 : ℝ) ^ ((1 : ℝ)/2) = 30 := by
          rw [show (900 : ℝ) = 30 ^ (2 : ℕ) by norm_num]
          rw [← Real.rpow_natCast (30 : ℝ) 2]
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 30)]
          norm_num
        rw [← h900eq]
        exact Real.rpow_le_rpow (by norm_num) hy_900 (by norm_num)
      have h3 : 30 * y ^ ((1 : ℝ)/2) ≤ y := by
        have hsqrt_sq : y ^ ((1 : ℝ)/2) * y ^ ((1 : ℝ)/2) = y := by
          rw [← Real.rpow_add hy_pos]
          norm_num
        have hineq : 30 * y ^ ((1 : ℝ)/2) ≤ y ^ ((1 : ℝ)/2) * y ^ ((1 : ℝ)/2) := by
          have := mul_le_mul_of_nonneg_right h_30_le
            (Real.rpow_nonneg hy_pos.le ((1 : ℝ)/2))
          linarith [this]
        linarith [hsqrt_sq, hineq]
      linarith
    have hK_le_one : 1 ≤ K := hK_pos
    have hpmodel_K_good_pos : 0 < pmodel_K_good :=
      lt_of_le_of_ne hpmodel_K_good_nonneg (Ne.symm hpos)
    have hpmodel_K_good_le_one : pmodel_K_good ≤ 1 := by
      rw [hpmodel_K_good_def, ← finitePrimeModelProb_true (compositePrimeWindow 20 y)]
      -- pmodel(Q) ≤ pmodel(True) since Q → True.
      unfold finitePrimeModelProb
      classical
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro S hS
        simp only [Finset.mem_filter] at hS ⊢
        exact ⟨hS.1, trivial⟩
      · intro S _ _
        exact selectionWeight_nonneg
          (fun _q hq => compositePrimeWindow_one_le hq)
    -- Apply step6_subset_product_application to μ.
    have hμ_nonneg : ∀ g, 0 ≤ conditionalResidueMeasure y d K g :=
      fun g => conditionalResidueMeasure_nonneg g
    have hμ_sum : (∑ g : Fin K → (ZMod d)ˣ, conditionalResidueMeasure y d K g) = 1 :=
      conditionalResidueMeasure_sum_eq_one (hpmodel_K_good_def ▸ hpos)
    have hy2 : (2 : ℝ) ≤ y := le_trans hy₀_step5 hy
    -- Provide the L1 hypothesis (paper §6.2 line 1741: TV-close, paper proof line 1488).
    -- Use block_uniform_total_variation_bound_l1, converting ∑ over (ZMod d)ˣ
    -- to ∑ over (Finset.range d).filter (Nat.Coprime · d) via the bijection
    -- (ZMod d)ˣ → {a < d : Coprime a d} given by `.val`.
    have hy_l1 : y₀_step5_l1 ≤ y := by
      have h1 : y₀_step5_l1 ≤ y₀_step5 := le_max_right _ _
      exact h1.trans (by show y₀_step5 ≤ y; exact hy)
    have hstep5_l1 :
        ∀ k : ℕ, k < compositeBlockCount y →
          (∑ a : (ZMod d)ˣ,
              |blockConditionalResidueProbability (compositeBlock y k) d ((a : ZMod d).val) -
                  (1 : ℝ) / (d.totient : ℝ)|) ≤ C_step5 * y ^ (-(1 : ℝ) / 2) := by
      intro k hk
      classical
      -- Convert sum over (ZMod d)ˣ to sum over Finset.range d filter coprime via .val map.
      have h_sum_eq :
          (∑ a : (ZMod d)ˣ,
              |blockConditionalResidueProbability (compositeBlock y k) d ((a : ZMod d).val) -
                  (1 : ℝ) / (d.totient : ℝ)|) =
          ∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
              |blockConditionalResidueProbability (compositeBlock y k) d a -
                  (1 : ℝ) / (d.totient : ℝ)| := by
        symm
        refine Finset.sum_bij
          (fun (a : ℕ) (ha : a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d)) =>
            ZMod.unitOfCoprime a (Finset.mem_filter.mp ha).2)
          ?hi ?inj ?surj ?h
        · -- target ∈ univ
          intro a _; exact Finset.mem_univ _
        · -- injective
          intro a₁ ha₁ a₂ ha₂ hu
          have ha₁_lt : a₁ < d := Finset.mem_range.mp (Finset.mem_filter.mp ha₁).1
          have ha₂_lt : a₂ < d := Finset.mem_range.mp (Finset.mem_filter.mp ha₂).1
          have h_coe :
              ((ZMod.unitOfCoprime a₁ (Finset.mem_filter.mp ha₁).2 : ZMod d) =
               (ZMod.unitOfCoprime a₂ (Finset.mem_filter.mp ha₂).2 : ZMod d)) :=
            congrArg (fun (u : (ZMod d)ˣ) => (u : ZMod d)) hu
          rw [ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime] at h_coe
          have h_a₁_eq : (a₁ : ZMod d).val = a₁ := by
            rw [ZMod.val_natCast]
            exact Nat.mod_eq_of_lt ha₁_lt
          have h_a₂_eq : (a₂ : ZMod d).val = a₂ := by
            rw [ZMod.val_natCast]
            exact Nat.mod_eq_of_lt ha₂_lt
          have h_val := congrArg (fun (z : ZMod d) => z.val) h_coe
          rw [h_a₁_eq, h_a₂_eq] at h_val
          exact h_val
        · -- surjective
          intro u _hu
          have : NeZero d := ⟨by omega⟩
          have h_val_lt : (u : ZMod d).val < d := ZMod.val_lt _
          have h_val_cop : Nat.Coprime (u : ZMod d).val d :=
            ZMod.val_coe_unit_coprime u
          refine ⟨(u : ZMod d).val, ?_, ?_⟩
          · rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨h_val_lt, h_val_cop⟩
          · -- ZMod.unitOfCoprime ((u : ZMod d).val) _ = u
            apply Units.ext
            rw [ZMod.coe_unitOfCoprime]
            exact ZMod.natCast_zmod_val (u : ZMod d)
        · -- per-element equality
          intro a ha
          have ha_lt : a < d := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
          have h_unit_val :
              ((ZMod.unitOfCoprime a (Finset.mem_filter.mp ha).2 : ZMod d).val) = a := by
            rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
            exact Nat.mod_eq_of_lt ha_lt
          show |blockConditionalResidueProbability (compositeBlock y k) d a -
                  (1 : ℝ) / (d.totient : ℝ)| =
              |blockConditionalResidueProbability (compositeBlock y k) d
                  (((ZMod.unitOfCoprime a (Finset.mem_filter.mp ha).2 : (ZMod d)ˣ) :
                    ZMod d).val) -
                  (1 : ℝ) / (d.totient : ℝ)|
          rw [h_unit_val]
      rw [h_sum_eq]
      have hd_le_y' : (d : ℝ) ≤ y := hd_le_y
      have h_lemma := hstep5_l1_lemma y hy_l1 d hd_ge_2 hd_le_y' k hk
      have hC_le : C_step5_l1 ≤ C_step5 := le_max_right _ _
      have hr_nn : 0 ≤ y ^ (-(1 : ℝ) / 2) :=
        Real.rpow_nonneg (by linarith) _
      calc (∑ a ∈ (Finset.range d).filter (fun a => Nat.Coprime a d),
              |blockConditionalResidueProbability (compositeBlock y k) d a -
                  (1 : ℝ) / (d.totient : ℝ)|)
          ≤ C_step5_l1 * y ^ (-(1 : ℝ) / 2) := h_lemma
        _ ≤ C_step5 * y ^ (-(1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hC_le hr_nn
    have hcondprob_nn :
        ∀ k : ℕ, k < compositeBlockCount y → ∀ a : (ZMod d)ˣ,
          0 ≤ blockConditionalResidueProbability (compositeBlock y k) d ((a : ZMod d).val) := by
      intro k _hk a
      unfold blockConditionalResidueProbability
      apply div_nonneg
      · exact Finset.sum_nonneg (fun q _ => by positivity)
      · exact Finset.sum_nonneg (fun q _ => by positivity)
    have hcondprob_sum :
        ∀ k : ℕ, k < compositeBlockCount y →
          (∑ a : (ZMod d)ˣ,
            blockConditionalResidueProbability (compositeBlock y k) d ((a : ZMod d).val)) = 1 := by
      intro k hk
      classical
      -- Step 1: Block nonempty (paper §6.2 step 2 line 1574-1590).
      have hmass_close := (hstep2 y hy_step2).2.2 k hk
      have hC₂_div_lt : C₂ / y < 1 := by
        rw [div_lt_one hy_pos]
        linarith
      have hmass_pos : 0 < reciprocalPrimeMass (compositeBlock y k) := by
        have h_abs := (abs_le.mp hmass_close.2).1
        linarith
      have hblock_nonempty : (compositeBlock y k).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        unfold reciprocalPrimeMass at hmass_pos
        rw [hempty, Finset.sum_empty] at hmass_pos
        exact lt_irrefl _ hmass_pos
      -- Step 2: Every q ∈ B is coprime to d (paper line 1716).
      have hcoprime : ∀ q ∈ compositeBlock y k, Nat.Coprime q d := by
        intro q hq
        have hq_prime : q.Prime := compositeBlock_prime hq
        have hy_nn : (0 : ℝ) ≤ y := le_of_lt hy_pos
        have hq_gt_exp : Real.exp y < (q : ℝ) := compositeBlock_prime_gt_exp_y hy_nn hq
        have hexp_gt_y : y < Real.exp y := by
          have h := Real.add_one_lt_exp (x := y) (by linarith : y ≠ 0)
          linarith
        have hd_lt_q : (d : ℝ) < (q : ℝ) := by linarith
        have hd_lt_q_nat : d < q := by exact_mod_cast hd_lt_q
        have hnot_dvd : ¬ q ∣ d := fun hdvd =>
          absurd (Nat.le_of_dvd (by omega) hdvd) (not_le.mpr hd_lt_q_nat)
        exact (hq_prime.coprime_iff_not_dvd).mpr hnot_dvd
      -- Step 3: D > 0.
      set B := compositeBlock y k with hB_def
      set D : ℝ := ∑ q ∈ B, (1 : ℝ) / (((q - 1 : ℕ) : ℝ)) with hD_def
      have hD_pos : 0 < D := by
        rcases hblock_nonempty with ⟨q₀, hq₀⟩
        apply Finset.sum_pos
        · intro q hq
          have hq_prime : q.Prime := compositeBlock_prime hq
          have hq_ge2 : 2 ≤ q := hq_prime.two_le
          have h1 : (1 : ℝ) ≤ ((q - 1 : ℕ) : ℝ) := by
            have : 1 ≤ q - 1 := by omega
            exact_mod_cast this
          positivity
        · exact ⟨q₀, hq₀⟩
      have hD_ne : D ≠ 0 := hD_pos.ne'
      -- Step 4: Partition sum = D.
      unfold blockConditionalResidueProbability
      rw [← Finset.sum_div]
      have h_partition : (∑ a : (ZMod d)ˣ,
          ∑ q ∈ B.filter (fun q => q % d = ((a : ZMod d).val) % d),
            (1 : ℝ) / (((q - 1 : ℕ) : ℝ))) = D := by
        have h_inner_eq : ∀ (a : (ZMod d)ˣ),
            (∑ q ∈ B.filter (fun q => q % d = ((a : ZMod d).val) % d),
              (1 : ℝ) / (((q - 1 : ℕ) : ℝ))) =
            ∑ q ∈ B, (if q % d = ((a : ZMod d).val) % d
              then (1 : ℝ) / (((q - 1 : ℕ) : ℝ)) else 0) :=
          fun a => Finset.sum_filter _ _
        simp_rw [h_inner_eq]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro q hq
        have hcop_q : Nat.Coprime q d := hcoprime q hq
        have h_a₀_coe : (ZMod.unitOfCoprime q hcop_q : ZMod d) = (q : ZMod d) :=
          ZMod.coe_unitOfCoprime q hcop_q
        -- For each q, the inner sum has exactly one nonzero term: a₀ := ZMod.unitOfCoprime q hcop_q.
        -- Use Finset.sum_eq_single to extract this term.
        rw [Finset.sum_eq_single (ZMod.unitOfCoprime q hcop_q)]
        · -- f (ZMod.unitOfCoprime q hcop_q) = (1/(q-1))
          rw [if_pos]
          -- prove: q % d = (ZMod.unitOfCoprime q hcop_q : ZMod d).val % d
          rw [h_a₀_coe, ZMod.val_natCast, Nat.mod_mod]
        · -- ∀ b ∈ univ, b ≠ ZMod.unitOfCoprime q hcop_q → if cond b then ... else 0 = 0
          intro b _ hb_ne
          rw [if_neg]
          intro hcond
          apply hb_ne
          have h_b_val_lt : (b : ZMod d).val < d := ZMod.val_lt _
          have h_b_val_mod : (b : ZMod d).val % d = (b : ZMod d).val :=
            Nat.mod_eq_of_lt h_b_val_lt
          rw [h_b_val_mod] at hcond
          -- hcond : q % d = (b : ZMod d).val
          -- Goal: b = ZMod.unitOfCoprime q hcop_q
          apply Units.ext
          rw [h_a₀_coe]
          apply ZMod.val_injective d
          rw [ZMod.val_natCast]
          exact hcond.symm
        · -- ZMod.unitOfCoprime q hcop_q ∉ univ → ... (vacuous)
          intro h_not_mem
          exact absurd (Finset.mem_univ _) h_not_mem
      rw [h_partition]
      exact div_self hD_ne
    have hsub_block : ∀ k : ℕ, k < compositeBlockCount y →
        compositeBlock y k ⊆ compositePrimeWindow 20 y := by
      intro k hk
      exact ((hstep2 y hy_step2).2.2 k hk).1
    have hμ_near := conditionalResidueMeasure_near_uniform hy2 hd_ge_2 hd_le_y hsub_block
      (hpmodel_K_good_def ▸ hpos) C_step5 hC_step5_pos
      hstep5_l1 hcondprob_nn hcondprob_sum
    have h_step6 := step6_subset_product_application (K := K) hK_le_one
      (d := d) hd_ge_2 hd_le_y ε_y hε_y_nonneg
      (conditionalResidueMeasure y d K) hμ_nonneg hμ_sum hμ_near
    obtain ⟨h_bound, _hN_le⟩ := h_step6
    -- h_bound : ∑_{g ∈ bad} μ(g) ≤ N/(2^K - 1) + K · ε_y.
    have hK_eq : K = compositeGoodBlockThreshold y := hK_def
    set bad : Finset (Fin K → (ZMod d)ˣ) := Finset.univ.filter
      (fun g : Fin K → (ZMod d)ˣ =>
        ∀ T : Finset (Fin K), T.Nonempty → subsetProd T g ≠ 1) with hbad_def
    -- Chain (b): pmodel(failure ∧ ≥K good) ≤ ∑_{g ∈ bad} num(g).
    -- This requires:
    --   1. failure_implies_bad_residue: failure(S) ∧ ≥K good ⟹ extract S ∈ bad.
    --   2. Pmodel sum decomposition: ∑_{g ∈ bad} pmodel(extract = g ∧ ≥K good)
    --      = pmodel(extract ∈ bad ∧ ≥K good) by partition over g.
    --   3. Monotonicity: pmodel(failure ∧ ≥K good) ≤ pmodel(extract ∈ bad ∧ ≥K good).
    -- Each step is paper-faithful.  Defer the explicit Lean calculation to a sub-claim.
    have h_chain :
        finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => CompositeProductFailure 20 y d S ∧
              ¬ (goodBlockCount S y < compositeGoodBlockThreshold y)) ≤
          ∑ g ∈ bad,
            finitePrimeModelProb (compositePrimeWindow 20 y)
              (fun S => K ≤ goodBlockCount S y ∧
                firstKResidueVector S y d K = g) := by
      classical
      -- Step 1+2: pmodel(failure ∧ ≥K good) ≤ pmodel(≥K good ∧ extract S ∈ bad).
      have h_le : finitePrimeModelProb (compositePrimeWindow 20 y)
                  (fun S => CompositeProductFailure 20 y d S ∧
                    ¬ (goodBlockCount S y < compositeGoodBlockThreshold y)) ≤
                  finitePrimeModelProb (compositePrimeWindow 20 y)
                  (fun S => K ≤ goodBlockCount S y ∧
                    firstKResidueVector S y d K ∈ bad) := by
        unfold finitePrimeModelProb
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro S hS
          simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
          obtain ⟨hSsub, hfail, hKge⟩ := hS
          have hKle : K ≤ goodBlockCount S y := by rw [hK_eq]; omega
          have hbad_mem : firstKResidueVector S y d K ∈ bad := by
            rw [hbad_def, Finset.mem_filter]
            exact ⟨Finset.mem_univ _,
              failure_implies_bad_residue hy2 hy_log_le_y
                hd_ge_2 hd_le_y hK_pos hK_eq
                hSsub hKle hfail⟩
          exact ⟨hSsub, hKle, hbad_mem⟩
        · intro S _ _
          exact selectionWeight_nonneg
            (fun _q hq => compositePrimeWindow_one_le hq)
      -- Step 3: pmodel(≥K good ∧ extract S ∈ bad) = ∑_{g ∈ bad} num(g) via fiberwise sum.
      have h_eq : finitePrimeModelProb (compositePrimeWindow 20 y)
                  (fun S => K ≤ goodBlockCount S y ∧
                    firstKResidueVector S y d K ∈ bad) =
                  ∑ g ∈ bad, finitePrimeModelProb (compositePrimeWindow 20 y)
                    (fun S => K ≤ goodBlockCount S y ∧
                      firstKResidueVector S y d K = g) := by
        unfold finitePrimeModelProb
        -- LHS sum = ∑_{S in filter} weight S where filter = {S : ≥K good ∧ extract S ∈ bad}.
        -- RHS = ∑_{g ∈ bad} ∑_{S in filter (≥K good ∧ extract S = g)} weight S.
        symm
        -- For each g ∈ bad, the inner sum equals the sum over S with extract S = g.
        -- Combine via sum_fiberwise_of_maps_to.
        have : ∀ g ∈ bad,
            (compositePrimeWindow 20 y).powerset.filter
              (fun S => K ≤ goodBlockCount S y ∧ firstKResidueVector S y d K = g) =
            ((compositePrimeWindow 20 y).powerset.filter
              (fun S => K ≤ goodBlockCount S y ∧
                firstKResidueVector S y d K ∈ bad)).filter
              (fun S => firstKResidueVector S y d K = g) := by
          intro g hg
          ext S
          simp only [Finset.mem_filter, Finset.mem_powerset]
          constructor
          · rintro ⟨hSsub, hKle, hext⟩
            refine ⟨⟨hSsub, hKle, ?_⟩, hext⟩
            rw [hext]; exact hg
          · rintro ⟨⟨hSsub, hKle, _⟩, hext⟩
            exact ⟨hSsub, hKle, hext⟩
        have h_inner_eq : ∀ g ∈ bad,
            (compositePrimeWindow 20 y).powerset.filter
              (fun S => K ≤ goodBlockCount S y ∧
                firstKResidueVector S y d K = g) =
            ((compositePrimeWindow 20 y).powerset.filter
              (fun S => K ≤ goodBlockCount S y ∧
                firstKResidueVector S y d K ∈ bad)).filter
              (fun S => firstKResidueVector S y d K = g) := by
          intros g hg
          ext S
          simp only [Finset.mem_filter, Finset.mem_powerset]
          constructor
          · rintro ⟨hsub, hKle, hext⟩
            refine ⟨⟨hsub, hKle, ?_⟩, hext⟩
            rw [hext]; exact hg
          · rintro ⟨⟨hsub, hKle, _⟩, hext⟩
            exact ⟨hsub, hKle, hext⟩
        have h_fiber := Finset.sum_fiberwise_of_maps_to
            (s := (compositePrimeWindow 20 y).powerset.filter
              (fun S => K ≤ goodBlockCount S y ∧
                firstKResidueVector S y d K ∈ bad))
            (t := bad) (g := fun S => firstKResidueVector S y d K)
            (fun S hS => by
              simp only [Finset.mem_filter] at hS
              exact hS.2.2)
            (selectionWeight (compositePrimeWindow 20 y))
        -- After symm above, goal is: ∑_{g ∈ bad} ∑_{S in filter (≥K good ∧ extract = g)} weight = ∑_{S in filter (≥K good ∧ extract ∈ bad)} weight.
        convert h_fiber using 3 with g hg
        ext i
        simp only [Finset.mem_filter, Finset.mem_powerset]
        constructor
        · rintro ⟨hsub, hKle, hext⟩
          refine ⟨⟨hsub, hKle, ?_⟩, hext⟩
          rw [hext]; exact hg
        · rintro ⟨⟨hsub, hKle, _⟩, hext⟩
          exact ⟨hsub, hKle, hext⟩
      linarith
    -- Chain (c)+(d): num(g) = μ(g) · pmodel_K_good (def of μ), so ∑ num = pmodel_K_good · ∑ μ
    --   ≤ ∑ μ since pmodel_K_good ≤ 1.
    have h_num_eq_μ_mul : ∀ g : Fin K → (ZMod d)ˣ,
        finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => K ≤ goodBlockCount S y ∧
              firstKResidueVector S y d K = g) =
          conditionalResidueMeasure y d K g * pmodel_K_good := by
      intro g
      unfold conditionalResidueMeasure
      rw [hpmodel_K_good_def] at hpos
      rw [div_mul_cancel₀ _ hpos]
    have h_num_le_μ : ∀ g : Fin K → (ZMod d)ˣ,
        finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => K ≤ goodBlockCount S y ∧
              firstKResidueVector S y d K = g) ≤
          conditionalResidueMeasure y d K g := by
      intro g
      rw [h_num_eq_μ_mul g]
      have hμ_nn := hμ_nonneg g
      calc conditionalResidueMeasure y d K g * pmodel_K_good
          ≤ conditionalResidueMeasure y d K g * 1 :=
            mul_le_mul_of_nonneg_left hpmodel_K_good_le_one hμ_nn
        _ = conditionalResidueMeasure y d K g := by ring
    -- Chain (e): ∑_{g ∈ bad} num(g) ≤ ∑_{g ∈ bad} μ(g) ≤ N/(2^K-1) + K·ε_y.
    have h_sum_num_le_bound :
        (∑ g ∈ bad, finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => K ≤ goodBlockCount S y ∧
              firstKResidueVector S y d K = g)) ≤
          (d.totient : ℝ) / ((2:ℝ)^K - 1) + (K : ℝ) * ε_y := by
      calc ∑ g ∈ bad, finitePrimeModelProb (compositePrimeWindow 20 y)
            (fun S => K ≤ goodBlockCount S y ∧
              firstKResidueVector S y d K = g)
          ≤ ∑ g ∈ bad, conditionalResidueMeasure y d K g :=
            Finset.sum_le_sum (fun g _ => h_num_le_μ g)
        _ ≤ (d.totient : ℝ) / ((2:ℝ)^K - 1) + (K : ℝ) * ε_y := h_bound
    -- Combine.
    exact h_chain.trans h_sum_num_le_bound

-- Paper §6.2 Step 6 algebra (lines 1773-1786): bound `N/(2^K - 1) + K · ε_y ≤ y^{-c}`.
-- Combines `step6_pmodel_bound` with the arithmetic estimate.
-- Paper takes c_2 = min(κ log 2 - 1, 1/3); we use c := c_2 / 4 with slack.
private lemma pmodel_failure_K_good_no_subproduct :
    ∃ c : ℝ, 0 < c ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ y →
            finitePrimeModelProb (compositePrimeWindow 20 y)
                (fun S => CompositeProductFailure 20 y d S ∧
                  ¬ (goodBlockCount S y < compositeGoodBlockThreshold y)) ≤
              Real.exp (-c * Real.log y) := by
  rcases step6_pmodel_bound with ⟨C5, hC5, y₀_step6, hy₀_step6, hbound⟩
  -- Paper line 1679: κ := ρ γ / 2 with ρ = e^{-1}, γ = 15.
  set κ : ℝ := (Real.exp (-1) * 15) / 2 with hκ_def
  have hκ_pos : 0 < κ := by rw [hκ_def]; positivity
  -- Paper line 1679: κ · log 2 > 1 (numerical).
  have hκlog2 : κ * Real.log 2 > 1 := kappa_log_two_gt_one
  -- c_1 := κ log 2 - 1 (paper line 1784).
  set c1 : ℝ := κ * Real.log 2 - 1 with hc1_def
  have hc1_pos : 0 < c1 := by rw [hc1_def]; linarith
  -- c_2 := min(c_1, 1/3) (paper line 1784).
  set c2 : ℝ := min c1 (1/3) with hc2_def
  have hc2_pos : 0 < c2 := by rw [hc2_def]; exact lt_min hc1_pos (by norm_num)
  -- c := c_2 / 4 with slack.
  set c : ℝ := c2 / 4 with hc_def
  have hc_pos : 0 < c := by rw [hc_def]; positivity
  -- For term2 decay: apply helper with bound `2c < 1/2`.  Then term2 ≤ exp(-2c log y),
  -- which is half of exp(-c log y) for log y ≥ log 2 / c.
  -- c = c2/4 ≤ (1/3)/4 = 1/12, so 2c ≤ 1/6 < 1/2.
  have hc_le_twelfth : c ≤ 1/12 := by
    rw [hc_def, hc2_def]
    have : min c1 (1/3) ≤ 1/3 := min_le_right _ _
    linarith
  have hc_2c_pos : 0 < 2 * c := by positivity
  have hc_2c_lt_half : 2 * c < 1/2 := by linarith
  rcases kappa_logy_eps_decays C5 hC5 hc_2c_pos hc_2c_lt_half with
    ⟨y₀_term2, hy₀_term2_pos, hterm2_bound⟩
  -- y₀ chosen so log y ≥ 4/c (gives c log y ≥ 4, so exp(c log y) ≥ exp(4) ≥ 54 ≥ 3).
  set y₀ : ℝ := max y₀_step6 (max y₀_term2 (max (Real.exp (4 / c)) 16)) with hy₀_def
  refine ⟨c, hc_pos, y₀, ?_, ?_⟩
  · rw [hy₀_def]
    -- 2 ≤ y₀: chain through the maxes.
    have h16 : (16 : ℝ) ≤ max (Real.exp (4 / c)) 16 := le_max_right _ _
    have hsub : max (Real.exp (4 / c)) 16 ≤ max y₀_term2 (max (Real.exp (4 / c)) 16) :=
      le_max_right _ _
    have hsub2 : max y₀_term2 (max (Real.exp (4 / c)) 16) ≤
        max y₀_step6 (max y₀_term2 (max (Real.exp (4 / c)) 16)) := le_max_right _ _
    linarith
  intro y hy d hd_ge_2 hd_le_y
  have hy_step6 : y₀_step6 ≤ y := le_trans (le_max_left _ _) hy
  have hy_term2 : y₀_term2 ≤ y :=
    le_trans (le_max_left _ _) (le_max_right _ _ |>.trans hy)
  have hy_exp_4c : Real.exp (4 / c) ≤ y :=
    le_trans (le_max_left _ _)
      (le_max_right _ _ |>.trans (le_max_right _ _ |>.trans hy))
  have hy_16 : (16 : ℝ) ≤ y :=
    le_trans (le_max_right _ _)
      (le_max_right _ _ |>.trans (le_max_right _ _ |>.trans hy))
  have hy_pos : 0 < y := by linarith
  have hlog_y_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog_y_ge_4_c : 4 / c ≤ Real.log y := by
    have h := Real.log_le_log (Real.exp_pos _) hy_exp_4c
    rwa [Real.log_exp] at h
  -- Apply step6 bound.
  have hb := hbound y hy_step6 d hd_ge_2 hd_le_y
  set K : ℕ := compositeGoodBlockThreshold y with hK_def
  -- (d.totient : ℝ) ≤ y.
  have hN_le_y : (d.totient : ℝ) ≤ y := by
    have h1 : (d.totient : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
    linarith
  have hN_nonneg : (0 : ℝ) ≤ (d.totient : ℝ) := by exact_mod_cast Nat.zero_le _
  -- K ≥ κ log y (from `compositeGoodBlockThreshold = ⌈κ log y⌉₊`, paper line 1708).
  have hK_lower : (κ : ℝ) * Real.log y ≤ (K : ℝ) := by
    rw [hK_def, hκ_def]
    unfold compositeGoodBlockThreshold
    exact Nat.le_ceil _
  -- K > 0.
  have hK_pos : 0 < K := by
    rw [hK_def]
    unfold compositeGoodBlockThreshold
    have hpos : 0 < ((Real.exp (-1) * 15) / 2) * Real.log y :=
      mul_pos (by positivity) hlog_y_pos
    exact Nat.ceil_pos.mpr hpos
  -- 2^K ≥ 2 (since K ≥ 1).
  have h2K_pos : (0 : ℝ) < (2:ℝ)^K := by positivity
  have h2K_ge_2 : (2 : ℝ) ≤ (2:ℝ)^K := by
    calc (2 : ℝ) = (2:ℝ)^1 := by norm_num
      _ ≤ (2:ℝ)^K := by
        apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
        exact hK_pos
  have h2K_minus_1_pos : (0 : ℝ) < (2:ℝ)^K - 1 := by linarith
  -- 2^K - 1 ≥ 2^K / 2 (since 2^K ≥ 2).
  have h2K_minus_1_ge_half_2K : ((2:ℝ)^K) / 2 ≤ (2:ℝ)^K - 1 := by linarith
  -- (2:ℝ)^K = exp(K log 2).
  have h2_pow_K : (2:ℝ)^K = Real.exp ((K : ℝ) * Real.log 2) := by
    rw [show (2:ℝ) = Real.exp (Real.log 2) from
      (Real.exp_log (by norm_num : (0:ℝ) < 2)).symm]
    rw [← Real.exp_nat_mul]
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)]
  -- N/(2^K - 1) ≤ 2 y · exp(-(κ log 2) · log y) = 2 · exp(-(κ log 2 - 1) · log y) = 2 · exp(-c1 log y).
  have hterm1 : (d.totient : ℝ) / ((2:ℝ)^K - 1) ≤ 2 * Real.exp (-c1 * Real.log y) := by
    have hdiv1 : (d.totient : ℝ) / ((2:ℝ)^K - 1) ≤ y / ((2:ℝ)^K - 1) :=
      div_le_div_of_nonneg_right hN_le_y h2K_minus_1_pos.le
    have hdiv2 : y / ((2:ℝ)^K - 1) ≤ y / ((2:ℝ)^K / 2) :=
      div_le_div_of_nonneg_left hy_pos.le (div_pos h2K_pos (by norm_num))
        h2K_minus_1_ge_half_2K
    have hdiv3 : y / ((2:ℝ)^K / 2) = 2 * y / (2:ℝ)^K := by
      rw [div_div_eq_mul_div]; ring
    have h2K_ge_yκlog2 : Real.exp ((κ * Real.log 2) * Real.log y) ≤ (2:ℝ)^K := by
      rw [h2_pow_K]
      apply Real.exp_le_exp.mpr
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have := mul_le_mul_of_nonneg_right hK_lower hlog2_pos.le
      nlinarith [this]
    have hinv_2K_le : ((2:ℝ)^K)⁻¹ ≤ Real.exp (-((κ * Real.log 2) * Real.log y)) := by
      rw [show Real.exp (-((κ * Real.log 2) * Real.log y)) =
          (Real.exp ((κ * Real.log 2) * Real.log y))⁻¹ by rw [Real.exp_neg]]
      exact inv_anti₀ (Real.exp_pos _) h2K_ge_yκlog2
    have hdiv4 : 2 * y / (2:ℝ)^K ≤ 2 * y * Real.exp (-((κ * Real.log 2) * Real.log y)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv_2K_le (by positivity)
    have hclean : 2 * y * Real.exp (-((κ * Real.log 2) * Real.log y)) =
        2 * Real.exp (-c1 * Real.log y) := by
      rw [hc1_def]
      -- Express `y * exp(-(κ log 2) log y) = exp(log y - (κ log 2) log y) = exp(-(κ log 2 - 1) log y)`
      -- without rewriting `y` everywhere (which would loop on `log y`).
      have h_y_factor : y * Real.exp (-((κ * Real.log 2) * Real.log y)) =
          Real.exp (-(κ * Real.log 2 - 1) * Real.log y) := by
        rw [show -(κ * Real.log 2 - 1) * Real.log y =
            Real.log y + (-((κ * Real.log 2) * Real.log y)) by ring]
        rw [Real.exp_add, Real.exp_log hy_pos]
      rw [show 2 * y * Real.exp (-((κ * Real.log 2) * Real.log y)) =
          2 * (y * Real.exp (-((κ * Real.log 2) * Real.log y))) by ring]
      rw [h_y_factor]
    linarith [hclean ▸ (hdiv1.trans (hdiv2.trans (hdiv3.trans_le hdiv4)))]
  -- K · ε_y ≤ exp(-c log y).  Use crude bound K ≤ y^{1/12}, C5 · y^{1/12 - 1/2} ≤ y^{-1/3} for y large.
  -- We bound this term by exp(-c log y) directly using y₀ ≥ exp(4/c).
  -- Specifically: K ≤ κ log y + 1, ε_y = C5 · y^{-1/2}.
  -- K · ε_y ≤ (κ log y + 1) · C5 · y^{-1/2}.
  -- For y ≥ exp(4/c), log y ≥ 4/c, so c log y ≥ 4 and y^c ≥ exp(4).
  -- We need K · C5 · y^{-1/2} ≤ exp(-c log y) = y^{-c}.
  -- I.e., (κ log y + 1) · C5 ≤ y^{1/2 - c}.
  -- For c ≤ 1/12, 1/2 - c ≥ 5/12, and (κ log y + 1) · C5 = O(log y) ≤ y^{1/12} for y large.
  -- So K · ε_y ≤ y^{1/12} · y^{-1/2} = y^{-5/12} ≤ y^{-c}.
  have hK_upper : (K : ℝ) ≤ κ * Real.log y + 1 := by
    rw [hK_def]
    unfold compositeGoodBlockThreshold
    rw [hκ_def]
    have hpos : 0 ≤ ((Real.exp (-1) * 15) / 2) * Real.log y :=
      mul_nonneg (by positivity) hlog_y_pos.le
    have h := Nat.ceil_lt_add_one hpos
    linarith
  -- term2: K · ε_y ≤ exp(-2c · log y) by helper `kappa_logy_eps_decays` with bound 2c.
  have hterm2 : (compositeGoodBlockThreshold y : ℝ) * (C5 * y ^ (-(1:ℝ)/2)) ≤
      Real.exp (-(2*c) * Real.log y) := by
    have hb_term2 := hterm2_bound y hy_term2
    have hK_R_le : (K : ℝ) ≤ ((Real.exp (-1) * 15) / 2) * Real.log y + 1 := by
      have h := hK_upper
      rw [hκ_def] at h
      exact h
    have hε_pos : 0 ≤ C5 * y ^ (-(1:ℝ)/2) := by
      apply mul_nonneg hC5.le
      apply Real.rpow_nonneg hy_pos.le
    calc (compositeGoodBlockThreshold y : ℝ) * (C5 * y ^ (-(1:ℝ)/2))
        = (K : ℝ) * (C5 * y ^ (-(1:ℝ)/2)) := by rw [hK_def]
      _ ≤ (((Real.exp (-1) * 15) / 2) * Real.log y + 1) * (C5 * y ^ (-(1:ℝ)/2)) :=
          mul_le_mul_of_nonneg_right hK_R_le hε_pos
      _ ≤ Real.exp (-(2*c) * Real.log y) := hb_term2
  -- Combine: pmodel ≤ term1 + term2 ≤ 2 · exp(-c1 log y) + exp(-2c · log y) ≤ exp(-c log y).
  -- Bound term1 + term2:
  --   term1 = N/(2^K - 1) ≤ 2 exp(-c1 log y) ≤ exp(-2c log y) (since c1 ≥ 4c, log y ≥ log 2 / (c1 - 2c)).
  --   term2 ≤ exp(-2c log y).
  --   sum ≤ 2 exp(-2c log y) ≤ exp(-c log y) (since log y ≥ log 2 / c).
  --
  -- We have log y ≥ 4/c.  Need (c1 - 2c) log y ≥ log 2, i.e., (c1 - 2c) · (4/c) ≥ log 2.
  -- Since c1 ≥ 4c (c = c2/4 ≤ c1/4), c1 - 2c ≥ 2c.  So 4(c1 - 2c)/c ≥ 8 ≥ log 2. ✓
  -- Need c · log y ≥ log 2, i.e., c · (4/c) = 4 ≥ log 2. ✓
  have hlog2_lt_4 : Real.log 2 < 4 := by
    have := Real.log_two_lt_d9; linarith
  have hc1_ge_4c : c1 ≥ 4 * c := by
    rw [hc_def, hc2_def]
    have h1 : min c1 (1/3) ≤ c1 := min_le_left _ _
    linarith
  have hc1_minus_2c_pos : 0 < c1 - 2 * c := by linarith
  have hclog_ge_4 : 4 ≤ c * Real.log y := by
    have h : 4 / c ≤ Real.log y := hlog_y_ge_4_c
    have hc_pos' : 0 < c := hc_pos
    rw [div_le_iff₀ hc_pos'] at h
    linarith
  -- term1 ≤ exp(-2c log y).
  have hterm1_to_2c :
      2 * Real.exp (-c1 * Real.log y) ≤ Real.exp (-(2*c) * Real.log y) := by
    -- 2 ≤ exp((c1 - 2c) log y).  Have (c1 - 2c) log y ≥ 2 · (c · log y) ≥ 2 · 4 = 8 ≥ log 2.
    have hkey : (c1 - 2*c) * Real.log y ≥ Real.log 2 := by
      have h1 : c1 - 2*c ≥ 2*c := by linarith
      have h2 : (c1 - 2*c) * Real.log y ≥ (2*c) * Real.log y := by
        apply mul_le_mul_of_nonneg_right h1 hlog_y_pos.le
      have h3 : (2*c) * Real.log y ≥ 8 := by
        have := hclog_ge_4
        nlinarith
      linarith
    have hexp_log2 : (2 : ℝ) ≤ Real.exp ((c1 - 2*c) * Real.log y) := by
      have h := Real.exp_le_exp.mpr hkey
      rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
      exact h
    have heq : Real.exp (-(2*c) * Real.log y) =
        Real.exp ((c1 - 2*c) * Real.log y) * Real.exp (-c1 * Real.log y) := by
      rw [← Real.exp_add]
      congr 1; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hexp_log2 (Real.exp_pos _).le
  have hterm1_2c : (d.totient : ℝ) / ((2:ℝ)^K - 1) ≤ Real.exp (-(2*c) * Real.log y) :=
    hterm1.trans hterm1_to_2c
  -- sum ≤ 2 exp(-2c log y) ≤ exp(-c log y).
  have hclog_ge_log2 : c * Real.log y ≥ Real.log 2 := by
    have := hclog_ge_4; linarith
  have h2_le_expc : (2 : ℝ) ≤ Real.exp (c * Real.log y) := by
    have h := Real.exp_le_exp.mpr hclog_ge_log2
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h
    exact h
  have hsum_bound : 2 * Real.exp (-(2*c) * Real.log y) ≤ Real.exp (-c * Real.log y) := by
    have heq : Real.exp (-c * Real.log y) =
        Real.exp (c * Real.log y) * Real.exp (-(2*c) * Real.log y) := by
      rw [← Real.exp_add]
      congr 1; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right h2_le_expc (Real.exp_pos _).le
  -- Final assembly.
  calc finitePrimeModelProb (compositePrimeWindow 20 y)
        (fun S => CompositeProductFailure 20 y d S ∧
          ¬ (goodBlockCount S y < compositeGoodBlockThreshold y))
      ≤ (d.totient : ℝ) / ((2:ℝ)^(compositeGoodBlockThreshold y) - 1) +
          (compositeGoodBlockThreshold y : ℝ) * (C5 * y ^ (-(1:ℝ)/2)) := hb
    _ = (d.totient : ℝ) / ((2:ℝ)^K - 1) +
          (compositeGoodBlockThreshold y : ℝ) * (C5 * y ^ (-(1:ℝ)/2)) := by rw [hK_def]
    _ ≤ Real.exp (-(2*c) * Real.log y) + Real.exp (-(2*c) * Real.log y) :=
        add_le_add hterm1_2c hterm2
    _ = 2 * Real.exp (-(2*c) * Real.log y) := by ring
    _ ≤ Real.exp (-c * Real.log y) := hsum_bound

-- Paper §6.2 lines 1786-1815 (case d ≥ 2, Step 7 union-bound assembly).
-- Combines step4 (P(<K good) ≤ y^{-c₁}) with `pmodel_failure_K_good_no_subproduct` (≤ y^{-c₂}).
private lemma pmodel_failure_d_ge_2_bound :
    ∃ c : ℝ, 0 < c ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 2 ≤ d → (d : ℝ) ≤ y →
            finitePrimeModelProb (compositePrimeWindow 20 y)
                (CompositeProductFailure 20 y d) ≤
              Real.exp (-c * Real.log y) := by
  rcases step4_chernoff_good_blocks with ⟨c1, hc1, y0_step4, hy0_step4, hchernoff⟩
  rcases pmodel_failure_K_good_no_subproduct with ⟨c2, hc2, y0_step6, hy0_step6, hbound_step6⟩
  set c : ℝ := min c1 c2 / 2 with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]; exact div_pos (lt_min hc1 hc2) (by norm_num)
  have hmin_pos : (0 : ℝ) < min c1 c2 := lt_min hc1 hc2
  -- y₀ : need y ≥ y0_step4, y0_step6, and 2 ≤ y^{min(c1,c2)/2} (so 2 exp(-min*log y) ≤ exp(-c log y)).
  set y₀ : ℝ := max (max y0_step4 y0_step6) (max 2 (Real.exp (2 * Real.log 2 / min c1 c2))) with hy0_def
  refine ⟨c, hc_pos, y₀, ?_, ?_⟩
  · rw [hy0_def]; exact le_max_of_le_right (le_max_left _ _)
  intro y hy d hd_ge_2 hd_le_y
  have hy_step4 : y0_step4 ≤ y :=
    le_trans (le_max_left _ _) (le_max_left _ _ |>.trans hy)
  have hy_step6 : y0_step6 ≤ y :=
    le_trans (le_max_right _ _) (le_max_left _ _ |>.trans hy)
  have hy_2 : (2 : ℝ) ≤ y :=
    le_trans (le_max_left _ _) (le_max_right _ _ |>.trans hy)
  have hy_4_min : Real.exp (2 * Real.log 2 / min c1 c2) ≤ y :=
    le_trans (le_max_right _ _) (le_max_right _ _ |>.trans hy)
  have hy_pos : 0 < y := by linarith
  have hlog_y_pos : 0 < Real.log y := Real.log_pos (by linarith)
  -- Apply finitePrimeModelProb_le_split to decompose:
  -- P(failure) ≤ P(<K good) + P(failure ∧ ≥K good)
  have hwindow_one_le : ∀ q ∈ compositePrimeWindow 20 y, 1 ≤ q :=
    fun q hq => compositePrimeWindow_one_le hq
  have h_split := finitePrimeModelProb_le_split (U := compositePrimeWindow 20 y)
    hwindow_one_le (CompositeProductFailure 20 y d)
    (fun S => goodBlockCount S y < compositeGoodBlockThreshold y)
  -- Bound P(<K good) by step4.
  have h_step4 := hchernoff y hy_step4
  -- Bound P(failure ∧ ≥K good) by sub-claim.
  have h_step6 := hbound_step6 y hy_step6 d hd_ge_2 hd_le_y
  -- Combine: P(failure) ≤ y^{-c1} + y^{-c2} ≤ 2 y^{-min(c1,c2)} ≤ y^{-c}.
  -- Need: 2 exp(-min(c1,c2) log y) ≤ exp(-c log y) ⟺ 2 ≤ y^{min/2}.
  have hkey : Real.exp (-c1 * Real.log y) + Real.exp (-c2 * Real.log y) ≤
      Real.exp (-c * Real.log y) := by
    have hexp_c1 : Real.exp (-c1 * Real.log y) ≤ Real.exp (-(min c1 c2) * Real.log y) := by
      apply Real.exp_le_exp.mpr
      have : -c1 ≤ -(min c1 c2) := by
        have := min_le_left c1 c2; linarith
      exact mul_le_mul_of_nonneg_right this hlog_y_pos.le
    have hexp_c2 : Real.exp (-c2 * Real.log y) ≤ Real.exp (-(min c1 c2) * Real.log y) := by
      apply Real.exp_le_exp.mpr
      have : -c2 ≤ -(min c1 c2) := by
        have := min_le_right c1 c2; linarith
      exact mul_le_mul_of_nonneg_right this hlog_y_pos.le
    have hsum_le : Real.exp (-c1 * Real.log y) + Real.exp (-c2 * Real.log y) ≤
        2 * Real.exp (-(min c1 c2) * Real.log y) := by linarith
    -- Now: 2 exp(-min * log y) ≤ exp(-c log y) iff 2 ≤ y^{min - c} = y^{min/2}.
    have hlog_y_ge : 2 * Real.log 2 / min c1 c2 ≤ Real.log y := by
      have h := Real.log_le_log (Real.exp_pos _) hy_4_min
      rwa [Real.log_exp] at h
    have h_min_half_log : Real.log 2 ≤ min c1 c2 / 2 * Real.log y := by
      rw [div_le_iff₀ hmin_pos] at hlog_y_ge
      nlinarith [hlog_y_ge]
    have h_diff : Real.log 2 ≤ ((min c1 c2) - c) * Real.log y := by
      have hsub : min c1 c2 / 2 ≤ (min c1 c2) - c := by
        rw [hc_def]; linarith
      have := mul_le_mul_of_nonneg_right hsub hlog_y_pos.le
      linarith
    have hexp_le : (2 : ℝ) ≤ Real.exp (((min c1 c2) - c) * Real.log y) := by
      have h := Real.exp_le_exp.mpr h_diff
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
      exact h
    have hmul : 2 * Real.exp (-(min c1 c2) * Real.log y) ≤
        Real.exp (((min c1 c2) - c) * Real.log y) * Real.exp (-(min c1 c2) * Real.log y) :=
      mul_le_mul_of_nonneg_right hexp_le (Real.exp_pos _).le
    rw [← Real.exp_add] at hmul
    have hadd : ((min c1 c2) - c) * Real.log y + -(min c1 c2) * Real.log y =
        -c * Real.log y := by ring
    rw [hadd] at hmul
    linarith
  linarith

private lemma pmodel_composite_product_failure_bound :
    ∃ c : ℝ, 0 < c ∧
      ∃ y₀ : ℝ, 2 ≤ y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ y →
            finitePrimeModelProb (compositePrimeWindow 20 y)
                (CompositeProductFailure 20 y d) ≤
              Real.exp (-c * Real.log y) / 2 := by
  -- Paper §6.2 line 1533-1554 (case d=1, Mertens on sub-window) + lines 1556-1816 (case d≥2, steps 1-7).
  rcases pmodel_failure_d_1_bound with ⟨y0_d1, hy0_d1, hbound_d1⟩
  rcases pmodel_failure_d_ge_2_bound with ⟨c2, hc2, y0_d2, hy0_d2, hbound_d2⟩
  -- Take c := min(1/2, c2) / 2.  Always satisfies c ≤ 1/4 (so 1/2 - c ≥ 1/4 > 0)
  -- and c ≤ c2/2 when c2 ≤ 1/2 (else c2 - c = c2 - 1/4 ≥ c2/2).
  set c : ℝ := min ((1 : ℝ) / 2) c2 / 2 with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]
    exact div_pos (lt_min (by norm_num : (0:ℝ) < 1/2) hc2) (by norm_num)
  have hc_le_quarter : c ≤ 1 / 4 := by
    rw [hc_def]
    have hmin : min ((1 : ℝ) / 2) c2 ≤ 1/2 := min_le_left _ _
    linarith
  have hc_le_c2 : 2 * c ≤ c2 := by
    rw [hc_def]
    have hmin : min ((1 : ℝ) / 2) c2 ≤ c2 := min_le_right _ _
    linarith
  -- y₀ chosen so that 2 ≤ y^{1/4} (for d=1) and 2 ≤ y^{c2-c} (for d ≥ 2).
  set y₀ : ℝ := max (max y0_d1 y0_d2) (max 16 (Real.exp (2 * Real.log 2 / c2))) with hy0_def
  refine ⟨c, hc_pos, y₀, ?_, ?_⟩
  · -- 2 ≤ y₀
    rw [hy0_def]
    have h16 : (16 : ℝ) ≤ max 16 (Real.exp (2 * Real.log 2 / c2)) := le_max_left _ _
    have : (2 : ℝ) ≤ 16 := by norm_num
    linarith [le_max_right (max y0_d1 y0_d2) (max 16 (Real.exp (2 * Real.log 2 / c2)))]
  intro y hy d hd_pos hd_le_y
  have hy_d1 : y0_d1 ≤ y := le_trans (le_max_left _ _) (le_max_left _ _ |>.trans hy)
  have hy_d2 : y0_d2 ≤ y := le_trans (le_max_right _ _) (le_max_left _ _ |>.trans hy)
  have hy_16 : (16 : ℝ) ≤ y := le_trans (le_max_left _ _) (le_max_right _ _ |>.trans hy)
  have hy_4_c2 : Real.exp (2 * Real.log 2 / c2) ≤ y :=
    le_trans (le_max_right _ _) (le_max_right _ _ |>.trans hy)
  have hy_2 : (2 : ℝ) ≤ y := by linarith
  have hy_pos : 0 < y := by linarith
  have hlog_y_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog_2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- For d ≥ 2: c2 - c ≥ c2/2, and y^{c2/2} ≥ 2 from hy_4_c2.
  -- ⟹ 2 exp(-c2 log y) ≤ exp(-c log y).
  -- For d = 1: y^{1/4} ≥ 2 from y ≥ 16, so log 2 ≤ (1/2 - c) log y.
  -- ⟹ 2 exp(-(1/2) log y) ≤ exp(-c log y).
  have hkey_d2 : 2 * Real.exp (-c2 * Real.log y) ≤ Real.exp (-c * Real.log y) := by
    have hlog_y_ge : 2 * Real.log 2 / c2 ≤ Real.log y := by
      have h := Real.log_le_log (Real.exp_pos _) hy_4_c2
      rwa [Real.log_exp] at h
    have h_c2_half_log : Real.log 2 ≤ c2 / 2 * Real.log y := by
      have h_pos : (0 : ℝ) < c2 := hc2
      rw [div_le_iff₀ h_pos] at hlog_y_ge
      nlinarith [hlog_y_ge]
    have h_c2_minus_c : Real.log 2 ≤ (c2 - c) * Real.log y := by
      have : c2 / 2 ≤ c2 - c := by linarith
      have hlog_pos : 0 ≤ Real.log y := hlog_y_pos.le
      have := mul_le_mul_of_nonneg_right this hlog_pos
      linarith
    have : Real.exp (Real.log 2) ≤ Real.exp ((c2 - c) * Real.log y) :=
      Real.exp_le_exp.mpr h_c2_minus_c
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at this
    have hmul : 2 * Real.exp (-c2 * Real.log y) ≤
        Real.exp ((c2 - c) * Real.log y) * Real.exp (-c2 * Real.log y) :=
      mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    rw [← Real.exp_add] at hmul
    have hadd : (c2 - c) * Real.log y + -c2 * Real.log y = -c * Real.log y := by ring
    rw [hadd] at hmul
    exact hmul
  have hkey_d1 : 2 * Real.exp (-(1/2) * Real.log y) ≤ Real.exp (-c * Real.log y) := by
    -- y ≥ 16 ⟹ log y ≥ 4 log 2 ⟹ log 2 ≤ (1/4) log y ≤ (1/2 - c) log y.
    have hlog_y_ge_4log2 : 4 * Real.log 2 ≤ Real.log y := by
      have h16_pos : (0 : ℝ) < 16 := by norm_num
      have hlog_16 : Real.log 16 ≤ Real.log y := Real.log_le_log h16_pos hy_16
      have h16_eq : Real.log 16 = 4 * Real.log 2 := by
        have : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
        rw [this, Real.log_pow]; ring
      linarith
    have h_quarter_log : Real.log 2 ≤ (1/4) * Real.log y := by linarith
    have h_half_minus_c : Real.log 2 ≤ ((1:ℝ)/2 - c) * Real.log y := by
      have hsub : (1:ℝ)/4 ≤ 1/2 - c := by linarith
      have hlog_nn : 0 ≤ Real.log y := hlog_y_pos.le
      have hmul := mul_le_mul_of_nonneg_right hsub hlog_nn
      linarith
    have hexp_le : Real.exp (Real.log 2) ≤ Real.exp (((1:ℝ)/2 - c) * Real.log y) :=
      Real.exp_le_exp.mpr h_half_minus_c
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp_le
    have hmul : 2 * Real.exp (-(1/2) * Real.log y) ≤
        Real.exp (((1:ℝ)/2 - c) * Real.log y) * Real.exp (-(1/2) * Real.log y) :=
      mul_le_mul_of_nonneg_right hexp_le (Real.exp_pos _).le
    rw [← Real.exp_add] at hmul
    have hadd : ((1:ℝ)/2 - c) * Real.log y + -(1/2) * Real.log y = -c * Real.log y := by ring
    rw [hadd] at hmul
    exact hmul
  -- Case split.
  by_cases hd1 : d = 1
  · subst hd1
    have h := hbound_d1 y hy_d1
    -- pmodel ≤ exp(-(1/2) log y) ≤ exp(-c log y) / 2
    linarith
  · have hd_ge_2 : 2 ≤ d := by omega
    have h := hbound_d2 y hy_d2 d hd_ge_2 hd_le_y
    -- pmodel ≤ exp(-c2 log y) ≤ exp(-c log y) / 2
    linarith

private lemma step7_residue_density_bound :
    ∃ c : ℝ, 0 < c ∧
      ∃ y₀ : ℝ, 0 < y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ y →
            (Nat.card
              {r : Fin (compositeSuccessorCRTPeriod 20 y d) //
                CompositeSuccessorCoreBad 20 y d r.val} : ℝ) /
              (compositeSuccessorCRTPeriod 20 y d : ℝ) ≤
              Real.exp (-c * Real.log y) / 2 := by
  -- Combine the bridge `residue_density_le_pmodel_bridge` with the product-model
  -- bound `pmodel_composite_product_failure_bound`.
  rcases pmodel_composite_product_failure_bound with ⟨c, hc, y₀, hy₀, hpmodel⟩
  refine ⟨c, hc, max y₀ 2, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (le_max_right _ _)
  intro y hy d hd_pos hd_le_y
  have hy_y₀ : y₀ ≤ y := (le_max_left _ _).trans hy
  have hy_two : (2 : ℝ) ≤ y := (le_max_right _ _).trans hy
  exact (residue_density_le_pmodel_bridge hy_two hd_pos hd_le_y).trans
    (hpmodel y hy_y₀ d hd_pos hd_le_y)

/-! ### The paper-§6.2-faithful integer-density form of Lemma 6.2.

The previous decomposition (Mertens bridge + finite-sieve-count, removed 2026-04-28)
was **structurally wrong**: it required constructing a deterministic finite set `S`
with high reciprocal mass for arbitrary `d ≤ y`, which is impossible for
`d > (log y)^A` (no Siegel–Walfisz lower bound + pairwise-coprime constraint).
Paper §6.2's proof uses **subset products + Chernoff over good blocks +
conditional residue uniformity + Lemma 6.1 (`subset_product_main`)**, which
is captured in the deferred lemma below; transfer to integer density is via
`crt_transfer` (Lemma 2.7) applied with cutoff `P = ⌊exp(y^A)⌋`.

The single deferred lemma `composite_successor_pmodel_density` encodes the
combined statement of paper Lemma 6.2 + Lemma 2.7. Its proof (paper §6.2 Steps
1-7 + §7.4 CRT bookkeeping) is the only remaining analytic obligation in this
file. -/
/-! ### d-conditional strengthening of Lemma 6.2.

The naive integer-density bound `|bad(A,y,d,x)| ≤ exp(-c log y) · x` becomes
trivial when `d` is large because density-among-multiples-of-d blows up by a
factor of `d`.  The paper actually proves the stronger d-conditional form
`P(stage fails | d ∣ n) ≤ y^{-c}`, which after CRT transfer gives
`|bad(A,y,d,x)| ≤ exp(-c log y) · x / d`.  This strengthening is essential
for the d-summation in the H-chain proof (paper §7.2 line 1944-1976):
`∑_{d ≤ y_j} 1/d = O(log y_j)`, so the d-conditional sum
`∑_d exp(-c log y) · x / d ≤ (log y) · exp(-c log y) · x → 0`. -/

/-- Strong d-conditional residue-density bridge: `ρ(y,d) ≤ pmodel/d`.

The existing `residue_density_le_pmodel_bridge` uses `1 ≤ d` to weaken the
intermediate bound `bad_card ≤ primorial · pmodel` into `bad_card ≤ pmodel · M`
where `M = d · primorial`, giving `ρ ≤ pmodel`.  We instead retain the tighter
`bad_card ≤ primorial · pmodel` and divide by `M = d · primorial` to get
`ρ ≤ pmodel / d`. -/
private lemma residue_density_le_pmodel_bridge_strong {y : ℝ} (hy : 2 ≤ y)
    {d : ℕ} (hd : 1 ≤ d) (hd_le_y : (d : ℝ) ≤ y) :
    (Nat.card {r : Fin (compositeSuccessorCRTPeriod 20 y d) //
        CompositeSuccessorCoreBad 20 y d r.val} : ℝ) /
      (compositeSuccessorCRTPeriod 20 y d : ℝ) ≤
      finitePrimeModelProb (compositePrimeWindow 20 y)
        (CompositeProductFailure 20 y d) / (d : ℝ) := by
  classical
  rw [cs_fin_card_subtype_eq_range_filter_card]
  unfold compositeSuccessorCRTPeriod
  rw [coreBad_card_eq_no_good_quotient hy hd hd_le_y]
  have hStepB := step_b_count_no_good_le_primorial_pmodel hy hd hd_le_y
  have hd_pos_R : (0 : ℝ) < d := by exact_mod_cast hd
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos_R
  have hprimorial_pos_R :
      (0 : ℝ) < (primorial (compositeSuccessorCutoff 20 y) : ℝ) := by
    exact_mod_cast cs_primorial_pos _
  have hprimorial_ne : (primorial (compositeSuccessorCutoff 20 y) : ℝ) ≠ 0 :=
    ne_of_gt hprimorial_pos_R
  have hcast :
      ((d * primorial (compositeSuccessorCutoff 20 y) : ℕ) : ℝ) =
        (d : ℝ) * (primorial (compositeSuccessorCutoff 20 y) : ℝ) := by push_cast; ring
  rw [hcast]
  have hM_pos : (0 : ℝ) < (d : ℝ) * (primorial (compositeSuccessorCutoff 20 y) : ℝ) := by
    positivity
  have hpmodel_nonneg :
      0 ≤ finitePrimeModelProb (compositePrimeWindow 20 y)
        (CompositeProductFailure 20 y d) := by
    apply finitePrimeModelProb_nonneg
    intro q hq; exact compositePrimeWindow_one_le hq
  -- Goal: bad/M ≤ pmodel/d.  Equivalent to bad ≤ (pmodel/d) · M = pmodel · primorial.
  rw [div_le_iff₀ hM_pos]
  have h_eq : finitePrimeModelProb (compositePrimeWindow 20 y)
        (CompositeProductFailure 20 y d) / (d : ℝ) *
        ((d : ℝ) * (primorial (compositeSuccessorCutoff 20 y) : ℝ)) =
      (primorial (compositeSuccessorCutoff 20 y) : ℝ) *
        finitePrimeModelProb (compositePrimeWindow 20 y)
          (CompositeProductFailure 20 y d) := by
    field_simp
  rw [h_eq]
  exact hStepB

/-- Strong d-conditional residue density bound: `ρ(y,d) ≤ exp(-c log y) / (2d)`. -/
lemma step7_residue_density_bound_strong :
    ∃ c : ℝ, 0 < c ∧
      ∃ y₀ : ℝ, 0 < y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ y →
            (Nat.card
              {r : Fin (compositeSuccessorCRTPeriod 20 y d) //
                CompositeSuccessorCoreBad 20 y d r.val} : ℝ) /
              (compositeSuccessorCRTPeriod 20 y d : ℝ) ≤
              Real.exp (-c * Real.log y) / (2 * (d : ℝ)) := by
  rcases pmodel_composite_product_failure_bound with ⟨c, hc, y₀, hy₀, hpmodel⟩
  refine ⟨c, hc, max y₀ 2, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (le_max_right _ _)
  intro y hy d hd_pos hd_le_y
  have hy_y₀ : y₀ ≤ y := (le_max_left _ _).trans hy
  have hy_two : (2 : ℝ) ≤ y := (le_max_right _ _).trans hy
  have hd_pos_R : (0 : ℝ) < d := by exact_mod_cast hd_pos
  have hbridge := residue_density_le_pmodel_bridge_strong hy_two hd_pos hd_le_y
  have hpb := hpmodel y hy_y₀ d hd_pos hd_le_y
  -- ρ ≤ pmodel / d ≤ (exp(-c log y) / 2) / d = exp(-c log y) / (2d).
  calc (Nat.card
            {r : Fin (compositeSuccessorCRTPeriod 20 y d) //
              CompositeSuccessorCoreBad 20 y d r.val} : ℝ) /
          (compositeSuccessorCRTPeriod 20 y d : ℝ)
      ≤ finitePrimeModelProb (compositePrimeWindow 20 y)
          (CompositeProductFailure 20 y d) / (d : ℝ) := hbridge
    _ ≤ (Real.exp (-c * Real.log y) / 2) / (d : ℝ) := by
        apply div_le_div_of_nonneg_right hpb hd_pos_R.le
    _ = Real.exp (-c * Real.log y) / (2 * (d : ℝ)) := by
        field_simp

/-- **Public residue-density form of Lemma 6.2 (paper §6.2 line 1517-1525).**

The product-model failure probability for parent `d` at scale `y` is bounded
by `exp(-c log y) / 2 = y^{-c}/2`, expressed as a residue density modulo
`M_d := d · primorial(⌊exp(y^20)⌋)`.

This is the SHARP product-model bound: among `M_d` residues, the fraction
satisfying "no admissible squarefree product `e ≡ 1 [MOD d]` of selected primes"
is at most `y^{-c}/2`.  Used by the H-chain proof in `LowerBoundH.lean` to
bound the stage-failure density at the residue level (paper §7.4 line 2049). -/
theorem composite_successor_residue_density :
    ∃ c : ℝ, 0 < c ∧
      ∃ y₀ : ℝ, 0 < y₀ ∧
        ∀ y : ℝ, y₀ ≤ y →
          ∀ d : ℕ, 1 ≤ d → (d : ℝ) ≤ y →
            (Nat.card
              {r : Fin (compositeSuccessorCRTPeriod 20 y d) //
                CompositeSuccessorCoreBad 20 y d r.val} : ℝ) /
              (compositeSuccessorCRTPeriod 20 y d : ℝ) ≤
              Real.exp (-c * Real.log y) / 2 :=
  step7_residue_density_bound

end Erdos696
