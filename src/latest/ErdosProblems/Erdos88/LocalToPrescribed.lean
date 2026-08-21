import ErdosProblems.Erdos88.AKSPrescribed
import ErdosProblems.Erdos88.Assembly
import ErdosProblems.Erdos88.Probability

open Classical SimpleGraph

namespace Erdos88

noncomputable def liftOverFinSubset {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (T : Finset (Fin A.card)) : Finset (Fin n) :=
  let H := G.induce (A : Set (Fin n))
  let e := H.overFinIso (card_subtype_coe_finset A)
  (T.map e.symm.toEquiv.toEmbedding).image Subtype.val

lemma liftOverFinSubset_subset {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (T : Finset (Fin A.card)) :
    liftOverFinSubset G A T ⊆ A := by
  intro x hx
  simp only [liftOverFinSubset, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact y.property

lemma inducedEdges_liftOverFinSubset {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) (T : Finset (Fin A.card)) :
    inducedEdges G (liftOverFinSubset G A T) =
      inducedEdges ((G.induce (A : Set (Fin n))).overFin
        (card_subtype_coe_finset A)) T := by
  let H := G.induce (A : Set (Fin n))
  let e := H.overFinIso (card_subtype_coe_finset A)
  let sT : Set (Fin A.card) := T
  let sA : Set A := e.symm '' sT
  let sV : Set (Fin n) := Subtype.val '' sA
  have hbij : Set.BijOn e.symm sT sA := by
    exact e.symm.toEquiv.bijOn_image
  let iso₁ : (H.overFin (card_subtype_coe_finset A)).induce sT ≃g H.induce sA :=
    e.symm.induce hbij
  let ev : sA ≃ sV := Equiv.Set.image Subtype.val sA Subtype.val_injective
  let iso₂ : H.induce sA ≃g G.induce sV :=
    { toEquiv := ev
      map_rel_iff' := by intro x y; rfl }
  have hU : (↑(liftOverFinSubset G A T) : Set (Fin n)) = sV := by
    ext x
    simp [liftOverFinSubset, sV, sA, sT, e, H]
  let iso₂' : H.induce sA ≃g
      G.induce (↑(liftOverFinSubset G A T) : Set (Fin n)) := by
    rw [hU]
    exact iso₂
  rw [inducedEdges_eq_card_edgeFinset_induce,
    inducedEdges_eq_card_edgeFinset_induce]
  exact (iso₂'.comp iso₁).card_edgeFinset_eq.symm

/-- The first `k` vertices of `Fin n`, with `k` allowed to exceed `n`. -/
def finPrefix (n k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.val < k

@[simp] lemma mem_finPrefix {n k : ℕ} (i : Fin n) :
    i ∈ finPrefix n k ↔ i.val < k := by
  simp [finPrefix]

lemma card_finPrefix {n k : ℕ} (hk : k ≤ n) :
    (finPrefix n k).card = k := by
  let e : Fin k ↪ Fin n := Fin.castLEEmb hk
  have heq : finPrefix n k = Finset.univ.map e := by
    ext i
    simp only [mem_finPrefix, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact ⟨⟨i, hi⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [heq, Finset.card_map]
  simp

@[simp] lemma finPrefix_self (n : ℕ) : finPrefix n n = Finset.univ := by
  ext i
  simp

lemma finPrefix_succ {n k : ℕ} (hk : k + 1 ≤ n) :
    finPrefix n (k + 1) =
      insert (⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ : Fin n)
        (finPrefix n k) := by
  ext i
  simp only [mem_finPrefix, Finset.mem_insert]
  constructor
  · intro hi
    by_cases hik : i.val = k
    · exact Or.inl (Fin.ext hik)
    · exact Or.inr (by omega)
  · rintro (rfl | hi)
    · simp
    · omega

lemma edgeCount_finPrefix_succ_le {n k : ℕ} (G : SimpleGraph (Fin n))
    (hk : k + 1 ≤ n) :
    AKSGraph.edgeCount G (finPrefix n (k + 1)) ≤
      AKSGraph.edgeCount G (finPrefix n k) + k := by
  let v : Fin n := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
  have hv : v ∉ finPrefix n k := by simp [v]
  calc
    AKSGraph.edgeCount G (finPrefix n (k + 1)) =
        AKSGraph.edgeCount G (insert v (finPrefix n k)) := by
          rw [finPrefix_succ hk]
    _ = AKSGraph.edgeCount G (finPrefix n k) +
        AKSGraph.degreeInto G v (finPrefix n k) :=
      AKSGraph.edgeCount_insert G v (finPrefix n k) hv
    _ ≤ AKSGraph.edgeCount G (finPrefix n k) + k := by
      gcongr
      simpa [card_finPrefix (Nat.le_trans (Nat.le_add_right k 1) hk)] using
        AKSGraph.degreeInto_le_card G v (finPrefix n k)

/-- The lower half of KSSS Theorem 1.2 in the explicit finite Bernoulli
model used throughout this development. -/
def KSSSLocalPointLower : Prop :=
  ∀ (C A lambda : ℝ), 0 < C → 0 < A → 0 < lambda → lambda < 1 / 2 →
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n → RamseyFree C G →
        ∀ p : ℝ, lambda ≤ p → p ≤ 1 - lambda →
          ∀ x : ℕ,
            |(x : ℝ) - p ^ 2 * (G.edgeFinset.card : ℝ)| ≤
                A * (n : ℝ) ^ (3 / 2 : ℝ) →
              kappa * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
                Probability.eventProbability p
                  (fun S : Finset (Fin n) ↦ inducedEdges G S = x)

lemma exists_inducedEdges_eq_of_localPointLower
    (hlocal : KSSSLocalPointLower)
    {C A lambda : ℝ} (hC : 0 < C) (hA : 0 < A)
    (hlambda : 0 < lambda) (hlambdaHalf : lambda < 1 / 2) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      N ≤ n → 0 < n → RamseyFree C G →
      ∀ p : ℝ, lambda ≤ p → p ≤ 1 - lambda →
        ∀ x : ℕ,
          |(x : ℝ) - p ^ 2 * (G.edgeFinset.card : ℝ)| ≤
              A * (n : ℝ) ^ (3 / 2 : ℝ) →
            ∃ S : Finset (Fin n), inducedEdges G S = x := by
  obtain ⟨kappa, hkappa, N, hN⟩ :=
    hlocal C A lambda hC hA hlambda hlambdaHalf
  refine ⟨N, ?_⟩
  intro n G hn hnpos hG p hlp hpl x hx
  have hprob := hN n G hn hG p hlp hpl x hx
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hprobpos : 0 < Probability.eventProbability p
      (fun S : Finset (Fin n) ↦ inducedEdges G S = x) :=
    (mul_pos hkappa (Real.rpow_pos_of_pos hnreal _)).trans_le hprob
  by_contra hnone
  push Not at hnone
  simp [Probability.eventProbability, Probability.expectation, hnone] at hprobpos

/-- KSSS Theorem 1.2 (lower local estimate) together with the exact AKS
small-count theorem implies the full prescribed-count theorem. -/
theorem hasPrescribedCounts_of_localPointLower
    (hlocal : KSSSLocalPointLower) : HasPrescribedCounts := by
  intro C hC eta heta
  by_cases hetaOne : 1 ≤ eta
  · refine ⟨0, ?_⟩
    intro n G hn hG m hm
    have hm0 : m = 0 := by
      have hedge : 0 ≤ (G.edgeFinset.card : ℝ) := by positivity
      have hrhs : (1 - eta) * (G.edgeFinset.card : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hetaOne) hedge
      have hmle : (m : ℝ) ≤ 0 := hm.trans hrhs
      exact Nat.le_zero.mp (by exact_mod_cast hmle)
    exact ⟨∅, by simp [hm0]⟩
  have hetaLt : eta < 1 := lt_of_not_ge hetaOne
  obtain ⟨alpha, halpha, Naks, haks⟩ :=
    AKSGraph.aksPrescribedSmallCounts C hC
  let lambda : ℝ := eta / 4
  let p : ℝ := 1 - lambda
  have hlambda : 0 < lambda := div_pos heta (by norm_num)
  have hlambdaHalf : lambda < 1 / 2 := by
    dsimp only [lambda]
    linarith
  have hp : 0 < p := by
    dsimp only [p, lambda]
    linarith
  have hpOne : p ≤ 1 := by
    dsimp only [p]
    linarith
  have hlp : lambda ≤ p := by
    dsimp only [p, lambda]
    linarith
  have hpl : p ≤ 1 - lambda := le_rfl
  have hetaP : 1 - eta ≤ p ^ 2 := by
    dsimp only [p, lambda]
    nlinarith [sq_nonneg eta]
  let D : ℝ := C / (alpha / 2)
  have hD : 0 < D := div_pos hC (div_pos halpha (by norm_num))
  obtain ⟨Nlocal, hlocalExists⟩ :=
    exists_inducedEdges_eq_of_localPointLower hlocal hD zero_lt_one
      hlambda hlambdaHalf
  have htend : Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (alpha / 2))
      Filter.atTop Filter.atTop := by
    exact (tendsto_rpow_atTop (div_pos halpha (by norm_num))).comp
      tendsto_natCast_atTop_atTop
  have hevent := htend.eventually
    (Filter.eventually_ge_atTop (Nlocal : ℝ))
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Npow, hNpow⟩ := hevent
  refine ⟨max 1 (max Naks Npow), ?_⟩
  intro n G hn hG x hx
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnaks : Naks ≤ n := by omega
  have hnpow : Npow ≤ n := by omega
  by_cases hxsmall : (x : ℝ) ≤ (n : ℝ) ^ alpha
  · have hcounts := haks hnaks G hG x hxsmall
    obtain ⟨S, hS⟩ := hcounts x le_rfl
    refine ⟨S, ?_⟩
    rw [inducedEdges_eq_card_filter]
    exact hS
  · have hxlarge : (n : ℝ) ^ alpha < (x : ℝ) := lt_of_not_ge hxsmall
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hpSq : 0 < p ^ 2 := sq_pos_of_pos hp
    have hpSqOne : p ^ 2 ≤ 1 := by nlinarith [sq_nonneg p]
    have hxTotal : (x : ℝ) ≤ p ^ 2 * (G.edgeFinset.card : ℝ) := by
      calc
        (x : ℝ) ≤ (1 - eta) * (G.edgeFinset.card : ℝ) := hx
        _ ≤ p ^ 2 * (G.edgeFinset.card : ℝ) := by
          gcongr
    let P : ℕ → Prop := fun k ↦
      (x : ℝ) ≤ p ^ 2 *
        (AKSGraph.edgeCount G (finPrefix n k) : ℝ)
    have hPn : P n := by
      simpa [P, finPrefix_self, AKSGraph.edgeCount] using hxTotal
    let m : ℕ := Nat.find ⟨n, hPn⟩
    have hPm : P m := Nat.find_spec ⟨n, hPn⟩
    have hmn : m ≤ n := Nat.find_min' ⟨n, hPn⟩ hPn
    have hmpos : 0 < m := by
      by_contra hm0
      have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
      have hxle0 : (x : ℝ) ≤ 0 := by
        rw [hmzero] at hPm
        simpa [P, finPrefix, AKSGraph.edgeCount] using hPm
      have hxpos : 0 < (x : ℝ) :=
        (Real.rpow_pos_of_pos hnreal alpha).trans hxlarge
      linarith
    have hprevNot : ¬P (m - 1) := by
      apply Nat.find_min ⟨n, hPn⟩
      omega
    have hprev : p ^ 2 *
        (AKSGraph.edgeCount G (finPrefix n (m - 1)) : ℝ) < (x : ℝ) := by
      simpa [P, not_le] using hprevNot
    have hstepNat : AKSGraph.edgeCount G (finPrefix n m) ≤
        AKSGraph.edgeCount G (finPrefix n (m - 1)) + (m - 1) := by
      have hsucc : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
      simpa only [hsucc] using edgeCount_finPrefix_succ_le G
        (show m - 1 + 1 ≤ n by omega)
    have hEmLower : (n : ℝ) ^ alpha ≤
        (AKSGraph.edgeCount G (finPrefix n m) : ℝ) := by
      have hdiv : (x : ℝ) / p ^ 2 ≤
          (AKSGraph.edgeCount G (finPrefix n m) : ℝ) :=
        (div_le_iff₀ hpSq).2 (by simpa [P, mul_comm] using hPm)
      calc
        (n : ℝ) ^ alpha ≤ (x : ℝ) := hxlarge.le
        _ ≤ (x : ℝ) / p ^ 2 := by
          exact (le_div_iff₀ hpSq).2
            (by nlinarith [show 0 ≤ (x : ℝ) by positivity])
        _ ≤ _ := hdiv
    have hEmUpper :
        (AKSGraph.edgeCount G (finPrefix n m) : ℝ) ≤ (m : ℝ) ^ 2 := by
      have hchoose := AKSGraph.edgeCount_le_choose G (finPrefix n m)
      have hcard : (finPrefix n m).card = m := card_finPrefix hmn
      have hchooseSq : (finPrefix n m).card.choose 2 ≤ m ^ 2 := by
        rw [hcard]
        exact Nat.choose_le_pow m 2
      exact_mod_cast hchoose.trans hchooseSq
    have hpowCard : (n : ℝ) ^ (alpha / 2) ≤ (m : ℝ) := by
      have hsqrt := Real.sqrt_le_sqrt (hEmLower.trans hEmUpper)
      have hleft : Real.sqrt ((n : ℝ) ^ alpha) =
          (n : ℝ) ^ (alpha / 2) := by
        rw [Real.sqrt_eq_rpow]
        calc
          ((n : ℝ) ^ alpha) ^ (1 / 2 : ℝ) =
              (n : ℝ) ^ (alpha * (1 / 2 : ℝ)) := by
                symm
                exact Real.rpow_mul (le_of_lt hnreal) alpha (1 / 2 : ℝ)
          _ = (n : ℝ) ^ (alpha / 2) := by ring_nf
      rw [hleft, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at hsqrt
      exact hsqrt
    let Aset := finPrefix n m
    let H := (G.induce (Aset : Set (Fin n))).overFin
      (card_subtype_coe_finset Aset)
    have hcardA : Aset.card = m := by
      exact card_finPrefix hmn
    have hNlocal : Nlocal ≤ Aset.card := by
      rw [hcardA]
      exact_mod_cast (hNpow n hnpow).trans hpowCard
    have hRamsey : RamseyFree D H := by
      have hpowA : (n : ℝ) ^ (alpha / 2) ≤ (Aset.card : ℝ) := by
        rw [hcardA]
        exact hpowCard
      simpa only [D, hcardA] using
        AKSGraph.ramseyFree_induce_overFin_of_rpow G Aset hC
          (div_pos halpha (by norm_num)) hn1 hG hpowA
    have hEdgeH : H.edgeFinset.card = AKSGraph.edgeCount G Aset := by
      let GI := G.induce (Aset : Set (Fin n))
      calc
        H.edgeFinset.card = GI.edgeFinset.card := by
          exact (GI.overFinIso (card_subtype_coe_finset Aset)).card_edgeFinset_eq.symm
        _ = AKSGraph.edgeCount G Aset := by
          simpa only [GI, AKSGraph.edgeCount] using
            (G.card_filter_edgeFinset_toFinset_subset Aset).symm
    have hclose :
        |(x : ℝ) - p ^ 2 * (H.edgeFinset.card : ℝ)| ≤
          (Aset.card : ℝ) ^ (3 / 2 : ℝ) := by
      rw [hEdgeH, hcardA]
      have hstep :
          (AKSGraph.edgeCount G (finPrefix n m) : ℝ) ≤
            (AKSGraph.edgeCount G (finPrefix n (m - 1)) : ℝ) + (m - 1 : ℕ) := by
        exact_mod_cast hstepNat
      have hnonneg : 0 ≤ p ^ 2 *
          (AKSGraph.edgeCount G (finPrefix n m) : ℝ) - x := by
        simpa [P] using hPm
      rw [abs_of_nonpos (by linarith)]
      have hdiff : p ^ 2 *
          (AKSGraph.edgeCount G (finPrefix n m) : ℝ) - x ≤ (m : ℝ) := by
        have hmul : p ^ 2 *
            (AKSGraph.edgeCount G (finPrefix n m) : ℝ) ≤
            p ^ 2 * ((AKSGraph.edgeCount G (finPrefix n (m - 1)) : ℝ) +
              (m - 1 : ℕ)) := mul_le_mul_of_nonneg_left hstep (sq_nonneg p)
        have hcastPred : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
        nlinarith
      have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
      have hmRpow : (m : ℝ) ≤ (m : ℝ) ^ (3 / 2 : ℝ) :=
        Real.self_le_rpow_of_one_le hmone (by norm_num)
      change -(x - p ^ 2 *
        (AKSGraph.edgeCount G (finPrefix n m) : ℝ)) ≤
          (m : ℝ) ^ (3 / 2 : ℝ)
      rw [show -(x - p ^ 2 *
        (AKSGraph.edgeCount G (finPrefix n m) : ℝ)) =
          p ^ 2 * (AKSGraph.edgeCount G (finPrefix n m) : ℝ) - x by ring]
      exact hdiff.trans hmRpow
    obtain ⟨T, hT⟩ := hlocalExists Aset.card H hNlocal
      (by simpa [hcardA] using hmpos) hRamsey p hlp hpl x (by
        simpa [one_mul] using hclose)
    exact ⟨liftOverFinSubset G Aset T,
      (inducedEdges_liftOverFinSubset G Aset T).trans hT⟩

/-- Exact reduction of Erdős Problem 88 to the lower local point estimate.
All graph-theoretic density, AKS interpolation, and finite-order bookkeeping
have been discharged in the preceding theorems. -/
theorem erdos_88_of_localPointLower
    (hlocal : KSSSLocalPointLower) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          HomogeneousFree epsilon G →
            ∀ m : ℕ, (m : ℝ) ≤ delta * (n : ℝ) ^ 2 →
              ∃ S : Finset (Fin n), inducedEdges G S = m :=
  erdos_88_of_deep_inputs hasRamseyDensity
    (hasPrescribedCounts_of_localPointLower hlocal)

/-- The specialization of the local lower estimate actually needed for
Problem 88: unbiased sampling and no linear perturbation. -/
def KSSSUnbiasedEdgeLocalLower : Prop :=
  ∀ (C A : ℝ), 0 < C → 0 < A →
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n → RamseyFree C G →
        ∀ x : ℕ,
          |(x : ℝ) - (1 / 4 : ℝ) * (G.edgeFinset.card : ℝ)| ≤
              A * (n : ℝ) ^ (3 / 2 : ℝ) →
            kappa * (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
              Probability.eventProbability (1 / 2 : ℝ)
                (fun S : Finset (Fin n) ↦ inducedEdges G S = x)

lemma exists_inducedEdges_eq_of_unbiasedEdgeLocalLower
    (hlocal : KSSSUnbiasedEdgeLocalLower) {C A : ℝ}
    (hC : 0 < C) (hA : 0 < A) :
    ∃ N : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      N ≤ n → 0 < n → RamseyFree C G →
        ∀ x : ℕ,
          |(x : ℝ) - (1 / 4 : ℝ) * (G.edgeFinset.card : ℝ)| ≤
              A * (n : ℝ) ^ (3 / 2 : ℝ) →
            ∃ S : Finset (Fin n), inducedEdges G S = x := by
  obtain ⟨kappa, hkappa, N, hN⟩ := hlocal C A hC hA
  refine ⟨N, ?_⟩
  intro n G hn hnpos hG x hx
  have hprob := hN n G hn hG x hx
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hprobpos : 0 < Probability.eventProbability (1 / 2 : ℝ)
      (fun S : Finset (Fin n) ↦ inducedEdges G S = x) :=
    (mul_pos hkappa (Real.rpow_pos_of_pos hnreal _)).trans_le hprob
  by_contra hnone
  push Not at hnone
  simp [Probability.eventProbability, Probability.expectation, hnone] at hprobpos

/-- Uniform prescribed counts through one quarter of the edge set.  This
fixed positive fraction is enough for Erdős Problem 88. -/
def HasQuarterPrescribedCounts : Prop :=
  ∀ C : ℝ, 0 < C → ∃ N : ℕ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), N ≤ n → RamseyFree C G →
      ∀ m : ℕ, (m : ℝ) ≤ (1 / 4 : ℝ) * (G.edgeFinset.card : ℝ) →
        ∃ S : Finset (Fin n), inducedEdges G S = m

/-- The unbiased edge-count local estimate and AKS small-count theorem give
all prescribed counts through a fixed quarter of the edges. -/
theorem hasQuarterPrescribedCounts_of_unbiasedEdgeLocalLower
    (hlocal : KSSSUnbiasedEdgeLocalLower) : HasQuarterPrescribedCounts := by
  intro C hC
  obtain ⟨alpha, halpha, Naks, haks⟩ :=
    AKSGraph.aksPrescribedSmallCounts C hC
  let D : ℝ := C / (alpha / 2)
  have hD : 0 < D := div_pos hC (div_pos halpha (by norm_num))
  obtain ⟨Nlocal, hlocalExists⟩ :=
    exists_inducedEdges_eq_of_unbiasedEdgeLocalLower hlocal hD zero_lt_one
  have htend : Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (alpha / 2))
      Filter.atTop Filter.atTop := by
    exact (tendsto_rpow_atTop (div_pos halpha (by norm_num))).comp
      tendsto_natCast_atTop_atTop
  have hevent := htend.eventually
    (Filter.eventually_ge_atTop (Nlocal : ℝ))
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨Npow, hNpow⟩ := hevent
  refine ⟨max 1 (max Naks Npow), ?_⟩
  intro n G hn hG x hx
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnaks : Naks ≤ n := by omega
  have hnpow : Npow ≤ n := by omega
  by_cases hxsmall : (x : ℝ) ≤ (n : ℝ) ^ alpha
  · have hcounts := haks hnaks G hG x hxsmall
    obtain ⟨S, hS⟩ := hcounts x le_rfl
    refine ⟨S, ?_⟩
    rw [inducedEdges_eq_card_filter]
    exact hS
  · have hxlarge : (n : ℝ) ^ alpha < (x : ℝ) := lt_of_not_ge hxsmall
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn1
    let p : ℝ := 1 / 2
    have hp : 0 < p := by norm_num [p]
    have hpSq : 0 < p ^ 2 := sq_pos_of_pos hp
    have hpSqEq : p ^ 2 = (1 / 4 : ℝ) := by norm_num [p]
    let P : ℕ → Prop := fun k ↦
      (x : ℝ) ≤ p ^ 2 *
        (AKSGraph.edgeCount G (finPrefix n k) : ℝ)
    have hPn : P n := by
      change (x : ℝ) ≤ p ^ 2 *
        (AKSGraph.edgeCount G (finPrefix n n) : ℝ)
      rw [finPrefix_self, AKSGraph.edgeCount_univ, hpSqEq]
      exact hx
    let m : ℕ := Nat.find ⟨n, hPn⟩
    have hPm : P m := Nat.find_spec ⟨n, hPn⟩
    have hmn : m ≤ n := Nat.find_min' ⟨n, hPn⟩ hPn
    have hmpos : 0 < m := by
      by_contra hm0
      have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm0
      have hxle0 : (x : ℝ) ≤ 0 := by
        rw [hmzero] at hPm
        simpa [P, finPrefix, AKSGraph.edgeCount] using hPm
      have hxpos : 0 < (x : ℝ) :=
        (Real.rpow_pos_of_pos hnreal alpha).trans hxlarge
      linarith
    have hprevNot : ¬P (m - 1) := by
      apply Nat.find_min ⟨n, hPn⟩
      omega
    have hprev : p ^ 2 *
        (AKSGraph.edgeCount G (finPrefix n (m - 1)) : ℝ) < (x : ℝ) := by
      simpa [P, not_le] using hprevNot
    have hstepNat : AKSGraph.edgeCount G (finPrefix n m) ≤
        AKSGraph.edgeCount G (finPrefix n (m - 1)) + (m - 1) := by
      have hsucc : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
      simpa only [hsucc] using edgeCount_finPrefix_succ_le G
        (show m - 1 + 1 ≤ n by omega)
    have hEmLower : (n : ℝ) ^ alpha ≤
        (AKSGraph.edgeCount G (finPrefix n m) : ℝ) := by
      have hdiv : (x : ℝ) / p ^ 2 ≤
          (AKSGraph.edgeCount G (finPrefix n m) : ℝ) :=
        (div_le_iff₀ hpSq).2 (by simpa [P, mul_comm] using hPm)
      calc
        (n : ℝ) ^ alpha ≤ (x : ℝ) := hxlarge.le
        _ ≤ (x : ℝ) / p ^ 2 := by
          rw [hpSqEq]
          nlinarith [show 0 ≤ (x : ℝ) by positivity]
        _ ≤ _ := hdiv
    have hEmUpper :
        (AKSGraph.edgeCount G (finPrefix n m) : ℝ) ≤ (m : ℝ) ^ 2 := by
      have hchoose := AKSGraph.edgeCount_le_choose G (finPrefix n m)
      have hcard : (finPrefix n m).card = m := card_finPrefix hmn
      have hchooseSq : (finPrefix n m).card.choose 2 ≤ m ^ 2 := by
        rw [hcard]
        exact Nat.choose_le_pow m 2
      exact_mod_cast hchoose.trans hchooseSq
    have hpowCard : (n : ℝ) ^ (alpha / 2) ≤ (m : ℝ) := by
      have hsqrt := Real.sqrt_le_sqrt (hEmLower.trans hEmUpper)
      have hleft : Real.sqrt ((n : ℝ) ^ alpha) =
          (n : ℝ) ^ (alpha / 2) := by
        rw [Real.sqrt_eq_rpow]
        calc
          ((n : ℝ) ^ alpha) ^ (1 / 2 : ℝ) =
              (n : ℝ) ^ (alpha * (1 / 2 : ℝ)) := by
                symm
                exact Real.rpow_mul (le_of_lt hnreal) alpha (1 / 2 : ℝ)
          _ = (n : ℝ) ^ (alpha / 2) := by ring_nf
      rw [hleft, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at hsqrt
      exact hsqrt
    let Aset := finPrefix n m
    let H := (G.induce (Aset : Set (Fin n))).overFin
      (card_subtype_coe_finset Aset)
    have hcardA : Aset.card = m := card_finPrefix hmn
    have hNlocal : Nlocal ≤ Aset.card := by
      rw [hcardA]
      exact_mod_cast (hNpow n hnpow).trans hpowCard
    have hRamsey : RamseyFree D H := by
      have hpowA : (n : ℝ) ^ (alpha / 2) ≤ (Aset.card : ℝ) := by
        rw [hcardA]
        exact hpowCard
      simpa only [D, hcardA] using
        AKSGraph.ramseyFree_induce_overFin_of_rpow G Aset hC
          (div_pos halpha (by norm_num)) hn1 hG hpowA
    have hEdgeH : H.edgeFinset.card = AKSGraph.edgeCount G Aset := by
      let GI := G.induce (Aset : Set (Fin n))
      calc
        H.edgeFinset.card = GI.edgeFinset.card := by
          exact (GI.overFinIso (card_subtype_coe_finset Aset)).card_edgeFinset_eq.symm
        _ = AKSGraph.edgeCount G Aset := by
          simpa only [GI, AKSGraph.edgeCount] using
            (G.card_filter_edgeFinset_toFinset_subset Aset).symm
    have hclose :
        |(x : ℝ) - (1 / 4 : ℝ) * (H.edgeFinset.card : ℝ)| ≤
          (Aset.card : ℝ) ^ (3 / 2 : ℝ) := by
      rw [hEdgeH, hcardA, ← hpSqEq]
      have hstep :
          (AKSGraph.edgeCount G (finPrefix n m) : ℝ) ≤
            (AKSGraph.edgeCount G (finPrefix n (m - 1)) : ℝ) + (m - 1 : ℕ) := by
        exact_mod_cast hstepNat
      have hnonneg : 0 ≤ p ^ 2 *
          (AKSGraph.edgeCount G (finPrefix n m) : ℝ) - x := by
        simpa [P] using hPm
      rw [abs_of_nonpos (by linarith)]
      have hdiff : p ^ 2 *
          (AKSGraph.edgeCount G (finPrefix n m) : ℝ) - x ≤ (m : ℝ) := by
        have hmul : p ^ 2 *
            (AKSGraph.edgeCount G (finPrefix n m) : ℝ) ≤
            p ^ 2 * ((AKSGraph.edgeCount G (finPrefix n (m - 1)) : ℝ) +
              (m - 1 : ℕ)) := mul_le_mul_of_nonneg_left hstep (sq_nonneg p)
        have hcastPred : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast Nat.sub_le m 1
        rw [hpSqEq] at hmul hprev ⊢
        nlinarith
      have hmone : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
      have hmRpow : (m : ℝ) ≤ (m : ℝ) ^ (3 / 2 : ℝ) :=
        Real.self_le_rpow_of_one_le hmone (by norm_num)
      change -(x - p ^ 2 *
        (AKSGraph.edgeCount G (finPrefix n m) : ℝ)) ≤
          (m : ℝ) ^ (3 / 2 : ℝ)
      rw [show -(x - p ^ 2 *
        (AKSGraph.edgeCount G (finPrefix n m) : ℝ)) =
          p ^ 2 * (AKSGraph.edgeCount G (finPrefix n m) : ℝ) - x by ring]
      exact hdiff.trans hmRpow
    obtain ⟨T, hT⟩ := hlocalExists Aset.card H hNlocal
      (by simpa [hcardA] using hmpos) hRamsey x (by
        simpa [one_mul] using hclose)
    exact ⟨liftOverFinSubset G Aset T,
      (inducedEdges_liftOverFinSubset G Aset T).trans hT⟩

/-- Erdős Problem 88 follows already from the unbiased edge-count local
estimate; the full biased local theorem is not needed for this final target. -/
theorem erdos_88_of_unbiasedEdgeLocalLower
    (hlocal : KSSSUnbiasedEdgeLocalLower) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
          HomogeneousFree epsilon G →
            ∀ m : ℕ, (m : ℝ) ≤ delta * (n : ℝ) ^ 2 →
              ∃ S : Finset (Fin n), inducedEdges G S = m := by
  intro epsilon hepsilon
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let C : ℝ := epsilon * Real.log 2
  have hC : 0 < C := by
    dsimp only [C]
    exact mul_pos hepsilon hlogTwo
  obtain ⟨a, ha, Ndensity, hdensity⟩ := hasRamseyDensity C hC
  obtain ⟨Nlocal, hprescribed⟩ :=
    hasQuarterPrescribedCounts_of_unbiasedEdgeLocalLower hlocal C hC
  let N : ℕ := max Ndensity Nlocal + 1
  have hN : 0 < N := by dsimp only [N]; omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let delta : ℝ := min (a / 4) (1 / (2 * (N : ℝ) ^ 2))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (div_pos ha (by norm_num))
      (one_div_pos.mpr (mul_pos (by norm_num) (sq_pos_of_pos hNreal)))
  refine ⟨delta, hdelta, ?_⟩
  intro n G hG m hm
  have hRamsey : RamseyFree C G :=
    (homogeneousFree_iff_ramseyFree epsilon G).mp hG
  by_cases hn : N ≤ n
  · have hNdensity : Ndensity ≤ n := by dsimp only [N] at hn; omega
    have hNlocal : Nlocal ≤ n := by dsimp only [N] at hn; omega
    have hedge := hdensity n G hNdensity hRamsey
    have hdeltaA : delta ≤ a / 4 := by
      dsimp only [delta]
      exact min_le_left _ _
    have hmQuarter : (m : ℝ) ≤
        (1 / 4 : ℝ) * (G.edgeFinset.card : ℝ) := by
      calc
        (m : ℝ) ≤ delta * (n : ℝ) ^ 2 := hm
        _ ≤ (a / 4) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hdeltaA (sq_nonneg (n : ℝ))
        _ = (1 / 4 : ℝ) * (a * (n : ℝ) ^ 2) := by ring
        _ ≤ (1 / 4 : ℝ) * (G.edgeFinset.card : ℝ) := by
          exact mul_le_mul_of_nonneg_left hedge (by norm_num)
    exact hprescribed n G hNlocal hRamsey m hmQuarter
  · have hnlt : n < N := Nat.lt_of_not_ge hn
    have hdeltaN : delta ≤ 1 / (2 * (N : ℝ) ^ 2) := by
      dsimp only [delta]
      exact min_le_right _ _
    have hnsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
      have hnreal : (n : ℝ) < (N : ℝ) := by exact_mod_cast hnlt
      nlinarith [sq_nonneg ((N : ℝ) - n)]
    have hfactor : 0 ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
    have hhalf :
        (1 / (2 * (N : ℝ) ^ 2)) * (N : ℝ) ^ 2 = (1 / 2 : ℝ) := by
      field_simp [ne_of_gt hNreal]
    have hmOne : (m : ℝ) < 1 := by
      calc
        (m : ℝ) ≤ delta * (n : ℝ) ^ 2 := hm
        _ ≤ (1 / (2 * (N : ℝ) ^ 2)) * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hdeltaN (sq_nonneg (n : ℝ))
        _ ≤ (1 / (2 * (N : ℝ) ^ 2)) * (N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hnsq hfactor
        _ = (1 / 2 : ℝ) := hhalf
        _ < 1 := by norm_num
    have hmZero : m = 0 := by
      have : m < 1 := by exact_mod_cast hmOne
      omega
    exact ⟨∅, by simp [hmZero]⟩

end Erdos88
