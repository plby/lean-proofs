/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.BetaSieveFailureCombinatorics
import ErdosProblems.Erdos851.EulerLogBounds

/-!
# Product ratios imply beta-sieve depth bounds

This file supplies the missing finite bridge between an actual inverse
Euler-product estimate on a prefix of the ordered prime list and the mass of
the explicit first-failure terms at one depth.  In particular, the exported
theorems do not assume `HasDepthProductRatio`; they prove its pointwise
content from a product-ratio inequality.
-/

namespace Erdos851.BetaSieveFundamental

open scoped BigOperators
open Erdos851.FiniteCombinatorialSieve
open List

private theorem buchstabProduct_pos_of_lt_one {α : Type*}
    (x : α → ℝ) (l : List α) (hx1 : ∀ a ∈ l, x a < 1) :
    0 < buchstabProduct x l := by
  unfold buchstabProduct
  apply List.prod_pos
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  exact sub_pos.mpr (hx1 a ha)

private theorem buchstabProduct_nonneg_of_le_one {α : Type*}
    (x : α → ℝ) (l : List α) (hx1 : ∀ a ∈ l, x a ≤ 1) :
    0 ≤ buchstabProduct x l := by
  unfold buchstabProduct
  apply List.prod_nonneg
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  exact sub_nonneg.mpr (hx1 a ha)

private theorem buchstabProduct_le_one {α : Type*}
    (x : α → ℝ) (l : List α)
    (hx0 : ∀ a, 0 ≤ x a) (hx1 : ∀ a ∈ l, x a ≤ 1) :
    buchstabProduct x l ≤ 1 := by
  induction l with
  | nil => simp [buchstabProduct]
  | cons a l ih =>
      rw [buchstabProduct]
      simp only [List.map_cons, List.prod_cons]
      change (1 - x a) * buchstabProduct x l ≤ 1
      exact mul_le_one₀ (by linarith [hx0 a])
        (buchstabProduct_nonneg_of_le_one x l
          (fun b hb => hx1 b (by simp [hb])))
        (ih (fun b hb => hx1 b (by simp [hb])))

/-- If `Q` is a prefix of a noduplicate list `P`, and a selected chain ending
in `last` is contained in `Q`, then the residual tail of `P` after `Q` is a
suffix of the residual tail after `last`. -/
private theorem prefix_residual_isSuffix_of_chain {α : Type*}
    [DecidableEq α] {P Q before suffix chain : List α} {last : α}
    (hPnodup : P.Nodup) (hQ : Q <+: P)
    (hchain : chain <+ Q) (hchainLast : ∃ init, chain = init ++ [last])
    (hP : P = before ++ last :: suffix) :
    ∃ residual, P = Q ++ residual ∧ residual <:+ suffix := by
  obtain ⟨init, rfl⟩ := hchainLast
  have hlastQ : last ∈ Q := hchain.subset (by simp)
  have hbeforeNot : last ∉ before := by
    rw [hP] at hPnodup
    simp only [List.nodup_append, List.nodup_cons, List.mem_cons] at hPnodup
    intro hlast
    exact (hPnodup.2.2 last hlast last (by simp)) rfl
  have hidx : List.idxOf last P = before.length := by
    rw [hP, List.idxOf_append_of_notMem hbeforeNot]
    simp
  have hlen : before.length + 1 ≤ Q.length := by
    have hmemidx := (hQ.mem_iff_idxOf_lt_length last).mp hlastQ
    rw [hidx] at hmemidx
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hlen
  obtain ⟨residual, hQR⟩ := hQ
  refine ⟨residual, hQR.symm, ?_⟩
  use suffix.take k
  have hdrop : residual = suffix.drop k := by
    have hR : residual = P.drop Q.length := by
      rw [← hQR]
      simp
    rw [hR, hP, hk]
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]
    simp only [List.nil_append]
    have hsub : before.length + 1 + k - before.length = 1 + k := by omega
    rw [hsub, Nat.one_add]
    exact List.drop_succ_cons
  rw [hdrop]
  exact List.take_append_drop k suffix

/-- The terminal Buchstab factor is bounded by the full Euler product times
the inverse Euler product of any prefix containing the selected chain. -/
private theorem failureTerm_suffix_le_prefix_ratio {α : Type*}
    [DecidableEq α] (x : α → ℝ) {P Q : List α}
    (hx0 : ∀ a, 0 ≤ x a) (hx1 : ∀ a ∈ P, x a < 1)
    (hPnodup : P.Nodup) (hQ : Q <+: P)
    {t : List α × List α} (hstructure : FailureTermStructure P t)
    (hchain : t.1 <+ Q) :
    buchstabProduct x t.2 ≤
      buchstabProduct x P * (buchstabProduct x Q)⁻¹ := by
  obtain ⟨_hsub, init, last, before, hselected, hremaining⟩ := hstructure
  obtain ⟨residual, hPQR, hresidual⟩ :=
    prefix_residual_isSuffix_of_chain hPnodup hQ hchain
      ⟨init, hselected⟩ hremaining
  have hsuffix : buchstabProduct x t.2 ≤ buchstabProduct x residual := by
    obtain ⟨extra, hextra⟩ := hresidual
    have htSuffix : t.2 <:+ P := by
      use before ++ [last]
      simpa [List.append_assoc] using hremaining.symm
    have hextraP : ∀ a ∈ extra, a ∈ P := by
      intro a ha
      apply htSuffix.subset
      rw [← hextra]
      exact List.mem_append_left _ ha
    have hresidualP : ∀ a ∈ residual, a ∈ P := by
      intro a ha
      rw [hPQR]
      exact List.mem_append_right Q ha
    rw [← hextra]
    simp only [buchstabProduct, List.map_append, List.prod_append]
    simpa [buchstabProduct] using
      (mul_le_mul_of_nonneg_right
        (buchstabProduct_le_one x extra hx0
          (fun a ha => (hx1 a (hextraP a ha)).le))
        (buchstabProduct_pos_of_lt_one x residual
          (fun a ha => hx1 a (hresidualP a ha))).le)
  have hQpos : 0 < buchstabProduct x Q :=
    buchstabProduct_pos_of_lt_one x Q
      (fun a ha => hx1 a (hQ.subset ha))
  have hsplit : buchstabProduct x P =
      buchstabProduct x Q * buchstabProduct x residual := by
    rw [hPQR]
    simp [buchstabProduct]
  have hratio : buchstabProduct x P * (buchstabProduct x Q)⁻¹ =
      buchstabProduct x residual := by
    rw [hsplit]
    calc
      (buchstabProduct x Q * buchstabProduct x residual) *
            (buchstabProduct x Q)⁻¹ =
          buchstabProduct x Q * (buchstabProduct x Q)⁻¹ *
            buchstabProduct x residual := by ring
      _ = buchstabProduct x residual := by
        rw [mul_inv_cancel₀ hQpos.ne', one_mul]
  simpa [hratio] using hsuffix

private theorem sum_map_le_sum_map_of_nodup_subset {α : Type*}
    (f : α → ℝ) (l₁ l₂ : List α)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (hsub : ∀ a ∈ l₁, a ∈ l₂) (hf : ∀ a ∈ l₂, 0 ≤ f a) :
    (l₁.map f).sum ≤ (l₂.map f).sum := by
  classical
  rw [← List.sum_toFinset f h₁, ← List.sum_toFinset f h₂]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact List.mem_toFinset.mpr (hsub a (List.mem_toFinset.mp ha))
  · intro a ha _ha'
    exact hf a (List.mem_toFinset.mp ha)

/-- A noduplicate family of depth-`r` chains contained in a cutoff prefix
obeys the elementary-symmetric factorial estimate on that prefix. -/
private theorem failureChainMassAtDepth_le_prefix {α : Type*}
    (x : α → ℝ) (hx0 : ∀ a, 0 ≤ x a)
    (terms : List (List α × List α)) (Q : List α) (r : ℕ)
    (hchainsNodup : (failureChainsAtDepth terms r).Nodup)
    (hQnodup : Q.Nodup)
    (hchain : ∀ t ∈ terms, t.1.length = r → t.1 <+ Q) :
    failureChainMassAtDepth x terms r ≤
      (Q.map x).sum ^ r / (r.factorial : ℝ) := by
  calc
    failureChainMassAtDepth x terms r ≤ sublistsLenMass x Q r := by
      apply sum_map_le_sum_map_of_nodup_subset
      · exact hchainsNodup
      · exact List.nodup_sublistsLen r hQnodup
      · intro c hc
        simp only [failureChainsAtDepth, List.mem_filter, List.mem_map] at hc
        obtain ⟨⟨t, ht, rfl⟩, hlen⟩ := hc
        simp only [decide_eq_true_eq] at hlen
        exact List.mem_sublistsLen.mpr ⟨hchain t ht hlen, hlen⟩
      · intro c _hc
        exact List.prod_nonneg fun y hy => by
          obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hy
          exact hx0 a
    _ ≤ (Q.map x).sum ^ r / (r.factorial : ℝ) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < r.factorial)).2
      simpa [mul_comm] using factorial_mul_sublistsLenMass_le_sum_pow x hx0 Q r

/-- The generic one-depth product-ratio bridge.  `Q` is the common cutoff
prefix forced by stopping geometry at depth `r`; the only analytic premise
is the genuine inverse Euler-product estimate on `Q`. -/
theorem depthFailureMass_le_of_prefix_productRatio {α : Type*}
    [DecidableEq α] (x : α → ℝ) (terms : List (List α × List α))
    {P Q : List α} {A κ : ℝ} {r : ℕ}
    (hx0 : ∀ a, 0 ≤ x a) (hx1 : ∀ a ∈ P, x a < 1)
    (hPnodup : P.Nodup) (hQ : Q <+: P)
    (hchainsNodup : (failureChainsAtDepth terms r).Nodup)
    (hstructure : ∀ t ∈ terms, t.1.length = r → FailureTermStructure P t)
    (hchain : ∀ t ∈ terms, t.1.length = r → t.1 <+ Q)
    (hA : 1 ≤ A)
    (hproduct : (buchstabProduct x Q)⁻¹ ≤
      A * Real.rpow betaRatio (κ * r)) :
    depthFailureMass x terms r ≤
      buchstabProduct x P * betaDepthMajorant A κ r := by
  let I : ℝ := (buchstabProduct x Q)⁻¹
  let L : ℝ := (Q.map x).sum
  have hQpos : 0 < buchstabProduct x Q :=
    buchstabProduct_pos_of_lt_one x Q
      (fun a ha => hx1 a (hQ.subset ha))
  have hIpos : 0 < I := inv_pos.mpr hQpos
  have hL0 : 0 ≤ L :=
    List.sum_nonneg fun y hy => by
      obtain ⟨a, _ha, rfl⟩ := List.mem_map.mp hy
      exact hx0 a
  have hsum : L ≤ Real.log I := by
    simpa [I, L, finiteEulerProduct, buchstabProduct] using
      (Erdos851.list_sum_le_log_finiteEulerProduct_inv x Q
        (fun a ha => hx0 a) (fun a ha => hx1 a (hQ.subset ha)))
  have hfactorial : I * L ^ r / (r.factorial : ℝ) ≤
      betaDepthMajorant A κ r :=
    productRatio_factorialTerm_le_betaDepthMajorant r hA hIpos hL0
      (by simpa [I] using hproduct) hsum
  have hP0 : 0 ≤ buchstabProduct x P :=
    (buchstabProduct_pos_of_lt_one x P hx1).le
  have hdepth : depthFailureMass x terms r ≤
      (buchstabProduct x P * I) * failureChainMassAtDepth x terms r := by
    apply depthFailureMass_le_mul_failureChainMassAtDepth x hx0 terms r
    intro t ht hlen
    simpa [I] using failureTerm_suffix_le_prefix_ratio x hx0 hx1
      hPnodup hQ (hstructure t ht hlen) (hchain t ht hlen)
  have hchainMass : failureChainMassAtDepth x terms r ≤
      L ^ r / (r.factorial : ℝ) := by
    simpa [L] using failureChainMassAtDepth_le_prefix x hx0 terms Q r
      hchainsNodup (hQ.nodup hPnodup) hchain
  calc
    depthFailureMass x terms r ≤
        (buchstabProduct x P * I) * failureChainMassAtDepth x terms r := hdepth
    _ ≤ (buchstabProduct x P * I) *
          (L ^ r / (r.factorial : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hchainMass (mul_nonneg hP0 hIpos.le)
    _ = buchstabProduct x P * (I * L ^ r / (r.factorial : ℝ)) := by ring
    _ ≤ buchstabProduct x P * betaDepthMajorant A κ r :=
      mul_le_mul_of_nonneg_left hfactorial hP0

/-- Upper first-failure specialization of
`depthFailureMass_le_of_prefix_productRatio`. -/
theorem upper_depthFailureMass_le_of_prefix_productRatio {α : Type*}
    [DecidableEq α] (stop : List α → Bool) (x : α → ℝ)
    (fuel : ℕ) (selected : List α) {P Q : List α}
    {A κ : ℝ} {r : ℕ}
    (hx0 : ∀ a, 0 ≤ x a) (hx1 : ∀ a ∈ P, x a < 1)
    (hPnodup : P.Nodup) (hQ : Q <+: P)
    (hchain : ∀ t ∈ upperFailureTerms stop fuel selected P,
      t.1.length = r → t.1 <+ Q)
    (hA : 1 ≤ A)
    (hproduct : (buchstabProduct x Q)⁻¹ ≤
      A * Real.rpow betaRatio (κ * r)) :
    depthFailureMass x (upperFailureTerms stop fuel selected P) r ≤
      buchstabProduct x P * betaDepthMajorant A κ r := by
  apply depthFailureMass_le_of_prefix_productRatio x _ hx0 hx1 hPnodup hQ
    (upper_failureChainsAtDepth_nodup stop fuel selected P hPnodup r)
  · intro t ht _hlen
    exact (failureTerms_structure stop fuel selected P).1 t ht
  · exact hchain
  · exact hA
  · exact hproduct

/-- Lower first-failure specialization of
`depthFailureMass_le_of_prefix_productRatio`. -/
theorem lower_depthFailureMass_le_of_prefix_productRatio {α : Type*}
    [DecidableEq α] (stop : List α → Bool) (x : α → ℝ)
    (fuel : ℕ) (selected : List α) {P Q : List α}
    {A κ : ℝ} {r : ℕ}
    (hx0 : ∀ a, 0 ≤ x a) (hx1 : ∀ a ∈ P, x a < 1)
    (hPnodup : P.Nodup) (hQ : Q <+: P)
    (hchain : ∀ t ∈ lowerFailureTerms stop fuel selected P,
      t.1.length = r → t.1 <+ Q)
    (hA : 1 ≤ A)
    (hproduct : (buchstabProduct x Q)⁻¹ ≤
      A * Real.rpow betaRatio (κ * r)) :
    depthFailureMass x (lowerFailureTerms stop fuel selected P) r ≤
      buchstabProduct x P * betaDepthMajorant A κ r := by
  apply depthFailureMass_le_of_prefix_productRatio x _ hx0 hx1 hPnodup hQ
    (lower_failureChainsAtDepth_nodup stop fuel selected P hPnodup r)
  · intro t ht _hlen
    exact (failureTerms_structure stop fuel selected P).2 t ht
  · exact hchain
  · exact hA
  · exact hproduct

/-- No first-failure chain can contribute below a common lower bound for the
lengths of all chains in the term list. -/
theorem depthFailureMass_eq_zero_of_min_length {α : Type*}
    (x : α → ℝ) (terms : List (List α × List α)) {start r : ℕ}
    (hstart : ∀ t ∈ terms, start ≤ t.1.length) (hr : r < start) :
    depthFailureMass x terms r = 0 := by
  rw [depthFailureMass_eq_failureTermMassAtDepth]
  unfold failureTermMassAtDepth
  have hfilter : terms.filter (fun t => t.1.length = r) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro t ht
    simp only [Bool.not_eq_true, decide_eq_false_iff_not]
    intro hlen
    exact (Nat.not_le_of_gt hr) (by simpa [hlen] using hstart t ht)
  rw [hfilter]
  simp

/-- A family of genuine prefix product-ratio bounds constructs the full
upper `HasDepthProductRatio` conclusion.  This is an adapter for the existing
geometric summation theorem; callers supply cutoff prefixes and inverse Euler
products, not the desired depth estimate itself. -/
theorem upper_hasDepthProductRatio_of_prefixProductRatio {α : Type*}
    [DecidableEq α] (stop : List α → Bool) (x : α → ℝ)
    (fuel : ℕ) (selected : List α) {P : List α}
    (cutoff : ℕ → List α) {V A κ : ℝ} {start : ℕ}
    (hx0 : ∀ a, 0 ≤ x a) (hx1 : ∀ a ∈ P, x a < 1)
    (hPnodup : P.Nodup) (hV : V = buchstabProduct x P)
    (hprefix : ∀ r ≤ fuel, cutoff r <+: P)
    (hchain : ∀ r ≤ fuel,
      ∀ t ∈ upperFailureTerms stop fuel selected P,
        t.1.length = r → t.1 <+ cutoff r)
    (hstart : ∀ t ∈ upperFailureTerms stop fuel selected P,
      start ≤ t.1.length)
    (hA : 1 ≤ A)
    (hproduct : ∀ r ≤ fuel, start ≤ r →
      (buchstabProduct x (cutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r)) :
    HasDepthProductRatio x (upperFailureTerms stop fuel selected P)
      V A κ start fuel := by
  intro r hr
  split_ifs with hsr
  · rw [hV]
    exact upper_depthFailureMass_le_of_prefix_productRatio
      stop x fuel selected hx0 hx1 hPnodup (hprefix r hr)
      (hchain r hr) hA (hproduct r hr hsr)
  · have hrstart : r < start := Nat.lt_of_not_ge hsr
    rw [depthFailureMass_eq_zero_of_min_length x _ hstart hrstart]

/-- Lower analogue of
`upper_hasDepthProductRatio_of_prefixProductRatio`. -/
theorem lower_hasDepthProductRatio_of_prefixProductRatio {α : Type*}
    [DecidableEq α] (stop : List α → Bool) (x : α → ℝ)
    (fuel : ℕ) (selected : List α) {P : List α}
    (cutoff : ℕ → List α) {V A κ : ℝ} {start : ℕ}
    (hx0 : ∀ a, 0 ≤ x a) (hx1 : ∀ a ∈ P, x a < 1)
    (hPnodup : P.Nodup) (hV : V = buchstabProduct x P)
    (hprefix : ∀ r ≤ fuel, cutoff r <+: P)
    (hchain : ∀ r ≤ fuel,
      ∀ t ∈ lowerFailureTerms stop fuel selected P,
        t.1.length = r → t.1 <+ cutoff r)
    (hstart : ∀ t ∈ lowerFailureTerms stop fuel selected P,
      start ≤ t.1.length)
    (hA : 1 ≤ A)
    (hproduct : ∀ r ≤ fuel, start ≤ r →
      (buchstabProduct x (cutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r)) :
    HasDepthProductRatio x (lowerFailureTerms stop fuel selected P)
      V A κ start fuel := by
  intro r hr
  split_ifs with hsr
  · rw [hV]
    exact lower_depthFailureMass_le_of_prefix_productRatio
      stop x fuel selected hx0 hx1 hPnodup (hprefix r hr)
      (hchain r hr) hA (hproduct r hr hsr)
  · have hrstart : r < start := Nat.lt_of_not_ge hsr
    rw [depthFailureMass_eq_zero_of_min_length x _ hstart hrstart]

/-- Full quantitative recursive boundary estimate derived directly from
cutoff-prefix inverse Euler-product bounds.  Unlike the older endpoint, no
`HasDepthProductRatio` argument appears in this statement. -/
theorem rosserBoundaries_le_geometric_of_prefixProductRatio {α : Type*}
    [DecidableEq α] (stop : List α → Bool) (x : α → ℝ)
    (fuel : ℕ) (selected : List α) {P : List α}
    (upperCutoff lowerCutoff : ℕ → List α) {A κ : ℝ} {start : ℕ}
    (hx0 : ∀ a, 0 ≤ x a) (hx1 : ∀ a ∈ P, x a < 1)
    (hPnodup : P.Nodup)
    (hupperPrefix : ∀ r ≤ fuel, upperCutoff r <+: P)
    (hlowerPrefix : ∀ r ≤ fuel, lowerCutoff r <+: P)
    (hupperChain : ∀ r ≤ fuel,
      ∀ t ∈ upperFailureTerms stop fuel selected P,
        t.1.length = r → t.1 <+ upperCutoff r)
    (hlowerChain : ∀ r ≤ fuel,
      ∀ t ∈ lowerFailureTerms stop fuel selected P,
        t.1.length = r → t.1 <+ lowerCutoff r)
    (hupperStart : ∀ t ∈ upperFailureTerms stop fuel selected P,
      start ≤ t.1.length)
    (hlowerStart : ∀ t ∈ lowerFailureTerms stop fuel selected P,
      start ≤ t.1.length)
    (hA : 1 ≤ A) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (hupperProduct : ∀ r ≤ fuel, start ≤ r →
      (buchstabProduct x (upperCutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r))
    (hlowerProduct : ∀ r ≤ fuel, start ≤ r →
      (buchstabProduct x (lowerCutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r))
    (hlogA : ∀ r, start ≤ r → r ≤ fuel →
      Real.log A ≤ 2 * κ * r / 99) :
    rosserUpperBoundary stop x fuel selected P ≤
          buchstabProduct x P *
            ((4 * A / 3) * (1 / 4 : ℝ) ^ start) ∧
      rosserLowerBoundary stop x fuel selected P ≤
          buchstabProduct x P *
            ((4 * A / 3) * (1 / 4 : ℝ) ^ start) := by
  apply rosserBoundaries_le_geometric_of_depthProductRatio
    stop x selected P
    (buchstabProduct_pos_of_lt_one x P hx1).le
    hA hκ0 hκ2
  · exact upper_hasDepthProductRatio_of_prefixProductRatio
      stop x fuel selected upperCutoff hx0 hx1 hPnodup rfl
      hupperPrefix hupperChain hupperStart hA hupperProduct
  · exact lower_hasDepthProductRatio_of_prefixProductRatio
      stop x fuel selected lowerCutoff hx0 hx1 hPnodup rfl
      hlowerPrefix hlowerChain hlowerStart hA hlowerProduct
  · exact hlogA

/-- The prefix product-ratio hypotheses give the usual multiplicative lower
and upper estimates for the recursive Rosser main terms. -/
theorem rosserMainTerms_bounds_of_prefixProductRatio {α : Type*}
    [DecidableEq α] (stop : List α → Bool) (x : α → ℝ)
    (fuel : ℕ) (selected : List α) {P : List α}
    (upperCutoff lowerCutoff : ℕ → List α) {A κ : ℝ} {start : ℕ}
    (hx0 : ∀ a, 0 ≤ x a) (hx1 : ∀ a ∈ P, x a < 1)
    (hPnodup : P.Nodup) (hfuel : P.length ≤ fuel)
    (hupperPrefix : ∀ r ≤ fuel, upperCutoff r <+: P)
    (hlowerPrefix : ∀ r ≤ fuel, lowerCutoff r <+: P)
    (hupperChain : ∀ r ≤ fuel,
      ∀ t ∈ upperFailureTerms stop fuel selected P,
        t.1.length = r → t.1 <+ upperCutoff r)
    (hlowerChain : ∀ r ≤ fuel,
      ∀ t ∈ lowerFailureTerms stop fuel selected P,
        t.1.length = r → t.1 <+ lowerCutoff r)
    (hupperStart : ∀ t ∈ upperFailureTerms stop fuel selected P,
      start ≤ t.1.length)
    (hlowerStart : ∀ t ∈ lowerFailureTerms stop fuel selected P,
      start ≤ t.1.length)
    (hA : 1 ≤ A) (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (hupperProduct : ∀ r ≤ fuel, start ≤ r →
      (buchstabProduct x (upperCutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r))
    (hlowerProduct : ∀ r ≤ fuel, start ≤ r →
      (buchstabProduct x (lowerCutoff r))⁻¹ ≤
        A * Real.rpow betaRatio (κ * r))
    (hlogA : ∀ r, start ≤ r → r ≤ fuel →
      Real.log A ≤ 2 * κ * r / 99) :
    let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ start
    (1 - eta) * buchstabProduct x P ≤
        rosserLowerEval stop x fuel selected P ∧
      rosserUpperEval stop x fuel selected P ≤
        (1 + eta) * buchstabProduct x P := by
  dsimp only
  obtain ⟨hupper, hlower⟩ :=
    rosserBoundaries_le_geometric_of_prefixProductRatio
      stop x fuel selected upperCutoff lowerCutoff hx0 hx1 hPnodup
      hupperPrefix hlowerPrefix hupperChain hlowerChain
      hupperStart hlowerStart hA hκ0 hκ2 hupperProduct hlowerProduct hlogA
  obtain ⟨hupperEq, hlowerEq⟩ :=
    rosser_eval_sub_product_eq_boundary stop x fuel selected P hfuel
  constructor <;> linarith

end Erdos851.BetaSieveFundamental
