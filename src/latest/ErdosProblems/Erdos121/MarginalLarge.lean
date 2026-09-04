import ErdosProblems.Erdos121.MarginalSmall

/-!
# The large-prime part of a marginal

The dyadic bins attached to different edges are disjoint.  Consequently the
four primes incident to a fixed vertex are determined by their product.  The
other six prime choices retain their full reciprocal mass.
-/

open scoped BigOperators

namespace Erdos121

set_option autoImplicit false

noncomputable section

def k5IncidentLargeProduct {U : ℕ} {σ : K5ControlledAssignment U}
    {t : K5Parameter U} (v : Fin 5) (p : K5LargeChoice U σ t) : ℕ :=
  ∏ e, if k5Incident v e then (p e : ℕ) else 1

def k5NonincidentLargeWeight {U : ℕ} {σ : K5ControlledAssignment U}
    {t : K5Parameter U} (v : Fin 5) (p : K5LargeChoice U σ t) : ℝ :=
  ∏ e, if k5Incident v e then 1 else ((p e : ℕ) : ℝ)⁻¹

lemma k5IncidentLargeProduct_eq {U : ℕ} {σ : K5ControlledAssignment U}
    {t : K5Parameter U} (v : Fin 5) (p : K5LargeChoice U σ t) :
    k5IncidentLargeProduct v p = k5Tuple (fun e => (p e : ℕ)) v := by
  fin_cases v <;>
    simp [k5IncidentLargeProduct, k5Incident, k5EdgeEnds, k5Tuple,
      Fin.prod_univ_succ] <;> ring

lemma k5LargePrime_prime {U : ℕ} {σ : K5ControlledAssignment U}
    {t : K5Parameter U} {e : Fin 10} (p : K5LargePrime U σ t e) :
    Nat.Prime (p : ℕ) :=
  (Erdos888.mem_dyadicPrimes.mp p.property).1

lemma k5LargePrime_edge_eq {U : ℕ} (hU : 1000000000 ≤ U)
    {σ σ' : K5ControlledAssignment U} {t t' : K5Parameter U}
    {e f : Fin 10} (p : K5LargePrime U σ t e)
    (q : K5LargePrime U σ' t' f) (hpq : (p : ℕ) = (q : ℕ)) : e = f := by
  by_contra hef
  rcases k5Outcome_bins_cross_separated hU σ σ' t t' hef with h | h
  · have hpUpper := (Erdos888.mem_dyadicPrimes.mp p.property).2.2
    have hqLower := (Erdos888.mem_dyadicPrimes.mp q.property).2.1
    have hpow := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h
    omega
  · have hqUpper := (Erdos888.mem_dyadicPrimes.mp q.property).2.2
    have hpLower := (Erdos888.mem_dyadicPrimes.mp p.property).2.1
    have hpow := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h
    omega

/-- Prime factorization in the separated bins assigns every incident prime to
its unique edge. -/
lemma k5IncidentChoice_eq {U : ℕ} (hU : 1000000000 ≤ U)
    {σ : K5ControlledAssignment U} {t t' : K5Parameter U}
    (v : Fin 5) (p : K5LargeChoice U σ t) (p' : K5LargeChoice U σ t')
    (hprod : k5IncidentLargeProduct v p =
      k5IncidentLargeProduct v p') :
    ∀ e, k5Incident v e → (p e : ℕ) = (p' e : ℕ) := by
  intro e he
  have hprime := k5LargePrime_prime (p e)
  have hdvdLeft : (p e : ℕ) ∣ k5IncidentLargeProduct v p := by
    rw [k5IncidentLargeProduct]
    simpa [he] using
      (Finset.dvd_prod_of_mem (f := fun f : Fin 10 =>
        if k5Incident v f then (p f : ℕ) else 1) (Finset.mem_univ e))
  have hdvdRight : (p e : ℕ) ∣ k5IncidentLargeProduct v p' := by
    rwa [← hprod]
  rw [k5IncidentLargeProduct, hprime.prime.dvd_finsetProd_iff] at hdvdRight
  obtain ⟨f, _hf, hdiv⟩ := hdvdRight
  by_cases hfinc : k5Incident v f
  · simp [hfinc] at hdiv
    have hpfPrime := k5LargePrime_prime (p' f)
    have heq : (p e : ℕ) = (p' f : ℕ) := by
      rcases (Nat.dvd_prime hpfPrime).mp hdiv with hone | heq
      · exact (hprime.ne_one hone).elim
      · exact heq
    have hef : e = f := k5LargePrime_edge_eq hU (p e) (p' f) heq
    subst f
    exact heq
  · simp [hfinc] at hdiv
    exact (hprime.ne_one hdiv).elim

lemma k5IncidentBins_eq {U : ℕ} (hU : 1000000000 ≤ U)
    {σ : K5ControlledAssignment U} {t t' : K5Parameter U}
    (v : Fin 5) (p : K5LargeChoice U σ t) (p' : K5LargeChoice U σ t')
    (hprod : k5IncidentLargeProduct v p =
      k5IncidentLargeProduct v p') :
    ∀ e, k5Incident v e →
      k5OutcomeBins U σ t e = k5OutcomeBins U σ t' e := by
  intro e he
  have hpEq := k5IncidentChoice_eq hU v p p' hprod e he
  let q : ℕ := (p e : ℕ)
  have hp := (Erdos888.mem_dyadicPrimes.mp (p e).property).2
  have hp' := (Erdos888.mem_dyadicPrimes.mp (p' e).property).2
  by_contra hb
  rcases lt_or_gt_of_ne hb with hb | hb
  · have hsucc : k5OutcomeBins U σ t e + 1 ≤
        k5OutcomeBins U σ t' e := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hsucc
    omega
  · have hsucc : k5OutcomeBins U σ t' e + 1 ≤
        k5OutcomeBins U σ t e := by omega
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hsucc
    omega

lemma smallPrime_lt_k5LargePrime {U : ℕ} (hU : 1000000000 ≤ U)
    {σ : K5ControlledAssignment U} {t : K5Parameter U} {e : Fin 10}
    (q : SmallPrime (smallCutoff U)) (p : K5LargePrime U σ t e) :
    (q : ℕ) < (p : ℕ) := by
  have hq := (Erdos469.mem_primesThrough.mp q.property).2
  have hb := (k5Outcome_bin_bounds hU σ t e).1
  have hexp : U / 1000000 ≤ k5OutcomeBins U σ t e := by omega
  have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
  have hp := (Erdos888.mem_dyadicPrimes.mp p.property).2.1
  exact hq.trans_lt (by simpa [smallCutoff] using hpow.trans_lt hp)

lemma smallPrime_not_dvd_k5LargePrime {U : ℕ}
    (hU : 1000000000 ≤ U) {σ : K5ControlledAssignment U}
    {t : K5Parameter U} {e : Fin 10} (q : SmallPrime (smallCutoff U))
    (p : K5LargePrime U σ t e) : ¬ (q : ℕ) ∣ (p : ℕ) := by
  intro hdiv
  rcases (Nat.dvd_prime (k5LargePrime_prime p)).mp hdiv with hone | heq
  · exact (Erdos469.mem_primesThrough.mp q.property).1.ne_one hone
  · exact (Nat.ne_of_lt (smallPrime_lt_k5LargePrime hU q p)) heq

lemma smallPrime_not_dvd_k5LargeVertexProduct {U : ℕ}
    (hU : 1000000000 ≤ U) {σ : K5ControlledAssignment U}
    {t : K5Parameter U} (q : SmallPrime (smallCutoff U))
    (p : K5LargeChoice U σ t) (v : Fin 5) :
    ¬ (q : ℕ) ∣ k5Tuple (fun e => (p e : ℕ)) v := by
  have hprime := (Erdos469.mem_primesThrough.mp q.property).1
  have hall : ∀ e, ¬ (q : ℕ) ∣ (p e : ℕ) := fun e =>
    smallPrime_not_dvd_k5LargePrime hU q (p e)
  fin_cases v <;> simp [k5Tuple, hprime.dvd_mul, hall]

/-- Equality of one output forces exactly the local divisibility condition
used in the small Euler-product cancellation. -/
lemma smallIncidentCondition_of_output_eq {U n : ℕ}
    (hU : 1000000000 ≤ U) (ω : K5Outcome U) (v : Fin 5)
    (hout : k5OutcomeTuple ω v = n) :
    SmallIncidentCondition v n ω.1.1 := by
  intro q
  rw [← prime_dvd_smallVertexFactor_iff]
  have hprime := (Erdos469.mem_primesThrough.mp q.property).1
  constructor
  · intro hd
    rw [← hout, k5OutcomeTuple_factor]
    exact dvd_mul_of_dvd_left hd _
  · intro hn
    rw [← hout, k5OutcomeTuple_factor] at hn
    rcases hprime.dvd_mul.mp hn with hd | hlarge
    · exact hd
    · exact (smallPrime_not_dvd_k5LargeVertexProduct hU q ω.2.2 v hlarge).elim

abbrev K5OutputParameterFiber (U n : ℕ) (σ : K5ControlledAssignment U)
    (v : Fin 5) :=
  {t : K5Parameter U // ∃ p : K5LargeChoice U σ t,
    k5Tuple (smallEdgeFactor σ.1) v *
      k5Tuple (fun e => (p e : ℕ)) v = n}

/-- Once one output is fixed, the possible lattice parameters form a
rank-three fibre and hence have only two free box coordinates (and one parity
bit). -/
lemma card_k5OutputParameterFiber_le {U n : ℕ}
    (hU : 1000000000 ≤ U) (σ : K5ControlledAssignment U) (v : Fin 5)
    (t₀ : K5Parameter U) (p₀ : K5LargeChoice U σ t₀)
    (hout₀ : k5Tuple (smallEdgeFactor σ.1) v *
      k5Tuple (fun e => (p₀ e : ℕ)) v = n) :
    Fintype.card (K5OutputParameterFiber U n σ v) ≤
      2 * (U / 100000000 + 1) ^ 2 := by
  let f : K5OutputParameterFiber U n σ v →
      K5IncidentFiber U (k5OutcomeTarget U σ) v t₀ := fun t =>
    ⟨t.1, by
      obtain ⟨p, hp⟩ := t.2
      intro e he
      apply k5IncidentBins_eq hU v p p₀
      · rw [k5IncidentLargeProduct_eq, k5IncidentLargeProduct_eq]
        have hdpos : 0 < k5Tuple (smallEdgeFactor σ.1) v := by
          fin_cases v <;> simp [k5Tuple, smallEdgeFactor_pos]
        exact Nat.eq_of_mul_eq_mul_left hdpos (hp.trans hout₀.symm)
      · exact he⟩
  have hinj : Function.Injective f := by
    intro t t' heq
    apply Subtype.ext
    simpa [f] using congrArg
      (fun z : K5IncidentFiber U (k5OutcomeTarget U σ) v t₀ => z.1) heq
  have hcard := Fintype.card_le_of_injective f hinj
  exact hcard.trans (card_k5IncidentFiber_le hU
    (fun i => (k5Outcome_target_bounds hU σ i).1)
    (fun i => (k5Outcome_target_bounds hU σ i).2) v t₀)

abbrev K5IncidentPrimeChoice (U : ℕ) (σ : K5ControlledAssignment U)
    (t : K5Parameter U) (v : Fin 5) :=
  ∀ e : {e : Fin 10 // k5Incident v e}, K5LargePrime U σ t e.1

abbrev K5NonincidentPrimeChoice (U : ℕ) (σ : K5ControlledAssignment U)
    (t : K5Parameter U) (v : Fin 5) :=
  ∀ e : {e : Fin 10 // ¬ k5Incident v e}, K5LargePrime U σ t e.1

def k5IncidentChoiceProduct {U : ℕ} {σ : K5ControlledAssignment U}
    {t : K5Parameter U} {v : Fin 5}
    (a : K5IncidentPrimeChoice U σ t v) : ℕ := ∏ e, (a e : ℕ)

def k5IncidentChoiceWeight {U : ℕ} {σ : K5ControlledAssignment U}
    {t : K5Parameter U} {v : Fin 5}
    (a : K5IncidentPrimeChoice U σ t v) : ℝ :=
  ∏ e, ((a e : ℕ) : ℝ)⁻¹

def k5NonincidentChoiceWeight {U : ℕ} {σ : K5ControlledAssignment U}
    {t : K5Parameter U} {v : Fin 5}
    (b : K5NonincidentPrimeChoice U σ t v) : ℝ :=
  ∏ e, ((b e : ℕ) : ℝ)⁻¹

lemma k5NonincidentChoiceWeight_nonneg {U : ℕ}
    {σ : K5ControlledAssignment U} {t : K5Parameter U} {v : Fin 5}
    (b : K5NonincidentPrimeChoice U σ t v) :
    0 ≤ k5NonincidentChoiceWeight b := by
  apply Finset.prod_nonneg
  intro e he
  positivity

lemma k5IncidentChoiceProduct_injective {U : ℕ}
    (hU : 1000000000 ≤ U) {σ : K5ControlledAssignment U}
    {t : K5Parameter U} (v : Fin 5) :
    Function.Injective
      (k5IncidentChoiceProduct : K5IncidentPrimeChoice U σ t v → ℕ) := by
  intro a b hab
  funext e
  apply Subtype.ext
  have hprime := k5LargePrime_prime (a e)
  have hdvd : (a e : ℕ) ∣ k5IncidentChoiceProduct b := by
    rw [← hab, k5IncidentChoiceProduct]
    exact Finset.dvd_prod_of_mem (fun f => (a f : ℕ)) (Finset.mem_univ e)
  rw [k5IncidentChoiceProduct, hprime.prime.dvd_finsetProd_iff] at hdvd
  obtain ⟨f, _hf, hdiv⟩ := hdvd
  have hbfPrime := k5LargePrime_prime (b f)
  rcases (Nat.dvd_prime hbfPrime).mp hdiv with hone | heq
  · exact (hprime.ne_one hone).elim
  · have hef : e.1 = f.1 := k5LargePrime_edge_eq hU (a e) (b f) heq
    have hef' : e = f := Subtype.ext hef
    subst f
    exact heq

lemma k5IncidentChoiceWeight_eq_inv {U : ℕ}
    {σ : K5ControlledAssignment U} {t : K5Parameter U} {v : Fin 5}
    (a : K5IncidentPrimeChoice U σ t v) :
    k5IncidentChoiceWeight a = ((k5IncidentChoiceProduct a : ℕ) : ℝ)⁻¹ := by
  rw [k5IncidentChoiceWeight, k5IncidentChoiceProduct, Nat.cast_prod]
  exact Finset.prod_inv_distrib (fun e => ((a e : ℕ) : ℝ))

lemma card_k5Nonincident (v : Fin 5) :
    Fintype.card {e : Fin 10 // ¬ k5Incident v e} = 6 := by
  fin_cases v <;> decide

lemma k5IncidentProduct_of_split {U : ℕ} {σ : K5ControlledAssignment U}
    {t : K5Parameter U} (v : Fin 5) (p : K5LargeChoice U σ t) :
    k5IncidentChoiceProduct
        ((Equiv.piEquivPiSubtypeProd (k5Incident v)
          (fun e => K5LargePrime U σ t e)) p).1 =
      k5IncidentLargeProduct v p := by
  rw [k5IncidentChoiceProduct, k5IncidentLargeProduct]
  simpa only [Equiv.piEquivPiSubtypeProd_apply, Finset.subtype_univ,
      Finset.prod_ite, Finset.prod_const_one, mul_one,
      Finset.mem_univ, true_and] using
    (Finset.prod_subtype_eq_prod_filter
      (s := (Finset.univ : Finset (Fin 10)))
      (f := fun e => (p e : ℕ)) (p := k5Incident v))

lemma k5LargeChoiceWeight_split {U : ℕ} {σ : K5ControlledAssignment U}
    {t : K5Parameter U} (v : Fin 5) (p : K5LargeChoice U σ t) :
    (∏ e, ((p e : ℕ) : ℝ)⁻¹) =
      k5IncidentChoiceWeight
          ((Equiv.piEquivPiSubtypeProd (k5Incident v)
            (fun e => K5LargePrime U σ t e)) p).1 *
        k5NonincidentChoiceWeight
          ((Equiv.piEquivPiSubtypeProd (k5Incident v)
            (fun e => K5LargePrime U σ t e)) p).2 := by
  symm
  exact Fintype.prod_subtype_mul_prod_subtype (k5Incident v)
    (fun e => (((p e : ℕ) : ℝ)⁻¹))

lemma sum_k5NonincidentChoiceWeight (U : ℕ) (σ : K5ControlledAssignment U)
    (t : K5Parameter U) (v : Fin 5) :
    (∑ b : K5NonincidentPrimeChoice U σ t v,
      k5NonincidentChoiceWeight b) =
      ∏ e : {e : Fin 10 // ¬ k5Incident v e},
        dyadicPrimeMass (k5OutcomeBins U σ t e.1) := by
  simp only [k5NonincidentChoiceWeight]
  calc
    (∑ b : K5NonincidentPrimeChoice U σ t v,
      ∏ e, ((b e : ℕ) : ℝ)⁻¹) =
        ∏ e : {e : Fin 10 // ¬ k5Incident v e},
          ∑ p : K5LargePrime U σ t e.1, ((p : ℕ) : ℝ)⁻¹ := by
      symm
      let s : ∀ e : {e : Fin 10 // ¬ k5Incident v e},
          Finset (K5LargePrime U σ t e.1) := fun _ => Finset.univ
      have hs : Fintype.piFinset s =
          (Finset.univ : Finset (K5NonincidentPrimeChoice U σ t v)) := by
        ext b
        simp [s, Fintype.mem_piFinset]
      have h := Finset.prod_univ_sum s (fun e
        (p : K5LargePrime U σ t e.1) => ((p : ℕ) : ℝ)⁻¹)
      rw [hs] at h
      simpa [s] using h
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e he
      exact sum_inv_k5LargePrime U σ t e.1

lemma sum_k5NonincidentChoiceWeight_le {U : ℕ}
    (hU : 1000000000 ≤ U)
    (hprime : ∀ b : ℕ, U / 100 ≤ b → b ≤ U →
      dyadicPrimeMass b ≤
        (800 * Classical.choose
          Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U)
    (σ : K5ControlledAssignment U) (t : K5Parameter U) (v : Fin 5) :
    (∑ b : K5NonincidentPrimeChoice U σ t v,
      k5NonincidentChoiceWeight b) ≤
      ((800 * Classical.choose
        Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U) ^ 6 := by
  rw [sum_k5NonincidentChoiceWeight]
  let M : ℝ := (800 * Classical.choose
    Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U
  calc
    (∏ e : {e : Fin 10 // ¬ k5Incident v e},
        dyadicPrimeMass (k5OutcomeBins U σ t e.1)) ≤
        ∏ _e : {e : Fin 10 // ¬ k5Incident v e}, M := by
      apply Finset.prod_le_prod
      · intro e he
        exact dyadicPrimeMass_nonneg _
      · intro e he
        have hb := k5Outcome_bin_bounds hU σ t e.1
        exact hprime _ hb.1 (hb.2.trans (Nat.div_le_self U 2))
    _ = M ^ 6 := by
      rw [Finset.prod_const, Finset.card_univ, card_k5Nonincident]

lemma k5IncidentChoiceWeight_of_output {U n : ℕ}
    {σ : K5ControlledAssignment U} {t : K5Parameter U} {v : Fin 5}
    (a : K5IncidentPrimeChoice U σ t v)
    (hout : k5Tuple (smallEdgeFactor σ.1) v *
      k5IncidentChoiceProduct a = n) :
    k5IncidentChoiceWeight a =
      (k5Tuple (smallEdgeFactor σ.1) v : ℝ) / n := by
  have hdpos : 0 < k5Tuple (smallEdgeFactor σ.1) v := by
    fin_cases v <;> simp [k5Tuple, smallEdgeFactor_pos]
  have hppos : 0 < k5IncidentChoiceProduct a := by
    apply Finset.prod_pos
    intro e he
    exact (k5LargePrime_prime (a e)).pos
  have hnpos : 0 < n := by
    rw [← hout]
    exact Nat.mul_pos hdpos hppos
  rw [k5IncidentChoiceWeight_eq_inv]
  have houtR : (k5Tuple (smallEdgeFactor σ.1) v : ℝ) *
      (k5IncidentChoiceProduct a : ℝ) = n := by exact_mod_cast hout
  apply (eq_div_iff (by positivity : (n : ℝ) ≠ 0)).2
  rw [← houtR]
  field_simp

/-- For one lattice point, fixing one output spends the four incident prime
choices; only the six nonincident reciprocal-prime masses remain. -/
lemma sum_k5LargeChoice_output_eq_le {U n : ℕ}
    (hU : 1000000000 ≤ U)
    (hprime : ∀ b : ℕ, U / 100 ≤ b → b ≤ U →
      dyadicPrimeMass b ≤
        (800 * Classical.choose
          Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U)
    (σ : K5ControlledAssignment U) (t : K5Parameter U) (v : Fin 5) :
    (∑ p : K5LargeChoice U σ t,
      if k5Tuple (smallEdgeFactor σ.1) v *
          k5Tuple (fun e => (p e : ℕ)) v = n then
        ∏ e, ((p e : ℕ) : ℝ)⁻¹ else 0) ≤
      (k5Tuple (smallEdgeFactor σ.1) v : ℝ) / n *
        ((800 * Classical.choose
          Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U) ^ 6 := by
  let E := Equiv.piEquivPiSubtypeProd (k5Incident v)
    (fun e => K5LargePrime U σ t e)
  let d := k5Tuple (smallEdgeFactor σ.1) v
  let M : ℝ := (800 * Classical.choose
    Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U
  let I : Type := K5IncidentPrimeChoice U σ t v
  let J : Type := K5NonincidentPrimeChoice U σ t v
  have hrewrite :
      (∑ p : K5LargeChoice U σ t,
        if d * k5Tuple (fun e => (p e : ℕ)) v = n then
          ∏ e, ((p e : ℕ) : ℝ)⁻¹ else 0) =
        ∑ z : I × J,
          if d * k5IncidentChoiceProduct z.1 = n then
            k5IncidentChoiceWeight z.1 *
              k5NonincidentChoiceWeight z.2 else 0 := by
    apply Fintype.sum_equiv E
    intro p
    have hprod : k5IncidentChoiceProduct (E p).1 =
        k5Tuple (fun e => (p e : ℕ)) v := by
      exact (k5IncidentProduct_of_split v p).trans
        (k5IncidentLargeProduct_eq v p)
    rw [← hprod, k5LargeChoiceWeight_split v p]
  rw [show k5Tuple (smallEdgeFactor σ.1) v = d from rfl]
  rw [hrewrite]
  have hfactor :
      (∑ z : I × J,
        if d * k5IncidentChoiceProduct z.1 = n then
          k5IncidentChoiceWeight z.1 *
            k5NonincidentChoiceWeight z.2 else 0) =
      (∑ a : I, if d * k5IncidentChoiceProduct a = n then
          k5IncidentChoiceWeight a else 0) *
        ∑ b : J, k5NonincidentChoiceWeight b := by
    rw [Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases h : d * k5IncidentChoiceProduct a = n
    · simp [h, Finset.mul_sum]
    · simp [h]
  rw [hfactor]
  have hdpos : 0 < d := by
    dsimp [d]
    fin_cases v <;> simp [k5Tuple, smallEdgeFactor_pos]
  have hinj : Function.Injective
      (fun a : I => d * k5IncidentChoiceProduct a) := by
    intro a b hab
    apply k5IncidentChoiceProduct_injective hU v
    exact Nat.eq_of_mul_eq_mul_left hdpos hab
  have hincident :
      (∑ a : I, if d * k5IncidentChoiceProduct a = n then
          k5IncidentChoiceWeight a else 0) ≤ (d : ℝ) / n := by
    by_cases hex : ∃ a : I, d * k5IncidentChoiceProduct a = n
    · obtain ⟨a₀, ha₀⟩ := hex
      have hiff : ∀ a : I,
          d * k5IncidentChoiceProduct a = n ↔ a = a₀ := by
        intro a
        constructor
        · intro ha
          exact hinj (ha.trans ha₀.symm)
        · rintro rfl
          exact ha₀
      simp_rw [hiff]
      simpa [k5IncidentChoiceWeight_of_output a₀ ha₀, d]
    · have hnone : ∀ a : I, d * k5IncidentChoiceProduct a ≠ n := by
        simpa only [not_exists] using hex
      simp only [ge_iff_le]
      positivity
  have hnon := sum_k5NonincidentChoiceWeight_le hU hprime σ t v
  exact mul_le_mul hincident hnon
    (Finset.sum_nonneg fun b hb => k5NonincidentChoiceWeight_nonneg b)
    (div_nonneg (by positivity) (by positivity))

/-- Summing over the lattice parameters costs only the rank-three fibre
cardinality, rather than all five free parameters. -/
lemma sum_k5ParameterLargeChoice_output_eq_le {U n : ℕ}
    (hU : 1000000000 ≤ U)
    (hprime : ∀ b : ℕ, U / 100 ≤ b → b ≤ U →
      dyadicPrimeMass b ≤
        (800 * Classical.choose
          Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U)
    (σ : K5ControlledAssignment U) (v : Fin 5) :
    (∑ t : K5Parameter U, ∑ p : K5LargeChoice U σ t,
      if k5Tuple (smallEdgeFactor σ.1) v *
          k5Tuple (fun e => (p e : ℕ)) v = n then
        ∏ e, ((p e : ℕ) : ℝ)⁻¹ else 0) ≤
      (2 * (U / 100000000 + 1) ^ 2 : ℕ) *
        ((k5Tuple (smallEdgeFactor σ.1) v : ℝ) / n *
          ((800 * Classical.choose
            Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U) ^ 6) := by
  let P : K5Parameter U → Prop := fun t =>
    ∃ p : K5LargeChoice U σ t,
      k5Tuple (smallEdgeFactor σ.1) v *
        k5Tuple (fun e => (p e : ℕ)) v = n
  let B : ℝ := (k5Tuple (smallEdgeFactor σ.1) v : ℝ) / n *
    ((800 * Classical.choose
      Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U) ^ 6
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  by_cases hex : ∃ t, P t
  · obtain ⟨t₀, p₀, hp₀⟩ := hex
    have hpoint : ∀ t : K5Parameter U,
        (∑ p : K5LargeChoice U σ t,
          if k5Tuple (smallEdgeFactor σ.1) v *
              k5Tuple (fun e => (p e : ℕ)) v = n then
            ∏ e, ((p e : ℕ) : ℝ)⁻¹ else 0) ≤
          if P t then B else 0 := by
      intro t
      by_cases ht : P t
      · rw [if_pos ht]
        exact sum_k5LargeChoice_output_eq_le hU hprime σ t v
      · rw [if_neg ht]
        have hnone : ∀ p : K5LargeChoice U σ t,
            k5Tuple (smallEdgeFactor σ.1) v *
              k5Tuple (fun e => (p e : ℕ)) v ≠ n := by
          simpa only [P, not_exists] using ht
        simp [hnone]
    calc
      (∑ t : K5Parameter U, ∑ p : K5LargeChoice U σ t,
          if k5Tuple (smallEdgeFactor σ.1) v *
              k5Tuple (fun e => (p e : ℕ)) v = n then
            ∏ e, ((p e : ℕ) : ℝ)⁻¹ else 0) ≤
          ∑ t : K5Parameter U, if P t then B else 0 := by
        exact Finset.sum_le_sum fun t ht => hpoint t
      _ = (Fintype.card (K5OutputParameterFiber U n σ v) : ℝ) * B := by
        rw [← Finset.sum_filter]
        simp [P, K5OutputParameterFiber, nsmul_eq_mul,
          Fintype.card_subtype]
      _ ≤ (2 * (U / 100000000 + 1) ^ 2 : ℕ) * B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact_mod_cast card_k5OutputParameterFiber_le hU σ v t₀ p₀ hp₀
  · have hnone : ∀ t : K5Parameter U, ∀ p : K5LargeChoice U σ t,
        k5Tuple (smallEdgeFactor σ.1) v *
          k5Tuple (fun e => (p e : ℕ)) v ≠ n := by
      simpa only [P, not_exists] using hex
    simp only [hnone, if_false, Finset.sum_const_zero]
    exact mul_nonneg (by positivity) hB

lemma k5MarginalFormula (U n : ℕ) (v : Fin 5) :
    (k5Weight U).mass (fun ω => k5OutcomeTuple ω v = n) =
      ∑ σ : K5ControlledAssignment U,
        smallAssignmentWeight σ.1 *
          ∑ t : K5Parameter U, ∑ p : K5LargeChoice U σ t,
            if k5Tuple (smallEdgeFactor σ.1) v *
                k5Tuple (fun e => (p e : ℕ)) v = n then
              ∏ e, ((p e : ℕ) : ℝ)⁻¹ else 0 := by
  classical
  rw [FiniteWeight.mass]
  simp only [k5Weight]
  rw [Finset.sum_filter]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [k5OutcomeTuple_factor]
  simp only [k5OutcomeWeight, k5LargeVertexProduct]
  by_cases h : k5Tuple (smallEdgeFactor σ.1) v *
      k5Tuple (fun e => (p e : ℕ)) v = n <;> simp [h]

/-- Complete one-coordinate marginal estimate before the elementary
asymptotic simplification. -/
theorem k5Marginal_le {U n : ℕ} (hn : 0 < n)
    (hU : 1000000000 ≤ U)
    (hprime : ∀ b : ℕ, U / 100 ≤ b → b ≤ U →
      dyadicPrimeMass b ≤
        (800 * Classical.choose
          Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U)
    (v : Fin 5) :
    (k5Weight U).mass (fun ω => k5OutcomeTuple ω v = n) ≤
      ((2 * (U / 100000000 + 1) ^ 2 : ℕ) : ℝ) *
        ((800 * Classical.choose
          Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U) ^ 6 /
        n * smallEuler 6 (smallCutoff U) := by
  rw [k5MarginalFormula]
  let C : ℝ := ((2 * (U / 100000000 + 1) ^ 2 : ℕ) : ℝ) *
    ((800 * Classical.choose
      Erdos888.exists_forall_dyadicPrimeCount_le_scale) / U) ^ 6 / n
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    (∑ σ : K5ControlledAssignment U,
        smallAssignmentWeight σ.1 *
          ∑ t : K5Parameter U, ∑ p : K5LargeChoice U σ t,
            if k5Tuple (smallEdgeFactor σ.1) v *
                k5Tuple (fun e => (p e : ℕ)) v = n then
              ∏ e, ((p e : ℕ) : ℝ)⁻¹ else 0) ≤
        ∑ σ : K5ControlledAssignment U,
          if SmallIncidentCondition v n σ.1 then
            C * (smallAssignmentWeight σ.1 *
              (k5Tuple (smallEdgeFactor σ.1) v : ℝ)) else 0 := by
      apply Finset.sum_le_sum
      intro σ hσ
      by_cases hcond : SmallIncidentCondition v n σ.1
      · rw [if_pos hcond]
        have hbound := sum_k5ParameterLargeChoice_output_eq_le
          (n := n) hU hprime σ v
        apply (mul_le_mul_of_nonneg_left hbound
          (smallAssignmentWeight_nonneg σ.1)).trans_eq
        dsimp [C]
        field_simp
      · rw [if_neg hcond]
        have hnone : ∀ t : K5Parameter U,
            ∀ p : K5LargeChoice U σ t,
            k5Tuple (smallEdgeFactor σ.1) v *
              k5Tuple (fun e => (p e : ℕ)) v ≠ n := by
          intro t p hout
          apply hcond
          let ω : K5Outcome U := ⟨σ, t, p⟩
          apply smallIncidentCondition_of_output_eq hU ω v
          rw [k5OutcomeTuple_factor]
          change k5Tuple (smallEdgeFactor σ.1) v *
            k5Tuple (fun e => (p e : ℕ)) v = n
          exact hout
        simp [hnone, smallAssignmentWeight_nonneg]
    _ = C * ∑ σ : K5ControlledAssignment U,
          if SmallIncidentCondition v n σ.1 then
            smallAssignmentWeight σ.1 *
              (k5Tuple (smallEdgeFactor σ.1) v : ℝ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      by_cases hcond : SmallIncidentCondition v n σ.1 <;> simp [hcond]
    _ ≤ C * smallEuler 6 (smallCutoff U) := by
      apply mul_le_mul_of_nonneg_left _ hC
      have hsmall := sum_small_marginal_le (smallCutoff U) n v
      let f : SmallAssignment (smallCutoff U) → ℝ := fun σ =>
        if SmallIncidentCondition v n σ then
          smallAssignmentWeight σ *
            (k5Tuple (smallEdgeFactor σ) v : ℝ) else 0
      calc
        (∑ σ : K5ControlledAssignment U,
            if SmallIncidentCondition v n σ.1 then
              smallAssignmentWeight σ.1 *
                (k5Tuple (smallEdgeFactor σ.1) v : ℝ) else 0) =
            ∑ σ : SmallAssignment (smallCutoff U) with
              smallAssignedLog σ ≤ smallLogBudget U, f σ := by
          simpa [f, K5ControlledAssignment] using
            (Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset
                (SmallAssignment (smallCutoff U))))
              f (p := fun σ =>
                smallAssignedLog σ ≤ smallLogBudget U))
        _ ≤ ∑ σ : SmallAssignment (smallCutoff U), f σ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
          intro σ hσ hnot
          dsimp [f]
          split
          · exact mul_nonneg (smallAssignmentWeight_nonneg σ) (by positivity)
          · norm_num
        _ ≤ smallEuler 6 (smallCutoff U) := by
          simpa [f] using hsmall
    _ = _ := rfl

end

end Erdos121
