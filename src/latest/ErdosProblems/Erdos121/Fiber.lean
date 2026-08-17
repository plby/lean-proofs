import ErdosProblems.Erdos121.SmallSize

/-!
# Fibres of the `K₅` bin lattice

Fixing the four bins incident to one vertex leaves at most two free
parameters.  This is the rank-three statement for the four incident columns,
spelled out for the explicit lattice used in this development.
-/

namespace Erdos121

set_option autoImplicit false

def k5EdgeEnds : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2),
    (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

def k5Incident (v : Fin 5) (e : Fin 10) : Prop :=
  v = (k5EdgeEnds e).1 ∨ v = (k5EdgeEnds e).2

instance (v : Fin 5) (e : Fin 10) : Decidable (k5Incident v e) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Two coordinates which encode a fibre after the four bins at `v` have
been fixed. -/
def k5FiberCode (v : Fin 5) (t : Fin 5 → ℕ) : Fin 2 → ℕ :=
  ![![t 0, t 1], ![t 2, t 3], ![t 0, t 1], ![t 1, t 3], ![t 0, t 2]] v

/-- The only rounding ambiguity in the solved coordinates is removed by one
parity bit. -/
def k5FiberParity (v : Fin 5) (t : Fin 5 → ℕ) : Fin 2 :=
  if v.val ≤ 2 then ⟨t 4 % 2, Nat.mod_lt _ (by norm_num)⟩ else 0

lemma k5SolvedBinsInt_cross_separated {U : ℕ} (hU : 1000000000 ≤ U)
    {s s' : Fin 5 → ℕ}
    (hsLower : ∀ i, 998 * U / 1000 ≤ s i)
    (hsUpper : ∀ i, s i ≤ U)
    (hsLower' : ∀ i, 998 * U / 1000 ≤ s' i)
    (hsUpper' : ∀ i, s' i ≤ U)
    {t t' : Fin 5 → ℕ} (ht : t ∈ k5ParameterBox U)
    (ht' : t' ∈ k5ParameterBox U) {e f : Fin 10} (hef : e ≠ f) :
    k5SolvedBins U s t e + 1 < k5SolvedBins U s' t' f ∨
      k5SolvedBins U s' t' f + 1 < k5SolvedBins U s t e := by
  have he := k5SolvedBinsInt_close_base hU hsLower hsUpper ht e
  have hf := k5SolvedBinsInt_close_base hU hsLower' hsUpper' ht' f
  have hne := k5SolvedBinsInt_nonneg hU hsLower hsUpper ht e
  have hnf := k5SolvedBinsInt_nonneg hU hsLower' hsUpper' ht' f
  have heq : (k5SolvedBins U s t e : ℤ) =
      k5SolvedBinsInt s (k5FreeBins U t) e := by
    simp [k5SolvedBins, Int.toNat_of_nonneg hne]
  have hfq : (k5SolvedBins U s' t' f : ℤ) =
      k5SolvedBinsInt s' (k5FreeBins U t') f := by
    simp [k5SolvedBins, Int.toNat_of_nonneg hnf]
  rw [← heq] at he
  rw [← hfq] at hf
  have hgap : 2 * (U / 200) + 1 < 20 * (U / 1000) := by omega
  have hcoefE : 20 ≤ k5BaseCoefficient e :=
    (by norm_num : 20 ≤ 40).trans (k5BaseCoefficient_ge e)
  have hcoefF : 20 ≤ k5BaseCoefficient f :=
    (by norm_num : 20 ≤ 40).trans (k5BaseCoefficient_ge f)
  have hcoefMulE := Nat.mul_le_mul_right (U / 1000) hcoefE
  have hcoefMulF := Nat.mul_le_mul_right (U / 1000) hcoefF
  rcases k5BaseCoefficient_separated hef with hsep | hsep
  · left
    have hmul := Nat.mul_le_mul_right (U / 1000) hsep
    rw [Nat.add_mul] at hmul
    omega
  · right
    have hmul := Nat.mul_le_mul_right (U / 1000) hsep
    rw [Nat.add_mul] at hmul
    omega

/-- On a fixed row-target lattice, the incident bins and the two-coordinate
code determine all five free parameters. -/
lemma k5Parameter_eq_of_incident_bins_eq {U : ℕ} (hU : 1000000000 ≤ U)
    {s : Fin 5 → ℕ} (hsLower : ∀ i, 998 * U / 1000 ≤ s i)
    (hsUpper : ∀ i, s i ≤ U) {t t' : Fin 5 → ℕ}
    (ht : t ∈ k5ParameterBox U) (ht' : t' ∈ k5ParameterBox U)
    (v : Fin 5)
    (hinc : ∀ e, k5Incident v e →
      k5SolvedBins U s t e = k5SolvedBins U s t' e)
    (hcode : k5FiberCode v t = k5FiberCode v t')
    (hparity : k5FiberParity v t = k5FiberParity v t') : t = t' := by
  have hn : ∀ e : Fin 10,
      0 ≤ k5SolvedBinsInt s (k5FreeBins U t) e :=
    k5SolvedBinsInt_nonneg hU hsLower hsUpper ht
  have hn' : ∀ e : Fin 10,
      0 ≤ k5SolvedBinsInt s (k5FreeBins U t') e :=
    k5SolvedBinsInt_nonneg hU hsLower hsUpper ht'
  have hbin : ∀ e, k5Incident v e →
      k5SolvedBinsInt s (k5FreeBins U t) e =
        k5SolvedBinsInt s (k5FreeBins U t') e := by
    intro e he
    have h := hinc e he
    simpa [k5SolvedBins, Int.toNat_of_nonneg (hn e),
      Int.toNat_of_nonneg (hn' e)] using congrArg Int.ofNat h
  fin_cases v
  · have h0 := hbin 0 (by simp [k5Incident, k5EdgeEnds])
    have h2 := hbin 2 (by simp [k5Incident, k5EdgeEnds])
    have h3 := hbin 3 (by simp [k5Incident, k5EdgeEnds])
    have hc0 := congrFun hcode 0
    have hc1 := congrFun hcode 1
    have hp := congrArg Fin.val hparity
    simp [k5SolvedBinsInt, k5FreeBins, k5FiberCode, k5FiberParity] at h0 h2 h3 hc0 hc1 hp
    have ht0 : t 0 = t' 0 := hc0
    have ht1 : t 1 = t' 1 := hc1
    have ht2 : t 2 = t' 2 := by omega
    have ht3 : t 3 = t' 3 := by omega
    have ht4 : t 4 = t' 4 := by omega
    funext i
    fin_cases i <;> assumption
  · have h4 := hbin 4 (by simp [k5Incident, k5EdgeEnds])
    have h5 := hbin 5 (by simp [k5Incident, k5EdgeEnds])
    have h6 := hbin 6 (by simp [k5Incident, k5EdgeEnds])
    have hc0 := congrFun hcode 0
    have hc1 := congrFun hcode 1
    have hp := congrArg Fin.val hparity
    simp [k5SolvedBinsInt, k5FreeBins, k5FiberCode, k5FiberParity] at h4 h5 h6 hc0 hc1 hp
    have ht0 : t 0 = t' 0 := by omega
    have ht1 : t 1 = t' 1 := by omega
    have ht2 : t 2 = t' 2 := hc0
    have ht3 : t 3 = t' 3 := hc1
    have ht4 : t 4 = t' 4 := by omega
    funext i
    fin_cases i <;> assumption
  · have h4 := hbin 4 (by simp [k5Incident, k5EdgeEnds])
    have h7 := hbin 7 (by simp [k5Incident, k5EdgeEnds])
    have h8 := hbin 8 (by simp [k5Incident, k5EdgeEnds])
    have hc0 := congrFun hcode 0
    have hc1 := congrFun hcode 1
    have hp := congrArg Fin.val hparity
    simp [k5SolvedBinsInt, k5FreeBins, k5FiberCode, k5FiberParity] at h4 h7 h8 hc0 hc1 hp
    have ht0 : t 0 = t' 0 := hc0
    have ht1 : t 1 = t' 1 := hc1
    have ht2 : t 2 = t' 2 := by omega
    have ht3 : t 3 = t' 3 := by omega
    have ht4 : t 4 = t' 4 := by omega
    funext i
    fin_cases i <;> assumption
  · have h5 := hbin 5 (by simp [k5Incident, k5EdgeEnds])
    have h7 := hbin 7 (by simp [k5Incident, k5EdgeEnds])
    have h9 := hbin 9 (by simp [k5Incident, k5EdgeEnds])
    have hc0 := congrFun hcode 0
    have hc1 := congrFun hcode 1
    simp [k5SolvedBinsInt, k5FreeBins, k5FiberCode] at h5 h7 h9 hc0 hc1
    have ht0 : t 0 = t' 0 := by omega
    have ht1 : t 1 = t' 1 := hc0
    have ht2 : t 2 = t' 2 := by omega
    have ht3 : t 3 = t' 3 := hc1
    have ht4 : t 4 = t' 4 := by omega
    funext i
    fin_cases i <;> assumption
  · have h6 := hbin 6 (by simp [k5Incident, k5EdgeEnds])
    have h8 := hbin 8 (by simp [k5Incident, k5EdgeEnds])
    have h9 := hbin 9 (by simp [k5Incident, k5EdgeEnds])
    have hc0 := congrFun hcode 0
    have hc1 := congrFun hcode 1
    simp [k5SolvedBinsInt, k5FreeBins, k5FiberCode] at h6 h8 h9 hc0 hc1
    have ht0 : t 0 = t' 0 := hc0
    have ht1 : t 1 = t' 1 := by omega
    have ht2 : t 2 = t' 2 := hc1
    have ht3 : t 3 = t' 3 := by omega
    have ht4 : t 4 = t' 4 := by omega
    funext i
    fin_cases i <;> assumption

/-- Parameters in the finite box. -/
abbrev K5Parameter (U : ℕ) := ↥(k5ParameterBox U)

/-- A bounded version of `k5FiberCode`. -/
def k5BoundedFiberCode (U : ℕ) (v : Fin 5) (t : K5Parameter U) :
    Fin 2 → Fin (U / 100000000 + 1) := fun j =>
  ⟨k5FiberCode v t.1 j, by
    have ht := mem_k5ParameterBox.mp t.2
    fin_cases v <;> fin_cases j <;>
      simp only [k5FiberCode, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.tail_cons, Fin.isValue] <;>
      exact Nat.lt_succ_of_le (ht _)⟩

/-- The fibre over the four incident bins of a reference parameter. -/
abbrev K5IncidentFiber (U : ℕ) (s : Fin 5 → ℕ) (v : Fin 5)
    (t₀ : K5Parameter U) :=
  {t : K5Parameter U // ∀ e, k5Incident v e →
    k5SolvedBins U s t.1 e = k5SolvedBins U s t₀.1 e}

def k5FiberEmbeddingData {U : ℕ} {s : Fin 5 → ℕ} {v : Fin 5}
    {t₀ : K5Parameter U} (t : K5IncidentFiber U s v t₀) :
    (Fin 2 → Fin (U / 100000000 + 1)) × Fin 2 :=
  (k5BoundedFiberCode U v t.1, k5FiberParity v t.1.1)

lemma k5FiberEmbeddingData_injective {U : ℕ} (hU : 1000000000 ≤ U)
    {s : Fin 5 → ℕ} (hsLower : ∀ i, 998 * U / 1000 ≤ s i)
    (hsUpper : ∀ i, s i ≤ U) {v : Fin 5} {t₀ : K5Parameter U} :
    Function.Injective
      (k5FiberEmbeddingData (U := U) (s := s) (v := v) (t₀ := t₀)) := by
  intro t t' heq
  apply Subtype.ext
  apply Subtype.ext
  apply k5Parameter_eq_of_incident_bins_eq hU hsLower hsUpper
      t.1.2 t'.1.2 v
  · intro e he
    exact (t.2 e he).trans (t'.2 e he).symm
  · funext j
    have h := congrFun (congrArg Prod.fst heq) j
    exact congrArg Fin.val h
  · exact congrArg Prod.snd heq

/-- Quantitative rank-three bound: at most two box coordinates and one
parity bit remain after the incident bins have been fixed. -/
theorem card_k5IncidentFiber_le {U : ℕ} (hU : 1000000000 ≤ U)
    {s : Fin 5 → ℕ} (hsLower : ∀ i, 998 * U / 1000 ≤ s i)
    (hsUpper : ∀ i, s i ≤ U) (v : Fin 5) (t₀ : K5Parameter U) :
    Fintype.card (K5IncidentFiber U s v t₀) ≤
      2 * (U / 100000000 + 1) ^ 2 := by
  have hcard := Fintype.card_le_of_injective
    (k5FiberEmbeddingData (U := U) (s := s) (v := v) (t₀ := t₀))
    (k5FiberEmbeddingData_injective hU hsLower hsUpper
      (v := v) (t₀ := t₀))
  simpa [Fintype.card_prod, Fintype.card_pi, Nat.mul_comm] using hcard

end Erdos121
