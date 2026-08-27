import ErdosProblems.Erdos4.TiltedSignedOffsets
import ErdosProblems.Erdos4.TiltedWitnessCount
import ErdosProblems.Erdos4.TiltedGlobalCorrelation

/-! Signed divisor witnesses count colors whose root companions have a common divisor. -/

open scoped BigOperators

namespace Erdos4.Tilted

theorem rooted_divisor_count (colors : Finset ℕ) (companion : ℕ → Finset ℕ)
    (v Y U M d : ℕ) (hd : Squarefree d)
    (hcolors : ∀ p ∈ colors, 1 ≤ p ∧ p ≤ M)
    (hvY : v ≤ Y) (hYU : ∀ p ∈ colors, Y < p * U)
    (hcomp : ∀ p ∈ colors, ∀ n ∈ companion p,
      n ≤ Y ∧ n ≠ v ∧ (n : ZMod p) = (v : ZMod p))
    (hU : ∀ s ∈ d.primeFactors, U ≤ s) :
    (((colors.filter (fun p => d ∣ ∏ n ∈ companion p, n)).card : ℝ)) ≤
      (2 * (U : ℝ)) ^ d.primeFactors.card * ((M : ℝ) / d + 1) := by
  classical
  let good := colors.filter (fun p => d ∣ ∏ n ∈ companion p, n)
  have hex : ∀ (p : good) (s : d.primeFactors),
      ∃ o : Bool × Fin U, ∃ n ∈ companion p.val,
        s.val ∣ n ∧ SignedOffsetWitness p.val v n U o := by
    intro p s
    have hp := (Finset.mem_filter.mp p.property).1
    have hs := Nat.prime_of_mem_primeFactors s.property
    have hdiv : s.val ∣ ∏ n ∈ companion p.val, n :=
      (Nat.dvd_of_mem_primeFactors s.property).trans (Finset.mem_filter.mp p.property).2
    obtain ⟨n, hn, hsn⟩ := ((Nat.prime_iff.mp hs).dvd_finsetProd_iff (fun n : ℕ => n)).mp hdiv
    obtain ⟨hnY, hnv, hnmod⟩ := hcomp p.val hp n hn
    obtain ⟨o, ho⟩ := exists_signed_offset (hcolors p.val hp).1 hvY hnY hnv (hYU p.val hp) hnmod
    exact ⟨o, n, hn, hsn, ho⟩
  choose signature witness hwmem hwdiv hwoff using hex
  have hinj : Function.Injective (fun p : good => (signature p, p.val)) := by
    intro p q hpq
    exact Subtype.ext (congrArg Prod.snd hpq)
  have hcongr : ∀ p q : good, signature p = signature q → p.val ≡ q.val [MOD d] := by
    intro p q hpq
    apply squarefree_modEq_of_prime_factors hd
    intro s hs
    let s₀ : d.primeFactors := ⟨s, hs⟩
    have ho := congrFun hpq s₀
    have hq : SignedOffsetWitness q.val v (witness q s₀) U (signature p s₀) := by
      rw [ho]
      exact hwoff q s₀
    exact same_signed_witness_modEq (Nat.prime_of_mem_primeFactors hs) (signature p s₀)
      (hU s hs) (hwoff p s₀) hq (hwdiv p s₀) (hwdiv q s₀)
  have hc := card_signature_congruence_le signature (fun p : good => p.val) hinj
    hd.ne_zero.bot_lt (fun p => hcolors p.val (Finset.mem_filter.mp p.property).1) hcongr
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hc

theorem rooted_gcd_pair_count (colors : Finset ℕ) (companion : ℕ → Finset ℕ)
    (v Y U M d : ℕ) (hd : Squarefree d)
    (hcolors : ∀ p ∈ colors, 1 ≤ p ∧ p ≤ M)
    (hvY : v ≤ Y) (hYU : ∀ p ∈ colors, Y < p * U)
    (hcomp : ∀ p ∈ colors, ∀ n ∈ companion p,
      n ≤ Y ∧ n ≠ v ∧ (n : ZMod p) = (v : ZMod p))
    (hU : ∀ s ∈ d.primeFactors, U ≤ s) :
    ((((colors ×ˢ colors).filter (fun pq => d ∣ blockGcd (companion pq.1) (companion pq.2))).card : ℝ)) ≤
      ((2 * (U : ℝ)) ^ d.primeFactors.card * ((M : ℝ) / d + 1)) ^ 2 := by
  classical
  let good := colors.filter (fun p => d ∣ ∏ n ∈ companion p, n)
  have hsub : (colors ×ˢ colors).filter
      (fun pq => d ∣ blockGcd (companion pq.1) (companion pq.2)) ⊆ good ×ˢ good := by
    intro pq hpq
    obtain ⟨hpq, hdpq⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    obtain ⟨hdp, hdq⟩ := Nat.dvd_gcd_iff.mp hdpq
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp, hdp⟩,
      Finset.mem_filter.mpr ⟨hq, hdq⟩⟩
  have hc : (((colors ×ˢ colors).filter
      (fun pq => d ∣ blockGcd (companion pq.1) (companion pq.2))).card : ℝ) ≤
      (good.card : ℝ) ^ 2 := by
    have hh := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
    simpa only [Finset.card_product, Nat.cast_mul, pow_two] using hh
  exact hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg good.card)
    (rooted_divisor_count colors companion v Y U M d hd hcolors hvY hYU hcomp hU) 2)

end Erdos4.Tilted
