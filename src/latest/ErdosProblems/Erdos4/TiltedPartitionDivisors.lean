import ErdosProblems.Erdos4.TiltedWitnessCount
import ErdosProblems.Erdos4.TiltedFiberOffsets
import ErdosProblems.Erdos4.TiltedGlobalCorrelation

/-! Prime-divisor witness signatures for blocks of a fixed fiber partition. -/

open scoped BigOperators

namespace Erdos4.Tilted

theorem partition_divisor_count {C : Finset ℕ} (P : Finpartition C) (p U M d : ℕ)
    (hd : Squarefree d) (hd1 : 1 < d)
    (representative : P.parts → ℕ) (offset : ∀ E : P.parts, E.val → Fin U)
    (hrep : ∀ E, 1 ≤ representative E ∧ representative E ≤ M)
    (hformula : ∀ (E : P.parts) (n : E.val), n.val = representative E + p * (offset E n).val) :
    (((P.parts.filter (fun E => d ∣ ∏ n ∈ E, n)).card : ℝ)) ≤
      (U : ℝ) ^ d.primeFactors.card * ((M : ℝ) / d + 1) := by
  classical
  let good := P.parts.filter (fun E => d ∣ ∏ n ∈ E, n)
  let block : good → P.parts := fun E => ⟨E.val, (Finset.mem_filter.mp E.property).1⟩
  have hex : ∀ (E : good) (s : d.primeFactors), ∃ n : E.val, s.val ∣ n.val := by
    intro E s
    have hs := Nat.prime_of_mem_primeFactors s.property
    have hdiv : s.val ∣ ∏ n ∈ E.val, n :=
      (Nat.dvd_of_mem_primeFactors s.property).trans (Finset.mem_filter.mp E.property).2
    obtain ⟨n, hn, hsn⟩ := ((Nat.prime_iff.mp hs).dvd_finsetProd_iff (fun n : ℕ => n)).mp hdiv
    exact ⟨⟨n, hn⟩, hsn⟩
  choose witness hwitness using hex
  let signature : good → (d.primeFactors → Fin U) := fun E s => offset (block E) (witness E s)
  let value : good → ℕ := fun E => representative (block E)
  have hsig (E : good) (s : d.primeFactors) :
      (witness E s).val = value E + p * (signature E s).val := hformula (block E) (witness E s)
  have hinj : Function.Injective (fun E : good => (signature E, value E)) := by
    intro E F hEF
    have hsEq : signature E = signature F := congrArg Prod.fst hEF
    have hrEq : value E = value F := congrArg Prod.snd hEF
    obtain ⟨s, hs⟩ := Nat.nonempty_primeFactors.mpr hd1
    let s₀ : d.primeFactors := ⟨s, hs⟩
    have ho := congrArg Fin.val (congrFun hsEq s₀)
    have hn : (witness E s₀).val = (witness F s₀).val := by
      rw [hsig, hsig, hrEq, ho]
    apply Subtype.ext
    apply P.eq_of_mem_parts (block E).property (block F).property (witness E s₀).property
    rw [hn]
    exact (witness F s₀).property
  have hcongr : ∀ E F : good, signature E = signature F → value E ≡ value F [MOD d] := by
    intro E F hEF
    apply squarefree_modEq_of_prime_factors hd
    intro s hs
    let s₀ : d.primeFactors := ⟨s, hs⟩
    have ho := congrArg Fin.val (congrFun hEF s₀)
    have hn : (witness E s₀).val ≡ (witness F s₀).val [MOD s] :=
      (hwitness E s₀).modEq_zero_nat.trans (hwitness F s₀).zero_modEq_nat
    rw [hsig, hsig, ho] at hn
    exact Nat.ModEq.add_right_cancel' _ hn
  have hc := card_signature_congruence_le signature value hinj hd.ne_zero.bot_lt
    (fun E => hrep (block E)) hcongr
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hc

theorem partition_divisor_count_of_interval {C : Finset ℕ} (P : Finpartition C)
    (x p Y U d : ℕ) (hp : 0 < p) (hd : Squarefree d) (hd1 : 1 < d)
    (hC : ∀ n ∈ C, x < n ∧ n ≤ Y) (hYU : Y < p * U)
    (hfiber : ∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod p) = (m : ZMod p)) :
    (((P.parts.filter (fun E => d ∣ ∏ n ∈ E, n)).card : ℝ)) ≤
      (U : ℝ) ^ d.primeFactors.card * (((x + p : ℕ) : ℝ) / d + 1) := by
  obtain ⟨representative, offset, hrep, hformula⟩ := exists_partition_offsets P x p Y U hp hC hYU hfiber
  exact partition_divisor_count P p U (x + p) d hd hd1 representative offset hrep hformula

/-- The two block witnesses may be counted separately, then paired. -/
theorem partition_gcd_pair_count {C : Finset ℕ} (P : Finpartition C)
    (x p Y U d : ℕ) (hp : 0 < p) (hd : Squarefree d) (hd1 : 1 < d)
    (hC : ∀ n ∈ C, x < n ∧ n ≤ Y) (hYU : Y < p * U)
    (hfiber : ∀ E ∈ P.parts, ∀ n ∈ E, ∀ m ∈ E, (n : ZMod p) = (m : ZMod p)) :
    ((((P.parts ×ˢ P.parts).filter (fun EF => d ∣ blockGcd EF.1 EF.2)).card : ℝ)) ≤
      ((U : ℝ) ^ d.primeFactors.card * (((x + p : ℕ) : ℝ) / d + 1)) ^ 2 := by
  classical
  let good := P.parts.filter (fun E => d ∣ ∏ n ∈ E, n)
  have hsub : (P.parts ×ˢ P.parts).filter (fun EF => d ∣ blockGcd EF.1 EF.2) ⊆ good ×ˢ good := by
    intro EF hEF
    obtain ⟨hEF, hdEF⟩ := Finset.mem_filter.mp hEF
    obtain ⟨hE, hF⟩ := Finset.mem_product.mp hEF
    obtain ⟨hdE, hdF⟩ := Nat.dvd_gcd_iff.mp hdEF
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hE, hdE⟩,
      Finset.mem_filter.mpr ⟨hF, hdF⟩⟩
  have hc : (((P.parts ×ˢ P.parts).filter (fun EF => d ∣ blockGcd EF.1 EF.2)).card : ℝ) ≤
      (good.card : ℝ) ^ 2 := by
    have hh := Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)
    simpa only [Finset.card_product, Nat.cast_mul, pow_two] using hh
  exact hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg good.card)
    (partition_divisor_count_of_interval P x p Y U d hp hd hd1 hC hYU hfiber) 2)

end Erdos4.Tilted
