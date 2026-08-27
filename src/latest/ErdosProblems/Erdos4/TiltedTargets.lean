import ErdosProblems.Erdos4.TiltedBlockProbability

/-! Concrete coordinate primes and squarefree rough-composite targets. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve

def IsRough (w n : ℕ) : Prop := ∀ p, p.Prime → p ∣ n → w < p

def coordinatePrimes (w B : ℕ) : Finset ℕ := B.primesLE.filter (fun p => w < p)

def coordinateValue (w B : ℕ) (p : coordinatePrimes w B) : ℕ := p.val

theorem mem_coordinatePrimes {w B p : ℕ} :
    p ∈ coordinatePrimes w B ↔ p.Prime ∧ w < p ∧ p ≤ B := by
  simp only [coordinatePrimes, Finset.mem_filter, Nat.mem_primesLE]
  tauto

instance coordinate_prime (w B : ℕ) (p : coordinatePrimes w B) :
    Fact (coordinateValue w B p).Prime := ⟨(mem_coordinatePrimes.mp p.property).1⟩

theorem coordinateValue_injective (w B : ℕ) : Function.Injective (coordinateValue w B) :=
  Subtype.val_injective

/-- A composite rough number cannot have a prime factor with a small cofactor. -/
theorem prime_factor_times_cutoff_le {w n p : ℕ} (hn : 0 < n) (hnp : ¬n.Prime)
    (hrough : IsRough w n) (hp : p.Prime) (hpn : p ∣ n) : p * w ≤ n := by
  obtain ⟨m, hm⟩ := hpn
  have hm0 : 0 < m := by
    by_contra h
    have hz : m = 0 := by omega
    simp [hm, hz] at hn
  have hm1 : m ≠ 1 := by
    intro h
    have hnp' : n = p := by simpa [h] using hm
    exact hnp (hnp' ▸ hp)
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
  have hqn : q ∣ n := by rw [hm]; exact dvd_mul_of_dvd_right hqm p
  have hwm : w ≤ m := (hrough q hq hqn).le.trans (Nat.le_of_dvd hm0 hqm)
  rw [hm]
  exact Nat.mul_le_mul_left p hwm

theorem rough_composite_prime_factor_le {w B Y n : ℕ}
    (hn : 0 < n) (hnY : n ≤ Y) (hnp : ¬n.Prime) (hrough : IsRough w n)
    (hwidth : Y < (B + 1) * w) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) : p ≤ B := by
  have hmul := (prime_factor_times_cutoff_le hn hnp hrough hp hpn).trans hnY
  by_contra h
  have hpB : B + 1 ≤ p := by omega
  exact (not_lt_of_ge ((Nat.mul_le_mul_right w hpB).trans hmul)) hwidth

noncomputable def roughComposites (x Y w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc x Y).filter (fun n => ¬n.Prime ∧ Squarefree n ∧ IsRough w n)

theorem mem_roughComposites {x Y w n : ℕ} :
    n ∈ roughComposites x Y w ↔ x < n ∧ n ≤ Y ∧ ¬n.Prime ∧ Squarefree n ∧ IsRough w n := by
  classical
  simp only [roughComposites, Finset.mem_filter, Finset.mem_Ioc]
  tauto

/-- Every prime factor is among the actual sieve coordinates, as in Lemma 3.2. -/
theorem roughComposites_primeFactors_covered {x Y w B n : ℕ}
    (hn : n ∈ roughComposites x Y w) (hwidth : Y < (B + 1) * w) :
    ∀ p ∈ n.primeFactors, ∃ l : coordinatePrimes w B, coordinateValue w B l = p := by
  obtain ⟨hxn, hnY, hnp, _, hrough⟩ := mem_roughComposites.mp hn
  intro p hp
  obtain ⟨hpprime, hpdvd, _⟩ := Nat.mem_primeFactors.mp hp
  have hpB := rough_composite_prime_factor_le (show 0 < n by omega) hnY hnp hrough hwidth hpprime hpdvd
  exact ⟨⟨p, mem_coordinatePrimes.mpr ⟨hpprime, hrough p hpprime hpdvd, hpB⟩⟩, rfl⟩

theorem roughComposites_survival {x Y w B n : ℕ}
    (hn : n ∈ roughComposites x Y w) (hwidth : Y < (B + 1) * w)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    (sieveLaw (coordinateValue w B) τ hτ).prob
        (fun a => Survives (coordinateValue w B) a {n}) =
      primeSurvival (coordinateValue w B) τ * (n : ℝ) ^ (-τ) :=
  sieveLaw_squarefree (coordinateValue w B) (coordinateValue_injective w B) τ hτ
    (mem_roughComposites.mp hn).2.2.2.1 (roughComposites_primeFactors_covered hn hwidth)

end Erdos4.Tilted
