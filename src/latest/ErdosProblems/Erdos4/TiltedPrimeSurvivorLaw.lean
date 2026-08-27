import ErdosProblems.Erdos4.TiltedCompositeFamily
import ErdosProblems.Erdos4.TiltedPrimeAccuracy
import ErdosProblems.Erdos4.FGKMTReweighting

/-! The true prime-survivor law is the pushforward of the tilted coordinate sieve. -/

namespace Erdos4.Tilted

open Filter FGKMT RandomResidueSieve

noncomputable def primeTargets (c : ℝ) (x : ℕ) : Finset ℕ :=
  ChebyshevIntervals.primeInterval x (gapTarget c x)

theorem primeTargets_properties {c : ℝ} {x q : ℕ} (hq : q ∈ primeTargets c x) :
    q.Prime ∧ x < q ∧ q ≤ gapTarget c x := ChebyshevIntervals.mem_primeInterval.mp hq

theorem primeTargets_card_le (c : ℝ) (x : ℕ) : (primeTargets c x).card ≤ gapTarget c x := by
  have hs : primeTargets c x ⊆ Finset.Icc 1 (gapTarget c x) := by
    intro q hq
    have hh := primeTargets_properties hq
    exact Finset.mem_Icc.mpr ⟨hh.1.one_le, hh.2.2⟩
  simpa using Finset.card_le_card hs

open Classical in
noncomputable def primeSurvivors (c : ℝ) (x : ℕ) (a : SieveState x) : Finset (primeTargets c x) :=
  Finset.univ.filter (fun q => Survives (sievePrimeValue x) a {q.val})

noncomputable def primeSurvivorLaw (c : ℝ) (x : ℕ) (hτ : 0 ≤ tiltExponent x) :
    FiniteLaw (Finset (primeTargets c x)) := (actualSieveLaw x hτ).map (primeSurvivors c x)

theorem mem_primeSurvivors (c : ℝ) (x : ℕ) (a : SieveState x) (q : primeTargets c x) :
    q ∈ primeSurvivors c x a ↔ Survives (sievePrimeValue x) a {q.val} := by
  simp only [primeSurvivors, Finset.mem_filter, Finset.mem_univ, true_and]

theorem subset_primeSurvivors (c : ℝ) (x : ℕ) (a : SieveState x) (T : Finset (primeTargets c x)) :
    T ⊆ primeSurvivors c x a ↔ Survives (sievePrimeValue x) a (T.image Subtype.val) := by
  rw [← blockEvent_survives]
  constructor
  · intro h n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    exact (mem_primeSurvivors c x a q).mp (h hq)
  · intro h q hq
    exact (mem_primeSurvivors c x a q).mpr (h q.val (Finset.mem_image.mpr ⟨q, hq, rfl⟩))

theorem primeSurvivorLaw_survival (c : ℝ) (x : ℕ) (hτ : 0 ≤ tiltExponent x)
    (T : Finset (primeTargets c x)) :
    survival (primeSurvivorLaw c x hτ) T =
      (actualSieveLaw x hτ).prob (fun a => Survives (sievePrimeValue x) a (T.image Subtype.val)) := by
  rw [survival, primeSurvivorLaw, FiniteLaw.prob_map]
  congr 1
  funext a
  exact propext (subset_primeSurvivors c x a T)

theorem primeSurvivorLaw_singleton (c : ℝ) (x : ℕ) (hτ : 0 ≤ tiltExponent x)
    (q : primeTargets c x) : survival (primeSurvivorLaw c x hτ) {q} = primeDensity x := by
  rw [primeSurvivorLaw_survival, Finset.image_singleton]
  exact sieveLaw_singleton_prime (sievePrimeValue x) (tiltExponent x) hτ
    (primeTargets_properties q.property).1
    (fun l => (sievePrimeValue_le x l).trans_lt (primeTargets_properties q.property).2.1)

theorem primeDensity_le_one (x : ℕ) : primeDensity x ≤ 1 := by
  unfold primeDensity primeSurvival
  apply Finset.prod_le_one
  · intro p _
    exact (baseline_pos (Fact.out : (sievePrimeValue x p).Prime).two_le
      (rpow_tilt_pos (Fact.out : (sievePrimeValue x p).Prime).two_le (tiltExponent x)).le).le
  · intro p _
    exact baseline_le_one (Fact.out : (sievePrimeValue x p).Prime).two_le
      (rpow_tilt_pos (Fact.out : (sievePrimeValue x p).Prime).two_le (tiltExponent x)).le

theorem eventually_primeSurvivorLaw_accurate {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ hτ : 0 ≤ tiltExponent x,
      SurvivalAccurate (primeSurvivorLaw c x hτ) (fun _ => primeDensity x)
        (3 * sieveDimension (growingIndex x)) (1 / Real.log (x : ℝ) ^ (80 : ℕ)) := by
  classical
  filter_upwards [eventually_tilted_prime_accuracy.{0}, eventually_gapTarget_bounds hc,
    eventually_growingDimension_bounds, eventually_outerScale_bounds] with x hacc hY hdim hb
  intro hτ T hT
  have hL : 1 ≤ Real.log (x : ℝ) := by linarith [hb.1]
  have hk : (sieveDimension (growingIndex x) : ℝ) ≤ Real.log (x : ℝ) :=
    hdim.2.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1 / 100 : ℝ) ≤ 1))
  have hcard : (T.image Subtype.val).card = T.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hnonzero : ∀ n ∈ T.image Subtype.val, ∀ p : sievePrimes x, ¬sievePrimeValue x p ∣ n := by
    intro n hn p hd
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hn
    have hh := primeTargets_properties q.property
    have heq := (Nat.prime_dvd_prime_iff_eq (Fact.out : (sievePrimeValue x p).Prime) hh.1).mp hd
    exact (ne_of_lt ((sievePrimeValue_le x p).trans_lt hh.2.1)) heq
  have hh := hacc (sievePrimes x) (sievePrimeValue x) (tiltExponent x) hτ
    (gapTarget c x) (3 * sieveDimension (growingIndex x)) hY.1
    (by have hh := hY.2.2.2.2.1; omega)
    (by push_cast; linarith) (sievePrimeValue_injective x)
    (fun p => (mem_coordinatePrimes.mp p.property).2.1) (T.image Subtype.val)
    (hcard.le.trans hT)
    (fun n hn => by obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hn; exact (primeTargets_properties q.property).2.2)
    hnonzero
  simpa only [primeSurvivorLaw_survival, setProduct, Finset.prod_const, hcard,
    primeDensity, sievePrimeValue, actualSieveLaw] using hh

end Erdos4.Tilted
