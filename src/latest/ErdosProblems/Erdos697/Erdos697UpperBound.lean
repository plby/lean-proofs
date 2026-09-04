import ErdosProblems.Erdos697.Erdos697Cover
import ErdosProblems.Erdos697.Erdos697Factorization
import ErdosProblems.Erdos697.Erdos697MarkedSubset

/-!
# Finite multiscale upper bound for Erdős Problem 697
-/

open Filter Set Real
open scoped Topology BigOperators

namespace Erdos697.UpperBound

noncomputable section

open Erdos697

/-- Prime coordinates in a window which are units modulo `m`. -/
def coprimePrimes (L U m : ℕ) : Finset ℕ :=
  (PrimeWindow.primes L U).filter fun p ↦ p.Coprime m

@[simp] theorem mem_coprimePrimes {L U m p : ℕ} :
    p ∈ coprimePrimes L U m ↔
      L < p ∧ p ≤ U ∧ p.Prime ∧ p.Coprime m := by
  simp [coprimePrimes, and_assoc]

def goodParts (R U m : ℕ) : Finset ℕ :=
  (Smooth.parts R U).filter fun a ↦ a < m ∧ a.Coprime m

def badParts (R U m : ℕ) : Finset ℕ :=
  (Smooth.parts R U).filter fun a ↦ m ≤ a

def multiples (a : ℕ) : Set ℕ := {n | a ∣ n}

/-- If a density-bearing set is covered by finitely many other
density-bearing sets, its density is at most the sum of their densities. -/
theorem hasDensity_le_finset_iUnion
    {A : Type*} [DecidableEq A]
    {S : Set ℕ} {s : ℝ} (hS : S.HasDensity s)
    (I : Finset A) (T : A → Set ℕ) (d : A → ℝ)
    (hT : ∀ i ∈ I, (T i).HasDensity (d i))
    (hsub : S ⊆ ⋃ i ∈ I, T i) :
    s ≤ ∑ i ∈ I, d i := by
  have hsum : Tendsto
      (fun n : ℕ ↦ ∑ i ∈ I, (T i).partialDensity Set.univ n)
      atTop (𝓝 (∑ i ∈ I, d i)) := by
    apply tendsto_finsetSum
    intro i hi
    exact hT i hi
  apply le_of_tendsto_of_tendsto' hS hsum
  intro n
  simp only [Set.partialDensity, Set.inter_univ]
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hfinite (i : A) : (T i ∩ Set.Iio n).Finite := Set.toFinite _
  have hcover : S ∩ Set.Iio n ⊆ ⋃ i ∈ I, (T i ∩ Set.Iio n) := by
    intro x hx
    have hxU := hsub hx.1
    simp only [Set.mem_iUnion] at hxU ⊢
    obtain ⟨i, hiI, hxi⟩ := hxU
    exact ⟨i, hiI, hxi, hx.2⟩
  calc
    ((S ∩ Set.Iio n).ncard : ℝ) ≤
        ((⋃ i ∈ I, (T i ∩ Set.Iio n)).ncard : ℕ) := by
      exact_mod_cast Set.ncard_le_ncard hcover
    _ ≤ ∑ i ∈ I, ((T i ∩ Set.Iio n).ncard : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast I.set_ncard_biUnion_le (fun i ↦ T i ∩ Set.Iio n)

private theorem pairwise_val_primes
    {P : Finset ℕ} (hprime : ∀ p ∈ P, p.Prime) :
    Pairwise (Function.onFun Nat.Coprime (fun p : ↑P ↦ p.1)) := by
  intro p q hpq
  have hp := hprime p.1 p.2
  have hq := hprime q.1 q.2
  exact hp.coprime_iff_not_dvd.mpr fun hd ↦
    hpq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd))

theorem smooth_coprime_prime
    {R U a p : ℕ} (ha : a ∈ Smooth.parts R U)
    (hp : p.Prime) (hRp : R < p) : a.Coprime p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hpa
  have hsmooth := (Smooth.mem_parts.mp ha).2.2
  have hlt := (Nat.mem_smoothNumbers'.mp hsmooth) p hp hpa
  omega

/-- Exact density of ordinary multiples, obtained as the empty-coordinate
case of the CRT conditioning theorem. -/
theorem multiples_hasDensity {a : ℕ} (ha : 0 < a) :
    (multiples a).HasDensity (1 / (a : ℝ)) := by
  let q : Empty → ℕ := Empty.elim
  let Good : Finset Empty → Prop := fun _ ↦ True
  have h := Cover.eventSet_hasDensity a ha q (fun i ↦ i.elim)
    (by intro i; exact i.elim) (by intro i; exact i.elim) Good
  have hsum :
      (∑ S ∈ (Finset.univ : Finset (Finset Empty)).filter Good,
        Bernoulli.weight Finset.univ (fun i ↦ 1 / (q i : ℝ)) S) = 1 := by
    have huniv : (Finset.univ : Finset (Finset Empty)) = {∅} := by
      ext S
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim S ∅
    rw [huniv]
    simp [Good, Bernoulli.weight]
  rw [hsum] at h
  simpa [multiples, Cover.eventSet, Cover.selected, Good] using h

/-- Selected-cardinality event in one full prime window. -/
def highSet (a L U K : ℕ) : Set ℕ :=
  Cover.eventSet a (fun p : ↑(PrimeWindow.primes L U) ↦ p.1)
    (fun S ↦ K < S.card)

/-- Target-hitting event in the coprime prime window. -/
def hitSet (a L U m : ℕ) (B : Finset (ZMod m)ˣ) (K : ℕ) : Set ℕ :=
  let P := coprimePrimes L U m
  let f : ↑P → (ZMod m)ˣ := fun p ↦
    ZMod.unitOfCoprime p.1 (mem_coprimePrimes.mp p.2).2.2.2
  Cover.eventSet a (fun p : ↑P ↦ p.1)
    (fun S ↦ S.card ≤ K ∧
      MarkedSubset.hitsUsing f Finset.univ B S)

/-- Target-hitting event where the witnessing subproduct must use a prime
above `M`, while coordinates range over the entire `(L,U]` window. -/
def markedHitSet (a L M U m : ℕ) (B : Finset (ZMod m)ˣ) (K : ℕ) : Set ℕ :=
  let P := coprimePrimes L U m
  let f : ↑P → (ZMod m)ˣ := fun p ↦
    ZMod.unitOfCoprime p.1 (mem_coprimePrimes.mp p.2).2.2.2
  let J : Finset ↑P := Finset.univ.filter fun p ↦ M < p.1
  Cover.eventSet a (fun p : ↑P ↦ p.1)
    (fun S ↦ S.card ≤ K ∧ MarkedSubset.hitsUsing f J B S)

/-- Bernoulli probability of selecting more than `K` primes in `(L,U]`. -/
def highProb (L U K : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ :
      Finset (Finset ↑(PrimeWindow.primes L U))).filter
        (fun S ↦ K < S.card),
    Bernoulli.weight Finset.univ (fun p ↦ 1 / (p.1 : ℝ)) S

/-- Bernoulli probability of a bounded-cardinality target hit. -/
def hitProb (L U m : ℕ) (B : Finset (ZMod m)ˣ) (K : ℕ) : ℝ :=
  ∑ S ∈ MarkedSubset.event
      (fun p : ↑(coprimePrimes L U m) ↦
        ZMod.unitOfCoprime p.1 (mem_coprimePrimes.mp p.2).2.2.2)
      Finset.univ B K,
    Bernoulli.weight Finset.univ (fun p ↦ 1 / (p.1 : ℝ)) S

/-- Bernoulli probability of a bounded-cardinality target hit that uses a
prime above `M`. -/
def markedHitProb (L M U m : ℕ) (B : Finset (ZMod m)ˣ) (K : ℕ) : ℝ :=
  ∑ S ∈ MarkedSubset.event
      (fun p : ↑(coprimePrimes L U m) ↦
        ZMod.unitOfCoprime p.1 (mem_coprimePrimes.mp p.2).2.2.2)
      ((Finset.univ : Finset ↑(coprimePrimes L U m)).filter
        (fun p ↦ M < p.1)) B K,
    Bernoulli.weight Finset.univ (fun p ↦ 1 / (p.1 : ℝ)) S

private theorem window_pairwise (L U : ℕ) :
    Pairwise (Function.onFun Nat.Coprime
      (fun p : ↑(PrimeWindow.primes L U) ↦ p.1)) :=
  pairwise_val_primes fun p hp ↦ (PrimeWindow.mem_primes.mp hp).2.2

private theorem coprimeWindow_pairwise (L U m : ℕ) :
    Pairwise (Function.onFun Nat.Coprime
      (fun p : ↑(coprimePrimes L U m) ↦ p.1)) :=
  pairwise_val_primes fun p hp ↦ (mem_coprimePrimes.mp hp).2.2.1

theorem highSet_hasDensity
    {a L U K : ℕ} (ha : a ∈ Smooth.parts L U) :
    (highSet a L U K).HasDensity ((1 : ℝ) / a * highProb L U K) := by
  have ha0 : 0 < a := (Smooth.mem_parts.mp ha).1
  have h := Cover.eventSet_hasDensity a ha0
    (fun p : ↑(PrimeWindow.primes L U) ↦ p.1)
    (fun p ↦ (PrimeWindow.mem_primes.mp p.2).2.2.pos)
    (window_pairwise L U)
    (fun p ↦ smooth_coprime_prime ha
      (PrimeWindow.mem_primes.mp p.2).2.2
      (PrimeWindow.mem_primes.mp p.2).1)
    (fun S : Finset ↑(PrimeWindow.primes L U) ↦ K < S.card)
  simpa [highSet, highProb] using h

theorem hitSet_hasDensity
    {a L U m K : ℕ} (ha : a ∈ Smooth.parts L U)
    (B : Finset (ZMod m)ˣ) :
    (hitSet a L U m B K).HasDensity
      ((1 : ℝ) / a * hitProb L U m B K) := by
  classical
  have ha0 : 0 < a := (Smooth.mem_parts.mp ha).1
  have h := Cover.eventSet_hasDensity a ha0
    (fun p : ↑(coprimePrimes L U m) ↦ p.1)
    (fun p ↦ (mem_coprimePrimes.mp p.2).2.2.1.pos)
    (coprimeWindow_pairwise L U m)
    (fun p ↦ smooth_coprime_prime ha
      (mem_coprimePrimes.mp p.2).2.2.1
      (mem_coprimePrimes.mp p.2).1)
    (fun S ↦ S.card ≤ K ∧ MarkedSubset.hitsUsing
      (fun p : ↑(coprimePrimes L U m) ↦
        ZMod.unitOfCoprime p.1 (mem_coprimePrimes.mp p.2).2.2.2)
      Finset.univ B S)
  simpa [hitSet, hitProb, MarkedSubset.event] using h

theorem markedHitSet_hasDensity
    {a L M U m K : ℕ} (ha : a ∈ Smooth.parts L U)
    (B : Finset (ZMod m)ˣ) :
    (markedHitSet a L M U m B K).HasDensity
      ((1 : ℝ) / a * markedHitProb L M U m B K) := by
  classical
  have ha0 : 0 < a := (Smooth.mem_parts.mp ha).1
  have h := Cover.eventSet_hasDensity a ha0
    (fun p : ↑(coprimePrimes L U m) ↦ p.1)
    (fun p ↦ (mem_coprimePrimes.mp p.2).2.2.1.pos)
    (coprimeWindow_pairwise L U m)
    (fun p ↦ smooth_coprime_prime ha
      (mem_coprimePrimes.mp p.2).2.2.1
      (mem_coprimePrimes.mp p.2).1)
    (fun S ↦ S.card ≤ K ∧ MarkedSubset.hitsUsing
      (fun p : ↑(coprimePrimes L U m) ↦
        ZMod.unitOfCoprime p.1 (mem_coprimePrimes.mp p.2).2.2.2)
      ((Finset.univ : Finset ↑(coprimePrimes L U m)).filter
        (fun p ↦ M < p.1)) B S)
  simpa [markedHitSet, markedHitProb, MarkedSubset.event] using h

/-! ## The deterministic factorization cover -/

/-- Regard a finite set as a set of coordinates in a larger finite set. -/
def subtypeMapOfSubset {S P : Finset ℕ} (hSP : S ⊆ P) : ↑S ↪ ↑P where
  toFun p := ⟨p.1, hSP p.2⟩
  inj' := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ h
    simp only [Subtype.mk.injEq] at h ⊢
    exact h

/-- The coordinate copy of `S` inside the subtype attached to `P`. -/
def liftFinset {S P : Finset ℕ} (hSP : S ⊆ P) : Finset ↑P :=
  (Finset.univ : Finset ↑S).map (subtypeMapOfSubset hSP)

@[simp] theorem mem_liftFinset {S P : Finset ℕ} (hSP : S ⊆ P)
    (p : ↑P) : p ∈ liftFinset hSP ↔ p.1 ∈ S := by
  constructor
  · intro hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp
    exact q.2
  · intro hp
    refine Finset.mem_map.mpr ⟨⟨p.1, hp⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    rfl

theorem card_liftFinset {S P : Finset ℕ} (hSP : S ⊆ P) :
    (liftFinset hSP).card = S.card := by
  rw [liftFinset, Finset.card_map, Finset.card_univ, Fintype.card_coe]

theorem prod_liftFinset {S P : Finset ℕ} (hSP : S ⊆ P)
    {M : Type*} [CommMonoid M] (f : ↑P → M) :
    (∏ p ∈ liftFinset hSP, f p) =
      ∏ p : ↑S, f (subtypeMapOfSubset hSP p) := by
  rw [liftFinset, Finset.prod_map]

/-- The modular product forced by `d ≡ 1 (mod m)` after the small/rough
factorization of `d`. -/
theorem prod_rough_units_eq_small_inv
    {m a d : ℕ} {S : Finset ℕ}
    (ha : a.Coprime m)
    (hcop : ∀ p ∈ S, p.Coprime m)
    (hsplit : a * (∏ p ∈ S, p) = d)
    (hmod : d ≡ 1 [MOD m]) :
    (∏ p : ↑S, ZMod.unitOfCoprime p.1 (hcop p.1 p.2)) =
      (ZMod.unitOfCoprime a ha)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  apply Units.ext
  simp only [Units.val_mul, Units.val_one, ZMod.coe_unitOfCoprime]
  have hz : (d : ZMod m) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff d 1 m).2 hmod
  have hs := congrArg (fun n : ℕ ↦ (n : ZMod m)) hsplit
  rw [Nat.cast_mul, Nat.cast_prod] at hs
  have hprod :
      (∏ p ∈ S, (p : ZMod m)) = ∏ p : ↑S, (p.1 : ZMod m) :=
    Finset.prod_subtype S (fun _ ↦ Iff.rfl) (fun p ↦ (p : ZMod m))
  rw [hprod] at hs
  have hval :
      ((↑(∏ p : ↑S, ZMod.unitOfCoprime p.1 (hcop p.1 p.2)) : ZMod m)) =
        ∏ p : ↑S, (p.1 : ZMod m) := by
    simp [ZMod.coe_unitOfCoprime]
  rw [hval, hs, hz]

@[simp] theorem mem_goodParts {R U m a : ℕ} :
    a ∈ goodParts R U m ↔
      a ∈ Smooth.parts R U ∧ a < m ∧ a.Coprime m := by
  simp [goodParts, and_assoc]

@[simp] theorem mem_badParts {R U m a : ℕ} :
    a ∈ badParts R U m ↔ a ∈ Smooth.parts R U ∧ m ≤ a := by
  simp [badParts]

theorem smooth_parts_mono_left {R P U a : ℕ} (hRP : R ≤ P)
    (ha : a ∈ Smooth.parts R U) : a ∈ Smooth.parts P U := by
  rw [Smooth.mem_parts] at ha ⊢
  refine ⟨ha.1, ha.2.1, ?_⟩
  rw [Nat.mem_smoothNumbers'] at ha ⊢
  intro p hp hpa
  have := ha.2.2 p hp hpa
  omega

theorem goodPart_mem_middle_parts {R P U m a : ℕ}
    (hRP : R ≤ P) (hmP : m ≤ P) (ha : a ∈ goodParts R U m) :
    a ∈ Smooth.parts R P := by
  have h := mem_goodParts.mp ha
  rw [Smooth.mem_parts] at h ⊢
  exact ⟨h.1.1, le_trans (Nat.le_of_lt h.2.1) hmP, h.1.2.2⟩

/-- Finite index type for the bad smooth parts, repeated rough primes, and
the four probability events attached to each good smooth part. -/
abbrev CoverIndex (R U m : ℕ) :=
  Sum (Sum ↑(badParts R U m) ↑(PrimeWindow.primes R U))
    (↑(goodParts R U m) × Fin 4)

def targetUnit {R U m : ℕ} (a : ↑(goodParts R U m)) : (ZMod m)ˣ :=
  (ZMod.unitOfCoprime a.1 (mem_goodParts.mp a.2).2.2)⁻¹

/-- The actual set attached to one cover index. -/
def indexedCoverSet (R P U m Kmid Kmark : ℕ) :
    CoverIndex R U m → Set ℕ
  | Sum.inl (Sum.inl a) => multiples a.1
  | Sum.inl (Sum.inr p) => multiples (p.1 ^ 2)
  | Sum.inr (a, j) =>
      if j = 0 then highSet a.1 R P Kmid
      else if j = 1 then highSet a.1 P U Kmark
      else if j = 2 then
        hitSet a.1 R P m {targetUnit a} Kmid
      else markedHitSet a.1 R P U m {targetUnit a} (Kmid + Kmark)

/-- Exact density attached to one cover index. -/
def indexedCoverDensity (R P U m Kmid Kmark : ℕ) :
    CoverIndex R U m → ℝ
  | Sum.inl (Sum.inl a) => 1 / (a.1 : ℝ)
  | Sum.inl (Sum.inr p) => 1 / (p.1 : ℝ) ^ 2
  | Sum.inr (a, j) =>
      if j = 0 then (1 / (a.1 : ℝ)) * highProb R P Kmid
      else if j = 1 then (1 / (a.1 : ℝ)) * highProb P U Kmark
      else if j = 2 then
        (1 / (a.1 : ℝ)) * hitProb R P m {targetUnit a} Kmid
      else (1 / (a.1 : ℝ)) *
        markedHitProb R P U m {targetUnit a} (Kmid + Kmark)

theorem indexedCoverSet_hasDensity
    {R P U m Kmid Kmark : ℕ} (hRP : R ≤ P) (hmP : m ≤ P) :
    ∀ i : CoverIndex R U m,
      (indexedCoverSet R P U m Kmid Kmark i).HasDensity
        (indexedCoverDensity R P U m Kmid Kmark i) := by
  classical
  intro i
  rcases i with (⟨a⟩ | ⟨p⟩) | ⟨a, j⟩
  · simpa [indexedCoverSet, indexedCoverDensity] using
      multiples_hasDensity (Smooth.mem_parts.mp
        (mem_badParts.mp a.2).1).1
  · have hp : 0 < p.1 := (PrimeWindow.mem_primes.mp p.2).2.2.pos
    simpa [indexedCoverSet, indexedCoverDensity, Nat.cast_pow] using
      multiples_hasDensity (pow_pos hp 2)
  · have haRU := (mem_goodParts.mp a.2).1
    have haRP := goodPart_mem_middle_parts hRP hmP a.2
    have haPU := smooth_parts_mono_left hRP haRU
    fin_cases j
    · simpa [indexedCoverSet, indexedCoverDensity] using
        highSet_hasDensity (K := Kmid) haRP
    · simpa [indexedCoverSet, indexedCoverDensity] using
        highSet_hasDensity (K := Kmark) haPU
    · simpa [indexedCoverSet, indexedCoverDensity] using
        hitSet_hasDensity (K := Kmid) haRP {targetUnit a}
    · simpa [indexedCoverSet, indexedCoverDensity] using
        markedHitSet_hasDensity (M := P) (K := Kmid + Kmark)
          haRU {targetUnit a}

theorem liftFinset_subset_selected
    {S P : Finset ℕ} (hSP : S ⊆ P) {n : ℕ}
    (hdiv : ∀ p ∈ S, p ∣ n) :
    liftFinset hSP ⊆ Cover.selected (fun p : ↑P ↦ p.1) n := by
  intro p hp
  rw [mem_liftFinset] at hp
  simp only [Cover.selected, Finset.mem_filter, Finset.mem_univ, true_and]
  exact hdiv p.1 hp

/-- A squarefree rough-prime set gives the precise subset-product witness
inside any ambient prime-coordinate set containing it. -/
theorem lift_hitsUsing
    {m a d n : ℕ} {S P : Finset ℕ} (hSP : S ⊆ P)
    (ha : a.Coprime m) (hPcop : ∀ p ∈ P, p.Coprime m)
    (hsplit : a * (∏ p ∈ S, p) = d) (hmod : d ≡ 1 [MOD m])
    (hdiv : ∀ p ∈ S, p ∣ n) (hSne : S.Nonempty)
    (J : Finset ↑P)
    (hmark : ∃ p : ↑S, subtypeMapOfSubset hSP p ∈ J) :
    MarkedSubset.hitsUsing
      (fun p : ↑P ↦ ZMod.unitOfCoprime p.1
        (hPcop p.1 p.2))
      J {(ZMod.unitOfCoprime a ha)⁻¹}
      (Cover.selected (fun p : ↑P ↦ p.1) n) := by
  classical
  let T := liftFinset hSP
  refine ⟨T, liftFinset_subset_selected hSP hdiv, ?_, ?_, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hT
    have : T.card = 0 := by simp [hT]
    rw [card_liftFinset hSP] at this
    have hpos : 0 < S.card := Finset.card_pos.mpr hSne
    omega
  · simp only [Finset.mem_singleton]
    rw [prod_liftFinset hSP]
    calc
      (∏ p : ↑S, ZMod.unitOfCoprime
          (subtypeMapOfSubset hSP p).1
          (hPcop _ (subtypeMapOfSubset hSP p).2)) =
          ∏ p : ↑S, ZMod.unitOfCoprime p.1
            (hPcop p.1 (hSP p.2)) := by
        apply Finset.prod_congr rfl
        intro p _
        apply Units.ext
        change ((subtypeMapOfSubset hSP p).1 : ZMod m) = (p.1 : ZMod m)
        rfl
      _ = _ := prod_rough_units_eq_small_inv ha
        (fun p hp ↦ hPcop p (hSP hp)) hsplit hmod
  · obtain ⟨p, hpJ⟩ := hmark
    refine ⟨subtypeMapOfSubset hSP p, ?_, hpJ⟩
    exact (mem_liftFinset hSP _).2 p.2

theorem selected_card_eq_filter (P : Finset ℕ) (n : ℕ) :
    (Cover.selected (fun p : ↑P ↦ p.1) n).card =
      (P.filter fun p ↦ p ∣ n).card := by
  classical
  unfold Cover.selected
  have huniv : (Finset.univ : Finset ↑P) = P.attach := by
    ext p
    simp
  rw [huniv]
  change (P.attach.filter (fun p ↦ p.1 ∣ n)).card = _
  let e : ↑P ↪ ℕ := Function.Embedding.subtype (fun p ↦ p ∈ P)
  have hmap :
      ((P.attach.filter (fun p ↦ p.1 ∣ n)).map e) =
        P.filter (fun p ↦ p ∣ n) := by
    ext p
    simp [e, and_comm]
  rw [← hmap, Finset.card_map]

theorem selected_coprime_card_le_split
    (R P U m n : ℕ) :
    (Cover.selected (fun p : ↑(coprimePrimes R U m) ↦ p.1) n).card ≤
      (Cover.selected (fun p : ↑(PrimeWindow.primes R P) ↦ p.1) n).card +
      (Cover.selected (fun p : ↑(PrimeWindow.primes P U) ↦ p.1) n).card := by
  classical
  simp only [selected_card_eq_filter]
  let A := (PrimeWindow.primes R P).filter fun p ↦ p ∣ n
  let B := (PrimeWindow.primes P U).filter fun p ↦ p ∣ n
  have hsub : (coprimePrimes R U m).filter (fun p ↦ p ∣ n) ⊆ A ∪ B := by
    intro p hp
    have h := mem_coprimePrimes.mp (Finset.mem_filter.mp hp).1
    have hpn := (Finset.mem_filter.mp hp).2
    by_cases hpP : p ≤ P
    · apply Finset.mem_union_left B
      exact Finset.mem_filter.mpr
        ⟨PrimeWindow.mem_primes.mpr ⟨h.1, hpP, h.2.2.1⟩, hpn⟩
    · apply Finset.mem_union_right A
      exact Finset.mem_filter.mpr
        ⟨PrimeWindow.mem_primes.mpr ⟨by omega, h.2.1, h.2.2.1⟩, hpn⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le A B)

theorem selected_card_mono {P Q : Finset ℕ} (hPQ : P ⊆ Q) (n : ℕ) :
    (Cover.selected (fun p : ↑P ↦ p.1) n).card ≤
      (Cover.selected (fun p : ↑Q ↦ p.1) n).card := by
  classical
  rw [selected_card_eq_filter, selected_card_eq_filter]
  apply Finset.card_le_card
  intro p hp
  exact Finset.mem_filter.mpr
    ⟨hPQ (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩

/-- A cutoff version of the divisor set.  The main file maps every
eligible divisor into this set using `m < d` and the exact integer cutoff. -/
def boundedDivisorSet (m U : ℕ) : Set ℕ :=
  {n | ∃ d, m < d ∧ d ≤ U ∧ d ≡ 1 [MOD m] ∧ d ∣ n}

/-- Deterministic multiscale cover.  Every relevant divisor either has a
large small-prime part, a repeated rough prime, too many rough primes in
one of the two windows, or a bounded subset-product witness. -/
theorem boundedDivisorSet_subset_cover
    {R P U m Kmid Kmark : ℕ}
    (hR : 1 ≤ R) (hRP : R ≤ P) (hmP : m ≤ P) :
    boundedDivisorSet m U ⊆
      ⋃ i ∈ (Finset.univ : Finset (CoverIndex R U m)),
        indexedCoverSet R P U m Kmid Kmark i := by
  classical
  intro n hn
  obtain ⟨d, hmd, hdU, hmod, hdn⟩ := hn
  have hdpos : 0 < d := by omega
  have hdcop : d.Coprime m := by
    simpa [Nat.mul_comm] using Nat.coprime_of_mul_modEq_one 1
      (show d * 1 ≡ 1 [MOD m] by simpa using hmod)
  let a := Factorization.smallPart R d
  have hapos : 0 < a := Factorization.smallPart_pos hdpos
  have hadvd : a ∣ d := Factorization.smallPart_dvd hdpos
  have hadivn : a ∣ n := hadvd.trans hdn
  have haU : a ≤ U := (Nat.le_of_dvd hdpos hadvd).trans hdU
  have haParts : a ∈ Smooth.parts R U :=
    Smooth.mem_parts.mpr ⟨hapos, haU,
      Factorization.smallPart_smooth hdpos⟩
  by_cases hma : m ≤ a
  · let A : ↑(badParts R U m) := ⟨a, mem_badParts.mpr ⟨haParts, hma⟩⟩
    simp only [Set.mem_iUnion]
    refine ⟨Sum.inl (Sum.inl A), Finset.mem_univ _, ?_⟩
    simpa [indexedCoverSet, multiples] using hadivn
  have ham : a < m := by omega
  have hacop : a.Coprime m := Factorization.smallPart_coprime hdpos hdcop
  let A : ↑(goodParts R U m) :=
    ⟨a, mem_goodParts.mpr ⟨haParts, ham, hacop⟩⟩
  by_cases hsquare : ∃ p ∈ PrimeWindow.primes R U, p ^ 2 ∣ n
  · obtain ⟨p, hp, hp2⟩ := hsquare
    let Q : ↑(PrimeWindow.primes R U) := ⟨p, hp⟩
    simp only [Set.mem_iUnion]
    refine ⟨Sum.inl (Sum.inr Q), Finset.mem_univ _, ?_⟩
    simpa [indexedCoverSet, multiples] using hp2
  have hsqD : ∀ p ∈ PrimeWindow.primes R d, ¬p ^ 2 ∣ n := by
    intro p hp
    intro hp2
    exact hsquare ⟨p, PrimeWindow.mem_primes.mpr
      ⟨(PrimeWindow.mem_primes.mp hp).1,
        (PrimeWindow.mem_primes.mp hp).2.1.trans hdU,
        (PrimeWindow.mem_primes.mp hp).2.2⟩, hp2⟩
  let S := Factorization.roughPrimes R d
  have hSPRU : S ⊆ PrimeWindow.primes R U :=
    Factorization.roughPrimes_subset_window hdpos hdU
  have hdivS : ∀ p ∈ S, p ∣ n := fun p hp ↦
    Factorization.roughPrimes_dvd hdn hp
  have hsplit : a * (∏ p ∈ S, p) = d :=
    Factorization.smallPart_mul_prod_roughPrimes hdpos hdn hsqD
  have hSne : S.Nonempty := by
    by_contra hne
    have hzero : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hzero] at hsplit
    simp only [Finset.prod_empty, mul_one] at hsplit
    omega
  let SelMid := Cover.selected
    (fun p : ↑(PrimeWindow.primes R P) ↦ p.1) n
  let SelMark := Cover.selected
    (fun p : ↑(PrimeWindow.primes P U) ↦ p.1) n
  by_cases hmid : Kmid < SelMid.card
  · simp only [Set.mem_iUnion]
    refine ⟨Sum.inr (A, 0), Finset.mem_univ _, ?_⟩
    simpa [indexedCoverSet, highSet, Cover.eventSet, SelMid] using
      And.intro hadivn hmid
  have hmidcap : SelMid.card ≤ Kmid := by omega
  by_cases hmark : Kmark < SelMark.card
  · simp only [Set.mem_iUnion]
    refine ⟨Sum.inr (A, 1), Finset.mem_univ _, ?_⟩
    simpa [indexedCoverSet, highSet, Cover.eventSet, SelMark] using
      And.intro hadivn hmark
  have hmarkcap : SelMark.card ≤ Kmark := by omega
  by_cases hlarge : ∃ p ∈ S, P < p
  · let Q := coprimePrimes R U m
    have hSPQ : S ⊆ Q := by
      intro p hp
      have hpw := PrimeWindow.mem_primes.mp (hSPRU hp)
      exact mem_coprimePrimes.mpr
        ⟨hpw.1, hpw.2.1, hpw.2.2,
          hdcop.of_dvd_left ((Factorization.mem_roughPrimes hdpos.ne').mp hp).2.2⟩
    have hQcop : ∀ p ∈ Q, p.Coprime m := fun p hp ↦
      (mem_coprimePrimes.mp hp).2.2.2
    let J : Finset ↑Q := Finset.univ.filter fun p ↦ P < p.1
    have hmarked : ∃ p : ↑S, subtypeMapOfSubset hSPQ p ∈ J := by
      obtain ⟨p, hpS, hpP⟩ := hlarge
      refine ⟨⟨p, hpS⟩, ?_⟩
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
      change P < p
      exact hpP
    have hhits := lift_hitsUsing hSPQ hacop hQcop hsplit hmod
      hdivS hSne J hmarked
    have hcap :
        (Cover.selected (fun p : ↑Q ↦ p.1) n).card ≤ Kmid + Kmark := by
      exact (selected_coprime_card_le_split R P U m n).trans
        (Nat.add_le_add hmidcap hmarkcap)
    simp only [Set.mem_iUnion]
    refine ⟨Sum.inr (A, 3), Finset.mem_univ _, ?_⟩
    simpa [indexedCoverSet, markedHitSet, Cover.eventSet, Q, J,
      targetUnit, A] using And.intro hadivn (And.intro hcap hhits)
  · have hSPmid : S ⊆ coprimePrimes R P m := by
      intro p hp
      have hpdata := (Factorization.mem_roughPrimes hdpos.ne').mp hp
      have hpP : p ≤ P := by
        by_contra hnot
        exact hlarge ⟨p, hp, by omega⟩
      exact mem_coprimePrimes.mpr
        ⟨hpdata.1, hpP, hpdata.2.1,
          hdcop.of_dvd_left hpdata.2.2⟩
    let Q := coprimePrimes R P m
    have hQcop : ∀ p ∈ Q, p.Coprime m := fun p hp ↦
      (mem_coprimePrimes.mp hp).2.2.2
    have hhits := lift_hitsUsing hSPmid hacop hQcop hsplit hmod
      hdivS hSne (Finset.univ : Finset ↑Q)
      (by obtain ⟨p, hp⟩ := hSne
          exact ⟨⟨p, hp⟩, Finset.mem_univ _⟩)
    have hcopsub : Q ⊆ PrimeWindow.primes R P := by
      intro p hp
      exact (Finset.mem_filter.mp hp).1
    have hcap :
        (Cover.selected (fun p : ↑Q ↦ p.1) n).card ≤ Kmid :=
      (selected_card_mono hcopsub n).trans hmidcap
    simp only [Set.mem_iUnion]
    refine ⟨Sum.inr (A, 2), Finset.mem_univ _, ?_⟩
    simpa [indexedCoverSet, hitSet, Cover.eventSet, Q, targetUnit, A] using
      And.intro hadivn (And.intro hcap hhits)

theorem density_le_indexedCover
    {S₀ : Set ℕ} {s : ℝ} {R P U m Kmid Kmark : ℕ}
    (hS : S₀.HasDensity s) (hsub : S₀ ⊆ boundedDivisorSet m U)
    (hR : 1 ≤ R) (hRP : R ≤ P) (hmP : m ≤ P) :
    s ≤ ∑ i : CoverIndex R U m,
      indexedCoverDensity R P U m Kmid Kmark i := by
  classical
  have h := hasDensity_le_finset_iUnion hS
    (Finset.univ : Finset (CoverIndex R U m))
    (indexedCoverSet R P U m Kmid Kmark)
    (indexedCoverDensity R P U m Kmid Kmark)
    (fun i _ ↦ indexedCoverSet_hasDensity hRP hmP i)
    (hsub.trans (boundedDivisorSet_subset_cover hR hRP hmP))
  simpa using h

theorem sum_indexedCoverDensity
    (R P U m Kmid Kmark : ℕ) :
    (∑ i : CoverIndex R U m,
      indexedCoverDensity R P U m Kmid Kmark i) =
      (∑ a : ↑(badParts R U m), (1 : ℝ) / a.1) +
      (∑ p : ↑(PrimeWindow.primes R U), (1 : ℝ) / (p.1 : ℝ) ^ 2) +
      ∑ a : ↑(goodParts R U m), (1 / (a.1 : ℝ)) *
        (highProb R P Kmid + highProb P U Kmark +
          hitProb R P m {targetUnit a} Kmid +
          markedHitProb R P U m {targetUnit a}
            (Kmid + Kmark)) := by
  classical
  unfold CoverIndex
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fintype.sum_prod_type]
  simp only [indexedCoverDensity, Fin.sum_univ_four]
  simp only [Finset.univ_eq_attach, one_div, ↓reduceIte, Fin.isValue, one_ne_zero, Fin.reduceEq, add_right_inj]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-! ## Probability bounds for the indexed cover -/

theorem highProb_le_chernoff
    {L U K : ℕ} {r : ℝ} (hr : 1 < r)
    (hK : r * PrimeWindow.reciprocalMass L U ≤ (K + 1 : ℕ)) :
    highProb L U K ≤
      Real.exp
        (((-(r * ((r - 1) / (2 * r)))) +
          (1 / (1 - ((r - 1) / (2 * r))) - 1)) *
            PrimeWindow.reciprocalMass L U) := by
  classical
  let P := PrimeWindow.primes L U
  let p : ↑P → ℝ := fun q ↦ 1 / (q.1 : ℝ)
  have hp0 : ∀ q ∈ (Finset.univ : Finset ↑P), 0 ≤ p q := by
    intro q _
    positivity
  have hp1 : ∀ q ∈ (Finset.univ : Finset ↑P), p q ≤ 1 := by
    intro q _
    have hq : (1 : ℝ) ≤ q.1 := by
      exact_mod_cast (PrimeWindow.mem_primes.mp q.2).2.2.one_le
    dsimp [p]
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hq
  have hsum : PrimeWindow.reciprocalMass L U =
      ∑ q ∈ (Finset.univ : Finset ↑P), p q := by
    unfold PrimeWindow.reciprocalMass
    rw [show (Finset.univ : Finset ↑P) = P.attach by ext; simp]
    exact (Finset.sum_attach P (fun q ↦ 1 / (q : ℝ))).symm
  have h := Bernoulli.upper_tail_chernoff
    (Finset.univ : Finset ↑P) p hp0 hp1 hsum hr hK
  have huniv : (Finset.univ : Finset (Finset ↑P)) =
      (Finset.univ : Finset ↑P).powerset := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_powerset, true_iff]
    intro q _
    simpa using q.2
  unfold highProb
  rw [huniv]
  simpa [P, p] using h

theorem odds_one_div_eq {q : ℕ} (hq : 1 < q) :
    Bernoulli.odds (fun _ : Unit ↦ 1 / (q : ℝ)) () =
      1 / ((q : ℝ) - 1) := by
  unfold Bernoulli.odds
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_one.trans hq))
  field_simp [hq0]

/-- A marked unit fiber in the coprime coordinate window is exactly the
corresponding odds-weighted prime residue class. -/
theorem markedUnitFiber_eq_residue
    {L M U m : ℕ} (hm : 0 < m) (hLM : L ≤ M)
    (g : (ZMod m)ˣ) :
    (∑ q ∈ ((Finset.univ : Finset ↑(coprimePrimes L U m)).filter
          (fun q ↦ M < q.1)).filter
          (fun q ↦ ZMod.unitOfCoprime q.1
            (mem_coprimePrimes.mp q.2).2.2.2 = g),
      Bernoulli.odds (fun q : ↑(coprimePrimes L U m) ↦
        1 / (q.1 : ℝ)) q) =
      PrimeWindow.residueOddsMass M U m (g : ZMod m).val := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  let P := coprimePrimes L U m
  let E := ((Finset.univ : Finset ↑P).filter (fun q ↦ M < q.1)).filter
    (fun q ↦ ZMod.unitOfCoprime q.1
      (mem_coprimePrimes.mp q.2).2.2.2 = g)
  let Q := (PrimeWindow.primes M U).filter
    (fun q ↦ q % m = (g : ZMod m).val % m)
  have heq (q : ℕ) (hqcop : q.Coprime m) :
      ZMod.unitOfCoprime q hqcop = g ↔
        q % m = (g : ZMod m).val % m := by
    have hvalmod : (g : ZMod m).val % m = (g : ZMod m).val :=
      Nat.mod_eq_of_lt (ZMod.val_lt _)
    constructor
    · intro h
      have hc := congrArg (fun v : (ZMod m)ˣ ↦ (v : ZMod m)) h
      rw [ZMod.coe_unitOfCoprime] at hc
      have hv := congrArg ZMod.val hc
      simpa [hvalmod] using hv
    · intro h
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime]
      apply ZMod.val_injective
      simpa [hvalmod] using h
  unfold PrimeWindow.residueOddsMass
  change (∑ q ∈ E, Bernoulli.odds
      (fun q : ↑P ↦ 1 / (q.1 : ℝ)) q) = ∑ q ∈ Q, 1 / ((q : ℝ) - 1)
  apply Finset.sum_bij (fun q _ ↦ q.1)
  · intro q hq
    have hqe := Finset.mem_filter.mp hq
    have hqM := (Finset.mem_filter.mp hqe.1).2
    have hqdata := mem_coprimePrimes.mp q.2
    exact Finset.mem_filter.mpr
      ⟨PrimeWindow.mem_primes.mpr ⟨hqM, hqdata.2.1, hqdata.2.2.1⟩,
        (heq q.1 hqdata.2.2.2).mp hqe.2⟩
  · intro q₁ hq₁ q₂ hq₂ he
    exact Subtype.ext he
  · intro q hq
    have hqdata := Finset.mem_filter.mp hq
    have hqwin := PrimeWindow.mem_primes.mp hqdata.1
    have hcast : (q : ZMod m) = (g : ZMod m) := by
      apply ZMod.val_injective
      have hqval : (q : ZMod m).val = q % m := ZMod.val_natCast m q
      rw [hqval]
      simpa [Nat.mod_eq_of_lt (ZMod.val_lt (g : ZMod m))] using hqdata.2
    have hunit : IsUnit (q : ZMod m) := by
      rw [hcast]
      exact g.isUnit
    have hqcop : q.Coprime m := (ZMod.isUnit_iff_coprime q m).mp hunit
    have hqP : q ∈ P := mem_coprimePrimes.mpr
      ⟨lt_of_le_of_lt hLM hqwin.1, hqwin.2.1, hqwin.2.2, hqcop⟩
    let qP : ↑P := ⟨q, hqP⟩
    refine ⟨qP, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqwin.1⟩, ?_⟩
    exact (heq q hqcop).mpr hqdata.2
  · intro q hq
    have hqprime := (mem_coprimePrimes.mp q.2).2.2.1
    unfold Bernoulli.odds
    have hq0 : (q.1 : ℝ) ≠ 0 := by exact_mod_cast hqprime.ne_zero
    field_simp [hq0]

theorem hitProb_le_residueBound
    {L U m K : ℕ} (hm : 0 < m) (b : (ZMod m)ˣ)
    {M : ℝ} (hM0 : 0 ≤ M)
    (hres : ∀ g : (ZMod m)ˣ,
      PrimeWindow.residueOddsMass L U m (g : ZMod m).val ≤ M) :
    hitProb L U m {b} K ≤ (2 : ℝ) ^ K * M := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  let P := coprimePrimes L U m
  let p : ↑P → ℝ := fun q ↦ 1 / (q.1 : ℝ)
  let f : ↑P → (ZMod m)ˣ := fun q ↦
    ZMod.unitOfCoprime q.1 (mem_coprimePrimes.mp q.2).2.2.2
  have hp0 : ∀ q, 0 ≤ p q := by intro q; dsimp [p]; positivity
  have hp1 : ∀ q, p q < 1 := by
    intro q
    have hq : (1 : ℝ) < q.1 := by
      exact_mod_cast (mem_coprimePrimes.mp q.2).2.2.1.one_lt
    dsimp [p]
    exact (div_lt_one₀ (by positivity : (0 : ℝ) < q.1)).2 hq
  have hJ : (Finset.univ : Finset ↑P).filter (fun q ↦ L < q.1) =
      Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro q _
    exact (mem_coprimePrimes.mp q.2).1
  have hfiber (g : (ZMod m)ˣ) :
      (∑ q ∈ (Finset.univ : Finset ↑P).filter (fun q ↦ f q = g),
        Bernoulli.odds p q) ≤ M := by
    have heq := markedUnitFiber_eq_residue (L := L) (M := L)
      (U := U) hm le_rfl g
    rw [hJ] at heq
    calc
      _ = PrimeWindow.residueOddsMass L U m (g : ZMod m).val := heq
      _ ≤ M := hres g
  have h := MarkedSubset.sum_weight_event_le p f
    (Finset.univ : Finset ↑P) {b} hp0 hp1 hM0 hfiber K
  simpa [hitProb, P, p, f] using h

theorem markedHitProb_le_residueBound
    {L M U m K : ℕ} (hm : 0 < m) (hLM : L ≤ M)
    (b : (ZMod m)ˣ) {D : ℝ} (hD0 : 0 ≤ D)
    (hres : ∀ g : (ZMod m)ˣ,
      PrimeWindow.residueOddsMass M U m (g : ZMod m).val ≤ D) :
    markedHitProb L M U m {b} K ≤ (2 : ℝ) ^ K * D := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  let P := coprimePrimes L U m
  let p : ↑P → ℝ := fun q ↦ 1 / (q.1 : ℝ)
  let f : ↑P → (ZMod m)ˣ := fun q ↦
    ZMod.unitOfCoprime q.1 (mem_coprimePrimes.mp q.2).2.2.2
  let J : Finset ↑P := Finset.univ.filter fun q ↦ M < q.1
  have hp0 : ∀ q, 0 ≤ p q := by intro q; dsimp [p]; positivity
  have hp1 : ∀ q, p q < 1 := by
    intro q
    have hq : (1 : ℝ) < q.1 := by
      exact_mod_cast (mem_coprimePrimes.mp q.2).2.2.1.one_lt
    dsimp [p]
    exact (div_lt_one₀ (by positivity : (0 : ℝ) < q.1)).2 hq
  have hfiber (g : (ZMod m)ˣ) :
      (∑ q ∈ J.filter (fun q ↦ f q = g), Bernoulli.odds p q) ≤ D := by
    have heq := markedUnitFiber_eq_residue (L := L) (M := M)
      (U := U) hm hLM g
    calc
      _ = PrimeWindow.residueOddsMass M U m (g : ZMod m).val := heq
      _ ≤ D := hres g
  have h := MarkedSubset.sum_weight_event_le p f J {b}
    hp0 hp1 hD0 hfiber K
  simpa [markedHitProb, P, p, f, J] using h

theorem residueOddsMass_split {L M U q a : ℕ} (hLM : L ≤ M) (hMU : M ≤ U) :
    PrimeWindow.residueOddsMass L U q a =
      PrimeWindow.residueOddsMass L M q a +
        PrimeWindow.residueOddsMass M U q a := by
  classical
  unfold PrimeWindow.residueOddsMass
  have hsplit : PrimeWindow.primes L U =
      PrimeWindow.primes L M ∪ PrimeWindow.primes M U := by
    ext p
    simp only [PrimeWindow.mem_primes, Finset.mem_union]
    constructor
    · intro hp
      by_cases hpM : p ≤ M
      · exact Or.inl ⟨hp.1, hpM, hp.2.2⟩
      · exact Or.inr ⟨by omega, hp.2.1, hp.2.2⟩
    · rintro (hp | hp)
      · exact ⟨hp.1, hp.2.1.trans hMU, hp.2.2⟩
      · exact ⟨hLM.trans_lt hp.1, hp.2.1, hp.2.2⟩
  have hdisj : Disjoint (PrimeWindow.primes L M)
      (PrimeWindow.primes M U) := by
    apply Finset.disjoint_left.mpr
    intro p hpL hpU
    have hple := (PrimeWindow.mem_primes.mp hpL).2.1
    have hplt := (PrimeWindow.mem_primes.mp hpU).1
    omega
  have hdisjf : Disjoint
      ((PrimeWindow.primes L M).filter (fun p ↦ p % q = a % q))
      ((PrimeWindow.primes M U).filter (fun p ↦ p % q = a % q)) :=
    hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [hsplit, Finset.filter_union, Finset.sum_union hdisjf]

def upperTail (r x : ℝ) : ℝ :=
  Real.exp
    (((-(r * ((r - 1) / (2 * r)))) +
      (1 / (1 - ((r - 1) / (2 * r))) - 1)) * x)

theorem sum_subtype_eq {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (s : Finset α) (f : α → M) :
    (∑ x : ↑s, f x.1) = ∑ x ∈ s, f x := by
  classical
  change (∑ x ∈ (Finset.univ : Finset ↑s), f x.1) = _
  rw [show (Finset.univ : Finset ↑s) = s.attach by ext; simp]
  exact Finset.sum_attach s f

/-- The complete finite upper estimate.  All analytic choices have been
isolated into the two cardinal thresholds and two residue-fiber bounds. -/
theorem density_le_multiscale
    {S₀ : Set ℕ} {s : ℝ} {R P U m Kmid Kmark : ℕ}
    (hS : S₀.HasDensity s) (hsub : S₀ ⊆ boundedDivisorSet m U)
    (hm : 0 < m) (hR : 1 ≤ R) (hRP : R ≤ P) (hmP : m ≤ P)
    {rmid rmark Mmid Mmark : ℝ}
    (hrmid : 1 < rmid) (hrmark : 1 < rmark)
    (hKmid : rmid * PrimeWindow.reciprocalMass R P ≤ (Kmid + 1 : ℕ))
    (hKmark : rmark * PrimeWindow.reciprocalMass P U ≤ (Kmark + 1 : ℕ))
    (hMmid0 : 0 ≤ Mmid) (hMmark0 : 0 ≤ Mmark)
    (hMmid : ∀ g : (ZMod m)ˣ,
      PrimeWindow.residueOddsMass R P m (g : ZMod m).val ≤ Mmid)
    (hMmark : ∀ g : (ZMod m)ˣ,
      PrimeWindow.residueOddsMass P U m (g : ZMod m).val ≤ Mmark) :
    s ≤
      (Real.sqrt (m : ℝ))⁻¹ * Real.exp (5 * (R + 1 : ℕ)) +
      1 / (R : ℝ) +
      Real.exp (2 * PrimeHarmonic.sum R) *
        (upperTail rmid (PrimeWindow.reciprocalMass R P) +
          upperTail rmark (PrimeWindow.reciprocalMass P U) +
          (2 : ℝ) ^ Kmid * Mmid +
          (2 : ℝ) ^ (Kmid + Kmark) * Mmark) := by
  classical
  let B := upperTail rmid (PrimeWindow.reciprocalMass R P) +
    upperTail rmark (PrimeWindow.reciprocalMass P U) +
    (2 : ℝ) ^ Kmid * Mmid +
    (2 : ℝ) ^ (Kmid + Kmark) * Mmark
  have htailMid : highProb R P Kmid ≤
      upperTail rmid (PrimeWindow.reciprocalMass R P) := by
    exact highProb_le_chernoff hrmid hKmid
  have htailMark : highProb P U Kmark ≤
      upperTail rmark (PrimeWindow.reciprocalMass P U) := by
    exact highProb_le_chernoff hrmark hKmark
  have hhit (a : ↑(goodParts R U m)) :
      hitProb R P m {targetUnit a} Kmid ≤ (2 : ℝ) ^ Kmid * Mmid :=
    hitProb_le_residueBound hm (targetUnit a) hMmid0 hMmid
  have hmarked (a : ↑(goodParts R U m)) :
      markedHitProb R P U m {targetUnit a} (Kmid + Kmark) ≤
        (2 : ℝ) ^ (Kmid + Kmark) * Mmark :=
    markedHitProb_le_residueBound hm hRP (targetUnit a) hMmark0 hMmark
  have hB0 : 0 ≤ B := by
    dsimp [B, upperTail]
    positivity
  have hgoodRecip :
      (∑ a : ↑(goodParts R U m), (1 : ℝ) / a.1) ≤
        Real.exp (2 * PrimeHarmonic.sum R) := by
    rw [sum_subtype_eq (goodParts R U m) (fun a ↦ (1 : ℝ) / a)]
    calc
      (∑ a ∈ goodParts R U m, (1 : ℝ) / a) ≤
          ∑ a ∈ Smooth.parts R U, (1 : ℝ) / a := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro a ha
          exact (mem_goodParts.mp ha).1
        · intro a _ _
          positivity
      _ ≤ Real.exp (2 * PrimeHarmonic.sum R) :=
        Smooth.sum_parts_reciprocal_le_exp R U
  have hgood :
      (∑ a : ↑(goodParts R U m), (1 / (a.1 : ℝ)) *
        (highProb R P Kmid + highProb P U Kmark +
          hitProb R P m {targetUnit a} Kmid +
          markedHitProb R P U m {targetUnit a} (Kmid + Kmark))) ≤
        Real.exp (2 * PrimeHarmonic.sum R) * B := by
    calc
      _ ≤ ∑ a : ↑(goodParts R U m), (1 / (a.1 : ℝ)) * B := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [B]
        linarith [htailMid, htailMark, hhit a, hmarked a]
      _ = (∑ a : ↑(goodParts R U m), (1 / (a.1 : ℝ))) * B := by
        rw [Finset.sum_mul]
      _ ≤ Real.exp (2 * PrimeHarmonic.sum R) * B :=
        mul_le_mul_of_nonneg_right hgoodRecip hB0
  have hbad :
      (∑ a : ↑(badParts R U m), (1 : ℝ) / a.1) ≤
        (Real.sqrt (m : ℝ))⁻¹ * Real.exp (5 * (R + 1 : ℕ)) := by
    rw [sum_subtype_eq (badParts R U m) (fun a ↦ (1 : ℝ) / a)]
    simpa [badParts] using Smooth.sum_parts_reciprocal_ge_le R U m hm
  have hsquare :
      (∑ p : ↑(PrimeWindow.primes R U), (1 : ℝ) / (p.1 : ℝ) ^ 2) ≤
        1 / (R : ℝ) := by
    rw [sum_subtype_eq (PrimeWindow.primes R U)
      (fun p ↦ (1 : ℝ) / (p : ℝ) ^ 2)]
    exact PrimeWindow.squareReciprocalMass_le hR
  have hcover := density_le_indexedCover (Kmid := Kmid) (Kmark := Kmark)
    hS hsub hR hRP hmP
  rw [sum_indexedCoverDensity] at hcover
  calc
    s ≤ (∑ a : ↑(badParts R U m), (1 : ℝ) / a.1) +
        (∑ p : ↑(PrimeWindow.primes R U), (1 : ℝ) / (p.1 : ℝ) ^ 2) +
        ∑ a : ↑(goodParts R U m), (1 / (a.1 : ℝ)) *
          (highProb R P Kmid + highProb P U Kmark +
            hitProb R P m {targetUnit a} Kmid +
            markedHitProb R P U m {targetUnit a} (Kmid + Kmark)) := hcover
    _ ≤ (Real.sqrt (m : ℝ))⁻¹ * Real.exp (5 * (R + 1 : ℕ)) +
        1 / (R : ℝ) + Real.exp (2 * PrimeHarmonic.sum R) * B := by
      gcongr
    _ = _ := rfl

end

end Erdos697.UpperBound
