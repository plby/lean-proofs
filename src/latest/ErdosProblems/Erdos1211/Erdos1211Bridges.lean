import ErdosProblems.Erdos1211.Erdos1211Finite

namespace Erdos344

open BigOperators Set
open scoped Pointwise

attribute [local instance] Classical.propDecidable

/-- If the current remainder generates the full cyclic group, every normalized
coset fiber of a seeded subset-sum set contains an injective translate of the
seed. -/
lemma seed_card_le_normalizedCosetFiber_of_closureModulus_eq_one
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R E A : Finset (ZMod b)) (u : ZMod b)
    (hmod : closureModulus hb R = 1) :
    E.card ≤
      (normalizedCosetFiber (AddSubgroup.closure (R : Set (ZMod b)))
        (E + A.subsetSum) u).card := by
  classical
  let H := AddSubgroup.closure (R : Set (ZMod b))
  letI : Fintype H :=
    Fintype.ofInjective (fun h : H ↦ h.1) Subtype.val_injective
  let f : ZMod b → H := fun e ↦
    ⟨e - u, (mem_closure_iff_modulus_dvd_val hb R (e - u)).2 (by
      rw [hmod]
      exact one_dvd _)⟩
  apply Finset.card_le_card_of_injOn f
  · intro e he
    rw [Finset.mem_coe, mem_normalizedCosetFiber]
    rw [Finset.mem_add]
    refine ⟨e, he, 0, Finset.zero_mem_subsetSum, ?_⟩
    dsimp [f]
    abel
  · intro x _ y _ hxy
    have hval := congrArg Subtype.val hxy
    dsimp [f] at hval
    exact sub_left_injective hval

/-- A generic size criterion forcing full cyclic closure.  It cleanly
separates the roughness input (`every nontrivial possible closure modulus is
at least D`) from the counting input (`R` is too large for such a modulus). -/
lemma closureModulus_eq_one_of_nontrivial_ge_of_mul_card_gt
    {b : ℕ} [NeZero b] (hb : 0 < b) (R : Finset (ZMod b)) (D : ℕ)
    (hgap : 1 < closureModulus hb R → D ≤ closureModulus hb R)
    (hlarge : b < D * R.card) :
    closureModulus hb R = 1 := by
  have hqpos : 0 < closureModulus hb R := closureModulus_pos hb R
  by_contra hqne
  have hqgt : 1 < closureModulus hb R := by omega
  have hmul := closureModulus_mul_card_le hb R
  have hD := hgap hqgt
  nlinarith

/-- A modular phase set with an arbitrary natural seed lifts to ordinary
natural sums consisting of one seed element plus at most `k` pool elements. -/
lemma modularPhaseSums_subset_seeded_bounded_image
    {b : ℕ} [NeZero b] (hb : 0 < b) (D C : Finset ℕ)
    (hinj : Set.InjOn (fun c : ℕ ↦ (c : ZMod b)) C)
    (R₀ E : Finset (ZMod b))
    (hR₀ : R₀ = C.image fun c : ℕ ↦ (c : ZMod b))
    (hEimage : E = D.image fun d : ℕ ↦ (d : ZMod b))
    (hE : E.Nonempty) (hdiverse : PhaseDiverse hb R₀)
    {k : ℕ} (hk : k ≤ R₀.card) :
    modularPhaseSums hb R₀ E hE hdiverse k ⊆
      (D + boundedSubsetSum C k).image fun u : ℕ ↦ (u : ZMod b) := by
  classical
  intro z hz
  rw [modularPhaseSums, Finset.mem_add] at hz
  obtain ⟨e, he, v, hv, hzEq⟩ := hz
  have heImage : e ∈ D.image fun d : ℕ ↦ (d : ZMod b) := by
    simpa only [← hEimage] using he
  obtain ⟨d, hdD, hde⟩ := Finset.mem_image.mp heImage
  rw [Finset.mem_subsetSum_iff] at hv
  obtain ⟨G, hGused, hGsum⟩ := hv
  have hGR₀ : G ⊆ R₀ := hGused.trans Finset.sdiff_subset
  obtain ⟨H, hHC, hHcard, hHimage⟩ :=
    exists_preimage_finset_of_subset_image C
      (fun c : ℕ ↦ (c : ZMod b)) hinj G (by simpa [hR₀] using hGR₀)
  have husedCard :
      (R₀ \ modularRemainder hb R₀ E hE hdiverse k).card = k :=
    card_used_modularRemainder hb R₀ E hE hdiverse hk
  have hHk : H.card ≤ k := by
    rw [hHcard, ← husedCard]
    exact Finset.card_le_card hGused
  let s := ∑ h ∈ H, h
  have hsBounded : s ∈ boundedSubsetSum C k :=
    mem_boundedSubsetSum_iff.mpr ⟨H, hHC, hHk, rfl⟩
  apply Finset.mem_image.mpr
  refine ⟨d + s, Finset.add_mem_add hdD hsBounded, ?_⟩
  rw [← hzEq, ← hGsum, ← hHimage]
  simp only [s]
  rw [Finset.sum_image (hinj.mono hHC)]
  push_cast
  rw [hde]

/-- Full closure plus a seed larger than a quarter of the remainder rules out
the internal modular-growth branch. -/
lemma not_isModularGrowthPhase_of_full_closure_seed
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ R E : Finset (ZMod b))
    (hmod : closureModulus hb R = 1)
    (hseed : R.card < 4 * E.card) :
    ¬ IsModularGrowthPhase hb R₀ R E := by
  intro hgrowth
  obtain ⟨u, hu⟩ := hgrowth
  have hlower :=
    seed_card_le_normalizedCosetFiber_of_closureModulus_eq_one
      hb R E (R₀ \ R) u hmod
  omega

/-- Zero-growth specialization of the phase dichotomy.  If all of the first
`k` large remainders generate the full cyclic group and the seed is larger
than a quarter of the initial pool, the potential alternative itself forces
quarter-coverage of the modulus. -/
lemma modularPhaseSums_quarter_of_full_closure_seed
    {b : ℕ} [NeZero b] (hb : 0 < b)
    (R₀ E : Finset (ZMod b)) (hE : E.Nonempty)
    (hdiverse : PhaseDiverse hb R₀) {k : ℕ}
    (hhalf : 2 * k ≤ R₀.card)
    (hclosure : ∀ i < k,
      closureModulus hb (modularRemainder hb R₀ E hE hdiverse i) = 1)
    (hseed : R₀.card < 4 * E.card)
    (hmass : 4 * b ≤ k * (R₀.card - k)) :
    b ≤ 4 * (modularPhaseSums hb R₀ E hE hdiverse k).card := by
  have hnogrowth : ∀ i < k, ¬ IsModularGrowthPhase hb R₀
      (modularRemainder hb R₀ E hE hdiverse i) E := by
    intro i hi
    apply not_isModularGrowthPhase_of_full_closure_seed hb R₀ _ E
      (hclosure i hi)
    have hrem :
        (modularRemainder hb R₀ E hE hdiverse i).card ≤ R₀.card :=
      Finset.card_le_card
        (modularRemainder_subset_initial hb R₀ E hE hdiverse i)
    omega
  have hGempty : modularGrowthIndices hb R₀ E hE hdiverse k = ∅ := by
    ext i
    constructor
    · intro hi
      rw [modularGrowthIndices, Finset.mem_filter] at hi
      exact (hnogrowth i (Finset.mem_range.mp hi.1) hi.2).elim
    · simp
  rcases modularPhase_dichotomy hb R₀ E hE hdiverse hhalf with hfill | hpot
  · exact hfill
  · rw [hGempty] at hpot
    simp only [Finset.card_empty, Nat.sub_zero] at hpot
    omega

/-- Combined zero-growth/lifting bridge in the exact form consumed by
`card_pivotExtended_lower`: the seeded bounded natural sums occupy at least
one quarter of the residue classes modulo `b`. -/
lemma seededBoundedSubsetSum_quarter_modulus_of_full_closure_seed
    {b : ℕ} [NeZero b] (hb : 0 < b) (D C : Finset ℕ)
    (hinj : Set.InjOn (fun c : ℕ ↦ (c : ZMod b)) C)
    (R₀ E : Finset (ZMod b))
    (hR₀ : R₀ = C.image fun c : ℕ ↦ (c : ZMod b))
    (hEimage : E = D.image fun d : ℕ ↦ (d : ZMod b))
    (hE : E.Nonempty) (hdiverse : PhaseDiverse hb R₀) {k : ℕ}
    (hhalf : 2 * k ≤ R₀.card)
    (hclosure : ∀ i < k,
      closureModulus hb (modularRemainder hb R₀ E hE hdiverse i) = 1)
    (hseed : R₀.card < 4 * E.card)
    (hmass : 4 * b ≤ k * (R₀.card - k)) :
    b ≤ 4 * ((D + boundedSubsetSum C k).image
      (fun u : ℕ ↦ (u : ZMod b))).card := by
  have hquarter := modularPhaseSums_quarter_of_full_closure_seed
    hb R₀ E hE hdiverse hhalf hclosure hseed hmass
  have hk : k ≤ R₀.card := by omega
  have hlift := modularPhaseSums_subset_seeded_bounded_image
    hb D C hinj R₀ E hR₀ hEimage hE hdiverse hk
  exact hquarter.trans
    (Nat.mul_le_mul_left 4 (Finset.card_le_card hlift))

/-- `n` has no prime divisor at most `Q`. -/
def RoughUpTo (Q n : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → q ≤ Q → ¬ q ∣ n

/-- Reduction modulo `b` is injective on any natural interval of width `b`.
This is the shell form useful when the elements themselves are much larger
than the modulus. -/
lemma natCast_zmod_injOn_of_subset_Ico_width
    {b N : ℕ} [NeZero b] {C : Finset ℕ}
    (hC : C ⊆ Finset.Ico N (N + b)) :
    Set.InjOn (fun c : ℕ ↦ (c : ZMod b)) C := by
  intro x hx y hy hxy
  have hxI := Finset.mem_Ico.mp (hC hx)
  have hyI := Finset.mem_Ico.mp (hC hy)
  have hmod : x ≡ y [MOD b] :=
    (ZMod.natCast_eq_natCast_iff x y b).mp hxy
  apply hmod.eq_of_abs_lt
  rw [abs_lt]
  constructor <;> omega

/-- A large subset of the modular image of a `Q`-rough set generates the
whole cyclic group.  No small-representative hypothesis is needed: the
closure modulus divides both `b` and `c % b`, hence also the original `c`. -/
lemma closureModulus_eq_one_of_rough_image
    {b Q : ℕ} [NeZero b] (hb : 0 < b) {C : Finset ℕ}
    (hrough : ∀ c ∈ C, RoughUpTo Q c)
    (R : Finset (ZMod b))
    (hRsub : R ⊆ C.image fun c : ℕ ↦ (c : ZMod b))
    (hlarge : b < (Q + 1) * R.card) :
    closureModulus hb R = 1 := by
  apply closureModulus_eq_one_of_nontrivial_ge_of_mul_card_gt
    hb R (Q + 1) ?_ hlarge
  intro hq
  have hRpos : 0 < R.card := by
    by_contra hnot
    have hzero : R.card = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hlarge
    simp at hlarge
  obtain ⟨r, hr⟩ := Finset.card_pos.mp hRpos
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp (hRsub hr)
  let q := closureModulus hb R
  have hqdivVal : q ∣ ((c : ZMod b).val) := by
    exact (closureModulus_spec hb R).2.2.1 _
      (AddSubgroup.subset_closure hr)
  have hqdivMod : q ∣ c % b := by
    simpa [q, ZMod.val_natCast] using hqdivVal
  have hqdivB : q ∣ b := by
    simpa [q] using closureModulus_dvd hb R
  have hqdivC : q ∣ c := by
    rw [← Nat.mod_add_div c b]
    exact Nat.dvd_add hqdivMod (dvd_mul_of_dvd_left hqdivB _)
  have hqgtQ : Q < q := by
    by_contra hnot
    have hqQ : q ≤ Q := Nat.le_of_not_gt hnot
    obtain ⟨p, hpprime, hpq⟩ :=
      Nat.ne_one_iff_exists_prime_dvd.mp (by simpa [q] using hq.ne')
    have hpqle : p ≤ q := Nat.le_of_dvd (by omega) hpq
    exact hrough c hc p hpprime (hpqle.trans hqQ) (hpq.trans hqdivC)
  simpa [q] using Nat.succ_le_iff.mpr hqgtQ

private noncomputable def roughDivideMultiples
    (Y : Finset ℕ) (e : ℕ) : Finset ℕ :=
  (Y.filter fun y ↦ e ∣ y).image fun y ↦ y / e

private lemma mem_roughDivideMultiples_iff
    {Y : Finset ℕ} {e y : ℕ} (he : 0 < e) :
    y ∈ roughDivideMultiples Y e ↔ e * y ∈ Y := by
  classical
  rw [roughDivideMultiples, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Finset.mem_filter] at hx
    simpa [Nat.mul_div_cancel' hx.2] using hx.1
  · intro hy
    refine ⟨e * y, Finset.mem_filter.mpr ⟨hy, dvd_mul_right e y⟩, ?_⟩
    exact Nat.mul_div_right y he

private lemma card_roughDivideMultiples
    {Y : Finset ℕ} {e : ℕ} (he : 0 < e) :
    (roughDivideMultiples Y e).card =
      (Y.filter fun y ↦ e ∣ y).card := by
  classical
  rw [roughDivideMultiples, Finset.card_image_iff]
  intro x hx y hy hxy
  have hx' : x ∈ Y ∧ e ∣ x := Finset.mem_filter.mp hx
  have hy' : y ∈ Y ∧ e ∣ y := Finset.mem_filter.mp hy
  have hxmul : e * (x / e) = x := by
    simpa [mul_comm] using Nat.mul_div_cancel' hx'.2
  have hymul : e * (y / e) = y := by
    simpa [mul_comm] using Nat.mul_div_cancel' hy'.2
  change x / e = y / e at hxy
  rw [← hxmul, ← hymul]
  exact congrArg (fun z ↦ e * z) hxy

private lemma roughDivideMultiples_subset_Icc
    {Y : Finset ℕ} {e n : ℕ} (he : 0 < e)
    (hY : Y ⊆ Finset.Icc 1 n) :
    roughDivideMultiples Y e ⊆ Finset.Icc 1 (n / e) := by
  intro y hy
  rw [mem_roughDivideMultiples_iff he] at hy
  have hmem := Finset.mem_Icc.mp (hY hy)
  rw [Finset.mem_Icc]
  constructor
  · by_contra h
    have : y = 0 := Nat.eq_zero_of_not_pos h
    subst y
    simp at hmem
  · exact (Nat.le_div_iff_mul_le he).2
      (by simpa [mul_comm] using hmem.2)

lemma subset_boundedSubsetSum_of_pos {C : Finset ℕ} {s : ℕ}
    (hs : 0 < s) : C ⊆ boundedSubsetSum C s := by
  intro c hc
  rw [mem_boundedSubsetSum_iff]
  refine ⟨{c}, by simpa, by simp; omega, by simp⟩

/-- Fixed-shell aperiodicity.  A linearly large block of `Q`-rough integers
in `[N,2N)` cannot all occupy one nontrivial residue class; since every
singleton from the block occurs in the bounded-sum part, neither can the
pivot-extended leaf. -/
lemma pivotExtended_notContained_of_rough
    {Q N s : ℕ} {C P : Finset ℕ} (hN : 0 < N)
    (hC : C ⊆ Finset.Ico N (2 * N))
    (hrough : ∀ c ∈ C, RoughUpTo Q c)
    (hlarge : 2 * N ≤ Q * C.card) (hs : 0 < s) :
    ¬ Erdos360.ContainedInNontrivialAP
      (pivotExtended (boundedSubsetSum C s) P) := by
  classical
  rintro ⟨d, a, hd, hclass⟩
  have hzero : 0 ∈ pivotExtended (boundedSubsetSum C s) P :=
    zero_mem_pivotExtended (zero_mem_boundedSubsetSum C s)
  have hzeroClass : 0 = a % d := by
    simpa using hclass 0 hzero
  have hCleaf : C ⊆ pivotExtended (boundedSubsetSum C s) P :=
    (subset_boundedSubsetSum_of_pos hs).trans
      (subset_pivotExtended_left (boundedSubsetSum C s) P)
  have hdvdC : ∀ c ∈ C, d ∣ c := by
    intro c hc
    apply Nat.dvd_of_mod_eq_zero
    calc
      c % d = a % d := hclass c (hCleaf hc)
      _ = 0 := hzeroClass.symm
  have hCpos : 0 < C.card := by
    by_contra hnot
    have : C.card = 0 := Nat.eq_zero_of_not_pos hnot
    rw [this] at hlarge
    omega
  have hCIcc : C ⊆ Finset.Icc 1 (2 * N - 1) := by
    intro c hc
    have hc' := Finset.mem_Ico.mp (hC hc)
    rw [Finset.mem_Icc]
    omega
  have hfilter : C.filter (fun c ↦ d ∣ c) = C := by
    ext c
    simp only [Finset.mem_filter]
    constructor
    · exact fun hc ↦ hc.1
    · exact fun hc ↦ ⟨hc, hdvdC c hc⟩
  have hdivSub := roughDivideMultiples_subset_Icc (Y := C) (e := d)
    (n := 2 * N - 1) (by omega) hCIcc
  have hcardDiv := Finset.card_le_card hdivSub
  have hcardLe : C.card ≤ (2 * N - 1) / d := by
    rw [card_roughDivideMultiples (Y := C) (e := d) (by omega), hfilter]
      at hcardDiv
    simpa using hcardDiv
  have hmul : d * C.card ≤ 2 * N - 1 := by
    calc
      d * C.card ≤ d * ((2 * N - 1) / d) :=
        Nat.mul_le_mul_left d hcardLe
      _ ≤ 2 * N - 1 := by
        simpa [mul_comm] using Nat.mul_div_le (2 * N - 1) d
  have hdQ : d < Q := by
    by_contra hnot
    have hQd : Q ≤ d := Nat.le_of_not_gt hnot
    have hbad : 2 * N ≤ 2 * N - 1 :=
      hlarge.trans ((Nat.mul_le_mul_right C.card hQd).trans hmul)
    omega
  obtain ⟨q, hqprime, hqd⟩ :=
    Nat.ne_one_iff_exists_prime_dvd.mp (by omega : d ≠ 1)
  have hqQ : q ≤ Q := by
    have hqdle : q ≤ d := Nat.le_of_dvd (by omega) hqd
    omega
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hCpos
  exact hrough c hc q hqprime hqQ (hqd.trans (hdvdC c hc))

/-- A finite natural set is primitive for the sum-tree argument when no
nontrivial modulus puts it in one residue class. -/
def SumTreePrimitive (S : Finset ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → Erdos13Additive.InOneResidue S d → d = 1

lemma sumTreePrimitive_of_zero_mem_gcd_eq_one {S : Finset ℕ}
    (hzero : 0 ∈ S) (hgcd : S.gcd id = 1) : SumTreePrimitive S := by
  intro d hd hres
  obtain ⟨r, hr⟩ := hres
  have hrzero : (0 : ZMod d) = r := by simpa using hr 0 hzero
  have hdvd : d ∣ S.gcd id := by
    rw [Finset.dvd_gcd_iff]
    intro x hx
    apply (ZMod.natCast_eq_zero_iff x d).mp
    rw [hr x hx, ← hrzero]
  rw [hgcd] at hdvd
  exact Nat.dvd_one.mp hdvd

lemma subset_pivotExtended_right {S P : Finset ℕ} (hzero : 0 ∈ S) :
    P ⊆ pivotExtended S P := by
  intro p hp
  have hpSum : p ∈ P.subsetSum := by
    rw [Finset.mem_subsetSum_iff]
    exact ⟨{p}, by simpa, by simp⟩
  simpa [pivotExtended] using Finset.add_mem_add hzero hpSum

/-- A pivot-extended leaf is primitive as soon as its pivot set has gcd one;
the bounded-sum part only needs to contain zero. -/
lemma sumTreePrimitive_pivotExtended {S P : Finset ℕ}
    (hzero : 0 ∈ S) (hgcd : P.gcd id = 1) :
    SumTreePrimitive (pivotExtended S P) := by
  have hPsub : P ⊆ pivotExtended S P := subset_pivotExtended_right hzero
  have hgdvd : (pivotExtended S P).gcd id ∣ P.gcd id :=
    Finset.gcd_mono hPsub
  rw [hgcd] at hgdvd
  apply sumTreePrimitive_of_zero_mem_gcd_eq_one
    (zero_mem_pivotExtended hzero)
  exact Nat.dvd_one.mp hgdvd

lemma sumTreePrimitive_add_left {S T : Finset ℕ}
    (hzero : 0 ∈ T) (hS : SumTreePrimitive S) :
    SumTreePrimitive (S + T) := by
  intro d hd hres
  apply hS d hd
  obtain ⟨r, hr⟩ := hres
  refine ⟨r, ?_⟩
  intro x hx
  exact hr x (Finset.add_mem_add hx hzero)

lemma sumTreePrimitive_carrier {t : ℕ} {T : SumTree t}
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S)
    (hprimitive : T.AllLeaves SumTreePrimitive) :
    SumTreePrimitive T.carrier := by
  induction T with
  | leaf S => exact hprimitive
  | node left right ihl ihr =>
      apply sumTreePrimitive_add_left (SumTree.zero_mem_carrier hzero.2)
      exact ihl hzero.1 hprimitive.1

/-- Interval-valued version of the sum-tree alternative.  Primitivity of
every leaf forces the progression difference in the Bardaji--Grynkiewicz
branch to equal one. -/
lemma SumTree.containsIcc_or_card_growth
    {t k : ℕ} {T : SumTree t} (hk : 2 ≤ k)
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S)
    (hcard : T.AllLeaves fun S ↦ k ≤ S.card)
    (hprimitive : T.AllLeaves SumTreePrimitive) :
    (∃ a : ℕ, Finset.Icc a (a + (2 * k - 2)) ⊆ T.carrier) ∨
      SumTree.growthLower k t ≤ T.carrier.card := by
  induction T with
  | leaf S =>
      right
      simpa [SumTree.carrier, SumTree.AllLeaves, SumTree.growthLower] using hcard
  | @node t left right ihl ihr =>
      rcases ihl hzero.1 hcard.1 hprimitive.1 with hI | hleft
      · left
        obtain ⟨a, ha⟩ := hI
        refine ⟨a, fun x hx ↦ ?_⟩
        exact Finset.add_mem_add (ha hx) (SumTree.zero_mem_carrier hzero.2)
      rcases ihr hzero.2 hcard.2 hprimitive.2 with hI | hright
      · left
        obtain ⟨a, ha⟩ := hI
        refine ⟨a, fun x hx ↦ ?_⟩
        simpa [SumTree.carrier] using
          Finset.add_mem_add (SumTree.zero_mem_carrier hzero.1) (ha hx)
      have hleftne : left.carrier.Nonempty :=
        ⟨0, SumTree.zero_mem_carrier hzero.1⟩
      have hrightne : right.carrier.Nonempty :=
        ⟨0, SumTree.zero_mem_carrier hzero.2⟩
      rcases Erdos13Additive.growth_or_long_AP hleftne hrightne with hgrow | hprog
      · right
        rw [SumTree.growthLower]
        have hmin : SumTree.growthLower k t ≤
            min left.carrier.card right.carrier.card := le_min hleft hright
        have hsum : 3 * SumTree.growthLower k t ≤
            left.carrier.card + right.carrier.card +
              min left.carrier.card right.carrier.card := by omega
        change 3 * SumTree.growthLower k t - 3 ≤
          (left.carrier + right.carrier).card
        omega
      · left
        obtain ⟨a, d, hd, hAP, hres⟩ := hprog
        have hprim : SumTreePrimitive (left.carrier + right.carrier) :=
          sumTreePrimitive_carrier hzero hprimitive
        have hd1 : d = 1 := hprim d hd hres
        subst d
        refine ⟨a, ?_⟩
        intro x hx
        obtain ⟨j, hjlt, hjeq⟩ : ∃ j < 2 * k - 1, a + j = x := by
          refine ⟨x - a, ?_, ?_⟩
          · have hxI := Finset.mem_Icc.mp hx
            omega
          · have hxI := Finset.mem_Icc.mp hx
            omega
        have hkleft : k ≤ left.carrier.card :=
          (SumTree.growthLower_ge hk t).trans hleft
        have hkright : k ≤ right.carrier.card :=
          (SumTree.growthLower_ge hk t).trans hright
        have hjroot : j < left.carrier.card + right.carrier.card - 1 := by
          omega
        apply hAP
        rw [Erdos13Additive.mem_natAP]
        exact ⟨j, hjroot, by simpa [Nat.one_mul] using hjeq⟩

/-- Quantitative interval wrapper: once perpetual growth exceeds the ambient
diameter, the carrier contains an ordinary interval of length `2*k-1`. -/
theorem SumTree.Icc_subset_carrier_of_growth_exceeds_diameter
    {t k m : ℕ} {T : SumTree t} (hk : 2 ≤ k)
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S)
    (hcard : T.AllLeaves fun S ↦ k ≤ S.card)
    (hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m)
    (hprimitive : T.AllLeaves SumTreePrimitive)
    (hexceed : 2 ^ t * m + 1 < SumTree.growthLower k t) :
    ∃ a : ℕ, Finset.Icc a (a + (2 * k - 2)) ⊆ T.carrier := by
  rcases SumTree.containsIcc_or_card_growth hk hzero hcard hprimitive with hI | hgrowth
  · exact hI
  · have hupp := SumTree.card_carrier_le hbox
    omega

/-- If every leaf is aperiodic and every leaf contains zero, then the whole
iterated sum is aperiodic.  Indeed each parent contains its right child. -/
lemma SumTree.notContained_carrier
    {t : ℕ} {T : SumTree t}
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S)
    (haper : T.AllLeaves fun S ↦
      ¬ Erdos360.ContainedInNontrivialAP S) :
    ¬ Erdos360.ContainedInNontrivialAP T.carrier := by
  induction T with
  | leaf S => exact haper
  | node left right ihl ihr =>
      intro hroot
      apply ihr hzero.2 haper.2
      obtain ⟨d, a, hd, hclass⟩ := hroot
      refine ⟨d, a, hd, ?_⟩
      intro x hx
      apply hclass x
      simpa [SumTree.carrier] using
        Finset.add_mem_add (SumTree.zero_mem_carrier hzero.1) hx

/-- Aperiodic interval-valued sum-tree alternative.  This is the form needed
for a fixed rough shell: `Erdos360` converts the local structured branch into
an ordinary interval because the right subtree cannot lie in a nontrivial
residue class. -/
lemma SumTree.containsInterval_or_card_growth
    {t K : ℕ} {T : SumTree t} (hK : 2 ≤ K)
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S)
    (hcard : T.AllLeaves fun S ↦ K ≤ S.card)
    (haper : T.AllLeaves fun S ↦
      ¬ Erdos360.ContainedInNontrivialAP S) :
    (∃ a : ℕ, Finset.Icc a (a + (2 * K - 2)) ⊆ T.carrier) ∨
      SumTree.growthLower K t ≤ T.carrier.card := by
  induction T with
  | leaf S =>
      right
      simpa [SumTree.carrier, SumTree.AllLeaves, SumTree.growthLower] using hcard
  | @node t left right ihl ihr =>
      rcases ihl hzero.1 hcard.1 haper.1 with hI | hleft
      · left
        obtain ⟨a, ha⟩ := hI
        refine ⟨a, fun x hx ↦ ?_⟩
        exact Finset.add_mem_add (ha hx) (SumTree.zero_mem_carrier hzero.2)
      rcases ihr hzero.2 hcard.2 haper.2 with hI | hright
      · left
        obtain ⟨a, ha⟩ := hI
        refine ⟨a, fun x hx ↦ ?_⟩
        simpa [SumTree.carrier] using
          Finset.add_mem_add (SumTree.zero_mem_carrier hzero.1) (ha hx)
      have hleftne : left.carrier.Nonempty :=
        ⟨0, SumTree.zero_mem_carrier hzero.1⟩
      have hrightne : right.carrier.Nonempty :=
        ⟨0, SumTree.zero_mem_carrier hzero.2⟩
      have hrightaper :
          ¬ Erdos360.ContainedInNontrivialAP right.carrier :=
        SumTree.notContained_carrier hzero.2 haper.2
      rcases Erdos360.growth_or_interval_of_notContainedInNontrivialAP_right
          hleftne hrightne hrightaper with hgrow | hinterval
      · right
        rw [SumTree.growthLower]
        have hmin : SumTree.growthLower K t ≤
            min left.carrier.card right.carrier.card := le_min hleft hright
        have hsum : 3 * SumTree.growthLower K t ≤
            left.carrier.card + right.carrier.card +
              min left.carrier.card right.carrier.card := by omega
        change 3 * SumTree.growthLower K t - 3 ≤
          (left.carrier + right.carrier).card
        omega
      · left
        obtain ⟨a, ha⟩ := hinterval
        refine ⟨a, ?_⟩
        intro x hx
        apply ha
        rw [Finset.mem_Icc] at hx ⊢
        have hkleft : K ≤ left.carrier.card :=
          (SumTree.growthLower_ge hK t).trans hleft
        have hkright : K ≤ right.carrier.card :=
          (SumTree.growthLower_ge hK t).trans hright
        omega

/-- Quantitative aperiodic interval wrapper. -/
theorem SumTree.containsInterval_of_growth_exceeds_diameter
    {t K m : ℕ} {T : SumTree t} (hK : 2 ≤ K)
    (hzero : T.AllLeaves fun S ↦ 0 ∈ S)
    (hcard : T.AllLeaves fun S ↦ K ≤ S.card)
    (haper : T.AllLeaves fun S ↦
      ¬ Erdos360.ContainedInNontrivialAP S)
    (hbox : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m)
    (hexceed : 2 ^ t * m + 1 < SumTree.growthLower K t) :
    ∃ a : ℕ, Finset.Icc a (a + (2 * K - 2)) ⊆ T.carrier := by
  rcases SumTree.containsInterval_or_card_growth hK hzero hcard haper with
    hI | hgrowth
  · exact hI
  · have hupp := SumTree.card_carrier_le hbox
    omega

namespace PartitionTree

variable {iota : Type*} [DecidableEq iota]

lemma allLeaves_true {t : ℕ} (T : PartitionTree iota t) :
    T.AllLeaves fun _ ↦ True := by
  induction T with
  | leaf S => trivial
  | node left right ihl ihr => exact ⟨ihl, ihr⟩

/-- End-to-end wrapper for the balanced paired-pivot tree.  Leaf cardinality
and diameter estimates are left abstract, while gcd-one pivot leaves force
the long progression branch to be an ordinary interval; the carrier theorem
then places that interval in genuine distinct subset sums of all inputs. -/
theorem pairedPivotSumTree_Icc_subset_subsetSum
    {t k ell m : ℕ} (A B : PartitionTree ℕ t)
    (hell : 2 ≤ ell)
    (hA : A.PairwiseDisjoint) (hB : B.PairwiseDisjoint)
    (hAB : Disjoint A.carrier B.carrier)
    (hcard : AllLeafPairs
      (fun C P ↦ ell ≤ (pivotExtended (boundedSubsetSum C k) P).card) A B)
    (hbox : AllLeafPairs
      (fun C P ↦ pivotExtended (boundedSubsetSum C k) P ⊆ Finset.Icc 0 m) A B)
    (haper : AllLeafPairs
      (fun C P ↦ ¬ Erdos360.ContainedInNontrivialAP
        (pivotExtended (boundedSubsetSum C k) P)) A B)
    (hexceed : 2 ^ t * m + 1 < SumTree.growthLower ell t) :
    ∃ a : ℕ, Finset.Icc a (a + (2 * ell - 2)) ⊆
      (A.carrier ∪ B.carrier).subsetSum := by
  let T := pairedPivotSumTree k A B
  have hzero : T.AllLeaves fun S ↦ 0 ∈ S := by
    rw [allLeaves_pairedPivotSumTree_iff]
    apply allLeafPairs_of_allLeaves (allLeaves_true A) (allLeaves_true B)
    intro C P _ _
    exact zero_mem_pivotExtended (zero_mem_boundedSubsetSum C k)
  have hcardT : T.AllLeaves fun S ↦ ell ≤ S.card := by
    rwa [allLeaves_pairedPivotSumTree_iff]
  have hboxT : T.AllLeaves fun S ↦ S ⊆ Finset.Icc 0 m := by
    rwa [allLeaves_pairedPivotSumTree_iff]
  have haperT : T.AllLeaves fun S ↦
      ¬ Erdos360.ContainedInNontrivialAP S := by
    rwa [allLeaves_pairedPivotSumTree_iff]
  obtain ⟨a, ha⟩ := SumTree.containsInterval_of_growth_exceeds_diameter
    hell hzero hcardT haperT hboxT hexceed
  refine ⟨a, ha.trans ?_⟩
  exact carrier_pairedPivotSumTree_subset_subsetSum A B hA hB hAB

/-- The same wrapper followed by the CFP/Graham absorption lemma from
`Erdos360`: a disjoint reserve of elements no larger than the initial
interval length extends the covered interval by the full reserve mass. -/
theorem pairedPivotSumTree_Icc_subset_subsetSum_absorb
    {t k ell m : ℕ} (A B : PartitionTree ℕ t) (reserve : Finset ℕ)
    (hell : 2 ≤ ell)
    (hA : A.PairwiseDisjoint) (hB : B.PairwiseDisjoint)
    (hAB : Disjoint A.carrier B.carrier)
    (hcard : AllLeafPairs
      (fun C P ↦ ell ≤ (pivotExtended (boundedSubsetSum C k) P).card) A B)
    (hbox : AllLeafPairs
      (fun C P ↦ pivotExtended (boundedSubsetSum C k) P ⊆ Finset.Icc 0 m) A B)
    (haper : AllLeafPairs
      (fun C P ↦ ¬ Erdos360.ContainedInNontrivialAP
        (pivotExtended (boundedSubsetSum C k) P)) A B)
    (hexceed : 2 ^ t * m + 1 < SumTree.growthLower ell t)
    (hdisj : Disjoint (A.carrier ∪ B.carrier) reserve)
    (hreserve : ∀ r ∈ reserve, r ≤ 2 * ell - 1) :
    ∃ a : ℕ, Finset.Icc a
        (a + (2 * ell - 2) + ∑ r ∈ reserve, r) ⊆
      ((A.carrier ∪ B.carrier) ∪ reserve).subsetSum := by
  obtain ⟨a, ha⟩ := pairedPivotSumTree_Icc_subset_subsetSum A B hell
    hA hB hAB hcard hbox haper hexceed
  refine ⟨a, ?_⟩
  apply Erdos360.Icc_subset_subsetSum_union_of_le_length
    (show a ≤ a + (2 * ell - 2) by omega) hdisj ha
  intro r hr
  have hr' := hreserve r hr
  omega

end PartitionTree

end Erdos344
