import ErdosProblems.Erdos360.Core

open scoped Pointwise

namespace Erdos360

/-! Interval-contraction step in CFP Lemma 5.7. -/

/-- Fill the unused slots in a fixed-length sum with zero. -/
lemma nsmul_mem_iteratedFinsetSum_of_le
    {G : Type*} [AddCommGroup G] [DecidableEq G]
    {P : Finset G} {x : G} (hx : x ∈ P) (hzero : 0 ∈ P) :
    ∀ {r k : ℕ}, r ≤ k → r • x ∈ iteratedFinsetSum P k := by
  intro r k hr
  induction k generalizing r with
  | zero =>
      have : r = 0 := by omega
      subst r
      simp
  | succ k ih =>
      rw [iteratedFinsetSum_succ, Finset.mem_add]
      by_cases hrk : r ≤ k
      · refine ⟨r • x, ih hrk, 0, hzero, ?_⟩
        simp
      · have hre : r = k + 1 := by omega
        subst r
        refine ⟨k • x, ih (Nat.le_refl k), x, hx, ?_⟩
        simp [succ_nsmul]

/-- Additive homomorphisms commute with the fixed-length iterated sumset. -/
lemma image_iteratedFinsetSum_addHom
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    [DecidableEq G] [DecidableEq K]
    (f : G →+ K) (P : Finset G) (k : ℕ) :
    (iteratedFinsetSum P k).image f =
      iteratedFinsetSum (P.image f) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [iteratedFinsetSum_succ, iteratedFinsetSum_succ,
        Finset.image_add, ih]

/-- A surjective additive image of a generating finite set still generates. -/
lemma closure_image_addHom_eq_top
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    [DecidableEq G] [DecidableEq K]
    {P : Finset G} (f : G →+ K) (hf : Function.Surjective f)
    (hclosure : AddSubgroup.closure (P : Set G) = ⊤) :
    AddSubgroup.closure ((P.image f : Finset K) : Set K) = ⊤ := by
  classical
  let M : AddSubgroup G :=
    (AddSubgroup.closure ((P.image f : Finset K) : Set K)).comap f
  have hPM : (P : Set G) ⊆ M := by
    intro x hx
    change f x ∈ AddSubgroup.closure ((P.image f : Finset K) : Set K)
    apply AddSubgroup.subset_closure
    exact Finset.mem_image.mpr ⟨x, by simpa using hx, rfl⟩
  have hMtop : M = ⊤ := by
    apply top_unique
    rw [← hclosure, AddSubgroup.closure_le]
    exact hPM
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have hxM : x ∈ M := by rw [hMtop]; trivial
  exact hxM

/-- If `u` is congruent to `z`, lies strictly below `N+z`, and `z<N`,
then there was no wrap and `u=z`. -/
lemma eq_of_natCast_eq_natCast_of_lt_add
    {N u z : ℕ} [NeZero N]
    (hcast : (u : ZMod N) = (z : ZMod N))
    (hz : z < N) (hu : u < N + z) : u = z := by
  have hmod : u % N = z % N := by
    simpa [ZMod.natCast_eq_natCast_iff'] using hcast
  rw [Nat.mod_eq_of_lt hz] at hmod
  by_cases huN : u < N
  · exact Nat.ModEq.eq_of_lt_of_lt
      ((ZMod.natCast_eq_natCast_iff u z N).mp hcast) huN hz
  · have hdiv : u / N = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · omega
    have hdecomp := Nat.mod_add_div u N
    rw [hmod, hdiv] at hdecomp
    omega

/-- Positive-coordinate part of interval contraction. -/
lemma cyclic_interval_positive_coordinate_contracts
    {N L k z i : ℕ} [NeZero N] {a x : ZMod N}
    (hhalf : 2 * L ≤ N) (hz : z < L) (hi : i < L) (hzi : z ≤ i)
    (ha : a + (z : ZMod N) = 0)
    (hx : x = a + (i : ZMod N))
    (hmul : ∀ r ≤ k, ∃ j < L, r • x = a + (j : ZMod N)) :
    k * (i - z) + z < L := by
  let delta := i - z
  have hxcoord : x = (delta : ZMod N) := by
    dsimp [delta]
    rw [hx]
    push_cast
    have hiz : (i : ZMod N) = (z : ZMod N) + ((i - z : ℕ) : ZMod N) := by
      rw [← Nat.cast_add, Nat.add_sub_of_le hzi]
    rw [hiz]
    calc
      a + ((z : ZMod N) + ((i - z : ℕ) : ZMod N)) =
          (a + (z : ZMod N)) + ((i - z : ℕ) : ZMod N) := by abel
      _ = ((i - z : ℕ) : ZMod N) := by rw [ha]; simp
  have hcontract : ∀ r ≤ k, r * delta + z < L := by
    intro r hr
    induction r with
    | zero => simpa using hz
    | succ r ihr =>
        have hrk : r ≤ k := by omega
        have hprev := ihr hrk
        obtain ⟨j, hj, hrx⟩ := hmul (r + 1) (by omega)
        have hcast : (((r + 1) * delta + z : ℕ) : ZMod N) =
            (j : ZMod N) := by
          calc
            (((r + 1) * delta + z : ℕ) : ZMod N) =
                (r + 1) • x + (z : ZMod N) := by
              rw [hxcoord]
              push_cast
              simp [nsmul_eq_mul]
            _ = (a + (j : ZMod N)) + (z : ZMod N) := by rw [hrx]
            _ = (j : ZMod N) := by
              rw [add_assoc]
              rw [add_comm (j : ZMod N) (z : ZMod N), ← add_assoc, ha]
              simp
        have hleftN : (r + 1) * delta + z < N := by
          have hdlt : delta < L := by dsimp [delta]; omega
          have heq : (r + 1) * delta + z = (r * delta + z) + delta := by ring
          rw [heq]
          omega
        have hjN : j < N := by omega
        have heq := congrArg ZMod.val hcast
        rw [ZMod.val_natCast_of_lt hleftN, ZMod.val_natCast_of_lt hjN] at heq
        omega
  exact hcontract k (Nat.le_refl k)

/-- Negative-coordinate counterpart of
`cyclic_interval_positive_coordinate_contracts`. -/
lemma cyclic_interval_negative_coordinate_contracts
    {N L k z i : ℕ} [NeZero N] {a x : ZMod N}
    (hhalf : 2 * L ≤ N) (hz : z < L) (hi : i < L) (hiz : i ≤ z)
    (ha : a + (z : ZMod N) = 0)
    (hx : x = a + (i : ZMod N))
    (hmul : ∀ r ≤ k, ∃ j < L, r • x = a + (j : ZMod N)) :
    k * (z - i) ≤ z := by
  let delta := z - i
  have hxcoord : x = -((delta : ℕ) : ZMod N) := by
    dsimp [delta]
    rw [hx]
    have hzi : (z : ZMod N) = (i : ZMod N) + ((z - i : ℕ) : ZMod N) := by
      rw [← Nat.cast_add, Nat.add_sub_of_le hiz]
    have ha' : a = -(z : ZMod N) := by
      calc
        a = (a + (z : ZMod N)) - (z : ZMod N) := by abel
        _ = -(z : ZMod N) := by rw [ha]; simp
    rw [ha', hzi]
    abel
  have hcontract : ∀ r ≤ k, r * delta ≤ z := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ihr =>
        have hrk : r ≤ k := by omega
        have hprev := ihr hrk
        obtain ⟨j, hj, hrx⟩ := hmul (r + 1) (by omega)
        have hcast : ((((r + 1) * delta + j : ℕ) : ZMod N)) =
            (z : ZMod N) := by
          calc
            ((((r + 1) * delta + j : ℕ) : ZMod N)) =
                (j : ZMod N) - (r + 1) • x := by
              rw [hxcoord]
              push_cast
              simp [nsmul_eq_mul]
              ring
            _ = (z : ZMod N) := by
              rw [hrx]
              have ha' : a = -(z : ZMod N) := by
                calc
                  a = (a + (z : ZMod N)) - (z : ZMod N) := by abel
                  _ = -(z : ZMod N) := by rw [ha]; simp
              rw [ha']
              abel
        have hdlt : delta < L := by dsimp [delta]; omega
        have hbound : (r + 1) * delta + j < N + z := by
          have hs : (r + 1) * delta = r * delta + delta := by ring
          rw [hs]
          omega
        have hzN : z < N := by omega
        have heq := eq_of_natCast_eq_natCast_of_lt_add hcast hzN hbound
        omega
  exact hcontract k (Nat.le_refl k)

/-- Contraction in the normalized quotient `ZMod N`.  If the `k`-fold
sumset lies in a length-`L` interval occupying at most half the circle, then
the original zero-containing set lies in an interval whose length `ell`
satisfies the division-free estimate `k * ell ≤ 2 * L`.

The harmless hypothesis `k ≤ L` is automatic in the CFP application from
the Cauchy--Olson--Scherk growth bound (the almost-period set generates and
contains at least two points). -/
theorem zmod_interval_contraction
    {N L k : ℕ} [NeZero N] {P : Finset (ZMod N)} {a : ZMod N}
    (hzero : 0 ∈ P) (hk : 0 < k) (hkL : k ≤ L)
    (hhalf : 2 * L ≤ N)
    (hsum : iteratedFinsetSum P k ⊆
      cyclicCosetProgression (⊥ : AddSubgroup (ZMod N)) a 1 L) :
    ∃ a' : ZMod N, ∃ ell : ℕ,
      P ⊆ cyclicCosetProgression (⊥ : AddSubgroup (ZMod N)) a' 1 ell ∧
      k * ell ≤ 2 * L := by
  classical
  have hzeroSum : 0 ∈ iteratedFinsetSum P k := by
    simpa using nsmul_mem_iteratedFinsetSum_of_le hzero hzero
      (r := 0) (k := k) (Nat.zero_le k)
  obtain ⟨z, hz, hza⟩ := mem_cyclicCosetProgression_iff.mp (hsum hzeroSum)
  rw [AddSubgroup.mem_bot, sub_eq_zero] at hza
  have ha : a + (z : ZMod N) = 0 := by
    simpa using hza.symm
  have hmul : ∀ x ∈ P, ∀ r ≤ k, ∃ j < L,
      r • x = a + (j : ZMod N) := by
    intro x hx r hr
    have hrmem := nsmul_mem_iteratedFinsetSum_of_le hx hzero hr
    obtain ⟨j, hj, hrel⟩ :=
      mem_cyclicCosetProgression_iff.mp (hsum hrmem)
    rw [AddSubgroup.mem_bot, sub_eq_zero] at hrel
    refine ⟨j, hj, ?_⟩
    simpa using hrel
  let left := z / k
  let right := (L - 1 - z) / k
  let ell := left + right + 1
  let a' : ZMod N := a + ((z - left : ℕ) : ZMod N)
  have hleftLe : left ≤ z := by
    dsimp [left]
    exact Nat.div_le_self z k
  have hleftMul : k * left ≤ z := by
    dsimp [left]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self z k
  have hrightMul : k * right ≤ L - 1 - z := by
    dsimp [right]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (L - 1 - z) k
  refine ⟨a', ell, ?_, ?_⟩
  · intro x hxP
    obtain ⟨i, hi, hxi⟩ := hmul x hxP 1 hk
    have hx : x = a + (i : ZMod N) := by simpa using hxi
    rcases le_total i z with hiz | hzi
    · have hneg := cyclic_interval_negative_coordinate_contracts
        hhalf hz hi hiz ha hx (hmul x hxP)
      have hdist : z - i ≤ left := by
        rw [Nat.le_div_iff_mul_le hk]
        simpa [Nat.mul_comm] using hneg
      let q := i - (z - left)
      have hstartLe : z - left ≤ i := by omega
      have hqle : q ≤ left := by
        dsimp [q]
        omega
      have hq : q < ell := by
        have hleftEll : left < ell := by
          change left < left + right + 1
          exact Nat.lt_succ_of_le (Nat.le_add_right left right)
        exact hqle.trans_lt hleftEll
      apply mem_cyclicCosetProgression_iff.mpr
      refine ⟨q, hq, ?_⟩
      rw [AddSubgroup.mem_bot, sub_eq_zero]
      dsimp [a']
      have heq : z - left + (i - (z - left)) = i := by omega
      calc
        x = a + (i : ZMod N) := hx
        _ = a + (((z - left) + q : ℕ) : ZMod N) := by rw [heq]
        _ = a + (z - left : ℕ) + q • (1 : ZMod N) := by
          push_cast
          simp [nsmul_eq_mul]
          abel
    · have hpos := cyclic_interval_positive_coordinate_contracts
        hhalf hz hi hzi ha hx (hmul x hxP)
      have hdistMul : k * (i - z) ≤ L - 1 - z := by omega
      have hdist : i - z ≤ right := by
        rw [Nat.le_div_iff_mul_le hk]
        simpa [Nat.mul_comm] using hdistMul
      let q := left + (i - z)
      have hq : q < ell := by
        dsimp [q, ell]
        omega
      apply mem_cyclicCosetProgression_iff.mpr
      refine ⟨q, hq, ?_⟩
      rw [AddSubgroup.mem_bot, sub_eq_zero]
      dsimp [a']
      have heq : z - left + (left + (i - z)) = i := by omega
      calc
        x = a + (i : ZMod N) := hx
        _ = a + (((z - left) + q : ℕ) : ZMod N) := by rw [heq]
        _ = a + (z - left : ℕ) + q • (1 : ZMod N) := by
          push_cast
          simp [nsmul_eq_mul]
          abel
  · dsimp [ell]
    have hzL : z ≤ L - 1 := by omega
    calc
      k * (left + right + 1) = k * left + k * right + k := by ring
      _ ≤ z + (L - 1 - z) + k := by omega
      _ = L - 1 + k := by omega
      _ ≤ 2 * L := by omega

/-- In the generating case, containment of the `k`-fold sumset in a
half-circle interval already forces `k ≤ L`. -/
lemma k_le_length_of_generating_zmod_iterated_subset_half_interval
    {N L k : ℕ} [NeZero N] {P : Finset (ZMod N)} {a : ZMod N}
    (hzero : 0 ∈ P) (hk : 0 < k)
    (hclosure : AddSubgroup.closure (P : Set (ZMod N)) = ⊤)
    (hhalf : 2 * L ≤ N)
    (hsum : iteratedFinsetSum P k ⊆
      cyclicCosetProgression (⊥ : AddSubgroup (ZMod N)) a 1 L) :
    k ≤ L := by
  classical
  have hzeroSum : 0 ∈ iteratedFinsetSum P k := by
    simpa using nsmul_mem_iteratedFinsetSum_of_le hzero hzero
      (r := 0) (k := k) (Nat.zero_le k)
  have hLpos : 0 < L := by
    obtain ⟨i, hi, _⟩ := mem_cyclicCosetProgression_iff.mp (hsum hzeroSum)
    omega
  have hNtwo : 2 ≤ N := by omega
  have hone : (1 : ZMod N) ≠ 0 := by
    intro heq
    letI : Fact (1 < N) := ⟨by omega⟩
    have hv := congrArg ZMod.val heq
    simpa using hv
  have hPtwo : 2 ≤ P.card := by
    by_contra hnot
    have hcard : P.card ≤ 1 := by omega
    have hallzero : ∀ x ∈ P, x = 0 := by
      intro x hx
      exact (Finset.card_le_one.mp hcard x hx 0 hzero)
    have hclbot : AddSubgroup.closure (P : Set (ZMod N)) ≤ ⊥ := by
      rw [AddSubgroup.closure_le]
      intro x hx
      change x = 0
      exact hallzero x (by simpa using hx)
    have honebot : (1 : ZMod N) ∈ (⊥ : AddSubgroup (ZMod N)) := by
      apply hclbot
      rw [hclosure]
      trivial
    exact hone (by simpa using honebot)
  have hcoset : NotContainedInProperCoset P :=
    notContainedInProperCoset_of_zero_mem_closure_eq_top hzero hclosure
  have hlower :=
    min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
      ⟨0, hzero⟩ hcoset k hk
  have hiterCard : (iteratedFinsetSum P k).card ≤ L := by
    calc
      (iteratedFinsetSum P k).card ≤
          (cyclicCosetProgression
            (⊥ : AddSubgroup (ZMod N)) a 1 L).card :=
        Finset.card_le_card hsum
      _ ≤ L * Nat.card (⊥ : AddSubgroup (ZMod N)) :=
        cyclicCosetProgression_card_le _ _ _ _
      _ = L := by simp
  have hnotGroup : ¬ 2 * Fintype.card (ZMod N) ≤
      2 * (iteratedFinsetSum P k).card := by
    simp only [ZMod.card]
    omega
  have hmain : (k + 1) * P.card ≤
      2 * (iteratedFinsetSum P k).card := by
    rcases le_total (2 * Fintype.card (ZMod N))
        ((k + 1) * P.card) with hgroup | htarget
    · have hbad : 2 * Fintype.card (ZMod N) ≤
          2 * (iteratedFinsetSum P k).card := by
        have h := hlower
        rw [min_eq_left hgroup] at h
        exact h
      exact False.elim (hnotGroup hbad)
    · have h := hlower
      rw [min_eq_right htarget] at h
      exact h
  have htwo : 2 * (k + 1) ≤ 2 * L := by
    calc
      2 * (k + 1) ≤ P.card * (k + 1) :=
        Nat.mul_le_mul_right (k + 1) hPtwo
      _ = (k + 1) * P.card := by ring
      _ ≤ 2 * (iteratedFinsetSum P k).card := hmain
      _ ≤ 2 * L := Nat.mul_le_mul_left 2 hiterCard
  omega

/-- Quotient/H-coset form of `zmod_interval_contraction`.  An explicit
generator-preserving equivalence identifies the quotient by `H` with
`ZMod N`; the result is pulled back to the original cyclic group. -/
theorem cyclic_coset_progression_contraction
    {t N L k : ℕ} [NeZero t] [NeZero N]
    {P : Finset (ZMod t)} (H : AddSubgroup (ZMod t))
    (a d : ZMod t)
    (e : ZMod N ≃+ (ZMod t ⧸ H))
    (hgen : e 1 = QuotientAddGroup.mk' H d)
    (hzero : 0 ∈ P) (hk : 0 < k) (hkL : k ≤ L)
    (hhalf : 2 * L ≤ N)
    (hsum : iteratedFinsetSum P k ⊆ cyclicCosetProgression H a d L) :
    ∃ a' : ZMod t, ∃ ell : ℕ,
      P ⊆ cyclicCosetProgression H a' d ell ∧
      k * (ell * Nat.card H) ≤ 2 * (L * Nat.card H) := by
  classical
  let f : ZMod t →+ ZMod N :=
    e.symm.toAddMonoidHom.comp (QuotientAddGroup.mk' H)
  let Q : Finset (ZMod N) := P.image f
  have hzeroQ : 0 ∈ Q := by
    exact Finset.mem_image.mpr ⟨0, hzero, by simp [f]⟩
  have hsumImage : (iteratedFinsetSum P k).image f =
      iteratedFinsetSum Q k := by
    simpa [Q] using image_iteratedFinsetSum_addHom f P k
  have hfd : f d = 1 := by
    dsimp [f]
    change e.symm (QuotientAddGroup.mk' H d) = 1
    rw [← hgen]
    simp
  have hnorm : iteratedFinsetSum Q k ⊆
      cyclicCosetProgression (⊥ : AddSubgroup (ZMod N)) (f a) 1 L := by
    intro y hy
    rw [← hsumImage] at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨i, hi, hxi⟩ := mem_cyclicCosetProgression_iff.mp (hsum hx)
    apply mem_cyclicCosetProgression_iff.mpr
    refine ⟨i, hi, ?_⟩
    rw [AddSubgroup.mem_bot, sub_eq_zero]
    have hquot : QuotientAddGroup.mk' H x =
        QuotientAddGroup.mk' H (a + i • d) := by
      exact (QuotientAddGroup.eq_iff_sub_mem).2 hxi
    change f x = f a + i • (1 : ZMod N)
    rw [← hfd]
    simpa [f] using congrArg e.symm hquot
  obtain ⟨abar, ell, hQ, hmass⟩ :=
    zmod_interval_contraction hzeroQ hk hkL hhalf hnorm
  obtain ⟨a', ha'⟩ := QuotientAddGroup.mk'_surjective H (e abar)
  refine ⟨a', ell, ?_, ?_⟩
  · intro x hx
    have hfxQ : f x ∈ Q := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨i, hi, hfi⟩ := mem_cyclicCosetProgression_iff.mp (hQ hfxQ)
    rw [AddSubgroup.mem_bot, sub_eq_zero] at hfi
    apply mem_cyclicCosetProgression_iff.mpr
    refine ⟨i, hi, ?_⟩
    apply (QuotientAddGroup.eq_iff_sub_mem).1
    have hmap : QuotientAddGroup.mk' H x =
        QuotientAddGroup.mk' H (a' + i • d) := by
      calc
        QuotientAddGroup.mk' H x = e (f x) := by simp [f]
        _ = e (abar + i • (1 : ZMod N)) := congrArg e hfi
        _ = e abar + e (i • (1 : ZMod N)) := by rw [e.map_add]
        _ = e abar + i • e 1 := by simp only [map_nsmul]
        _ = QuotientAddGroup.mk' H a' +
            i • QuotientAddGroup.mk' H d := by rw [ha', hgen]
        _ = QuotientAddGroup.mk' H (a' + i • d) := by simp
    simpa using hmap
  · calc
      k * (ell * Nat.card H) = (k * ell) * Nat.card H := by ring
      _ ≤ (2 * L) * Nat.card H := Nat.mul_le_mul_right _ hmass
      _ = 2 * (L * Nat.card H) := by ring

/-- Application-ready version: generation of the ambient cyclic group
forces the displayed quotient step to generate the quotient, so the
generator-preserving `ZMod` equivalence required above is canonical. -/
theorem cyclic_coset_progression_contraction_of_closure_eq_top
    {t L k : ℕ} [NeZero t] {P : Finset (ZMod t)}
    (H : AddSubgroup (ZMod t)) (a d : ZMod t)
    (hzero : 0 ∈ P) (hk : 0 < k) (hkL : k ≤ L)
    (hclosure : AddSubgroup.closure (P : Set (ZMod t)) = ⊤)
    (hhalf : 2 * L ≤ Nat.card (ZMod t ⧸ H))
    (hsum : iteratedFinsetSum P k ⊆ cyclicCosetProgression H a d L) :
    ∃ a' : ZMod t, ∃ ell : ℕ,
      P ⊆ cyclicCosetProgression H a' d ell ∧
      k * (ell * Nat.card H) ≤ 2 * (L * Nat.card H) := by
  classical
  let q : ZMod t →+ (ZMod t ⧸ H) := QuotientAddGroup.mk' H
  have hzeroSum : 0 ∈ iteratedFinsetSum P k := by
    simpa using nsmul_mem_iteratedFinsetSum_of_le hzero hzero
      (r := 0) (k := k) (Nat.zero_le k)
  obtain ⟨z, hz, hzrel⟩ :=
    mem_cyclicCosetProgression_iff.mp (hsum hzeroSum)
  have hqa : q a ∈ AddSubgroup.zmultiples (q d) := by
    have hzeroq : q 0 = q (a + z • d) := by
      simpa [q] using (QuotientAddGroup.eq_iff_sub_mem).2 hzrel
    have heq : q a = -(z • q d) := by
      rw [map_zero, map_add, map_nsmul] at hzeroq
      exact eq_neg_of_add_eq_zero_left hzeroq.symm
    rw [heq]
    exact (AddSubgroup.zmultiples (q d)).neg_mem
      ((AddSubgroup.zmultiples (q d)).nsmul_mem
        (AddSubgroup.mem_zmultiples (q d)) z)
  let K : AddSubgroup (ZMod t) :=
    (AddSubgroup.zmultiples (q d)).comap q
  have hPK : (P : Set (ZMod t)) ⊆ K := by
    intro x hx
    have hxmem := nsmul_mem_iteratedFinsetSum_of_le
      (show x ∈ P from hx) hzero (r := 1) (k := k) hk
    obtain ⟨i, hi, hxrel⟩ :=
      mem_cyclicCosetProgression_iff.mp (hsum hxmem)
    change q x ∈ AddSubgroup.zmultiples (q d)
    have hxq : q x = q (a + i • d) :=
      by simpa [q] using (QuotientAddGroup.eq_iff_sub_mem).2 hxrel
    rw [hxq, map_add, map_nsmul]
    exact (AddSubgroup.zmultiples (q d)).add_mem hqa
      ((AddSubgroup.zmultiples (q d)).nsmul_mem
        (AddSubgroup.mem_zmultiples (q d)) i)
  have hKtop : K = ⊤ := by
    apply top_unique
    rw [← hclosure, AddSubgroup.closure_le]
    exact hPK
  have hgenQ : ∀ y : (ZMod t ⧸ H),
      y ∈ AddSubgroup.zmultiples (q d) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H y
    have hxK : x ∈ K := by rw [hKtop]; trivial
    exact hxK
  let N := Nat.card (ZMod t ⧸ H)
  have hNpos : 0 < N := Nat.card_pos
  letI : NeZero N := ⟨hNpos.ne'⟩
  let e : ZMod N ≃+ (ZMod t ⧸ H) :=
    zmodAddEquivOfGenerator hgenQ (n := N) rfl
  have heone : e 1 = QuotientAddGroup.mk' H d := by
    simpa [e, q] using zmodAddEquivOfGenerator_apply_one hgenQ rfl
  exact cyclic_coset_progression_contraction H a d e heone
    hzero hk hkL (by simpa [N] using hhalf) hsum

/-- CFP's two numerical hypotheses imply that the inverse-theorem
progression occupies less than half of the quotient by `H`. -/
lemma quotient_half_of_progression_mass_and_sparse
    {t L BCard : ℕ} [NeZero t] (H : AddSubgroup (ZMod t))
    (hmass : 25 * (L * Nat.card H) ≤ 52 * BCard)
    (hsparse : 104 * BCard < 25 * t) :
    2 * L ≤ Nat.card (ZMod t ⧸ H) := by
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hcard : t = Nat.card (ZMod t ⧸ H) * Nat.card H := by
    simpa using H.card_eq_card_quotient_mul_card_addSubgroup
  have hscaled : 25 * ((2 * L) * Nat.card H) <
      25 * (Nat.card (ZMod t ⧸ H) * Nat.card H) := by
    rw [← hcard]
    nlinarith
  have hmul : (2 * L) * Nat.card H <
      Nat.card (ZMod t ⧸ H) * Nat.card H := by
    apply (Nat.mul_lt_mul_left (by omega : 0 < 25)).mp
    simpa only [mul_assoc] using hscaled
  exact ((Nat.mul_lt_mul_right hHpos).mp hmul).le

/-- The length lower bound needed by contraction, stated before quotient
normalization.  Generation of `P` makes the quotient progression step a
generator, after which the normalized Kneser estimate applies. -/
lemma k_le_length_of_generating_cyclic_coset_iterated_subset
    {t L k : ℕ} [NeZero t] {P : Finset (ZMod t)}
    (H : AddSubgroup (ZMod t)) (a d : ZMod t)
    (hzero : 0 ∈ P) (hk : 0 < k)
    (hclosure : AddSubgroup.closure (P : Set (ZMod t)) = ⊤)
    (hhalf : 2 * L ≤ Nat.card (ZMod t ⧸ H))
    (hsum : iteratedFinsetSum P k ⊆ cyclicCosetProgression H a d L) :
    k ≤ L := by
  classical
  let q : ZMod t →+ (ZMod t ⧸ H) := QuotientAddGroup.mk' H
  have hzeroSum : 0 ∈ iteratedFinsetSum P k := by
    simpa using nsmul_mem_iteratedFinsetSum_of_le hzero hzero
      (r := 0) (k := k) (Nat.zero_le k)
  obtain ⟨z, hz, hzrel⟩ :=
    mem_cyclicCosetProgression_iff.mp (hsum hzeroSum)
  have hqa : q a ∈ AddSubgroup.zmultiples (q d) := by
    have hzeroq : q 0 = q (a + z • d) := by
      simpa [q] using (QuotientAddGroup.eq_iff_sub_mem).2 hzrel
    have heq : q a = -(z • q d) := by
      rw [map_zero, map_add, map_nsmul] at hzeroq
      exact eq_neg_of_add_eq_zero_left hzeroq.symm
    rw [heq]
    exact (AddSubgroup.zmultiples (q d)).neg_mem
      ((AddSubgroup.zmultiples (q d)).nsmul_mem
        (AddSubgroup.mem_zmultiples (q d)) z)
  let K : AddSubgroup (ZMod t) :=
    (AddSubgroup.zmultiples (q d)).comap q
  have hPK : (P : Set (ZMod t)) ⊆ K := by
    intro x hx
    have hxmem := nsmul_mem_iteratedFinsetSum_of_le
      (show x ∈ P from hx) hzero (r := 1) (k := k) hk
    obtain ⟨i, hi, hxrel⟩ :=
      mem_cyclicCosetProgression_iff.mp (hsum hxmem)
    change q x ∈ AddSubgroup.zmultiples (q d)
    have hxq : q x = q (a + i • d) := by
      simpa [q] using (QuotientAddGroup.eq_iff_sub_mem).2 hxrel
    rw [hxq, map_add, map_nsmul]
    exact (AddSubgroup.zmultiples (q d)).add_mem hqa
      ((AddSubgroup.zmultiples (q d)).nsmul_mem
        (AddSubgroup.mem_zmultiples (q d)) i)
  have hKtop : K = ⊤ := by
    apply top_unique
    rw [← hclosure, AddSubgroup.closure_le]
    exact hPK
  have hgenQ : ∀ y : (ZMod t ⧸ H),
      y ∈ AddSubgroup.zmultiples (q d) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H y
    have hxK : x ∈ K := by rw [hKtop]; trivial
    exact hxK
  let N := Nat.card (ZMod t ⧸ H)
  have hNpos : 0 < N := Nat.card_pos
  letI : NeZero N := ⟨hNpos.ne'⟩
  let e : ZMod N ≃+ (ZMod t ⧸ H) :=
    zmodAddEquivOfGenerator hgenQ (n := N) rfl
  have heone : e 1 = QuotientAddGroup.mk' H d := by
    simpa [e, q] using zmodAddEquivOfGenerator_apply_one hgenQ rfl
  let f : ZMod t →+ ZMod N :=
    e.symm.toAddMonoidHom.comp (QuotientAddGroup.mk' H)
  let Q : Finset (ZMod N) := P.image f
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨xbar, hxbar⟩ := e.symm.surjective y
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective H xbar
    refine ⟨x, ?_⟩
    dsimp [f]
    change e.symm (QuotientAddGroup.mk' H x) = y
    rw [hx, hxbar]
  have hclosureQ : AddSubgroup.closure (Q : Set (ZMod N)) = ⊤ := by
    simpa [Q] using closure_image_addHom_eq_top f hf hclosure
  have hzeroQ : 0 ∈ Q := Finset.mem_image.mpr ⟨0, hzero, by simp [f]⟩
  have hsumImage : (iteratedFinsetSum P k).image f =
      iteratedFinsetSum Q k := by
    simpa [Q] using image_iteratedFinsetSum_addHom f P k
  have hfd : f d = 1 := by
    dsimp [f]
    change e.symm (QuotientAddGroup.mk' H d) = 1
    rw [← heone]
    simp
  have hnorm : iteratedFinsetSum Q k ⊆
      cyclicCosetProgression (⊥ : AddSubgroup (ZMod N)) (f a) 1 L := by
    intro y hy
    rw [← hsumImage] at hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨i, hi, hxi⟩ := mem_cyclicCosetProgression_iff.mp (hsum hx)
    apply mem_cyclicCosetProgression_iff.mpr
    refine ⟨i, hi, ?_⟩
    rw [AddSubgroup.mem_bot, sub_eq_zero]
    have hquot : QuotientAddGroup.mk' H x =
        QuotientAddGroup.mk' H (a + i • d) :=
      (QuotientAddGroup.eq_iff_sub_mem).2 hxi
    change f x = f a + i • (1 : ZMod N)
    rw [← hfd]
    simpa [f] using congrArg e.symm hquot
  exact k_le_length_of_generating_zmod_iterated_subset_half_interval
    hzeroQ hk hclosureQ (by simpa [N] using hhalf) hnorm

/-- The complete CFP quotient-interval contraction connector.  The inverse
progression mass and sparse ambient-group hypotheses supply the half-circle
condition; generation supplies both the quotient generator and `k ≤ L`. -/
theorem cyclic_coset_progression_contraction_of_mass_and_sparse
    {t L k BCard : ℕ} [NeZero t] {P : Finset (ZMod t)}
    (H : AddSubgroup (ZMod t)) (a d : ZMod t)
    (hzero : 0 ∈ P) (hk : 0 < k)
    (hclosure : AddSubgroup.closure (P : Set (ZMod t)) = ⊤)
    (hsum : iteratedFinsetSum P k ⊆ cyclicCosetProgression H a d L)
    (hmass : 25 * (L * Nat.card H) ≤ 52 * BCard)
    (hsparse : 104 * BCard < 25 * t) :
    ∃ a' : ZMod t, ∃ ell : ℕ,
      P ⊆ cyclicCosetProgression H a' d ell ∧
      k * (ell * Nat.card H) ≤ 2 * (L * Nat.card H) := by
  have hhalf := quotient_half_of_progression_mass_and_sparse H hmass hsparse
  have hkL := k_le_length_of_generating_cyclic_coset_iterated_subset
    H a d hzero hk hclosure hhalf hsum
  exact cyclic_coset_progression_contraction_of_closure_eq_top
    H a d hzero hk hkL hclosure hhalf hsum

end Erdos360
