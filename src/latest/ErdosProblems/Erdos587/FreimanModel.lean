import Mathlib

open scoped BigOperators Pointwise

namespace Erdos587

def badMultipliers (q M : ℕ) [NeZero q] (x : ℤ) : Finset (ZMod q) :=
  Finset.univ.filter fun lam => M ∣ (lam * (x : ZMod q)).val

@[simp] lemma mem_badMultipliers {q M : ℕ} [NeZero q] {x : ℤ} {lam : ZMod q} :
    lam ∈ badMultipliers q M x ↔ M ∣ (lam * (x : ZMod q)).val := by
  simp [badMultipliers]

lemma card_badMultipliers_le {q M : ℕ} [NeZero q] [Fact q.Prime]
    (hM : 0 < M) {x : ℤ} (hx : (x : ZMod q) ≠ 0) :
    (badMultipliers q M x).card ≤ q / M + 1 := by
  let f : ZMod q → ℕ := fun lam => (lam * (x : ZMod q)).val / M
  rw [← Finset.card_range (q / M + 1)]
  apply Finset.card_le_card_of_injOn f
      (s := badMultipliers q M x) (t := Finset.range (q / M + 1))
  · intro lam hlam
    dsimp only [f]
    have hval := (lam * (x : ZMod q)).val_lt
    have hdiv : (lam * (x : ZMod q)).val / M ≤ q / M :=
      Nat.div_le_div_right hval.le
    simpa only [Finset.mem_coe, Finset.mem_range, Nat.succ_eq_add_one] using
      Nat.lt_succ_of_le hdiv
  · intro lam hlam mu hmu heq
    have hlamDiv : M ∣ (lam * (x : ZMod q)).val :=
      mem_badMultipliers.mp hlam
    have hmuDiv : M ∣ (mu * (x : ZMod q)).val :=
      mem_badMultipliers.mp hmu
    dsimp only [f] at heq
    have hval : (lam * (x : ZMod q)).val = (mu * (x : ZMod q)).val := by
      calc
        (lam * (x : ZMod q)).val =
            M * ((lam * (x : ZMod q)).val / M) :=
              (Nat.mul_div_cancel' hlamDiv).symm
        _ = M * ((mu * (x : ZMod q)).val / M) := by rw [heq]
        _ = (mu * (x : ZMod q)).val := Nat.mul_div_cancel' hmuDiv
    have hprod : lam * (x : ZMod q) = mu * (x : ZMod q) := by
      rw [← ZMod.natCast_zmod_val (lam * (x : ZMod q)),
        ← ZMod.natCast_zmod_val (mu * (x : ZMod q)), hval]
    exact mul_right_cancel₀ hx hprod

lemma intCast_zmod_ne_zero_of_natAbs_lt {q : ℕ} [NeZero q]
    {x : ℤ} (hx0 : x ≠ 0) (hxq : x.natAbs < q) :
    (x : ZMod q) ≠ 0 := by
  intro hx
  have hdiv : (q : ℤ) ∣ x :=
    (CharP.intCast_eq_zero_iff (ZMod q) q x).mp hx
  have hqle : q ≤ x.natAbs := by
    exact_mod_cast Int.natAbs_le_of_dvd_ne_zero hdiv hx0
  omega

lemma card_biUnion_badMultipliers_le {q M : ℕ} [NeZero q] [Fact q.Prime]
    (hM : 0 < M) {D : Finset ℤ}
    (hx : ∀ x ∈ D, (x : ZMod q) ≠ 0) :
    (D.biUnion (badMultipliers q M)).card ≤ D.card * (q / M + 1) := by
  calc
    (D.biUnion (badMultipliers q M)).card ≤
        ∑ x ∈ D, (badMultipliers q M x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ D, (q / M + 1) := by
      gcongr with x hxD
      exact card_badMultipliers_le hM (hx x hxD)
    _ = D.card * (q / M + 1) := by simp

lemma multiplier_union_card_lt {N q : ℕ} (hN : 0 < N)
    (hq : 4 * N < q) :
    N * (q / (2 * N) + 1) < q := by
  have hden : 0 < 2 * N := by omega
  have hdiv := Nat.mul_div_le q (2 * N)
  have hmul : 2 * (N * (q / (2 * N))) ≤ q := by
    calc
      2 * (N * (q / (2 * N))) = (2 * N) * (q / (2 * N)) := by ring
      _ ≤ q := hdiv
  nlinarith

theorem exists_good_multiplier {D : Finset ℤ} {N q : ℕ}
    [NeZero q] [Fact q.Prime] (hN : 0 < N) (hcard : D.card ≤ N)
    (habs : ∀ x ∈ D, x.natAbs < q) (hq : 4 * N < q) :
    ∃ lam : ZMod q, lam ≠ 0 ∧
      ∀ x ∈ D, x ≠ 0 → ¬ (2 * N ∣ (lam * (x : ZMod q)).val) := by
  classical
  let D₀ := D.erase 0
  by_cases hD₀ : D₀.Nonempty
  · let U : Finset (ZMod q) := D₀.biUnion (badMultipliers q (2 * N))
    have hxcast : ∀ x ∈ D₀, (x : ZMod q) ≠ 0 := by
      intro x hxD
      have hxD' := Finset.mem_erase.mp hxD
      exact intCast_zmod_ne_zero_of_natAbs_lt hxD'.1 (habs x hxD'.2)
    have hUcard : U.card < q := by
      calc
        U.card ≤ D₀.card * (q / (2 * N) + 1) :=
          card_biUnion_badMultipliers_le (by omega) hxcast
        _ ≤ N * (q / (2 * N) + 1) := by
          gcongr
          exact Finset.card_erase_le.trans hcard
        _ < q := multiplier_union_card_lt hN hq
    have hUne : U ≠ Finset.univ := by
      intro hEq
      have : U.card = q := by simpa [hEq]
      omega
    have hex : ∃ lam : ZMod q, lam ∉ U := by
      by_contra h
      push_neg at h
      apply hUne
      ext lam
      simp [h lam]
    obtain ⟨lam, hlamU⟩ := hex
    refine ⟨lam, ?_, ?_⟩
    · intro hlam0
      have hxU : (0 : ZMod q) ∈ U := by
        obtain ⟨x, hxD₀⟩ := hD₀
        apply Finset.mem_biUnion.mpr
        refine ⟨x, hxD₀, ?_⟩
        simp
      exact hlamU (by simpa [hlam0] using hxU)
    · intro x hxD hx0 hbad
      apply hlamU
      apply Finset.mem_biUnion.mpr
      exact ⟨x, Finset.mem_erase.mpr ⟨hx0, hxD⟩,
        mem_badMultipliers.mpr hbad⟩
  · refine ⟨1, one_ne_zero, ?_⟩
    intro x hxD hx0
    exfalso
    apply hD₀
    exact ⟨x, Finset.mem_erase.mpr ⟨hx0, hxD⟩⟩

lemma multiset_sum_mem_nsmul (A : Finset ℤ) {T : Multiset ℤ}
    (hT : ∀ x ∈ T, x ∈ A) : T.sum ∈ T.card • A := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons a T ih =>
      rw [Multiset.card_cons, succ_nsmul, Finset.mem_add]
      refine ⟨T.sum, ih ?_, a, hT a (by simp), ?_⟩
      · intro x hx
        exact hT x (by simp [hx])
      · simp [add_comm]

def ruzsaRepresentative (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ℕ :=
  (lam * (a : ZMod q)).val

def ruzsaColor (q s : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ℕ :=
  ruzsaRepresentative q lam a / (q / (2 * s) + 1)

def ruzsaModelMap (q M : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ZMod M :=
  ruzsaRepresentative q lam a

lemma ruzsaRepresentative_lt (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) :
    ruzsaRepresentative q lam a < q := by
  exact (lam * (a : ZMod q)).val_lt

lemma ruzsaRepresentative_cast (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) :
    (ruzsaRepresentative q lam a : ZMod q) = lam * (a : ZMod q) := by
  exact ZMod.natCast_zmod_val _

lemma ruzsaColor_lt {q s : ℕ} [NeZero q] (lam : ZMod q)
    (hs : 0 < s) (hq : 2 * s < q) (a : ℤ) :
    ruzsaColor q s lam a < 2 * s := by
  let L := q / (2 * s) + 1
  have hden : 0 < 2 * s := by omega
  have hqL : q < (2 * s) * L := by
    simp only [L]
    exact Nat.lt_mul_div_succ q hden
  have hrep : ruzsaRepresentative q lam a < q := ruzsaRepresentative_lt q lam a
  dsimp [ruzsaColor]
  rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
  simpa only [L] using hrep.trans hqL

lemma ruzsaRepresentative_sub_lt_of_color_eq {q s : ℕ} [NeZero q]
    (lam : ZMod q) {a b : ℤ}
    (hcolor : ruzsaColor q s lam a = ruzsaColor q s lam b) :
    (ruzsaRepresentative q lam a : ℤ) - ruzsaRepresentative q lam b <
      (q / (2 * s) + 1 : ℕ) := by
  let L := q / (2 * s) + 1
  have hL : 0 < L := by exact Nat.succ_pos _
  have hmoda := Nat.mod_lt (ruzsaRepresentative q lam a) hL
  have hmodb := Nat.mod_lt (ruzsaRepresentative q lam b) hL
  have ha := Nat.mod_add_div (ruzsaRepresentative q lam a) L
  have hb := Nat.mod_add_div (ruzsaRepresentative q lam b) L
  have hdiv : ruzsaRepresentative q lam a / L = ruzsaRepresentative q lam b / L := by
    simpa [ruzsaColor, L] using hcolor
  have habNat : ruzsaRepresentative q lam a < ruzsaRepresentative q lam b + L := by
    calc
      ruzsaRepresentative q lam a =
          ruzsaRepresentative q lam a % L +
            L * (ruzsaRepresentative q lam a / L) := ha.symm
      _ < L + L * (ruzsaRepresentative q lam a / L) := by omega
      _ = L + L * (ruzsaRepresentative q lam b / L) := by rw [hdiv]
      _ ≤ ruzsaRepresentative q lam b + L := by omega
  have habZ : (ruzsaRepresentative q lam a : ℤ) <
      (ruzsaRepresentative q lam b : ℤ) + L := by
    exact_mod_cast habNat
  simpa only [L, Nat.cast_add, Nat.cast_one] using (show
    (ruzsaRepresentative q lam a : ℤ) - ruzsaRepresentative q lam b < (L : ℤ) by
      omega)

lemma ruzsaRepresentative_bounds_of_color_eq {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {a : ℤ} (hcolor : ruzsaColor q s lam a = c) :
    c * (q / (2 * s) + 1) ≤ ruzsaRepresentative q lam a ∧
      ruzsaRepresentative q lam a < (c + 1) * (q / (2 * s) + 1) := by
  have hL : 0 < q / (2 * s) + 1 := Nat.succ_pos _
  have hdiv : ruzsaRepresentative q lam a / (q / (2 * s) + 1) = c := by
    simpa [ruzsaColor] using hcolor
  constructor
  · rw [← hdiv]
    simpa [mul_comm] using Nat.div_mul_le_self
      (ruzsaRepresentative q lam a) (q / (2 * s) + 1)
  · rw [← hdiv]
    simpa [mul_comm] using Nat.lt_mul_div_succ (ruzsaRepresentative q lam a) hL

def ruzsaRepresentativeSum (q : ℕ) [NeZero q] (lam : ZMod q)
    (T : Multiset ℤ) : ℕ :=
  (T.map (ruzsaRepresentative q lam)).sum

lemma ruzsaRepresentativeSum_bounds {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {T : Multiset ℤ} (hcard : T.card = s) (hs : 0 < s)
    (hcolor : ∀ x ∈ T, ruzsaColor q s lam x = c) :
    s * (c * (q / (2 * s) + 1)) ≤ ruzsaRepresentativeSum q lam T ∧
      ruzsaRepresentativeSum q lam T < s * ((c + 1) * (q / (2 * s) + 1)) := by
  let L := q / (2 * s) + 1
  have hlo : T.card • (c * L) ≤ ruzsaRepresentativeSum q lam T := by
    have hlo' := Multiset.card_nsmul_le_sum
      (s := T.map (ruzsaRepresentative q lam)) (a := c * L) (by
        intro y hy
        rw [Multiset.mem_map] at hy
        obtain ⟨x, hxT, rfl⟩ := hy
        simpa only [L] using
          (ruzsaRepresentative_bounds_of_color_eq lam (hcolor x hxT)).1)
    simpa only [ruzsaRepresentativeSum, Multiset.card_map] using hlo'
  have hTne : T ≠ 0 := by
    intro hT
    simp [hT] at hcard
    omega
  have hhi : ruzsaRepresentativeSum q lam T < T.card • ((c + 1) * L) := by
    have hhi' := Multiset.sum_lt_sum_of_nonempty hTne fun x hxT =>
      (ruzsaRepresentative_bounds_of_color_eq lam (hcolor x hxT)).2
    simpa only [ruzsaRepresentativeSum, Multiset.map_const',
      Multiset.sum_replicate, L] using hhi'
  simpa only [hcard, L, Nat.nsmul_eq_mul] using And.intro hlo hhi

lemma ruzsaRepresentativeSum_sub_abs_lt {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {T U : Multiset ℤ}
    (hTcard : T.card = s) (hUcard : U.card = s) (hs : 0 < s)
    (hTcolor : ∀ x ∈ T, ruzsaColor q s lam x = c)
    (hUcolor : ∀ x ∈ U, ruzsaColor q s lam x = c) :
    (ruzsaRepresentativeSum q lam T : ℤ) - ruzsaRepresentativeSum q lam U <
        s * (q / (2 * s) + 1) ∧
      -((s * (q / (2 * s) + 1) : ℕ) : ℤ) <
        (ruzsaRepresentativeSum q lam T : ℤ) - ruzsaRepresentativeSum q lam U := by
  obtain ⟨hTlo, hThi⟩ :=
    ruzsaRepresentativeSum_bounds lam hTcard hs hTcolor
  obtain ⟨hUlo, hUhi⟩ :=
    ruzsaRepresentativeSum_bounds lam hUcard hs hUcolor
  have hTU : ruzsaRepresentativeSum q lam T <
      ruzsaRepresentativeSum q lam U + s * (q / (2 * s) + 1) := by
    nlinarith
  have hUT : ruzsaRepresentativeSum q lam U <
      ruzsaRepresentativeSum q lam T + s * (q / (2 * s) + 1) := by
    nlinarith
  have hTU' : (ruzsaRepresentativeSum q lam T : ℤ) <
      (ruzsaRepresentativeSum q lam U : ℤ) + s * (q / (2 * s) + 1) := by
    exact_mod_cast hTU
  have hUT' : (ruzsaRepresentativeSum q lam U : ℤ) <
      (ruzsaRepresentativeSum q lam T : ℤ) + s * (q / (2 * s) + 1) := by
    exact_mod_cast hUT
  constructor <;> omega

lemma ruzsaRepresentativeSum_cast (q : ℕ) [NeZero q] (lam : ZMod q)
    (T : Multiset ℤ) :
    (ruzsaRepresentativeSum q lam T : ZMod q) = lam * (T.sum : ZMod q) := by
  induction T using Multiset.induction_on with
  | empty => simp [ruzsaRepresentativeSum]
  | @cons a T ih =>
      rw [show ruzsaRepresentativeSum q lam (a ::ₘ T) =
        ruzsaRepresentative q lam a + ruzsaRepresentativeSum q lam T by
          simp [ruzsaRepresentativeSum]]
      rw [Nat.cast_add, ruzsaRepresentative_cast, ih, Multiset.sum_cons,
        Int.cast_add]
      ring

lemma ruzsaModelMap_sum (q M : ℕ) [NeZero q] [NeZero M]
    (lam : ZMod q) (T : Multiset ℤ) :
    (T.map (ruzsaModelMap q M lam)).sum =
      (ruzsaRepresentativeSum q lam T : ZMod M) := by
  induction T using Multiset.induction_on with
  | empty => simp [ruzsaRepresentativeSum]
  | @cons a T ih =>
      simp only [ruzsaModelMap, ruzsaRepresentativeSum, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add, ih]

lemma ruzsaBlockWidth_lt {q s : ℕ} (hs : 0 < s) (hq : 2 * s < q) :
    s * (q / (2 * s) + 1) < q := by
  have hdiv := Nat.mul_div_le q (2 * s)
  have hhalf : 2 * (s * (q / (2 * s))) ≤ q := by
    simpa only [mul_assoc] using hdiv
  nlinarith

lemma ruzsaRepresentativeSum_sub_cast (q : ℕ) [NeZero q]
    (lam : ZMod q) (T U : Multiset ℤ) :
    (((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U : ℤ) : ZMod q) =
      lam * ((T.sum - U.sum : ℤ) : ZMod q) := by
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    ruzsaRepresentativeSum_cast, ruzsaRepresentativeSum_cast, Int.cast_sub]
  ring

lemma ruzsaModelMap_sum_eq_iff_dvd (q M : ℕ) [NeZero q] [NeZero M]
    (lam : ZMod q) (T U : Multiset ℤ) :
    (T.map (ruzsaModelMap q M lam)).sum =
        (U.map (ruzsaModelMap q M lam)).sum ↔
      (M : ℤ) ∣ ((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U) := by
  rw [ruzsaModelMap_sum, ruzsaModelMap_sum]
  constructor
  · intro h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
  · intro h
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr h
    simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero] using hz

lemma zmod_val_eq_natAbs_of_nonneg {q : ℕ} [NeZero q]
    {y : ℤ} {z : ZMod q} (hy : 0 ≤ y) (hyq : y.natAbs < q)
    (hcast : (y : ZMod q) = z) : z.val = y.natAbs := by
  have hycoe : (y.natAbs : ℤ) = y := Int.natAbs_of_nonneg hy
  have hcastNat : (y.natAbs : ZMod q) = z := by
    rw [← hcast]
    simpa using congrArg (fun t : ℤ => (t : ZMod q)) hycoe
  rw [← hcastNat, ZMod.val_natCast_of_lt hyq]

lemma int_natAbs_lt_of_neg_lt_and_lt {y : ℤ} {B : ℕ}
    (hlo : -(B : ℤ) < y) (hhi : y < B) : y.natAbs < B := by
  by_cases hy : 0 ≤ y
  · have hcast : (y.natAbs : ℤ) < B := by
      rw [Int.natAbs_of_nonneg hy]
      exact hhi
    exact_mod_cast hcast
  · have hyneg : 0 ≤ -y := by omega
    have hcast : ((-y).natAbs : ℤ) < B := by
      rw [Int.natAbs_of_nonneg hyneg]
      omega
    rw [Int.natAbs_neg] at hcast
    exact_mod_cast hcast

lemma ruzsaModelMap_multiset_sum_eq_iff
    {A : Finset ℤ} {s M q c : ℕ} [NeZero q] [NeZero M]
    (lam : ZMod q) (hs : 0 < s) (hq : 2 * s < q)
    (hmono : ∀ a ∈ A, ruzsaColor q s lam a = c)
    (hgood : ∀ x ∈ s • A - s • A, x ≠ 0 →
      ¬ (M ∣ (lam * (x : ZMod q)).val))
    {T U : Multiset ℤ}
    (hTA : ∀ x ∈ T, x ∈ A) (hUA : ∀ x ∈ U, x ∈ A)
    (hTcard : T.card = s) (hUcard : U.card = s) :
    (T.map (ruzsaModelMap q M lam)).sum =
        (U.map (ruzsaModelMap q M lam)).sum ↔ T.sum = U.sum := by
  have hTsum : T.sum ∈ s • A := by
    simpa only [hTcard] using multiset_sum_mem_nsmul A hTA
  have hUsum : U.sum ∈ s • A := by
    simpa only [hUcard] using multiset_sum_mem_nsmul A hUA
  have hTUmem : T.sum - U.sum ∈ s • A - s • A :=
    Finset.mem_sub.mpr ⟨T.sum, hTsum, U.sum, hUsum, rfl⟩
  have hUTmem : U.sum - T.sum ∈ s • A - s • A :=
    Finset.mem_sub.mpr ⟨U.sum, hUsum, T.sum, hTsum, rfl⟩
  have hshort := ruzsaRepresentativeSum_sub_abs_lt lam hTcard hUcard hs
    (fun x hx => hmono x (hTA x hx)) (fun x hx => hmono x (hUA x hx))
  have hwidth := ruzsaBlockWidth_lt hs hq
  have hsmall :
      (((ruzsaRepresentativeSum q lam T : ℤ) -
          ruzsaRepresentativeSum q lam U : ℤ)).natAbs < q := by
    have hwidthZ : ((s * (q / (2 * s) + 1) : ℕ) : ℤ) < q := by
      exact_mod_cast hwidth
    apply int_natAbs_lt_of_neg_lt_and_lt
    · exact (by omega : -(q : ℤ) <
        -((s * (q / (2 * s) + 1) : ℕ) : ℤ)).trans hshort.2
    · exact hshort.1.trans hwidthZ
  constructor
  · intro hmap
    by_contra hsum
    have hx : T.sum - U.sum ≠ 0 := sub_ne_zero.mpr hsum
    by_cases hy : 0 ≤ (ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U
    · have hdiv : (M : ℤ) ∣
          ((ruzsaRepresentativeSum q lam T : ℤ) -
            ruzsaRepresentativeSum q lam U) :=
        (ruzsaModelMap_sum_eq_iff_dvd q M lam T U).mp hmap
      have hdivNat : M ∣ (((ruzsaRepresentativeSum q lam T : ℤ) -
          ruzsaRepresentativeSum q lam U : ℤ)).natAbs :=
        Int.natCast_dvd.mp hdiv
      have hval : (lam * ((T.sum - U.sum : ℤ) : ZMod q)).val =
          (((ruzsaRepresentativeSum q lam T : ℤ) -
            ruzsaRepresentativeSum q lam U : ℤ)).natAbs := by
        apply zmod_val_eq_natAbs_of_nonneg hy hsmall
        exact ruzsaRepresentativeSum_sub_cast q lam T U
      exact hgood (T.sum - U.sum) hTUmem hx (by rwa [hval])
    · have hswapNonneg : 0 ≤ (ruzsaRepresentativeSum q lam U : ℤ) -
          ruzsaRepresentativeSum q lam T := by omega
      have hswapShort := ruzsaRepresentativeSum_sub_abs_lt lam hUcard hTcard hs
        (fun x hx => hmono x (hUA x hx)) (fun x hx => hmono x (hTA x hx))
      have hswapSmall :
          (((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T : ℤ)).natAbs < q := by
        have hwidthZ : ((s * (q / (2 * s) + 1) : ℕ) : ℤ) < q := by
          exact_mod_cast hwidth
        apply int_natAbs_lt_of_neg_lt_and_lt
        · exact (by omega : -(q : ℤ) <
            -((s * (q / (2 * s) + 1) : ℕ) : ℤ)).trans hswapShort.2
        · exact hswapShort.1.trans hwidthZ
      have hdiv : (M : ℤ) ∣
          ((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T) :=
        (ruzsaModelMap_sum_eq_iff_dvd q M lam U T).mp hmap.symm
      have hdivNat : M ∣ (((ruzsaRepresentativeSum q lam U : ℤ) -
          ruzsaRepresentativeSum q lam T : ℤ)).natAbs :=
        Int.natCast_dvd.mp hdiv
      have hval : (lam * ((U.sum - T.sum : ℤ) : ZMod q)).val =
          (((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T : ℤ)).natAbs := by
        apply zmod_val_eq_natAbs_of_nonneg hswapNonneg hswapSmall
        exact ruzsaRepresentativeSum_sub_cast q lam U T
      have hx' : U.sum - T.sum ≠ 0 := sub_ne_zero.mpr (Ne.symm hsum)
      exact hgood (U.sum - T.sum) hUTmem hx' (by rwa [hval])
  · intro hsum
    have hcast : ((((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U : ℤ) : ZMod q)) = 0 := by
      rw [ruzsaRepresentativeSum_sub_cast, hsum, sub_self, Int.cast_zero, mul_zero]
    have hdiv : (q : ℤ) ∣ ((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hcast
    have hzero : (ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
      simpa only [Int.natAbs_natCast] using hsmall
    have hrepeq : ruzsaRepresentativeSum q lam T =
        ruzsaRepresentativeSum q lam U := by omega
    rw [ruzsaModelMap_sum, ruzsaModelMap_sum, hrepeq]

theorem isAddFreimanIso_ruzsaModelMap
    {A : Finset ℤ} {s M q c : ℕ} [NeZero q] [NeZero M]
    (lam : ZMod q) (hs : 0 < s) (hq : 2 * s < q)
    (hmono : ∀ a ∈ A, ruzsaColor q s lam a = c)
    (hgood : ∀ x ∈ s • A - s • A, x ≠ 0 →
      ¬ (M ∣ (lam * (x : ZMod q)).val)) :
    IsAddFreimanIso s (A : Set ℤ)
      (A.image (ruzsaModelMap q M lam) : Set (ZMod M))
      (ruzsaModelMap q M lam) := by
  let f := ruzsaModelMap q M lam
  have hrel {T U : Multiset ℤ}
      (hTA : ∀ x ∈ T, x ∈ A) (hUA : ∀ x ∈ U, x ∈ A)
      (hTcard : T.card = s) (hUcard : U.card = s) :
      (T.map f).sum = (U.map f).sum ↔ T.sum = U.sum :=
    ruzsaModelMap_multiset_sum_eq_iff lam hs hq hmono hgood
      hTA hUA hTcard hUcard
  have hinj : Set.InjOn f (A : Set ℤ) := by
    intro a ha b hb hab
    have hrepl := hrel
      (T := Multiset.replicate s a) (U := Multiset.replicate s b)
      (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
      (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using hb)
      (by simp) (by simp)
    have hsum := hrepl.mp (by simp [f, hab])
    simp only [Multiset.sum_replicate, nsmul_eq_mul] at hsum
    have hsZ : (0 : ℤ) < s := by exact_mod_cast hs
    nlinarith
  refine ⟨⟨?_, hinj, ?_⟩, ?_⟩
  · intro a ha
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_coe.mp ha, rfl⟩)
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, Finset.mem_coe.mpr ha, rfl⟩
  · intro T U hTA hUA hTcard hUcard
    apply hrel
    · intro x hx
      exact Finset.mem_coe.mp (hTA hx)
    · intro x hx
      exact Finset.mem_coe.mp (hUA hx)
    · exact hTcard
    · exact hUcard

lemma exists_nonempty_large_color_fiber {A : Finset ℤ} {k : ℕ}
    (hA : A.Nonempty) (hk : 0 < k) (f : ℤ → ℕ)
    (hf : ∀ a ∈ A, f a < k) :
    ∃ c < k, let B := A.filter fun a => f a = c
      B.Nonempty ∧ A.card / k ≤ B.card := by
  classical
  by_cases hquot : A.card / k = 0
  · obtain ⟨a, ha⟩ := hA
    refine ⟨f a, hf a ha, ?_⟩
    dsimp
    constructor
    · exact ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
    · simp [hquot]
  · obtain ⟨c, hc, hcard⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := A) (t := Finset.range k) (f := f)
        (fun a ha => Finset.mem_range.mpr (hf a ha))
        ⟨0, Finset.mem_range.mpr hk⟩
        (by simpa using Nat.mul_div_le A.card k)
    refine ⟨c, Finset.mem_range.mp hc, ?_⟩
    dsimp
    exact ⟨Finset.card_pos.mp ((Nat.pos_of_ne_zero hquot).trans_le hcard), hcard⟩

/-- A multiplicative form of the same pigeonhole estimate.  This formulation
has no floor-error term and is the one needed to transfer density to the
cyclic Freiman model. -/
lemma exists_nonempty_large_color_fiber_mul {A : Finset ℤ} {k : ℕ}
    (hA : A.Nonempty) (hk : 0 < k) (f : ℤ → ℕ)
    (hf : ∀ a ∈ A, f a < k) :
    ∃ c < k, let B := A.filter fun a => f a = c
      B.Nonempty ∧ A.card ≤ k * B.card := by
  classical
  let n := (A.card - 1) / k
  have hApos : 0 < A.card := Finset.card_pos.mpr hA
  have hkn : k * n < A.card := by
    have hle : k * n ≤ A.card - 1 := by
      simpa only [n] using Nat.mul_div_le (A.card - 1) k
    omega
  obtain ⟨c, hc, hcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := A) (t := Finset.range k) (f := f)
      (fun a ha => Finset.mem_range.mpr (hf a ha)) (by simpa using hkn)
  refine ⟨c, Finset.mem_range.mp hc, ?_⟩
  dsimp
  have hceil : A.card - 1 < k * (n + 1) := by
    simpa only [n] using Nat.lt_mul_div_succ (A.card - 1) hk
  have hmul : k * (n + 1) ≤
      k * (A.filter fun a => f a = c).card := by
    exact Nat.mul_le_mul_left k (by omega)
  constructor
  · exact Finset.card_pos.mp ((Nat.zero_le n).trans_lt hcard)
  · have hpred : A.card - 1 + 1 = A.card :=
      Nat.sub_one_add_one hApos.ne'
    have hlt : A.card - 1 <
        k * (A.filter fun a => f a = c).card := hceil.trans_le hmul
    omega

theorem exists_large_cyclic_freiman_model (A : Finset ℤ) (s : ℕ)
    (hA : A.Nonempty) (hs : 0 < s) :
    let D := s • A - s • A
    ∃ (A' : Finset ℤ) (B : Finset (ZMod (2 * D.card)))
      (f : ℤ → ZMod (2 * D.card)),
      A'.Nonempty ∧ A' ⊆ A ∧ A.card ≤ (2 * s) * A'.card ∧
        B = A'.image f ∧ IsAddFreimanIso s (A' : Set ℤ) (B : Set _) f := by
  classical
  let D := s • A - s • A
  have hD : D.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have hsum : (Multiset.replicate s a).sum ∈ s • A := by
      simpa using multiset_sum_mem_nsmul A (T := Multiset.replicate s a)
        (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
    exact ⟨0, Finset.mem_sub.mpr ⟨_, hsum, _, hsum, sub_self _⟩⟩
  have hDcard : 0 < D.card := Finset.card_pos.mpr hD
  let R := D.sup Int.natAbs
  let K := max (max (4 * D.card) (2 * s)) R + 1
  obtain ⟨q, hKq, hqPrime⟩ := Nat.exists_infinite_primes K
  have h4q : 4 * D.card < q := by
    dsimp [K] at hKq
    omega
  have h2sq : 2 * s < q := by
    dsimp [K] at hKq
    omega
  have hRq : R < q := by
    dsimp [K] at hKq
    omega
  letI : Fact q.Prime := ⟨hqPrime⟩
  letI : NeZero q := ⟨hqPrime.ne_zero⟩
  obtain ⟨lam, hlam, hgood⟩ := exists_good_multiplier
    (D := D) (N := D.card) (q := q) hDcard le_rfl
    (fun x hx => (Finset.le_sup hx).trans_lt hRq) h4q
  obtain ⟨c, hc, hfiber⟩ :=
    exists_nonempty_large_color_fiber_mul hA (by omega)
      (ruzsaColor q s lam) (fun a _ha => ruzsaColor_lt lam hs h2sq a)
  let A' := A.filter fun a => ruzsaColor q s lam a = c
  have hA'ne : A'.Nonempty := hfiber.1
  have hA'card : A.card ≤ (2 * s) * A'.card := hfiber.2
  have hA'sub : A' ⊆ A := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hmono : ∀ a ∈ A', ruzsaColor q s lam a = c := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hsumSub : s • A' ⊆ s • A := by
    exact nsmul_le_nsmul_right hA'sub s
  have hdiffSub : s • A' - s • A' ⊆ D := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.mem_sub.mpr ⟨u, hsumSub hu, v, hsumSub hv, rfl⟩
  have hgood' : ∀ x ∈ s • A' - s • A', x ≠ 0 →
      ¬ (2 * D.card ∣ (lam * (x : ZMod q)).val) := by
    intro x hx hx0
    exact hgood x (hdiffSub hx) hx0
  have hM : 0 < 2 * D.card := by omega
  letI : NeZero (2 * D.card) := ⟨hM.ne'⟩
  let f : ℤ → ZMod (2 * D.card) := ruzsaModelMap q (2 * D.card) lam
  let B := A'.image f
  refine ⟨A', B, f, hA'ne, hA'sub, hA'card, rfl, ?_⟩
  exact isAddFreimanIso_ruzsaModelMap lam hs h2sq hmono hgood'

end Erdos587
