import ErdosProblems.Erdos360.Core
import ErdosProblems.Erdos360.WeightedGraph
import ErdosProblems.Erdos360.CosetContraction

/-!
# The rectified core of the corrected cyclic inverse theorem

This file isolates the part of the Deshouillers--Freiman alternative which
follows once the cyclic set has an order-two Freiman model in the natural
numbers.  It deliberately has no new unproved declaration: the
remaining cyclic argument has to construct the model (or enter one of the
low-layer subgroup exceptions).
-/

open scoped Pointwise

namespace Erdos360

/-- Once the graph-valued `3k-4` argument supplies generalized affine
structure, gcd normalization turns its common integer step into one.  This
small lemma is the exact algebraic last step of affine fibre alignment. -/
theorem affine_on_of_graphProgressionStructured_gcd_one
    {G : Type*} [AddCommGroup G] {A : Finset ℕ} {x : ℕ → G}
    (hzero : 0 ∈ A) (hgcd : A.gcd (fun n : ℕ ↦ n) = 1)
    (hgraph : GraphProgressionStructured A x) :
    ∃ u v : G, ∀ a ∈ A, x a = a • u + v := by
  classical
  obtain ⟨p, q, hpq, hgen, hgeneral⟩ := hgraph
  obtain ⟨r, hr⟩ := adjacent_of_progressionTernaryGenerates hzero hgcd
    ⟨p, q, hpq, hgen⟩
  exact affine_on_of_ternaryGenerates hr rfl
    (preservesPairSums_of_generalizedAffineOn hpq hgeneral)

/-! ## The ordered `51/25` theorem without the coarse cardinality cutoff -/

/-- At the actual CFP threshold, Ruzsa's normalized diameter estimate puts
every five-element integer set in an arithmetic progression of length at
most `52/25` times its cardinality.  The `30`-element cutoff in the older
`21/10` wrapper is only needed for that weaker numerical threshold. -/
theorem integer_small_sumset_contained_AP_51_25
    {S : Finset ℕ} (hSne : S.Nonempty) (hScard : 5 ≤ S.card)
    (hsmall : 25 * (S + S).card ≤ 51 * S.card) :
    ∃ a d L : ℕ, 0 < d ∧ 25 * L ≤ 52 * S.card ∧
      S ⊆ Erdos13Additive.natAP a d L := by
  classical
  let s := S.min' hSne
  let M := S.max' hSne
  let u := M - s
  have hsS : s ∈ S := S.min'_mem hSne
  have hMS : M ∈ S := S.max'_mem hSne
  have hsmin : ∀ x ∈ S, s ≤ x := fun x hx => S.min'_le x hx
  have hMmax : ∀ x ∈ S, x ≤ M := fun x hx => S.le_max' x hx
  have hupos : 0 < u := by
    by_contra hu
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos hu
    have hsM : s ≤ M := hsmin M hMS
    have hSM : s = M := by dsimp only [u] at hu0; omega
    have hsingle : S = {s} := by
      ext x
      constructor
      · intro hx
        simp only [Finset.mem_singleton]
        have := hsmin x hx
        have := hMmax x hx
        omega
      · intro hx
        simp only [Finset.mem_singleton] at hx
        subst x
        exact hsS
    have : S.card = 1 := by simp [hsingle]
    omega
  let S₁ := Erdos13Additive.normalizeNat S s 1
  let d := S₁.gcd (fun n : ℕ => n)
  have huS₁ : u ∈ S₁ := by
    have h := Erdos13Additive.top_mem_normalizeNat
      (m := s) (d := 1) hMS
    simpa [S₁, u, M, s] using h
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd
    have hz := (Finset.gcd_eq_zero_iff.mp hd) u huS₁
    omega
  have hdiv : ∀ x ∈ S, d ∣ x - s := by
    intro x hx
    apply Finset.gcd_dvd
    exact Erdos13Additive.mem_normalizeNat.mpr ⟨x, hx, by simp⟩
  have hdu : d ∣ u := Finset.gcd_dvd huS₁
  have hdule : d ≤ u := Nat.le_of_dvd hupos hdu
  have huqpos : 0 < u / d := Nat.div_pos hdule hdpos
  let A := Erdos13Additive.normalizeNat S s d
  have hAint : A ⊆ Finset.Icc 0 (u / d) := by
    apply Erdos13Additive.normalizeNat_subset_Icc
    intro x hx
    exact Finset.mem_Icc.mpr ⟨hsmin x hx, hMmax x hx⟩
  have hAzero : 0 ∈ A := Erdos13Additive.zero_mem_normalizeNat hsS
  have hAtop : u / d ∈ A := by
    simpa [A, u, M, s] using
      (Erdos13Additive.top_mem_normalizeNat (m := s) (d := d) hMS)
  have hAeq : A = S₁.image (fun z => z / d) := by
    ext q
    simp only [A, S₁, Erdos13Additive.normalizeNat,
      Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x - s, ⟨x, hx, by simp⟩, rfl⟩
    · rintro ⟨z, ⟨x, hx, hxz⟩, rfl⟩
      exact ⟨x, hx, by simpa using congrArg (fun n => n / d) hxz⟩
  have hS₁gcd : S₁.gcd (fun z => z / d) = 1 := by
    exact Finset.gcd_div_id_eq_one huS₁ hupos.ne'
  have hAgcdNat : A.gcd (fun n : ℕ => n) = 1 := by
    rw [hAeq, Finset.gcd_image]
    exact hS₁gcd
  have hAgcdInt : A.gcd (fun n => (n : ℤ)) = 1 := by
    rw [Erdos13Additive.nat_int_finset_gcd, hAgcdNat]
    norm_num
  have hAcard : A.card = S.card :=
    Erdos13Additive.card_normalizeNat hdpos hsmin hdiv
  have hsumcard : (A + A).card = (S + S).card := by
    symm
    exact Erdos13Additive.card_sumset_eq_card_normalized
      hdpos hsmin hsmin hdiv hdiv
  have hruzsa := Erdos13Additive.ruzsa_normalized_diameter_bound
    hAint hAint (le_refl (u / d)) huqpos hAzero hAtop hAzero hAtop
      (by simpa using hAgcdInt)
  have hthree : (A + A).card < 3 * S.card - 3 := by
    rw [hsumcard]
    omega
  have hdiameter : S.card + u / d ≤ (A + A).card := by
    by_contra hnot
    have hfirst : (A + A).card < S.card + u / d :=
      Nat.lt_of_not_ge hnot
    have hsecond : (A + A).card <
        A.card + A.card + min A.card A.card - 3 := by
      rw [hAcard]
      simp only [min_self]
      omega
    have : (A + A).card < min (A.card + u / d)
        (A.card + A.card + min A.card A.card - 3) := by
      apply lt_min
      · simpa [hAcard] using hfirst
      · exact hsecond
    exact (not_lt_of_ge hruzsa) this
  have hL : 25 * (u / d + 1) ≤ 52 * S.card := by
    rw [hsumcard] at hdiameter
    omega
  refine ⟨s, d, u / d + 1, hdpos, hL, ?_⟩
  intro x hx
  have hqmem : (x - s) / d ∈ A :=
    Erdos13Additive.mem_normalizeNat.mpr ⟨x, hx, rfl⟩
  have hqle : (x - s) / d ≤ u / d :=
    (Finset.mem_Icc.mp (hAint hqmem)).2
  apply Erdos13Additive.mem_natAP.mpr
  refine ⟨(x - s) / d, by omega, ?_⟩
  calc
    s + d * ((x - s) / d) = s + (x - s) := by
      rw [Nat.mul_div_cancel' (hdiv x hx)]
    _ = x := Nat.add_sub_of_le (hsmin x hx)

/-- At the `51/25` threshold a rectified cyclic set lies in a proper cyclic
coset progression whose displayed mass is at most `6/5` of the set.  This is
the quantitative core of the corrected Deshouillers--Freiman alternative. -/
theorem modeled_cyclicCosetProgression_of_doubling_51_25
    {t : ℕ} [NeZero t] {B : Finset (ZMod t)}
    (hmodel : HasNatFreimanModel B) (hcard : 30 ≤ B.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card) :
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      B ⊆ cyclicCosetProgression H a d L ∧
      IsProperCyclicCosetProgression H a d L ∧
      5 * (L * Nat.card H) ≤ 6 * B.card := by
  have hsmall' : 10 * (B + B).card ≤ 21 * B.card := by
    omega
  obtain ⟨H, a, d, L, hB, hproper, hcase⟩ :=
    natFreimanModel_cyclic_progression_dichotomy hmodel hcard hsmall'
  refine ⟨H, a, d, L, hB, hproper, ?_⟩
  rcases hcase with ⟨rfl, hL⟩ | ⟨rfl, hH⟩
  · simp only [Nat.card_eq_fintype_card, Fintype.card_ofSubsingleton,
      mul_one]
    omega
  · simpa using hH

/-- The sharp `6/5` modeled bound implies the slightly weaker `52/25`
mass convention used by CFP. -/
theorem modeled_cyclicCosetProgression_of_doubling_51_25_cfpMass
    {t : ℕ} [NeZero t] {B : Finset (ZMod t)}
    (hmodel : HasNatFreimanModel B) (hcard : 30 ≤ B.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card) :
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      B ⊆ cyclicCosetProgression H a d L ∧
      IsProperCyclicCosetProgression H a d L ∧
      25 * (L * Nat.card H) ≤ 52 * B.card := by
  obtain ⟨H, a, d, L, hB, hproper, hmass⟩ :=
    modeled_cyclicCosetProgression_of_doubling_51_25 hmodel hcard hsmall
  refine ⟨H, a, d, L, hB, hproper, ?_⟩
  nlinarith only [hmass]

/-- The same CFP mass conclusion needs only five modeled elements.  This
form deliberately does not assert properness: ambient sparsity, used below,
is the cleaner way to obtain the half-quotient condition needed for
contraction. -/
theorem modeled_cyclicCosetProgression_of_doubling_51_25_cfpMass_five
    {t : ℕ} [NeZero t] {B : Finset (ZMod t)}
    (hmodel : HasNatFreimanModel B) (hcard : 5 ≤ B.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card) :
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      B ⊆ cyclicCosetProgression H a d L ∧
      25 * (L * Nat.card H) ≤ 52 * B.card := by
  obtain ⟨A, hAne, hAcard, hAB, hsum⟩ := hmodel
  obtain ⟨a, d, L, _hd, hL, hAprog⟩ :=
    integer_small_sumset_contained_AP_51_25 hAne
      (by simpa [hAcard] using hcard)
      (by simpa [hsum, hAcard] using hsmall)
  refine ⟨⊥, (a : ZMod t), (d : ZMod t), L, ?_, ?_⟩
  · intro x hx
    rw [← hAB] at hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact zmodNatAP_subset_cyclicCosetProgression_bot
      (Finset.mem_image.mpr ⟨y, hAprog hy, rfl⟩)
  · simpa only [Nat.card_eq_fintype_card,
      Fintype.card_ofSubsingleton, mul_one, hAcard] using hL

/-- A no-wrap cyclic set is a concrete rectified set, so the modeled
`51/25` theorem applies without any abstract Freiman-model hypothesis. -/
theorem noWrap_cyclicCosetProgression_of_doubling_51_25
    {t : ℕ} [NeZero t] {B : Finset (ZMod t)}
    (hB : B.Nonempty) (hnowrap : ∀ x ∈ B, 2 * x.val < t)
    (hcard : 30 ≤ B.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card) :
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      B ⊆ cyclicCosetProgression H a d L ∧
      IsProperCyclicCosetProgression H a d L ∧
      25 * (L * Nat.card H) ≤ 52 * B.card := by
  exact modeled_cyclicCosetProgression_of_doubling_51_25_cfpMass
    (hasNatFreimanModel_of_double_val_lt hB hnowrap) hcard hsmall

/-- Exact CFP local output after rectification.  The two nontrivial side
conditions on the inverse progression are not assumptions: ambient sparsity
gives the half-quotient bound, while generation of the original summand gives
the lower bound on its length. -/
theorem modeled_iterated_cyclicDF_longAlternative
    {t k : ℕ} [NeZero t] {P B : Finset (ZMod t)}
    (hzero : 0 ∈ P) (hk : 0 < k)
    (hclosure : AddSubgroup.closure (P : Set (ZMod t)) = ⊤)
    (hB : B = iteratedFinsetSum P k)
    (hmodel : HasNatFreimanModel B) (hcard : 5 ≤ B.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 104 * B.card < 25 * t) :
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      k ≤ L ∧
      2 * L ≤ Nat.card (ZMod t ⧸ H) ∧
      B ⊆ cyclicCosetProgression H a d L ∧
      25 * (L * Nat.card H) ≤ 52 * B.card := by
  obtain ⟨H, a, d, L, hprog, hmass⟩ :=
    modeled_cyclicCosetProgression_of_doubling_51_25_cfpMass_five
      hmodel hcard hsmall
  have hhalf : 2 * L ≤ Nat.card (ZMod t ⧸ H) :=
    quotient_half_of_progression_mass_and_sparse H hmass hsparse
  have hsum : iteratedFinsetSum P k ⊆
      cyclicCosetProgression H a d L := by
    simpa [hB] using hprog
  have hkL : k ≤ L :=
    k_le_length_of_generating_cyclic_coset_iterated_subset
      H a d hzero hk hclosure hhalf hsum
  exact ⟨H, a, d, L, hkL, hhalf, hprog, hmass⟩

/-- The same exact local output with the no-wrap condition used to construct
the required Freiman model. -/
theorem noWrap_iterated_cyclicDF_longAlternative
    {t k : ℕ} [NeZero t] {P B : Finset (ZMod t)}
    (hzero : 0 ∈ P) (hk : 0 < k)
    (hclosure : AddSubgroup.closure (P : Set (ZMod t)) = ⊤)
    (hB : B = iteratedFinsetSum P k) (hBne : B.Nonempty)
    (hnowrap : ∀ x ∈ B, 2 * x.val < t)
    (hcard : 5 ≤ B.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 104 * B.card < 25 * t) :
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      k ≤ L ∧
      2 * L ≤ Nat.card (ZMod t ⧸ H) ∧
      B ⊆ cyclicCosetProgression H a d L ∧
      25 * (L * Nat.card H) ≤ 52 * B.card := by
  exact modeled_iterated_cyclicDF_longAlternative hzero hk hclosure hB
    (hasNatFreimanModel_of_double_val_lt hBne hnowrap) hcard hsmall hsparse

/-- The modeled theorem in precisely the proper-subgroup-or-long-progression
shape consumed at a slow dyadic scale.  Notice that the proper-subgroup
branch concerns the original summand `P`, rather than merely its iterated
sumset.  Thus the only additional input compared with the desired raw cyclic
theorem is the honest order-two model of `B` (and the harmless finite-size
cutoff used by the integer `3k-4` theorem). -/
theorem modeled_iterated_cyclicDF_localAlternative
    {t k : ℕ} [NeZero t] {P B : Finset (ZMod t)}
    (hzero : 0 ∈ P) (hk : 0 < k)
    (hB : B = iteratedFinsetSum P k)
    (hmodel : HasNatFreimanModel B) (hcard : 5 ≤ B.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 104 * B.card < 25 * t) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      (P : Set (ZMod t)) ⊆ (K : Set (ZMod t))) ∨
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      k ≤ L ∧
      2 * L ≤ Nat.card (ZMod t ⧸ H) ∧
      B ⊆ cyclicCosetProgression H a d L ∧
      25 * (L * Nat.card H) ≤ 52 * B.card := by
  classical
  by_cases hclosure : AddSubgroup.closure (P : Set (ZMod t)) = ⊤
  · exact Or.inr (modeled_iterated_cyclicDF_longAlternative
      hzero hk hclosure hB hmodel hcard hsmall hsparse)
  · exact Or.inl ⟨AddSubgroup.closure (P : Set (ZMod t)), hclosure,
      AddSubgroup.subset_closure⟩

/-- Concrete no-wrap specialization of the exact local-alternative
interface. -/
theorem noWrap_iterated_cyclicDF_localAlternative
    {t k : ℕ} [NeZero t] {P B : Finset (ZMod t)}
    (hzero : 0 ∈ P) (hk : 0 < k)
    (hB : B = iteratedFinsetSum P k) (hBne : B.Nonempty)
    (hnowrap : ∀ x ∈ B, 2 * x.val < t)
    (hcard : 5 ≤ B.card)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 104 * B.card < 25 * t) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      (P : Set (ZMod t)) ⊆ (K : Set (ZMod t))) ∨
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      k ≤ L ∧
      2 * L ≤ Nat.card (ZMod t ⧸ H) ∧
      B ⊆ cyclicCosetProgression H a d L ∧
      25 * (L * Nat.card H) ≤ 52 * B.card := by
  exact modeled_iterated_cyclicDF_localAlternative hzero hk hB
    (hasNatFreimanModel_of_double_val_lt hBne hnowrap) hcard hsmall hsparse

/-- At a four-fold (hence every CFP dyadic) scale, generation and ambient
sparsity force the five elements needed by the sharp ordered theorem.  This
removes the last cardinality hypothesis from the modeled local alternative. -/
theorem modeled_iterated_cyclicDF_localAlternative_four
    {t k : ℕ} [NeZero t] {P B : Finset (ZMod t)}
    (hzero : 0 ∈ P) (hk : 4 ≤ k)
    (hB : B = iteratedFinsetSum P k)
    (hmodel : HasNatFreimanModel B)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 104 * B.card < 25 * t) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      (P : Set (ZMod t)) ⊆ (K : Set (ZMod t))) ∨
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      k ≤ L ∧
      2 * L ≤ Nat.card (ZMod t ⧸ H) ∧
      B ⊆ cyclicCosetProgression H a d L ∧
      25 * (L * Nat.card H) ≤ 52 * B.card := by
  classical
  by_cases hclosure : AddSubgroup.closure (P : Set (ZMod t)) = ⊤
  · have hPne : P.Nonempty := ⟨0, hzero⟩
    have hBne : B.Nonempty := by
      rw [hB]
      exact iteratedFinsetSum_nonempty hPne k
    have htlarge : 5 ≤ t := by
      have hBpos : 0 < B.card := Finset.card_pos.mpr hBne
      omega
    have hPcard : 2 ≤ P.card := by
      by_contra hnot
      have hPle : P.card ≤ 1 := by omega
      have hPeq : P = {0} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hzero, ?_⟩
        intro x hx
        exact Finset.card_le_one.mp hPle x hx 0 hzero
      have hbotTop : (⊥ : AddSubgroup (ZMod t)) = ⊤ := by
        calc
          (⊥ : AddSubgroup (ZMod t)) =
              AddSubgroup.closure ((P : Finset (ZMod t)) : Set (ZMod t)) := by
                rw [hPeq]
                rw [Finset.coe_singleton]
                exact AddSubgroup.closure_singleton_zero.symm
          _ = ⊤ := hclosure
      have hsubsingleton : Subsingleton (ZMod t) := by
        constructor
        intro x y
        have hx : x ∈ (⊥ : AddSubgroup (ZMod t)) := by rw [hbotTop]; simp
        have hy : y ∈ (⊥ : AddSubgroup (ZMod t)) := by rw [hbotTop]; simp
        simpa using hx.trans hy.symm
      have htone : Fintype.card (ZMod t) ≤ 1 :=
        Fintype.card_le_one_iff_subsingleton.mpr hsubsingleton
      have : t ≤ 1 := by simpa using htone
      omega
    have hcoset : NotContainedInProperCoset P :=
      notContainedInProperCoset_of_zero_mem_closure_eq_top hzero hclosure
    have hgrowth :=
      min_group_card_iteratedFinsetSum_lower_of_notContainedInProperCoset
        hPne hcoset k (by omega)
    have htarget : (k + 1) * P.card ≤ 2 * B.card := by
      have hBlt : 2 * B.card < 2 * Fintype.card (ZMod t) := by
        simpa using (show 2 * B.card < 2 * t by omega)
      rcases le_total (2 * Fintype.card (ZMod t))
          ((k + 1) * P.card) with hgroup | htargetGroup
      · have hgrowth' := hgrowth
        rw [min_eq_left hgroup] at hgrowth'
        rw [hB] at hBlt
        omega
      · have hgrowth' := hgrowth
        rw [min_eq_right htargetGroup] at hgrowth'
        rw [hB]
        exact hgrowth'
    have hBcard : 5 ≤ B.card := by
      nlinarith only [hk, hPcard, htarget]
    exact Or.inr (modeled_iterated_cyclicDF_longAlternative
      hzero (by omega) hclosure hB hmodel hBcard hsmall hsparse)
  · exact Or.inl ⟨AddSubgroup.closure (P : Set (ZMod t)), hclosure,
      AddSubgroup.subset_closure⟩

/-- No-wrap version of the cardinality-free four-fold local alternative. -/
theorem noWrap_iterated_cyclicDF_localAlternative_four
    {t k : ℕ} [NeZero t] {P B : Finset (ZMod t)}
    (hzero : 0 ∈ P) (hk : 4 ≤ k)
    (hB : B = iteratedFinsetSum P k) (hBne : B.Nonempty)
    (hnowrap : ∀ x ∈ B, 2 * x.val < t)
    (hsmall : 25 * (B + B).card ≤ 51 * B.card)
    (hsparse : 104 * B.card < 25 * t) :
    (∃ K : AddSubgroup (ZMod t), K ≠ ⊤ ∧
      (P : Set (ZMod t)) ⊆ (K : Set (ZMod t))) ∨
    ∃ H : AddSubgroup (ZMod t), ∃ a d : ZMod t, ∃ L : ℕ,
      k ≤ L ∧
      2 * L ≤ Nat.card (ZMod t ⧸ H) ∧
      B ⊆ cyclicCosetProgression H a d L ∧
      25 * (L * Nat.card H) ≤ 52 * B.card := by
  exact modeled_iterated_cyclicDF_localAlternative_four hzero hk hB
    (hasNatFreimanModel_of_double_val_lt hBne hnowrap) hsmall hsparse

end Erdos360

#print axioms Erdos360.integer_small_sumset_contained_AP_51_25
#print axioms Erdos360.modeled_cyclicCosetProgression_of_doubling_51_25
#print axioms Erdos360.modeled_cyclicCosetProgression_of_doubling_51_25_cfpMass_five
#print axioms Erdos360.noWrap_cyclicCosetProgression_of_doubling_51_25
#print axioms Erdos360.modeled_iterated_cyclicDF_longAlternative
#print axioms Erdos360.modeled_iterated_cyclicDF_localAlternative
#print axioms Erdos360.modeled_iterated_cyclicDF_localAlternative_four
