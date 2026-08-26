import ErdosProblems.Erdos336.MinimalV3StrongNineTenthsPartialRectification
import ErdosProblems.Erdos336.NineTenthsSixFibers
import ErdosProblems.Erdos336.HighPowerExceptionalDense
import ErdosProblems.Erdos336.ConditionalStableV3Structure

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

/-- The rank-one conclusion, in a finset form convenient for applying an
inverse theorem to a large subset which is not itself an exact power. -/
def FinsetRankCertificate {N : ℕ} [NeZero N] (A : Finset (ZMod N)) : Prop :=
  ∃ (m : ℕ) (hm : 0 < m),
    let _ : NeZero m := ⟨hm.ne'⟩
    ∃ (π : ZMod N →+ ZMod m), Function.Surjective π ∧
      ∃ (α : ZMod m) (L V : ℕ),
        0 < L ∧
        (∀ x ∈ A, ∃ k : ℕ, k ≤ L ∧ π x = α + (k : ZMod m)) ∧
        (∀ z : ZMod m, (homFiberFinset π z).card ≤ V) ∧
        A.card + L * V ≤ (A + A).card

/-- A finset affinely generates its ambient group if it is not contained in
a coset of any proper subgroup.  This is the precise hypothesis which makes
the progression direction generate the quotient in the rectifiable theorem. -/
def FinsetAffineGenerates {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) : Prop :=
  ∀ (H : AddSubgroup G) (b : G),
    (∀ x ∈ A, x - b ∈ H) → H = ⊤

/-- Isolated classical input: the rectifiable `3n-3` theorem with finite
fibres.  Its hypothesis says that `A` affinely generates the source and lies,
under a cyclic quotient, over a strict half-interval.  The threshold is the
exact moderate-torsion threshold determined by the number `s` of occupied
fibres. -/
def HasRectifiableThreeMinusThree : Prop :=
  ∀ (N : ℕ) (hN : 0 < N),
    let _ : NeZero N := ⟨hN.ne'⟩
    ∀ (A : Finset (ZMod N)), A.Nonempty → FinsetAffineGenerates A →
      ∀ (m : ℕ) (hm : 0 < m),
        let _ : NeZero m := ⟨hm.ne'⟩
        ∀ (π : ZMod N →+ ZMod m), Function.Surjective π →
          ∀ α : ZMod m,
            (∀ x ∈ A, ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m)) →
            (A.image π).card * (A + A).card <
              3 * ((A.image π).card - 1) * A.card →
            FinsetRankCertificate A

variable {N : ℕ} [NeZero N]

/-- A finset rank certificate is exactly the first branch of the structural
certificate after coercing the finset to a set. -/
theorem rankExceptionalCertificate_of_finsetRankCertificate
    (A : Finset (ZMod N)) (hA : FinsetRankCertificate A) :
    RankExceptionalCertificate (A : Set (ZMod N)) := by
  rcases hA with ⟨m, hm, π, hπ, α, L, V, hL, houter, hfiber, hcost⟩
  left
  refine ⟨m, hm, π, hπ, α, L, V, hL, ?_, hfiber, ?_⟩
  · intro x hx
    exact houter x hx
  · rw [exactPower_eq_nsmul, two_nsmul]
    have heq : ((A : Set (ZMod N)) + (A : Set (ZMod N))).ncard =
        (A + A).card := by
      rw [← Finset.coe_add, Set.ncard_coe_finset]
    rw [heq, Set.ncard_coe_finset]
    exact hcost

/-- If `B` lies over a quotient interval of span `L`, then every element of
`2B-B` lies over the translated interval of span `3L`. -/
theorem image_interval_of_subset_two_sub_one
    {m : ℕ} [NeZero m] (π : ZMod N →+ ZMod m)
    {A B : Finset (ZMod N)} {α : ZMod m} {L : ℕ}
    (hcover : A ⊆ (B + B) - B)
    (houter : ∀ x ∈ B, ∃ k : ℕ, k ≤ L ∧ π x = α + (k : ZMod m)) :
    ∀ x ∈ A, ∃ q : ℕ, q ≤ 3 * L ∧
      π x = (α - (L : ZMod m)) + (q : ZMod m) := by
  intro x hx
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp (hcover hx)
  obtain ⟨b₁, hb₁, b₂, hb₂, hb₁b₂⟩ := Finset.mem_add.mp hu
  obtain ⟨i, hi, hπi⟩ := houter b₁ hb₁
  obtain ⟨j, hj, hπj⟩ := houter b₂ hb₂
  obtain ⟨k, hk, hπk⟩ := houter v hv
  refine ⟨i + j + (L - k), by omega, ?_⟩
  rw [← huv, ← hb₁b₂, map_sub, map_add, hπi, hπj, hπk]
  push_cast [Nat.cast_sub hk]
  ring

/-- A primitive zero-containing root makes its positive exact power
an affine generating set. -/
theorem finsetAffineGenerates_exactPower
    (C : Set (ZMod N)) {t : ℕ} (ht : 0 < t) (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ) :
    FinsetAffineGenerates (exactPowerFinset C t) := by
  intro H b hcos
  have hzA : 0 ∈ exactPowerFinset C t := by
    rw [mem_exactPowerFinset]
    refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
    intro y hy
    rw [List.mem_replicate] at hy
    simpa [hy.2] using hzero
  have hnegb : -b ∈ H := by
    simpa using hcos 0 hzA
  have hb : b ∈ H := by simpa using H.neg_mem hnegb
  have hC : C ⊆ H := by
    intro c hc
    have hcA : c ∈ exactPowerFinset C t := by
      rw [mem_exactPowerFinset]
      have hc1 : c ∈ ExactPower C 1 :=
        ⟨[c], by simp, by simpa, by simp⟩
      exact exactPower_mono_of_zero hzero (by omega) hc1
    have hcH := H.add_mem (hcos c hcA) hb
    simpa using hcH
  obtain ⟨q, hq⟩ := hprimitive
  rw [AddSubgroup.eq_top_iff']
  intro x
  have hx : x ∈ ExactPower C q := by rw [hq]; simp
  obtain ⟨xs, _hlen, hxs, hxsum⟩ := hx
  rw [← hxsum]
  exact H.list_sum_mem fun y hy => hC (hxs y hy)

/-- If `A` is a primitive affine-generating power and `A ⊆ 2B-B`, then the
large slice `B` also affinely generates the whole group. -/
theorem finsetAffineGenerates_of_subset_two_sub_one
    (C : Set (ZMod N)) {t : ℕ} (ht : 0 < t) (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    {B : Finset (ZMod N)}
    (hcover : exactPowerFinset C t ⊆ (B + B) - B) :
    FinsetAffineGenerates B := by
  intro H b hcos
  have hAcos : ∀ x ∈ exactPowerFinset C t, x - b ∈ H := by
    intro x hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp (hcover hx)
    obtain ⟨b₁, hb₁, b₂, hb₂, hb₁b₂⟩ := Finset.mem_add.mp hu
    have h₁ := hcos b₁ hb₁
    have h₂ := hcos b₂ hb₂
    have h₃ := hcos v hv
    rw [← huv, ← hb₁b₂]
    have := H.sub_mem (H.add_mem h₁ h₂) h₃
    convert this using 1 <;> abel
  have hzA : 0 ∈ exactPowerFinset C t := by
    rw [mem_exactPowerFinset]
    refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
    intro y hy
    rw [List.mem_replicate] at hy
    simpa [hy.2] using hzero
  have hnegb : -b ∈ H := by simpa using hAcos 0 hzA
  have hb : b ∈ H := by simpa using H.neg_mem hnegb
  have hC : C ⊆ H := by
    intro c hc
    have hcA : c ∈ exactPowerFinset C t := by
      rw [mem_exactPowerFinset]
      have hc1 : c ∈ ExactPower C 1 :=
        ⟨[c], by simp, by simpa, by simp⟩
      exact exactPower_mono_of_zero hzero (by omega) hc1
    have hcH := H.add_mem (hAcos c hcA) hb
    simpa using hcH
  obtain ⟨q, hq⟩ := hprimitive
  rw [AddSubgroup.eq_top_iff']
  intro x
  have hx : x ∈ ExactPower C q := by rw [hq]; simp
  obtain ⟨xs, _hlen, hxs, hxsum⟩ := hx
  rw [← hxsum]
  exact H.list_sum_mem fun y hy => hC (hxs y hy)

/-- The isolated rectifiable theorem closes a minimal V3 counterexample.
The first application, to the nine-tenths slice, gives a progression of span
`L`.  The covering `A ⊆ 2B-B` then gives span `3L` for the whole high power.
The V3 sparsity alternative forces `6L` below the new quotient modulus, so a
second rectifiable application gives the required rank certificate for `A`. -/
theorem stableV3_of_rectifiableThreeMinusThree_of_smaller
    (hrect : HasRectifiableThreeMinusThree)
    (C : Set (ZMod N)) (t : ℕ) (ht : 237 ≤ t)
    (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hsmaller : ∀ (m : ℕ) (hm : 0 < m),
      let _ : NeZero m := ⟨hm.ne'⟩
      m < N →
        ∀ (D : Set (ZMod m)), 0 ∈ D →
          7 ≤ (ExactPower D t).ncard →
          (∃ q : ℕ, ExactPower D q = Set.univ) →
          4 * (ExactPower D (2 * t)).ncard <
            9 * (ExactPower D t).ncard →
          StableHighPowerCertificateV3 D t) :
    StableHighPowerCertificateV3 C t := by
  by_contra hnot
  let S : Set (ZMod N) := ExactPower C t
  let A : Finset (ZMod N) := exactPowerFinset C t
  let a : ℕ := A.card
  let d : ℕ := (A + A).card
  have hnotfull : S ≠ Set.univ := by
    intro hfull
    apply hnot
    change Fintype.card (ZMod N) = 1 ∨
      Fintype.card (ZMod N) < (10000000 * Nat.factorial 36) * stableWeight S ∨
      RankExceptionalCertificate S
    by_cases hN1 : N = 1
    · left
      simpa using hN1
    · right
      left
      have hN2 : 2 ≤ N := by have := NeZero.pos N; omega
      have hU2 : ExactPower (Set.univ : Set (ZMod N)) 2 = Set.univ := by
        rw [exactPower_eq_nsmul, two_nsmul]
        simp
      rw [ZMod.card]
      unfold stableWeight
      rw [hfull, hU2]
      have hcardU : (Set.univ : Set (ZMod N)).ncard = N := by
        simp [Nat.card_eq_fintype_card]
      rw [hcardU]
      simp only [Nat.sub_self, add_zero]
      have hK3 : 3 ≤ 10000000 * Nat.factorial 36 := by
        norm_num [Nat.factorial]
      have hmul := Nat.mul_le_mul_right (N - 1) hK3
      omega
  have hlarge := add_one_le_ncard_exactPower_of_not_full
    hzero hprimitive t hnotfull
  have ha238 : 238 ≤ a := by
    dsimp [a, A]
    rw [card_exactPowerFinset]
    omega
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨m, hm, π, hπ, hm37, B, hBA, hdense, hcover, α, hhalf⟩ :=
    minimalV3_counterexample_strong_nine_tenths_partial_rectification
      C t ht hzero hprimitive hdoub hnot hsmaller
  letI : NeZero m := ⟨hm.ne'⟩
  have hBne : B.Nonempty := by
    rw [← Finset.card_pos]
    have : 0 < a := by omega
    simpa [a, A] using (show 0 < B.card by omega)
  have hdoubFin : 4 * (exactPowerFinset C (2 * t)).card <
      9 * (exactPowerFinset C t).card := by
    simpa [card_exactPowerFinset] using hdoub
  have hr6 : 6 ≤ (B.image π).card :=
    six_le_card_image_of_nine_tenths_highPower C t (by omega) hzero
      hprimitive π hπ hm37 B hBA hdense hdoubFin
  have hBBsub : B + B ⊆ A + A :=
    Finset.add_subset_add hBA hBA
  have hBBle : (B + B).card ≤ d := by
    simpa [d] using Finset.card_le_card hBBsub
  have hdoub' : 4 * d < 9 * a := by
    simpa [d, a, A, exactPowerFinset_add_self] using hdoub
  have hdense' : 9 * a < 10 * B.card := by
    simpa [a, A] using hdense
  have hBthreshold :
      (B.image π).card * (B + B).card <
        3 * ((B.image π).card - 1) * B.card := by
    let r : ℕ := (B.image π).card
    let e : ℕ := (B + B).card
    have hrpos : 0 < r := by omega
    have h2BB : 2 * e < 5 * B.card := by
      dsimp [e]
      omega
    have hcoef : 5 * r ≤ 6 * (r - 1) := by omega
    have hcoefMul := Nat.mul_le_mul_right B.card hcoef
    have hscaled : 2 * (r * e) <
        2 * (3 * (r - 1) * B.card) := by
      calc
        2 * (r * e) = r * (2 * e) := by ring
        _ < r * (5 * B.card) := (Nat.mul_lt_mul_left hrpos).2 h2BB
        _ = (5 * r) * B.card := by ring
        _ ≤ (6 * (r - 1)) * B.card := hcoefMul
        _ = 2 * (3 * (r - 1) * B.card) := by ring
    change r * e < 3 * (r - 1) * B.card
    exact Nat.lt_of_mul_lt_mul_left hscaled
  have hBaff : FinsetAffineGenerates B :=
    finsetAffineGenerates_of_subset_two_sub_one C (by omega) hzero
      hprimitive hcover
  have hBrank : FinsetRankCertificate B :=
    hrect N (NeZero.pos N) B hBne hBaff m hm π hπ α hhalf hBthreshold
  rcases hBrank with
    ⟨n, hn, ρ, hρ, β, L, V, hL, hBouter, hfiber, hBcost⟩
  letI : NeZero n := ⟨hn.ne'⟩
  have hAouterRaw := image_interval_of_subset_two_sub_one ρ hcover hBouter
  have hzA : 0 ∈ A := by
    rw [mem_exactPowerFinset]
    refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
    intro y hy
    rw [List.mem_replicate] at hy
    simpa [hy.2] using hzero
  have hAleD : a ≤ d := by
    have hsub : A ⊆ A + A := by
      intro x hx
      exact Finset.mem_add.mpr ⟨x, hx, 0, hzA, by simp⟩
    simpa [a, d] using Finset.card_le_card hsub
  have hAcard : A.card = S.ncard := by
    simp [A, S, card_exactPowerFinset]
  have hdcard : d = (ExactPower S 2).ncard := by
    rw [exactPower_eq_nsmul, two_nsmul]
    have heq : ((A : Set (ZMod N)) + (A : Set (ZMod N))).ncard =
        (A + A).card := by
      rw [← Finset.coe_add, Set.ncard_coe_finset]
    calc
      d = (A + A).card := rfl
      _ = ((A : Set (ZMod N)) + (A : Set (ZMod N))).ncard := heq.symm
      _ = (S + S).ncard := by simp [A, S, coe_exactPowerFinset]
  have hweight : stableWeight S = d - 1 := by
    unfold stableWeight
    rw [← hAcard, ← hdcard]
    omega
  have hnotDense : ¬ Fintype.card (ZMod N) <
      (10000000 * Nat.factorial 36) * stableWeight S := by
    intro hdenseGlobal
    exact hnot (Or.inr (Or.inl hdenseGlobal))
  have hNlower : (10000000 * Nat.factorial 36) * (d - 1) ≤ N := by
    rw [hweight] at hnotDense
    rw [ZMod.card] at hnotDense
    omega
  have hM7 : 7 ≤ 10000000 * Nat.factorial 36 := by
    norm_num [Nat.factorial]
  have h7lower : 7 * (d - 1) ≤ N :=
    le_trans (Nat.mul_le_mul_right (d - 1) hM7) hNlower
  have h6dN : 6 * d < N := by omega
  have hNfiber : N ≤ n * V := by
    have hc := card_le_modulus_mul_of_fiber_bound hn ρ hfiber
    simpa [ZMod.card] using hc
  have hLVd : L * V ≤ d := by omega
  have h6Ln : 6 * L < n := by
    by_contra hbad
    have hn6L : n ≤ 6 * L := by omega
    have hmul : n * V ≤ (6 * L) * V :=
      Nat.mul_le_mul_right V hn6L
    have hsmall : n * V ≤ 6 * d := by
      calc
        n * V ≤ (6 * L) * V := hmul
        _ = 6 * (L * V) := by ring
        _ ≤ 6 * d := Nat.mul_le_mul_left 6 hLVd
    omega
  have hAhalf : ∀ x ∈ A, ∃ q : ℕ, 2 * q < n ∧
      ρ x = (β - (L : ZMod n)) + (q : ZMod n) := by
    intro x hx
    obtain ⟨q, hq, hρq⟩ := hAouterRaw x hx
    refine ⟨q, ?_, hρq⟩
    omega
  let s : ℕ := (A.image ρ).card
  have hs4 : 4 ≤ s := by
    by_contra hbad
    have hs3 : s ≤ 3 := by omega
    let D : Set (ZMod n) := ρ '' C
    have hzD : 0 ∈ D := ⟨0, hzero, ρ.map_zero⟩
    have hpD : ∃ u : ℕ, ExactPower D u = Set.univ :=
      exactPower_univ_image_of_surjective ρ hρ hprimitive
    have himageA : A.image ρ = exactPowerFinset D t := by
      simpa [A, D] using image_exactPowerFinset ρ C t
    have hsmallD : (ExactPower D t).ncard ≤ s := by
      rw [← card_exactPowerFinset, ← himageA]
    have hst : s ≤ t := by omega
    have hnle : n ≤ s := by
      have hc := card_le_of_highPower_ncard_le hzD hpD hst hsmallD
      simpa [ZMod.card] using hc
    omega
  have hAthreshold :
      (A.image ρ).card * (A + A).card <
        3 * ((A.image ρ).card - 1) * A.card := by
    have hspos : 0 < s := by omega
    have hcoef : 9 * s ≤ 12 * (s - 1) := by omega
    have hcoefMul := Nat.mul_le_mul_right a hcoef
    have hscaled : 4 * (s * d) <
        4 * (3 * (s - 1) * a) := by
      calc
        4 * (s * d) = s * (4 * d) := by ring
        _ < s * (9 * a) := (Nat.mul_lt_mul_left hspos).2 hdoub'
        _ = (9 * s) * a := by ring
        _ ≤ (12 * (s - 1)) * a := hcoefMul
        _ = 4 * (3 * (s - 1) * a) := by ring
    change s * d < 3 * (s - 1) * a
    exact Nat.lt_of_mul_lt_mul_left hscaled
  have hAaff : FinsetAffineGenerates A := by
    simpa [A] using finsetAffineGenerates_exactPower C (by omega) hzero hprimitive
  have hArank : FinsetRankCertificate A :=
    hrect N (NeZero.pos N) A hAne hAaff n hn ρ hρ
      (β - (L : ZMod n)) hAhalf hAthreshold
  have hstruct : RankExceptionalCertificate S := by
    have hc := rankExceptionalCertificate_of_finsetRankCertificate A hArank
    simpa [S, A, coe_exactPowerFinset] using hc
  exact hnot (Or.inr (Or.inr hstruct))

/-- Thus the only remaining input for the complete V3 theorem is the explicit
rectifiable `3n-3` statement. -/
theorem stableHighPowerStructureV3_of_rectifiableThreeMinusThree
    (hrect : HasRectifiableThreeMinusThree) :
    HasStableHighPowerStructureV3 := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hN
      letI : NeZero N := ⟨hN.ne'⟩
      dsimp
      intro C t ht hzero hprimitive hdoub
      apply stableV3_of_rectifiableThreeMinusThree_of_smaller
        hrect C t ht hzero hprimitive hdoub
      intro m hm
      letI : NeZero m := ⟨hm.ne'⟩
      dsimp
      intro hmN D hz hcard hp hd
      exact ih m hmN hm D t ht hz hp hd

end Erdos336
