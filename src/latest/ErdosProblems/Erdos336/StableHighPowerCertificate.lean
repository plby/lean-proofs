import ErdosProblems.Erdos336.LevHighPowerReduction
import ErdosProblems.Erdos336.FailedGrowthQuotient

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The rank-one and three-fibre alternatives from the Lev-shaped interface,
separated from its global-density alternative. -/
def RankExceptionalCertificate (S : Set G) : Prop :=
  (∃ (m : ℕ) (_hm : 0 < m) (π : G →+ ZMod m), Function.Surjective π ∧
    ∃ (α : ZMod m) (L V : ℕ),
      0 < L ∧
      (∀ x ∈ S, ∃ k : ℕ, k ≤ L ∧ π x = α + (k : ZMod m)) ∧
      (∀ z : ZMod m, (homFiberFinset π z).card ≤ V) ∧
      S.ncard + L * V ≤ (ExactPower S 2).ncard) ∨
  (∃ (m : ℕ) (_hm : 0 < m) (π : G →+ ZMod m), Function.Surjective π ∧
    ∃ V : ℕ,
      (∀ z : ZMod m, (homFiberFinset π z).card ≤ V) ∧
      (π '' S).ncard ≤ 3 ∧
      S.ncard + 3 * V ≤ (ExactPower S 2).ncard)

/-- A quotient-stable version of the desired structural certificate. Density
is measured by doubling defect, which scales correctly through subgroup
quotients. -/
def StableHighPowerCertificate (C : Set G) (t : ℕ) : Prop :=
  let S := ExactPower C t
  Fintype.card G < 20000 * ((ExactPower S 2).ncard - S.ncard) ∨
    RankExceptionalCertificate S

/-- The stable certificate is strong enough for the older Lev-shaped
interface under strict `9/4` doubling. -/
theorem levHighPowerCertificate_of_stable
    {C : Set G} {t : ℕ} (hzero : 0 ∈ C)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hstable : StableHighPowerCertificate C t) :
    LevHighPowerCertificate C t := by
  let S := ExactPower C t
  have hpower : ExactPower S 2 = ExactPower C (2 * t) := by
    simpa [S] using exactPower_exactPower C t 2
  rcases hstable with hdense | hstruct
  · left
    change Fintype.card G < 20000 *
      ((ExactPower S 2).ncard - S.ncard) at hdense
    have hzS : 0 ∈ S := by
      refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
      intro y hy
      rw [List.mem_replicate] at hy
      simpa [hy.2] using hzero
    have hSle : S.ncard ≤ (ExactPower S 2).ncard := by
      refine Set.ncard_le_ncard ?_ (Set.toFinite _)
      intro x hx
      rw [exactPower_eq_nsmul, two_nsmul]
      exact ⟨x, hx, 0, hzS, by simp⟩
    have hdoubS : 4 * (ExactPower S 2).ncard < 9 * S.ncard := by
      rw [hpower]
      simpa [S] using hdoub
    have hdef : 4 * ((ExactPower S 2).ncard - S.ncard) < 5 * S.ncard := by
      omega
    change Fintype.card G < 30000 * S.ncard
    omega
  · rcases hstruct with hrank | hexception
    · exact Or.inr (Or.inl hrank)
    · exact Or.inr (Or.inr hexception)

section Lift

variable [IsAddCyclic G]

/-- Rank/exceptional structure and defect-density lift from a cyclic quotient.
This is the induction mechanism behind the subgroup-saturation reduction. -/
theorem stableHighPowerCertificate_of_quotient
    (K : AddSubgroup G) [NeZero (Nat.card (G ⧸ K))]
    (C : Set G) (t : ℕ) (hzero : 0 ∈ C)
    (hchild : StableHighPowerCertificate (cyclicQuotientHom K '' C) t)
    (hdefect :
      ((ExactPower (ExactPower (cyclicQuotientHom K '' C) t) 2).ncard -
        (ExactPower (cyclicQuotientHom K '' C) t).ncard) *
          (addSubgroupFinset K).card ≤
      (ExactPower (ExactPower C t) 2).ncard - (ExactPower C t).ncard) :
    StableHighPowerCertificate C t := by
  let m := Nat.card (G ⧸ K)
  let f := cyclicQuotientHom K
  let S := ExactPower C t
  let S' := ExactPower (f '' C) t
  let k := (addSubgroupFinset K).card
  have hm : 0 < m := Nat.card_pos
  have hf : Function.Surjective f := cyclicQuotientHom_surjective K
  have himageS : f '' S = S' := by
    simpa [S, S'] using image_exactPower f C t
  have hzS : 0 ∈ S := by
    refine ⟨List.replicate t 0, by simp, ?_, by simp⟩
    intro y hy
    rw [List.mem_replicate] at hy
    simpa [hy.2] using hzero
  have hSle : S.ncard ≤ (ExactPower S 2).ncard := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    intro x hx
    rw [exactPower_eq_nsmul, two_nsmul]
    exact ⟨x, hx, 0, hzS, by simp⟩
  have hGcard : Fintype.card G = m * k := by
    letI : Fintype K := Fintype.ofFinite K
    rw [← Nat.card_eq_fintype_card,
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
    congr 1
    simpa [k, addSubgroupFinset] using
      (Nat.card_eq_fintype_card (α := K))
  have hkpos : 0 < k := by
    dsimp [k]
    rw [Finset.card_pos]
    exact ⟨0, by simp⟩
  change ((ExactPower S' 2).ncard - S'.ncard) * k ≤
    (ExactPower S 2).ncard - S.ncard at hdefect
  change Fintype.card (ZMod m) < 20000 *
      ((ExactPower S' 2).ncard - S'.ncard) ∨
    RankExceptionalCertificate S' at hchild
  rcases hchild with hdense | hstruct
  · left
    change Fintype.card G < 20000 *
      ((ExactPower S 2).ncard - S.ncard)
    have hmcard : Fintype.card (ZMod m) = m := ZMod.card m
    rw [hmcard] at hdense
    rw [hGcard]
    calc
      m * k < (20000 * ((ExactPower S' 2).ncard - S'.ncard)) * k :=
        Nat.mul_lt_mul_of_pos_right hdense hkpos
      _ = 20000 * (((ExactPower S' 2).ncard - S'.ncard) * k) := by ring
      _ ≤ 20000 * ((ExactPower S 2).ncard - S.ncard) :=
        Nat.mul_le_mul_left 20000 hdefect
  · right
    rcases hstruct with hrank | hexception
    · left
      obtain ⟨n, hn, π, hπ, α, L, V, hL, houter, hfiber, hdiff⟩ := hrank
      change S'.ncard + L * V ≤ (ExactPower S' 2).ncard at hdiff
      let π' : G →+ ZMod n := π.comp f
      refine ⟨n, hn, π', hπ.comp hf, α, L, V * k, hL, ?_, ?_, ?_⟩
      · intro x hx
        have hfx : f x ∈ S' := by
          rw [← himageS]
          exact ⟨x, hx, rfl⟩
        obtain ⟨j, hj, hπj⟩ := houter (f x) hfx
        exact ⟨j, hj, hπj⟩
      · intro z
        have heq : homFiberFinset π' z =
            homPreimageFinset f (homFiberFinset π z) := by
          ext x
          simp [π', homPreimageFinset]
        rw [heq, card_homPreimageFinset f hf]
        simpa [f, k] using Nat.mul_le_mul_right k (hfiber z)
      · have hLV : L * V ≤ (ExactPower S' 2).ncard - S'.ncard := by
          omega
        have hscaled : L * (V * k) ≤
            ((ExactPower S' 2).ncard - S'.ncard) * k := by
          nlinarith
        have hcost : L * (V * k) ≤
            (ExactPower S 2).ncard - S.ncard :=
          le_trans hscaled hdefect
        change S.ncard + L * (V * k) ≤ (ExactPower S 2).ncard
        omega
    · right
      obtain ⟨n, hn, π, hπ, V, hfiber, himage, hdiff⟩ := hexception
      change S'.ncard + 3 * V ≤ (ExactPower S' 2).ncard at hdiff
      let π' : G →+ ZMod n := π.comp f
      refine ⟨n, hn, π', hπ.comp hf, V * k, ?_, ?_, ?_⟩
      · intro z
        have heq : homFiberFinset π' z =
            homPreimageFinset f (homFiberFinset π z) := by
          ext x
          simp [π', homPreimageFinset]
        rw [heq, card_homPreimageFinset f hf]
        simpa [f, k] using Nat.mul_le_mul_right k (hfiber z)
      · have himageEq : π' '' S = π '' S' := by
          rw [← himageS]
          ext z
          simp [π', Set.image_image]
        rw [himageEq]
        exact himage
      · have h3V : 3 * V ≤ (ExactPower S' 2).ncard - S'.ncard := by
          omega
        have hscaled : 3 * (V * k) ≤
            ((ExactPower S' 2).ncard - S'.ncard) * k := by
          nlinarith
        have hcost : 3 * (V * k) ≤
            (ExactPower S 2).ncard - S.ncard :=
          le_trans hscaled hdefect
        change S.ncard + 3 * (V * k) ≤ (ExactPower S 2).ncard
        omega

/-- A failed subgroup-growth inequality plus a stable certificate in the
smaller cyclic quotient yields a stable certificate upstairs. -/
theorem stableHighPowerCertificate_of_failed_growth
    (K : AddSubgroup G) (C : Set G) (t : ℕ)
    (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hfail : (exactPowerFinset C t + addSubgroupFinset K).card <
      (exactPowerFinset C t).card + (addSubgroupFinset K).card)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hchild :
      let _ : NeZero (Nat.card (G ⧸ K)) :=
        ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
      StableHighPowerCertificate (cyclicQuotientHom K '' C) t) :
    StableHighPowerCertificate C t := by
  letI : NeZero (Nat.card (G ⧸ K)) :=
    ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  have hdata := failed_growth_cyclic_quotient_highPower_data K C t
    hzero hprimitive hfail hdoub
  rcases hdata with ⟨hm, hf, hz, hp, hd, hdef⟩
  have hdef' :
      ((ExactPower (ExactPower (cyclicQuotientHom K '' C) t) 2).ncard -
        (ExactPower (cyclicQuotientHom K '' C) t).ncard) *
          (addSubgroupFinset K).card ≤
      (ExactPower (ExactPower C t) 2).ncard - (ExactPower C t).ncard := by
    simpa [exactPower_exactPower] using hdef
  exact stableHighPowerCertificate_of_quotient K C t hzero hchild hdef'

/-- In a minimal-cardinality counterexample to the stable high-power theorem,
every nonzero subgroup gives full one-fibre growth. A failure would descend all
hypotheses to a strictly smaller cyclic quotient and then lift its certificate. -/
theorem proper_saturation_growth_of_smaller_stable
    (C : Set G) (t : ℕ) (hzero : 0 ∈ C)
    (hprimitive : ∃ q : ℕ, ExactPower C q = Set.univ)
    (hdoub : 4 * (ExactPower C (2 * t)).ncard <
      9 * (ExactPower C t).ncard)
    (hnot : ¬ StableHighPowerCertificate C t)
    (hsmaller : ∀ (m : ℕ) (hm : 0 < m),
      let _ : NeZero m := ⟨hm.ne'⟩
      m < Fintype.card G →
        ∀ (D : Set (ZMod m)), 0 ∈ D →
          (∃ q : ℕ, ExactPower D q = Set.univ) →
          4 * (ExactPower D (2 * t)).ncard <
            9 * (ExactPower D t).ncard →
          StableHighPowerCertificate D t) :
    ∀ K : AddSubgroup G, K ≠ ⊥ →
      (exactPowerFinset C t).card + (addSubgroupFinset K).card ≤
        (exactPowerFinset C t + addSubgroupFinset K).card := by
  intro K hK
  by_contra hfailNot
  have hfail : (exactPowerFinset C t + addSubgroupFinset K).card <
      (exactPowerFinset C t).card + (addSubgroupFinset K).card := by omega
  let m := Nat.card (G ⧸ K)
  have hm : 0 < m := Nat.card_pos
  letI : NeZero m := ⟨hm.ne'⟩
  have hdata := failed_growth_cyclic_quotient_highPower_data K C t
    hzero hprimitive hfail hdoub
  rcases hdata with ⟨_, hf, hz, hp, hd, hdef⟩
  have hGcard : Fintype.card G = m * (addSubgroupFinset K).card := by
    letI : Fintype K := Fintype.ofFinite K
    rw [← Nat.card_eq_fintype_card,
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]
    congr 1
    simpa [addSubgroupFinset] using (Nat.card_eq_fintype_card (α := K))
  have hk2 : 2 ≤ (addSubgroupFinset K).card := by
    letI : Fintype K := Fintype.ofFinite K
    have hk := (AddSubgroup.one_lt_card_iff_ne_bot K).mpr hK
    have hk' : 1 < (addSubgroupFinset K).card := by
      simpa [addSubgroupFinset, Nat.card_eq_fintype_card] using hk
    omega
  have hmG : m < Fintype.card G := by
    rw [hGcard]
    change m < m * (addSubgroupFinset K).card
    nlinarith
  have hchild := hsmaller m hm hmG (cyclicQuotientHom K '' C) hz hp hd
  exact hnot (stableHighPowerCertificate_of_failed_growth K C t
    hzero hprimitive hfail hdoub hchild)

end Lift

end Erdos336
