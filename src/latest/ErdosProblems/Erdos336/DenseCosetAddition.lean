import Mathlib
import ErdosProblems.Erdos336.VerySmallDoublingStructure

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The underlying finset of a subgroup of a finite ambient group. -/
noncomputable def addSubgroupFinset (K : AddSubgroup G) : Finset G :=
  Set.Finite.toFinset (Set.toFinite (K : Set G))

@[simp] theorem mem_addSubgroupFinset (K : AddSubgroup G) (x : G) :
    x ∈ addSubgroupFinset K ↔ x ∈ K := by simp [addSubgroupFinset]

private lemma disjoint_vadd_addSubgroup_toFinset
    (K : AddSubgroup G) {b c : G} (hbc : b - c ∉ K) :
    Disjoint (b +ᵥ addSubgroupFinset K) (c +ᵥ addSubgroupFinset K) := by
  rw [Finset.disjoint_left]
  intro x hxb hxc
  obtain ⟨u, hu, hub⟩ := Finset.mem_vadd_finset.mp hxb
  obtain ⟨v, hv, hvc⟩ := Finset.mem_vadd_finset.mp hxc
  apply hbc
  have huK : u ∈ K := by simpa using hu
  have hvK : v ∈ K := by simpa using hv
  have huv : b - c = v - u := by
    simp only [vadd_eq_add] at hub hvc
    have hb' : b = x - u := by rw [← hub]; abel
    have hc' : c = x - v := by rw [← hvc]; abel
    rw [hb', hc']
    abel
  rw [huv]
  exact K.sub_mem hvK huK

private lemma disjoint_vadd_of_coset_support
    (K : AddSubgroup G) {A : Finset G} {a b c : G}
    (hA : A ⊆ a +ᵥ addSubgroupFinset K) (hbc : b - c ∉ K) :
    Disjoint (b +ᵥ A) (c +ᵥ A) := by
  have hbc' : (b + a) - (c + a) ∉ K := by
    simpa only [add_sub_add_right_eq_sub] using hbc
  have hdiscoset := disjoint_vadd_addSubgroup_toFinset K hbc'
  apply hdiscoset.mono
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_vadd_finset.mp hx
    obtain ⟨y0, hy0, hay⟩ := Finset.mem_vadd_finset.mp (hA hy)
    apply Finset.mem_vadd_finset.mpr
    refine ⟨y0, hy0, ?_⟩
    simp only [vadd_eq_add] at hyx hay ⊢
    rw [← hyx, ← hay]
    abel
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_vadd_finset.mp hx
    obtain ⟨y0, hy0, hay⟩ := Finset.mem_vadd_finset.mp (hA hy)
    apply Finset.mem_vadd_finset.mpr
    refine ⟨y0, hy0, ?_⟩
    simp only [vadd_eq_add] at hyx hay ⊢
    rw [← hyx, ← hay]
    abel

private lemma vadd_toFinset_subset_add_of_mem
    (K : AddSubgroup G) {A B : Finset G} {b : G} (hb : b ∈ B) :
    b +ᵥ A ⊆ B + A := by
  intro x hx
  obtain ⟨a, ha, hax⟩ := Finset.mem_vadd_finset.mp hx
  exact Finset.mem_add.mpr ⟨b, hb, a, ha, hax⟩

/-- Pigeonhole addition inside a finite subgroup coset. -/
theorem add_eq_vadd_of_coset_support_of_card_lt_add
    (K : AddSubgroup G) {A B : Finset G} {a b : G}
    (hA : A ⊆ a +ᵥ addSubgroupFinset K) (hB : B ⊆ b +ᵥ addSubgroupFinset K)
    (hcard : (addSubgroupFinset K).card < A.card + B.card) :
    A + B = (a + b) +ᵥ addSubgroupFinset K := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    obtain ⟨u0, hu0, huu⟩ := Finset.mem_vadd_finset.mp (hA hu)
    obtain ⟨v0, hv0, hvv⟩ := Finset.mem_vadd_finset.mp (hB hv)
    apply Finset.mem_vadd_finset.mpr
    refine ⟨u0 + v0, ?_, ?_⟩
    · simpa using K.add_mem (by simpa using hu0) (by simpa using hv0)
    · simp only [vadd_eq_add] at huu hvv ⊢
      rw [← huv, ← huu, ← hvv]
      abel
  · intro x hx
    obtain ⟨k, hk, hkx⟩ := Finset.mem_vadd_finset.mp hx
    let T : Finset G := B.image (fun y => x - y)
    have hTcard : T.card = B.card := by
      dsimp [T]
      rw [Finset.card_image_of_injective]
      intro y z hyz
      exact sub_right_injective hyz
    have hTsub : T ⊆ a +ᵥ addSubgroupFinset K := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y0, hy0, hyy⟩ := Finset.mem_vadd_finset.mp (hB hy)
      apply Finset.mem_vadd_finset.mpr
      refine ⟨k - y0, ?_, ?_⟩
      · simpa using K.sub_mem (by simpa using hk) (by simpa using hy0)
      · simp only [vadd_eq_add] at hkx hyy ⊢
        rw [← hkx, ← hyy]
        abel
    have hUcard : (a +ᵥ addSubgroupFinset K).card = (addSubgroupFinset K).card :=
      Finset.card_vadd_finset _ _
    have hinter : ¬ Disjoint A T := by
      apply not_disjoint_of_card_add_gt_of_subset hA hTsub
      rw [hUcard, hTcard]
      exact hcard
    rw [Finset.not_disjoint_iff] at hinter
    obtain ⟨z, hzA, hzT⟩ := hinter
    obtain ⟨y, hyB, hyz⟩ := Finset.mem_image.mp hzT
    refine Finset.mem_add.mpr ⟨z, hzA, y, hyB, ?_⟩
    rw [← hyz]
    abel

/-- Lev's first elementary dense-coset addition bound (Lemma 6.1(i)). -/
theorem card_add_ge_subgroup_of_dense_coset
    (K : AddSubgroup G) {A B : Finset G} {a : G}
    (hA : A ⊆ a +ᵥ addSubgroupFinset K)
    (hdense : (addSubgroupFinset K).card ≤ 2 * A.card)
    (hB : B.Nonempty)
    (hlarge : (addSubgroupFinset K).card < A.card + B.card) :
    (addSubgroupFinset K).card ≤ (A + B).card := by
  by_cases hcoset : ∃ b : G, B ⊆ b +ᵥ addSubgroupFinset K
  · obtain ⟨b, hb⟩ := hcoset
    rw [add_eq_vadd_of_coset_support_of_card_lt_add K hA hb hlarge]
    have hc := Finset.card_vadd_finset (a + b) (addSubgroupFinset K)
    omega
  · obtain ⟨b, hb⟩ := hB
    have hex : ∃ c ∈ B, c ∉ b +ᵥ addSubgroupFinset K := by
      by_contra hn
      push_neg at hn
      apply hcoset
      exact ⟨b, hn⟩
    obtain ⟨c, hc, hcb⟩ := hex
    have hbc : b - c ∉ K := by
      intro hmem
      apply hcb
      apply Finset.mem_vadd_finset.mpr
      refine ⟨c - b, ?_, ?_⟩
      · have : c - b = -(b - c) := by abel
        rw [this]
        simpa using K.neg_mem hmem
      · simp only [vadd_eq_add]
        abel
    have hbc' : (b + a) - (c + a) ∉ K := by simpa only [add_sub_add_right_eq_sub] using hbc
    have hdiscoset := disjoint_vadd_addSubgroup_toFinset K hbc'
    have hbA : b +ᵥ A ⊆ (b + a) +ᵥ addSubgroupFinset K := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_vadd_finset.mp hx
      obtain ⟨y0, hy0, hay⟩ := Finset.mem_vadd_finset.mp (hA hy)
      apply Finset.mem_vadd_finset.mpr
      refine ⟨y0, hy0, ?_⟩
      simp only [vadd_eq_add] at hyx hay ⊢
      rw [← hyx, ← hay]
      abel
    have hcA : c +ᵥ A ⊆ (c + a) +ᵥ addSubgroupFinset K := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_vadd_finset.mp hx
      obtain ⟨y0, hy0, hay⟩ := Finset.mem_vadd_finset.mp (hA hy)
      apply Finset.mem_vadd_finset.mpr
      refine ⟨y0, hy0, ?_⟩
      simp only [vadd_eq_add] at hyx hay ⊢
      rw [← hyx, ← hay]
      abel
    have hdis : Disjoint (b +ᵥ A) (c +ᵥ A) :=
      hdiscoset.mono hbA hcA
    have hbsub : b +ᵥ A ⊆ B + A :=
      vadd_toFinset_subset_add_of_mem K hb
    have hcsub : c +ᵥ A ⊆ B + A :=
      vadd_toFinset_subset_add_of_mem K hc
    have hunion : (b +ᵥ A) ∪ (c +ᵥ A) ⊆ A + B := by
      rw [add_comm]
      exact Finset.union_subset hbsub hcsub
    have hcardunion := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_vadd_finset, Finset.card_vadd_finset] at hcardunion
    omega

/-- Lev's second elementary dense-coset addition bound (Lemma 6.1(ii)). -/
theorem card_add_ge_card_add_subgroup_or_coset
    (K : AddSubgroup G) {A B : Finset G} {a : G}
    (hAne : A.Nonempty) (hA : A ⊆ a +ᵥ addSubgroupFinset K)
    (hdense : (addSubgroupFinset K).card ≤ 2 * A.card)
    (hB : B.Nonempty)
    (hlarge : 2 * ((addSubgroupFinset K).card - A.card) < B.card) :
    (∃ b : G, B ⊆ b +ᵥ addSubgroupFinset K) ∨
      A.card + (addSubgroupFinset K).card ≤ (A + B).card := by
  by_cases hcoset : ∃ b : G, B ⊆ b +ᵥ addSubgroupFinset K
  · exact Or.inl hcoset
  · apply Or.inr
    let H := addSubgroupFinset K
    have hAcard : A.card ≤ H.card := by
      calc
        A.card ≤ (a +ᵥ H).card := Finset.card_le_card hA
        _ = H.card := Finset.card_vadd_finset _ _
    have hlarge' : 2 * (H.card - A.card) < B.card := by
      simpa [H] using hlarge
    obtain ⟨b, hb⟩ := hB
    let Fb : Finset G := B.filter (fun x => x ∈ b +ᵥ H)
    have hFbB : Fb ⊆ B := Finset.filter_subset _ _
    have hFbcos : Fb ⊆ b +ᵥ H := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hbFb : b ∈ Fb := by
      apply Finset.mem_filter.mpr
      refine ⟨hb, ?_⟩
      apply Finset.mem_vadd_finset.mpr
      refine ⟨0, ?_, by simp⟩
      simp [H]
    have hex : ∃ c ∈ B, c ∉ b +ᵥ H := by
      by_contra hn
      push_neg at hn
      apply hcoset
      exact ⟨b, hn⟩
    obtain ⟨c, hc, hcb⟩ := hex
    let Fc : Finset G := B.filter (fun x => x ∈ c +ᵥ H)
    have hFcB : Fc ⊆ B := Finset.filter_subset _ _
    have hFccos : Fc ⊆ c +ᵥ H := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hcFc : c ∈ Fc := by
      apply Finset.mem_filter.mpr
      refine ⟨hc, ?_⟩
      apply Finset.mem_vadd_finset.mpr
      refine ⟨0, ?_, by simp⟩
      simp [H]
    have hbc : b - c ∉ K := by
      intro hmem
      apply hcb
      apply Finset.mem_vadd_finset.mpr
      refine ⟨c - b, ?_, ?_⟩
      · have heq : c - b = -(b - c) := by abel
        rw [heq]
        simpa [H] using K.neg_mem hmem
      · simp only [vadd_eq_add]
        abel
    have hdisbc : Disjoint (b +ᵥ A) (c +ᵥ A) :=
      disjoint_vadd_of_coset_support K hA hbc
    by_cases hFbLarge : H.card - A.card < Fb.card
    · have hsumfull : A + Fb = (a + b) +ᵥ H := by
        apply add_eq_vadd_of_coset_support_of_card_lt_add K hA
          (by simpa [H] using hFbcos)
        dsimp [H] at hFbLarge ⊢
        omega
      have hfullsub : (a + b) +ᵥ H ⊆ A + B := by
        rw [← hsumfull]
        exact Finset.add_subset_add_left hFbB
      have hcsub : c +ᵥ A ⊆ A + B := by
        rw [add_comm]
        exact vadd_toFinset_subset_add_of_mem K hc
      have hdisfull : Disjoint ((a + b) +ᵥ H) (c +ᵥ A) := by
        have hfullcos : Disjoint ((a + b) +ᵥ H) ((a + c) +ᵥ H) := by
          have hdiff : (a + b) - (a + c) ∉ K := by
            have : (a + b) - (a + c) = b - c := by abel
            rwa [this]
          exact disjoint_vadd_addSubgroup_toFinset K hdiff
        apply hfullcos.mono (by rfl)
        intro x hx
        obtain ⟨y, hy, hyx⟩ := Finset.mem_vadd_finset.mp hx
        obtain ⟨y0, hy0, hay⟩ := Finset.mem_vadd_finset.mp (hA hy)
        apply Finset.mem_vadd_finset.mpr
        refine ⟨y0, by simpa [H] using hy0, ?_⟩
        simp only [vadd_eq_add] at hyx hay ⊢
        rw [← hyx, ← hay]
        abel
      have hunion : ((a + b) +ᵥ H) ∪ (c +ᵥ A) ⊆ A + B :=
        Finset.union_subset hfullsub hcsub
      have hle := Finset.card_le_card hunion
      rw [Finset.card_union_of_disjoint hdisfull,
        Finset.card_vadd_finset, Finset.card_vadd_finset] at hle
      simpa [H, Nat.add_comm] using hle
    · have hFbSmall : Fb.card ≤ H.card - A.card := by omega
      by_cases hFcLarge : H.card - A.card < Fc.card
      · have hsumfull : A + Fc = (a + c) +ᵥ H := by
          apply add_eq_vadd_of_coset_support_of_card_lt_add K hA
            (by simpa [H] using hFccos)
          dsimp [H] at hFcLarge ⊢
          omega
        have hfullsub : (a + c) +ᵥ H ⊆ A + B := by
          rw [← hsumfull]
          exact Finset.add_subset_add_left hFcB
        have hbsub : b +ᵥ A ⊆ A + B := by
          rw [add_comm]
          exact vadd_toFinset_subset_add_of_mem K hb
        have hdisfull : Disjoint ((a + c) +ᵥ H) (b +ᵥ A) := by
          have hfullcos : Disjoint ((a + c) +ᵥ H) ((a + b) +ᵥ H) := by
            have hdiff : (a + c) - (a + b) ∉ K := by
              intro hmem
              apply hbc
              have hneg : -((a + c) - (a + b)) ∈ K := K.neg_mem hmem
              have heq : -((a + c) - (a + b)) = b - c := by abel
              rwa [heq] at hneg
            exact disjoint_vadd_addSubgroup_toFinset K hdiff
          apply hfullcos.mono (by rfl)
          intro x hx
          obtain ⟨y, hy, hyx⟩ := Finset.mem_vadd_finset.mp hx
          obtain ⟨y0, hy0, hay⟩ := Finset.mem_vadd_finset.mp (hA hy)
          apply Finset.mem_vadd_finset.mpr
          refine ⟨y0, by simpa [H] using hy0, ?_⟩
          simp only [vadd_eq_add] at hyx hay ⊢
          rw [← hyx, ← hay]
          abel
        have hunion : ((a + c) +ᵥ H) ∪ (b +ᵥ A) ⊆ A + B :=
          Finset.union_subset hfullsub hbsub
        have hle := Finset.card_le_card hunion
        rw [Finset.card_union_of_disjoint hdisfull,
          Finset.card_vadd_finset, Finset.card_vadd_finset] at hle
        simpa [H, Nat.add_comm] using hle
      · have hFcSmall : Fc.card ≤ H.card - A.card := by omega
        have hdex : ∃ d ∈ B, d ∉ Fb ∪ Fc := by
          by_contra hn
          push_neg at hn
          have hsub : B ⊆ Fb ∪ Fc := by
            intro x hx
            exact hn x hx
          have hle := Finset.card_le_card hsub
          have hunion := Finset.card_union_le Fb Fc
          omega
        obtain ⟨d, hd, hdout⟩ := hdex
        have hdb : d ∉ b +ᵥ H := by
          intro hdin
          apply hdout
          exact Finset.mem_union_left Fc (Finset.mem_filter.mpr ⟨hd, hdin⟩)
        have hdc : d ∉ c +ᵥ H := by
          intro hdin
          apply hdout
          exact Finset.mem_union_right Fb (Finset.mem_filter.mpr ⟨hd, hdin⟩)
        have hbd : b - d ∉ K := by
          intro hmem
          apply hdb
          apply Finset.mem_vadd_finset.mpr
          refine ⟨d - b, ?_, ?_⟩
          · have heq : d - b = -(b - d) := by abel
            rw [heq]
            simpa [H] using K.neg_mem hmem
          · simp only [vadd_eq_add]
            abel
        have hcd : c - d ∉ K := by
          intro hmem
          apply hdc
          apply Finset.mem_vadd_finset.mpr
          refine ⟨d - c, ?_, ?_⟩
          · have heq : d - c = -(c - d) := by abel
            rw [heq]
            simpa [H] using K.neg_mem hmem
          · simp only [vadd_eq_add]
            abel
        have hdisbd : Disjoint (b +ᵥ A) (d +ᵥ A) :=
          disjoint_vadd_of_coset_support K hA hbd
        have hdiscd : Disjoint (c +ᵥ A) (d +ᵥ A) :=
          disjoint_vadd_of_coset_support K hA hcd
        have hdisunion : Disjoint ((b +ᵥ A) ∪ (c +ᵥ A)) (d +ᵥ A) :=
          Finset.disjoint_union_left.mpr ⟨hdisbd, hdiscd⟩
        have hbsub : b +ᵥ A ⊆ B + A := vadd_toFinset_subset_add_of_mem K hb
        have hcsub : c +ᵥ A ⊆ B + A := vadd_toFinset_subset_add_of_mem K hc
        have hdsub : d +ᵥ A ⊆ B + A := vadd_toFinset_subset_add_of_mem K hd
        have hunion : ((b +ᵥ A) ∪ (c +ᵥ A)) ∪ (d +ᵥ A) ⊆ A + B := by
          rw [add_comm]
          exact Finset.union_subset (Finset.union_subset hbsub hcsub) hdsub
        have hle := Finset.card_le_card hunion
        rw [Finset.card_union_of_disjoint hdisunion,
          Finset.card_union_of_disjoint hdisbc,
          Finset.card_vadd_finset, Finset.card_vadd_finset,
          Finset.card_vadd_finset] at hle
        change A.card + (addSubgroupFinset K).card ≤ (A + B).card
        omega

end Erdos336
