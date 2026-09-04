/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1027.Basic

namespace Erdos1027.Tree

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {α : Type*} [DecidableEq α] [LinearOrder α]

lemma residual_min_at_leaf {C n r : ℕ} (hn : r + 2 ≤ n)
    {X : Finset α} {F : Hypergraph α}
    (hedges : ∀ A ∈ F, A ⊆ X ∧ A.card = n)
    {q : Partial α}
    (hq : q ∈ (build (4 * C * 2 ^ n) r X F X.card (Partial.mk ∅ ∅)).leaves) :
    ∀ E ∈ residual X F q, r ≤ E.card := by
  intro E hE
  rw [residual] at hE
  rcases Finset.mem_image.mp hE with ⟨A, hAlive, rfl⟩
  have hAF := (Finset.mem_filter.mp hAlive).1
  have hlive := (Finset.mem_filter.mp hAlive).2
  rcases leaf_eq_root_or_has_parent (4 * C * 2 ^ n) r X F X.card
      (Partial.mk ∅ ∅) q hq with hroot | ⟨parent, v, b, hsel, hnf, hnr, hchild⟩
  · subst q
    have hAX := (hedges A hAF).1
    have heq : A ∩ (Partial.mk (α := α) ∅ ∅).uncolored X = A := by
      ext x
      simp only [Finset.mem_inter, and_iff_left_iff_imp]
      exact fun hx => hAX hx
    rw [heq, (hedges A hAF).2]
    omega
  · subst q
    have hvU : v ∈ parent.uncolored X := selectMin_mem hsel
    have hliveParent := live_parent_of_live_child parent A v b hlive
    have hgt : r < (A ∩ parent.uncolored X).card := by
      by_contra hle
      exact hnr ⟨A, hAF, hliveParent, by omega⟩
    have hdrop := parent_edge_uncolored_le_child_add_one (A := A) hvU b
    omega

lemma completion_from_residual {X : Finset α} {F : Hypergraph α} {p : Partial α}
    (hp : p.Valid X) (hedges : ∀ A ∈ F, A ⊆ X)
    {R : Finset α} (hR : ProperColoring (residual X F p) R) :
    ∃ B : Finset α, B ⊆ X ∧ Extends p B ∧ ProperColoring F B := by
  let U := p.uncolored X
  let B := p.red ∪ (R ∩ U)
  have hblueU : Disjoint p.blue U := by
    rw [Finset.disjoint_left]
    intro x hxb hxu
    exact (Finset.mem_sdiff.mp hxu).2 (Finset.mem_union_right _ hxb)
  have hext : Extends p B := by
    constructor
    · exact Finset.subset_union_left
    · rw [Finset.disjoint_left]
      intro x hxb hxB
      rcases Finset.mem_union.mp hxB with hxr | hxRU
      · exact Finset.disjoint_left.mp hp.1 hxr hxb
      · exact Finset.disjoint_left.mp hblueU hxb (Finset.mem_inter.mp hxRU).2
  have hBsub : B ⊆ X := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxred | hxRU
    · exact hp.2 (Finset.mem_union_left _ hxred)
    · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxRU).2).1
  refine ⟨B, hBsub, hext, ?_⟩
  intro A hAF
  by_cases hlive : Live p A
  · have hmem : A ∩ U ∈ residual X F p := by
      exact Finset.mem_image.mpr ⟨A, Finset.mem_filter.mpr ⟨hAF, hlive⟩, rfl⟩
    obtain ⟨hred, hblue⟩ := hR (A ∩ U) hmem
    constructor
    · obtain ⟨x, hx⟩ := hred
      have ⟨hxAU, hxR⟩ := Finset.mem_inter.mp hx
      have ⟨hxA, hxU⟩ := Finset.mem_inter.mp hxAU
      refine ⟨x, Finset.mem_inter.mpr ⟨hxA, ?_⟩⟩
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr ⟨hxR, hxU⟩))
    · obtain ⟨x, hx⟩ := hblue
      have ⟨hxAU, hxR⟩ := Finset.mem_sdiff.mp hx
      have ⟨hxA, hxU⟩ := Finset.mem_inter.mp hxAU
      refine ⟨x, Finset.mem_sdiff.mpr ⟨hxA, ?_⟩⟩
      intro hxB
      rcases Finset.mem_union.mp hxB with hxr | hxRU
      · exact (Finset.mem_sdiff.mp hxU).2 (Finset.mem_union_left _ hxr)
      · exact hxR (Finset.mem_inter.mp hxRU).1
  · simp only [Live, not_or] at hlive
    rcases Finset.not_disjoint_iff.mp hlive.1 with ⟨xr, hxAr, hxred⟩
    rcases Finset.not_disjoint_iff.mp hlive.2 with ⟨xb, hxAb, hxblue⟩
    constructor
    · refine ⟨xr, Finset.mem_inter.mpr ⟨hxAr, ?_⟩⟩
      exact Finset.mem_union_left _ hxred
    · refine ⟨xb, Finset.mem_sdiff.mpr ⟨hxAb, ?_⟩⟩
      intro hxB
      rcases Finset.mem_union.mp hxB with hxred' | hxRU
      · exact Finset.disjoint_left.mp hp.1 hxred' hxblue
      · exact Finset.disjoint_left.mp hblueU hxblue (Finset.mem_inter.mp hxRU).2

lemma nonfailed_leaf_has_proper_extension {C n r : ℕ} (hn : r + 2 ≤ n)
    {X : Finset α} {F : Hypergraph α}
    (hedges : ∀ A ∈ F, A ⊆ X ∧ A.card = n)
    (beckFixedBudget : BeckFixedBudget (α := α) C n r)
    {q : Partial α}
    (hq : q ∈ (build (4 * C * 2 ^ n) r X F X.card (Partial.mk ∅ ∅)).leaves)
    (hnf : ¬ Failed (4 * C * 2 ^ n) F q) :
    ∃ B : Finset α, B ⊆ X ∧ Extends q B ∧ ProperColoring F B := by
  have hmin := residual_min_at_leaf hn hedges hq
  have hweight : scaledWeight n (residual X F q) ≤ 4 * C * 2 ^ n := by
    exact (scaledWeight_residual_le_totalScore hedges).trans (by
      simpa [Failed] using Nat.le_of_not_gt hnf)
  obtain ⟨R, hR⟩ := beckFixedBudget (residual X F q) hmin hweight
  have hqvalid : q.Valid X := leaf_valid (4 * C * 2 ^ n) r X F X.card
    (Partial.mk ∅ ∅) q (by simp [Partial.Valid]) hq
  exact completion_from_residual hqvalid (fun A hA => (hedges A hA).1) hR

def heavyEdges (n r : ℕ) (F : Hypergraph α) (p : Partial α) : Hypergraph α :=
  F.filter fun A => 2 ^ (n - r - 1) ≤ edgeScore p A

lemma repairable_child_heavy_cover {n r : ℕ} (hn : r + 2 ≤ n)
    {X : Finset α} {F : Hypergraph α}
    (hedges : ∀ A ∈ F, A ⊆ X ∧ A.card = n)
    {parent : Partial α} {v : α} {b : Bool}
    (hsel : selectMin (parent.uncolored X) (vertexLoad F parent) = some v)
    (hnr : ¬ Repairable r X F parent)
    (hrep : Repairable r X F (parent.child v b)) :
    (parent.child v b).uncolored X ⊆
      (heavyEdges n r F parent).biUnion (fun A => A ∩ parent.uncolored X) := by
  obtain ⟨A, hAF, hliveChild, huChild⟩ := hrep
  have hvU : v ∈ parent.uncolored X := selectMin_mem hsel
  have hliveParent := live_parent_of_live_child parent A v b hliveChild
  have huParentGt : r < (A ∩ parent.uncolored X).card := by
    by_contra hle
    exact hnr ⟨A, hAF, hliveParent, by omega⟩
  have hdrop := parent_edge_uncolored_le_child_add_one (A := A) hvU b
  have huParent : (A ∩ parent.uncolored X).card = r + 1 := by omega
  have huChildEq : (A ∩ (parent.child v b).uncolored X).card = r := by omega
  have hvA : v ∈ A := by
    by_contra hvA
    have heq : A ∩ (parent.child v b).uncolored X = A ∩ parent.uncolored X := by
      rw [parent.uncolored_child hvU]
      ext x
      simp
      aesop
    rw [heq] at huChildEq
    omega
  have hpartition := card_colored_add_uncolored (p := parent) (hedges A hAF).1
  have hk : (A ∩ parent.colored).card = n - r - 1 := by
    rw [(hedges A hAF).2] at hpartition
    omega
  have hheavyA : 2 ^ (n - r - 1) ≤ edgeScore parent A := by
    rw [← hk]
    exact edgeScore_lower_of_live (hedges A hAF).1 hliveParent
  have hloadv : 2 ^ (n - r - 1) ≤ vertexLoad F parent v := by
    exact hheavyA.trans (Finset.le_sup (f := edgeScore parent)
      (Finset.mem_filter.mpr ⟨hAF, hvA⟩))
  intro x hx
  have hxParent : x ∈ parent.uncolored X := by
    exact Finset.mem_of_subset (by
      rw [parent.uncolored_child hvU]
      exact Finset.sdiff_subset) hx
  have hloadx : 2 ^ (n - r - 1) ≤ vertexLoad F parent x :=
    hloadv.trans (selectMin_minimal hsel x hxParent)
  have hpos : 0 < 2 ^ (n - r - 1) := by positivity
  rw [vertexLoad, Finset.le_sup_iff hpos] at hloadx
  obtain ⟨E, hEfilter, hheavyE⟩ := hloadx
  have hEF : E ∈ F := (Finset.mem_filter.mp hEfilter).1
  have hxE : x ∈ E := (Finset.mem_filter.mp hEfilter).2
  exact Finset.mem_biUnion.mpr ⟨E,
    Finset.mem_filter.mpr ⟨hEF, hheavyE⟩,
    Finset.mem_inter.mpr ⟨hxE, hxParent⟩⟩

lemma heavyEdges_card_le {C n r : ℕ} (hn : r + 2 ≤ n)
    {F : Hypergraph α} {p : Partial α}
    (hscore : totalScore F p ≤ 4 * C * 2 ^ n) :
    (heavyEdges n r F p).card ≤ C * 2 ^ (r + 3) := by
  let H := heavyEdges n r F p
  have hsumLower : 2 ^ (n - r - 1) * H.card ≤ ∑ A ∈ H, edgeScore p A := by
    simpa [Nat.nsmul_eq_mul, mul_comm] using
      (Finset.card_nsmul_le_sum H (edgeScore p) (2 ^ (n - r - 1))
        (fun A hA => (Finset.mem_filter.mp hA).2))
  have hsumUpper : (∑ A ∈ H, edgeScore p A) ≤ totalScore F p := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)
  have hfactor : 4 * C * 2 ^ n =
      2 ^ (n - r - 1) * (C * 2 ^ (r + 3)) := by
    have hnSplit : n = (n - r - 1) + (r + 1) := by omega
    have hpowN : 2 ^ n = 2 ^ (n - r - 1) * 2 ^ (r + 1) := by
      calc
        2 ^ n = 2 ^ ((n - r - 1) + (r + 1)) := by congr 1
        _ = _ := by rw [pow_add]
    have hpowR : 2 ^ (r + 3) = 2 ^ (r + 1) * 4 := by
      calc
        2 ^ (r + 3) = 2 ^ ((r + 1) + 2) := by congr 1 <;> omega
        _ = _ := by rw [pow_add]; norm_num
    rw [hpowN, hpowR]
    ring
  have hmul : 2 ^ (n - r - 1) * H.card ≤
      2 ^ (n - r - 1) * (C * 2 ^ (r + 3)) := by
    rw [← hfactor]
    exact hsumLower.trans (hsumUpper.trans hscore)
  exact Nat.le_of_mul_le_mul_left hmul (by positivity)

/-- Koishi Chan's minimum-load argument. -/
lemma bounded_uncolored_leaf {C n r : ℕ} (hn : r + 2 ≤ n)
    {X : Finset α} {F : Hypergraph α}
    (hedges : ∀ A ∈ F, A ⊆ X ∧ A.card = n)
    {q : Partial α}
    (hq : q ∈ (build (4 * C * 2 ^ n) r X F X.card (Partial.mk ∅ ∅)).leaves)
    (hnf : ¬ Failed (4 * C * 2 ^ n) F q) :
    (q.uncolored X).card ≤ C * 2 ^ (r + 3) * (r + 2) := by
  have hvalid0 : (Partial.mk (α := α) ∅ ∅).Valid X := by simp [Partial.Valid]
  have hq' : q ∈ (build (4 * C * 2 ^ n) r X F
      ((Partial.mk (α := α) ∅ ∅).uncolored X).card (Partial.mk ∅ ∅)).leaves := by
    simpa [Partial.uncolored, Partial.colored] using hq
  have hterminal := terminal_leaf (4 * C * 2 ^ n) r X F
    (Partial.mk ∅ ∅) q hvalid0 hq'
  rcases hterminal with hfailed | hrep | hcomplete
  · exact False.elim (hnf hfailed)
  · rcases leaf_eq_root_or_has_parent (4 * C * 2 ^ n) r X F X.card
      (Partial.mk ∅ ∅) q hq with hroot | ⟨parent, v, b, hsel, hparentNF, hparentNR, hchild⟩
    · subst q
      obtain ⟨A, hAF, hlive, hsmall⟩ := hrep
      have heq : A ∩ (Partial.mk (α := α) ∅ ∅).uncolored X = A := by
        ext x
        simp only [Finset.mem_inter, and_iff_left_iff_imp]
        exact fun hx => (hedges A hAF).1 hx
      rw [heq, (hedges A hAF).2] at hsmall
      omega
    · subst q
      have hcover := repairable_child_heavy_cover hn hedges hsel hparentNR hrep
      have hparentScore : totalScore F parent ≤ 4 * C * 2 ^ n := by
        simpa [Failed] using Nat.le_of_not_gt hparentNF
      have hHcard := heavyEdges_card_le hn hparentScore
      have hrescard : ∀ A ∈ heavyEdges n r F parent,
          (A ∩ parent.uncolored X).card ≤ r + 2 := by
        intro A hA
        exact heavy_edge_residual_card_le hn (hedges A (Finset.mem_filter.mp hA).1).1
          (hedges A (Finset.mem_filter.mp hA).1).2 (Finset.mem_filter.mp hA).2
      calc
        ((parent.child v b).uncolored X).card ≤
            ((heavyEdges n r F parent).biUnion
              (fun A => A ∩ parent.uncolored X)).card := Finset.card_le_card hcover
        _ ≤ (heavyEdges n r F parent).card * (r + 2) := by
          apply Finset.card_biUnion_le_card_mul
          exact hrescard
        _ ≤ (C * 2 ^ (r + 3)) * (r + 2) := Nat.mul_le_mul_right _ hHcard
        _ = C * 2 ^ (r + 3) * (r + 2) := rfl
  · rw [hcomplete]
    exact Nat.zero_le _

noncomputable def goodSets (X : Finset α) (F : Hypergraph α) : Finset (Finset α) :=
  X.powerset.filter (GoodSet F)

lemma mem_goodSets {X B : Finset α} {F : Hypergraph α} :
    B ∈ goodSets X F ↔ B ⊆ X ∧ GoodSet F B := by
  simp [goodSets]

lemma good_leaf_count_le_goodSets {C n r : ℕ} (hn : r + 2 ≤ n)
    {X : Finset α} {F : Hypergraph α}
    (hedges : ∀ A ∈ F, A ⊆ X ∧ A.card = n)
    (beckFixedBudget : BeckFixedBudget (α := α) C n r) :
    leafCount (fun q => ¬ Failed (4 * C * 2 ^ n) F q)
        (build (4 * C * 2 ^ n) r X F X.card (Partial.mk ∅ ∅)) ≤
      (goodSets X F).card := by
  let t := build (4 * C * 2 ^ n) r X F X.card (Partial.mk ∅ ∅)
  let G : Finset (Partial α) :=
    (t.leaves.filter (fun q => ¬ Failed (4 * C * 2 ^ n) F q)).toFinset
  have hnodup : t.leaves.Nodup := leaves_build_nodup _ _ _ _ _ _ (by simp [Partial.Valid])
  have hGcard : G.card = leafCount (fun q => ¬ Failed (4 * C * 2 ^ n) F q) t := by
    simpa [G, leafCount] using
      List.toFinset_card_of_nodup
        (hnodup.filter (fun q => ¬ Failed (4 * C * 2 ^ n) F q))
  have hex : ∀ q ∈ G, ∃ B : Finset α,
      B ∈ goodSets X F ∧ Extends q B := by
    intro q hq
    have hqBoth : q ∈ t.leaves ∧ ¬ Failed (4 * C * 2 ^ n) F q := by
      simpa [G] using hq
    have hqList : q ∈ t.leaves := hqBoth.1
    have hqNF : ¬ Failed (4 * C * 2 ^ n) F q := hqBoth.2
    obtain ⟨B, hBX, hext, hproper⟩ :=
      nonfailed_leaf_has_proper_extension hn hedges beckFixedBudget hqList hqNF
    exact ⟨B, mem_goodSets.mpr ⟨hBX, (goodSet_iff_properColoring F B).mpr hproper⟩, hext⟩
  let pick (q : Partial α) : Finset α :=
    if hq : q ∈ G then Classical.choose (hex q hq) else ∅
  have hpickGood (q : Partial α) (hq : q ∈ G) : pick q ∈ goodSets X F := by
    simpa only [pick, dif_pos hq] using (Classical.choose_spec (hex q hq)).1
  have hpickExt (q : Partial α) (hq : q ∈ G) : Extends q (pick q) := by
    simpa only [pick, dif_pos hq] using (Classical.choose_spec (hex q hq)).2
  rw [← hGcard]
  refine Finset.card_le_card_of_injOn pick (fun q hq => hpickGood q hq) ?_
  intro q₀ hq₀ q₁ hq₁ heq
  have hq₀Both : q₀ ∈ t.leaves ∧ ¬ Failed (4 * C * 2 ^ n) F q₀ := by
    simpa [G] using hq₀
  have hq₁Both : q₁ ∈ t.leaves ∧ ¬ Failed (4 * C * 2 ^ n) F q₁ := by
    simpa [G] using hq₁
  exact compatible_leaves_eq (4 * C * 2 ^ n) r X F X.card
    (Partial.mk ∅ ∅) q₀ q₁ (pick q₀) hq₀Both.1 hq₁Both.1
    (hpickExt q₀ hq₀) (by simpa [heq] using hpickExt q₁ hq₁)

/-- Integer-budget resolution on a linearly ordered finite ambient set. -/
theorem natBudgetResolutionLinear (C n r : ℕ) (hC : 0 < C) (hn : r + 2 ≤ n)
    (X : Finset α) (F : Hypergraph α)
    (hedges : ∀ A ∈ F, A ⊆ X ∧ A.card = n)
    (hcard : F.card ≤ C * 2 ^ n)
    (beckFixedBudget : BeckFixedBudget (α := α) C n r) :
    2 ^ X.card ≤
      2 ^ (C * 2 ^ (r + 3) * (r + 2) + 1) * (goodSets X F).card := by
  let threshold := 4 * C * 2 ^ n
  let t := build threshold r X F X.card (Partial.mk ∅ ∅)
  let P : Partial α → Prop := fun q => Failed threshold F q
  let K := C * 2 ^ (r + 3) * (r + 2)
  have hfailed : 2 * leafMass X P t ≤ 2 ^ X.card := by
    simpa [threshold, t, P] using failed_mass_at_most_half C n r hC X F hcard
  have hvalid : (Partial.mk (α := α) ∅ ∅).Valid X := by simp [Partial.Valid]
  have hall : allMass X t = 2 ^ X.card := by
    simpa [t, threshold, Partial.uncolored, Partial.colored] using
      allMass_build threshold r X F X.card (Partial.mk ∅ ∅) hvalid
  have hsplit : leafMass X P t + leafMass X (fun q => ¬ P q) t = 2 ^ X.card := by
    rw [leafMass_add_compl, hall]
  have hgoodMass : 2 ^ X.card ≤ 2 * leafMass X (fun q => ¬ P q) t := by omega
  have hmassCount : leafMass X (fun q => ¬ P q) t ≤
      2 ^ K * leafCount (fun q => ¬ P q) t := by
    apply leafMass_le_pow_mul_leafCount
    intro q hq hqNF
    exact bounded_uncolored_leaf hn hedges (by simpa [t, threshold] using hq)
      (by simpa [P, threshold] using hqNF)
  have hcount : leafCount (fun q => ¬ P q) t ≤ (goodSets X F).card := by
    simpa [P, t, threshold] using good_leaf_count_le_goodSets hn hedges beckFixedBudget
  calc
    2 ^ X.card ≤ 2 * leafMass X (fun q => ¬ P q) t := hgoodMass
    _ ≤ 2 * (2 ^ K * leafCount (fun q => ¬ P q) t) := Nat.mul_le_mul_left 2 hmassCount
    _ ≤ 2 * (2 ^ K * (goodSets X F).card) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ hcount)
    _ = 2 ^ (K + 1) * (goodSets X F).card := by rw [pow_succ]; ring
    _ = 2 ^ (C * 2 ^ (r + 3) * (r + 2) + 1) * (goodSets X F).card := rfl

section Transport

universe u

variable {γ : Type u} [DecidableEq γ]

/-- Restrict a finite set to the finite subtype carried by `X`. -/
def restrictSet (X A : Finset γ) : Finset {x // x ∈ X} :=
  X.attach.filter fun x => x.1 ∈ A

@[simp] lemma mem_restrictSet {X A : Finset γ} {x : {x // x ∈ X}} :
    x ∈ restrictSet X A ↔ x.1 ∈ A := by
  simp [restrictSet]

lemma image_restrictSet {X A : Finset γ} (hA : A ⊆ X) :
    (restrictSet X A).image Subtype.val = A := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact (mem_restrictSet.mp hy)
  · intro hx
    exact Finset.mem_image.mpr ⟨⟨x, hA hx⟩, mem_restrictSet.mpr hx, rfl⟩

lemma card_restrictSet {X A : Finset γ} (hA : A ⊆ X) :
    (restrictSet X A).card = A.card := by
  calc
    (restrictSet X A).card =
        ((restrictSet X A).image (@Subtype.val γ (fun x => x ∈ X))).card :=
      (Finset.card_image_of_injective
        (f := @Subtype.val γ (fun x => x ∈ X)) (restrictSet X A)
        Subtype.val_injective).symm
    _ = A.card := congrArg Finset.card (image_restrictSet hA)

lemma restrictSet_injective_on {X : Finset γ} :
    Set.InjOn (restrictSet X) {A : Finset γ | A ⊆ X} := by
  intro A hA B hB heq
  have := congrArg (Finset.image Subtype.val) heq
  simpa [image_restrictSet hA, image_restrictSet hB] using this

def restrictHypergraph (X : Finset γ) (F : Hypergraph γ) :
    Hypergraph {x // x ∈ X} := F.image (restrictSet X)

lemma card_restrictHypergraph {X : Finset γ} {F : Hypergraph γ}
    (hedges : ∀ A ∈ F, A ⊆ X) :
    (restrictHypergraph X F).card = F.card := by
  apply Finset.card_image_of_injOn
  intro A hA B hB heq
  exact restrictSet_injective_on (hedges A hA) (hedges B hB) heq

def liftBack {X : Finset γ} (B : Finset {x // x ∈ X}) : Finset γ :=
  B.image Subtype.val

lemma liftBack_subset {X : Finset γ} (B : Finset {x // x ∈ X}) : liftBack B ⊆ X := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  exact y.2

lemma liftBack_injective {X : Finset γ} : Function.Injective (@liftBack γ _ X) := by
  intro B₀ B₁ heq
  ext x
  constructor <;> intro hx
  · have hm : x.1 ∈ liftBack B₀ := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rw [heq] at hm
    rcases Finset.mem_image.mp hm with ⟨y, hy, hval⟩
    simpa [Subtype.ext hval] using hy
  · have hm : x.1 ∈ liftBack B₁ := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rw [← heq] at hm
    rcases Finset.mem_image.mp hm with ⟨y, hy, hval⟩
    simpa [Subtype.ext hval] using hy

lemma properColoring_liftBack {X : Finset γ} {F : Hypergraph γ}
    (hedges : ∀ A ∈ F, A ⊆ X) {B : Finset {x // x ∈ X}}
    (hB : ProperColoring (restrictHypergraph X F) B) :
    ProperColoring F (liftBack B) := by
  intro A hAF
  have hmem : restrictSet X A ∈ restrictHypergraph X F :=
    Finset.mem_image.mpr ⟨A, hAF, rfl⟩
  obtain ⟨hred, hblue⟩ := hB (restrictSet X A) hmem
  constructor
  · rcases hred with ⟨x, hx⟩
    have hx' := Finset.mem_inter.mp hx
    refine ⟨x.1, Finset.mem_inter.mpr ⟨mem_restrictSet.mp hx'.1, ?_⟩⟩
    exact Finset.mem_image.mpr ⟨x, hx'.2, rfl⟩
  · rcases hblue with ⟨x, hx⟩
    have hx' := Finset.mem_sdiff.mp hx
    refine ⟨x.1, Finset.mem_sdiff.mpr ⟨mem_restrictSet.mp hx'.1, ?_⟩⟩
    intro hxImage
    rcases Finset.mem_image.mp hxImage with ⟨y, hyB, hxy⟩
    exact hx'.2 (by simpa [Subtype.ext hxy] using hyB)

lemma goodSets_restrict_card_le {X : Finset γ} {F : Hypergraph γ}
    (hedges : ∀ A ∈ F, A ⊆ X) :
    (goodSets (Finset.univ : Finset {x // x ∈ X}) (restrictHypergraph X F)).card ≤
      (goodSets X F).card := by
  refine Finset.card_le_card_of_injOn liftBack ?_ ?_
  · intro B hB
    have hgood : GoodSet (restrictHypergraph X F) B := by
      exact (Finset.mem_filter.mp hB).2
    have hproper := (goodSet_iff_properColoring _ _).mp hgood
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (liftBack_subset B),
      (goodSet_iff_properColoring _ _).mpr (properColoring_liftBack hedges hproper)⟩
  · exact liftBack_injective.injOn

/-- API expected from the Beck--Lu part: the same fixed budget works over
every finite vertex type. -/
def UniversalBeckFixedBudget (_ambient : Type u) (C n r : ℕ) : Prop :=
  ∀ (β : Type u) [Fintype β] [DecidableEq β], BeckFixedBudget (α := β) C n r

/-- Public integer-budget theorem.  The vertex type need not be finite or
ordered; all work is transported to the finite subtype of the ground set. -/
theorem NatBudgetResolution (C n r : ℕ) (hC : 0 < C) (hn : r + 2 ≤ n)
    (X : Finset γ) (F : Hypergraph γ)
    (hedges : ∀ A ∈ F, A ⊆ X ∧ A.card = n)
    (hcard : F.card ≤ C * 2 ^ n)
    (beckFixedBudget : UniversalBeckFixedBudget γ C n r) :
    2 ^ X.card ≤
      2 ^ (C * 2 ^ (r + 3) * (r + 2) + 1) * (goodSets X F).card := by
  let β := {x // x ∈ X}
  let : LinearOrder β := (Fintype.equivFin β).linearOrder
  let F' : Hypergraph β := restrictHypergraph X F
  have hedges' : ∀ A ∈ F', A ⊆ (Finset.univ : Finset β) ∧ A.card = n := by
    intro A hA
    rcases Finset.mem_image.mp hA with ⟨E, hEF, rfl⟩
    exact ⟨Finset.subset_univ _, (card_restrictSet (hedges E hEF).1).trans (hedges E hEF).2⟩
  have hcard' : F'.card ≤ C * 2 ^ n := by
    rw [show F'.card = F.card from card_restrictHypergraph (fun A hA => (hedges A hA).1)]
    exact hcard
  have hbeck : BeckFixedBudget (α := β) C n r := beckFixedBudget β
  have hlinear := natBudgetResolutionLinear (α := β) C n r hC hn
    (Finset.univ : Finset β) F' hedges' hcard' hbeck
  have hgoodCard := goodSets_restrict_card_le (fun A hA => (hedges A hA).1)
  have hXcard : (Finset.univ : Finset β).card = X.card := by simp [β]
  rw [hXcard] at hlinear
  exact hlinear.trans (Nat.mul_le_mul_left _ hgoodCard)

end Transport

end Erdos1027.Tree
