-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.E5IntersectionColoring
import ErdosProblems.Erdos1177.EHBase
import ErdosProblems.Erdos1177.E4Proof
import ErdosProblems.Erdos1177.ReiherPassage

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Hajnal–Komjáth's grid and the loose seven-cycle

This module formalizes the part of Hajnal–Komjáth, *Obligatory subsystems of
triple systems* (2008), Theorem 1 and its corollary, needed for the loose
seven-cycle.
-/

open Cardinal

namespace Erdos1177

universe u

/-- The finite Hajnal–Komjáth system `Mₙ`.  The three tags represent
`x(i,j)`, `y(i,j)`, and `z(i,j)` respectively; its edges are
`{x(i,j), y(i,k), z(j,k)}`. -/
noncomputable def hkMn (n : ℕ) : FTS where
  V := Fin 3 × Fin n × Fin n
  edges := ((Finset.univ : Finset (Fin n × Fin n × Fin n)).image fun p =>
    ({(0, p.1, p.2.1), (1, p.1, p.2.2), (2, p.2.1, p.2.2)} :
      Finset (Fin 3 × Fin n × Fin n)))
  card3 := by
    intro e he
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at he
    obtain ⟨p, rfl⟩ := he
    simp +decide

/-
The explicit seven-edge table on pp. 6–7 of Hajnal–Komjáth embeds the
loose seven-cycle into `M₃`.
-/
theorem looseCycle7_sub_hkMn3 : looseCycle7.Sub (hkMn 3) := by
  unfold FTS.Sub;
  by_contra h;
  push_neg at h;
  exact absurd ( h ( fun x => if x = Sum.inl 0 then ( 0, 0, 0 ) else if x = Sum.inl 1 then ( 1, 0, 0 ) else if x = Sum.inl 2 then ( 2, 1, 0 ) else if x = Sum.inl 3 then ( 0, 1, 1 ) else if x = Sum.inl 4 then ( 1, 1, 1 ) else if x = Sum.inl 5 then ( 2, 2, 1 ) else if x = Sum.inl 6 then ( 1, 0, 1 ) else if x = Sum.inr 0 then ( 2, 0, 0 ) else if x = Sum.inr 1 then ( 0, 0, 1 ) else if x = Sum.inr 2 then ( 1, 1, 0 ) else if x = Sum.inr 3 then ( 2, 1, 1 ) else if x = Sum.inr 4 then ( 0, 1, 2 ) else if x = Sum.inr 5 then ( 0, 0, 2 ) else ( 2, 0, 1 ) ) ( by decide ) ) ( by decide )

/-- A six-point realization of a fixed `3 × 3` array of lower vertices. -/
def HKRealizes (H : Hypergraph W) (Z : Fin 3 → Fin 3 → W)
    (X Y : Fin 3 → W) : Prop :=
  Function.Injective X ∧ Function.Injective Y ∧
  (∀ i j, X i ≠ Y j) ∧
  (∀ i k l, X i ≠ Z k l) ∧ (∀ i k l, Y i ≠ Z k l) ∧
  ∀ j k, ({X j, Y k, Z j k} : Set W) ∈ H.edges

/-
Three mutually disjoint realizations over one injective lower array assemble
an embedding of `M₃`.
-/
theorem hkMn3_embeds_of_realizations (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (hZ : ∀ i j i' j', Z i j = Z i' j' → i = i' ∧ j = j')
    (X Y : Fin 3 → Fin 3 → W)
    (hreal : ∀ a, HKRealizes H Z (X a) (Y a))
    (hdisjX : ∀ a b i j, a ≠ b → X a i ≠ X b j)
    (hdisjY : ∀ a b i j, a ≠ b → Y a i ≠ Y b j)
    (hdisjXY : ∀ a b i j, a ≠ b → X a i ≠ Y b j) :
    (hkMn 3).Embeds H := by
  simp +decide [ HKRealizes ] at hreal;
  refine' ⟨ fun x => _, _, _ ⟩;
  exact if x.1 = 0 then X x.2.1 x.2.2 else if x.1 = 1 then Y x.2.1 x.2.2 else Z x.2.1 x.2.2;
  · intro x y hxy;
    rcases x with ⟨ x₁, x₂, x₃ ⟩ ; rcases y with ⟨ y₁, y₂, y₃ ⟩ ; simp +decide at hxy ⊢;
    grind;
  · simp +decide [ hkMn ];
    rintro e a b c rfl; simp +decide [ *, Set.image_insert_eq, Set.image_singleton ] ;

/-- The six-point support of one realization. -/
noncomputable def hkRealizationSupport (X Y : Fin 3 → W) : Finset W := by
  classical
  exact Finset.univ.image X ∪ Finset.univ.image Y

lemma hkRealizationSupport_card_le (X Y : Fin 3 → W) :
    (hkRealizationSupport X Y).card ≤ 6 := by
  convert! Finset.card_union_le ( Finset.image X Finset.univ ) ( Finset.image Y Finset.univ ) |> le_trans <| add_le_add ( Finset.card_image_le ) ( Finset.card_image_le ) using 1

lemma mem_hkRealizationSupport_left (X Y : Fin 3 → W) (i : Fin 3) :
    X i ∈ hkRealizationSupport X Y := by
  simp +decide [ hkRealizationSupport, Finset.mem_union, Finset.mem_image ]

lemma mem_hkRealizationSupport_right (X Y : Fin 3 → W) (i : Fin 3) :
    Y i ∈ hkRealizationSupport X Y := by
  convert! Finset.mem_union.mpr ( Or.inr <| Finset.mem_image.mpr ⟨ i, Finset.mem_univ _, rfl ⟩ ) using 1

lemma hk_support_disjoint_cross
    (X Y X' Y' : Fin 3 → W)
    (hd : Disjoint (hkRealizationSupport X Y) (hkRealizationSupport X' Y')) :
    (∀ i j, X i ≠ X' j) ∧ (∀ i j, Y i ≠ Y' j) ∧
      (∀ i j, X i ≠ Y' j) ∧ (∀ i j, X' i ≠ Y j) := by
  simp_all +decide only [ne_eq];
  exact ⟨ fun i j => fun h => hd ( Or.inl ⟨ i, rfl ⟩ ) |>.1 j h.symm, fun i j => fun h => hd ( Or.inr ⟨ i, rfl ⟩ ) |>.2 j h.symm, fun i j => fun h => hd ( Or.inl ⟨ i, rfl ⟩ ) |>.2 j h.symm ⟩

lemma hk_support_disjoint_of_avoids
    (X Y X' Y' : Fin 3 → W)
    (hX : ∀ i, X' i ∉ hkRealizationSupport X Y)
    (hY : ∀ i, Y' i ∉ hkRealizationSupport X Y) :
    Disjoint (hkRealizationSupport X Y) (hkRealizationSupport X' Y') := by
  simp_all +decide [ Finset.disjoint_left, hkRealizationSupport ];
  grind

lemma hk_avoid_support (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (havoid : ∀ S : Finset W, S.card ≤ 18 →
      ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
        (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S))
    (X0 Y0 : Fin 3 → W) :
    ∃ X1 Y1 : Fin 3 → W, HKRealizes H Z X1 Y1 ∧
      Disjoint (hkRealizationSupport X0 Y0) (hkRealizationSupport X1 Y1) := by
  obtain ⟨ X1, Y1, h1, h2, h3 ⟩ := havoid ( hkRealizationSupport X0 Y0 ) ( by exact le_trans ( hkRealizationSupport_card_le X0 Y0 ) ( by decide ) );
  exact ⟨ X1, Y1, h1, hk_support_disjoint_of_avoids X0 Y0 X1 Y1 h2 h3 ⟩

lemma hk_avoid_two_supports (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (havoid : ∀ S : Finset W, S.card ≤ 18 →
      ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
        (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S))
    (X0 Y0 X1 Y1 : Fin 3 → W) :
    ∃ X2 Y2 : Fin 3 → W, HKRealizes H Z X2 Y2 ∧
      Disjoint (hkRealizationSupport X0 Y0) (hkRealizationSupport X2 Y2) ∧
      Disjoint (hkRealizationSupport X1 Y1) (hkRealizationSupport X2 Y2) := by
  classical
  let S0 := hkRealizationSupport X0 Y0
  let S1 := hkRealizationSupport X1 Y1
  have hc : (S0 ∪ S1).card ≤ 18 := by
    calc
      (S0 ∪ S1).card ≤ S0.card + S1.card := Finset.card_union_le _ _
      _ ≤ 6 + 6 := Nat.add_le_add (hkRealizationSupport_card_le X0 Y0)
        (hkRealizationSupport_card_le X1 Y1)
      _ ≤ 18 := by omega
  obtain ⟨X2, Y2, hr, hx, hy⟩ := havoid (S0 ∪ S1) hc
  have hx0 : ∀ i, X2 i ∉ S0 := by
    intro i hi
    exact hx i (Finset.mem_union.mpr (Or.inl hi))
  have hy0 : ∀ i, Y2 i ∉ S0 := by
    intro i hi
    exact hy i (Finset.mem_union.mpr (Or.inl hi))
  have hx1 : ∀ i, X2 i ∉ S1 := by
    intro i hi
    exact hx i (Finset.mem_union.mpr (Or.inr hi))
  have hy1 : ∀ i, Y2 i ∉ S1 := by
    intro i hi
    exact hy i (Finset.mem_union.mpr (Or.inr hi))
  exact ⟨X2, Y2, hr,
    hk_support_disjoint_of_avoids X0 Y0 X2 Y2 hx0 hy0,
    hk_support_disjoint_of_avoids X1 Y1 X2 Y2 hx1 hy1⟩

lemma hk_select_three (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (havoid : ∀ S : Finset W, S.card ≤ 18 →
      ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
        (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S)) :
    ∃ X0 Y0 X1 Y1 X2 Y2 : Fin 3 → W,
      HKRealizes H Z X0 Y0 ∧ HKRealizes H Z X1 Y1 ∧ HKRealizes H Z X2 Y2 ∧
      Disjoint (hkRealizationSupport X0 Y0) (hkRealizationSupport X1 Y1) ∧
      Disjoint (hkRealizationSupport X0 Y0) (hkRealizationSupport X2 Y2) ∧
      Disjoint (hkRealizationSupport X1 Y1) (hkRealizationSupport X2 Y2) := by
  obtain ⟨X0, Y0, hR0⟩ : ∃ X0 Y0 : Fin 3 → W, HKRealizes H Z X0 Y0 := by
    exact Exists.elim ( havoid ∅ ( by simp +decide ) ) fun X hX => Exists.elim hX fun Y hY => ⟨ X, Y, hY.1 ⟩;
  obtain ⟨ X1, Y1, hR1, h01 ⟩ := hk_avoid_support H Z havoid X0 Y0;
  obtain ⟨ X2, Y2, hR2, h02, h12 ⟩ := hk_avoid_two_supports H Z havoid X0 Y0 X1 Y1;
  exact ⟨ X0, Y0, X1, Y1, X2, Y2, hR0, hR1, hR2, h01, h02, h12 ⟩

lemma hk_three_disjoint_realizations (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (havoid : ∀ S : Finset W, S.card ≤ 18 →
      ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
        (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S)) :
    ∃ X Y : Fin 3 → Fin 3 → W,
      (∀ a, HKRealizes H Z (X a) (Y a)) ∧
      ∀ a b, a ≠ b →
        Disjoint (hkRealizationSupport (X a) (Y a))
          (hkRealizationSupport (X b) (Y b)) := by
  obtain ⟨ X0, Y0, X1, Y1, X2, Y2, hR0, hR1, hR2, d01, d02, d12 ⟩ := hk_select_three H Z havoid;
  refine' ⟨ fun a => if a = 0 then X0 else if a = 1 then X1 else X2, fun a => if a = 0 then Y0 else if a = 1 then Y1 else Y2, _, _ ⟩ <;> simp +decide only [Fin.isValue, ne_eq];
  · exact ⟨ hR0, hR1, hR2 ⟩;
  · exact ⟨ ⟨ d01, d02 ⟩, ⟨ d01.symm, d12 ⟩, d02.symm, d12.symm ⟩

/-
Greedy finite blocking lemma: if every set of at most eighteen forbidden
vertices can be avoided by a realization over `Z`, then three pairwise disjoint
realizations exist and hence `M₃` embeds.
-/
theorem hkMn3_embeds_of_avoidance (H : Hypergraph W)
    (Z : Fin 3 → Fin 3 → W)
    (hZ : ∀ i j i' j', Z i j = Z i' j' → i = i' ∧ j = j')
    (havoid : ∀ S : Finset W, S.card ≤ 18 →
      ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
        (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S)) :
    (hkMn 3).Embeds H := by
  convert! hkMn3_embeds_of_realizations H Z hZ _ _ _ _ _ _ using 1;
  exact fun a i => ( hk_three_disjoint_realizations H Z havoid |> Classical.choose ) a i;
  exact fun a i => ( hk_three_disjoint_realizations H Z havoid |> Classical.choose_spec |> Classical.choose ) a i;
  · exact Classical.choose_spec ( hk_three_disjoint_realizations H Z havoid ) |> Classical.choose_spec |> And.left;
  · intro a b i j hab;
    have := Classical.choose_spec ( hk_three_disjoint_realizations H Z havoid ) |> Classical.choose_spec;
    exact hk_support_disjoint_cross _ _ _ _ ( this.2 a b hab ) |>.1 i j;
  · intro a b i j hab;
    have := Classical.choose_spec ( hk_three_disjoint_realizations H Z havoid ) |> Classical.choose_spec;
    have := hk_support_disjoint_cross _ _ _ _ ( this.2 a b hab );
    grind;
  · intro a b i j hab
    generalize_proofs at *;
    rename_i h₁ h₂;
    have := Classical.choose_spec h₂ |>.2 a b hab; simp_all +decide only [ne_eq] ;
    exact fun h => this ( Or.inl ⟨ i, rfl ⟩ ) |>.2 j h.symm

/-- A finite set blocks realizations over `Z` if every realization meets it. -/
def HKBlocks (H : Hypergraph W) (Z : Fin 3 → Fin 3 → W) (S : Finset W) : Prop :=
  S.card ≤ 18 ∧ ∀ X Y : Fin 3 → W, HKRealizes H Z X Y →
    (∃ i, X i ∈ S) ∨ ∃ i, Y i ∈ S

/-- A canonical chosen blocker, empty if no blocker exists. -/
noncomputable def hkBlocker (H : Hypergraph W) (Z : Fin 3 → Fin 3 → W) : Finset W := by
  classical
  exact if h : ∃ S : Finset W, HKBlocks H Z S then h.choose else ∅

lemma hkBlocker_spec (H : Hypergraph W) (Z : Fin 3 → Fin 3 → W)
    (h : ∃ S : Finset W, HKBlocks H Z S) :
    HKBlocks H Z (hkBlocker H Z) := by
  have := Classical.choose_spec h;
  unfold hkBlocker; aesop;

/-- One combined closure step: pair completion, followed by all chosen blockers
whose nine-point premise is already present. -/
def HKCloseStep (H : Hypergraph W) (X : Set W) : Set W :=
  DCloseStep H 2 X ∪
    {v | ∃ Z : Fin 3 → Fin 3 → W, (∀ i j, Z i j ∈ X) ∧ v ∈ hkBlocker H Z}

def HKCloseIter (H : Hypergraph W) (X : Set W) : ℕ → Set W
  | 0 => X
  | k + 1 => HKCloseStep H (HKCloseIter H X k)

def HKcl (H : Hypergraph W) (X : Set W) : Set W := ⋃ k, HKCloseIter H X k

lemma subset_HKCloseIter (H : Hypergraph W) (X : Set W) (k : ℕ) :
    X ⊆ HKCloseIter H X k := by
  induction' k with k ih <;> simp_all +decide [ Set.subset_def, HKCloseIter ];
  exact fun x hx => Set.mem_union_left _ ( Set.mem_union_left _ ( ih x hx ) )

lemma HKCloseIter_mono_index (H : Hypergraph W) (X : Set W) {k l : ℕ}
    (h : k ≤ l) : HKCloseIter H X k ⊆ HKCloseIter H X l := by
  refine' Nat.le_induction _ _ l h <;> intro l _ <;> simp_all +decide [ Set.subset_def, HKCloseIter ];
  exact fun h x hx => Set.mem_union_left _ ( Set.mem_union_left _ ( h x hx ) )

lemma subset_HKcl (H : Hypergraph W) (X : Set W) : X ⊆ HKcl H X := by
  exact Set.subset_iUnion ( fun k => HKCloseIter H X k ) 0 |> Set.Subset.trans ( subset_HKCloseIter H X 0 )

lemma HKcl_mono (H : Hypergraph W) {X Y : Set W} (h : X ⊆ Y) :
    HKcl H X ⊆ HKcl H Y := by
  -- By induction on $k$, we can show that $HKCloseIter H X k \subseteq HKCloseIter H Y k$ for all $k$.
  have h_ind : ∀ k, HKCloseIter H X k ⊆ HKCloseIter H Y k := by
    intro k;
    induction' k with k ih;
    · exact h;
    · refine' Set.union_subset_union ( Set.union_subset_union _ _ ) _;
      · exact ih;
      · exact fun v hv => by obtain ⟨ x, hx, y, hy, hxy, hv ⟩ := hv; exact ⟨ x, ih hx, y, ih hy, hxy, hv ⟩ ;
      · exact fun v hv => by obtain ⟨ Z, hZ₁, hZ₂ ⟩ := hv; exact ⟨ Z, fun i j => ih ( hZ₁ i j ), hZ₂ ⟩ ;
  exact Set.iUnion_mono h_ind

lemma HKcl_pairClosed (H : Hypergraph W) (X : Set W) :
    DClosed H 2 (HKcl H X) := by
  intro x hx; simp_all +decide only [ne_eq] ;
  intro y hy hxy; simp_all +decide [ Set.subset_def, HKcl ] ;
  obtain ⟨ kx, hkx ⟩ := hx; obtain ⟨ ky, hky ⟩ := hy; use fun z hz => ⟨ kx + ky + 1, ?_ ⟩ ; simp_all +decide [ Set.subset_def, HKCloseIter ] ;
  refine' Set.mem_union_left _ ( Set.mem_union_right _ _ );
  exact ⟨ x, HKCloseIter_mono_index H X ( by linarith ) hkx, y, HKCloseIter_mono_index H X ( by linarith ) hky, hxy, hz ⟩

lemma HKcl_blockerClosed (H : Hypergraph W) (X : Set W)
    (Z : Fin 3 → Fin 3 → W) (hZ : ∀ i j, Z i j ∈ HKcl H X) :
    (hkBlocker H Z : Set W) ⊆ HKcl H X := by
  by_contra h_false;
  obtain ⟨ v, hv ⟩ := Set.not_subset.mp h_false;
  obtain ⟨ k, hk ⟩ : ∃ k, ∀ i j, Z i j ∈ HKCloseIter H X k := by
    choose k hk using fun i j => Set.mem_iUnion.mp ( hZ i j );
    exact ⟨ Finset.univ.sup ( fun p : Fin 3 × Fin 3 => k p.1 p.2 ), fun i j => HKCloseIter_mono_index H X ( Finset.le_sup ( f := fun p : Fin 3 × Fin 3 => k p.1 p.2 ) ( Finset.mem_univ ( i, j ) ) ) ( hk i j ) ⟩;
  refine' hv.2 ( Set.mem_iUnion.2 ⟨ k + 1, Set.mem_union_right _ _ ⟩ );
  exact ⟨ Z, hk, hv.1 ⟩

lemma HKCloseStep_card_le (H : Hypergraph W) (htri : H.IsTripleSystem)
    (X : Set W) : #(HKCloseStep H X) ≤ #X + ℵ₀ := by
  have h_card_le : #(DCloseStep H 2 X) ≤ #X + ℵ₀ := by
    convert! DCloseStep_card_le H htri 2 X using 1;
  have h_card_le : #(⋃ (Z : Fin 3 → Fin 3 → X), (hkBlocker H (fun i j => Z i j) : Set W)) ≤ #(Fin 3 → Fin 3 → X) * 18 := by
    refine' le_trans ( Cardinal.mk_iUnion_le _ ) _;
    gcongr;
    refine' ciSup_le' _;
    intro Z; exact (by
    by_cases h : ∃ S : Finset W, HKBlocks H ( fun i j => ( Z i j : W ) ) S <;> simp_all +decide only [SetLike.coe_sort_coe, mk_fintype, Fintype.card_coe, Nat.cast_le_ofNat];
    exact h.choose_spec.1);
  by_cases hX : Infinite X <;> simp_all +decide only [ge_iff_le];
  · refine' le_trans ( Cardinal.mk_union_le _ _ ) _;
    refine' le_trans ( add_le_add ‹_› _ ) _;
    exact ( #X ^ 3 ) ^ 3 * 18;
    · refine' le_trans _ h_card_le;
      refine' Cardinal.mk_le_mk_of_subset _;
      intro v hv; obtain ⟨ Z, hZ₁, hZ₂ ⟩ := hv; exact Set.mem_iUnion.2 ⟨ fun i j => ⟨ Z i j, hZ₁ i j ⟩, hZ₂ ⟩ ;
    · simp +decide [ Cardinal.add_eq_max, Cardinal.mul_eq_max, Cardinal.power_nat_eq ];
      exact le_trans ( mul_le_mul_right ( Cardinal.nat_lt_aleph0 18 |> le_of_lt ) _ ) ( by simp +decide [ Cardinal.mul_eq_max ] );
  · convert! Cardinal.mk_union_le _ _ |> le_trans <| add_le_add ‹#↑(DCloseStep H 2 X) ≤ #↑X + ℵ₀› h_card_le using 1;
    · congr with x ; simp +decide [ HKCloseStep ];
      constructor <;> intro h;
      · rcases h with ( h | ⟨ Z, hZ₁, hZ₂ ⟩ );
        · exact Or.inl h;
        · exact Or.inr ⟨ fun i j => ⟨ Z i j, hZ₁ i j ⟩, by simpa [ Subtype.ext_iff ] using! hZ₂ ⟩;
      · exact h.imp id fun ⟨ Z, hZ ⟩ => ⟨ _, fun i j => Z i j |>.2, hZ ⟩;
    · have := Fintype.ofFinite X; simp +decide [ Cardinal.mk_fintype ] ;
      rw [ Cardinal.add_eq_left ];
      · norm_num;
      · exact_mod_cast Cardinal.nat_lt_aleph0 _ |> le_of_lt

lemma HKcl_card_le (H : Hypergraph W) (htri : H.IsTripleSystem) (X : Set W) :
    #(HKcl H X) ≤ #X + ℵ₀ := by
  convert! Cardinal.mk_iUnion_le _ |> le_trans <| _;
  rotate_left;
  exact ULift ℕ
  exact fun i => HKCloseIter H X i.down
  generalize_proofs at *;
  · refine' le_trans ( mul_le_mul_right ( ciSup_le _ ) _ ) _;
    exact #X + ℵ₀;
    · intro x;
      induction' x.down with k ih;
      · exact le_add_right ( by rfl );
      · convert! le_trans ( HKCloseStep_card_le H htri ( HKCloseIter H X k ) ) _ using 1;
        convert! add_le_add_right ih ℵ₀ using 1;
        · rw [ add_comm ];
        · rw [ add_comm, Cardinal.add_eq_max ];
          · rw [ Cardinal.add_eq_right ]; all_goals exact le_max_left _ _;
          · norm_num;
    · simp +decide [ Cardinal.mk_nat ];
  · ext; simp [HKcl]

/-- The exact closed-filtration interface used in the proof of HK Theorem 1.
Pair closure rules out a unique top vertex; finite blocking-set closure reflects
a blocker for a lower grid below the current level. -/
structure HKFiltration (H : Hypergraph W) where
  Idx : Type u
  linearOrder : LinearOrder Idx
  wellFounded : WellFoundedLT Idx
  rank : W → Idx
  levelColorable : ∀ a, ∃ c : W → ℕ,
    ∀ e ∈ H.edges, e ⊆ {v | rank v = a} →
      ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y
  noUniqueTop : ∀ (x y z : W), rank x < rank z → rank y < rank z → x ≠ y →
    ∀ e ∈ H.edges, x ∈ e → y ∈ e → z ∈ e → False
  reflectBlocker : ∀ (a : Idx) (Z : Fin 3 → Fin 3 → W),
    (∀ i j, rank (Z i j) < a) →
    (∃ S : Finset W, HKBlocks H Z S) →
    ∃ S : Finset W, HKBlocks H Z S ∧ ∀ x ∈ S, rank x < a

lemma Hsub_linear_of_linear (H : Hypergraph W) (hlin : H.Linear) (S : Set W) :
    (Hsub H S).Linear := by
  -- Let $e'$ and $f'$ be edges in the induced hypergraph $Hsub H S$ that share two vertices.
  intro e' f' h_inter
  simp_all +decide only [ne_eq];
  intro g' hne;
  contrapose! hlin;
  refine' ⟨ _, f', _, g', _, _ ⟩;
  · exact fun h => hne <| Set.ext fun x => by simpa using! Set.ext_iff.mp h x;
  · obtain ⟨ x, hx, y, hy, hxy ⟩ := hlin; use x, by aesop, y, by aesop;
    exact fun h => hxy <| Subtype.ext h

lemma hkMn_embeds_of_Hsub (H : Hypergraph W) (S : Set W)
    (h : (hkMn 3).Embeds (Hsub H S)) : (hkMn 3).Embeds H := by
  obtain ⟨ f, hf₁, hf₂ ⟩ := h;
  refine' ⟨ fun x => f x, _, _ ⟩;
  · exact Subtype.coe_injective.comp hf₁;
  · intro e he; specialize hf₂ e he; simp_all +decide [ Set.ext_iff, Hsub ] ;
    convert! hf₂ using 1;
    ext; simp [Set.mem_image]

lemma hk_level_colorable (H : Hypergraph W) (htri : H.IsTripleSystem)
    (hlin : H.Linear) (hfree : ¬ (hkMn 3).Embeds H)
    (minimal : ∀ (W' : Type u) (H' : Hypergraph W'), #W' < #W →
      H'.IsTripleSystem → H'.Linear → ¬ (hkMn 3).Embeds H' →
      H'.ColorableBy ℵ₀)
    (S : Set W) (hS : #S < #W) :
    ∃ c : W → ℕ, ∀ e ∈ H.edges, e ⊆ S →
      ∃ x ∈ e, ∃ y ∈ e, c x ≠ c y := by
  classical
  have htriS : (Hsub H S).IsTripleSystem := Hsub_isTripleSystem H htri S
  have hlinS : (Hsub H S).Linear := Hsub_linear_of_linear H hlin S
  have hfreeS : ¬ (hkMn 3).Embeds (Hsub H S) :=
    fun h => hfree (hkMn_embeds_of_Hsub H S h)
  obtain ⟨c, hc⟩ := minimal (↑S) (Hsub H S) hS htriS hlinS hfreeS
  have hcnt : Countable (ℵ₀ : Cardinal.{u}).out :=
    Cardinal.mk_le_aleph0_iff.mp (le_of_eq (Cardinal.mk_out _))
  obtain ⟨g, hg⟩ : ∃ g : (ℵ₀ : Cardinal.{u}).out → ℕ, Function.Injective g :=
    ⟨_, (exists_injective_nat _).choose_spec⟩
  set d : W → ℕ := fun v => if h : v ∈ S then g (c ⟨v, h⟩) else 0 with hd
  have hval : ∀ a : ↑S, d (a : W) = g (c a) := by
    intro a
    simp only [hd, dif_pos a.2, Subtype.coe_eta]
  refine ⟨d, fun e he hsub => ?_⟩
  obtain ⟨s, hsimg, hsedge⟩ := Hsub_edge_of_subset H S e he hsub
  obtain ⟨x, hx, y, hy, hxy⟩ := hc s hsedge
  refine ⟨(x : W), by rw [← hsimg]; exact ⟨x, hx, rfl⟩,
    (y : W), by rw [← hsimg]; exact ⟨y, hy, rfl⟩, ?_⟩
  rw [hval x, hval y]
  exact fun h => hxy (hg h)

lemma linear_not_deltaRoot_two (H : Hypergraph W) (hlin : H.Linear)
    (x y : W) (hxy : x ≠ y) : ¬ IsDeltaRoot H 2 ({x, y} : Set W) := by
  rintro ⟨D, hDH, hcard, hroot, hinter⟩
  have hcard' : (2 : Cardinal) ≤ #D := by exact_mod_cast hcard
  rw [Cardinal.two_le_iff] at hcard'
  obtain ⟨e₁, e₂, hne⟩ := hcard'
  have hs := hlin e₁ (hDH e₁.2) e₂ (hDH e₂.2)
    (fun h => hne (Subtype.ext h))
  have hx : x ∈ (e₁.1 ∩ e₂.1) :=
    ⟨hroot e₁ e₁.2 (by simp), hroot e₂ e₂.2 (by simp)⟩
  have hy : y ∈ (e₁.1 ∩ e₂.1) :=
    ⟨hroot e₁ e₁.2 (by simp), hroot e₂ e₂.2 (by simp)⟩
  exact hxy (hs hx hy)

lemma HKpairClosed_biUnion_lt {σ : Type u} [LinearOrder σ]
    (H : Hypergraph W) (M : σ → Set W) (hmono : Monotone M)
    (hclosed : ∀ a, DClosed H 2 (M a)) (a : σ) :
    DClosed H 2 (⋃ b ∈ {b | b < a}, M b) := by
  intro x hx y hy hxy
  simp only [Set.mem_iUnion] at hx hy ⊢
  obtain ⟨i, hia, hxM⟩ := hx
  obtain ⟨j, hja, hyM⟩ := hy
  intro v hv
  refine Set.mem_iUnion₂.mpr ⟨max i j, max_lt hia hja, ?_⟩
  exact hclosed (max i j) x (hmono (le_max_left _ _) hxM)
    y (hmono (le_max_right _ _) hyM) hxy hv

/-- Minimal-cardinality induction plus the finitary pair/blocker closure gives
the filtration interface. -/
theorem exists_hk_filtration (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) (hfree : ¬ (hkMn 3).Embeds H)
    (minimal : ∀ (W' : Type u) (H' : Hypergraph W'), #W' < #W →
      H'.IsTripleSystem → H'.Linear → ¬ (hkMn 3).Embeds H' →
      H'.ColorableBy ℵ₀) :
    Nonempty (HKFiltration.{u, u} H) := by
  classical
  have hbig : ℵ₀ < #W := by
    by_contra hle
    exact huc (tripleSystem_colorable_of_le_aleph0 H htri (not_lt.mp hle))
  let Idx := (#W).ord.ToType
  let e : Idx ≃ W := Classical.choice (Cardinal.eq.1 (by simp [Idx]))
  let M : Idx → Set W := fun a => HKcl H (e '' {b | b ≤ a})
  have hMmono : Monotone M := by
    intro a b hab
    apply HKcl_mono
    exact Set.image_mono (fun x hx => le_trans hx hab)
  have hMclosed : ∀ a, DClosed H 2 (M a) := fun a => HKcl_pairClosed H _
  have hMblock : ∀ a Z, (∀ i j, Z i j ∈ M a) →
      (hkBlocker H Z : Set W) ⊆ M a := by
    intro a Z hZ
    exact HKcl_blockerClosed H _ Z hZ
  have hMsmall : ∀ a, #(M a) < #W := by
    intro a
    have himg : #(e '' {b | b ≤ a}) ≤ Cardinal.mk (Set.Iic a) :=
      Cardinal.mk_image_le.trans (by simp [Set.Iic_def])
    have hiio : Cardinal.mk (Set.Iio a) < #W := by
      convert! Cardinal.mk_Iio_ord_toType a using 1
    have hiic : Cardinal.mk (Set.Iic a) < #W := by
      have heq : Cardinal.mk (Set.Iic a) = Cardinal.mk (Set.Iio a) + 1 := by
        rw [← Cardinal.mk_singleton (a : Idx), ← Cardinal.mk_union_of_disjoint]
        · congr with x; simp [le_iff_lt_or_eq, eq_comm]
        · exact Set.disjoint_singleton_right.mpr (lt_irrefl a)
      rw [heq]
      exact Cardinal.add_lt_of_lt (le_of_lt hbig) hiio
        (lt_of_le_of_lt (Cardinal.nat_lt_aleph0 1 |>.le) hbig)
    refine lt_of_le_of_lt (HKcl_card_le H htri _) ?_
    refine lt_of_le_of_lt (add_le_add himg le_rfl) ?_
    exact Cardinal.add_lt_of_lt (le_of_lt hbig) hiic hbig
  have hcover : ∀ x, x ∈ M (e.symm x) := by
    intro x
    apply subset_HKcl H _
    exact ⟨e.symm x, by simp, by simp⟩
  obtain ⟨rank, hrank⟩ : ∃ rank : W → Idx,
      ∀ x, x ∈ M (rank x) ∧ ∀ b, b < rank x → x ∉ M b := by
    have hwf : WellFounded (fun x y : Idx => x < y) := wellFounded_lt
    have hleast : ∀ x, ∃ a, x ∈ M a ∧ ∀ b, b < a → x ∉ M b := by
      intro x
      have hm := hwf.has_min {a | x ∈ M a} ⟨e.symm x, hcover x⟩
      exact ⟨hm.choose, hm.choose_spec.1,
        fun b hb hbM => hm.choose_spec.2 b hbM hb⟩
    exact ⟨fun x => (hleast x).choose, fun x => (hleast x).choose_spec⟩
  let : LinearOrder Idx := inferInstance
  let : WellFoundedLT Idx := inferInstance
  refine ⟨⟨Idx, inferInstance, inferInstance, rank, ?_, ?_, ?_⟩⟩
  · intro a
    have hsub : {v | rank v = a} ⊆ M a := by
      intro v hv
      rw [← hv]
      exact (hrank v).1
    apply hk_level_colorable H htri hlin hfree minimal
    exact lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset hsub) (hMsmall a)
  · intro x y z hxz hyz hxy ed hed hxe hye hze
    let U := ⋃ b ∈ {b : Idx | b < rank z}, M b
    have hxU : x ∈ U := Set.mem_iUnion₂.mpr ⟨rank x, hxz, (hrank x).1⟩
    have hyU : y ∈ U := Set.mem_iUnion₂.mpr ⟨rank y, hyz, (hrank y).1⟩
    have hzU : z ∉ U := by
      intro hz
      obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.mp hz
      exact (hrank z).2 b hb hzb
    have hclosedU : DClosed H 2 U :=
      HKpairClosed_biUnion_lt H M hMmono hMclosed (rank z)
    have hxz' : x ≠ z := fun h => hxz.ne (h ▸ rfl)
    have hyz' : y ≠ z := fun h => hyz.ne (h ▸ rfl)
    exact claim22_abstract H htri 2 U hclosedU x y z hxU hyU hzU hxy
      hxz' hyz' ed hed hxe hye hze (linear_not_deltaRoot_two H hlin x y hxy)
  · intro a Z hZa hblock
    choose k hk using fun i j => Set.mem_iUnion₂.mp
      (show Z i j ∈ (⋃ b ∈ {b : Idx | b < a}, M b) from
        Set.mem_iUnion₂.mpr ⟨rank (Z i j), hZa i j, (hrank (Z i j)).1⟩)
    let K : Finset Idx := Finset.univ.image (fun p : Fin 3 × Fin 3 => k p.1 p.2)
    have hK : K.Nonempty := ⟨k 0 0, by simp [K]⟩
    let b : Idx := K.max' hK
    have hbmem : b ∈ K := K.max'_mem hK
    obtain ⟨p, -, hbp⟩ := Finset.mem_image.mp hbmem
    have hba : b < a := by simpa [b, ← hbp] using! (hk p.1 p.2).1
    have hkb : ∀ i j, k i j ≤ b := by
      intro i j
      exact Finset.le_max' K (k i j) (by simp [K])
    have hZM : ∀ i j, Z i j ∈ M b := by
      intro i j
      exact hMmono (hkb i j) (hk i j).2
    refine ⟨hkBlocker H Z, hkBlocker_spec H Z hblock, ?_⟩
    intro x hx
    have hxb : x ∈ M b := hMblock b Z hZM hx
    have hrle : rank x ≤ b := by
      by_contra hn
      exact (hrank x).2 b (lt_of_not_ge hn) hxb
    exact lt_of_le_of_lt hrle hba

/-- The link graph on one filtration block. -/
def hkLinkGraph (H : Hypergraph W) (F : HKFiltration H) (a : F.Idx) :
    SimpleGraph W := by
  letI := F.linearOrder
  exact SimpleGraph.fromRel (fun x y =>
    F.rank x = a ∧ F.rank y = a ∧ ∃ z, F.rank z < a ∧
      ({x, y, z} : Set W) ∈ H.edges)

lemma hk_edge_flat_or_link (H : Hypergraph W) (htri : H.IsTripleSystem)
    (F : HKFiltration H) (e : Set W) (he : e ∈ H.edges) :
    (∃ a, ∀ v ∈ e, F.rank v = a) ∨
      ∃ a x y, x ∈ e ∧ y ∈ e ∧ F.rank x = a ∧ F.rank y = a ∧
        (hkLinkGraph H F a).Adj x y := by
  let := F.linearOrder
  by_cases hflat : ∃ a, ∀ v ∈ e, F.rank v = a
  · exact Or.inl hflat
  right
  obtain ⟨p, q, r, hpq, hpr, hqr, hedge⟩ := Set.ncard_eq_three.mp (htri e he)
  have hnomax :
      ¬ (F.rank p > F.rank q ∧ F.rank p > F.rank r) ∧
      ¬ (F.rank q > F.rank p ∧ F.rank q > F.rank r) ∧
      ¬ (F.rank r > F.rank p ∧ F.rank r > F.rank q) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨hpq', hpr'⟩
      exact F.noUniqueTop q r p hpq' hpr' hqr e he
        (by simp [hedge]) (by simp [hedge]) (by simp [hedge])
    · rintro ⟨hqp', hqr'⟩
      exact F.noUniqueTop p r q hqp' hqr' hpr e he
        (by simp [hedge]) (by simp [hedge]) (by simp [hedge])
    · rintro ⟨hrp', hrq'⟩
      exact F.noUniqueTop p q r hrp' hrq' hpq e he
        (by simp [hedge]) (by simp [hedge]) (by simp [hedge])
  have hpairs :
      (F.rank p = F.rank q ∧ F.rank r < F.rank p) ∨
      (F.rank p = F.rank r ∧ F.rank q < F.rank p) ∨
      (F.rank q = F.rank r ∧ F.rank p < F.rank q) := by
    have hnall : ¬ (F.rank p = F.rank q ∧ F.rank q = F.rank r) := by
      intro hall
      apply hflat
      refine ⟨F.rank p, ?_⟩
      intro v hv
      rw [hedge] at hv
      rcases hv with (rfl | rfl | rfl)
      · rfl
      · exact hall.1.symm
      · exact (hall.1.trans hall.2).symm
    grind
  rcases hpairs with hp | hp | hp
  · refine ⟨F.rank p, p, q, by simp [hedge], by simp [hedge], rfl, hp.1.symm, ?_⟩
    rw [hkLinkGraph, SimpleGraph.fromRel_adj]
    exact ⟨hpq, Or.inl ⟨rfl, hp.1.symm, r, hp.2,
      by simpa [hedge] using! he⟩⟩
  · refine ⟨F.rank p, p, r, by simp [hedge], by simp [hedge], rfl, hp.1.symm, ?_⟩
    rw [hkLinkGraph, SimpleGraph.fromRel_adj]
    exact ⟨hpr, Or.inl ⟨rfl, hp.1.symm, q, hp.2,
      by simpa [hedge, Set.pair_comm] using! he⟩⟩
  · refine ⟨F.rank q, q, r, by simp [hedge], by simp [hedge], rfl, hp.1.symm, ?_⟩
    rw [hkLinkGraph, SimpleGraph.fromRel_adj]
    exact ⟨hqr, Or.inl ⟨rfl, hp.1.symm, p, hp.2,
      by
        convert! he using 1
        ext v
        simp [hedge, or_comm, or_left_comm, or_assoc]⟩⟩

lemma exists_uncountable_hkLinkGraph (H : Hypergraph W)
    (htri : H.IsTripleSystem) (huc : H.UncountablyChromatic)
    (F : HKFiltration H) :
    ∃ a : F.Idx, ¬ (SimpleGraph.toHG (hkLinkGraph H F a)).ColorableBy ℵ₀ := by
  let := F.linearOrder
  by_contra hall
  push_neg at hall
  choose dlevel hdlevel using F.levelColorable
  have hflat :
      (⟨{e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a}⟩ : Hypergraph W).ColorableBy ℵ₀ := by
    apply colorable_combine F.rank _ dlevel
    rintro e ⟨he, a, ha⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hdlevel a e he (fun v hv => ha v hv)
    exact ⟨a, x, hx, y, hy, ha x hx, ha y hy, hxy⟩
  have hlinkcols : ∀ a : F.Idx, ∃ c : W → ℕ,
      ∀ x y, (hkLinkGraph H F a).Adj x y → c x ≠ c y :=
    fun a => (gCountColorable_iff_colorableBy _).2 (hall a)
  choose dlink hdlink using hlinkcols
  have hnonflat :
      (⟨H.edges \ {e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a}⟩ :
        Hypergraph W).ColorableBy ℵ₀ := by
    apply colorable_combine F.rank _ dlink
    rintro e ⟨he, hn⟩
    rcases hk_edge_flat_or_link H htri F e he with hf | ⟨a,x,y,hx,hy,hrx,hry,hadj⟩
    · exact False.elim (hn ⟨he, hf⟩)
    · exact ⟨a, x, hx, y, hy, hrx, hry, hdlink a x y hadj⟩
  have hu := colorableBy_aleph0_union
    {e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a}
    (H.edges \ {e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a})
    hflat hnonflat
  have hcov : {e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a} ∪
      (H.edges \ {e | e ∈ H.edges ∧ ∃ a, ∀ v ∈ e, F.rank v = a}) = H.edges := by
    rw [Set.union_diff_cancel]
    intro e he
    exact he.1
  rw [hcov] at hu
  exact huc hu

lemma hk_link_private_unique_row (H : Hypergraph W) (htri : H.IsTripleSystem)
    (hlin : H.Linear) {a b₁ b₂ z : W} (hab₁ : a ≠ b₁) (hab₂ : a ≠ b₂)
    (hb : b₁ ≠ b₂)
    (he₁ : ({a,b₁,z} : Set W) ∈ H.edges)
    (he₂ : ({a,b₂,z} : Set W) ∈ H.edges) : False := by
  have haz : a ≠ z := by
    intro h
    have hc := htri _ he₁
    subst z
    have : ({a, b₁, a} : Set W) = {a, b₁} := by ext; simp [or_comm]
    rw [this] at hc
    rw [Set.ncard_pair hab₁] at hc
    omega
  have hne : ({a,b₁,z} : Set W) ≠ ({a,b₂,z} : Set W) := by
    intro heq
    have hbmem : b₁ ∈ ({a,b₂,z} : Set W) := by
      rw [← heq]
      simp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbmem
    rcases hbmem with h | h | h
    · exact hab₁ h.symm
    · exact hb h
    · have hc := htri _ he₁
      rw [h] at hc
      have : ({a, z, z} : Set W) = {a, z} := by ext; simp [or_comm]
      rw [this] at hc
      rw [Set.ncard_pair haz] at hc
      omega
  have hs := hlin _ he₁ _ he₂ hne
  exact haz (hs (by simp) (by simp))

lemma hk_link_value_row_bound [DecidableEq W] (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    {q : ℕ} (A B : Fin q → W) (P : Fin q → Fin q → W)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hAB : ∀ i j, A i ≠ B j)
    (hedge : ∀ i j, ({A i, B j, P i j} : Set W) ∈ H.edges) :
    (∀ i v, (Finset.univ.filter (fun j => P i j = v)).card < 2) ∧
    (∀ j v, (Finset.univ.filter (fun i => P i j = v)).card < 2) := by
  classical
  constructor
  · intro i v
    by_contra hn
    have htwo : 2 ≤ (Finset.univ.filter (fun j => P i j = v)).card := by omega
    have hone : 1 < (Finset.univ.filter (fun j => P i j = v)).card := by omega
    rw [Finset.one_lt_card] at hone
    obtain ⟨j₁, hj₁, j₂, hj₂, hjne⟩ := hone
    have hp₁ := (Finset.mem_filter.mp hj₁).2
    have hp₂ := (Finset.mem_filter.mp hj₂).2
    exact hk_link_private_unique_row H htri hlin (hAB i j₁) (hAB i j₂)
      (fun h => hjne (hBinj h)) (by simpa [hp₁] using! hedge i j₁)
      (by simpa [hp₂] using! hedge i j₂)
  · intro j v
    by_contra hn
    have hone : 1 < (Finset.univ.filter (fun i => P i j = v)).card := by omega
    rw [Finset.one_lt_card] at hone
    obtain ⟨i₁, hi₁, i₂, hi₂, hine⟩ := hone
    have hp₁ := (Finset.mem_filter.mp hi₁).2
    have hp₂ := (Finset.mem_filter.mp hi₂).2
    exact hk_link_private_unique_row H htri hlin (hAB i₁ j).symm (hAB i₂ j).symm
      (fun h => hine (hAinj h)) (by simpa [hp₁, Set.insert_comm] using! hedge i₁ j)
      (by simpa [hp₂, Set.insert_comm] using! hedge i₂ j)

lemma hk_rainbow_realization_from_link (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    (F : HKFiltration H) (a : F.Idx)
    (huc : ¬ (SimpleGraph.toHG (hkLinkGraph H F a)).ColorableBy ℵ₀) :
    ∃ Z X Y,
      (∀ i j i' j', Z i j = Z i' j' → i = i' ∧ j = j') ∧
      HKRealizes H Z X Y ∧
      (∀ i, F.rank (X i) = a) ∧ (∀ i, F.rank (Y i) = a) ∧
      ∀ i j, F.linearOrder.lt (F.rank (Z i j)) a := by
  let := F.linearOrder
  classical
  let q := 228
  obtain ⟨A, B, hAinj, hBinj, hAB, hadj⟩ :=
    eh_hasKmm (hkLinkGraph H F a) huc q
  have hP : ∀ i j : Fin q, ∃ z, F.rank z < a ∧
      ({A i, B j, z} : Set W) ∈ H.edges := by
    intro i j
    have hh := hadj i j
    rw [hkLinkGraph, SimpleGraph.fromRel_adj] at hh
    rcases hh with ⟨_, hrel | hrel⟩
    · exact ⟨hrel.2.2.choose, hrel.2.2.choose_spec.1,
        hrel.2.2.choose_spec.2⟩
    · have hz := hrel.2.2.choose_spec
      exact ⟨hrel.2.2.choose, hz.1, by simpa [Set.insert_comm] using hz.2⟩
  choose P hPrank hPedge using hP
  have hb := hk_link_value_row_bound H htri hlin A B P hAinj hBinj hAB hPedge
  obtain ⟨I, J, hI, hJ, hrainbow⟩ :=
    greedy_rainbow 3 2 q (by omega) (by norm_num [q]) P hb.1 hb.2
  refine ⟨fun i j => P (I i) (J j), fun i => A (I i), fun j => B (J j),
    hrainbow, ?_, fun i => ?_, fun j => ?_, fun i j => hPrank (I i) (J j)⟩
  · refine ⟨hAinj.comp hI, hBinj.comp hJ, ?_, ?_, ?_, ?_⟩
    · exact fun i j => hAB (I i) (J j)
    · intro i k l h
      have hri := show F.rank (A (I i)) = a from by
        have hh := hadj (I i) (J k)
        rw [hkLinkGraph, SimpleGraph.fromRel_adj] at hh
        rcases hh with ⟨_, hh | hh⟩ <;> simp_all
      have hrz := hPrank (I k) (J l)
      have hrEq := congrArg F.rank h
      apply (lt_irrefl a)
      calc
        a = F.rank (A (I i)) := hri.symm
        _ = F.rank (P (I k) (J l)) := hrEq
        _ < a := hrz
    · intro i k l h
      have hri := show F.rank (B (J i)) = a from by
        have hh := hadj (I k) (J i)
        rw [hkLinkGraph, SimpleGraph.fromRel_adj] at hh
        rcases hh with ⟨_, hh | hh⟩ <;> simp_all
      have hrz := hPrank (I k) (J l)
      have hrEq := congrArg F.rank h
      apply (lt_irrefl a)
      calc
        a = F.rank (B (J i)) := hri.symm
        _ = F.rank (P (I k) (J l)) := hrEq
        _ < a := hrz
    · exact fun j k => hPedge (I j) (J k)
  · have hh := hadj (I i) (J 0)
    rw [hkLinkGraph, SimpleGraph.fromRel_adj] at hh
    rcases hh with ⟨_, hh | hh⟩ <;> simp_all
  · have hh := hadj (I 0) (J j)
    rw [hkLinkGraph, SimpleGraph.fromRel_adj] at hh
    rcases hh with ⟨_, hh | hh⟩ <;> simp_all

/-- The combinatorial second half of HK Theorem 1: a closed filtration yields
an injective lower `3 × 3` grid having realizations outside every small finite
set.  The complete bipartite graph is extracted from the uncountably chromatic
link graph, not from a private-vertex hypergraph grid. -/
theorem hk_unblocked_grid_of_filtration (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) (F : HKFiltration H) :
    ∃ Z : Fin 3 → Fin 3 → W,
      (∀ i j i' j', Z i j = Z i' j' → i = i' ∧ j = j') ∧
      ∀ S : Finset W, S.card ≤ 18 →
        ∃ X Y : Fin 3 → W, HKRealizes H Z X Y ∧
          (∀ i, X i ∉ S) ∧ (∀ i, Y i ∉ S) := by
  let := F.linearOrder
  obtain ⟨a, ha⟩ := exists_uncountable_hkLinkGraph H htri huc F
  obtain ⟨Z, X0, Y0, hZ, hreal0, hrX, hrY, hrZ⟩ :=
    hk_rainbow_realization_from_link H htri hlin F a ha
  refine ⟨Z, hZ, ?_⟩
  intro S hScard
  by_contra hno
  push_neg at hno
  have hblocks : HKBlocks H Z S := by
    refine ⟨hScard, ?_⟩
    intro X Y hreal
    by_cases hx : ∃ i, X i ∈ S
    · exact Or.inl hx
    · right
      exact hno X Y hreal (by simpa only [not_exists] using! hx)
  obtain ⟨T, hTblock, hrT⟩ := F.reflectBlocker a Z hrZ ⟨S, hblocks⟩
  have hhit := hTblock.2 X0 Y0 hreal0
  rcases hhit with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact (lt_irrefl a) (by
      calc a = F.rank (X0 i) := (hrX i).symm
           _ < a := hrT _ hi)
  · exact (lt_irrefl a) (by
      calc a = F.rank (Y0 i) := (hrY i).symm
           _ < a := hrT _ hi)

/-- The inductive contradiction at a minimal `M₃`-free host. -/
theorem hk_theorem1_three_step {W : Type u} (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) (hfree : ¬ (hkMn 3).Embeds H)
    (minimal : ∀ (W' : Type u) (H' : Hypergraph W'), #W' < #W →
      H'.IsTripleSystem → H'.Linear → ¬ (hkMn 3).Embeds H' →
      H'.ColorableBy ℵ₀) : False := by
  obtain ⟨F : HKFiltration.{u, u} H⟩ :=
    exists_hk_filtration (W := W) H htri hlin huc hfree minimal
  obtain ⟨Z, hZ, havoid⟩ := hk_unblocked_grid_of_filtration H htri hlin huc F
  exact hfree (hkMn3_embeds_of_avoidance H Z hZ havoid)

/-- The `n = 3` instance of Hajnal–Komjáth Theorem 1: every linear triple
system of uncountable chromatic number contains `M₃`. -/
theorem hk_theorem1_three {W : Type u} (H : Hypergraph W)
    (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) :
    (hkMn 3).Embeds H := by
  have key : ∀ κ : Cardinal.{u}, ∀ (W : Type u) (H : Hypergraph W),
      #W = κ → H.IsTripleSystem → H.Linear → H.UncountablyChromatic →
      (hkMn 3).Embeds H := by
    refine fun κ => Cardinal.lt_wf.induction
      (C := fun κ => ∀ (W : Type u) (H : Hypergraph W),
        #W = κ → H.IsTripleSystem → H.Linear → H.UncountablyChromatic →
        (hkMn 3).Embeds H) κ ?_
    intro κ IH W H hcard htri hlin huc
    by_contra hfree
    exact hk_theorem1_three_step H htri hlin huc hfree (fun W' H' hlt htri' hlin' hfree' => by
      by_contra hcol
      exact hfree' (IH (#W') (hcard ▸ hlt) W' H' rfl htri' hlin' hcol))
  exact key (#W) W H rfl htri hlin huc

/-- Hajnal–Komjáth's loose-seven-cycle corollary (E5), with no external
hypothesis. -/
theorem e5_HK_loose7 : E5_HK_loose7.{u} := by
  intro W H htri hlin huc
  obtain ⟨g, hg, hge⟩ := looseCycle7_sub_hkMn3
  obtain ⟨f, hf, hfe⟩ := hk_theorem1_three H htri hlin huc
  refine ⟨f ∘ g, hf.comp hg, ?_⟩
  intro e he
  rw [show (f ∘ g) '' (↑e : Set looseCycle7.V) =
    f '' (↑(e.image g) : Set (hkMn 3).V) by
      rw [Finset.coe_image, Set.image_comp]]
  exact hfe _ (hge e he)

end Erdos1177
