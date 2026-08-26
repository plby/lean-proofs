/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0.
-/
/-
Erdős Problem 927.
Informal proof: Joel H. Spencer, "On cliques in graphs" (1971).
Formal authors: John Jennings and Aristotle (Harmonic).
Jake Mallen replaced native evaluation with kernel-checked proofs in the selected copy.
Source: https://www.erdosproblems.com/927#post-6850
https://gist.githubusercontent.com/JohnEdwardJennings/24c9debc9854cb118fbc1314c70941c3/raw/b4fc5ef91876a89018b10508c479c000258504fb/Erdos927.lean
https://github.com/Jayyhk/erdos-lean/tree/cc6c94bd3f9de7c4cf7703ed40d8fd06380780a3/problems/927
Original and selected toolchain: Lean 4.28.0.
Selected Mathlib commit: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import ErdosProblems.Erdos927.Big

set_option linter.mathlibStandardSet false

namespace Erdos927

/-
# Small Clique Construction

For each d with 5 ≤ d ≤ n, we construct a maximal clique of size d
in Spencer's graph using z, w-vertices, and C*-vertices.
-/

/-! ## Level validity -/

/-- A level ℓ is "valid" for graph parameter n. -/
structure LevelValid (n ℓ : ℕ) : Prop where
  recSeq_ge : recSeq n (ℓ + 1) ≥ 2
  wfit : n / 2 + wOff n (ℓ + 1) ≤ n
  vfit : vOff n (ℓ + 1) ≤ spA n
  fuel : ℓ < n

/-! ## Clique at a level (filtering approach) -/

/-- Whether a w-vertex y_i belongs to level ℓ with position in S. -/
def wInLevel (n ℓ : ℕ) (S : Finset ℕ) (i : Fin n) : Bool :=
  decide (n / 2 ≤ (i : ℕ)) &&
  match wLookup n ((i : ℕ) - n / 2) 0 n with
  | some (wl, wp) => wl == ℓ && decide (wp ∈ S)
  | none => false

/-- Whether a C*-vertex cStar_j belongs to level ℓ with position NOT in S. -/
def vNotInLevel (n ℓ : ℕ) (S : Finset ℕ) (j : Fin (spA n)) : Bool :=
  let (vl, vp, _) := vLookup n (j : ℕ) 0 n
  vl == ℓ && !decide (vp ∈ S)

/-- The small clique at level ℓ with w-position set S.
  Includes z, w-vertices at positions in S, C*-vertices at positions NOT in S. -/
noncomputable def smallCl (n ℓ : ℕ) (S : Finset ℕ) :
    Finset (SpVtx n (spA n)) := by
  classical
  exact {.z} ∪
  (Finset.univ.filter fun i : Fin n => wInLevel n ℓ S i).image .y ∪
  (Finset.univ.filter fun j : Fin (spA n) => vNotInLevel n ℓ S j).image .cStar

/-! ## Membership helpers -/

/-- z is in the small clique. -/
lemma z_mem_smallCl (n ℓ : ℕ) (S : Finset ℕ) :
    SpVtx.z ∈ smallCl n ℓ S := by
  classical
  simp [smallCl]

/-
The w-vertex at position p is in smallCl when p ∈ S and the level is valid.
-/
lemma wVertex_mem_smallCl (n ℓ : ℕ) (S : Finset ℕ) (p : ℕ)
    (hv : LevelValid n ℓ) (hp : p < recSeq n (ℓ + 1)) (hpS : p ∈ S) :
    SpVtx.y ⟨n / 2 + wOff n ℓ + p, by
      have := hv.wfit; have : wOff n (ℓ + 1) = wOff n ℓ + recSeq n (ℓ + 1) := rfl; omega⟩
    ∈ smallCl n ℓ S := by
  classical
  unfold smallCl; simp +decide [ *, wInLevel ] ;
  rw [ show n / 2 + wOff n ℓ + p - n / 2 = wOff n ℓ + p by rw [ Nat.sub_eq_of_eq_add ] ; ring ];
  rw [ wLookup_at_level ] <;> norm_num [ hp, hpS ];
  · exact le_add_of_le_of_nonneg ( Nat.le_add_right _ _ ) ( Nat.zero_le _ );
  · exact hv.fuel;
  · have := hv.wfit; norm_num [ Nat.add_assoc ] at *; omega;

/-
The C*-vertex at position q, sub-index s, is in smallCl when q ∉ S.
-/
lemma cStarVertex_mem_smallCl (n ℓ : ℕ) (S : Finset ℕ) (q s : ℕ)
    (hv : LevelValid n ℓ) (hq : q < recSeq n (ℓ + 1)) (hs : s < 2 ^ q + 1)
    (hqS : q ∉ S) :
    SpVtx.cStar ⟨vOff n ℓ + cPosOff q + s, by
      have := hv.vfit
      have h1 : cPosOff q + s < cPosOff (q + 1) := by simp [cPosOff]; omega
      have h2 : cPosOff (q + 1) ≤ cPosOff (recSeq n (ℓ + 1)) := cPosOff_mono (by omega)
      rw [cPosOff_eq_levelVSize] at h2
      have : vOff n ℓ + levelVSize n ℓ = vOff n (ℓ + 1) := rfl; omega⟩
    ∈ smallCl n ℓ S := by
  classical
  unfold smallCl; simp +decide [ *, vNotInLevel ] ;
  have := vLookup_at_level n ℓ q s hq hs hv.fuel hv.vfit; aesop;

/-! ## Clique property -/

/-- The small clique is a clique in Spencer's graph. -/
lemma smallCl_isClique (n ℓ : ℕ) (S : Finset ℕ) :
    (spGraph n).IsClique (↑(smallCl n ℓ S) : Set _) := by
  classical
  intro u hu v hv huv;
  unfold smallCl at hu hv;
  unfold wInLevel vNotInLevel at *;
  unfold spGraph at *;
  unfold spAdj; simp +decide [ huv ] ;
  rcases u with ( _ | _ | _ | _ | _ ) <;> rcases v with ( _ | _ | _ | _ | _ ) <;> simp +decide at hu hv huv ⊢;
  · unfold wvAdj;
    cases h : wLookup n ( ↑‹Fin n› - n / 2 ) 0 n <;> simp_all +decide;
    grind;
  · exact isGeneric_false_of_ge n _ hu.1;
  · unfold wvAdj; simp +decide [ ] ;
    cases h : wLookup n ( ↑‹Fin n› - n / 2 ) 0 n <;> simp_all +decide;
    grind;
  · exact isGeneric_false_of_ge n _ hv.1

/-! ## Maximality helpers -/

/-
If y_i is non-generic and not in smallCl, then wLookup gives a result
  that allows finding a blocking cStar in smallCl.
-/
lemma y_blocked_by_cStar (n ℓ : ℕ) (S : Finset ℕ) (i : Fin n)
    (hv : LevelValid n ℓ)
    (hge : n / 2 ≤ (i : ℕ))
    (hnotW : wInLevel n ℓ S i = false)
    (hS_prop : ∃ q, q < recSeq n (ℓ + 1) ∧ q ∉ S) :
    ∃ j : Fin (spA n), SpVtx.cStar j ∈ smallCl n ℓ S ∧
      wvAdj n i j = false := by
  classical
  by_cases h : wLookup n ( i - n / 2 ) 0 n = none <;> simp_all +decide [ wInLevel ];
  · obtain ⟨ q, hq₁, hq₂ ⟩ := hS_prop;
    refine' ⟨ ⟨ vOff n ℓ + cPosOff q + 0, _ ⟩, _, _ ⟩;
    any_goals exact cStarVertex_mem_smallCl n ℓ S q 0 hv hq₁ ( by norm_num ) hq₂;
    exact wvAdj_none n i _ h;
  · rcases h' : wLookup n ( i - n / 2 ) 0 n with ( _ | ⟨ wl, wp ⟩ ) <;> simp_all +decide [ ];
    by_cases hwl : wl = ℓ <;> simp_all +decide [ ];
    · -- Since wp < recSeq n (ℓ + 1), we can use cStarVertex_mem_smallCl with (wp, 0).
      have hwp_lt : wp < recSeq n (ℓ + 1) := by
        have hwp_lt_recSeq : ∀ {offset level fuel : ℕ}, wLookup n offset level fuel = some (ℓ, wp) → wp < recSeq n (ℓ + 1) := by
          intros offset level fuel h; induction' fuel with fuel ih generalizing offset level <;> simp_all +decide [ wLookup ] ;
          · linarith [ hv.recSeq_ge ];
          · grind;
        exact hwp_lt_recSeq h';
      refine' ⟨ ⟨ vOff n ℓ + cPosOff wp + 0, _ ⟩, _, _ ⟩;
      any_goals exact cStarVertex_mem_smallCl n ℓ S wp 0 hv hwp_lt ( by norm_num ) hnotW;
      apply wvAdj_false_of_eq;
      exact h';
      convert vLookup_at_level n ℓ wp 0 _ _ _ _ using 1;
      · assumption;
      · positivity;
      · exact hv.fuel;
      · exact hv.vfit;
    · obtain ⟨ q, hq₁, hq₂ ⟩ := hS_prop;
      refine' ⟨ ⟨ vOff n ℓ + cPosOff q + 0, _ ⟩, _, _ ⟩;
      any_goals exact cStarVertex_mem_smallCl n ℓ S q 0 hv hq₁ ( by norm_num ) hq₂;
      apply wvAdj_diff_level;
      exact h';
      exact vLookup_at_level n ℓ q 0 hq₁ ( by norm_num ) hv.fuel hv.vfit;
      assumption

/-
If cStar_j is not in smallCl, then there exists a w-vertex in smallCl
  that is not adjacent to cStar_j.
-/
lemma cStar_blocked_by_y (n ℓ : ℕ) (S : Finset ℕ) (j : Fin (spA n))
    (hv : LevelValid n ℓ)
    (hnotV : vNotInLevel n ℓ S j = false)
    (hS_ne : S.Nonempty)
    (hS_sub : ∀ p ∈ S, p < recSeq n (ℓ + 1)) :
    ∃ i : Fin n, SpVtx.y i ∈ smallCl n ℓ S ∧
      isGeneric n i = false ∧ wvAdj n i j = false := by
  classical
  by_cases h_case2 : (vLookup n j 0 n).1 = ℓ ∧ (vLookup n j 0 n).2.1 ∈ S;
  · refine' ⟨ ⟨ n / 2 + wOff n ℓ + ( vLookup n j 0 n ).2.1, _ ⟩, _, _, _ ⟩;
    any_goals linarith [ hv.wfit, hS_sub _ h_case2.2, show wOff n ( ℓ + 1 ) = wOff n ℓ + recSeq n ( ℓ + 1 ) from rfl ];
    · convert wVertex_mem_smallCl n ℓ S ( vLookup n j 0 n |>.2.1 ) hv ( hS_sub _ h_case2.2 ) h_case2.2 using 1;
    · exact isGeneric_false_of_ge _ _ ( by simp +arith +decide );
    · apply wvAdj_false_of_eq;
      convert wLookup_at_level n ℓ ( vLookup n j 0 n |>.2.1 ) _ _ _ using 1;
      any_goals exact ( vLookup n j 0 n ).2.2;
      · grind;
      · exact hS_sub _ h_case2.2;
      · exact hv.fuel;
      · exact hv.wfit.trans' ( Nat.le_add_left _ _ );
      · grind;
  · obtain ⟨p, hp⟩ : ∃ p ∈ S, p < recSeq n (ℓ + 1) := by
      exact ⟨ _, hS_ne.choose_spec, hS_sub _ hS_ne.choose_spec ⟩;
    refine' ⟨ ⟨ n / 2 + wOff n ℓ + p, _ ⟩, _, _, _ ⟩;
    any_goals exact wVertex_mem_smallCl n ℓ S p hv hp.2 hp.1;
    · unfold isGeneric; simp +decide [ ] ;
      exact le_add_of_le_of_nonneg ( Nat.le_add_right _ _ ) ( Nat.zero_le _ );
    · apply wvAdj_diff_level;
      convert wLookup_at_level n ℓ p hp.2 hv.fuel _ using 1;
      grind;
      exact hv.wfit.trans' ( Nat.le_add_left _ _ );
      exact Prod.ext rfl rfl;
      unfold vNotInLevel at hnotV; aesop;

/-! ## Maximality -/

/-
The small clique is maximal.
-/
lemma smallCl_isMaximal (n ℓ : ℕ) (S : Finset ℕ)
    (hv : LevelValid n ℓ)
    (hS_ne : S.Nonempty)
    (hS_sub : ∀ p ∈ S, p < recSeq n (ℓ + 1))
    (hS_prop : ∃ q, q < recSeq n (ℓ + 1) ∧ q ∉ S) :
    ∀ t : Finset (SpVtx n (spA n)),
      (spGraph n).IsClique (↑t : Set _) → smallCl n ℓ S ⊆ t →
      t = smallCl n ℓ S := by
  classical
  intros t ht ht_sub
  apply Finset.Subset.antisymm;
  · intro v hv;
    rcases v with ( _ | _ | _ | _ | _ ) <;> simp_all +decide [ SimpleGraph.IsClique ];
    · rename_i i;
      by_cases hi : n / 2 ≤ (i : ℕ);
      · by_cases hi' : wInLevel n ℓ S i = true;
        · grind +locals;
        · obtain ⟨ j, hj₁, hj₂ ⟩ := y_blocked_by_cStar n ℓ S i ‹_› hi ( by simpa using hi' ) hS_prop;
          have := ht ( ht_sub hj₁ ) hv; simp_all +decide [ spGraph ] ;
          unfold spAdj at this; simp_all +decide [ isGeneric ] ;
          grind;
      · have := ht ( show SpVtx.z ∈ t from ht_sub ( z_mem_smallCl n ℓ S ) ) hv; simp_all +decide [ spGraph ] ;
        unfold spAdj at this; simp_all +decide [ isGeneric ] ;
    · have := ht ( z_mem_smallCl n ℓ S |> fun h => ht_sub h ) hv; simp_all +decide [ spGraph ] ;
      cases this ; contradiction;
    · have := ht ( show SpVtx.z ∈ t from ht_sub ( z_mem_smallCl n ℓ S ) ) hv; simp_all +decide [ spGraph, spAdj ] ;
    · by_cases h : vNotInLevel n ℓ S ‹_› <;> simp_all +decide [ smallCl ];
      obtain ⟨ i, hi, hi' ⟩ := cStar_blocked_by_y n ℓ S _ ‹_› h hS_ne hS_sub;
      have := ht ( show SpVtx.y i ∈ t from ?_ ) hv ?_ <;> simp_all +decide [ spGraph ];
      · unfold spAdj at this; aesop;
      · unfold smallCl at hi; aesop;
    · exact z_mem_smallCl n ℓ S;
  · assumption

/-! ## IsMaximalClique combined -/

/-- Combined: the small clique is a maximal clique. -/
lemma smallCl_isMaximalClique (n ℓ : ℕ) (S : Finset ℕ)
    (hv : LevelValid n ℓ) (hS_ne : S.Nonempty)
    (hS_sub : ∀ p ∈ S, p < recSeq n (ℓ + 1))
    (hS_prop : ∃ q, q < recSeq n (ℓ + 1) ∧ q ∉ S) :
    IsMaximalClique (spGraph n) (smallCl n ℓ S) :=
  ⟨smallCl_isClique n ℓ S, smallCl_isMaximal n ℓ S hv hS_ne hS_sub hS_prop⟩

/-! ## Card calculation -/

/-
Card of the w-filter.
-/
lemma wFilter_card (n ℓ : ℕ) (S : Finset ℕ) (hv : LevelValid n ℓ)
    (hS_sub : ∀ p ∈ S, p < recSeq n (ℓ + 1)) :
    (Finset.univ.filter fun i : Fin n => wInLevel n ℓ S i).card = S.card := by
  classical
  fapply Finset.card_bij;
  use fun a ha => (wLookup n ((a : ℕ) - n / 2) 0 n).get!.2;
  · unfold wInLevel at *; aesop;
  · simp +decide [ wInLevel ];
    intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h;
    rcases h₁ : wLookup n ( a₁ - n / 2 ) 0 n with ( _ | ⟨ wl₁, wp₁ ⟩ ) <;> rcases h₂ : wLookup n ( a₂ - n / 2 ) 0 n with ( _ | ⟨ wl₂, wp₂ ⟩ ) <;> simp_all +decide ;
    have := wLookup_offset_eq n ( a₁ - n / 2 ) 0 n ℓ wp₂ h₁; have := wLookup_offset_eq n ( a₂ - n / 2 ) 0 n ℓ wp₂ h₂; simp_all +decide [ Fin.ext_iff ] ;
    omega;
  · intro b hb;
    refine' ⟨ ⟨ n / 2 + wOff n ℓ + b, _ ⟩, _, _ ⟩ <;> norm_num [ wInLevel ];
    · have := hv.wfit; have := hS_sub b hb; have := wOff_succ n ℓ; norm_num at *; omega;
    · rw [ show n / 2 + wOff n ℓ + b - n / 2 = wOff n ℓ + b by rw [ Nat.sub_eq_of_eq_add ] ; ring ];
      rw [ wLookup_at_level ];
      · grind;
      · exact hS_sub b hb;
      · exact hv.fuel;
      · exact hv.wfit.trans' ( Nat.le_add_left _ _ );
    · rw [ show n / 2 + wOff n ℓ + b - n / 2 = wOff n ℓ + b by rw [ Nat.sub_eq_of_eq_add ] ; ring ];
      rw [ wLookup_at_level ] <;> norm_num [ hS_sub b hb, hv.fuel ];
      have := hv.wfit; norm_num [ wOff ] at *; omega;

/-
Card of the v-filter.
-/
lemma vFilter_card (n ℓ : ℕ) (S : Finset ℕ) (hv : LevelValid n ℓ) :
    (Finset.univ.filter fun j : Fin (spA n) => vNotInLevel n ℓ S j).card =
    (Finset.range (recSeq n (ℓ + 1)) \ S).sum (fun q => 2 ^ q + 1) := by
  classical
  -- To prove the equality of the cardinalities, we can use the fact that the function mapping j to (q, s)
  -- is a bijection between the filter and the sigma type.
  have h_bij : Finset.image (fun j : Fin (spA n) => ((vLookup n j 0 n).2.1, (vLookup n j 0 n).2.2))
        (Finset.univ.filter (fun j : Fin (spA n) => vNotInLevel n ℓ S j = true)) =
      Finset.biUnion (Finset.range (recSeq n (ℓ + 1)) \ S)
        (fun q => Finset.image (fun s => (q, s)) (Finset.range (2 ^ q + 1))) := by
    ext ⟨q, s⟩;
    constructor;
    · simp [vNotInLevel];
      intro x hx₁ hx₂ hx₃; have := vLookup_pos_bound n x 0 n ℓ q s; simp_all +decide ;
      exact this ( Prod.ext hx₁ hx₃ ) hv.fuel;
    · simp +zetaDelta at *;
      intro hq hqS hs
      use ⟨vOff n ℓ + cPosOff q + s, by
        have h_bound : cPosOff q + s < cPosOff (recSeq n (ℓ + 1)) := by
          refine' lt_of_lt_of_le _ ( cPosOff_mono hq );
          simp +arith +decide [ cPosOff ];
          grind;
        linarith [ hv.vfit, show vOff n ( ℓ + 1 ) = vOff n ℓ + levelVSize n ℓ from rfl, cPosOff_eq_levelVSize n ℓ ]⟩
      generalize_proofs at *;
      have h_vLookup : vLookup n (vOff n ℓ + cPosOff q + s) 0 n = (ℓ, q, s) := by
        apply vLookup_at_level;
        · assumption;
        · linarith;
        · exact hv.fuel;
        · exact hv.vfit;
      unfold vNotInLevel; aesop;
  have h_card_eq : Finset.card (Finset.image (fun j : Fin (spA n) => ((vLookup n j 0 n).2.1, (vLookup n j 0 n).2.2))
        (Finset.univ.filter (fun j : Fin (spA n) => vNotInLevel n ℓ S j = true))) =
      Finset.card (Finset.univ.filter (fun j : Fin (spA n) => vNotInLevel n ℓ S j = true)) := by
    apply Finset.card_image_of_injOn;
    intro j hj j' hj' h_eq;
    have h_eq_vLookup : (vLookup n j 0 n).1 = (vLookup n j' 0 n).1 := by
      unfold vNotInLevel at hj hj'; aesop;
    have h_eq_vLookup : j.val = vOff n (vLookup n j 0 n).1 + cPosOff (vLookup n j 0 n).2.1 + (vLookup n j 0 n).2.2 := by
      have := vLookup_offset_eq n j.val 0 n (vLookup n j.val 0 n).1 (vLookup n j.val 0 n).2.1 (vLookup n j.val 0 n).2.2 rfl (by
      exact Nat.zero_le _);
      simpa only [show vOff n 0 = 0 from rfl, Nat.sub_zero] using this
    have h_eq_vLookup' : j'.val = vOff n (vLookup n j' 0 n).1 + cPosOff (vLookup n j' 0 n).2.1 + (vLookup n j' 0 n).2.2 := by
      simpa only [show vOff n 0 = 0 from rfl, Nat.sub_zero] using
        vLookup_offset_eq n j'.val 0 n (vLookup n j'.val 0 n).1
          (vLookup n j'.val 0 n).2.1 (vLookup n j'.val 0 n).2.2 rfl (Nat.zero_le _)

    grind;
  rw [ ← h_card_eq, h_bij, Finset.card_biUnion ];
  · exact Finset.sum_congr rfl fun x hx => by rw [ Finset.card_image_of_injective ] <;> aesop_cat;
  · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z => by aesop;

/-
The card of the small clique.
-/
lemma smallCl_card (n ℓ : ℕ) (S : Finset ℕ)
    (hv : LevelValid n ℓ)
    (hS_sub : ∀ p ∈ S, p < recSeq n (ℓ + 1)) :
    (smallCl n ℓ S).card =
    1 + recSeq n (ℓ + 1) + (Finset.range (recSeq n (ℓ + 1)) \ S).sum (2 ^ ·) := by
  classical
  rw [ smallCl ];
  rw [ Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ];
  · rw [ Finset.card_image_of_injective, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
    rw [ wFilter_card n ℓ S hv hS_sub, vFilter_card n ℓ S hv ];
    simp +arith +decide [ Finset.sum_add_distrib, Finset.card_sdiff, * ];
    rw [ Finset.inter_eq_left.mpr fun x hx => Finset.mem_range.mpr ( hS_sub x hx ),
      add_tsub_cancel_of_le ( le_trans ( Finset.card_le_card
        ( show S ⊆ Finset.range ( recSeq n ( ℓ + 1 ) ) from fun x hx => Finset.mem_range.mpr ( hS_sub x hx ) ) ) ( by simp ) ) ];
  · aesop;
  · simp +decide [ Finset.disjoint_left ]

/-! ## Level validity lemmas -/

lemma recSeq1_le_half (n : ℕ) (hn : n ≥ 16) : recSeq n 1 ≤ n / 2 := by
  classical
  have h_log_lt : Nat.log 2 (n - 1) < n / 2 := by
    refine' Nat.log_lt_of_lt_pow _ _; · omega
    · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> norm_num
      · exact Nat.le_induction (by decide) (fun m hm ih => by rw [pow_succ']; omega) k (show k ≥ 8 by linarith)
      · norm_num [Nat.add_div]
        exact Nat.le_induction (by decide) (fun n hn ih => by rw [pow_succ']; linarith) k (show k ≥ 8 by linarith)
  unfold recSeq; unfold recSeq; split_ifs <;> omega

lemma level0_valid (n : ℕ) (hn : n ≥ 16) : LevelValid n 0 := by
  classical
  constructor
  · unfold recSeq; split_ifs <;> norm_num
    exact Nat.succ_le_succ (Nat.le_log_of_pow_le (by norm_num) (Nat.le_sub_one_of_lt (by linarith)))
  · simp +arith +decide [wOff]
    linarith [Nat.div_mul_le_self n 2, recSeq1_le_half n hn]
  · rcases n with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n) <;> simp +arith +decide [spA] at *
    unfold spAux; simp +arith +decide [levelVSize]
    split_ifs <;> simp_all +arith +decide [recSeq]
  · linarith

/-- Shifting the recursive sequence by one step changes its initial value. -/
lemma recSeq_shift (n k : ℕ) : recSeq n (k + 1) = recSeq (recSeq n 1) k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun t => recSeq t 1) ih

lemma levelVSize_shift (n k : ℕ) :
    levelVSize n (k + 1) = levelVSize (recSeq n 1) k := by
  unfold levelVSize
  rw [recSeq_shift n (k + 1)]

lemma vOff_shift (n k : ℕ) :
    vOff n (k + 1) = levelVSize n 0 + vOff (recSeq n 1) k := by
  induction k with
  | zero => simp [vOff]
  | succ k ih =>
    rw [vOff_succ, ih, vOff_succ, levelVSize_shift]
    omega

/-- The auxiliary size splits into its first level and its remaining recursive size. -/
lemma spA_step (n : ℕ) (hn : 3 ≤ n) :
    spA n = levelVSize n 0 + spA (recSeq n 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  let k := Nat.log 2 (m + 2) + 1
  have hrec : recSeq (m + 3) 1 = k := by
    simp [recSeq, k]
  change spAux (m + 3) = _
  rw [spAux]
  simp only [levelVSize, hrec, spA]
  change (if k ≤ 2 then 2 ^ k + k - 1 + 1 else 2 ^ k + k - 1 + spAux k) =
    2 ^ k + k - 1 + spAux k
  split_ifs with hk
  · have haux : spAux k = 1 := by
      interval_cases k <;> simp [spAux]
    rw [haux]
  · rfl

lemma recSeq1_ge_four' (n : ℕ) (hn : n ≥ 16) : recSeq n 1 ≥ 4 := by
  classical
  rw [show recSeq n 1 = if n ≤ 2 then 2 else Nat.log 2 (n - 1) + 1 from rfl]
  split_ifs <;> linarith [Nat.le_log_of_pow_le (by decide) (by omega : n - 1 ≥ 2 ^ 3)]

set_option maxHeartbeats 3200000 in
lemma level1_valid (n : ℕ) (hn : n ≥ 16) : LevelValid n 1 := by
  classical
  constructor;
  · exact recSeq_ge_two n 1 (recSeq_ge_two n 0 (show n ≥ 2 by omega));
  · rcases n with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n ) <;> simp +arith +decide [ ] at *;
    simp +arith +decide [ recSeq ];
    rcases k : Nat.log 2 ( n + 15 ) with ( _ | _ | k ) <;> simp_all +arith +decide;
    · omega;
    · rw [ Nat.log_eq_iff ] at k <;> norm_num at *;
      rename_i k';
      rcases k' with ( _ | _ | k' ) <;> simp +arith +decide [ Nat.pow_succ' ] at *;
      · norm_num [ k ];
      · have h_log : Nat.log 2 (k' + 4) ≤ k' + 2 := by
          refine Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ?_ ?_ ) <;> norm_num;
          exact Nat.recOn k' ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith;
        linarith [ Nat.div_mul_le_self ( n + 16 ) 2,
          show 2 ^ k' ≥ k' + 1 from Nat.recOn k' ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ ihn ] ];
  · have hnext := recSeq1_ge_four' n hn
    have hstep := spA_step (recSeq n 1) (by omega)
    rw [vOff_shift, spA_step n (by omega)]
    simp only [vOff, zero_add]
    omega
  · grind

lemma level0_max_ge_n' (n : ℕ) (hn : n ≥ 3) :
    2 ^ (recSeq n 1) + recSeq n 1 ≥ n := by
  classical
  rw [show recSeq n 1 = Nat.log 2 (n - 1) + 1 from ?_]
  · exact le_add_of_le_of_nonneg (Nat.le_of_pred_lt (Nat.lt_pow_succ_log_self (by decide) _)) (Nat.zero_le _)
  · rcases n with (_ | _ | _ | n) <;> simp +arith +decide [recSeq] at *

lemma level0_strict_bound (n : ℕ) (hn : n ≥ 3) :
    n < 2 ^ (recSeq n 1) + recSeq n 1 := by
  classical
  have h : 2 ^ (recSeq n 1) ≥ n := by
    rcases n with (_ | _ | _ | _ | _ | _ | _ | n) <;> simp_all +arith +decide []
    exact Nat.lt_pow_succ_log_self (by decide) _
  linarith [show recSeq n 1 > 0 from Nat.recOn n (by trivial) fun n ihn => by (unfold recSeq; aesop)]

/-! ## Maximal clique at a level -/

/-
For any d in [k+2, 2^k+k-1], ∃ maximal clique of size d at level ℓ.
-/
lemma small_clique_at_level (n ℓ d : ℕ) (hv : LevelValid n ℓ)
    (hd_lo : recSeq n (ℓ + 1) + 2 ≤ d)
    (hd_hi : d ≤ 2 ^ recSeq n (ℓ + 1) + recSeq n (ℓ + 1) - 1) :
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  classical
  refine' ⟨ _, _, _ ⟩;
  exact smallCl n ℓ ( Finset.range ( recSeq n ( ℓ + 1 ) ) \ ( Finset.image ( fun i : Fin ( recSeq n ( ℓ + 1 ) ) => i.val )
    ( Classical.choose ( binary_expansion ( recSeq n ( ℓ + 1 ) ) ( d - ( recSeq n ( ℓ + 1 ) + 1 ) ) ( by omega ) ) ) ) );
  · refine' smallCl_isMaximalClique n ℓ _ hv _ _ _;
    · have := Classical.choose_spec ( binary_expansion ( recSeq n ( ℓ + 1 ) ) ( d - ( recSeq n ( ℓ + 1 ) + 1 ) ) ( by omega ) );
      contrapose! this; simp_all +decide [ Finset.ext_iff ] ;
      have h_sum_eq : ∑ i ∈ Classical.choose (binary_expansion (recSeq n (ℓ + 1))
          (d - (recSeq n (ℓ + 1) + 1)) (by omega)), 2 ^ (i : ℕ)
          = ∑ i ∈ Finset.range (recSeq n (ℓ + 1)), 2 ^ i := by
        refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> aesop;
      rw [ h_sum_eq, Nat.geomSum_eq ] <;> norm_num;
      omega;
    · aesop;
    · have := Classical.choose_spec ( binary_expansion ( recSeq n ( ℓ + 1 ) ) ( d - ( recSeq n ( ℓ + 1 ) + 1 ) ) ( by omega ) );
      contrapose! this;
      rw [ Finset.sum_eq_zero ] <;> norm_num;
      · omega;
      · grind;
  · convert smallCl_card n ℓ _ hv _ using 1;
    · rw [ Finset.sdiff_sdiff_eq_self ];
      · have := Classical.choose_spec ( binary_expansion ( recSeq n ( ℓ + 1 ) ) ( d - ( recSeq n ( ℓ + 1 ) + 1 ) ) ( by omega ) );
        rw [ Finset.sum_image ];
        · omega;
        · exact fun x hx y hy hxy => Fin.ext hxy;
      · exact Finset.image_subset_iff.mpr fun i hi => Finset.mem_range.mpr i.2;
    · aesop

/-! ## Coverage -/

/-
When ℓ ≥ 1 and recSeq n (ℓ+1) ≥ 4, n must be at least 257.
-/
lemma n_ge_257_of_deep (n ℓ : ℕ) (hn : n ≥ 16)
    (hv : LevelValid n ℓ) (hℓ : ℓ ≥ 1) (h4 : recSeq n (ℓ + 1) ≥ 4) :
    n ≥ 257 := by
  classical
  -- By definition of recSeq, we know that recSeq n 2 ≥ 4.
  have h_recSeq2 : recSeq n 2 ≥ 4 := by
    have h_recSeq2 : ∀ k ≥ 2, recSeq n k ≥ 4 → recSeq n 2 ≥ 4 := by
      intros k hk h4k
      induction' hk with k hk ih;
      · assumption;
      · apply ih;
        contrapose! h4k;
        interval_cases _ : recSeq n k <;> simp_all +decide [ recSeq ];
    grind;
  contrapose! h_recSeq2;
  interval_cases n <;> decide

/-
The sum of iterated logs is bounded: wOff n k ≤ 2 * recSeq n 1
    when all intermediate recSeq values are ≥ 4.
-/
lemma wOff_bound_ge4 (n k : ℕ)
    (hk : ∀ i, 1 ≤ i → i ≤ k → recSeq n i ≥ 4) :
    wOff n k ≤ 2 * recSeq n 1 := by
  classical
  rcases k with ( _ | _ | k ) <;> simp +arith +decide [ * ];
  have h_ineq : ∀ i, 1 ≤ i → i ≤ k + 1 → recSeq n (i + 1) ≤ recSeq n i - 1 := by
    intros i hi1 hi2;
    rw [ recSeq ];
    split_ifs <;> norm_num;
    · linarith [ hk i hi1 ( by linarith ) ];
    · exact Nat.log_lt_of_lt_pow ( Nat.sub_ne_zero_of_lt ( by linarith ) )
        ( by exact Nat.recOn ( recSeq n i - 1 ) ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ ] at * ; linarith );
  have h_ineq_sum : ∀ i, 1 ≤ i → i ≤ k + 1 → recSeq n i + ∑ j ∈ Finset.Icc 1 i, recSeq n j ≤ 2 * recSeq n 1 := by
    intro i hi₁ hi₂; induction hi₁ <;> simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ] ;
    · linarith;
    · rename_i m hm ih;
      have h_subst : 2 * recSeq n (m + 1) ≤ recSeq n m := by
        have h_subst : recSeq n (m + 1) ≤ Nat.log 2 (recSeq n m - 1) + 1 := by
          rw [ recSeq ];
          grind +splitImp;
        have h_subst : 2 ^ (Nat.log 2 (recSeq n m - 1)) ≤ recSeq n m - 1 := by
          exact Nat.pow_log_le_self 2 ( Nat.sub_ne_zero_of_lt ( by linarith [ hk m hm ( by linarith ) ] ) );
        have h_subst : 2 * (Nat.log 2 (recSeq n m - 1) + 1) ≤ recSeq n m := by
          rcases x : Nat.log 2 ( recSeq n m - 1 ) with ( _ | _ | _ | _ | k ) <;> simp_all +arith +decide [ Nat.pow_succ ];
          · exact le_of_not_gt fun h => by have := hk m hm ( by linarith ) ; interval_cases recSeq n m ;
          · exact hk m hm ( by linarith );
          · grind;
          · omega;
          · have h_subst : 2 ^ k ≥ k + 1 := by
              exact Nat.recOn k ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith;
            omega;
        linarith;
      linarith [ ih ( by linarith ) ];
  specialize h_ineq_sum ( k + 1 ) ; simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
  rw [ show wOff n k = ∑ i ∈ Finset.Icc 1 k, recSeq n i from ?_ ];
  · linarith! [ h_ineq ( k + 1 ) ( by linarith ) ( by linarith ),
      Nat.sub_add_cancel ( show 1 ≤ recSeq n ( k + 1 ) from by linarith [ hk ( k + 1 ) ( by linarith ) ( by linarith ) ] ) ];
  · refine' Nat.recOn k _ _ <;> simp +arith +decide [ *, Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ]

/-
For n ≥ 257, 4 * (recSeq n 1) ≤ n.
-/
lemma four_recSeq_le (n : ℕ) (hn : n ≥ 257) : 4 * recSeq n 1 ≤ n := by
  classical
  rw [ show recSeq n 1 = Nat.log 2 ( n - 1 ) + 1 from ?_ ];
  · -- We'll use that $2^{Nat.log 2 (n - 1)} \leq n - 1$ and $Nat.log 2 (n - 1) \leq \frac{n}{4} - 1$ for $n \geq 257$.
    have h_log : 2 ^ (Nat.log 2 (n - 1)) ≤ n - 1 := by
      exact Nat.pow_log_le_self 2 ( Nat.sub_ne_zero_of_lt ( by linarith ) )
    have h_log_bound : Nat.log 2 (n - 1) ≤ n / 4 - 1 := by
      have h_log_bound : ∀ k ≥ 8, 2 ^ k > 4 * k + 3 := by
        exact fun k hk => by induction hk <;> norm_num [ Nat.pow_succ ] at * ; linarith;
      grind +locals;
    omega;
  · rcases n with ( _ | _ | n ) <;> simp +arith +decide [ recSeq ] at *;
    aesop

/-
vOff is bounded by spA when the recursive branch is taken at each level.
-/
lemma vOff_le_spA (n ℓ : ℕ) (hn : n ≥ 3)
    (hall : ∀ i, 0 ≤ i → i ≤ ℓ → recSeq n (i + 1) ≥ 3) :
    vOff n (ℓ + 1) ≤ spA n := by
  induction ℓ generalizing n with
  | zero =>
    rw [vOff_shift, spA_step n hn]
    simp [vOff]
  | succ ℓ ih =>
    have hnext : 3 ≤ recSeq n 1 := hall 0 (by omega) (by omega)
    have hall' : ∀ i, 0 ≤ i → i ≤ ℓ → recSeq (recSeq n 1) (i + 1) ≥ 3 := by
      intro i _ hi
      rw [← recSeq_shift n (i + 1)]
      exact hall (i + 1) (by omega) (by omega)
    rw [vOff_shift, spA_step n hn]
    exact Nat.add_le_add_left (ih (recSeq n 1) hnext hall') _

/-
Level validity propagates: from level ℓ to ℓ+1 when recSeq ≥ 4.

spAux m ≥ 2^(recSeq m 1) + recSeq m 1 for m ≥ 3.
-/
lemma spAux_ge_levelVSize (m : ℕ) (hm : m ≥ 3) :
    spAux m ≥ 2 ^ (recSeq m 1) + recSeq m 1 := by
  classical
  unfold spAux recSeq;
  rcases m with ( _ | _ | _ | m ) <;> simp +arith +decide [ recSeq ] at *;
  split_ifs <;> simp_all +arith +decide [ Nat.pow_succ' ];
  exact spAux_pos _

/-
The recSeq sequence is non-increasing for values ≥ 4:
    if recSeq n j ≥ 4, then recSeq n i ≥ 4 for all i ≤ j.
-/
lemma recSeq_mono_ge4 (n i j : ℕ) (hij : i ≤ j) (hj : recSeq n j ≥ 4) :
    recSeq n i ≥ 4 := by
  classical
  contrapose! hj;
  induction hij <;> simp_all +decide [ recSeq ];
  interval_cases recSeq n ‹_› <;> decide

/-
For n ≥ 257, 6 * recSeq n 1 ≤ n.
-/
lemma six_recSeq_le (n : ℕ) (hn : n ≥ 257) : 6 * recSeq n 1 ≤ n := by
  classical
  rw [ show recSeq n 1 = Nat.log 2 ( n - 1 ) + 1 from ?_ ];
  · have := Nat.pow_log_le_self 2 ( Nat.sub_ne_zero_of_lt ( by linarith : 1 < n ) );
    rcases k : Nat.log 2 ( n - 1 ) with ( _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> simp_all +arith +decide [ Nat.pow_succ ];
    any_goals omega;
    rename_i k';
    exact le_trans ( by
      { exact Nat.recOn k' ( by norm_num ) fun n ihn => by norm_num [ Nat.pow_succ' ] at * ; linarith } )
      ( Nat.le_trans this ( Nat.sub_le _ _ ) );
  · rcases n with ( _ | _ | n ) <;> simp +arith +decide [ recSeq ] at *;
    aesop

/-
Level validity propagates: from level ℓ to ℓ+1 when recSeq ≥ 4.
-/
set_option maxHeartbeats 1200000 in
lemma next_level_valid (n ℓ : ℕ) (hn : n ≥ 16)
    (hv : LevelValid n ℓ) (h4 : recSeq n (ℓ + 1) ≥ 4) :
    LevelValid n (ℓ + 1) := by
  classical
  constructor;
  · exact recSeq_ge_two _ _ ( by linarith );
  · -- Using the bound $wOff n (ℓ + 1) ≤ 2 * recSeq n 1$ and $recSeq n (ℓ + 2) ≤ recSeq n 1$, we get:
    have h_wOff_bound : wOff n (ℓ + 1 + 1) ≤ 2 * recSeq n 1 + recSeq n 1 := by
      have h_wOff_bound : wOff n (ℓ + 1) ≤ 2 * recSeq n 1 := by
        apply wOff_bound_ge4;
        exact fun i a a_1 ↦ recSeq_mono_ge4 n i (ℓ + 1) a_1 h4;
      have h_recSeq_bound : ∀ i, 1 ≤ i → i ≤ ℓ + 1 → recSeq n (i + 1) ≤ recSeq n i := by
        intros i hi1 hi2;
        have h_recSeq_bound : ∀ i, 1 ≤ i → i ≤ ℓ + 1 → recSeq n i ≥ 3 := by
          have h_recSeq_bound : ∀ i, 1 ≤ i → i ≤ ℓ + 1 → recSeq n i ≥ 4 := by
            intros i hi1 hi2;
            apply recSeq_mono_ge4 n i (ℓ + 1) hi2 h4;
          grind +splitImp;
        exact Nat.le_of_lt ( recSeq_decreasing n i ( h_recSeq_bound i hi1 hi2 ) );
      have h_recSeq_bound : ∀ i, 1 ≤ i → i ≤ ℓ + 1 → recSeq n (i + 1) ≤ recSeq n 1 := by
        intro i hi₁ hi₂; induction hi₁ <;> simp_all +arith +decide;
        grind;
      exact add_le_add h_wOff_bound ( h_recSeq_bound _ ( by linarith ) ( by linarith ) );
    by_cases h₂ : n ≥ 257;
    · linarith [ Nat.div_mul_le_self n 2, six_recSeq_le n h₂ ];
    · -- Below 257, the deep-level bound forces the first level.
      have hl0 : ℓ = 0 := by
        by_contra hne
        exact h₂ (n_ge_257_of_deep n ℓ hn hv (by omega) h4)
      subst ℓ
      interval_cases n <;> decide
  · by_cases h_recSeq_ge_3 : recSeq n (ℓ + 2) ≥ 3;
    · apply vOff_le_spA n (ℓ + 1) (by omega);
      intros i hi_nonneg hi_le_ℓ_plus_1
      by_cases hi : i ≤ ℓ;
      · have := recSeq_mono_ge4 n ( i + 1 ) ( ℓ + 1 ) ( by linarith ) h4; linarith;
      · grind;
    · interval_cases _ : recSeq n ( ℓ + 2 ) <;> simp_all +decide [ vOff ];
      · exact absurd ‹_› ( by linarith [ recSeq_ge_two n ( ℓ + 1 ) ( by linarith ) ] );
      · exact absurd ‹_› ( by exact ne_of_gt ( Nat.le_trans ( by decide ) ( recSeq_ge_two _ _ ( by linarith ) ) ) );
      · have h_vOff_le_spA : spA n = vOff n (ℓ + 1) + spAux (recSeq n (ℓ + 1)) := by
          have h_vOff_le_spA : ∀ ℓ, (∀ i, 0 ≤ i → i ≤ ℓ → recSeq n (i + 1) ≥ 3) → spA n
              = vOff n (ℓ + 1) + spAux (recSeq n (ℓ + 1)) := by
            intro ℓ hℓ; induction' ℓ with ℓ ih <;> simp_all +decide [ vOff ] ;
            · unfold spA levelVSize; simp +decide [ recSeq ] ;
              rcases n with ( _ | _ | _ | n ) <;> simp_all +arith +decide [ ];
              rw [ spAux ] ; simp +arith +decide [ ];
              exact fun h => absurd h ( by exact not_le_of_gt ( Nat.le_log_of_pow_le ( by norm_num ) ( by linarith ) ) );
            · rw [ ih fun i hi => hℓ i ( by linarith ) ];
              unfold levelVSize; simp +arith +decide [ * ] ;
              rw [ show recSeq n ( ℓ + 2 ) = Nat.log 2 ( recSeq n ( ℓ + 1 ) - 1 ) + 1 from ?_ ];
              · rcases k : recSeq n ( ℓ + 1 ) with ( _ | _ | _ | k ) <;> simp_all +arith +decide;
                · grind +revert;
                · linarith [ hℓ ℓ ( by linarith ) ];
                · linarith [ hℓ ℓ ( by linarith ) ];
                · rw [ spAux ] ; simp +arith +decide [ ];
                  intro h; interval_cases _ : Nat.log 2 ( _ + 2 ) <;> simp_all +decide ;
                  decide +kernel;
              · exact if_neg ( by linarith [ hℓ ℓ ( by linarith ) ] );
          apply h_vOff_le_spA;
          intros i hi_nonneg hi_le_ℓ
          have h_recSeq_ge_3 : recSeq n (i + 1) ≥ 4 := by
            apply recSeq_mono_ge4 n (i + 1) (ℓ + 1) (by linarith) h4
          linarith [h_recSeq_ge_3];
        have h_spAux_ge_levelVSize : spAux (recSeq n (ℓ + 1))
            ≥ levelVSize (recSeq n (ℓ + 1)) 0 + 1 := by
          convert spAux_ge_levelVSize ( recSeq n ( ℓ + 1 ) ) ( by linarith ) using 1;
          unfold levelVSize; simp +arith +decide [ * ] ;
          rw [ Nat.sub_add_cancel ( Nat.one_le_iff_ne_zero.mpr <| by positivity ) ];
        unfold levelVSize at * ; simp_all +decide [ Nat.pow_succ' ];
        unfold levelVSize at * ; simp_all +decide [ ];
        unfold recSeq at * ; simp_all +decide [ Nat.pow_succ' ];
        split_ifs at * <;> simp_all +arith +decide [ ];
        · exact Nat.le_of_add_left_le h_spAux_ge_levelVSize;
        · grind +suggestions;
  · have := hv.recSeq_ge; (
      have := hv.wfit; ( have := hv.vfit; ( have := hv.fuel; ( norm_num at *; ) ) ) );
    -- By definition of $wOff$, we know that $wOff n ℓ \geq 4 * ℓ$.
    have hwOff_ge : wOff n ℓ ≥ 4 * ℓ := by
      have hwOff_ge : ∀ i ≤ ℓ, recSeq n (i + 1) ≥ 4 := by
        intros i hi;
        apply recSeq_mono_ge4 n (i + 1) (ℓ + 1) (by linarith) h4;
      have hwOff_ge : ∀ i ≤ ℓ, wOff n i ≥ 4 * i := by
        intro i hi; induction' i with i ih <;> simp_all +decide [ Nat.mul_succ, wOff ] ;
        linarith [ ih ( Nat.le_of_lt hi ), hwOff_ge i ( Nat.le_of_lt hi ) ];
      exact hwOff_ge ℓ le_rfl;
    omega

/-- Recursive coverage with n ≥ 16 hypothesis. -/
lemma recursive_coverage (n ℓ d : ℕ)
    (hn : n ≥ 16)
    (hv : LevelValid n ℓ)
    (hd_lo : 5 ≤ d)
    (hd_hi : d ≤ 2 ^ recSeq n (ℓ + 1) + recSeq n (ℓ + 1) - 1) :
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  classical
  -- By strong induction on recSeq n (ℓ+1)
  suffices h : ∀ k l, k = recSeq n (l + 1) → LevelValid n l →
      5 ≤ d → d ≤ 2 ^ k + k - 1 →
      ∃ s : Finset (SpVtx n (spA n)), IsMaximalClique (spGraph n) s ∧ s.card = d from
    h _ ℓ rfl hv hd_lo hd_hi
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro l hk_eq hv' hd1' hd2'
    by_cases hbig : d ≥ k + 2
    · exact small_clique_at_level n l d hv' (by omega) (by subst hk_eq; omega)
    · -- d < k + 2, so k ≥ 4 (since d ≥ 5)
      push Not at hbig
      have hk4 : k ≥ 4 := by omega
      -- Level overlap gives the range at next level covers d
      have h_overlap := level_overlap n (l + 1) (by rw [← hk_eq]; omega)
      set k' := recSeq n (l + 2) with hk'_def
      have h_lt : k' < k := by
        rw [hk_eq]; exact recSeq_decreasing n (l + 1) (by rw [← hk_eq]; omega)
      have hd_next : d ≤ 2 ^ k' + k' - 1 := by omega
      -- Need LevelValid n (l+1)
      have hv'' : LevelValid n (l + 1) :=
        next_level_valid n l hn hv' (by rw [← hk_eq]; omega)
      exact ih k' h_lt (l + 1) rfl hv'' hd1' hd_next

/-
For each d with 5 ≤ d ≤ n, there exists a maximal clique of size d.
-/
theorem small_clique_exists (n : ℕ) (hn : n ≥ 16) (d : ℕ)
    (hd1 : 5 ≤ d) (hd2 : d ≤ n) :
    ∃ s : Finset (SpVtx n (spA n)),
      IsMaximalClique (spGraph n) s ∧ s.card = d := by
  classical
  apply recursive_coverage n 0 d hn (level0_valid n hn) hd1 (by
    exact le_trans hd2 ( Nat.le_sub_one_of_lt ( level0_strict_bound n ( by linarith ) ) ))

end Erdos927
