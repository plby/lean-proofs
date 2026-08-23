/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1128.
https://www.erdosproblems.com/forum/thread/1128

Informal authors:
- Karel Prikry
- George Mills

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1128.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1128.lean
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 1128

The problem asks whether every two-coloring of a product of three sets of
cardinality `aleph 1` has a monochromatic product of three countably infinite
sets.  The answer is negative.  This file formalizes a Mills--Prikry style
counterexample built from a locally finite coherent rank on `omega₁`.

The mathematical proof and a lemma-by-lemma Leanization guide are in
`tex/1128.tex`.
-/

open Cardinal Set Ordinal Order

namespace Erdos1128

noncomputable section

abbrev Omega1 := (Cardinal.aleph 1).ord.ToType

theorem omega1_mk : #Omega1 = Cardinal.aleph 1 := by
  exact Cardinal.mk_ord_toType _

theorem init_countable (x : Omega1) : Countable (Set.Iio x) := by
  rw [← Cardinal.mk_le_aleph0_iff, ← Cardinal.lt_aleph_one_iff]
  exact Cardinal.mk_Iio_toType_ord_lt x

noncomputable def rank (x : Omega1) : Set.Iio x → ℕ := by
  letI : Countable (Set.Iio x) := init_countable x
  letI : Encodable (Set.Iio x) := Encodable.ofCountable _
  exact Encodable.encode

theorem rank_injective (x : Omega1) : Function.Injective (rank x) := by
  letI : Countable (Set.Iio x) := init_countable x
  letI : Encodable (Set.Iio x) := Encodable.ofCountable _
  exact Encodable.encode_injective

noncomputable def rankExt (z x : Omega1) : ℕ :=
  if h : x < z then rank z ⟨x, h⟩ else 0

theorem rankExt_injOn (z : Omega1) :
    Set.InjOn (rankExt z) (Set.Iio z) := by
  intro x hx y hy hxy
  change x < z at hx
  change y < z at hy
  simp [rankExt, hx, hy] at hxy
  exact congrArg Subtype.val (rank_injective z hxy)

def ladder (z : Omega1) : Set Omega1 :=
  {x | x < z ∧ ∀ y, x < y → y < z → rankExt z x < rankExt z y}

theorem ladder_lt {z x : Omega1} (hx : x ∈ ladder z) : x < z := hx.1

theorem exists_ladder_ge {a z : Omega1} (haz : a < z) :
    ∃ x ∈ ladder z, a ≤ x := by
  let s : Set Omega1 := Set.Ico a z
  have hs : s.Nonempty := ⟨a, by simp [s, haz]⟩
  obtain ⟨x, hx, hmin⟩ :=
    (InvImage.wf (rankExt z) Nat.lt_wfRel.wf).has_min s hs
  refine ⟨x, ?_, hx.1⟩
  refine ⟨hx.2, ?_⟩
  intro y hxy hyz
  have hys : y ∈ s := ⟨hx.1.trans hxy.le, hyz⟩
  have hnlt : ¬ rankExt z y < rankExt z x := hmin y hys
  have hne : rankExt z x ≠ rankExt z y := by
    intro he
    exact hxy.ne (rankExt_injOn z hx.2 hyz he)
  omega

theorem ladder_rank_lt {z x y : Omega1}
    (hx : x ∈ ladder z) (hy : y ∈ ladder z) (hxy : x < y) :
    rankExt z x < rankExt z y :=
  hx.2 y hxy hy.1

theorem ladder_below_finite (z a : Omega1) (haz : a < z) :
    (ladder z ∩ Set.Iio a).Finite := by
  obtain ⟨y, hyC, hay⟩ := exists_ladder_ge haz
  let t : Set Omega1 := {x | x < z ∧ rankExt z x < rankExt z y}
  have ht : t.Finite := by
    apply Set.Finite.of_finite_image (f := rankExt z)
    · apply (Set.finite_Iio (rankExt z y)).subset
      rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · exact (rankExt_injOn z).mono fun _ hx => hx.1
  apply ht.subset
  rintro x ⟨hxC, hxa⟩
  exact ⟨hxC.1, ladder_rank_lt hxC hyC (hxa.trans_le hay)⟩

def stepSet (a z : Omega1) : Set Omega1 :=
  ladder z ∩ Set.Ici a

theorem stepSet_nonempty {a z : Omega1} (haz : a < z) :
    (stepSet a z).Nonempty := by
  obtain ⟨x, hxC, hax⟩ := exists_ladder_ge haz
  exact ⟨x, hxC, hax⟩

theorem omega1_wf : WellFounded ((· < ·) : Omega1 → Omega1 → Prop) :=
  IsWellFounded.wf

noncomputable def step (a z : Omega1) (haz : a < z) : Omega1 :=
  omega1_wf.min (stepSet a z) (stepSet_nonempty haz)

theorem step_mem_ladder {a z : Omega1} (haz : a < z) :
    step a z haz ∈ ladder z :=
  (omega1_wf.min_mem (stepSet a z) (stepSet_nonempty haz)).1

theorem le_step {a z : Omega1} (haz : a < z) :
    a ≤ step a z haz :=
  (omega1_wf.min_mem (stepSet a z) (stepSet_nonempty haz)).2

theorem step_lt {a z : Omega1} (haz : a < z) :
    step a z haz < z :=
  ladder_lt (step_mem_ladder haz)

theorem step_le_of_mem {a z x : Omega1} (haz : a < z)
    (hxC : x ∈ ladder z) (hax : a ≤ x) :
    step a z haz ≤ x := by
  apply le_of_not_gt
  exact omega1_wf.not_lt_min (stepSet a z) ⟨hxC, hax⟩

theorem step_mono {a b z : Omega1} (hab : a < b) (hbz : b < z) :
    step a z (hab.trans hbz) ≤ step b z hbz :=
  step_le_of_mem (hab.trans hbz) (step_mem_ladder hbz)
    (hab.le.trans (le_step hbz))

theorem step_lt_bound_of_lt {a b z : Omega1} (hab : a < b) (hbz : b < z)
    (hs : step a z (hab.trans hbz) < step b z hbz) :
    step a z (hab.trans hbz) < b := by
  by_contra h
  have hbs : b ≤ step a z (hab.trans hbz) := le_of_not_gt h
  have hle := step_le_of_mem hbz (step_mem_ladder (hab.trans hbz)) hbs
  exact (not_lt_of_ge hle) hs

noncomputable def ladderBelow (z a : Omega1) (haz : a < z) : Finset Omega1 :=
  (ladder_below_finite z a haz).toFinset

@[simp] theorem mem_ladderBelow {z a x : Omega1} {haz : a < z} :
    x ∈ ladderBelow z a haz ↔ x ∈ ladder z ∧ x < a := by
  simp [ladderBelow]

theorem ladderBelow_eq_of_step_eq {a b z : Omega1} (hab : a < b) (hbz : b < z)
    (hs : step a z (hab.trans hbz) = step b z hbz) :
    ladderBelow z a (hab.trans hbz) = ladderBelow z b hbz := by
  ext x
  simp only [mem_ladderBelow]
  constructor
  · exact fun hx => ⟨hx.1, hx.2.trans hab⟩
  · intro hx
    refine ⟨hx.1, ?_⟩
    by_contra hxa
    have hax : a ≤ x := le_of_not_gt hxa
    have hxs : step a z (hab.trans hbz) ≤ x :=
      step_le_of_mem (hab.trans hbz) hx.1 hax
    have hxb : x < step b z hbz :=
      hx.2.trans_le (le_step hbz)
    rw [hs] at hxs
    exact (not_lt_of_ge hxs) hxb

noncomputable def rhoBody (z : Omega1)
    (rec : ∀ y : Omega1, y < z → Omega1 → ℕ) (x : Omega1) : ℕ :=
  if hx : x < z then
    max (ladderBelow z x hx).card
      (max (rec (step x z hx) (step_lt hx) x)
        ((ladderBelow z x hx).sup fun y => rec x hx y))
  else 0

noncomputable def rho (x z : Omega1) : ℕ :=
  omega1_wf.fix rhoBody z x

theorem rho_eq_of_lt {x z : Omega1} (hx : x < z) :
    rho x z =
      max (ladderBelow z x hx).card
        (max (rho x (step x z hx))
          ((ladderBelow z x hx).sup fun y => rho y x)) := by
  rw [rho, WellFounded.fix_eq]
  simp only [rhoBody, dif_pos hx]
  rfl

theorem rho_eq_zero_of_le {x z : Omega1} (hx : z ≤ x) :
    rho x z = 0 := by
  rw [rho, WellFounded.fix_eq]
  simp [rhoBody, not_lt_of_ge hx]

@[simp] theorem rho_self (x : Omega1) : rho x x = 0 :=
  rho_eq_zero_of_le le_rfl

theorem ladderBelow_card_le_rho {x z : Omega1} (hx : x < z) :
    (ladderBelow z x hx).card ≤ rho x z := by
  rw [rho_eq_of_lt hx]
  exact le_max_left _ _

theorem rho_step_le {x z : Omega1} (hx : x < z) :
    rho x (step x z hx) ≤ rho x z := by
  rw [rho_eq_of_lt hx]
  exact (le_max_left _ _).trans (le_max_right _ _)

theorem rho_ladder_le {x z y : Omega1} (hx : x < z)
    (hy : y ∈ ladderBelow z x hx) :
    rho y x ≤ rho x z := by
  rw [rho_eq_of_lt hx]
  refine (Finset.le_sup (s := ladderBelow z x hx)
    (f := fun y => rho y x) hy).trans ?_
  exact (le_max_right _ _).trans (le_max_right _ _)

theorem ladderBelow_subset {a b z : Omega1} (hab : a < b) (hbz : b < z) :
    ladderBelow z a (hab.trans hbz) ⊆ ladderBelow z b hbz := by
  intro x hx
  rw [mem_ladderBelow] at hx ⊢
  exact ⟨hx.1, hx.2.trans hab⟩

def TrianglesAt (z : Omega1) : Prop :=
  ∀ ⦃a b : Omega1⦄, a < b → b < z →
    rho a z ≤ max (rho a b) (rho b z) ∧
    rho a b ≤ max (rho a z) (rho b z)

theorem rho_triangles_at : ∀ z : Omega1, TrianglesAt z := by
  intro z
  apply omega1_wf.induction z
  intro z ih a b hab hbz
  let ha : a < z := hab.trans hbz
  let sa : Omega1 := step a z ha
  let sb : Omega1 := step b z hbz
  have hsa_le : sa ≤ sb := step_mono hab hbz
  have hsa_z : sa < z := step_lt ha
  have hsb_z : sb < z := step_lt hbz
  by_cases hs : sa = sb
  · have hCeq : ladderBelow z a ha = ladderBelow z b hbz :=
      ladderBelow_eq_of_step_eq hab hbz hs
    constructor
    · let n := max (rho a b) (rho b z)
      rw [rho_eq_of_lt ha]
      apply max_le
      · rw [hCeq]
        exact (ladderBelow_card_le_rho hbz).trans (le_max_right _ _)
      · apply max_le
        · change rho a sa ≤ max (rho a b) (rho b z)
          have hbs : b ≤ sa := by
            rw [hs]
            exact le_step hbz
          rcases hbs.eq_or_lt with hba | hblt
          · rw [← hba]
            exact le_max_left (rho a b) (rho b z)
          · have htri := ih sa hsa_z hab hblt
            have hstepb : rho b sa ≤ rho b z := by
              rw [hs]
              exact rho_step_le hbz
            exact htri.1.trans (max_le_max le_rfl hstepb)
        · apply Finset.sup_le
          intro x hx
          have hxa : x < a := (mem_ladderBelow.mp hx).2
          have hxb : x < b := hxa.trans hab
          have htri := ih b hbz hxa hab
          have hmem : x ∈ ladderBelow z b hbz := by
            rw [← hCeq]
            exact hx
          have hxbnd := rho_ladder_le hbz hmem
          exact htri.2.trans
            (max_le
              (hxbnd.trans (le_max_right _ _))
              (le_max_left _ _))
    · let n := max (rho a z) (rho b z)
      have hbs : b ≤ sa := by
        rw [hs]
        exact le_step hbz
      rcases hbs.eq_or_lt with hba | hblt
      · calc
          rho a b = rho a sa := congrArg (rho a) hba
          _ = rho a (step a z ha) := rfl
          _ ≤ rho a z := rho_step_le ha
          _ ≤ max (rho a z) (rho b z) := le_max_left _ _
      · have htri := ih sa hsa_z hab hblt
        have has : rho a sa ≤ rho a z := rho_step_le ha
        have hbs' : rho b sa ≤ rho b z := by
          rw [hs]
          exact rho_step_le hbz
        exact htri.2.trans (max_le_max has hbs')
  · have hslt : sa < sb := lt_of_le_of_ne hsa_le hs
    have hsab : sa < b := step_lt_bound_of_lt hab hbz hslt
    have hsaC : sa ∈ ladder z := step_mem_ladder ha
    have hsa_mem_b : sa ∈ ladderBelow z b hbz := by
      rw [mem_ladderBelow]
      exact ⟨hsaC, hsab⟩
    constructor
    · rw [rho_eq_of_lt ha]
      apply max_le
      · exact (Finset.card_le_card (ladderBelow_subset hab hbz)).trans
          ((ladderBelow_card_le_rho hbz).trans (le_max_right _ _))
      · apply max_le
        · change rho a sa ≤ max (rho a b) (rho b z)
          have has : a ≤ sa := le_step ha
          rcases has.eq_or_lt with hae | halt
          · rw [← hae]
            simp
          · have htri := ih b hbz halt hsab
            exact htri.2.trans
              (max_le_max le_rfl (rho_ladder_le hbz hsa_mem_b))
        · apply Finset.sup_le
          intro x hx
          have hxa : x < a := (mem_ladderBelow.mp hx).2
          have htri := ih b hbz hxa hab
          have hmem : x ∈ ladderBelow z b hbz :=
            ladderBelow_subset hab hbz hx
          have hxbnd := rho_ladder_le hbz hmem
          exact htri.2.trans
            (max_le
              (hxbnd.trans (le_max_right _ _))
              (le_max_left _ _))
    · have has : a ≤ sa := le_step ha
      rcases has.eq_or_lt with hae | halt
      · have hle := rho_ladder_le hbz hsa_mem_b
        rw [← hae] at hle
        exact hle.trans (le_max_right (rho a z) (rho b z))
      · have htri := ih b hbz halt hsab
        exact htri.1.trans
          (max_le_max (rho_step_le ha) (rho_ladder_le hbz hsa_mem_b))

theorem rho_triangle₁ {a b z : Omega1} (hab : a < b) (hbz : b < z) :
    rho a z ≤ max (rho a b) (rho b z) :=
  (rho_triangles_at z hab hbz).1

theorem rho_triangle₂ {a b z : Omega1} (hab : a < b) (hbz : b < z) :
    rho a b ≤ max (rho a z) (rho b z) :=
  (rho_triangles_at z hab hbz).2

theorem rho_eq_of_gt {a b z : Omega1} (hab : a < b) (hbz : b < z)
    (hgt : rho b z < rho a z) :
    rho a b = rho a z := by
  have h₁ := rho_triangle₁ hab hbz
  have h₂ := rho_triangle₂ hab hbz
  omega

def prefixSet (z s : Omega1) : Set Omega1 :=
  ladder z ∩ Set.Iio s

noncomputable def prefixCard (z s : Omega1) : ℕ :=
  (prefixSet z s).ncard

theorem prefixSet_finite {z s : Omega1} (hs : s ∈ ladder z) :
    (prefixSet z s).Finite :=
  ladder_below_finite z s hs.1

theorem prefixSet_ssubset {z s t : Omega1}
    (hs : s ∈ ladder z) (ht : t ∈ ladder z) (hst : s < t) :
    prefixSet z s ⊂ prefixSet z t := by
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · intro x hx
    exact ⟨hx.1, hx.2.trans hst⟩
  · intro heq
    have hmem : s ∈ prefixSet z t := ⟨hs, hst⟩
    rw [← heq] at hmem
    exact (lt_irrefl s) hmem.2

theorem prefixCard_lt {z s t : Omega1}
    (hs : s ∈ ladder z) (ht : t ∈ ladder z) (hst : s < t) :
    prefixCard z s < prefixCard z t := by
  exact Set.ncard_lt_ncard (prefixSet_ssubset hs ht hst)
    (prefixSet_finite ht)

theorem bounded_prefix_finite (z : Omega1) (n : ℕ) :
    {s | s ∈ ladder z ∧ prefixCard z s ≤ n}.Finite := by
  apply Set.Finite.of_finite_image (f := prefixCard z)
  · apply (Set.finite_Iic n).subset
    rintro _ ⟨s, hs, rfl⟩
    exact hs.2
  · intro s hs t ht heq
    by_contra hst
    rcases lt_or_gt_of_ne hst with hlt | hgt
    · exact (Nat.ne_of_lt (prefixCard_lt hs.1 ht.1 hlt)) heq
    · exact (Nat.ne_of_lt (prefixCard_lt ht.1 hs.1 hgt)) heq.symm

theorem ladderBelow_step_eq {x z : Omega1} (hx : x < z) :
    ladderBelow z x hx =
      ladderBelow z (step x z hx) (step_lt hx) := by
  ext y
  simp only [mem_ladderBelow]
  constructor
  · intro hy
    exact ⟨hy.1, hy.2.trans_le (le_step hx)⟩
  · intro hy
    refine ⟨hy.1, ?_⟩
    by_contra h
    have hxy : x ≤ y := le_of_not_gt h
    have hle := step_le_of_mem hx hy.1 hxy
    exact (not_lt_of_ge hle) hy.2

theorem prefixCard_step_le_rho {x z : Omega1} (hx : x < z) :
    prefixCard z (step x z hx) ≤ rho x z := by
  rw [prefixCard, Set.ncard_eq_toFinset_card _
    (prefixSet_finite (step_mem_ladder hx))]
  change (ladderBelow z (step x z hx) (step_lt hx)).card ≤ rho x z
  rw [← ladderBelow_step_eq hx]
  exact ladderBelow_card_le_rho hx

def rhoSmall (z : Omega1) (n : ℕ) : Set Omega1 :=
  {x | x ≤ z ∧ rho x z ≤ n}

theorem rhoSmall_finite : ∀ z : Omega1, ∀ n : ℕ, (rhoSmall z n).Finite := by
  intro z
  apply omega1_wf.induction z
  intro z ih n
  let p : Set Omega1 := {s | s ∈ ladder z ∧ prefixCard z s ≤ n}
  have hp : p.Finite := bounded_prefix_finite z n
  let u : Set Omega1 := {z} ∪ ⋃ s ∈ p, rhoSmall s n
  have hu : u.Finite := by
    apply Set.Finite.union (Set.finite_singleton z)
    exact hp.biUnion fun s hs => ih s hs.1.1 n
  apply hu.subset
  intro x hx
  rcases hx with ⟨hxz, hrho⟩
  by_cases hEq : x = z
  · exact Set.mem_union_left _ (by simpa [hEq])
  · have hlt : x < z := lt_of_le_of_ne hxz hEq
    let s := step x z hlt
    have hsC : s ∈ ladder z := step_mem_ladder hlt
    have hsp : s ∈ p := ⟨hsC, (prefixCard_step_le_rho hlt).trans hrho⟩
    have hxs : x ∈ rhoSmall s n :=
      ⟨le_step hlt, (rho_step_le hlt).trans hrho⟩
    apply Set.mem_union_right
    simp only [Set.mem_iUnion]
    exact ⟨s, ⟨hsp, hxs⟩⟩

theorem rho_small_finite (z : Omega1) (n : ℕ) :
    {x | x < z ∧ rho x z ≤ n}.Finite := by
  exact (rhoSmall_finite z n).subset fun x hx => ⟨hx.1.le, hx.2⟩

def rhoBall (x : Omega1) (n : ℕ) : Set Omega1 :=
  {y | y ≤ x ∧ rho y x ≤ n}

theorem rhoBall_finite (x : Omega1) (n : ℕ) :
    (rhoBall x n).Finite :=
  rhoSmall_finite x n

noncomputable def nu (x : Omega1) (n : ℕ) : ℕ :=
  (rhoBall x n).ncard

theorem rhoBall_ssubset {x y : Omega1} (hxy : x < y) {n : ℕ}
    (hr : rho x y ≤ n) :
    rhoBall x n ⊂ rhoBall y n := by
  rw [Set.ssubset_iff_subset_ne]
  constructor
  · intro z hz
    refine ⟨hz.1.trans hxy.le, ?_⟩
    rcases hz.1.eq_or_lt with hzx | hzx
    · subst z
      exact hr
    · exact (rho_triangle₁ hzx hxy).trans (max_le hz.2 hr)
  · intro heq
    have hy : y ∈ rhoBall y n := ⟨le_rfl, by simp⟩
    rw [← heq] at hy
    exact (not_lt_of_ge hy.1) hxy

theorem nu_lt {x y : Omega1} (hxy : x < y) {n : ℕ}
    (hr : rho x y ≤ n) :
    nu x n < nu y n := by
  exact Set.ncard_lt_ncard (rhoBall_ssubset hxy hr) (rhoBall_finite y n)

abbrev Key := ℕ ×ₗ ℕ

noncomputable def key (x z : Omega1) : Key :=
  toLex (rho x z, nu x (rho x z))

theorem key_fst (x z : Omega1) :
    (ofLex (key x z)).1 = rho x z := rfl

theorem key_small_finite (z : Omega1) (q : Key) :
    {x | x < z ∧ key x z ≤ q}.Finite := by
  apply (rho_small_finite z (ofLex q).1).subset
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hlex := Prod.Lex.toLex_le_toLex.mp hx.2
  rcases hlex with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

theorem key_injOn (z : Omega1) :
    Set.InjOn (fun x => key x z) (Set.Iio z) := by
  intro x hx y hy hkey
  change x < z at hx
  change y < z at hy
  have hp :
      (rho x z, nu x (rho x z)) =
        (rho y z, nu y (rho y z)) :=
    toLex.injective hkey
  have hr : rho x z = rho y z := congrArg Prod.fst hp
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hbound : rho x y ≤ rho x z := by
      simpa [hr] using rho_triangle₂ hlt hy
    have hnu := nu_lt hlt hbound
    have hsecond := congrArg Prod.snd hp
    have hsecond' : nu x (rho x z) = nu y (rho x z) := by
      simpa [hr] using hsecond
    exact (Nat.ne_of_lt hnu) hsecond'
  · have hbound : rho y x ≤ rho y z := by
      simpa [hr] using rho_triangle₂ hgt hx
    have hnu := nu_lt hgt hbound
    have hsecond := congrArg Prod.snd hp
    have hsecond' : nu x (rho y z) = nu y (rho y z) := by
      simpa [hr] using hsecond
    exact (Nat.ne_of_lt hnu) hsecond'.symm

theorem key_ne {x y z : Omega1} (hxy : x < y) (hyz : y < z) :
    key x z ≠ key y z := by
  exact fun h => hxy.ne (key_injOn z (hxy.trans hyz) hyz h)

theorem key_eq_of_gt {x y z : Omega1} (hxy : x < y) (hyz : y < z)
    (hgt : key y z < key x z) :
    key x y = key x z := by
  have hlex := Prod.Lex.toLex_lt_toLex.mp hgt
  have hrle : rho y z ≤ rho x z := by
    rcases hlex with h | ⟨h, _⟩
    · exact h.le
    · exact h.le
  have hrlt : rho y z < rho x z := by
    apply lt_of_le_of_ne hrle
    intro heq
    have hbound : rho x y ≤ rho x z := by
      simpa [heq] using rho_triangle₂ hxy hyz
    have hnu := nu_lt hxy hbound
    have hsmall : key x z < key y z := by
      apply Prod.Lex.toLex_lt_toLex.mpr
      exact Or.inr ⟨heq.symm, by simpa [heq] using hnu⟩
    exact (not_lt_of_ge hgt.le) hsmall
  have hrEq : rho x y = rho x z := rho_eq_of_gt hxy hyz hrlt
  simp [key, hrEq]

theorem omega0_le_typeLT_of_infinite (S : Set Omega1) (hS : S.Infinite) :
    Ordinal.omega0 ≤ typeLT S := by
  have hI : Infinite S := Set.infinite_coe_iff.mpr hS
  have hc : Cardinal.aleph0 ≤ #S := Cardinal.aleph0_le_mk_iff.mpr hI
  exact (Cardinal.omega0_le_ord.mpr hc).trans
    (ord_le_type (α := S) (· < ·))

noncomputable def incSeq (S : Set Omega1) (hS : S.Infinite) (n : ℕ) : Omega1 :=
  (Ordinal.enum (α := S) (· < ·)
    ⟨(n : Ordinal),
      (Ordinal.natCast_lt_omega0 n).trans_le
        (omega0_le_typeLT_of_infinite S hS)⟩).1

theorem incSeq_mem (S : Set Omega1) (hS : S.Infinite) (n : ℕ) :
    incSeq S hS n ∈ S := by
  exact (Ordinal.enum (α := S) (· < ·)
    ⟨(n : Ordinal),
      (Ordinal.natCast_lt_omega0 n).trans_le
        (omega0_le_typeLT_of_infinite S hS)⟩).2

theorem incSeq_strictMono (S : Set Omega1) (hS : S.Infinite) :
    StrictMono (incSeq S hS) := by
  intro m n hmn
  apply (show
    (Ordinal.enum (α := S) (· < ·)
      ⟨(m : Ordinal),
        (Ordinal.natCast_lt_omega0 m).trans_le
          (omega0_le_typeLT_of_infinite S hS)⟩).1 <
    (Ordinal.enum (α := S) (· < ·)
      ⟨(n : Ordinal),
        (Ordinal.natCast_lt_omega0 n).trans_le
          (omega0_le_typeLT_of_infinite S hS)⟩).1 from ?_)
  have hsub :
      (Ordinal.enum (α := S) (· < ·)
        ⟨(m : Ordinal),
          (Ordinal.natCast_lt_omega0 m).trans_le
            (omega0_le_typeLT_of_infinite S hS)⟩) <
      (Ordinal.enum (α := S) (· < ·)
        ⟨(n : Ordinal),
          (Ordinal.natCast_lt_omega0 n).trans_le
            (omega0_le_typeLT_of_infinite S hS)⟩) := by
    apply Ordinal.enum_lt_enum.mpr
    change (m : Ordinal) < (n : Ordinal)
    exact_mod_cast hmn
  exact hsub

noncomputable def oVal (x : Omega1) : Ordinal :=
  (x : Ordinal)

theorem oVal_lt_iff {x y : Omega1} : oVal x < oVal y ↔ x < y := by
  simp [oVal]

theorem oVal_le_iff {x y : Omega1} : oVal x ≤ oVal y ↔ x ≤ y := by
  simp [oVal]

noncomputable def seqLimit (u : ℕ → Omega1) : Ordinal :=
  Ordinal.lsub (fun n => oVal (u n))

theorem seq_lt_limit (u : ℕ → Omega1) (n : ℕ) :
    oVal (u n) < seqLimit u := by
  exact Ordinal.lt_lsub _ n

theorem exists_seq_ge_of_lt_limit {u : ℕ → Omega1} {a : Ordinal}
    (h : a < seqLimit u) :
    ∃ n, a ≤ oVal (u n) := by
  exact Ordinal.lt_lsub_iff.mp h

theorem exists_seq_gt_of_lt_limit {u : ℕ → Omega1} (hu : StrictMono u)
    {a : Ordinal} (h : a < seqLimit u) :
    ∃ n, a < oVal (u n) := by
  obtain ⟨n, hn⟩ := exists_seq_ge_of_lt_limit h
  refine ⟨n + 1, hn.trans_lt ?_⟩
  exact oVal_lt_iff.mpr (hu (Nat.lt_succ_self n))

theorem exists_seq_above {u : ℕ → Omega1} (hu : StrictMono u)
    {x : Omega1} (hx : oVal x < seqLimit u) :
    ∃ n, x < u n := by
  obtain ⟨n, hn⟩ := exists_seq_gt_of_lt_limit hu hx
  exact ⟨n, oVal_lt_iff.mp hn⟩

theorem exists_key_gt_on_seq {u : ℕ → Omega1} (hu : StrictMono u)
    {z : Omega1} (huz : ∀ n, u n < z) (q : Key) :
    ∃ n, q < key (u n) z := by
  by_contra h
  have hsub : Set.range u ⊆ {x | x < z ∧ key x z ≤ q} := by
    rintro x ⟨n, rfl⟩
    exact ⟨huz n, le_of_not_gt fun hgt => h ⟨n, hgt⟩⟩
  exact (Set.infinite_range_of_injective hu.injective)
    ((key_small_finite z q).subset hsub)

noncomputable def rhoColor (a b c : Omega1) : Fin 2 :=
  if b < a ∧ c < a then
    if key b a < key c a then 0 else 1
  else if c < b ∧ a < b then
    if key c b < key a b then 0 else 1
  else if a < c ∧ b < c then
    if key a c < key b c then 0 else 1
  else 0

theorem rhoColor_a_zero {a b c : Omega1} (hba : b < a) (hca : c < a)
    (hcol : rhoColor a b c = 0) :
    key b a < key c a := by
  simpa [rhoColor, hba, hca] using hcol

theorem rhoColor_a_one {a b c : Omega1} (hba : b < a) (hca : c < a)
    (hbc : b ≠ c) (hcol : rhoColor a b c = 1) :
    key c a < key b a := by
  have hn : ¬key b a < key c a := by
    simpa [rhoColor, hba, hca] using hcol
  have hne : key b a ≠ key c a := fun heq =>
    hbc (key_injOn a hba hca heq)
  exact lt_of_le_of_ne (le_of_not_gt hn) hne.symm

theorem rhoColor_b_zero {a b c : Omega1} (hcb : c < b) (hab : a < b)
    (hcol : rhoColor a b c = 0) :
    key c b < key a b := by
  have hna : ¬(b < a ∧ c < a) := fun h => (not_lt_of_ge hab.le) h.1
  simpa [rhoColor, hna, hcb, hab] using hcol

theorem rhoColor_b_one {a b c : Omega1} (hcb : c < b) (hab : a < b)
    (hac : c ≠ a) (hcol : rhoColor a b c = 1) :
    key a b < key c b := by
  have hna : ¬(b < a ∧ c < a) := fun h => (not_lt_of_ge hab.le) h.1
  have hn : ¬key c b < key a b := by
    simpa [rhoColor, hna, hcb, hab] using hcol
  have hne : key c b ≠ key a b := fun heq =>
    hac (key_injOn b hcb hab heq)
  exact lt_of_le_of_ne (le_of_not_gt hn) hne.symm

theorem rhoColor_c_zero {a b c : Omega1} (hac : a < c) (hbc : b < c)
    (hcol : rhoColor a b c = 0) :
    key a c < key b c := by
  have hna : ¬(b < a ∧ c < a) := fun h => (not_lt_of_ge hac.le) h.2
  have hnb : ¬(c < b ∧ a < b) := fun h => (not_lt_of_ge hbc.le) h.1
  simpa [rhoColor, hna, hnb, hac, hbc] using hcol

theorem rhoColor_c_one {a b c : Omega1} (hac : a < c) (hbc : b < c)
    (hab : a ≠ b) (hcol : rhoColor a b c = 1) :
    key b c < key a c := by
  have hna : ¬(b < a ∧ c < a) := fun h => (not_lt_of_ge hac.le) h.2
  have hnb : ¬(c < b ∧ a < b) := fun h => (not_lt_of_ge hbc.le) h.1
  have hn : ¬key a c < key b c := by
    simpa [rhoColor, hna, hnb, hac, hbc] using hcol
  have hne : key a c ≠ key b c := fun heq =>
    hab (key_injOn c hac hbc heq)
  exact lt_of_le_of_ne (le_of_not_gt hn) hne.symm

theorem all_seq_below_of_limit_lt {u : ℕ → Omega1} {z : Omega1}
    (h : seqLimit u < oVal z) :
    ∀ n, u n < z := by
  intro n
  exact oVal_lt_iff.mp ((seq_lt_limit u n).trans h)

theorem exists_seq_above_two {u : ℕ → Omega1} (hu : StrictMono u)
    {p q : Ordinal} (hp : p < seqLimit u) (hq : q < seqLimit u) :
    ∃ n, p < oVal (u n) ∧ q < oVal (u n) := by
  obtain ⟨n, hn⟩ := exists_seq_gt_of_lt_limit hu (max_lt hp hq)
  exact ⟨n, (le_max_left _ _).trans_lt hn, (le_max_right _ _).trans_lt hn⟩

theorem no_mono_of_a_limit_gt
    (a b c : ℕ → Omega1) (ha : StrictMono a) (hb : StrictMono b)
    (hc : StrictMono c) (col : Fin 2)
    (hcol : ∀ i j k, rhoColor (a i) (b j) (c k) = col)
    (hba : seqLimit b < seqLimit a) (hca : seqLimit c < seqLimit a) :
    False := by
  obtain ⟨i, hib, hic⟩ := exists_seq_above_two ha hba hca
  have hbBelow : ∀ j, b j < a i :=
    all_seq_below_of_limit_lt hib
  have hcBelow : ∀ k, c k < a i :=
    all_seq_below_of_limit_lt hic
  fin_cases col
  · obtain ⟨j, hj⟩ := exists_key_gt_on_seq hb hbBelow (key (c 0) (a i))
    have hlt := rhoColor_a_zero (hbBelow j) (hcBelow 0) (hcol i j 0)
    exact (not_lt_of_ge hlt.le) hj
  · obtain ⟨k, hk⟩ := exists_key_gt_on_seq hc hcBelow (key (b 0) (a i))
    have hne : b 0 ≠ c k := by
      intro heq
      rw [← heq] at hk
      exact (lt_irrefl _) hk
    have hlt := rhoColor_a_one (hbBelow 0) (hcBelow k)
      hne (hcol i 0 k)
    exact (not_lt_of_ge hlt.le) hk

theorem no_mono_of_b_limit_gt
    (a b c : ℕ → Omega1) (ha : StrictMono a) (hb : StrictMono b)
    (hc : StrictMono c) (col : Fin 2)
    (hcol : ∀ i j k, rhoColor (a i) (b j) (c k) = col)
    (hab : seqLimit a < seqLimit b) (hcb : seqLimit c < seqLimit b) :
    False := by
  obtain ⟨j, hja, hjc⟩ := exists_seq_above_two hb hab hcb
  have haBelow : ∀ i, a i < b j :=
    all_seq_below_of_limit_lt hja
  have hcBelow : ∀ k, c k < b j :=
    all_seq_below_of_limit_lt hjc
  fin_cases col
  · obtain ⟨k, hk⟩ := exists_key_gt_on_seq hc hcBelow (key (a 0) (b j))
    have hlt := rhoColor_b_zero (hcBelow k) (haBelow 0) (hcol 0 j k)
    exact (not_lt_of_ge hlt.le) hk
  · obtain ⟨i, hi⟩ := exists_key_gt_on_seq ha haBelow (key (c 0) (b j))
    have hne : c 0 ≠ a i := by
      intro heq
      rw [← heq] at hi
      exact (lt_irrefl _) hi
    have hlt := rhoColor_b_one (hcBelow 0) (haBelow i)
      hne (hcol i j 0)
    exact (not_lt_of_ge hlt.le) hi

theorem no_mono_of_c_limit_gt
    (a b c : ℕ → Omega1) (ha : StrictMono a) (hb : StrictMono b)
    (hc : StrictMono c) (col : Fin 2)
    (hcol : ∀ i j k, rhoColor (a i) (b j) (c k) = col)
    (hac : seqLimit a < seqLimit c) (hbc : seqLimit b < seqLimit c) :
    False := by
  obtain ⟨k, hka, hkb⟩ := exists_seq_above_two hc hac hbc
  have haBelow : ∀ i, a i < c k :=
    all_seq_below_of_limit_lt hka
  have hbBelow : ∀ j, b j < c k :=
    all_seq_below_of_limit_lt hkb
  fin_cases col
  · obtain ⟨i, hi⟩ := exists_key_gt_on_seq ha haBelow (key (b 0) (c k))
    have hlt := rhoColor_c_zero (haBelow i) (hbBelow 0) (hcol i 0 k)
    exact (not_lt_of_ge hlt.le) hi
  · obtain ⟨j, hj⟩ := exists_key_gt_on_seq hb hbBelow (key (a 0) (c k))
    have hne : a 0 ≠ b j := by
      intro heq
      rw [← heq] at hj
      exact (lt_irrefl _) hj
    have hlt := rhoColor_c_one (haBelow 0) (hbBelow j)
      hne (hcol 0 j k)
    exact (not_lt_of_ge hlt.le) hj

theorem no_mono_of_ab_limits_eq
    (a b c : ℕ → Omega1) (ha : StrictMono a) (hb : StrictMono b)
    (hc : StrictMono c) (col : Fin 2)
    (hcol : ∀ i j k, rhoColor (a i) (b j) (c k) = col)
    (hab : seqLimit a = seqLimit b) (hcLow : seqLimit c < seqLimit a) :
    False := by
  fin_cases col
  · obtain ⟨i, hi⟩ := exists_seq_gt_of_lt_limit ha hcLow
    have hai : oVal (a i) < seqLimit b := by
      simpa [hab] using seq_lt_limit a i
    obtain ⟨j, hij⟩ := exists_seq_above hb hai
    have hcBelowA : ∀ k, c k < a i := all_seq_below_of_limit_lt hi
    have hcBelowB : ∀ k, c k < b j := fun k => (hcBelowA k).trans hij
    obtain ⟨k, hk⟩ := exists_key_gt_on_seq hc hcBelowB (key (a i) (b j))
    have hlt := rhoColor_b_zero (hcBelowB k) hij (hcol i j k)
    exact (not_lt_of_ge hlt.le) hk
  · obtain ⟨j, hj⟩ := exists_seq_gt_of_lt_limit hb (hcLow.trans_eq hab)
    have hbj : oVal (b j) < seqLimit a := by
      simpa using (seq_lt_limit b j).trans_eq hab.symm
    obtain ⟨i, hji⟩ := exists_seq_above ha hbj
    have hcBelowB : ∀ k, c k < b j := all_seq_below_of_limit_lt hj
    have hcBelowA : ∀ k, c k < a i := fun k => (hcBelowB k).trans hji
    obtain ⟨k, hk⟩ := exists_key_gt_on_seq hc hcBelowA (key (b j) (a i))
    have hne : b j ≠ c k := by
      intro heq
      rw [← heq] at hk
      exact (lt_irrefl _) hk
    have hlt := rhoColor_a_one hji (hcBelowA k) hne (hcol i j k)
    exact (not_lt_of_ge hlt.le) hk

theorem no_mono_of_ac_limits_eq
    (a b c : ℕ → Omega1) (ha : StrictMono a) (hb : StrictMono b)
    (hc : StrictMono c) (col : Fin 2)
    (hcol : ∀ i j k, rhoColor (a i) (b j) (c k) = col)
    (hac : seqLimit a = seqLimit c) (hbLow : seqLimit b < seqLimit a) :
    False := by
  fin_cases col
  · obtain ⟨k, hk⟩ := exists_seq_gt_of_lt_limit hc (hbLow.trans_eq hac)
    have hck : oVal (c k) < seqLimit a := by
      simpa using (seq_lt_limit c k).trans_eq hac.symm
    obtain ⟨i, hki⟩ := exists_seq_above ha hck
    have hbBelowC : ∀ j, b j < c k := all_seq_below_of_limit_lt hk
    have hbBelowA : ∀ j, b j < a i := fun j => (hbBelowC j).trans hki
    obtain ⟨j, hj⟩ := exists_key_gt_on_seq hb hbBelowA (key (c k) (a i))
    have hlt := rhoColor_a_zero (hbBelowA j) hki (hcol i j k)
    exact (not_lt_of_ge hlt.le) hj
  · obtain ⟨i, hi⟩ := exists_seq_gt_of_lt_limit ha hbLow
    have hai : oVal (a i) < seqLimit c := by
      simpa [hac] using seq_lt_limit a i
    obtain ⟨k, hik⟩ := exists_seq_above hc hai
    have hbBelowA : ∀ j, b j < a i := all_seq_below_of_limit_lt hi
    have hbBelowC : ∀ j, b j < c k := fun j => (hbBelowA j).trans hik
    obtain ⟨j, hj⟩ := exists_key_gt_on_seq hb hbBelowC (key (a i) (c k))
    have hne : a i ≠ b j := by
      intro heq
      rw [← heq] at hj
      exact (lt_irrefl _) hj
    have hlt := rhoColor_c_one hik (hbBelowC j) hne (hcol i j k)
    exact (not_lt_of_ge hlt.le) hj

theorem no_mono_of_bc_limits_eq
    (a b c : ℕ → Omega1) (ha : StrictMono a) (hb : StrictMono b)
    (hc : StrictMono c) (col : Fin 2)
    (hcol : ∀ i j k, rhoColor (a i) (b j) (c k) = col)
    (hbc : seqLimit b = seqLimit c) (haLow : seqLimit a < seqLimit b) :
    False := by
  fin_cases col
  · obtain ⟨j, hj⟩ := exists_seq_gt_of_lt_limit hb haLow
    have hbj : oVal (b j) < seqLimit c := by
      simpa [hbc] using seq_lt_limit b j
    obtain ⟨k, hjk⟩ := exists_seq_above hc hbj
    have haBelowB : ∀ i, a i < b j := all_seq_below_of_limit_lt hj
    have haBelowC : ∀ i, a i < c k := fun i => (haBelowB i).trans hjk
    obtain ⟨i, hi⟩ := exists_key_gt_on_seq ha haBelowC (key (b j) (c k))
    have hlt := rhoColor_c_zero (haBelowC i) hjk (hcol i j k)
    exact (not_lt_of_ge hlt.le) hi
  · obtain ⟨k, hk⟩ := exists_seq_gt_of_lt_limit hc (haLow.trans_eq hbc)
    have hck : oVal (c k) < seqLimit b := by
      simpa using (seq_lt_limit c k).trans_eq hbc.symm
    obtain ⟨j, hkj⟩ := exists_seq_above hb hck
    have haBelowC : ∀ i, a i < c k := all_seq_below_of_limit_lt hk
    have haBelowB : ∀ i, a i < b j := fun i => (haBelowC i).trans hkj
    obtain ⟨i, hi⟩ := exists_key_gt_on_seq ha haBelowB (key (c k) (b j))
    have hne : c k ≠ a i := by
      intro heq
      rw [← heq] at hi
      exact (lt_irrefl _) hi
    have hlt := rhoColor_b_one hkj (haBelowB i) hne (hcol i j k)
    exact (not_lt_of_ge hlt.le) hi

theorem no_mono_of_all_limits_eq
    (a b c : ℕ → Omega1) (ha : StrictMono a) (hb : StrictMono b)
    (hc : StrictMono c) (col : Fin 2)
    (hcol : ∀ i j k, rhoColor (a i) (b j) (c k) = col)
    (hab : seqLimit a = seqLimit b) (hac : seqLimit a = seqLimit c) :
    False := by
  fin_cases col
  · let Q : Set Key :=
      {q | ∃ i j k, a i < c k ∧ c k < b j ∧ q = key (c k) (b j)}
    have ha0c : oVal (a 0) < seqLimit c := by
      simpa [hac] using seq_lt_limit a 0
    obtain ⟨k₀, hak₀⟩ := exists_seq_above hc ha0c
    have hckb : oVal (c k₀) < seqLimit b := by
      have hck : oVal (c k₀) < seqLimit c := seq_lt_limit c k₀
      simpa [← hab, hac] using hck
    obtain ⟨j₀, hkj₀⟩ := exists_seq_above hb hckb
    have hQ : Q.Nonempty :=
      ⟨key (c k₀) (b j₀), 0, j₀, k₀, hak₀, hkj₀, rfl⟩
    obtain ⟨q, hqQ, hqmin⟩ := wellFounded_lt.has_min Q hQ
    rcases hqQ with ⟨i, j, k, hik, hkj, rfl⟩
    have hbja : oVal (b j) < seqLimit a := by
      have hbj : oVal (b j) < seqLimit b := seq_lt_limit b j
      simpa [hab] using hbj
    obtain ⟨i', hji'⟩ := exists_seq_above ha hbja
    have hai'c : oVal (a i') < seqLimit c := by
      simpa [hac] using seq_lt_limit a i'
    obtain ⟨k', hi'k'⟩ := exists_seq_above hc hai'c
    have hck'b : oVal (c k') < seqLimit b := by
      have hck' : oVal (c k') < seqLimit c := seq_lt_limit c k'
      simpa [← hab, hac] using hck'
    obtain ⟨j', hk'j'⟩ := exists_seq_above hb hck'b
    have h1 : key (b j) (a i') < key (c k) (a i') :=
      rhoColor_a_zero hji' (hkj.trans hji') (hcol i' j k)
    have heq1 : key (c k) (b j) = key (c k) (a i') :=
      key_eq_of_gt hkj hji' h1
    have h2 : key (a i') (c k') < key (b j) (c k') :=
      rhoColor_c_zero hi'k' (hji'.trans hi'k') (hcol i' j k')
    have heq2 : key (b j) (a i') = key (b j) (c k') :=
      key_eq_of_gt hji' hi'k' h2
    have h3 : key (c k') (b j') < key (a i') (b j') :=
      rhoColor_b_zero hk'j' (hi'k'.trans hk'j') (hcol i' j' k')
    have heq3 : key (a i') (c k') = key (a i') (b j') :=
      key_eq_of_gt hi'k' hk'j' h3
    have hdesc : key (c k') (b j') < key (c k) (b j) := by
      calc
        key (c k') (b j') < key (a i') (b j') := h3
        _ = key (a i') (c k') := heq3.symm
        _ < key (b j) (c k') := h2
        _ = key (b j) (a i') := heq2.symm
        _ < key (c k) (a i') := h1
        _ = key (c k) (b j) := heq1.symm
    have hnew : key (c k') (b j') ∈ Q :=
      ⟨i', j', k', hi'k', hk'j', rfl⟩
    exact hqmin _ hnew hdesc
  · let Q : Set Key :=
      {q | ∃ i j k, a i < b j ∧ b j < c k ∧ q = key (b j) (c k)}
    have ha0b : oVal (a 0) < seqLimit b := by
      simpa [hab] using seq_lt_limit a 0
    obtain ⟨j₀, haj₀⟩ := exists_seq_above hb ha0b
    have hbjc : oVal (b j₀) < seqLimit c := by
      have hbj : oVal (b j₀) < seqLimit b := seq_lt_limit b j₀
      simpa [← hab, hac] using hbj
    obtain ⟨k₀, hjk₀⟩ := exists_seq_above hc hbjc
    have hQ : Q.Nonempty :=
      ⟨key (b j₀) (c k₀), 0, j₀, k₀, haj₀, hjk₀, rfl⟩
    obtain ⟨q, hqQ, hqmin⟩ := wellFounded_lt.has_min Q hQ
    rcases hqQ with ⟨i, j, k, hij, hjk, rfl⟩
    have hcka : oVal (c k) < seqLimit a := by
      have hck : oVal (c k) < seqLimit c := seq_lt_limit c k
      simpa [hac] using hck
    obtain ⟨i', hki'⟩ := exists_seq_above ha hcka
    have hai'b : oVal (a i') < seqLimit b := by
      simpa [hab] using seq_lt_limit a i'
    obtain ⟨j', hi'j'⟩ := exists_seq_above hb hai'b
    have hbj'c : oVal (b j') < seqLimit c := by
      have hbj' : oVal (b j') < seqLimit b := seq_lt_limit b j'
      simpa [← hab, hac] using hbj'
    obtain ⟨k', hj'k'⟩ := exists_seq_above hc hbj'c
    have h1 : key (c k) (a i') < key (b j) (a i') :=
      rhoColor_a_one (hjk.trans hki') hki' hjk.ne (hcol i' j k)
    have heq1 : key (b j) (c k) = key (b j) (a i') :=
      key_eq_of_gt hjk hki' h1
    have h2 : key (a i') (b j') < key (c k) (b j') :=
      rhoColor_b_one (hki'.trans hi'j') hi'j' hki'.ne
        (hcol i' j' k)
    have heq2 : key (c k) (a i') = key (c k) (b j') :=
      key_eq_of_gt hki' hi'j' h2
    have h3 : key (b j') (c k') < key (a i') (c k') :=
      rhoColor_c_one (hi'j'.trans hj'k') hj'k' hi'j'.ne
        (hcol i' j' k')
    have heq3 : key (a i') (b j') = key (a i') (c k') :=
      key_eq_of_gt hi'j' hj'k' h3
    have hdesc : key (b j') (c k') < key (b j) (c k) := by
      calc
        key (b j') (c k') < key (a i') (c k') := h3
        _ = key (a i') (b j') := heq3.symm
        _ < key (c k) (b j') := h2
        _ = key (c k) (a i') := heq2.symm
        _ < key (b j) (a i') := h1
        _ = key (b j) (c k) := heq1.symm
    have hnew : key (b j') (c k') ∈ Q :=
      ⟨i', j', k', hi'j', hj'k', rfl⟩
    exact hqmin _ hnew hdesc

theorem no_mono_sequences
    (a b c : ℕ → Omega1) (ha : StrictMono a) (hb : StrictMono b)
    (hc : StrictMono c) (col : Fin 2)
    (hcol : ∀ i j k, rhoColor (a i) (b j) (c k) = col) :
    False := by
  rcases lt_trichotomy (seqLimit a) (seqLimit b) with hab | hab | hba
  · rcases lt_trichotomy (seqLimit b) (seqLimit c) with hbc | hbc | hcb
    · exact no_mono_of_c_limit_gt a b c ha hb hc col hcol
        (hab.trans hbc) hbc
    · exact no_mono_of_bc_limits_eq a b c ha hb hc col hcol hbc hab
    · exact no_mono_of_b_limit_gt a b c ha hb hc col hcol hab hcb
  · rcases lt_trichotomy (seqLimit a) (seqLimit c) with hac | hac | hca
    · exact no_mono_of_c_limit_gt a b c ha hb hc col hcol
        hac (hab.symm ▸ hac)
    · exact no_mono_of_all_limits_eq a b c ha hb hc col hcol hab hac
    · exact no_mono_of_ab_limits_eq a b c ha hb hc col hcol hab hca
  · rcases lt_trichotomy (seqLimit a) (seqLimit c) with hac | hac | hca
    · exact no_mono_of_c_limit_gt a b c ha hb hc col hcol
        hac (hba.trans hac)
    · exact no_mono_of_ac_limits_eq a b c ha hb hc col hcol hac hba
    · exact no_mono_of_a_limit_gt a b c ha hb hc col hcol hba hca

theorem no_infinite_monochromatic_box
    (A B C : Set Omega1) (hA : A.Infinite) (hB : B.Infinite)
    (hC : C.Infinite) :
    ¬ ∃ col : Fin 2,
      ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, rhoColor a b c = col := by
  rintro ⟨col, hcol⟩
  apply no_mono_sequences
    (incSeq A hA) (incSeq B hB) (incSeq C hC)
    (incSeq_strictMono A hA) (incSeq_strictMono B hB)
    (incSeq_strictMono C hC) col
  intro i j k
  exact hcol (incSeq A hA i) (incSeq_mem A hA i)
    (incSeq B hB j) (incSeq_mem B hB j)
    (incSeq C hC k) (incSeq_mem C hC k)

def IsMonochromaticBox {A B C : Type*} (f : A → B → C → Fin 2)
    (A₁ : Set A) (B₁ : Set B) (C₁ : Set C) : Prop :=
  ∃ c : Fin 2, ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ c' ∈ C₁, f a b c' = c

theorem infinite_set_of_mk_eq_aleph0 {α : Type*} {S : Set α}
    (hS : #S = Cardinal.aleph0) : S.Infinite := by
  rw [← Set.infinite_coe_iff, ← Cardinal.aleph0_le_mk_iff]
  simpa [hS]

theorem erdos_1128 : ¬
    ∀ (A B C : Type) (_ : #A = aleph 1) (_ : #B = aleph 1)
      (_ : #C = aleph 1) (f : A → B → C → Fin 2),
      ∃ (A₁ : Set A) (B₁ : Set B) (C₁ : Set C),
        #A₁ = aleph 0 ∧ #B₁ = aleph 0 ∧ #C₁ = aleph 0 ∧
        IsMonochromaticBox f A₁ B₁ C₁ := by
  intro h
  ·
    obtain ⟨A₁, B₁, C₁, hA, hB, hC, hmono⟩ :=
      h Omega1 Omega1 Omega1 omega1_mk omega1_mk omega1_mk rhoColor
    exact no_infinite_monochromatic_box A₁ B₁ C₁
      (infinite_set_of_mk_eq_aleph0 (hA.trans Cardinal.aleph_zero))
      (infinite_set_of_mk_eq_aleph0 (hB.trans Cardinal.aleph_zero))
      (infinite_set_of_mk_eq_aleph0 (hC.trans Cardinal.aleph_zero)) hmono

end

end Erdos1128

#print axioms Erdos1128.erdos_1128
