/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos13.Erdos13Additive

/-!
# Lev's multiple-addition theorem: modular boundary lemmas

This file develops the modular counting argument behind Theorem 1 of
V. F. Lev, *Addendum to "Structure Theorem for Multiple Addition"*, JNT 65
(1997), 96--100.  We work first with normalized subsets of `ℕ`.  The
important difference from the two-set Ruzsa estimate is that the partial
sumset may be wider than the modulus.  Consequently the extra lift in an
occupied residue class is obtained by shifting the *largest* member of that
fiber by the modulus.
-/

open Finset Nat
open scoped Pointwise BigOperators

namespace Erdos186.CFP.LevMultipleAddition

open Erdos13Additive

/-! ## Iterated sumsets -/

/-- A list sumset, with the conventional singleton `{0}` as empty sum. -/
def listSumset {G : Type*} [AddMonoid G] [DecidableEq G] :
    List (Finset G) → Finset G
  | [] => {0}
  | A :: As => A + listSumset As

@[simp] lemma listSumset_nil {G : Type*} [AddMonoid G] [DecidableEq G] :
    listSumset ([] : List (Finset G)) = {0} := rfl

@[simp] lemma listSumset_cons {G : Type*} [AddMonoid G] [DecidableEq G]
    (A : Finset G) (As : List (Finset G)) :
    listSumset (A :: As) = A + listSumset As := rfl

lemma listSumset_nonempty {G : Type*} [AddMonoid G] [DecidableEq G]
    {As : List (Finset G)} (hAs : ∀ A ∈ As, A.Nonempty) :
    (listSumset As).Nonempty := by
  induction As with
  | nil => simp
  | cons A As ih =>
      simp only [listSumset_cons, Finset.add_nonempty]
      exact ⟨hAs A (by simp), ih (fun B hB ↦ hAs B (by simp [hB]))⟩

lemma zero_mem_listSumset {G : Type*} [AddMonoid G] [DecidableEq G]
    {As : List (Finset G)} (hAs : ∀ A ∈ As, 0 ∈ A) :
    0 ∈ listSumset As := by
  induction As with
  | nil => simp
  | cons A As ih =>
      change 0 ∈ A + listSumset As
      simpa only [zero_add] using
        (Finset.add_mem_add (hAs A (by simp))
          (ih (fun B hB ↦ hAs B (by simp [hB]))))

lemma listSumset_append {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (As Bs : List (Finset G)) :
    listSumset (As ++ Bs) = listSumset As + listSumset Bs := by
  induction As with
  | nil =>
      ext x
      simp only [List.nil_append, listSumset_nil, Finset.mem_add,
        Finset.mem_singleton]
      constructor
      · intro hx
        exact ⟨0, rfl, x, hx, by simp⟩
      · rintro ⟨a, rfl, b, hb, rfl⟩
        simpa using hb
  | cons A As ih => simp only [List.cons_append, listSumset_cons, ih, add_assoc]

lemma modImage_listSumset (As : List (Finset ℕ)) (v : ℕ) :
    modImage (listSumset As) v = listSumset (As.map fun A ↦ modImage A v) := by
  induction As with
  | nil =>
      ext c
      simp [listSumset, modImage]
  | cons A As ih =>
      simp only [listSumset_cons, List.map_cons, modImage_add, ih]

/-! ## The upper representative in each residue fiber -/

/-- The greatest member of `S` in a residue represented by `S`. -/
noncomputable def residueMax (S : Finset ℕ) (v : ℕ)
    (c : ↑(modImage S v)) : ℕ :=
  (modFiber S v c.1).max' (modFiber_nonempty c.2)

lemma residueMax_mem (S : Finset ℕ) (v : ℕ) (c : ↑(modImage S v)) :
    residueMax S v c ∈ S := by
  exact (mem_modFiber.mp
    ((modFiber S v c.1).max'_mem (modFiber_nonempty c.2))).1

lemma residueMax_cast (S : Finset ℕ) (v : ℕ) (c : ↑(modImage S v)) :
    ((residueMax S v c : ℕ) : ZMod v) = c.1 := by
  exact (mem_modFiber.mp
    ((modFiber S v c.1).max'_mem (modFiber_nonempty c.2))).2

lemma le_residueMax {S : Finset ℕ} {v z : ℕ} (c : ↑(modImage S v))
    (hz : z ∈ S) (hzc : (z : ZMod v) = c.1) : z ≤ residueMax S v c := by
  apply (modFiber S v c.1).le_max' z
  exact mem_modFiber.mpr ⟨hz, hzc⟩

lemma residueMax_injective (S : Finset ℕ) (v : ℕ) :
    Function.Injective (residueMax S v) := by
  intro c d hcd
  apply Subtype.ext
  rw [← residueMax_cast S v c, ← residueMax_cast S v d, hcd]

/-- Shift the largest member of each occupied residue fiber by `v`. -/
noncomputable def upperShifts (S : Finset ℕ) (v : ℕ) : Finset ℕ :=
  (modImage S v).attach.image fun c ↦ residueMax S v c + v

lemma card_upperShifts (S : Finset ℕ) (v : ℕ) :
    (upperShifts S v).card = (modImage S v).card := by
  rw [upperShifts, card_image_iff.mpr]
  · simp
  · intro c _ d _ hcd
    apply residueMax_injective S v
    change residueMax S v c + v = residueMax S v d + v at hcd
    exact Nat.add_right_cancel hcd

lemma upperShifts_subset_add {S A : Finset ℕ} {v : ℕ} (hvA : v ∈ A) :
    upperShifts S v ⊆ S + A := by
  intro z hz
  simp only [upperShifts, mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  exact Finset.add_mem_add (residueMax_mem S v c) hvA

lemma cast_mem_modImage_of_mem_upperShifts {S : Finset ℕ} {v z : ℕ}
    (hz : z ∈ upperShifts S v) : (z : ZMod v) ∈ modImage S v := by
  simp only [upperShifts, mem_image] at hz
  obtain ⟨c, -, rfl⟩ := hz
  rw [Nat.cast_add, residueMax_cast]
  simpa using c.2

/-- The shifted upper representatives lie strictly above the old set. -/
lemma disjoint_upperShifts (S : Finset ℕ) {v : ℕ} (hv : 0 < v) :
    Disjoint S (upperShifts S v) := by
  rw [Finset.disjoint_left]
  intro z hzS hzU
  simp only [upperShifts, mem_image] at hzU
  obtain ⟨c, -, rfl⟩ := hzU
  have hcast : ((residueMax S v c + v : ℕ) : ZMod v) = c.1 := by
    rw [Nat.cast_add, residueMax_cast]
    simp
  have hle := le_residueMax c hzS hcast
  omega

/-! ## The arbitrary-width modular lift -/

/-- Residues outside `P ∪ D`, represented by their least actual sum. -/
noncomputable def outerReps (S : Finset ℕ) (v : ℕ)
    (P D : Finset (ZMod v)) : Finset ℕ :=
  residueRepsOutside S v (P ∪ D)

lemma card_outerReps (S : Finset ℕ) (v : ℕ) (P D : Finset (ZMod v)) :
    (outerReps S v P D).card = (modImage S v \ (P ∪ D)).card := by
  exact card_residueRepsOutside S v (P ∪ D)

lemma outerReps_subset (S : Finset ℕ) (v : ℕ)
    (P D : Finset (ZMod v)) : outerReps S v P D ⊆ S :=
  residueRepsOutside_subset S v (P ∪ D)

lemma cast_not_mem_union_of_mem_outerReps {S : Finset ℕ} {v : ℕ}
    {P D : Finset (ZMod v)} {z : ℕ} (hz : z ∈ outerReps S v P D) :
    (z : ZMod v) ∉ P ∪ D :=
  cast_not_mem_of_mem_residueRepsOutside hz

/-- Generalized refined lift.  The set `T` may have arbitrary diameter.
The endpoints `0,v` of `A` keep `T` itself and add one new upper lift over
each residue of `T`; the remaining residue classes are counted by least
representatives, except for the distinguished residue set `D`, where all
actual sums are retained. -/
theorem boundary_lift {T A : Finset ℕ} {v : ℕ}
    (hv : 0 < v) (hA0 : 0 ∈ A) (hvA : v ∈ A)
    (D : Finset (ZMod v))
    (hD : D ⊆ modImage (T + A) v)
    (hDP : Disjoint D (modImage T v)) :
    (modImage (T + A) v).card + T.card +
        (sumsOverResidues T A v D).card ≤
      (T + A).card + D.card := by
  let P := modImage T v
  let C := modImage (T + A) v
  let U := upperShifts T v
  let R := outerReps (T + A) v P D
  let F := sumsOverResidues T A v D
  have hTS : T ⊆ T + A := by
    intro t ht
    simpa using Finset.add_mem_add ht hA0
  have hUS : U ⊆ T + A := upperShifts_subset_add hvA
  have hRS : R ⊆ T + A := outerReps_subset (T + A) v P D
  have hFS : F ⊆ T + A := filter_subset _ _
  have hTU : Disjoint T U := disjoint_upperShifts T hv
  have hTR : Disjoint T R := by
    rw [Finset.disjoint_left]
    intro z hzT hzR
    exact (cast_not_mem_union_of_mem_outerReps hzR)
      (mem_union_left _ (mem_modImage.mpr ⟨z, hzT, rfl⟩))
  have hTF : Disjoint T F := by
    rw [Finset.disjoint_left]
    intro z hzT hzF
    exact (Finset.disjoint_left.mp hDP)
      (mem_sumsOverResidues.mp hzF).2
      (mem_modImage.mpr ⟨z, hzT, rfl⟩)
  have hUR : Disjoint U R := by
    rw [Finset.disjoint_left]
    intro z hzU hzR
    exact (cast_not_mem_union_of_mem_outerReps hzR)
      (mem_union_left _ (cast_mem_modImage_of_mem_upperShifts hzU))
  have hUF : Disjoint U F := by
    rw [Finset.disjoint_left]
    intro z hzU hzF
    exact (Finset.disjoint_left.mp hDP)
      (mem_sumsOverResidues.mp hzF).2
      (cast_mem_modImage_of_mem_upperShifts hzU)
  have hRF : Disjoint R F := by
    rw [Finset.disjoint_left]
    intro z hzR hzF
    exact (cast_not_mem_union_of_mem_outerReps hzR)
      (mem_union_right _ (mem_sumsOverResidues.mp hzF).2)
  have hTUR : Disjoint (T ∪ U) R := by
    rw [Finset.disjoint_left]
    intro z hz hzR
    rcases mem_union.mp hz with hzT | hzU
    · exact (Finset.disjoint_left.mp hTR) hzT hzR
    · exact (Finset.disjoint_left.mp hUR) hzU hzR
  have hTURF : Disjoint ((T ∪ U) ∪ R) F := by
    rw [Finset.disjoint_left]
    intro z hz hzF
    rcases mem_union.mp hz with hzTU | hzR
    · rcases mem_union.mp hzTU with hzT | hzU
      · exact (Finset.disjoint_left.mp hTF) hzT hzF
      · exact (Finset.disjoint_left.mp hUF) hzU hzF
    · exact (Finset.disjoint_left.mp hRF) hzR hzF
  have hsub : ((T ∪ U) ∪ R) ∪ F ⊆ T + A :=
    union_subset (union_subset (union_subset hTS hUS) hRS) hFS
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hTURF, card_union_of_disjoint hTUR,
    card_union_of_disjoint hTU, card_upperShifts, card_outerReps] at hc
  change T.card + P.card + (C \ (P ∪ D)).card + F.card ≤
    (T + A).card at hc
  have hPU : P ∪ D ⊆ C := by
    apply union_subset
    · intro p hp
      obtain ⟨t, ht, htp⟩ := mem_modImage.mp hp
      exact mem_modImage.mpr ⟨t, Finset.add_mem_add ht hA0, htp⟩
    · exact hD
  have hPDcard : (P ∪ D).card = P.card + D.card := by
    rw [card_union_of_disjoint hDP.symm]
  have hsplit := card_sdiff_add_card_eq_card hPU
  change (C \ (P ∪ D)).card + (P ∪ D).card = C.card at hsplit
  change C.card + T.card + F.card ≤ (T + A).card + D.card
  omega

/-! ## A telescoping form of multiple Kneser -/

lemma add_singleton_zero {G : Type*} [AddMonoid G] [DecidableEq G]
    (S : Finset G) : S + {0} = S := by
  ext x
  simp only [Finset.mem_add, Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, b, rfl, rfl⟩
    simpa using ha
  · intro hx
    exact ⟨x, hx, 0, rfl, by simp⟩

@[simp] lemma listSumset_singleton {G : Type*} [AddMonoid G] [DecidableEq G]
    (A : Finset G) : listSumset [A] = A := by
  change A + {0} = A
  exact add_singleton_zero A

/-- If `S + H = S`, every member of `H` is an additive stabilizer of `S`. -/
lemma mem_addStab_of_add_eq {G : Type*} [AddCommGroup G] [DecidableEq G]
    {S H : Finset G} (hS : S.Nonempty) (hSH : S + H = S)
    {h : G} (hh : h ∈ H) : h ∈ S.addStab := by
  rw [Finset.mem_addStab' hS]
  intro s hs
  have hmem : s + h ∈ S := by
    rw [← hSH]
    exact Finset.add_mem_add hs hh
  simpa [add_comm] using hmem

/-- Saturation is preserved when an additional summand is adjoined. -/
lemma add_eq_of_right_saturated {G : Type*} [AddCommGroup G] [DecidableEq G]
    (P X H : Finset G) (hX : X + H = X) :
    (P + X) + H = P + X := by
  rw [add_assoc, hX]

/-- Accumulator form of the multiple-set Kneser inequality.  The fixed
set `C` is the completed sum and `H = C.addStab`.  Writing the theorem this
way makes the standard telescoping proof a literal induction on `Xs`. -/
theorem multiple_kneser_acc {G : Type*} [AddCommGroup G] [DecidableEq G]
    {C P : Finset G} (Xs : List (Finset G))
    (hC : C.Nonempty) (hP : P.Nonempty)
    (hPsat : P + C.addStab = P)
    (hXne : ∀ X ∈ Xs, X.Nonempty)
    (hXsat : ∀ X ∈ Xs, X + C.addStab = X)
    (hcomplete : P + listSumset Xs = C) :
    P.card + (Xs.map Finset.card).sum ≤
      C.card + Xs.length * C.addStab.card := by
  induction Xs generalizing P with
  | nil =>
      simp only [List.map_nil, List.sum_nil, add_zero, List.length_nil,
        zero_mul, listSumset_nil] at hcomplete ⊢
      rw [add_singleton_zero] at hcomplete
      subst C
      simp
  | cons X Xs ih =>
      have hX : X.Nonempty := hXne X (by simp)
      have hQ : (P + X).Nonempty := by
        rw [Finset.add_nonempty]
        exact ⟨hP, hX⟩
      have hXsat0 : X + C.addStab = X := hXsat X (by simp)
      have hQsat : (P + X) + C.addStab = P + X :=
        add_eq_of_right_saturated P X C.addStab hXsat0
      have hcomplete' : (P + X) + listSumset Xs = C := by
        simpa only [listSumset_cons, add_assoc] using hcomplete
      have hQstab : (P + X).addStab = C.addStab := by
        apply Subset.antisymm
        · intro g hg
          rw [Finset.mem_addStab' hC]
          intro c hc
          rw [← hcomplete'] at hc ⊢
          obtain ⟨q, hq, r, hr, rfl⟩ := Finset.mem_add.mp hc
          have hgq : g + q ∈ P + X :=
            (Finset.mem_addStab' hQ).mp hg hq
          exact Finset.mem_add.mpr
            ⟨g + q, hgq, r, hr,
              by simpa only [vadd_eq_add] using add_assoc g q r⟩
        · intro g hg
          exact mem_addStab_of_add_eq hQ hQsat hg
      have hk := Finset.add_kneser P X
      change (P + (P + X).addStab).card +
          (X + (P + X).addStab).card ≤
        (P + X).card + (P + X).addStab.card at hk
      rw [hQstab, hPsat, hXsat0] at hk
      have hi := ih (P := P + X) hQ hQsat
        (fun Y hY ↦ hXne Y (by simp [hY]))
        (fun Y hY ↦ hXsat Y (by simp [hY])) hcomplete'
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

/-- Multiple Kneser for a nonempty list, in its final-stabilizer form. -/
theorem multiple_kneser {G : Type*} [AddCommGroup G] [DecidableEq G]
    {X : Finset G} {Xs : List (Finset G)}
    (hX : X.Nonempty) (hXs : ∀ Y ∈ Xs, Y.Nonempty)
    (hstabX : X + (listSumset (X :: Xs)).addStab = X)
    (hstabXs : ∀ Y ∈ Xs,
      Y + (listSumset (X :: Xs)).addStab = Y) :
    X.card + (Xs.map Finset.card).sum ≤
      (listSumset (X :: Xs)).card + Xs.length *
        (listSumset (X :: Xs)).addStab.card := by
  let C := listSumset (X :: Xs)
  have hC : C.Nonempty := by
    apply listSumset_nonempty
    intro Y hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hX
    · exact hXs Y hY
  apply multiple_kneser_acc Xs hC hX hstabX hXs hstabXs
  rfl

/-! ## The missing stabilizer coset -/

/-- Saturating by the stabilizer twice is the same as saturating once. -/
lemma add_addStab_addStab {G : Type*} [AddCommGroup G] [DecidableEq G]
    (C X : Finset G) : (X + C.addStab) + C.addStab = X + C.addStab := by
  rcases C.eq_empty_or_nonempty with rfl | hC
  · simp
  · apply Subset.antisymm
    · intro z hz
      obtain ⟨y, hy, h₂, hh₂, rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨x, hx, h₁, hh₁, rfl⟩ := Finset.mem_add.mp hy
      exact Finset.mem_add.mpr
        ⟨x, hx, h₁ + h₂, addStab_add_mem hC hh₁ hh₂, by abel⟩
    · intro z hz
      obtain ⟨x, hx, h, hh, rfl⟩ := Finset.mem_add.mp hz
      exact Finset.mem_add.mpr
        ⟨x + h, Finset.mem_add.mpr ⟨x, hx, h, hh, rfl⟩,
          0, zero_mem_addStab hC, by simp⟩

/-- In a nonempty iterated sum, saturating every summand by the final
stabilizer is the same as saturating the completed sum once. -/
lemma listSumset_map_addStab {G : Type*} [AddCommGroup G] [DecidableEq G]
    (C X : Finset G) (Xs : List (Finset G)) :
    listSumset ((X :: Xs).map fun Y ↦ Y + C.addStab) =
      listSumset (X :: Xs) + C.addStab := by
  have hHH : C.addStab + C.addStab = C.addStab := by
    simpa [add_comm] using add_addStab_addStab C ({0} : Finset G)
  induction Xs generalizing X with
  | nil =>
      change (X + C.addStab) + {0} = (X + {0}) + C.addStab
      rw [add_singleton_zero, add_singleton_zero]
  | cons Y Ys ih =>
      change (X + C.addStab) +
          listSumset ((Y :: Ys).map fun Z ↦ Z + C.addStab) =
        (X + listSumset (Y :: Ys)) + C.addStab
      rw [ih]
      calc
        (X + C.addStab) + (listSumset (Y :: Ys) + C.addStab) =
            (X + listSumset (Y :: Ys)) +
              (C.addStab + C.addStab) := by ac_rfl
        _ = (X + listSumset (Y :: Ys)) + C.addStab := by rw [hHH]

/-- A summand which is not contained in the final stabilizer creates a
whole stabilizer coset outside the preceding residue sumset. -/
lemma exists_new_stabilizer_coset {G : Type*} [AddCommGroup G] [DecidableEq G]
    {P X C : Finset G} (hP0 : 0 ∈ P) (hX0 : 0 ∈ X)
    (hCeq : C = P + X) (hXnot : ¬ X ⊆ C.addStab) :
    ∃ c ∈ C, c ∉ P + C.addStab := by
  have hC : C.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hCeq]
    simpa using Finset.add_mem_add hP0 hX0
  by_contra hn
  simp only [not_exists, not_and, not_not] at hn
  have hCsub : C ⊆ P + C.addStab := fun c hc ↦ hn c hc
  apply hXnot
  intro x hx
  apply (Finset.mem_addStab' hC).mpr
  intro z hz
  obtain ⟨p, hp, h, hh, hph⟩ := Finset.mem_add.mp (hCsub hz)
  have hpx : p + x ∈ C := by
    rw [hCeq]
    exact Finset.add_mem_add hp hx
  have hsum : (p + x) + h ∈ C := by
    rw [← C.add_addStab]
    exact Finset.add_mem_add hpx hh
  simpa only [vadd_eq_add, ← hph, add_assoc, add_left_comm, add_comm] using hsum

/-- GCD one prevents the modular image from lying in a proper final
stabilizer. -/
lemma modImage_not_subset_addStab_of_gcd_one {S : Finset ℕ} {v : ℕ}
    {C : Finset (ZMod v)} (hC : C.Nonempty)
    (hgcd : S.gcd (fun n ↦ (n : ℤ)) = 1)
    (hproper : C.addStab.card < v) :
    ¬ modImage S v ⊆ C.addStab := by
  have hHpos : 0 < C.addStab.card :=
    card_pos.mpr ⟨0, zero_mem_addStab hC⟩
  have hv : 0 < v := hHpos.trans_le (Nat.le_of_lt hproper)
  letI : NeZero v := ⟨Nat.ne_of_gt hv⟩
  intro hsub
  let K : AddSubgroup (ZMod v) :=
    AddAction.stabilizer (ZMod v) (C : Set (ZMod v))
  have hHK : (C.addStab : Set (ZMod v)) = (K : Set (ZMod v)) :=
    coe_addStab hC
  have hSK : ∀ n ∈ S, (n : ZMod v) ∈ K := by
    intro n hn
    have hnH : (n : ZMod v) ∈ C.addStab :=
      hsub (mem_modImage.mpr ⟨n, hn, rfl⟩)
    have hnHs : (n : ZMod v) ∈ (C.addStab : Set (ZMod v)) := hnH
    rwa [hHK] at hnHs
  have hKtop := stabilizer_eq_top_of_gcd_one hgcd K hSK
  have hHuniv : C.addStab = (Finset.univ : Finset (ZMod v)) := by
    ext x
    simp only [mem_univ, iff_true]
    have hxK : x ∈ K := by rw [hKtop]; trivial
    have hxKs : x ∈ (K : Set (ZMod v)) := hxK
    rw [← hHK] at hxKs
    exact hxKs
  have : C.addStab.card = v := by simp [hHuniv, ZMod.card]
  omega

/-! ## Fiber aggregation -/

/-- The saturation deficit of every summand is paid for by one integer
fiber of the completed sum.  This packages the fiberwise
Cauchy--Davenport induction used in Lev's argument. -/
theorem family_saturation_fiber {v : ℕ} {H : Finset (ZMod v)}
    {A : Finset ℕ} (As : List (Finset ℕ))
    (hH0 : (0 : ZMod v) ∈ H)
    (hHadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H)
    (c : ZMod v) (hc : c ∈ modImage (listSumset (A :: As)) v) :
    (modImage A v).card +
          (As.map fun B ↦ (modImage B v).card).sum +
        (As.length + 1) * H.card ≤
      (modImage A v + H).card +
          (As.map fun B ↦ (modImage B v + H).card).sum +
        (residueFiberSet (listSumset (A :: As)) v (c +ᵥ H)).card +
        As.length := by
  induction As generalizing A c with
  | nil =>
      rw [listSumset_singleton] at hc
      have hcA : c ∈ modImage A v := hc
      have hs := card_modImage_add_card_le_saturation_add_fiber hH0 hcA
      simpa only [List.map_nil, List.sum_nil, List.length_nil, zero_add,
        add_zero, zero_mul, one_mul, listSumset_singleton] using hs
  | cons B Bs ih =>
      have hc' : c ∈ modImage A v + modImage (listSumset (B :: Bs)) v := by
        simpa only [listSumset_cons, modImage_add] using hc
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hc'
      let R := residueFiberSet A v (a +ᵥ H)
      let S := residueFiberSet (listSumset (B :: Bs)) v (b +ᵥ H)
      let F := residueFiberSet (listSumset (A :: B :: Bs)) v (c +ᵥ H)
      have hRne : R.Nonempty := by
        obtain ⟨x, hx, hxa⟩ := mem_modImage.mp ha
        refine ⟨x, mem_residueFiberSet.mpr ⟨hx, ?_⟩⟩
        apply mem_vadd_finset.mpr
        refine ⟨0, hH0, ?_⟩
        simpa [hxa]
      have hSne : S.Nonempty := by
        obtain ⟨x, hx, hxb⟩ := mem_modImage.mp hb
        refine ⟨x, mem_residueFiberSet.mpr ⟨hx, ?_⟩⟩
        apply mem_vadd_finset.mpr
        refine ⟨0, hH0, ?_⟩
        simpa [hxb]
      have hRSF : R + S ⊆ F := by
        have hs := residueFiberSet_add_subset_sumsOverResidues
          (A := A) (B := listSumset (B :: Bs)) hab hHadd
        simpa only [R, S, F, sumsOverResidues, residueFiberSet,
          listSumset_cons] using hs
      have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hRne hSne
      have hsub := card_le_card hRSF
      have hF : R.card + S.card ≤ F.card + 1 := by
        change R.card + S.card - 1 ≤ (R + S).card at hcd
        have hRp : 0 < R.card := card_pos.mpr hRne
        have hSp : 0 < S.card := card_pos.mpr hSne
        omega
      have hA := card_modImage_add_card_le_saturation_add_fiber hH0 ha
      have htail := ih (A := B) (c := b) hb
      simp only [Nat.succ_mul] at htail
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.succ_mul]
      dsimp only [F] at hF
      dsimp only [R, S] at hA htail hF
      change (modImage A v).card +
          ((modImage B v).card +
            (Bs.map fun D ↦ (modImage D v).card).sum) +
          (Bs.length * H.card + H.card + H.card) ≤
        (modImage A v + H).card +
          ((modImage B v + H).card +
            (Bs.map fun D ↦ (modImage D v + H).card).sum) +
          (residueFiberSet (listSumset (A :: B :: Bs)) v
            (c +ᵥ H)).card + (Bs.length + 1)
      omega

lemma length_le_sum_card_modImage (As : List (Finset ℕ)) (v : ℕ)
    (hAs0 : ∀ A ∈ As, 0 ∈ A) :
    As.length ≤ (As.map fun A ↦ (modImage A v).card).sum := by
  induction As with
  | nil => simp
  | cons A As ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have hA : 1 ≤ (modImage A v).card := by
        apply card_pos.mpr
        exact modImage_nonempty ⟨0, hAs0 A (by simp)⟩
      have ih' := ih (fun B hB ↦ hAs0 B (by simp [hB]))
      simpa [add_comm] using Nat.add_le_add hA ih'

/-! ## Lev's normalized multiple-addition theorem -/

/-- Lev's multiple-addition increment in normalized natural-number form.
Every preceding summand contains zero; the final summand `A` contains both
endpoints `0,L` and has integer gcd one.  The quantities on the right are
exactly the numbers of residue classes modulo `L` represented by the
summands. -/
theorem lev1997_increment_normalized {A : Finset ℕ}
    (As : List (Finset ℕ)) {L : ℕ}
    (hL : 0 < L) (hA0 : 0 ∈ A) (hAL : L ∈ A)
    (hgcd : A.gcd (fun n ↦ (n : ℤ)) = 1)
    (hAs0 : ∀ B ∈ As, 0 ∈ B) :
    (listSumset As).card +
        min L ((modImage A L).card +
          (As.map fun B ↦ (modImage B L).card).sum -
          (As.length + 1) + 1) ≤
      (listSumset As + A).card := by
  letI : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let T := listSumset As
  let X := modImage A L
  let Xs := As.map fun B ↦ modImage B L
  let P := modImage T L
  let C := P + X
  let H := C.addStab
  have hT0 : 0 ∈ T := zero_mem_listSumset hAs0
  have hP0 : (0 : ZMod L) ∈ P := zero_mem_modImage hT0
  have hX0 : (0 : ZMod L) ∈ X := zero_mem_modImage hA0
  have hC0 : (0 : ZMod L) ∈ C := by
    change (0 : ZMod L) ∈ P + X
    simpa using Finset.add_mem_add hP0 hX0
  have hCne : C.Nonempty := ⟨0, hC0⟩
  have hH0 : (0 : ZMod L) ∈ H := zero_mem_addStab hCne
  have hHadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    exact addStab_add_mem hCne hx hy
  have hHneg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    exact addStab_neg_mem hCne hx
  have hCimage : C = modImage (T + A) L := by
    change modImage T L + modImage A L = modImage (T + A) L
    exact (modImage_add T A L).symm
  have hHcard : H.card ≤ L := by
    calc
      H.card ≤ (Finset.univ : Finset (ZMod L)).card :=
        card_le_card (subset_univ H)
      _ = L := by simp [ZMod.card]
  by_cases hwhole : H.card = L
  · have hHsubC : H ⊆ C := by
      intro h hh
      have hz : (0 : ZMod L) + h ∈ C + H := Finset.add_mem_add hC0 hh
      change (0 : ZMod L) + h ∈ C + C.addStab at hz
      rw [C.add_addStab] at hz
      simpa using hz
    have hCcardle : C.card ≤ L := by
      calc
        C.card ≤ (Finset.univ : Finset (ZMod L)).card :=
          card_le_card (subset_univ C)
        _ = L := by simp [ZMod.card]
    have hCcard : C.card = L := by
      have hc := card_le_card hHsubC
      omega
    have hb := boundary_lift (T := T) (A := A) hL hA0 hAL
      (∅ : Finset (ZMod L)) (by simp) (by simp)
    rw [← hCimage] at hb
    simp only [card_empty, add_zero] at hb
    have hm := min_le_left L
      ((modImage A L).card +
        (As.map fun B ↦ (modImage B L).card).sum -
        (As.length + 1) + 1)
    change T.card + _ ≤ (T + A).card
    omega
  · have hHlt : H.card < L := by omega
    have hXnot : ¬ X ⊆ H := by
      exact modImage_not_subset_addStab_of_gcd_one hCne hgcd hHlt
    obtain ⟨c, hcC, hcPH⟩ :=
      exists_new_stabilizer_coset hP0 hX0 (C := C) rfl hXnot
    let D := c +ᵥ H
    have hDsubC : D ⊆ C := by
      have hs : c +ᵥ H ⊆ C + H := vadd_finset_subset_add hcC
      change D ⊆ C + C.addStab at hs
      rw [C.add_addStab] at hs
      exact hs
    have hDdisjPH : Disjoint D (P + H) :=
      disjoint_vadd_add_of_not_mem hHadd hHneg hcPH
    have hPsubPH : P ⊆ P + H := by
      intro p hp
      exact Finset.mem_add.mpr ⟨p, hp, 0, hH0, by simp⟩
    have hDdisjP : Disjoint D P := hDdisjPH.mono_right hPsubPH
    have hDcard : D.card = H.card := card_vadd_finset c H
    have hb := boundary_lift (T := T) (A := A) hL hA0 hAL D
      (by rwa [← hCimage]) hDdisjP
    rw [← hCimage, hDcard] at hb
    change C.card + T.card +
        (residueFiberSet (T + A) L D).card ≤
      (T + A).card + H.card at hb
    have hsumImage : modImage (listSumset (A :: As)) L = C := by
      rw [listSumset_cons, modImage_add]
      change X + P = P + X
      exact add_comm X P
    have hcFamily : c ∈ modImage (listSumset (A :: As)) L := by
      rwa [hsumImage]
    have hfam := family_saturation_fiber As hH0 hHadd c hcFamily
    have hsumNat : listSumset (A :: As) = T + A := by
      change A + T = T + A
      exact add_comm A T
    rw [hsumNat] at hfam
    change X.card +
          (As.map fun B ↦ (modImage B L).card).sum +
          (As.length + 1) * H.card ≤
        (X + H).card +
          (As.map fun B ↦ (modImage B L + H).card).sum +
          (residueFiberSet (T + A) L D).card + As.length at hfam
    have hXne : X.Nonempty := modImage_nonempty ⟨0, hA0⟩
    have hY0ne : (X + H).Nonempty := by
      rw [Finset.add_nonempty]
      exact ⟨hXne, ⟨0, hH0⟩⟩
    have hYsne : ∀ Y ∈ Xs.map (fun Z ↦ Z + H), Y.Nonempty := by
      intro Y hY
      simp only [Xs, List.map_map, List.mem_map, Function.comp_apply] at hY
      obtain ⟨B, hB, rfl⟩ := hY
      rw [Finset.add_nonempty]
      exact ⟨modImage_nonempty ⟨0, hAs0 B (by simpa using hB)⟩, ⟨0, hH0⟩⟩
    have hY0sat : (X + H) + H = X + H := by
      exact add_addStab_addStab C X
    have hYssat : ∀ Y ∈ Xs.map (fun Z ↦ Z + H), Y + H = Y := by
      intro Y hY
      simp only [Xs, List.map_map, List.mem_map, Function.comp_apply] at hY
      obtain ⟨B, -, rfl⟩ := hY
      exact add_addStab_addStab C (modImage B L)
    have hXsSum : listSumset Xs = P := by
      simpa only [Xs, P, T] using (modImage_listSumset As L).symm
    have hOrig : listSumset (X :: Xs) = C := by
      rw [listSumset_cons]
      rw [hXsSum]
      change X + P = P + X
      exact add_comm X P
    have hComplete : (X + H) +
        listSumset (Xs.map fun Z ↦ Z + H) = C := by
      calc
        (X + H) + listSumset (Xs.map fun Z ↦ Z + H) =
            listSumset ((X :: Xs).map fun Z ↦ Z + H) := rfl
        _ = listSumset (X :: Xs) + H := listSumset_map_addStab C X Xs
        _ = C + H := by rw [hOrig]
        _ = C := C.add_addStab
    have hk := multiple_kneser_acc
      (C := C) (P := X + H) (Xs.map fun Z ↦ Z + H)
      hCne hY0ne hY0sat hYsne hYssat hComplete
    have hk' : (X + H).card +
        (As.map fun B ↦ (modImage B L + H).card).sum ≤
      C.card + As.length * H.card := by
      simpa only [Xs, List.map_map, List.length_map,
        Function.comp_apply, Function.comp_def, H] using hk
    have hnpos : As.length + 1 ≤ X.card +
        (As.map fun B ↦ (modImage B L).card).sum := by
      have hXcard : 1 ≤ X.card := card_pos.mpr hXne
      have hcards := length_le_sum_card_modImage As L hAs0
      simpa [add_comm] using Nat.add_le_add hXcard hcards
    have hm := min_le_right L
      ((modImage A L).card +
        (As.map fun B ↦ (modImage B L).card).sum -
        (As.length + 1) + 1)
    have hdecomp :
        ((modImage A L).card +
            (As.map fun B ↦ (modImage B L).card).sum -
            (As.length + 1) + 1) + As.length =
          (modImage A L).card +
            (As.map fun B ↦ (modImage B L).card).sum := by
      have hcancel := Nat.sub_add_cancel hnpos
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcancel
    have hexcess :
        ((modImage A L).card +
            (As.map fun B ↦ (modImage B L).card).sum -
            (As.length + 1) + 1) + H.card ≤
          C.card + (residueFiberSet (T + A) L D).card := by
      simp only [Nat.add_mul, one_mul] at hfam
      have hfam' :
          ((((modImage A L).card +
                (As.map fun B ↦ (modImage B L).card).sum -
                (As.length + 1) + 1) + H.card) +
              As.length * H.card) + As.length ≤
            ((X + H).card +
              (As.map fun B ↦ (modImage B L + H).card).sum +
              (residueFiberSet (T + A) L D).card) + As.length := by
        calc
          ((((modImage A L).card +
                  (As.map fun B ↦ (modImage B L).card).sum -
                  (As.length + 1) + 1) + H.card) +
                As.length * H.card) + As.length =
              (((modImage A L).card +
                  (As.map fun B ↦ (modImage B L).card).sum -
                  (As.length + 1) + 1) + As.length) +
                (As.length * H.card + H.card) := by ac_rfl
          _ = ((modImage A L).card +
                  (As.map fun B ↦ (modImage B L).card).sum) +
                (As.length * H.card + H.card) := by rw [hdecomp]
          _ ≤ ((X + H).card +
                  (As.map fun B ↦ (modImage B L + H).card).sum +
                  (residueFiberSet (T + A) L D).card) + As.length := hfam
      have hdrop :
          (((modImage A L).card +
                (As.map fun B ↦ (modImage B L).card).sum -
                (As.length + 1) + 1) + H.card) +
              As.length * H.card ≤
            (X + H).card +
              (As.map fun B ↦ (modImage B L + H).card).sum +
              (residueFiberSet (T + A) L D).card :=
        Nat.le_of_add_le_add_right hfam'
      have hkF := Nat.add_le_add_right hk'
        (residueFiberSet (T + A) L D).card
      have hcombined :
          (((modImage A L).card +
                (As.map fun B ↦ (modImage B L).card).sum -
                (As.length + 1) + 1) + H.card) +
              As.length * H.card ≤
            (C.card + (residueFiberSet (T + A) L D).card) +
              As.length * H.card := by
        exact hdrop.trans (by
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hkF)
      exact Nat.le_of_add_le_add_right hcombined
    have hraw : T.card +
        ((modImage A L).card +
          (As.map fun B ↦ (modImage B L).card).sum -
          (As.length + 1) + 1) ≤ (T + A).card := by
      have h₁ := Nat.add_le_add_left hexcess T.card
      have h₂ :
          (T.card +
              ((modImage A L).card +
                (As.map fun B ↦ (modImage B L).card).sum -
                (As.length + 1) + 1)) + H.card ≤
            (T + A).card + H.card := by
        exact (by
          have := h₁.trans (by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb)
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
      exact Nat.le_of_add_le_add_right h₂
    change T.card + _ ≤ (T + A).card
    exact (Nat.add_le_add_left hm T.card).trans hraw

/-- Short public name for the normalized Lev increment. -/
theorem lev1997_increment {A : Finset ℕ}
    (As : List (Finset ℕ)) {L : ℕ}
    (hL : 0 < L) (hA0 : 0 ∈ A) (hAL : L ∈ A)
    (hgcd : A.gcd (fun n ↦ (n : ℤ)) = 1)
    (hAs0 : ∀ B ∈ As, 0 ∈ B) :
    (listSumset As).card +
        min L ((modImage A L).card +
          (As.map fun B ↦ (modImage B L).card).sum -
          (As.length + 1) + 1) ≤
      (listSumset As + A).card :=
  lev1997_increment_normalized As hL hA0 hAL hgcd hAs0

end Erdos186.CFP.LevMultipleAddition
