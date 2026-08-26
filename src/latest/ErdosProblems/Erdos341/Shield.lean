import Mathlib

set_option linter.style.header false

/-!
# Kernel-checked prototype for the finite modulus-49 shield

This file is deliberately independent of `Erdos341.lean`.  The finite
certificate is evaluated directly by the kernel with `decide`.  The infinite
controller is abstracted by the three exact
NOR identities used by the paper.
-/

set_option autoImplicit false
set_option linter.style.setOption false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Erdos341Shield

abbrev R49 := Fin 49

def pResidues : Finset R49 := {7, 14, 28}
def bResidues : Finset R49 := {3, 22, 32, 40, 48}
def dResidues : Finset R49 := {1, 2, 5, 13, 27, 36, 47}

def sumFinset (A B : Finset R49) : Finset R49 :=
  A.biUnion fun a => B.image fun b => a + b

/-- Every non-background, non-controller residue is covered by one of the
three permitted source types. -/
theorem residue_cover :
    ∀ r : R49, r ∉ bResidues → r ∉ pResidues →
      r ∈ sumFinset bResidues bResidues ∨
      r ∈ sumFinset pResidues bResidues ∨
      r ∈ sumFinset dResidues bResidues := by
  decide

/-- No sum involving a background rail or one finite translator can land in
a selected background or controller residue. -/
theorem residue_avoid :
    Disjoint
      (sumFinset bResidues bResidues ∪
       sumFinset pResidues bResidues ∪
       sumFinset dResidues bResidues ∪
       sumFinset dResidues pResidues)
      (bResidues ∪ pResidues) := by
  decide

/-- The only controller-controller pairs that return to a selected residue
are the three intended diagonal gates. -/
theorem controller_diagonals :
    ∀ a ∈ pResidues, ∀ b ∈ pResidues,
      a + b ∈ bResidues ∪ pResidues →
        (a = 7 ∧ b = 7) ∨
        (a = 14 ∧ b = 14) ∨
        (a = 28 ∧ b = 28) := by
  decide

def dNat : Finset ℕ := {1, 2, 5, 13, 27, 36, 47}

def seed : Finset ℕ :=
  {1, 2, 3, 5, 7, 13, 22, 27, 28, 32, 36, 40, 47, 48,
   52, 63, 71, 77, 81, 89, 97}

def residue (n : ℕ) : R49 :=
  ⟨n % 49, Nat.mod_lt n (by omega)⟩

/-- Ordered pair-sum membership.  Equal summands are allowed. -/
def PairSum (X : ℕ → Prop) (n : ℕ) : Prop :=
  ∃ a b : ℕ, X a ∧ X b ∧ a + b = n

/-- The exact abstract interface required of the three Leiss rails.  The six
low-value facts are included only to certify the displayed finite prefix. -/
structure Controller where
  y0 : ℕ → Prop
  y1 : ℕ → Prop
  y2 : ℕ → Prop
  gate01 : ∀ n : ℕ, y1 n ↔ ¬ PairSum y0 n
  gate12 : ∀ n : ℕ, y2 n ↔ ¬ PairSum y1 n
  gate20 : ∀ n : ℕ, y0 (n + 1) ↔ ¬ PairSum y2 n
  y0_zero : y0 0
  y0_one_false : ¬ y0 1
  y1_zero_false : ¬ y1 0
  y1_one : y1 1
  y2_zero : y2 0
  y2_one : y2 1

def Selected (C : Controller) (n : ℕ) : Prop :=
  n ∈ dNat ∨
  residue n ∈ bResidues ∨
  (n % 49 = 7 ∧ C.y0 (n / 49)) ∨
  (n % 49 = 14 ∧ C.y1 (n / 49)) ∨
  (n % 49 = 28 ∧ C.y2 (n / 49))

lemma dNat_le_47 {n : ℕ} (hn : n ∈ dNat) : n ≤ 47 := by
  simp only [dNat, Finset.mem_insert, Finset.mem_singleton] at hn
  omega

lemma selected_positive (C : Controller) {n : ℕ} (hn : Selected C n) : 0 < n := by
  rcases hn with hnD | hnB | hn7 | hn14 | hn28
  · simp only [dNat, Finset.mem_insert, Finset.mem_singleton] at hnD
    omega
  · have hr : (residue n).val = 3 ∨ (residue n).val = 22 ∨
        (residue n).val = 32 ∨ (residue n).val = 40 ∨
        (residue n).val = 48 := by
      simp only [bResidues, Finset.mem_insert, Finset.mem_singleton] at hnB
      rcases hnB with h | h | h | h | h
      · exact Or.inl (congrArg Fin.val h)
      · exact Or.inr (Or.inl (congrArg Fin.val h))
      · exact Or.inr (Or.inr (Or.inl (congrArg Fin.val h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (congrArg Fin.val h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (congrArg Fin.val h))))
    simp only [residue] at hr
    omega
  · omega
  · omega
  · omega

/-- The target formula has exactly the advertised prescribed prefix. -/
theorem seed_prefix (C : Controller) :
    ∀ n : ℕ, n ≤ 97 → (Selected C n ↔ n ∈ seed) := by
  intro n hn
  interval_cases n <;>
    simp [Selected, residue, dNat, bResidues, seed,
      C.y0_zero, C.y0_one_false, C.y1_zero_false, C.y1_one,
      C.y2_zero, C.y2_one]

lemma residue_add_val {a b r : R49} (h : a + b = r) :
    a.val + b.val = 49 * ((a.val + b.val) / 49) + r.val := by
  have hm : (a.val + b.val) % 49 = r.val := by
    have hv := congrArg Fin.val h
    simpa [Fin.add_def] using hv
  nth_rewrite 1 [← Nat.div_add_mod (a.val + b.val) 49]
  omega

lemma residue_carry_le_one (a b : R49) :
    (a.val + b.val) / 49 ≤ 1 := by
  have ha := a.isLt
  have hb := b.isLt
  omega

lemma nat_div_mod_decompose (n : ℕ) :
    n = 49 * (n / 49) + n % 49 := by
  omega

lemma residue_eq_of_add {a b r : R49} (h : a + b = r) :
    (a.val + b.val) % 49 = r.val := by
  have hv := congrArg Fin.val h
  simpa [Fin.add_def] using hv

lemma residue_add (a b : ℕ) :
    residue (a + b) = residue a + residue b := by
  apply Fin.ext
  simp [residue, Fin.add_def, Nat.add_mod]

lemma mem_sumFinset_iff {A B : Finset R49} {r : R49} :
    r ∈ sumFinset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = r := by
  constructor
  · intro hr
    rw [sumFinset, Finset.mem_biUnion] at hr
    rcases hr with ⟨a, ha, hr⟩
    rw [Finset.mem_image] at hr
    rcases hr with ⟨b, hb, hab⟩
    exact ⟨a, ha, b, hb, hab⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [sumFinset, Finset.mem_biUnion]
    exact ⟨a, ha, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩

lemma dResidue_val_mem {d : R49} (hd : d ∈ dResidues) : d.val ∈ dNat := by
  simp only [dResidues, Finset.mem_insert, Finset.mem_singleton] at hd
  simp only [dNat, Finset.mem_insert, Finset.mem_singleton]
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma selected_background (C : Controller) (q : ℕ) {b : R49}
    (hb : b ∈ bResidues) : Selected C (49 * q + b.val) := by
  right
  left
  have heq : residue (49 * q + b.val) = b := by
    apply Fin.ext
    simp [residue]
  simpa [heq] using hb

lemma selected_y0 (C : Controller) (q : ℕ) (hq : C.y0 q) :
    Selected C (49 * q + 7) := by
  right
  right
  left
  constructor
  · omega
  · have hdiv : (49 * q + 7) / 49 = q := by omega
    simpa [hdiv] using hq

lemma selected_y1 (C : Controller) (q : ℕ) (hq : C.y1 q) :
    Selected C (49 * q + 14) := by
  right
  right
  right
  left
  constructor
  · omega
  · have hdiv : (49 * q + 14) / 49 = q := by omega
    simpa [hdiv] using hq

lemma selected_y2 (C : Controller) (q : ℕ) (hq : C.y2 q) :
    Selected C (49 * q + 28) := by
  right
  right
  right
  right
  constructor
  · omega
  · have hdiv : (49 * q + 28) / 49 = q := by omega
    simpa [hdiv] using hq

lemma pairSum_of_BB (C : Controller) {n : ℕ} {a b : R49}
    (hnq : 2 ≤ n / 49) (ha : a ∈ bResidues) (hb : b ∈ bResidues)
    (hab : a + b = residue n) : PairSum (Selected C) n := by
  let c := (a.val + b.val) / 49
  let vq := n / 49 - c
  have hc : c ≤ 1 := residue_carry_le_one a b
  have hvq : c ≤ n / 49 := by omega
  have hab' := residue_add_val hab
  have hab'' : a.val + b.val = 49 * c + n % 49 := by
    simpa [c, residue] using hab'
  have hn' := nat_div_mod_decompose n
  refine ⟨a.val, 49 * vq + b.val, ?_, ?_, ?_⟩
  · simpa using selected_background C 0 ha
  · exact selected_background C vq hb
  · dsimp [vq, c]
    dsimp [c] at hab''
    omega

lemma pairSum_of_DB (C : Controller) {n : ℕ} {d b : R49}
    (hnq : 2 ≤ n / 49) (hd : d ∈ dResidues) (hb : b ∈ bResidues)
    (hdb : d + b = residue n) : PairSum (Selected C) n := by
  let c := (d.val + b.val) / 49
  let vq := n / 49 - c
  have hc : c ≤ 1 := residue_carry_le_one d b
  have hvq : c ≤ n / 49 := by omega
  have hdb' := residue_add_val hdb
  have hdb'' : d.val + b.val = 49 * c + n % 49 := by
    simpa [c, residue] using hdb'
  have hn' := nat_div_mod_decompose n
  refine ⟨d.val, 49 * vq + b.val, ?_, ?_, ?_⟩
  · exact Or.inl (dResidue_val_mem hd)
  · exact selected_background C vq hb
  · dsimp [vq, c]
    dsimp [c] at hdb''
    omega

lemma pairSum_of_PB (C : Controller) {n : ℕ} {p b : R49}
    (hnq : 2 ≤ n / 49) (hp : p ∈ pResidues) (hb : b ∈ bResidues)
    (hpb : p + b = residue n) : PairSum (Selected C) n := by
  have hp_cases : p = 7 ∨ p = 14 ∨ p = 28 := by
    simpa [pResidues] using hp
  rcases hp_cases with rfl | rfl | rfl
  · let c := ((7 : R49).val + b.val) / 49
    let vq := n / 49 - c
    have hc : c ≤ 1 := residue_carry_le_one (7 : R49) b
    have hvq : c ≤ n / 49 := by omega
    have hpb' := residue_add_val hpb
    have hpb'' : (7 : R49).val + b.val = 49 * c + n % 49 := by
      simpa [c, residue] using hpb'
    have hn' := nat_div_mod_decompose n
    refine ⟨7, 49 * vq + b.val, ?_, selected_background C vq hb, ?_⟩
    · simpa using selected_y0 C 0 C.y0_zero
    · dsimp [vq, c]
      dsimp [c] at hpb''
      omega
  · let c := ((14 : R49).val + b.val) / 49
    let vq := n / 49 - 1 - c
    have hc : c ≤ 1 := residue_carry_le_one (14 : R49) b
    have hvq : 1 + c ≤ n / 49 := by omega
    have hpb' := residue_add_val hpb
    have hpb'' : (14 : R49).val + b.val = 49 * c + n % 49 := by
      simpa [c, residue] using hpb'
    have hn' := nat_div_mod_decompose n
    refine ⟨63, 49 * vq + b.val, ?_, selected_background C vq hb, ?_⟩
    · simpa using selected_y1 C 1 C.y1_one
    · dsimp [vq, c]
      dsimp [c] at hpb''
      omega
  · let c := ((28 : R49).val + b.val) / 49
    let vq := n / 49 - c
    have hc : c ≤ 1 := residue_carry_le_one (28 : R49) b
    have hvq : c ≤ n / 49 := by omega
    have hpb' := residue_add_val hpb
    have hpb'' : (28 : R49).val + b.val = 49 * c + n % 49 := by
      simpa [c, residue] using hpb'
    have hn' := nat_div_mod_decompose n
    refine ⟨28, 49 * vq + b.val, ?_, selected_background C vq hb, ?_⟩
    · simpa using selected_y2 C 0 C.y2_zero
    · dsimp [vq, c]
      dsimp [c] at hpb''
      omega

theorem garbage_covered (C : Controller) {n : ℕ} (hn : 97 < n)
    (hB : residue n ∉ bResidues) (hP : residue n ∉ pResidues) :
    PairSum (Selected C) n := by
  have hnq : 2 ≤ n / 49 := by omega
  rcases residue_cover (residue n) hB hP with hBB | hPB | hDB
  · rcases mem_sumFinset_iff.mp hBB with ⟨a, ha, b, hb, hab⟩
    exact pairSum_of_BB C hnq ha hb hab
  · rcases mem_sumFinset_iff.mp hPB with ⟨p, hp, b, hb, hpb⟩
    exact pairSum_of_PB C hnq hp hb hpb
  · rcases mem_sumFinset_iff.mp hDB with ⟨d, hd, b, hb, hdb⟩
    exact pairSum_of_DB C hnq hd hb hdb

lemma dNat_residue {n : ℕ} (hn : n ∈ dNat) : residue n ∈ dResidues := by
  simp only [dNat, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

lemma pResidue_of_mod7 {n : ℕ} (hn : n % 49 = 7) :
    residue n ∈ pResidues := by
  have hr : residue n = (7 : R49) := by
    apply Fin.ext
    simpa [residue] using hn
  rw [hr]
  decide

lemma pResidue_of_mod14 {n : ℕ} (hn : n % 49 = 14) :
    residue n ∈ pResidues := by
  have hr : residue n = (14 : R49) := by
    apply Fin.ext
    simpa [residue] using hn
  rw [hr]
  decide

lemma pResidue_of_mod28 {n : ℕ} (hn : n % 49 = 28) :
    residue n ∈ pResidues := by
  have hr : residue n = (28 : R49) := by
    apply Fin.ext
    simpa [residue] using hn
  rw [hr]
  decide

lemma selected_coarse (C : Controller) {n : ℕ} (hn : Selected C n) :
    n ∈ dNat ∨ residue n ∈ bResidues ∨ residue n ∈ pResidues := by
  rcases hn with hnD | hnB | hn7 | hn14 | hn28
  · exact Or.inl hnD
  · exact Or.inr (Or.inl hnB)
  · exact Or.inr (Or.inr (pResidue_of_mod7 hn7.1))
  · exact Or.inr (Or.inr (pResidue_of_mod14 hn14.1))
  · exact Or.inr (Or.inr (pResidue_of_mod28 hn28.1))

lemma selected_residue_of_large (C : Controller) {n : ℕ} (hn : 47 < n)
    (hS : Selected C n) : residue n ∈ bResidues ∪ pResidues := by
  rcases selected_coarse C hS with hD | hB | hP
  · have := dNat_le_47 hD
    omega
  · exact Finset.mem_union_left _ hB
  · exact Finset.mem_union_right _ hP

lemma avoid_pair_of_sourceSum {a b n : ℕ} (hab : a + b = n)
    (htarget : residue n ∈ bResidues ∪ pResidues)
    (hsource : residue a + residue b ∈
      sumFinset bResidues bResidues ∪
      sumFinset pResidues bResidues ∪
      sumFinset dResidues bResidues ∪
      sumFinset dResidues pResidues) : False := by
  have hrs : residue a + residue b = residue n := by
    rw [← residue_add, hab]
  rw [hrs] at hsource
  exact (Finset.disjoint_left.mp residue_avoid) hsource htarget

lemma avoid_BB {a b n : ℕ} (ha : residue a ∈ bResidues)
    (hb : residue b ∈ bResidues) (hab : a + b = n)
    (ht : residue n ∈ bResidues ∪ pResidues) : False := by
  apply avoid_pair_of_sourceSum hab ht
  simp only [Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl
    (mem_sumFinset_iff.mpr ⟨residue a, ha, residue b, hb, rfl⟩)))

lemma avoid_PB {a b n : ℕ} (ha : residue a ∈ pResidues)
    (hb : residue b ∈ bResidues) (hab : a + b = n)
    (ht : residue n ∈ bResidues ∪ pResidues) : False := by
  apply avoid_pair_of_sourceSum hab ht
  simp only [Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr
    (mem_sumFinset_iff.mpr ⟨residue a, ha, residue b, hb, rfl⟩)))

lemma avoid_DB {a b n : ℕ} (ha : residue a ∈ dResidues)
    (hb : residue b ∈ bResidues) (hab : a + b = n)
    (ht : residue n ∈ bResidues ∪ pResidues) : False := by
  apply avoid_pair_of_sourceSum hab ht
  simp only [Finset.mem_union]
  exact Or.inl (Or.inr
    (mem_sumFinset_iff.mpr ⟨residue a, ha, residue b, hb, rfl⟩))

lemma avoid_DP {a b n : ℕ} (ha : residue a ∈ dResidues)
    (hb : residue b ∈ pResidues) (hab : a + b = n)
    (ht : residue n ∈ bResidues ∪ pResidues) : False := by
  apply avoid_pair_of_sourceSum hab ht
  simp only [Finset.mem_union]
  exact Or.inr
    (mem_sumFinset_iff.mpr ⟨residue a, ha, residue b, hb, rfl⟩)

lemma selected_at_7 (C : Controller) {n : ℕ}
    (hS : Selected C n) (hr : residue n = 7) : C.y0 (n / 49) := by
  have hD : n ∉ dNat := by
    intro h
    have hdr := dNat_residue h
    rw [hr] at hdr
    exact (by decide : (7 : R49) ∉ dResidues) hdr
  have hB : residue n ∉ bResidues := by
    rw [hr]
    decide
  have hm : n % 49 = 7 := by
    have hv := congrArg Fin.val hr
    simpa [residue] using hv
  rcases hS with h | h | h | h | h
  · exact (hD h).elim
  · exact (hB h).elim
  · exact h.2
  · omega
  · omega

lemma selected_at_14 (C : Controller) {n : ℕ}
    (hS : Selected C n) (hr : residue n = 14) : C.y1 (n / 49) := by
  have hD : n ∉ dNat := by
    intro h
    have hdr := dNat_residue h
    rw [hr] at hdr
    exact (by decide : (14 : R49) ∉ dResidues) hdr
  have hB : residue n ∉ bResidues := by
    rw [hr]
    decide
  have hm : n % 49 = 14 := by
    have hv := congrArg Fin.val hr
    simpa [residue] using hv
  rcases hS with h | h | h | h | h
  · exact (hD h).elim
  · exact (hB h).elim
  · omega
  · exact h.2
  · omega

lemma selected_at_28 (C : Controller) {n : ℕ}
    (hS : Selected C n) (hr : residue n = 28) : C.y2 (n / 49) := by
  have hD : n ∉ dNat := by
    intro h
    have hdr := dNat_residue h
    rw [hr] at hdr
    exact (by decide : (28 : R49) ∉ dResidues) hdr
  have hB : residue n ∉ bResidues := by
    rw [hr]
    decide
  have hm : n % 49 = 28 := by
    have hv := congrArg Fin.val hr
    simpa [residue] using hv
  rcases hS with h | h | h | h | h
  · exact (hD h).elim
  · exact (hB h).elim
  · omega
  · omega
  · exact h.2

theorem selected_not_pairSum (C : Controller) {n : ℕ} (hn : 97 < n)
    (hS : Selected C n) : ¬ PairSum (Selected C) n := by
  intro hsum
  rcases hsum with ⟨a, b, haS, hbS, hab⟩
  have haPos := selected_positive C haS
  have hbPos := selected_positive C hbS
  have haLt : a < n := by omega
  have hbLt : b < n := by omega
  have ht := selected_residue_of_large C (by omega) hS
  rcases selected_coarse C haS with haD | haB | haP
  · rcases selected_coarse C hbS with hbD | hbB | hbP
    · have ha47 := dNat_le_47 haD
      have hb47 := dNat_le_47 hbD
      omega
    · exact avoid_DB (dNat_residue haD) hbB hab ht
    · exact avoid_DP (dNat_residue haD) hbP hab ht
  · rcases selected_coarse C hbS with hbD | hbB | hbP
    · exact avoid_DB (dNat_residue hbD) haB (by omega) ht
    · exact avoid_BB haB hbB hab ht
    · exact avoid_PB hbP haB (by omega) ht
  · rcases selected_coarse C hbS with hbD | hbB | hbP
    · exact avoid_DP (dNat_residue hbD) haP (by omega) ht
    · exact avoid_PB haP hbB hab ht
    · have hrs : residue a + residue b = residue n := by
        rw [← residue_add, hab]
      rcases controller_diagonals (residue a) haP (residue b) hbP
          (hrs ▸ ht) with h7 | h14 | h28
      · rcases h7 with ⟨ha7, hb7⟩
        have hn14 : residue n = 14 := by
          rw [← hrs, ha7, hb7]
          decide
        have hya := selected_at_7 C haS ha7
        have hyb := selected_at_7 C hbS hb7
        have hyn := selected_at_14 C hS hn14
        have haDec := nat_div_mod_decompose a
        have hbDec := nat_div_mod_decompose b
        have hnDec := nat_div_mod_decompose n
        have haMod : a % 49 = 7 := by
          have hv := congrArg Fin.val ha7
          simpa [residue] using hv
        have hbMod : b % 49 = 7 := by
          have hv := congrArg Fin.val hb7
          simpa [residue] using hv
        have hnMod : n % 49 = 14 := by
          have hv := congrArg Fin.val hn14
          simpa [residue] using hv
        have hq : a / 49 + b / 49 = n / 49 := by omega
        exact ((C.gate01 (n / 49)).mp hyn) ⟨a / 49, b / 49, hya, hyb, hq⟩
      · rcases h14 with ⟨ha14, hb14⟩
        have hn28 : residue n = 28 := by
          rw [← hrs, ha14, hb14]
          decide
        have hya := selected_at_14 C haS ha14
        have hyb := selected_at_14 C hbS hb14
        have hyn := selected_at_28 C hS hn28
        have haDec := nat_div_mod_decompose a
        have hbDec := nat_div_mod_decompose b
        have hnDec := nat_div_mod_decompose n
        have haMod : a % 49 = 14 := by
          have hv := congrArg Fin.val ha14
          simpa [residue] using hv
        have hbMod : b % 49 = 14 := by
          have hv := congrArg Fin.val hb14
          simpa [residue] using hv
        have hnMod : n % 49 = 28 := by
          have hv := congrArg Fin.val hn28
          simpa [residue] using hv
        have hq : a / 49 + b / 49 = n / 49 := by omega
        exact ((C.gate12 (n / 49)).mp hyn) ⟨a / 49, b / 49, hya, hyb, hq⟩
      · rcases h28 with ⟨ha28, hb28⟩
        have hn7 : residue n = 7 := by
          rw [← hrs, ha28, hb28]
          decide
        have hya := selected_at_28 C haS ha28
        have hyb := selected_at_28 C hbS hb28
        have hyn := selected_at_7 C hS hn7
        have haDec := nat_div_mod_decompose a
        have hbDec := nat_div_mod_decompose b
        have hnDec := nat_div_mod_decompose n
        have haMod : a % 49 = 28 := by
          have hv := congrArg Fin.val ha28
          simpa [residue] using hv
        have hbMod : b % 49 = 28 := by
          have hv := congrArg Fin.val hb28
          simpa [residue] using hv
        have hnMod : n % 49 = 7 := by
          have hv := congrArg Fin.val hn7
          simpa [residue] using hv
        have hq : a / 49 + b / 49 + 1 = n / 49 := by omega
        have hps : PairSum C.y2 (a / 49 + b / 49) :=
          ⟨a / 49, b / 49, hya, hyb, rfl⟩
        have hyshift : C.y0 (a / 49 + b / 49 + 1) := by
          convert hyn using 1
        have hnot := (C.gate20 (a / 49 + b / 49)).mp hyshift
        exact hnot hps

theorem omitted_controller_covered (C : Controller) {n : ℕ} (hn : 97 < n)
    (hP : residue n ∈ pResidues) (hnot : ¬ Selected C n) :
    PairSum (Selected C) n := by
  classical
  have hnq : 2 ≤ n / 49 := by omega
  have hp_cases : residue n = 7 ∨ residue n = 14 ∨ residue n = 28 := by
    simpa [pResidues] using hP
  rcases hp_cases with hr7 | hr14 | hr28
  · have hm : n % 49 = 7 := by
      have hv := congrArg Fin.val hr7
      simpa [residue] using hv
    have hny0 : ¬ C.y0 (n / 49) := by
      intro hy
      apply hnot
      exact Or.inr (Or.inr (Or.inl ⟨hm, hy⟩))
    have hps : PairSum C.y2 (n / 49 - 1) := by
      by_contra hno
      apply hny0
      have hg := (C.gate20 (n / 49 - 1)).mpr hno
      convert hg using 1
      omega
    rcases hps with ⟨a, b, ha, hb, hab⟩
    have hnDec := nat_div_mod_decompose n
    refine ⟨49 * a + 28, 49 * b + 28,
      selected_y2 C a ha, selected_y2 C b hb, ?_⟩
    omega
  · have hm : n % 49 = 14 := by
      have hv := congrArg Fin.val hr14
      simpa [residue] using hv
    have hny1 : ¬ C.y1 (n / 49) := by
      intro hy
      apply hnot
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, hy⟩)))
    have hps : PairSum C.y0 (n / 49) := by
      by_contra hno
      exact hny1 ((C.gate01 (n / 49)).mpr hno)
    rcases hps with ⟨a, b, ha, hb, hab⟩
    have hnDec := nat_div_mod_decompose n
    refine ⟨49 * a + 7, 49 * b + 7,
      selected_y0 C a ha, selected_y0 C b hb, ?_⟩
    omega
  · have hm : n % 49 = 28 := by
      have hv := congrArg Fin.val hr28
      simpa [residue] using hv
    have hny2 : ¬ C.y2 (n / 49) := by
      intro hy
      apply hnot
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hm, hy⟩)))
    have hps : PairSum C.y1 (n / 49) := by
      by_contra hno
      exact hny2 ((C.gate12 (n / 49)).mpr hno)
    rcases hps with ⟨a, b, ha, hb, hab⟩
    have hnDec := nat_div_mod_decompose n
    refine ⟨49 * a + 14, 49 * b + 14,
      selected_y1 C a ha, selected_y1 C b hb, ?_⟩
    omega

theorem omitted_pairSum (C : Controller) {n : ℕ} (hn : 97 < n)
    (hnot : ¬ Selected C n) : PairSum (Selected C) n := by
  by_cases hB : residue n ∈ bResidues
  · exact (hnot (Or.inr (Or.inl hB))).elim
  by_cases hP : residue n ∈ pResidues
  · exact omitted_controller_covered C hn hP hnot
  · exact garbage_covered C hn hB hP

/-- The finite shield turns any exact three-gate controller into an exact
greedy fixed point after the prescribed cutoff. -/
theorem exact_recurrence (C : Controller) :
    ∀ n : ℕ, 97 < n →
      (Selected C n ↔ ¬ PairSum (Selected C) n) := by
  intro n hn
  constructor
  · exact selected_not_pairSum C hn
  · intro hnotSum
    by_contra hnotSelected
    exact hnotSum (omitted_pairSum C hn hnotSelected)

def GreedyExtension (A X : ℕ → Prop) (N : ℕ) : Prop :=
  (∀ n : ℕ, n ≤ N → (X n ↔ A n)) ∧
  (∀ n : ℕ, N < n → (X n ↔ ¬ PairSum X n))

theorem selected_is_greedy (C : Controller) :
    GreedyExtension (fun n => n ∈ seed) (Selected C) 97 := by
  exact ⟨seed_prefix C, exact_recurrence C⟩

#print axioms garbage_covered
#print axioms selected_not_pairSum
#print axioms exact_recurrence
#print axioms selected_is_greedy

#print axioms residue_cover
#print axioms residue_avoid
#print axioms controller_diagonals
#print axioms seed_prefix

end Erdos341Shield
