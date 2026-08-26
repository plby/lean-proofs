/-
Copyright (c) 2019 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Jesse Han, Floris van Doorn
Lean 4 port: Ian Klatzco, Claude
-/
-- Lean 4 port of src/aleph_one.lean lines 1-450 — Task 19a (part 1 of 2)

import ErdosProblems.Erdos501.Flypitch4.BvmExtras2

set_option relaxedAutoImplicit true

open scoped Flypitch
open Lattice

universe u v

-- ============================================================
-- src/aleph_one.lean:5-241: namespace PSet
-- ============================================================

namespace PSet

section
open Cardinal

-- src/aleph_one.lean:10
/-- Foundation / regularity for pSet: every nonempty set has an ∈-minimal element. -/
lemma regularity (x : PSet.{u}) (H_nonempty : ¬ Equiv x (∅ : PSet.{u})) :
    ∃ (y : PSet) (_Hy : y ∈ x), ∀ z ∈ x, z ∉ y := by
  obtain ⟨y, Hy, Hmin⟩ := well_founded x H_nonempty
  exact ⟨y, Hy, Hmin⟩

-- src/aleph_one.lean:18
noncomputable def aleph_one : PSet := card_ex (Cardinal.aleph 1)

-- src/aleph_one.lean:20
lemma aleph_one_Ord : Ord aleph_one := Ord_mk (Cardinal.aleph 1).ord

-- src/aleph_one.lean:22
def aleph_one_weak_Ord_spec (x : PSet.{u}) : Prop :=
  Ord x ∧ (∀ y : PSet.{u}, Ord y ∧ ¬ injects_into y PSet.omega → x ⊆ y)

-- src/aleph_one.lean:25
def epsilon_trichotomy (x : PSet.{u}) : Prop :=
  ∀ (y : PSet), y ∈ x → ∀ (z : PSet), z ∈ x → Equiv y z ∨ y ∈ z ∨ z ∈ y

-- src/aleph_one.lean:27
lemma epsilon_trichotomy_of_Ord {x : PSet.{u}} (H_ord : Ord x) : epsilon_trichotomy x :=
  H_ord.left.left

-- src/aleph_one.lean:30
lemma epsilon_trichotomy_of_Ord' {x : PSet.{u}} (H_ord : Ord x) :
    ∀ {y} (_Hy : y ∈ x) {z} (_Hz : z ∈ x), Equiv y z ∨ y ∈ z ∨ z ∈ y := by
  intro y Hy z Hz
  exact epsilon_trichotomy_of_Ord H_ord y Hy z Hz

-- src/aleph_one.lean:33
lemma is_transitive_of_mem_Ord {x : PSet.{u}} (H_ord : Ord x) : is_transitive x := H_ord.right

-- src/aleph_one.lean:35
lemma mem_of_mem_subset' {x y z : PSet.{u}} (H_sub : y ⊆ z) (H_mem : x ∈ y) : x ∈ z :=
  (subset_iff_all_mem.mp H_sub) x H_mem

-- src/aleph_one.lean:38
lemma mem_of_mem_Ord' {x y z : PSet.{u}} (H_ord : Ord z) (H_mem₁ : x ∈ y) (H_mem₂ : y ∈ z) :
    x ∈ z :=
  mem_of_mem_subset' (is_transitive_of_mem_Ord H_ord y H_mem₂) H_mem₁

-- src/aleph_one.lean:44
lemma subset_of_mem_Ord' {x z : PSet.{u}} (H_ord : Ord z) (H_mem₁ : x ∈ z) : x ⊆ z :=
  is_transitive_of_mem_Ord H_ord x H_mem₁

-- src/aleph_one.lean:47
lemma Ord_of_mem_Ord' {x z : PSet.{u}} (H_mem : x ∈ z) (H : Ord z) : Ord x := by
  refine ⟨⟨?_, is_epsilon_well_founded x⟩, transitive_of_mem_Ord x z H H_mem⟩
  intro y₁ Hy₁ y₂ Hy₂
  apply epsilon_trichotomy_of_Ord H
  · exact mem_of_mem_Ord' H Hy₁ H_mem
  · exact mem_of_mem_Ord' H Hy₂ H_mem

-- src/aleph_one.lean:56
/-- Complement: elements of x not in y -/
def pSet_compl (x y : PSet.{u}) : PSet.{u} := PSet.sep (fun z => z ∉ y) x

-- src/aleph_one.lean:58
lemma mem_pSet_compl_iff {x y z : PSet.{u}} : z ∈ pSet_compl x y ↔ z ∈ x ∧ z ∉ y :=
  mem_sep_iff (P_ext_neg P_ext_mem_left)

-- src/aleph_one.lean:61
@[reducible] def non_empty (x : PSet.{u}) : Prop := ¬ (Equiv x (∅ : PSet.{u}))

-- src/aleph_one.lean:63
lemma equiv_unfold' {x y : PSet.{u}} :
    Equiv x y ↔ (∀ z, z ∈ x → z ∈ y) ∧ (∀ z, z ∈ y → z ∈ x) := by
  rw [ext_iff]
  exact ⟨fun h => ⟨fun z hz => (h z).mp hz, fun z hz => (h z).mpr hz⟩,
         fun ⟨h₁, h₂⟩ z => ⟨h₁ z, h₂ z⟩⟩

-- src/aleph_one.lean:66
lemma nonempty_iff_exists_mem {x : PSet.{u}} : non_empty x ↔ ∃ y, y ∈ x := by
  constructor
  · exact exists_mem_of_nonempty
  · intro ⟨y, Hy⟩ H_eq
    exact PSet.notMem_empty y ((ext_iff.mp H_eq y).mp Hy)

-- src/aleph_one.lean:73
lemma nonempty_compl_of_ne {x y : PSet.{u}} (H_ne : ¬ Equiv x y) :
    (non_empty $ pSet_compl x y) ∨ (non_empty $ pSet_compl y x) := by
  simp only [non_empty, nonempty_iff_exists_mem, mem_pSet_compl_iff]
  rw [equiv_unfold', not_and_or] at H_ne
  rcases H_ne with H_ne | H_ne
  · push_neg at H_ne
    obtain ⟨z, Hz₁, Hz₂⟩ := H_ne
    exact Or.inl ⟨z, Hz₁, Hz₂⟩
  · push_neg at H_ne
    obtain ⟨z, Hz₁, Hz₂⟩ := H_ne
    exact Or.inr ⟨z, Hz₁, Hz₂⟩

-- src/aleph_one.lean:80
lemma compl_empty_of_subset {x y : PSet.{u}} (H_sub : x ⊆ y) :
    Equiv (pSet_compl x y) (∅ : PSet.{u}) := by
  classical
  by_contra H_contra
  change non_empty _ at H_contra
  obtain ⟨z, Hz⟩ := nonempty_iff_exists_mem.mp H_contra
  rw [mem_pSet_compl_iff] at Hz
  exact Hz.2 (mem_of_mem_subset' H_sub Hz.1)

-- src/aleph_one.lean:89
/-- Binary intersection -/
def pSet_binary_inter (x y : PSet.{u}) : PSet.{u} := PSet.sep (fun z => z ∈ y) x

-- src/aleph_one.lean:91
lemma mem_pSet_binary_inter_iff {x y z : PSet.{u}} :
    z ∈ pSet_binary_inter x y ↔ (z ∈ x ∧ z ∈ y) :=
  mem_sep_iff P_ext_mem_left

-- src/aleph_one.lean:94
lemma pSet_binary_inter_subset {x y : PSet.{u}} :
    pSet_binary_inter x y ⊆ x ∧ pSet_binary_inter x y ⊆ y := by
  refine ⟨?_, ?_⟩
  · rw [subset_iff_all_mem]; intro z Hz; exact (mem_pSet_binary_inter_iff.mp Hz).1
  · rw [subset_iff_all_mem]; intro z Hz; exact (mem_pSet_binary_inter_iff.mp Hz).2

-- src/aleph_one.lean:97
lemma Ord_pSet_binary_inter {x y : PSet.{u}} (H₁ : Ord x) (H₂ : Ord y) :
    Ord (pSet_binary_inter x y) := by
  refine ⟨⟨?_, is_epsilon_well_founded _⟩, ?_⟩
  · intro w Hw_mem z Hz_mem
    rw [mem_pSet_binary_inter_iff] at Hw_mem Hz_mem
    exact epsilon_trichotomy_of_Ord H₁ w Hw_mem.1 z Hz_mem.1
  · intro z H_mem
    rw [mem_pSet_binary_inter_iff] at H_mem
    rw [subset_iff_all_mem]; intro w Hw
    rw [mem_pSet_binary_inter_iff]
    exact ⟨mem_of_mem_Ord' H₁ Hw H_mem.1, mem_of_mem_Ord' H₂ Hw H_mem.2⟩

-- src/aleph_one.lean:109
lemma Ord.lt_of_ne_and_le {x y : PSet.{u}} (H₁ : Ord x) (H₂ : Ord y)
    (H_ne : ¬ (Equiv x y)) (H_le : x ⊆ y) : x ∈ y := by
  -- The complement y \ x is nonempty since x ≠ y but x ⊆ y
  have H_compl_nonempty : non_empty (pSet_compl y x) := by
    -- nonempty_compl_of_ne H_ne : non_empty (compl x y) ∨ non_empty (compl y x)
    rcases nonempty_compl_of_ne H_ne with h | h
    · -- non_empty (pSet_compl x y), i.e., x \ y is nonempty
      -- But x ⊆ y, so x \ y is empty → contradiction
      exfalso
      obtain ⟨z, hz⟩ := nonempty_iff_exists_mem.mp h
      rw [mem_pSet_compl_iff] at hz
      exact hz.2 (mem_of_mem_subset' H_le hz.1)
    · exact h
  -- Find an ∈-minimal element z of y \ x
  obtain ⟨z, Hz₁, Hz_min⟩ := regularity _ H_compl_nonempty
  obtain ⟨Hz_mem_y, Hz_not_mem_x⟩ := mem_pSet_compl_iff.mp Hz₁
  -- Show Equiv x z, then x ∈ z ∈ y implies x ∈ y? No: Equiv x z means x ∈ y since z ∈ y
  suffices H_eq : Equiv x z by exact (PSet.Mem.congr_left H_eq).mpr Hz_mem_y
  rw [ext_iff]
  intro a
  constructor
  · intro Ha_mem_x
    -- a ∈ x ⊆ y, z ∈ y: trichotomy of a and z as members of y
    rcases epsilon_trichotomy_of_Ord' H₂ (mem_of_mem_subset' H_le Ha_mem_x) Hz_mem_y with h | h | h
    · -- Equiv a z: but a ∈ x and z ∉ x, so a ∉ x, contradiction
      -- Equiv a z means: a ∈ x ↔ z ∈ x (by Mem.congr_left h)
      have : a ∈ x ↔ z ∈ x := ⟨fun H => (PSet.Mem.congr_left h).mp H,
                                  fun H => (PSet.Mem.congr_left h).mpr H⟩
      exact absurd (this.mp Ha_mem_x) Hz_not_mem_x
    · exact h
    · -- z ∈ a ∈ x, so z ∈ x by transitivity: contradiction
      exact absurd (mem_of_mem_Ord' H₁ h Ha_mem_x) Hz_not_mem_x
  · intro Ha_mem_z
    -- a ∈ z ∈ y, so a ∈ y. If a ∉ x, then a ∈ y \ x, but z is ∈-minimal there
    by_contra Ha_not_mem_x
    have Ha_mem_yx : a ∈ pSet_compl y x :=
      mem_pSet_compl_iff.mpr ⟨mem_of_mem_Ord' H₂ Ha_mem_z Hz_mem_y, Ha_not_mem_x⟩
    exact Hz_min a Ha_mem_yx Ha_mem_z

-- src/aleph_one.lean:137
lemma Ord.le_or_le {x y : PSet.{u}} (H₁ : Ord x) (H₂ : Ord y) : x ⊆ y ∨ y ⊆ x := by
  let w := pSet_binary_inter x y
  have w_Ord : Ord w := Ord_pSet_binary_inter H₁ H₂
  have hw : Equiv w x ∨ Equiv w y := by
    classical
    by_contra H_contra
    push_neg at H_contra
    obtain ⟨H_ne₁, H_ne₂⟩ := H_contra
    -- w ∈ x and w ∈ y
    have Hwx : w ∈ x := Ord.lt_of_ne_and_le w_Ord H₁ H_ne₁ (pSet_binary_inter_subset.1)
    have Hwy : w ∈ y := Ord.lt_of_ne_and_le w_Ord H₂ H_ne₂ (pSet_binary_inter_subset.2)
    -- w ∈ w
    have Hww : w ∈ w := mem_pSet_binary_inter_iff.mpr ⟨Hwx, Hwy⟩
    exact PSet.mem_irrefl w Hww
  rcases hw with h | h
  · left
    exact subset_iff_all_mem.mpr (fun z hz =>
      (mem_pSet_binary_inter_iff.mp ((ext_iff.mp h.symm z).mp hz)).2)
  · right
    exact subset_iff_all_mem.mpr (fun z hz =>
      (mem_pSet_binary_inter_iff.mp ((ext_iff.mp h.symm z).mp hz)).1)

-- src/aleph_one.lean:155
lemma pSet_equiv_comm {x y : PSet.{u}} : Equiv x y ↔ Equiv y x :=
  ⟨Equiv.symm, Equiv.symm⟩

-- src/aleph_one.lean:158
lemma Ord.trichotomy {x y : PSet.{u}} (H₁ : Ord x) (H₂ : Ord y) :
    Equiv x y ∨ x ∈ y ∨ y ∈ x := by
  classical
  rcases Ord.le_or_le H₁ H₂ with h | h
  · by_cases H_eq : Equiv x y
    · exact Or.inl H_eq
    · exact Or.inr (Or.inl (Ord.lt_of_ne_and_le H₁ H₂ H_eq h))
  · by_cases H_eq : Equiv x y
    · exact Or.inl H_eq
    · exact Or.inr (Or.inr (Ord.lt_of_ne_and_le H₂ H₁ (fun h' => H_eq h'.symm) h))

-- src/aleph_one.lean:171
lemma Ord.lt_of_le_of_lt {x y z : PSet.{u}} (Hx : Ord x) (Hy : Ord y) (Hz : Ord z)
    (H_le : x ⊆ y) (H_lt : y ∈ z) : x ∈ z := by
  rcases Ord.trichotomy Hx Hy with h | h | h
  · -- Equiv x y, y ∈ z → x ∈ z
    exact (PSet.Mem.congr_left h).mpr H_lt
  · exact mem_trans_of_transitive h H_lt Hz.right
  · -- y ∈ x: y ∈ x and x ⊆ y → y ∈ y, contradiction
    exfalso; exact PSet.mem_irrefl y (mem_of_mem_subset' H_le h)

-- src/aleph_one.lean:182
lemma Ord.le_iff_lt_or_eq {x z : PSet.{u}} (H₁ : Ord x) (H₂ : Ord z) :
    x ⊆ z ↔ x ∈ z ∨ Equiv x z := by
  classical
  constructor
  · intro H
    by_cases H_eq : Equiv x z
    · exact Or.inr H_eq
    · exact Or.inl (Ord.lt_of_ne_and_le H₁ H₂ H_eq H)
  · intro h
    rcases h with h | h
    · exact is_transitive_of_mem_Ord H₂ x h
    · exact subset_iff_all_mem.mpr (fun z' hz' => (ext_iff.mp h z').mp hz')

-- src/aleph_one.lean:195
open Cardinal in
lemma mk_injects_into_of_mk_le_omega {η : Ordinal.{u}}
    (H_le : Cardinal.mk (ordinalMk η).Type ≤ Cardinal.mk (PSet.omega : PSet.{u}).Type) :
    injects_into (ordinalMk η) PSet.omega := by
  obtain ⟨f, Hf⟩ := injection_of_mk_le H_le
  let ψ : (ordinalMk η).Type → PSet.{u} := fun i => PSet.omega.Func (f i)
  have H_ext : ∀ i j, Equiv ((ordinalMk η).Func i) ((ordinalMk η).Func j) → Equiv (ψ i) (ψ j) := by
    intro i j H_eqv
    by_cases hij : i = j
    · subst hij; exact Equiv.refl _
    · exfalso; exact ordinalMk_inj η i j hij H_eqv
  refine ⟨function_mk.mk ψ H_ext, ?_, ?_⟩
  · apply function_mk.mk_is_func
    intro i; exact PSet.func_mem PSet.omega (f i)
  · apply function_mk.mk_inj_of_inj
    intro i₁ i₂ H_eqv
    have h := omega_inj H_eqv
    have hi := Hf h
    subst hi; exact Equiv.refl _

-- src/aleph_one.lean:216
open Cardinal in
lemma injects_into_omega_of_mem_aleph_one {z : PSet} (H_mem : z ∈ aleph_one) :
    injects_into z PSet.omega := by
  obtain ⟨w, Hw_lt, Hz_eq⟩ := equiv_mk_of_mem_mk z H_mem
  suffices injects_into (ordinalMk w) PSet.omega from
    P_ext_injects_into_left (ordinalMk w) z Hz_eq.symm this
  apply mk_injects_into_of_mk_le_omega
  rw [ordinalMk_card, mk_omega_eq_mk_omega]
  have h1 : w.card < Cardinal.aleph 1 := Cardinal.lt_ord.mp Hw_lt
  rw [aleph_one_eq_succ_aleph_zero] at h1
  exact Order.lt_succ_iff.mp h1

-- src/aleph_one.lean:226
lemma aleph_one_satisfies_spec : aleph_one_weak_Ord_spec aleph_one := by
  refine ⟨aleph_one_Ord, ?_⟩
  rintro z ⟨Hz₁, Hz₂⟩
  rw [Ord.le_iff_lt_or_eq aleph_one_Ord Hz₁]
  rcases Ord.trichotomy aleph_one_Ord Hz₁ with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exfalso; exact Hz₂ (injects_into_omega_of_mem_aleph_one h)

end

end PSet

-- ============================================================
-- src/aleph_one.lean:242-450: namespace bSet
-- ============================================================

open Cardinal bSet
namespace bSet

-- ============================================================
-- src/aleph_one.lean:256-450: section well_ordering
-- ============================================================

section well_ordering

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/aleph_one.lean:260
@[reducible] def is_rel (r x : bSet 𝔹) : 𝔹 := r ⊆ᴮ prod x x

-- src/aleph_one.lean:262
def is_wo (r x : bSet 𝔹) : 𝔹 :=
  is_rel r x ⊓
  ((⨅ y, pair y x ∈ᴮ r ⟹ (⨅ z, pair z x ∈ᴮ r ⟹ (y =ᴮ z ⊔ pair y z ∈ᴮ r ⊔ pair z y ∈ᴮ r))) ⊓
   (⨅ u, u ⊆ᴮ x ⟹ ((u =ᴮ ∅)ᶜ ⟹ ⨆ y, pair y u ∈ᴮ r ⊓ (⨅ z', pair z' u ∈ᴮ r ⟹ (pair z' y ∈ᴮ r)ᶜ))))

-- src/aleph_one.lean:266
def mem_rel (x : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun pr : (prod x x).type => x.func pr.1 ∈ᴮ x.func pr.2)

-- src/aleph_one.lean:268
lemma mem_mem_rel_iff {x y z : bSet 𝔹} {Γ} :
    Γ ≤ pair y z ∈ᴮ mem_rel x ↔ (Γ ≤ y ∈ᴮ x ∧ Γ ≤ z ∈ᴮ x ∧ Γ ≤ y ∈ᴮ z) := by
  -- mem_rel x = subset.mk (fun pr : (prod x x).type => x.func pr.1 ∈ x.func pr.2)
  unfold mem_rel
  rw [mem_subset.mk_iff]
  simp only [prod_func, prod_bval]
  constructor
  · -- MP: Γ ≤ ⨆ (i,j), pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) → each conclusion
    intro H
    refine ⟨?_, ?_, ?_⟩
    · -- y ∈ x
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      -- goal: pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) ≤ y ∈ x
      have hyi : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ y =ᴮ x.func i :=
        inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).1
      have hbi : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ x.bval i :=
        inf_le_right.trans (inf_le_right.trans inf_le_left)
      calc pair y z =ᴮ pair (x.func i) (x.func j) ⊓
              (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
          ≤ y =ᴮ x.func i ⊓ x.bval i := le_inf hyi hbi
        _ ≤ y ∈ᴮ x := by
            rw [mem_unfold]; apply le_iSup_of_le i
            exact le_inf inf_le_right inf_le_left
    · -- z ∈ x
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      have hzj : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ z =ᴮ x.func j :=
        inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).2
      have hbj : pair y z =ᴮ pair (x.func i) (x.func j) ⊓
          (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j)) ≤ x.bval j :=
        inf_le_right.trans (inf_le_right.trans inf_le_right)
      calc pair y z =ᴮ pair (x.func i) (x.func j) ⊓
              (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
          ≤ z =ᴮ x.func j ⊓ x.bval j := le_inf hzj hbj
        _ ≤ z ∈ᴮ x := by
            rw [mem_unfold]; apply le_iSup_of_le j
            exact le_inf inf_le_right inf_le_left
    · -- y ∈ z
      apply le_trans H; apply iSup_le; intro ⟨i, j⟩
      -- goal: pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj)) ≤ y∈z
      set T := pair y z =ᴮ pair (x.func i) (x.func j) ⊓
        (x.func i ∈ᴮ x.func j ⊓ (x.bval i ⊓ x.bval j))
      have hyi : T ≤ y =ᴮ x.func i := inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).1
      have hzj : T ≤ z =ᴮ x.func j := inf_le_left.trans (pair_eq_pair_iff.mp le_rfl).2
      have hxixj : T ≤ x.func i ∈ᴮ x.func j := inf_le_right.trans inf_le_left
      -- y = xi, xi ∈ xj, xj = z  →  y ∈ z via mem_congr
      exact mem_congr (bv_symm hyi) (bv_symm hzj) hxixj
  · -- MPI: y∈x ∧ z∈x ∧ y∈z → ⨆ ij, ...
    intro ⟨Hy, Hz, Hyz⟩
    rw [mem_unfold] at Hy Hz
    -- Use iSup_inf_iSup to combine the two iSups, then bound elementwise
    apply le_trans (le_inf (le_inf Hy Hz) Hyz)
    -- goal: (⨆ i, bi⊓y=xi) ⊓ (⨆ j, bj⊓z=xj) ⊓ y∈z ≤ ⨆ (k,l), ...
    rw [show (⨆ i : x.type, x.bval i ⊓ y =ᴮ x.func i) ⊓
              (⨆ j : x.type, x.bval j ⊓ z =ᴮ x.func j) =
              ⨆ ij : x.type × x.type, (x.bval ij.1 ⊓ y =ᴮ x.func ij.1) ⊓
                (x.bval ij.2 ⊓ z =ᴮ x.func ij.2) from iSup_inf_iSup]
    rw [inf_comm]
    apply bv_cases_right; intro ⟨i, j⟩
    apply le_iSup_of_le (i, j)
    simp only [prod_func, prod_bval]
    -- After bv_cases_right intro ⟨i, j⟩ and rw [inf_comm], context is:
    -- y∈z ⊓ ((bi⊓y=xi) ⊓ (bj⊓z=xj)) ≤ pair y z =ᴮ pair(xi,xj) ⊓ (xi∈xj ⊓ (bi⊓bj))
    -- Extract parts:
    have hbeq_y : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        y =ᴮ x.func i := inf_le_right.trans (inf_le_left.trans inf_le_right)
    have hbeq_z : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        z =ᴮ x.func j := inf_le_right.trans (inf_le_right.trans inf_le_right)
    have hbval_i : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        x.bval i := inf_le_right.trans (inf_le_left.trans inf_le_left)
    have hbval_j : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        x.bval j := inf_le_right.trans (inf_le_right.trans inf_le_left)
    have hyz : y ∈ᴮ z ⊓ ((x.bval i ⊓ y =ᴮ x.func i) ⊓ (x.bval j ⊓ z =ᴮ x.func j)) ≤
        y ∈ᴮ z := inf_le_left
    refine le_inf (pair_eq_pair_iff.mpr ⟨hbeq_y, hbeq_z⟩)
      (le_inf (mem_congr hbeq_y hbeq_z hyz) (le_inf hbval_i hbval_j))

-- src/aleph_one.lean:286
@[simp] lemma B_congr_mem_rel : B_congr (mem_rel : bSet 𝔹 → bSet 𝔹) := by
  intro x y Γ H_eq
  -- Use prod_ext: both subsets of prod x x
  have H_sub_x : Γ ≤ mem_rel x ⊆ᴮ prod x x := subset.mk_subset
  have H_prod_eq : Γ ≤ prod x x =ᴮ prod y y := prod_congr H_eq H_eq
  have H_sub_y : Γ ≤ mem_rel y ⊆ᴮ prod x x :=
    poset_yoneda_inv Γ subst_congr_subset_right
      (le_inf subset.mk_subset (bv_symm H_prod_eq))
  apply prod_ext H_sub_x H_sub_y
  apply le_iInf; intro v; rw [← deduction]
  apply le_iInf; intro w; rw [← deduction]
  -- ctx: Γ ⊓ v ∈ x ⊓ w ∈ x
  apply le_inf
  · -- pair v w ∈ mem_rel x → pair v w ∈ mem_rel y  (forward direction)
    rw [← deduction]
    -- Goal: Γ ⊓ v ∈ x ⊓ w ∈ x ⊓ pair v w ∈ mem_rel x ≤ pair v w ∈ mem_rel y
    -- Abbreviate the context:
    apply (mem_mem_rel_iff (x := y) (y := v) (z := w)).mpr
    -- Need: ctx ≤ v ∈ y ∧ ctx ≤ w ∈ y ∧ ctx ≤ v ∈ w
    have ctx_le_x_eq_y : Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel x ≤ x =ᴮ y :=
      inf_le_left.trans (inf_le_left.trans (inf_le_left.trans H_eq))
    have hpr := (mem_mem_rel_iff (Γ := Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel x)
      (x := x) (y := v) (z := w)).mp inf_le_right
    exact ⟨bv_rw'' ctx_le_x_eq_y hpr.1 B_ext_mem_right,
           bv_rw'' ctx_le_x_eq_y hpr.2.1 B_ext_mem_right,
           hpr.2.2⟩
  · -- pair v w ∈ mem_rel y → pair v w ∈ mem_rel x  (backward direction)
    rw [← deduction]
    apply (mem_mem_rel_iff (x := x) (y := v) (z := w)).mpr
    have ctx_le_y_eq_x : Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel y ≤ y =ᴮ x :=
      bv_symm (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans H_eq)))
    have hpr := (mem_mem_rel_iff (Γ := Γ ⊓ v ∈ᴮ x ⊓ w ∈ᴮ x ⊓ pair v w ∈ᴮ mem_rel y)
      (x := y) (y := v) (z := w)).mp inf_le_right
    exact ⟨bv_rw'' ctx_le_y_eq_x hpr.1 B_ext_mem_right,
           bv_rw'' ctx_le_y_eq_x hpr.2.1 B_ext_mem_right,
           hpr.2.2⟩

-- src/aleph_one.lean:297
def prod_map (x y v w : bSet 𝔹) (f g : bSet 𝔹) : bSet 𝔹 :=
  subset.mk (fun (pr : (prod (prod x v) (prod y w)).type) =>
    pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (v.func pr.1.2) (w.func pr.2.2) ∈ᴮ g)

-- src/aleph_one.lean:299
def prod_map_self (x y f : bSet 𝔹) : bSet 𝔹 :=
  prod_map x y x y f f

-- src/aleph_one.lean:302
lemma B_congr_prod_map_self_left_aux {y f x x' : bSet 𝔹} {Γ : 𝔹} (H_eq : Γ ≤ x =ᴮ x') :
    Γ ≤ ⨅ (z : bSet 𝔹), z ∈ᴮ prod_map_self x y f ⟹ z ∈ᴮ prod_map_self x' y f := by
  -- Goal: Γ ≤ ⨅ z, z ∈ prod_map_self x y f ⟹ z ∈ prod_map_self x' y f
  -- prod_map_self x y f = subset.mk χ where parent = prod(prod x x)(prod y y)
  -- Strategy: for each z, go through the iSup elements of prod_map_self x y f
  --   and produce corresponding elements for prod_map_self x' y f by reindexing
  apply le_iInf; intro z; rw [← deduction]
  -- ctx: Γ ⊓ z ∈ prod_map_self x y f
  -- unfold both sides
  show Γ ⊓ z ∈ᴮ prod_map_self x y f ≤ z ∈ᴮ prod_map_self x' y f
  -- Extract from iSup in prod_map_self x y f
  have Hmem_iff : Γ ⊓ z ∈ᴮ prod_map_self x y f ≤ z ∈ᴮ prod_map_self x y f := inf_le_right
  rw [show prod_map_self x y f = subset.mk (fun pr : (prod (prod x x) (prod y y)).type =>
    pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f) from rfl] at Hmem_iff
  rw [mem_subset.mk_iff₂] at Hmem_iff
  apply le_trans (le_inf Hmem_iff le_rfl)
  apply bv_cases_left; intro pr
  obtain ⟨⟨i₁, i₂⟩, j₁, j₂⟩ := pr
  simp only [prod_func, prod_bval]
  -- ctx: ((x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)) ⊓
  --       (z=ᴮpair(pair xi₁ xi₂)(pair yj₁ yj₂) ⊓ (χ₁⊓χ₂)) ⊓ (Γ ⊓ z∈...)
  -- Need: ctx ≤ z ∈ prod_map_self x' y f
  -- bv_rw' on zeq: reduce to pair(xi₁ xi₂)(yj₁ yj₂) ∈ prod_map_self x' y f
  -- Then provide the witness directly via mem_subset.mk_iff₂.mpr
  -- xi₁ ∈ x' (via bv_rw'' Heq (xi₁∈x)): for the new index i₁', use mem_unfold + bv_cases_left
  -- To avoid index extraction, we stay in the iSup form and use bv_use
  rw [show prod_map_self x' y f = subset.mk (fun pr' : (prod (prod x' x') (prod y y)).type =>
    pair (x'.func pr'.1.1) (y.func pr'.2.1) ∈ᴮ f ⊓ pair (x'.func pr'.1.2) (y.func pr'.2.2) ∈ᴮ f) from rfl,
    mem_subset.mk_iff₂]
  -- Goal: ctx ≤ ⨆ pr', bval'(pr') ⊓ (z=ᴮfunc'(pr') ⊓ χ'(pr'))
  -- Ctx structure: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (zeq ⊓ (χ1⊓χ2)) ⊓ (Γ ⊓ z∈...)
  -- xi₁ ∈ x' (via mem_congr) → get i₁' via le_trans + bv_cases_left
  apply le_trans (b := (⨆ i₁' : x'.type, x'.bval i₁' ⊓ x.func i₁ =ᴮ x'.func i₁') ⊓ _)
  · apply le_inf
    · rw [← mem_unfold]
      -- prove ctx ≤ x.func i₁ ∈ᴮ x'
      exact mem_congr bv_refl (inf_le_right.trans (inf_le_left.trans H_eq))
        ((inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))).trans (mem_mk' x i₁))
    · exact le_rfl
  apply bv_cases_left; intro i₁'
  -- ctx1 = (x'.bval i₁' ⊓ xi₁=x'.func i₁') ⊓ ctx
  -- xi₂ ∈ x' → get i₂' via le_trans + bv_cases_left
  apply le_trans (b := (⨆ i₂' : x'.type, x'.bval i₂' ⊓ x.func i₂ =ᴮ x'.func i₂') ⊓ _)
  · apply le_inf
    · rw [← mem_unfold]
      -- prove ctx1 ≤ x.func i₂ ∈ᴮ x'
      exact mem_congr bv_refl (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans H_eq)))
        ((inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))).trans
          (mem_mk' x i₂))
    · exact le_rfl
  apply bv_cases_left; intro i₂'
  -- ctx2 = (x'.bval i₂' ⊓ xi₂=x'.func i₂') ⊓ ctx1
  -- ctx2 structure:
  --   (x'.bval i₂' ⊓ x.func i₂ =ᴮ x'.func i₂') ⊓
  --   ((x'.bval i₁' ⊓ x.func i₁ =ᴮ x'.func i₁') ⊓
  --    (((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (zeq ⊓ (χ1⊓χ2)) ⊓ (Γ ⊓ z∈...)))
  apply bv_use ((i₁', i₂'), j₁, j₂)
  simp only [prod_func, prod_bval]
  -- Extractions from ctx2 (after simp):
  --   x'.bval i₁' : ir.il.il
  --   xi₁=x'.func i₁' : ir.il.ir
  --   x'.bval i₂' : il.il
  --   xi₂=x'.func i₂' : il.ir
  --   xb1 : ir.ir.il.il.il
  --   xb2 : ir.ir.il.il.ir
  --   yb1 : ir.ir.il.ir.il
  --   yb2 : ir.ir.il.ir.ir
  --   zeq : ir.ir.ir.il
  --   χ1  : ir.ir.ir.ir.il
  --   χ2  : ir.ir.ir.ir.ir
  apply le_inf
  · -- bval': (x'.bval i₁' ⊓ x'.bval i₂') ⊓ (y.bval j₁ ⊓ y.bval j₂)
    apply le_inf (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact inf_le_right.trans (inf_le_left.trans inf_le_left)
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_left))))
    · exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_right))))
  · apply le_inf
    · -- z =ᴮ pair(pair x'.func(i₁') x'.func(i₂'))(pair yj₁ yj₂)
      -- First prove z =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂), then rewrite xi₁ → x'.func i₁'
      apply bv_trans
      · -- zeq: ctx2 ≤ z =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
        exact inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_left)))
      · apply pair_eq_pair_iff.mpr; constructor
        · apply pair_eq_pair_iff.mpr
          -- Hi₁'eq: ir.il.ir, Hi₂'eq: il.ir
          exact ⟨inf_le_right.trans (inf_le_left.trans inf_le_right), inf_le_left.trans inf_le_right⟩
        · apply pair_eq_pair_iff.mpr; exact ⟨bv_refl, bv_refl⟩
    · apply le_inf
      · -- pair x'.func(i₁') yj₁ ∈ f
        exact bv_rw' (ϕ := fun v => pair v (y.func j₁) ∈ᴮ f) (h_congr := B_ext_pair_mem_left)
          (H := bv_symm (inf_le_right.trans (inf_le_left.trans inf_le_right)))
          (H_new := inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))))
      · -- pair x'.func(i₂') yj₂ ∈ f
        exact bv_rw' (ϕ := fun v => pair v (y.func j₂) ∈ᴮ f) (h_congr := B_ext_pair_mem_left)
          (H := bv_symm (inf_le_left.trans inf_le_right))
          (H_new := inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))))

-- src/aleph_one.lean:329
@[simp] lemma B_congr_prod_map_self_left {y f : bSet 𝔹} :
    B_congr (fun x : bSet 𝔹 => prod_map_self x y f) := by
  intro x x' Γ H_eq
  apply mem_ext
  · apply B_congr_prod_map_self_left_aux; exact H_eq
  · apply B_congr_prod_map_self_left_aux; exact bv_symm H_eq

-- src/aleph_one.lean:336
set_option maxHeartbeats 400000 in
lemma mem_prod_map_self_iff {x y f a₁ a₂ b₁ b₂ : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ pair (pair a₁ a₂) (pair b₁ b₂) ∈ᴮ prod_map_self x y f ↔
    Γ ≤ a₁ ∈ᴮ x ∧ Γ ≤ a₂ ∈ᴮ x ∧ Γ ≤ b₁ ∈ᴮ y ∧ Γ ≤ b₂ ∈ᴮ y ∧
    Γ ≤ pair a₁ b₁ ∈ᴮ f ∧ Γ ≤ pair a₂ b₂ ∈ᴮ f := by
  constructor
  · -- forward: prove each of the 6 conclusions from H
    intro H
    rw [show prod_map_self x y f = subset.mk (fun pr : (prod (prod x x) (prod y y)).type =>
      pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f) from rfl] at H
    rw [mem_subset.mk_iff₂] at H
    -- H : Γ ≤ ⨆ pr, bval pr ⊓ (pair_eq pr ⊓ χ pr)
    -- For pr = ((i₁,i₂),(j₁,j₂)):
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)
    --   pair_eq = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
    --   χ = pair xi₁ yj₁ ∈ f ⊓ pair xi₂ yj₂ ∈ f
    -- Each of the 6 conclusions: Γ ≤ P, proved by le_trans H (iSup_le ...)
    -- Helper: extract component equalities from the body
    -- body : bval ⊓ (peq ⊓ χ)
    -- peq : inf_le_right.trans inf_le_left
    -- after two pair_eq_pair_iff.mp: a₁=xi₁, a₂=xi₂, b₁=yj₁, b₂=yj₂
    -- body after simp for pr = ((i₁,i₂),(j₁,j₂)):
    -- bval ⊓ (peq ⊓ (χ₁ ⊓ χ₂)) where
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)
    --   peq  = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
    --   χ₁   = pair xi₁ yj₁ ∈ f,   χ₂ = pair xi₂ yj₂ ∈ f
    -- body after simp for pr = ((i₁,i₂),(j₁,j₂)):
    -- bval ⊓ (peq ⊓ (χ₁ ⊓ χ₂)) where
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)  [inf_le_left]
    --   peq  = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)  [inf_le_right.trans inf_le_left]
    --   χ₁   = pair xi₁ yj₁ ∈ f  [inf_le_right.trans inf_le_right.trans inf_le_left]
    --   χ₂   = pair xi₂ yj₂ ∈ f  [inf_le_right.trans inf_le_right.trans inf_le_right]
    -- All are proved using this tactic:
    -- body after simp for pr = ((i₁,i₂),(j₁,j₂)):
    --   bval = (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)  [inf_le_left]
    --   peq  = pair_eq                [inf_le_right.trans inf_le_left]
    --   χ₁   = pair xi₁ yj₁ ∈ f     [inf_le_right.trans inf_le_right.trans inf_le_left]
    --   χ₂   = pair xi₂ yj₂ ∈ f     [inf_le_right.trans inf_le_right.trans inf_le_right]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    -- body structure: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq = pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
    -- Chains: peq=ir.il; from peq: pair a₁ a₂ =ᴮ pair xi₁ xi₂ via eq_of_eq_pair_left
    --         from that: a₁=xi₁ via eq_of_eq_pair_left, a₂=xi₂ via eq_of_eq_pair_right
    -- bval: xb1=il.il.il, xb2=il.il.ir, yb1=il.ir.il, yb2=il.ir.ir
    -- χ1=ir.ir.il, χ2=ir.ir.ir
    -- body: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq extraction: ir.il; bval: xb1=il.il.il; xb2=il.il.ir; yb1=il.ir.il; yb2=il.ir.ir
    -- χ1=ir.ir.il; χ2=ir.ir.ir
    -- body: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq: ir.il; xb1=il.il.il; xb2=il.il.ir; yb1=il.ir.il; yb2=il.ir.ir
    -- χ1=ir.ir.il; χ2=ir.ir.ir
    -- body: ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- peq=ir.il; xb1=il.il.il; xb2=il.il.ir; yb1=il.ir.il; yb2=il.ir.ir; χ1=ir.ir.il; χ2=ir.ir.ir
    -- Inline approach: avoid 'have' and use exact with full chains
    -- After simp, body = ((xb1⊓xb2)⊓(yb1⊓yb2)) ⊓ (peq ⊓ (χ1⊓χ2))
    -- Use apply-based approach: each step creates a concrete goal, avoiding bidirectional inference
    -- Helper for peq extraction (used repeatedly):
    -- After simp: body ≤ peq ≡ body ≤ pair(pair a₁ a₂)(pair b₁ b₂)=ᴮpair(pair xi₁ xi₂)(pair yj₁ yj₂)
    -- via inf_le_right.trans inf_le_left.
    · -- a₁ ∈ x
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ x) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_left.trans inf_le_left)).trans (mem_mk' x i₁))
      apply eq_of_eq_pair_left'; apply eq_of_eq_pair_left'
      exact inf_le_right.trans inf_le_left
    · -- a₂ ∈ x
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ x) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_left.trans inf_le_right)).trans (mem_mk' x i₂))
      apply eq_of_eq_pair_right'; apply eq_of_eq_pair_left'
      exact inf_le_right.trans inf_le_left
    · -- b₁ ∈ y
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ y) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_right.trans inf_le_left)).trans (mem_mk' y j₁))
      apply eq_of_eq_pair_left'; apply eq_of_eq_pair_right'
      exact inf_le_right.trans inf_le_left
    · -- b₂ ∈ y
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ y) (h_congr := B_ext_mem_left)
        (H_new := (inf_le_left.trans (inf_le_right.trans inf_le_right)).trans (mem_mk' y j₂))
      apply eq_of_eq_pair_right'; apply eq_of_eq_pair_right'
      exact inf_le_right.trans inf_le_left
    · -- pair a₁ b₁ ∈ f: use bv_rw' to rewrite pair a₁ b₁ to pair xi₁ yj₁ (which ∈ f)
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ f) (h_congr := B_ext_mem_left)
        (H_new := inf_le_right.trans (inf_le_right.trans inf_le_left))
      apply pair_congr
      · apply eq_of_eq_pair_left'; apply eq_of_eq_pair_left'; exact inf_le_right.trans inf_le_left
      · apply eq_of_eq_pair_left'; apply eq_of_eq_pair_right'; exact inf_le_right.trans inf_le_left
    · -- pair a₂ b₂ ∈ f: same but using χ₂
      apply H.trans; apply iSup_le; rintro ⟨⟨i₁, i₂⟩, j₁, j₂⟩; simp only [prod_func, prod_bval]
      apply bv_rw' (ϕ := fun v => v ∈ᴮ f) (h_congr := B_ext_mem_left)
        (H_new := inf_le_right.trans (inf_le_right.trans inf_le_right))
      apply pair_congr
      · apply eq_of_eq_pair_right'; apply eq_of_eq_pair_left'; exact inf_le_right.trans inf_le_left
      · apply eq_of_eq_pair_right'; apply eq_of_eq_pair_right'; exact inf_le_right.trans inf_le_left
  · -- backward: construct the witness index from the 6 hypotheses
    intro ⟨Ha₁, Ha₂, Hb₁, Hb₂, Hpair₁, Hpair₂⟩
    rw [show prod_map_self x y f = subset.mk (fun pr : (prod (prod x x) (prod y y)).type =>
      pair (x.func pr.1.1) (y.func pr.2.1) ∈ᴮ f ⊓ pair (x.func pr.1.2) (y.func pr.2.2) ∈ᴮ f) from rfl]
    rw [mem_subset.mk_iff₂]
    -- Need: Γ ≤ ⨆ pr, bval pr ⊓ (pair_eq pr ⊓ χ pr)
    -- Extract witnesses via mem_unfold and sequential bv_cases_left
    rw [mem_unfold] at Ha₁ Ha₂ Hb₁ Hb₂
    -- LHS0 = (((Ha₁ ⊓ Ha₂) ⊓ Hb₁) ⊓ Hb₂) ⊓ Γ
    apply le_trans (le_inf (le_inf (le_inf (le_inf Ha₁ Ha₂) Hb₁) Hb₂) le_rfl)
    -- Extract i₁ from Ha₁: inf_le_left^3 then inf_le_left
    apply le_trans (le_inf (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))) le_rfl)
    apply bv_cases_left; intro i₁
    -- ctx1 = (x.bval i₁ ⊓ a₁=xi₁) ⊓ LHS0
    -- Extract i₂ from Ha₂ in LHS0: inf_le_right then inf_le_left^3 then inf_le_right
    apply le_trans (le_inf (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))) le_rfl)
    apply bv_cases_left; intro i₂
    -- ctx2 = (x.bval i₂ ⊓ a₂=xi₂) ⊓ ctx1
    -- Extract j₁ from Hb₁ in LHS0: inf_le_right^2 then inf_le_left^2 then inf_le_right
    apply le_trans (le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))) le_rfl)
    apply bv_cases_left; intro j₁
    -- ctx3 = (y.bval j₁ ⊓ b₁=yj₁) ⊓ ctx2
    -- Extract j₂ from Hb₂ in LHS0: inf_le_right^3 then inf_le_left then inf_le_right
    apply le_trans (le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)))) le_rfl)
    apply bv_cases_left; intro j₂
    -- ctx4 = (y.bval j₂ ⊓ b₂=yj₂) ⊓ ctx3
    -- ctx4 components (left-to-right nesting):
    --   y.bval j₂: inf_le_left.trans inf_le_left
    --   b₂=yj₂:   inf_le_left.trans inf_le_right
    --   y.bval j₁: inf_le_right.trans (inf_le_left.trans inf_le_left)
    --   b₁=yj₁:   inf_le_right.trans (inf_le_left.trans inf_le_right)
    --   x.bval i₂: inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
    --   a₂=xi₂:   inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
    --   x.bval i₁: inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)))
    --   a₁=xi₁:   inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)))
    --   Γ:         inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    apply bv_use ((i₁, i₂), j₁, j₂)
    simp only [prod_func, prod_bval]
    apply le_inf
    · -- bval: (x.bval i₁ ⊓ x.bval i₂) ⊓ (y.bval j₁ ⊓ y.bval j₂)
      exact le_inf (le_inf
        (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))))
        (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))))
        (le_inf
          (inf_le_right.trans (inf_le_left.trans inf_le_left))
          (inf_le_left.trans inf_le_left))
    · apply le_inf
      · -- pair equality: pair(pair a₁ a₂)(pair b₁ b₂) =ᴮ pair(pair xi₁ xi₂)(pair yj₁ yj₂)
        -- ctx4 component accesses: a₁=xi₁ at (.3.left.right), a₂=xi₂ at (.3.right), b₁=yj₁ at (.2.right), b₂=yj₂ at (.1.right)
        -- But mem_unfold gives: a₁ =ᴮ x.func i₁, not x.func i₁ =ᴮ a₁
        -- So we use them directly (no bv_symm needed):
        apply pair_eq_pair_iff.mpr; constructor
        · apply pair_eq_pair_iff.mpr; exact ⟨
            inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))),
            inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))⟩
        · apply pair_eq_pair_iff.mpr; exact ⟨
            inf_le_right.trans (inf_le_left.trans inf_le_right),
            inf_le_left.trans inf_le_right⟩
      · -- χ: pair(xi₁)(yj₁) ∈ f ⊓ pair(xi₂)(yj₂) ∈ f
        -- Γ accessible via inf_le_right^5 from ctx4; then compose with Hpair₁, Hpair₂
        apply le_inf
        · -- pair(xi₁)(yj₁) ∈ f: use mem_congr (pair a₁ b₁ =ᴮ pair xi₁ yj₁) bv_refl (pair a₁ b₁ ∈ f)
          apply mem_congr _ bv_refl
          · -- pair a₁ b₁ ∈ f via Hpair₁
            exact (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans
                    (inf_le_right.trans inf_le_right)))).trans Hpair₁
          · -- pair a₁ b₁ =ᴮ pair xi₁ yj₁ via pair_congr and equalities from ctx4
            apply pair_eq_pair_iff.mpr
            exact ⟨inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))),
                   inf_le_right.trans (inf_le_left.trans inf_le_right)⟩
        · -- pair(xi₂)(yj₂) ∈ f
          apply mem_congr _ bv_refl
          · exact (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans
                    (inf_le_right.trans inf_le_right)))).trans Hpair₂
          · apply pair_eq_pair_iff.mpr
            exact ⟨inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right)),
                   inf_le_left.trans inf_le_right⟩

-- src/aleph_one.lean:379
def induced_epsilon_rel (η : bSet 𝔹) (x : bSet 𝔹) (f : bSet 𝔹) : bSet 𝔹 :=
  image (mem_rel η) (prod x x) (prod_map_self η x f)

-- src/aleph_one.lean:382
lemma eq_pair_of_mem_induced_epsilon_rel {η x f pr : bSet 𝔹} {Γ}
    (H_mem : Γ ≤ pr ∈ᴮ induced_epsilon_rel η x f) :
    ∃ a b : bSet 𝔹, Γ ≤ a ∈ᴮ x ∧ Γ ≤ b ∈ᴮ x ∧ Γ ≤ pr =ᴮ pair a b ∧
    Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f := by
  have hmem : Γ ≤ pr ∈ᴮ prod x x :=
    mem_of_mem_subset subset.mk_subset H_mem
  obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp hmem
  exact ⟨v, w, Hv, Hw, H_eq,
    bv_rw' (bv_symm H_eq) (ϕ := fun z => z ∈ᴮ induced_epsilon_rel η x f)
      (h_congr := B_ext_mem_left) (H_new := H_mem)⟩

-- src/aleph_one.lean:391
lemma mem_induced_epsilon_rel_iff {η x f a b : bSet 𝔹} {Γ}
    (H_func : Γ ≤ is_function η x f) :
    Γ ≤ pair a b ∈ᴮ (induced_epsilon_rel η x f) ↔
    (Γ ≤ a ∈ᴮ x) ∧ (Γ ≤ b ∈ᴮ x) ∧
    (Γ ≤ ⨆ a', a' ∈ᴮ η ⊓ ⨆ b', b' ∈ᴮ η ⊓
      (pair a' a ∈ᴮ f ⊓ pair b' b ∈ᴮ f ⊓ a' ∈ᴮ b')) := by
  -- induced_epsilon_rel η x f = image (mem_rel η) (prod x x) (prod_map_self η x f)
  -- mem_image_iff: pair a b ∈ image S Y F ↔ pair a b ∈ Y ∧ ∃ z, z ∈ S ∧ pair z (pair a b) ∈ F
  -- unfold induced_epsilon_rel to allow mem_image_iff
  show Γ ≤ pair a b ∈ᴮ image (mem_rel η) (prod x x) (prod_map_self η x f) ↔ _
  constructor
  · -- Forward: from pair a b ∈ image (mem_rel η) (prod x x) (prod_map_self η x f)
    intro H
    rw [mem_image_iff] at H
    obtain ⟨H_prod, H_sup⟩ := H
    rw [mem_prod_iff] at H_prod
    obtain ⟨Ha, Hb⟩ := H_prod
    refine ⟨Ha, Hb, ?_⟩
    -- H_sup: Γ ≤ ⨆ z, z ∈ mem_rel η ⊓ pair z (pair a b) ∈ prod_map_self η x f
    -- For each z in iSup, derive the iSup on a', b'
    apply H_sup.trans; apply iSup_le; intro z
    -- goal: (z ∈ mem_rel η ⊓ pair z (pair a b) ∈ prod_map_self η x f) ≤ ⨆ a', ...
    -- Now we have a concrete LHS — no more `_` issues
    have hz_prod : (z ∈ᴮ mem_rel η ⊓ pair z (pair a b) ∈ᴮ prod_map_self η x f) ≤ z ∈ᴮ prod η η :=
      mem_of_mem_subset subset.mk_subset inf_le_left
    obtain ⟨v, Hv, w, Hw, H_eq⟩ := mem_prod_iff₂.mp hz_prod
    -- provide witnesses a' = v, b' = w
    apply bv_use v; apply le_inf Hv
    apply bv_use w; apply le_inf Hw
    -- need: pair v a ∈ f ⊓ pair w b ∈ f ⊓ v ∈ w
    -- From pair z (pair a b) ∈ prod_map_self η x f (rewrite z = pair v w via H_eq)
    -- Get pair (pair v w) (pair a b) ∈ prod_map_self via bv_rw' on Hz_map
    have Hz_map : (z ∈ᴮ mem_rel η ⊓ pair z (pair a b) ∈ᴮ prod_map_self η x f) ≤
        pair (pair v w) (pair a b) ∈ᴮ prod_map_self η x f := by
      apply bv_rw' (ϕ := fun s => pair s (pair a b) ∈ᴮ prod_map_self η x f)
        (h_congr := B_ext_pair_mem_left) (H_new := inf_le_right)
      exact bv_symm H_eq
    -- Now use mem_prod_map_self_iff (no H_func needed) to extract components
    obtain ⟨_Hv', _Hw', _Ha, _Hb, Hpva, Hwb⟩ := mem_prod_map_self_iff.mp Hz_map
    -- Get v ∈ w from pair v w ∈ mem_rel η (via H_eq rewrite)
    have Hpvw_mem_rel : (z ∈ᴮ mem_rel η ⊓ pair z (pair a b) ∈ᴮ prod_map_self η x f) ≤
        pair v w ∈ᴮ mem_rel η := by
      apply bv_rw' (ϕ := fun s => s ∈ᴮ mem_rel η)
        (h_congr := B_ext_mem_left) (H_new := inf_le_left)
      exact bv_symm H_eq
    obtain ⟨_, _, Hvw⟩ := mem_mem_rel_iff.mp Hpvw_mem_rel
    exact le_inf (le_inf Hpva Hwb) Hvw
  · -- Backward: construct the image membership from the 3 conditions
    intro ⟨Ha, Hb, H_sup⟩
    rw [mem_image_iff]
    refine ⟨mem_prod_iff.mpr ⟨Ha, Hb⟩, ?_⟩
    -- H_sup: Γ ≤ ⨆ a', a'∈η ⊓ ⨆ b', b'∈η ⊓ (pair a' a ∈ f ⊓ pair b' b ∈ f ⊓ a'∈b')
    -- Extract a', b' witnesses
    apply le_trans (le_inf H_sup le_rfl)
    apply bv_cases_left; intro a'
    -- goal: (a'∈η ⊓ ⨆ b', b'∈η ⊓ ...) ⊓ Γ ≤ ⨆ z, z∈mem_rel η ⊓ pair z (pair a b) ∈ prod_map_self η x f
    -- extract ⨆ b' from left: inf_le_left.trans inf_le_right
    apply le_trans (le_inf (inf_le_left.trans inf_le_right) le_rfl)
    apply bv_cases_left; intro b'
    -- ctx: (b'∈η ⊓ (pair a' a ∈ f ⊓ pair b' b ∈ f ⊓ a'∈b')) ⊓ ((a'∈η ⊓ ⨆ b',..) ⊓ Γ)
    -- Provide z = pair a' b'
    apply bv_use (pair a' b')
    apply le_inf
    · -- pair a' b' ∈ mem_rel η: need a'∈η, b'∈η, a'∈b'
      -- a'∈η: from right part, a'∈η at inf_le_right.trans inf_le_left.trans inf_le_left
      -- b'∈η: from left part at inf_le_left.trans inf_le_left
      -- a'∈b': from left part at inf_le_left.trans inf_le_right.trans inf_le_right
      rw [mem_mem_rel_iff]
      refine ⟨?_, ?_, ?_⟩
      · exact inf_le_right.trans (inf_le_left.trans inf_le_left)
      · exact inf_le_left.trans inf_le_left
      · exact inf_le_left.trans (inf_le_right.trans inf_le_right)
    · -- pair (pair a' b') (pair a b) ∈ prod_map_self η x f
      -- a'∈η: inf_le_right.trans inf_le_left.trans inf_le_left
      -- b'∈η: inf_le_left.trans inf_le_left
      -- a∈x: from Ha (outer)
      -- b∈x: from Hb (outer)
      -- pair a' a ∈ f: inf_le_left.trans inf_le_right.trans inf_le_left.trans inf_le_left
      -- pair b' b ∈ f: inf_le_left.trans inf_le_right.trans inf_le_left.trans inf_le_right
      -- pair (pair a' b') (pair a b) ∈ prod_map_self η x f
      -- Use mem_prod_map_self_iff with the ctx's H_func access
      exact mem_prod_map_self_iff.mpr
        ⟨inf_le_right.trans (inf_le_left.trans inf_le_left),
         inf_le_left.trans inf_le_left,
         inf_le_right.trans (inf_le_right.trans Ha),
         inf_le_right.trans (inf_le_right.trans Hb),
         inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)),
         inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))⟩

-- src/aleph_one.lean:425
lemma mem_induced_epsilon_rel_of_mem {η x f a b : bSet 𝔹} {Γ}
    (H_mem₁ : Γ ≤ a ∈ᴮ η) (H_mem₂ : Γ ≤ b ∈ᴮ η) (H_mem : Γ ≤ a ∈ᴮ b)
    (H_func : Γ ≤ is_function η x f) :
    Γ ≤ pair (function_eval H_func a H_mem₁) (function_eval H_func b H_mem₂) ∈ᴮ
      induced_epsilon_rel η x f := by
  rw [mem_induced_epsilon_rel_iff H_func]
  refine ⟨function_eval_mem_codomain, function_eval_mem_codomain, ?_⟩
  apply bv_use a; refine le_inf H_mem₁ ?_
  apply bv_use b; refine le_inf H_mem₂ ?_
  exact le_inf (le_inf function_eval_pair_mem function_eval_pair_mem) H_mem

-- src/aleph_one.lean:437
lemma mem_of_mem_induced_epsilon_rel {η x f a' b' a b : bSet 𝔹} {Γ}
    (H_inj : Γ ≤ is_injective_function η x f)
    (H_mem₁ : Γ ≤ pair a' a ∈ᴮ f) (H_mem₂ : Γ ≤ pair b' b ∈ᴮ f)
    (H_mem : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) : Γ ≤ a' ∈ᴮ b' := by
  rw [mem_induced_epsilon_rel_iff (bv_and_left H_inj)] at H_mem
  obtain ⟨_Ha_mem, _Hb_mem, H⟩ := H_mem
  -- H : Γ ≤ ⨆ a'', a'' ∈ η ⊓ ⨆ b'', b'' ∈ η ⊓ (pair a'' a ∈ f ⊓ pair b'' b ∈ f ⊓ a'' ∈ b'')
  have H_inj' : Γ ≤ is_inj f := is_inj_of_is_injective_function H_inj
  apply le_trans (le_inf H le_rfl)
  apply bv_cases_left; intro a''
  -- goal: (a''∈η ⊓ ⨆ b'', b''∈η ⊓ (...)) ⊓ Γ ≤ a'∈b'
  -- extract ⨆ b'' to left
  apply le_trans (le_inf (inf_le_left.trans inf_le_right) le_rfl)
  apply bv_cases_left; intro b''
  -- goal: (b''∈η ⊓ ((pair a'' a ∈ f ⊓ pair b'' b ∈ f) ⊓ a''∈b'')) ⊓ ((a''∈η ⊓ ⨆ ..) ⊓ Γ) ≤ a'∈b'
  -- use `apply` to decompose mem_congr, so each subgoal has a concrete type
  apply mem_congr (x₁ := a'') (x₂ := b'')
  · -- prove a'' =ᴮ a' via is_inj: pair a'' a ∈ f and pair a' a ∈ f
    apply eq_of_is_inj_of_eq
    · exact inf_le_right.trans (inf_le_right.trans H_inj')
    · exact bv_refl (x := a)
    · exact inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
    · exact inf_le_right.trans (inf_le_right.trans H_mem₁)
  · -- prove b'' =ᴮ b' via is_inj: pair b'' b ∈ f and pair b' b ∈ f
    apply eq_of_is_inj_of_eq
    · exact inf_le_right.trans (inf_le_right.trans H_inj')
    · exact bv_refl (x := b)
    · exact inf_le_left.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))
    · exact inf_le_right.trans (inf_le_right.trans H_mem₂)
  · -- prove a'' ∈ b''
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)

-- ============================================================
-- src/aleph_one.lean:451-579: remaining well_ordering lemmas
-- ============================================================

-- src/aleph_one.lean:451
lemma induced_epsilon_rel_sub_image_left {η x f a b : bSet 𝔹} {Γ}
    (H_func : Γ ≤ is_function η x f)
    (H : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) : Γ ≤ a ∈ᴮ image η x f := by
  rw [mem_image_iff]; rw [mem_induced_epsilon_rel_iff H_func] at H
  obtain ⟨Ha_mem, _, H_sup⟩ := H
  refine ⟨Ha_mem, le_trans H_sup (iSup_le (fun a' => le_iSup_of_le a'
    (le_inf inf_le_left (le_trans inf_le_right (iSup_le (fun b' =>
      le_trans inf_le_right (inf_le_left.trans inf_le_left)))))))⟩

-- src/aleph_one.lean:461
lemma induced_epsilon_rel_sub_image_right {η x f a b : bSet 𝔹} {Γ}
    (H_func : Γ ≤ is_function η x f)
    (H : Γ ≤ pair a b ∈ᴮ induced_epsilon_rel η x f) : Γ ≤ b ∈ᴮ image η x f := by
  rw [mem_image_iff]; rw [mem_induced_epsilon_rel_iff H_func] at H
  obtain ⟨_, Hb_mem, H_sup⟩ := H
  refine ⟨Hb_mem, le_trans H_sup (iSup_le (fun a' => le_trans inf_le_right (iSup_le (fun b' =>
    le_iSup_of_le b' (le_inf inf_le_left (le_trans inf_le_right
      (inf_le_left.trans inf_le_right)))))))⟩

-- src/aleph_one.lean:471
set_option maxHeartbeats 800000 in
lemma image_eq_of_eq_induced_epsilon_rel_aux
    {η ρ f g : bSet 𝔹} {Γ}
    (Hη_inj : Γ ≤ is_injective_function η omega f)
    (Hρ_inj : Γ ≤ is_injective_function ρ omega g)
    (H_eq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (H_exists_two : Γ ≤ exists_two η) :
    Γ ≤ ⨅ (z : bSet 𝔹), z ∈ᴮ image η omega f ⟹ z ∈ᴮ image ρ omega g := by
  apply le_iInf; intro z; rw [← deduction]
  -- ctx: Γ ⊓ z ∈ image η omega f
  -- Get z' ∈ η s.t. pair z' z ∈ f
  have H_func : Γ ⊓ z ∈ᴮ image η omega f ≤ is_function η omega f :=
    inf_le_left.trans (bv_and_left Hη_inj)
  have Hz_mem : Γ ⊓ z ∈ᴮ image η omega f ≤ z ∈ᴮ image η omega f := inf_le_right
  rw [mem_image_iff] at Hz_mem
  obtain ⟨Hz_omega, Hz_sup⟩ := Hz_mem
  -- Hz_sup : ctx ≤ ⨆ z', z' ∈ η ⊓ pair z' z ∈ f
  apply le_trans (le_inf Hz_sup le_rfl)
  apply bv_cases_left; intro z'
  -- ctx1 = (z' ∈ η ⊓ pair z' z ∈ f) ⊓ ctx
  have Hz'_mem_η : (z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η omega f) ≤ z' ∈ᴮ η :=
    inf_le_left.trans inf_le_left
  have Hpz'z_mem : (z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η omega f) ≤ pair z' z ∈ᴮ f :=
    inf_le_left.trans inf_le_right
  -- Get w' from exists_two: z' ∈ η → ∃ w', w' ∈ η ∧ (z' ∈ w' ∨ w' ∈ z')
  have H_et : (z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η omega f) ≤
      ⨆ w', w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z') :=
    le_trans (le_inf (inf_le_right.trans (inf_le_left.trans (H_exists_two.trans (iInf_le _ z'))))
      Hz'_mem_η) bv_imp_elim
  -- H_et : ctx1 ≤ ⨆ w', w' ∈ η ⊓ (z' ∈ w' ⊔ w' ∈ z')
  apply le_trans (le_inf H_et le_rfl)
  apply bv_cases_left; intro w'
  -- ctx2 = (w' ∈ η ⊓ (z'∈w' ⊔ w'∈z')) ⊓ ctx1
  -- Case split on z' ∈ w' or w' ∈ z'
  apply le_trans (le_inf (inf_le_left.trans inf_le_right) le_rfl)
  apply bv_or_elim_left
  · -- Case z' ∈ w': ctx3 = (z' ∈ w') ⊓ ctx2
    -- Extractions: w'∈η=ir.il.il, z'∈w'=il, pair z'z∈f=ir.il.ir, H_eq at ir.ir.ir.ir.H_eq
    -- H_func(η) at ir.ir.ir.il.bv_and_left_Hη_inj
    have Hw'_mem_η : (z' ∈ᴮ w') ⊓
        ((w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) ⊓
         ((z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η omega f))) ≤ w' ∈ᴮ η :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have Hfunc2 : (z' ∈ᴮ w') ⊓
        ((w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) ⊓
         ((z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η omega f))) ≤ is_function η omega f :=
      inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (bv_and_left Hη_inj))))
    -- Goal: ctx3 ≤ z ∈ image ρ omega g
    -- Use sub_image_left for ρ: pair z (f_η(w')) ∈ ind_eps_ρ → z ∈ image ρ omega g
    apply induced_epsilon_rel_sub_image_left
    · -- H_func for ρ: ctx3 ≤ is_function ρ omega g
      -- ctx3.ir.ir.ir.il = Γ → bv_and_left Hρ_inj
      exact inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (bv_and_left Hρ_inj))))
    · -- pair z (f_η(w')) ∈ ind_eps_ρ (via rewrite ind_eps_η → ind_eps_ρ using H_eq)
      exact bv_rw' (ϕ := fun r => pair z (function_eval Hfunc2 w' Hw'_mem_η) ∈ᴮ r)
        (h_congr := B_ext_mem_right)
        (bv_symm (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans H_eq)))))
        (H_new := by
          rw [mem_induced_epsilon_rel_iff Hfunc2]
          -- z∈omega: ctx3.ir.ir.ir.Hz_omega (3 rights, then Hz_omega which has LHS Γ⊓z∈image)
          refine ⟨inf_le_right.trans (inf_le_right.trans (inf_le_right.trans Hz_omega)),
                 function_eval_mem_codomain, ?_⟩
          -- z'∈η: ctx3.ir.ir.il.il
          apply bv_use z'; refine le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))) ?_
          apply bv_use w'; refine le_inf Hw'_mem_η ?_
          -- pair z' z ∈ f: ctx3.ir.ir.il.ir
          exact le_inf (le_inf (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))) function_eval_pair_mem)
                       inf_le_left)
  · -- Case w' ∈ z': ctx3' = (w' ∈ z') ⊓ ctx2
    have Hz'_mem_η' : (w' ∈ᴮ z') ⊓
        ((w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) ⊓
         ((z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η omega f))) ≤ z' ∈ᴮ η :=
      inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_left))
    have Hw'_mem_η' : (w' ∈ᴮ z') ⊓
        ((w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) ⊓
         ((z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η omega f))) ≤ w' ∈ᴮ η :=
      inf_le_right.trans (inf_le_left.trans inf_le_left)
    have Hfunc2' : (w' ∈ᴮ z') ⊓
        ((w' ∈ᴮ η ⊓ (z' ∈ᴮ w' ⊔ w' ∈ᴮ z')) ⊓
         ((z' ∈ᴮ η ⊓ pair z' z ∈ᴮ f) ⊓ (Γ ⊓ z ∈ᴮ image η omega f))) ≤ is_function η omega f :=
      inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (bv_and_left Hη_inj))))
    -- Goal: ctx3' ≤ z ∈ image ρ omega g
    apply induced_epsilon_rel_sub_image_right
    · -- H_func for ρ: ctx3'.ir.ir.ir.il.bv_and_left_Hρ_inj
      exact inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans (bv_and_left Hρ_inj))))
    · -- pair (f_η(w')) z ∈ ind_eps_ρ (via rewrite using H_eq)
      exact bv_rw' (ϕ := fun r => pair (function_eval Hfunc2' w' Hw'_mem_η') z ∈ᴮ r)
        (h_congr := B_ext_mem_right)
        (bv_symm (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans H_eq)))))
        (H_new := by
          rw [mem_induced_epsilon_rel_iff Hfunc2']
          refine ⟨function_eval_mem_codomain,
                 inf_le_right.trans (inf_le_right.trans (inf_le_right.trans Hz_omega)), ?_⟩
          apply bv_use w'; apply le_inf Hw'_mem_η'
          apply bv_use z'; apply le_inf Hz'_mem_η'
          -- pair z'z∈f: ctx3'.ir.ir.il.ir; w'∈z': il
          exact le_inf (le_inf function_eval_pair_mem (inf_le_right.trans (inf_le_right.trans (inf_le_left.trans inf_le_right))))
                       inf_le_left)

-- src/aleph_one.lean:503
lemma image_eq_of_eq_induced_epsilon_rel
    {η ρ f g : bSet 𝔹} {Γ}
    (Hη_inj : Γ ≤ is_injective_function η omega f)
    (Hρ_inj : Γ ≤ is_injective_function ρ omega g)
    (H_eq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (H_exists_two : Γ ≤ exists_two η)
    (H_exists_two' : Γ ≤ exists_two ρ) :
    Γ ≤ image η omega f =ᴮ image ρ omega g := by
  refine mem_ext ?_ ?_
  · apply image_eq_of_eq_induced_epsilon_rel_aux Hη_inj Hρ_inj H_eq H_exists_two
  · apply image_eq_of_eq_induced_epsilon_rel_aux Hρ_inj Hη_inj (bv_symm H_eq) H_exists_two'

-- src/aleph_one.lean:515
lemma eq_of_eq_induced_epsilon_rel
    {η ρ f g : bSet 𝔹} {Γ}
    (Hη_ord : Γ ≤ Ord η) (Hρ_ord : Γ ≤ Ord ρ)
    (Hη_inj : Γ ≤ is_injective_function η omega f)
    (Hρ_inj : Γ ≤ is_injective_function ρ omega g)
    (H_eq : Γ ≤ induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel ρ omega g)
    (H_exists_two : Γ ≤ exists_two η)
    (H_exists_two' : Γ ≤ exists_two ρ) :
    Γ ≤ η =ᴮ ρ := by
  -- Suffices: construct an eps_iso η ρ h, then apply eq_of_Ord_eps_iso
  suffices H_eps : Γ ≤ ⨆ h, eps_iso η ρ h from eq_of_Ord_eps_iso Hη_ord Hρ_ord H_eps
  -- Step 1: Build the components
  -- f_factor : η → image(η,ω,f), inj
  have Hf_factor := factor_image_is_injective_function Hη_inj
  -- g_inverse : image(ρ,ω,g) → ρ, inj
  have Hg_inv := @injective_function_inverse_is_injective_function _ _ _ _ _ _ Hρ_inj
  -- image(η) = image(ρ) from H_eq and exists_two conditions
  have H_img_eq : Γ ≤ image η omega f =ᴮ image ρ omega g :=
    image_eq_of_eq_induced_epsilon_rel Hη_inj Hρ_inj H_eq H_exists_two H_exists_two'
  -- g_inverse_rw : is_injective_function (image η ω f) ρ g⁻¹
  -- (rewrite image(ρ) to image(η) in g_inverse's domain type)
  have Hg_inv_rw : Γ ≤ is_injective_function (image η omega f) ρ
      (injective_function_inverse Hρ_inj) :=
    bv_rw' (H := H_img_eq) (h_congr := B_ext_is_injective_function_left)
      (H_new := Hg_inv)
  -- Step 2: Let h = comp(f_factor, g_inverse_rw)
  apply le_iSup_of_le (injective_function_comp Hf_factor Hg_inv_rw)
  -- Step 3: Show eps_iso η ρ h = is_function ⊓ strong_eps_hom ⊓ is_surj
  refine le_inf (le_inf ?_ ?_) ?_
  · -- is_function η ρ h
    exact injective_function_comp_is_function
  · -- strong_eps_hom η ρ h
    rw [strong_eps_hom_iff]
    intro Γ' H_le z₁ Hz₁_η z₂ Hz₂_η w₁ Hw₁_ρ w₂ Hw₂_ρ Hpr₁ Hpr₂
    -- Hpr₁ : pair z₁ w₁ ∈ h = comp(f_factor, g_inv_rw)
    -- Hpr₂ : pair z₂ w₂ ∈ h
    -- Unfold comp membership to get intermediate elements v₁, v₂ ∈ image(η)
    have Hf_func := is_func'_of_is_injective_function (H_le.trans Hf_factor)
    have Hg_func := is_func'_of_is_injective_function (H_le.trans Hg_inv_rw)
    have H_mem₁ := (mem_is_func'_comp_iff Hf_func Hg_func).mp Hpr₁
    have H_mem₂ := (mem_is_func'_comp_iff Hf_func Hg_func).mp Hpr₂
    -- H_mem₁ : z₁ ∈ η ∧ w₁ ∈ ρ ∧ ⨆ v₁, v₁ ∈ image(η) ⊓ (pair z₁ v₁ ∈ f ⊓ pair v₁ w₁ ∈ g⁻¹)
    obtain ⟨_, _, H_v₁_ex⟩ := H_mem₁
    obtain ⟨_, _, H_v₂_ex⟩ := H_mem₂
    obtain ⟨v₁, Hv₁⟩ := exists_convert H_v₁_ex
      (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))
    obtain ⟨v₂, Hv₂⟩ := exists_convert H_v₂_ex
      (B_ext_inf B_ext_mem_left (B_ext_inf B_ext_pair_mem_right B_ext_pair_mem_left))
    -- v₁, v₂ ∈ image(η) ⊓ (pair z₁ v₁ ∈ f ⊓ pair v₁ w₁ ∈ g⁻¹)
    have Hv₁_img : Γ' ≤ v₁ ∈ᴮ image η omega f := Hv₁.trans inf_le_left
    have Hv₁_f : Γ' ≤ pair z₁ v₁ ∈ᴮ f := Hv₁.trans (inf_le_right.trans inf_le_left)
    have Hv₁_ginv : Γ' ≤ pair v₁ w₁ ∈ᴮ injective_function_inverse Hρ_inj :=
      Hv₁.trans (inf_le_right.trans inf_le_right)
    have Hv₂_img : Γ' ≤ v₂ ∈ᴮ image η omega f := Hv₂.trans inf_le_left
    have Hv₂_f : Γ' ≤ pair z₂ v₂ ∈ᴮ f := Hv₂.trans (inf_le_right.trans inf_le_left)
    have Hv₂_ginv : Γ' ≤ pair v₂ w₂ ∈ᴮ injective_function_inverse Hρ_inj :=
      Hv₂.trans (inf_le_right.trans inf_le_right)
    -- pair v₁ w₁ ∈ g⁻¹ → pair w₁ v₁ ∈ g (by mem_inj_inverse_iff)
    have Hg_func₀ := is_func'_of_is_injective_function (H_le.trans Hρ_inj)
    have Hg_inj₀ := is_inj_of_is_injective_function (H_le.trans Hρ_inj)
    have Hw₁_v₁ := (mem_inj_inverse_iff Hg_func₀ Hg_inj₀).mp Hv₁_ginv
    have Hw₂_v₂ := (mem_inj_inverse_iff Hg_func₀ Hg_inj₀).mp Hv₂_ginv
    -- Hw₁_v₁ : w₁ ∈ ρ ∧ v₁ ∈ omega ∧ pair w₁ v₁ ∈ g
    -- Hw₂_v₂ : w₂ ∈ ρ ∧ v₂ ∈ omega ∧ pair w₂ v₂ ∈ g
    have Hpair_w₁v₁_g := Hw₁_v₁.2.2
    have Hpair_w₂v₂_g := Hw₂_v₂.2.2
    -- v₁, v₂ ∈ image(η) = image(ρ) (via H_img_eq)
    -- Actually, key: show v₁ ∈ v₂ ↔ z₁ ∈ z₂ ↔ w₁ ∈ w₂
    -- z₁ ∈ z₂ → v₁ ∈ v₂: from induced_epsilon_rel η omega f
    -- v₁ ∈ v₂ → w₁ ∈ w₂: from induced_epsilon_rel ρ omega g (via H_eq)
    constructor
    · -- Forward: z₁ ∈ z₂ → w₁ ∈ w₂
      intro Hz₁z₂
      -- pair v₁ v₂ ∈ induced_epsilon_rel η ω f (since z₁∈η, z₂∈η, pair z₁v₁∈f, pair z₂v₂∈f, z₁∈z₂)
      have Hv₁_omega : Γ' ≤ v₁ ∈ᴮ omega :=
        mem_of_mem_subset (H_le.trans image_subset) Hv₁_img
      have Hv₂_omega : Γ' ≤ v₂ ∈ᴮ omega :=
        mem_of_mem_subset (H_le.trans image_subset) Hv₂_img
      have Hpair_v₁v₂_ind_η : Γ' ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel η omega f := by
        rw [mem_induced_epsilon_rel_iff (H_le.trans (bv_and_left Hη_inj))]
        exact ⟨Hv₁_omega, Hv₂_omega,
               le_iSup_of_le z₁ (le_inf Hz₁_η (le_iSup_of_le z₂
                 (le_inf Hz₂_η (le_inf (le_inf Hv₁_f Hv₂_f) Hz₁z₂))))⟩
      -- pair v₁ v₂ ∈ induced_epsilon_rel ρ ω g (via H_eq)
      have Hpair_v₁v₂_ind_ρ : Γ' ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel ρ omega g :=
        bv_rw' (H := H_le.trans (bv_symm H_eq)) (h_congr := B_ext_mem_right)
          (H_new := Hpair_v₁v₂_ind_η)
      -- From pair v₁ v₂ ∈ ind_ρ with pair w₁ v₁ ∈ g and pair w₂ v₂ ∈ g: w₁ ∈ w₂
      exact mem_of_mem_induced_epsilon_rel (H_le.trans Hρ_inj) Hpair_w₁v₁_g Hpair_w₂v₂_g
        Hpair_v₁v₂_ind_ρ
    · -- Backward: w₁ ∈ w₂ → z₁ ∈ z₂
      intro Hw₁w₂
      -- pair v₁ v₂ ∈ induced_epsilon_rel ρ ω g (since w₁∈ρ, w₂∈ρ, pair w₁v₁∈g, pair w₂v₂∈g, w₁∈w₂)
      have Hv₁_omega : Γ' ≤ v₁ ∈ᴮ omega := Hw₁_v₁.2.1
      have Hv₂_omega : Γ' ≤ v₂ ∈ᴮ omega := Hw₂_v₂.2.1
      have Hpair_v₁v₂_ind_ρ : Γ' ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel ρ omega g := by
        rw [mem_induced_epsilon_rel_iff (H_le.trans (bv_and_left Hρ_inj))]
        exact ⟨Hv₁_omega, Hv₂_omega,
               le_iSup_of_le w₁ (le_inf Hw₁_ρ (le_iSup_of_le w₂
                 (le_inf Hw₂_ρ (le_inf (le_inf Hpair_w₁v₁_g Hpair_w₂v₂_g) Hw₁w₂))))⟩
      -- pair v₁ v₂ ∈ induced_epsilon_rel η ω f (via H_eq symm)
      have Hpair_v₁v₂_ind_η : Γ' ≤ pair v₁ v₂ ∈ᴮ induced_epsilon_rel η omega f :=
        bv_rw' (H := H_le.trans H_eq) (h_congr := B_ext_mem_right)
          (H_new := Hpair_v₁v₂_ind_ρ)
      -- From pair v₁ v₂ ∈ ind_η with pair z₁ v₁ ∈ f and pair z₂ v₂ ∈ f: z₁ ∈ z₂
      exact mem_of_mem_induced_epsilon_rel (H_le.trans Hη_inj) Hv₁_f Hv₂_f
        Hpair_v₁v₂_ind_η
  · -- is_surj η ρ h
    -- h = comp(f_factor, g_inv_rw)
    -- f_factor is surjective onto image(η) (surj_image)
    -- g_inv_rw is surjective onto ρ (injective_function_inverse_is_injective_function's surjectivity)
    apply is_func'_comp_surj
      (is_func'_of_is_injective_function Hf_factor)
      (is_func'_of_is_injective_function Hg_inv_rw)
    · -- f_factor is surjective η → image(η)
      exact surj_image (is_func'_of_is_injective_function Hη_inj)
    · -- g_inv_rw is surjective image(η) → ρ
      -- inj_inverse_is_surj gives: is_surj (image ρ omega g) ρ (inj_inverse)
      -- After rewriting image(ρ) = image(η) via H_img_eq:
      apply bv_rw' (H := H_img_eq)
        (ϕ := fun z => is_surj z ρ (injective_function_inverse Hρ_inj))
        (h_congr := B_ext_iInf (h := fun _ => B_ext_imp (h₁ := B_ext_const) (h₂ :=
          B_ext_iSup (h := fun w => B_ext_inf (h₁ := B_ext_mem_right) (h₂ := B_ext_const)))))
      exact inj_inverse_is_surj
        (is_func'_of_is_injective_function Hρ_inj)
        (is_inj_of_is_injective_function Hρ_inj)

end well_ordering

-- ============================================================
-- src/aleph_one.lean:583-888: section a1
-- ============================================================

section a1

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/aleph_one.lean:586
-- The comprehension predicate for a1
noncomputable def a1' : bSet 𝔹 :=
  comprehend
    (fun x : bSet 𝔹 => ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓
      (image (mem_rel η) (prod omega omega) (prod_map_self η omega f) =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ)
    (bv_powerset (prod omega omega))

-- src/aleph_one.lean:612
lemma a1'_AE {Γ : 𝔹} : Γ ≤ ⨅ z, z ∈ᴮ a1' ⟹
    ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓
    image (mem_rel η) (prod omega omega) (prod_map_self η omega f) =ᴮ z ⊓ (z =ᴮ ∅)ᶜ := by
  -- B_ext for ϕ (changing the last argument x)
  have H_congr : B_ext (fun x : bSet 𝔹 =>
      ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓
      (image (mem_rel η) (prod omega omega) (prod_map_self η omega f) =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ) :=
    B_ext_iSup (h := fun η => B_ext_inf (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun f => B_ext_inf
        (h₁ := B_ext_inf (h₁ := B_ext_const) (h₂ := B_ext_bv_eq_right))
        (h₂ := B_ext_neg (h := B_ext_bv_eq_left)))))
  apply le_iInf; intro z; rw [← deduction]
  -- From z ∈ a1' (= comprehend ϕ' (bv_powerset...)), use mem_comprehend_iff
  have H_from : Γ ⊓ z ∈ᴮ (a1' : bSet 𝔹) ≤ z ∈ᴮ (a1' : bSet 𝔹) := inf_le_right
  -- a1' is definitionally equal to comprehend ϕ' (bv_powerset (prod ω ω))
  -- Use mem_comprehend_iff to convert z ∈ a1' to ⨆ χ, ...
  -- Since a1' = comprehend ... by def, mem_comprehend_iff applies directly
  rw [show (a1' : bSet 𝔹) = comprehend
      (fun x : bSet 𝔹 => ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓
        (image (mem_rel η) (prod omega omega) (prod_map_self η omega f) =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ)
      (bv_powerset (prod omega omega)) from rfl] at H_from
  rw [mem_comprehend_iff] at H_from
  apply le_trans (le_inf H_from le_rfl)
  apply bv_cases_left; intro χ
  -- ctx: (bv_powerset...).bval χ ⊓ (z =ᴮ w ⊓ ϕ' w) ⊓ Γ, where w = (bv_powerset...).func χ
  -- The type is: (bv_powerset (prod omega omega)).bval χ ⊓
  --   (z =ᴮ (bv_powerset (prod omega omega)).func χ ⊓ (⨆ η, ...)) ⊓ Γ ≤ ⨆ η, ...
  -- h_zeq: ctx ≤ z =ᴮ w  (from the left ⊓ part)
  -- h_phi: ctx ≤ ϕ' w (the nested ⨆ expression)
  -- Apply H_congr: ϕ' w ≤ ϕ' z given w =ᴮ z
  refine le_trans (le_inf ?_ ?_) (H_congr ((bv_powerset (prod omega omega)).func χ) z)
  · -- Need: ctx ≤ (bv_powerset...).func χ =ᴮ z
    -- from inf_le_left (bval ⊓ (z=w ⊓ ϕ'w)) gives z=w; bv_symm gives w=z
    exact bv_symm (inf_le_left.trans (inf_le_right.trans inf_le_left))
  · -- Need: ctx ≤ ϕ' w (the outer ⨆ at w = func χ)
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)

-- src/aleph_one.lean:597: the predicate: a1_ψ v x holds when x is an ordinal injecting into ω
-- with induced epsilon relation on ω equal to v, and v ≠ ∅
private def a1_ψ {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] (v x : bSet 𝔹) : 𝔹 :=
  Ord x ⊓ (⨆ f, is_injective_function x omega f ⊓
    image (mem_rel x) (prod omega omega) (prod_map_self x omega f) =ᴮ v) ⊓ (v =ᴮ ∅)ᶜ

private lemma B_ext_a1_ψ {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
    {v : bSet 𝔹} : B_ext (a1_ψ v) := by
  unfold a1_ψ
  refine B_ext_inf (h₁ := B_ext_inf (h₁ := B_ext_Ord) (h₂ := ?_)) (h₂ := B_ext_const)
  -- B_ext (fun x => ⨆ f, is_injective_function x omega f ⊓
  --                  image (mem_rel x) (prod omega omega) (prod_map_self x omega f) =ᴮ v)
  -- For each fixed f (iSup variable), show B_ext in x
  apply B_ext_iSup; intro f
  apply B_ext_inf B_ext_is_injective_function_left
  -- B_ext (fun x => image (mem_rel x) (prod omega omega) (prod_map_self x omega f) =ᴮ v)
  -- = B_ext_term with ϕ = (fun w => w =ᴮ v) and t = (fun x => image(mem_rel x)(prod ω ω)(pm(x,ω,f)))
  apply B_ext_term (ϕ := fun w => w =ᴮ v) (t := fun x => image (mem_rel x) (prod omega omega) (prod_map_self x omega f)) B_ext_bv_eq_left
  -- B_congr (fun x => image (mem_rel x) (prod omega omega) (prod_map_self x omega f))
  intro x₁ x₂ Γ Hxy
  -- Step 1: image(mem_rel x₁)(prod ω ω)(pm(x₁)) =ᴮ image(mem_rel x₂)(prod ω ω)(pm(x₁))
  have h1 : Γ ≤ image (mem_rel x₁) (prod omega omega) (prod_map_self x₁ omega f) =ᴮ
      image (mem_rel x₂) (prod omega omega) (prod_map_self x₁ omega f) :=
    B_congr_image_left (B_congr_mem_rel Hxy)
  -- Step 2: image(mem_rel x₂)(prod ω ω)(pm(x₁)) =ᴮ image(mem_rel x₂)(prod ω ω)(pm(x₂))
  have h2 : Γ ≤ image (mem_rel x₂) (prod omega omega) (prod_map_self x₁ omega f) =ᴮ
      image (mem_rel x₂) (prod omega omega) (prod_map_self x₂ omega f) :=
    B_congr_image_right (B_congr_prod_map_self_left Hxy)
  exact le_trans (le_inf h1 h2) bv_eq_trans

-- src/aleph_one.lean:620
-- a1_func χ: the ordinal x such that a1_ψ (a1'.func χ) x holds
noncomputable def a1_func (χ : (a1' (𝔹 := 𝔹)).type) : bSet 𝔹 :=
  (AE_convert' (a1_ψ (𝔹 := 𝔹)) (fun v => B_ext_a1_ψ) a1' ((a1' (𝔹 := 𝔹)).func χ)).choose

-- Convert a1'_AE to the form needed by AE_convert'
private lemma a1'_AE_psi {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹] {Γ : 𝔹} :
    Γ ≤ ⨅ z, z ∈ᴮ (a1' (𝔹 := 𝔹)) ⟹ ⨆ w, a1_ψ z w := by
  apply le_iInf; intro z; rw [← deduction]
  -- Get ⨆ η, Ord η ⊓ ⨆ f, ...(η)... ⊓ (z=∅)ᶜ from a1'_AE
  have H : Γ ⊓ z ∈ᴮ (a1' (𝔹 := 𝔹)) ≤ ⨆ η, Ord η ⊓ ⨆ f, is_injective_function η omega f ⊓
      image (mem_rel η) (prod omega omega) (prod_map_self η omega f) =ᴮ z ⊓ (z =ᴮ ∅)ᶜ :=
    le_trans (le_inf (a1'_AE.trans (iInf_le _ z)) inf_le_right) bv_imp_elim
  apply le_trans H; apply iSup_le; intro η; apply le_iSup_of_le η
  -- Convert: Ord η ⊓ (⨆ f, A f ⊓ C) ≤ a1_ψ z η = Ord η ⊓ (⨆ f, A f) ⊓ C
  -- where C = (z =ᴮ ∅)ᶜ (doesn't depend on f)
  unfold a1_ψ
  -- LHS: Ord η ⊓ (⨆ f, (inj_fun η ω f ⊓ img =ᴮ z) ⊓ (z=∅)ᶜ)
  -- RHS: Ord η ⊓ (⨆ f, inj_fun ω f ⊓ img =ᴮ z) ⊓ (z=∅)ᶜ
  refine le_inf (le_inf inf_le_left (le_trans inf_le_right ?_)) (le_trans inf_le_right ?_)
  · -- ⨆ f, (A f ⊓ C) ≤ ⨆ f, A f
    exact iSup_le (fun f => le_iSup_of_le f inf_le_left)
  · -- ⨆ f, (A f ⊓ C) ≤ C
    exact iSup_le (fun f => inf_le_right)

-- Spec for a1_func
lemma a1_func_spec {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]
    {χ : (a1' (𝔹 := 𝔹)).type} {Γ : 𝔹}
    (H_mem : Γ ≤ (a1' (𝔹 := 𝔹)).func χ ∈ᴮ (a1' (𝔹 := 𝔹))) :
    Γ ≤ a1_ψ ((a1' (𝔹 := 𝔹)).func χ) (a1_func χ) :=
  (AE_convert' (a1_ψ (𝔹 := 𝔹)) (fun v => B_ext_a1_ψ) a1' ((a1' (𝔹 := 𝔹)).func χ)).choose_spec
    a1'_AE_psi H_mem

-- src/aleph_one.lean:630
noncomputable def a1_aux : bSet 𝔹 := ⟨(a1' (𝔹 := 𝔹)).type, a1_func, (a1' (𝔹 := 𝔹)).bval⟩

-- src/aleph_one.lean:632
lemma Ord_of_mem_a1_aux {Γ : 𝔹} {η : bSet 𝔹} (H_mem : Γ ≤ η ∈ᴮ a1_aux) : Γ ≤ Ord η := by
  rw [mem_unfold] at H_mem; apply le_trans H_mem; apply iSup_le; intro χ
  -- a1_aux.func χ = a1_func χ (the ordinal extracted by classical choice)
  -- a1'.bval χ ≤ (a1'.func χ) ∈ a1' → a1_ψ (a1'.func χ) (a1_func χ)
  -- a1_ψ includes Ord (a1_func χ), so we get Ord (a1_func χ)
  -- We need: a1'.bval χ ⊓ η =ᴮ a1_func χ ≤ Ord η
  -- From a1_func_spec (using H_mem' : a1'.func χ ∈ a1' from mem_mk''):
  have H_mem' : (a1' (𝔹 := 𝔹)).bval χ ≤ (a1' (𝔹 := 𝔹)).func χ ∈ᴮ a1' := mem_mk' a1' χ
  have H_spec : (a1' (𝔹 := 𝔹)).bval χ ≤ a1_ψ ((a1' (𝔹 := 𝔹)).func χ) (a1_func χ) :=
    a1_func_spec H_mem'
  have H_ord : (a1' (𝔹 := 𝔹)).bval χ ≤ Ord (a1_func χ) :=
    H_spec.trans (inf_le_left.trans inf_le_left)
  -- η =ᴮ a1_func χ and Ord (a1_func χ) → Ord η
  exact le_trans (le_inf (bv_symm inf_le_right) (le_trans inf_le_left H_ord)) (B_ext_Ord _ _)

-- src/aleph_one.lean:641
noncomputable def a1 : bSet 𝔹 := insert 0 (insert 1 a1_aux)

-- src/aleph_one.lean:643
lemma mem_a1_iff₀ {z : bSet 𝔹} {Γ : 𝔹} :
    Γ ≤ z ∈ᴮ a1 ↔ Γ ≤ z =ᴮ 0 ⊔ z =ᴮ 1 ⊔ z ∈ᴮ a1_aux := by
  simp only [a1, mem_insert1, sup_assoc]

-- src/aleph_one.lean:646
lemma Ord_of_mem_a1 {Γ : 𝔹} {η : bSet 𝔹} (H_mem : Γ ≤ η ∈ᴮ a1) : Γ ≤ Ord η := by
  rw [mem_a1_iff₀] at H_mem; apply le_trans H_mem; apply sup_le; apply sup_le
  · exact le_trans (le_inf (bv_symm le_rfl) (le_trans le_top (le_top.trans Ord_zero)))
      (B_ext_Ord _ _)
  · exact le_trans (le_inf (bv_symm le_rfl) (le_trans le_top (le_top.trans Ord_one)))
      (B_ext_Ord _ _)
  · exact Ord_of_mem_a1_aux le_rfl

-- src/aleph_one.lean:655
lemma eq_zero_iff_eq_empty {Γ : 𝔹} {u : bSet 𝔹} : Γ ≤ u =ᴮ 0 ↔ Γ ≤ u =ᴮ ∅ := by
  constructor
  · intro H
    exact le_trans (le_inf H (zero_eq_empty (Γ := Γ))) bv_eq_trans
  · intro H
    exact le_trans (le_inf H (bv_symm (zero_eq_empty (Γ := Γ)))) bv_eq_trans

-- src/aleph_one.lean:662
lemma induced_rel_empty_of_eq_zero {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η omega f)
    (H_eq_zero : Γ ≤ η =ᴮ 0) : Γ ≤ induced_epsilon_rel η omega f =ᴮ ∅ := by
  rw [empty_iff_forall_not_mem]
  apply le_iInf; intro pr
  rw [← imp_bot, ← deduction]
  -- goal: Γ ⊓ pr ∈ᴮ induced_epsilon_rel η omega f ≤ ⊥
  set Γ' := Γ ⊓ pr ∈ᴮ induced_epsilon_rel η omega f
  have H_mem' : Γ' ≤ pr ∈ᴮ induced_epsilon_rel η omega f := inf_le_right
  have H_func' : Γ' ≤ is_function η omega f := le_trans inf_le_left H_func
  obtain ⟨a, _b, _, _, _, Hab⟩ := eq_pair_of_mem_induced_epsilon_rel H_mem'
  have Ha_img : Γ' ≤ a ∈ᴮ image η omega f :=
    induced_epsilon_rel_sub_image_left H_func' Hab
  rw [mem_image_iff] at Ha_img
  have H_eq_empty : Γ' ≤ η =ᴮ ∅ :=
    eq_zero_iff_eq_empty.mp (le_trans inf_le_left H_eq_zero)
  have H_notz : Γ' ≤ ⨅ z, (z ∈ᴮ η)ᶜ := empty_iff_forall_not_mem.mp H_eq_empty
  apply bv_absurd (⨆ z, z ∈ᴮ η ⊓ pair z a ∈ᴮ f) Ha_img.2
  rw [compl_iSup]
  apply le_iInf; intro z
  exact le_trans (le_trans H_notz (iInf_le _ z)) (compl_le_compl inf_le_left)

-- src/aleph_one.lean:679
lemma nonempty_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η omega f)
    (H : Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ) : Γ ≤ (η =ᴮ ∅)ᶜ := by
  rw [← imp_bot, ← deduction]
  -- goal: Γ ⊓ (η =ᴮ ∅) ≤ ⊥
  have H_eq_zero : Γ ⊓ (η =ᴮ ∅) ≤ induced_epsilon_rel η omega f =ᴮ ∅ :=
    induced_rel_empty_of_eq_zero (le_trans inf_le_left H_func)
      (eq_zero_iff_eq_empty.mpr inf_le_right)
  exact bv_absurd _ H_eq_zero (le_trans inf_le_left H)

-- src/aleph_one.lean:690
lemma not_zero_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η omega f)
    (H' : Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ) : Γ ≤ (η =ᴮ 0)ᶜ := by
  rw [← imp_bot, ← deduction]
  -- goal: Γ ⊓ (η =ᴮ 0) ≤ ⊥
  have H_rel_empty : Γ ⊓ (η =ᴮ 0) ≤ induced_epsilon_rel η omega f =ᴮ ∅ :=
    induced_rel_empty_of_eq_zero (le_trans inf_le_left H_func) inf_le_right
  exact bv_absurd _ H_rel_empty (le_trans inf_le_left H')

-- src/aleph_one.lean:700
lemma not_one_of_induced_rel_nonempty {η f : bSet 𝔹} {Γ : 𝔹}
    (H_func : Γ ≤ is_function η omega f)
    (H : Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ) : Γ ≤ (η =ᴮ 1)ᶜ := by
  -- Proof: assume η = 1. Get pr ∈ induced_epsilon_rel. Get a', b' s.t. a' ∈ b'.
  -- Then a' ∈ η = 1 → a' = 0, b' ∈ η = 1 → b' = 0. So 0 ∈ 0, contradiction.
  rw [← imp_bot, ← deduction]
  -- Goal: Γ ⊓ (η =ᴮ 1) ≤ ⊥
  -- Extract pr from the nonempty induced_epsilon_rel
  have H' : Γ ⊓ (η =ᴮ 1) ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ := inf_le_left.trans H
  rw [nonempty_iff_exists_mem] at H'
  apply le_trans (le_inf H' le_rfl)
  apply bv_cases_left; intro pr
  -- ctx₀ = pr ∈ ind_eps ⊓ (Γ ⊓ η=1)
  have H_pr_mem₀ := @inf_le_left 𝔹 _ (pr ∈ᴮ induced_epsilon_rel η omega f) (Γ ⊓ (η =ᴮ 1))
  have H_func₀ : (pr ∈ᴮ induced_epsilon_rel η omega f) ⊓ (Γ ⊓ (η =ᴮ 1)) ≤ is_function η omega f :=
    @inf_le_right 𝔹 _ (pr ∈ᴮ induced_epsilon_rel η omega f) (Γ ⊓ (η =ᴮ 1)) |>.trans
      (inf_le_left.trans H_func)
  obtain ⟨a, b, _, _, _, H_pair_mem⟩ := eq_pair_of_mem_induced_epsilon_rel H_pr_mem₀
  rw [mem_induced_epsilon_rel_iff H_func₀] at H_pair_mem
  obtain ⟨_, _, H_sup⟩ := H_pair_mem
  apply le_trans (le_inf H_sup le_rfl)
  apply bv_cases_left; intro a'
  apply le_trans (le_inf (inf_le_left.trans inf_le_right) le_rfl)
  apply bv_cases_left; intro b'
  -- ctx: (b'∈η ⊓ (pa'a∈f ⊓ pb'b∈f ⊓ a'∈b')) ⊓ ((a'∈η ⊓ ⨆b',...) ⊓ (pr∈ind_eps ⊓ (Γ⊓η=1)))
  -- Goal: this ctx ≤ ⊥
  -- Derive 0 ∈ 0:
  -- 1. a' ∈ η: ir.il.il, b' ∈ η: il.il
  -- 2. η = 1: ir.ir.ir.ir (to Γ⊓η=1, then right = η=1)
  -- 3. a' ∈ 1: from a'∈η and η=1
  -- 4. a' = 0, b' = 0: eq_zero_of_mem_one
  -- 5. a' ∈ b': il.ir.ir
  -- 6. 0 ∈ 0: mem_congr
  -- Derive 0 ∈ 0 and use bot_of_mem_self'
  -- Paths in ctx: (b'∈η ⊓ (pa'a∈f ⊓ pb'b∈f ⊓ a'∈b')) ⊓ ((a'∈η ⊓ ⨆b',...) ⊓ (pr∈ ⊓ (Γ ⊓ η=1)))
  -- a' ∈ η: ir.il.il (3 steps)
  -- b' ∈ η: il.il (2 steps)
  -- η = 1: ir.ir.ir.ir (4 steps)
  -- a' ∈ b': il.ir.ir (3 steps)
  apply bot_of_mem_self'
  apply mem_congr
  · -- ctx ≤ 0 =ᴮ 0 for the "element" (a' =ᴮ 0)
    exact eq_zero_of_mem_one (mem_congr bv_refl
      (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
      (inf_le_right.trans (inf_le_left.trans inf_le_left)))
  · -- ctx ≤ 0 =ᴮ 0 for the "set" (b' =ᴮ 0)
    exact eq_zero_of_mem_one (mem_congr bv_refl
      (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
      (inf_le_left.trans inf_le_left))
  · -- ctx ≤ a' ∈ b' (becomes 0 ∈ 0 after rewriting)
    exact inf_le_left.trans (inf_le_right.trans inf_le_right)

-- src/aleph_one.lean:723
lemma nonempty_induced_rel_iff_not_zero_and_not_one {η f : bSet 𝔹} {Γ : 𝔹}
    (H_ord : Γ ≤ Ord η) (H_inj : Γ ≤ is_function η omega f) :
    Γ ≤ (induced_epsilon_rel η omega f =ᴮ ∅)ᶜ ↔
    (Γ ≤ (η =ᴮ 0)ᶜ ∧ Γ ≤ (η =ᴮ 1)ᶜ) := by
  constructor
  · intro H
    exact ⟨not_zero_of_induced_rel_nonempty H_inj H,
           not_one_of_induced_rel_nonempty H_inj H⟩
  · intro ⟨H₁, H₂⟩
    rw [nonempty_iff_exists_mem]
    -- Get 1 ∈ η (since η ≥ 2 ordinal-wise)
    have H_1_mem : Γ ≤ (1 : bSet 𝔹) ∈ᴮ η := one_mem_of_not_zero_and_not_one H_ord H₁ H₂
    -- Get 0 ∈ η (since 0 ∈ 1 ∈ η, and η is ordinal ↔ transitive)
    have H_0_mem : Γ ≤ (0 : bSet 𝔹) ∈ᴮ η := mem_of_mem_Ord zero_mem_one H_1_mem H_ord
    -- Apply mem_induced_epsilon_rel_of_mem with 0 ∈ η, 1 ∈ η, 0 ∈ 1
    -- Need is_function η omega f
    apply bv_use (pair (function_eval H_inj (0 : bSet 𝔹) H_0_mem) (function_eval H_inj 1 H_1_mem))
    exact mem_induced_epsilon_rel_of_mem H_0_mem H_1_mem zero_mem_one H_inj

-- src/aleph_one.lean:746
/-- a1 contains every ordinal η which injects into ω -/
lemma mem_a1_of_injects_into_omega_aux {Γ : 𝔹} {η : bSet 𝔹}
    (H_ord : Γ ≤ Ord η) (H_inj : Γ ≤ ⨆ f, is_injective_function η omega f)
    (H_not_zero : Γ ≤ (η =ᴮ 0)ᶜ) (H_not_one : Γ ≤ (η =ᴮ 1)ᶜ) :
    Γ ≤ η ∈ᴮ a1_aux := by
  -- Step 1: Extract f from H_inj using maximum_principle
  obtain ⟨f, Hf_eq⟩ := maximum_principle (fun f => is_injective_function η omega f)
    (B_ext_inf B_ext_is_function_right (B_ext_iInf (h := fun w₁ => B_ext_iInf (h := fun w₂ =>
      B_ext_iInf (h := fun v₁ => B_ext_iInf (h := fun v₂ =>
        B_ext_imp (h₁ := B_ext_inf (h₁ := B_ext_inf (h₁ := B_ext_mem_right) (h₂ := B_ext_mem_right))
          (h₂ := B_ext_const)) (h₂ := B_ext_const)))))))
  have Hf : Γ ≤ is_injective_function η omega f := Hf_eq ▸ H_inj
  -- Step 2: Let R = induced_epsilon_rel η omega f
  set R := induced_epsilon_rel η omega f
  -- Step 3: Show R ∈ a1'
  -- Need: (i) R ∈ bv_powerset (prod omega omega), (ii) ϕ' R holds
  -- (i) induced_epsilon_rel ⊆ prod omega omega (subset.mk_subset)
  -- (ii) ϕ'(R) = ∃ η', Ord η' ∧ ∃ g, inj_fun η' ω g ∧ image(mem_rel η')(prod ω ω)(pm η' ω g) =ᴮ R ∧ R ≠ ∅
  have HR_mem_a1' : Γ ≤ R ∈ᴮ (a1' : bSet 𝔹) := by
    -- a1' = comprehend ϕ' (bv_powerset (prod ω ω))
    -- use mem_comprehend_iff₂ with ϕ' being the big predicate
    rw [show (a1' (𝔹 := 𝔹)) = comprehend
        (fun x : bSet 𝔹 => ⨆ η', Ord η' ⊓ ⨆ f', is_injective_function η' omega f' ⊓
          (image (mem_rel η') (prod omega omega) (prod_map_self η' omega f') =ᴮ x) ⊓ (x =ᴮ ∅)ᶜ)
        (bv_powerset (prod omega omega)) from rfl]
    rw [mem_comprehend_iff₂
      (H_congr := B_ext_iSup (h := fun η' => B_ext_inf (h₁ := B_ext_const) (h₂ :=
        B_ext_iSup (h := fun f' => B_ext_inf
          (h₁ := B_ext_inf (h₁ := B_ext_const) (h₂ := B_ext_bv_eq_right))
          (h₂ := B_ext_neg (h := B_ext_bv_eq_left))))))]
    -- Provide witness: R itself (R ∈ bv_powerset and ϕ'(R))
    apply le_iSup_of_le R
    refine le_inf ?_ (le_inf bv_refl ?_)
    · -- R ∈ bv_powerset (prod omega omega)
      rw [mem_powerset_iff]
      -- induced_epsilon_rel = image (...) (prod omega omega) (...) ⊆ prod omega omega
      exact le_trans (le_top) (le_trans le_top image_subset)
    · -- ϕ'(R) = ⨆ η', Ord η' ⊓ ...
      apply le_iSup_of_le η
      refine le_inf H_ord ?_
      apply le_iSup_of_le f
      refine le_inf (le_inf Hf bv_refl) ?_
      -- R ≠ ∅: use nonempty_induced_rel_iff_not_zero_and_not_one
      exact ((nonempty_induced_rel_iff_not_zero_and_not_one H_ord (Hf.trans inf_le_left)).mpr
        ⟨H_not_zero, H_not_one⟩)
  -- Step 4: Show η ∈ a1_aux using the χ from R ∈ a1'
  -- Use bv_cases_left pattern to introduce χ while keeping Γ in context
  -- Goal: Γ ≤ η ∈ a1_aux = ⨆ χ : a1'.type, a1'.bval χ ⊓ η =ᴮ a1_func χ
  rw [mem_unfold] at HR_mem_a1'
  rw [mem_unfold]
  -- Transform: Γ ≤ (⨆ χ, bval χ ⊓ R =ᴮ func χ) → Γ ≤ (⨆ χ, bval χ ⊓ η =ᴮ a1_func χ)
  -- via bv_cases_left keeping Γ in context
  apply le_trans (le_inf HR_mem_a1' le_rfl)
  apply bv_cases_left; intro χ
  -- Now ctx = (a1'.bval χ ⊓ R =ᴮ a1'.func χ) ⊓ Γ
  apply le_iSup_of_le χ
  apply le_inf (inf_le_left.trans inf_le_left)
  -- Goal: (bval χ ⊓ R =ᴮ func χ) ⊓ Γ ≤ η =ᴮ a1_func χ
  -- Step 5: Use a1_func_spec
  have Hbval : (a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ ≤
      (a1' (𝔹 := 𝔹)).bval χ := inf_le_left.trans inf_le_left
  have Hfunc_eq : (a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ ≤
      R =ᴮ (a1' (𝔹 := 𝔹)).func χ := inf_le_left.trans inf_le_right
  have H_mem' : (a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ ≤
      (a1' (𝔹 := 𝔹)).func χ ∈ᴮ (a1' (𝔹 := 𝔹)) :=
    le_trans Hbval (mem_mk' _ _)
  have H_spec : (a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ ≤
      a1_ψ ((a1' (𝔹 := 𝔹)).func χ) (a1_func χ) := a1_func_spec H_mem'
  have H_afc_ord : (a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ ≤
      Ord (a1_func χ) := H_spec.trans (inf_le_left.trans inf_le_left)
  have H_spec_inj : (a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ ≤
      ⨆ g, is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ :=
    H_spec.trans (inf_le_left.trans inf_le_right)
  have H_afc_nonempty : (a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ ≤
      ((a1' (𝔹 := 𝔹)).func χ =ᴮ ∅)ᶜ := H_spec.trans inf_le_right
  -- Step 6: For each g, derive η =ᴮ a1_func χ
  apply le_trans (le_inf H_spec_inj le_rfl)
  apply bv_cases_left; intro g
  -- New ctx: (inj_fun(afc,ω,g) ⊓ img =ᴮ func χ) ⊓ ((bval χ ⊓ R =ᴮ func χ) ⊓ Γ)
  have Hg_inj : (is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ) ⊓
      ((a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ) ≤
      is_injective_function (a1_func χ) omega g :=
    inf_le_left.trans inf_le_left
  have Hg_img : (is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ) ⊓
      ((a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ) ≤
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ :=
    inf_le_left.trans inf_le_right
  have HR_func_χ : (is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ) ⊓
      ((a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ) ≤
      R =ᴮ (a1' (𝔹 := 𝔹)).func χ :=
    inf_le_right.trans Hfunc_eq
  have H_afc_ord2 : (is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ) ⊓
      ((a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ) ≤
      Ord (a1_func χ) := inf_le_right.trans H_afc_ord
  have H_nonempty2 : (is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ) ⊓
      ((a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ) ≤
      ((a1' (𝔹 := 𝔹)).func χ =ᴮ ∅)ᶜ := inf_le_right.trans H_afc_nonempty
  -- H_ord, Hf, H_not_one from Γ
  have H_ord2 := inf_le_right.trans (inf_le_right.trans H_ord) (a := (is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ) ⊓ ((a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ))
  have Hf2 := inf_le_right.trans (inf_le_right.trans Hf) (a := (is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ) ⊓ ((a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ))
  have H_not_one2 := inf_le_right.trans (inf_le_right.trans H_not_one) (a := (is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ) ⊓ ((a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ))
  have H_ind_eq : (is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ) ⊓
      ((a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ) ≤
      induced_epsilon_rel η omega f =ᴮ induced_epsilon_rel (a1_func χ) omega g := by
    unfold induced_epsilon_rel at *
    exact le_trans (le_inf HR_func_χ (bv_symm Hg_img)) bv_eq_trans
  have H_exists_two_η := (exists_two_iff H_ord2).mpr H_not_one2
  have H_exists_two_afc : (is_injective_function (a1_func χ) omega g ⊓
      image (mem_rel (a1_func χ)) (prod omega omega) (prod_map_self (a1_func χ) omega g) =ᴮ
      (a1' (𝔹 := 𝔹)).func χ) ⊓
      ((a1' (𝔹 := 𝔹)).bval χ ⊓ R =ᴮ (a1' (𝔹 := 𝔹)).func χ ⊓ Γ) ≤
      exists_two (a1_func χ) := by
    rw [exists_two_iff H_afc_ord2]
    -- Use: not_one_of_induced_rel_nonempty + ind nonempty from H_nonempty2 + Hg_img
    apply not_one_of_induced_rel_nonempty (Hg_inj.trans inf_le_left)
    -- Need: (induced_epsilon_rel (a1_func χ) omega g =ᴮ ∅)ᶜ
    -- From Hg_img: ind =ᴮ a1'.func χ and H_nonempty2: (a1'.func χ =ᴮ ∅)ᶜ
    apply bv_rw' (H := Hg_img) (ϕ := fun v => (v =ᴮ ∅)ᶜ)
      (h_congr := B_ext_neg (h := B_ext_bv_eq_left))
    exact H_nonempty2
  exact eq_of_eq_induced_epsilon_rel H_ord2 H_afc_ord2 Hf2 Hg_inj H_ind_eq
    H_exists_two_η H_exists_two_afc

-- src/aleph_one.lean:777
lemma mem_a1_iff {Γ : 𝔹} {η : bSet 𝔹} (H_ord : Γ ≤ Ord η) :
    Γ ≤ η ∈ᴮ a1 ↔ Γ ≤ ⨆ f, is_injective_function η omega f := by
  constructor
  · -- Forward: η ∈ a1 → η injects into ω
    intro H_mem
    rw [mem_a1_iff₀] at H_mem
    -- Case split: η = 0, η = 1, or η ∈ a1_aux
    apply le_trans H_mem; apply sup_le; apply sup_le
    · -- Case η = 0: 0 injects into ω
      exact le_trans (le_inf (bv_symm le_rfl) (le_trans le_top
        (injection_into_of_injects_into (injects_into_of_subset of_nat_subset_omega))))
        (B_ext_iSup (h := fun f => B_ext_is_injective_function_left) _ _)
    · -- Case η = 1: 1 injects into ω
      exact le_trans (le_inf (bv_symm le_rfl) (le_trans le_top
        (injection_into_of_injects_into (injects_into_of_subset of_nat_subset_omega))))
        (B_ext_iSup (h := fun f => B_ext_is_injective_function_left) _ _)
    · -- Case η ∈ a1_aux: get a1_func χ which injects into ω
      rw [mem_unfold]
      apply le_trans (b := ⨆ (i : (a1' (𝔹 := 𝔹)).type), (a1' (𝔹 := 𝔹)).bval i ⊓ η =ᴮ a1_func i)
      · exact le_rfl
      apply iSup_le; intro χ
      -- a1'.bval χ ⊓ η =ᴮ a1_func χ → η injects into ω
      -- a1_func_spec: Γ ≤ a1_ψ (a1'.func χ) (a1_func χ) includes ⨆ g, inj_fun(a1_func χ,ω,g)
      -- η =ᴮ a1_func χ → η has same injections
      have H_mem' : (a1' (𝔹 := 𝔹)).bval χ ⊓ η =ᴮ a1_func χ ≤
          (a1' (𝔹 := 𝔹)).func χ ∈ᴮ (a1' (𝔹 := 𝔹)) :=
        le_trans inf_le_left (mem_mk' _ _)
      have H_spec : (a1' (𝔹 := 𝔹)).bval χ ⊓ η =ᴮ a1_func χ ≤
          a1_ψ ((a1' (𝔹 := 𝔹)).func χ) (a1_func χ) := a1_func_spec H_mem'
      have H_afc_inj : (a1' (𝔹 := 𝔹)).bval χ ⊓ η =ᴮ a1_func χ ≤
          ⨆ g, is_injective_function (a1_func χ) omega g :=
        le_trans (H_spec.trans (inf_le_left.trans inf_le_right))
          (iSup_le (fun g => le_iSup_of_le g inf_le_left))
      -- Rewrite using η =ᴮ a1_func χ
      exact le_trans (le_inf (bv_symm inf_le_right) H_afc_inj)
        (B_ext_iSup (h := fun g => B_ext_is_injective_function_left) _ _)
  · -- Backward: η injects into ω → η ∈ a1
    intro H_inj
    rw [mem_a1_iff₀]
    -- BA-valued case split on η = 1, then η = 0
    apply le_trans (b := (η =ᴮ 1 ⊔ (η =ᴮ 1)ᶜ) ⊓ Γ)
    · simp [sup_compl_eq_top]
    apply bv_or_elim_left
    · -- Case η = 1: → z =ᴮ 0 ⊔ z =ᴮ 1 ⊔ _
      exact le_trans inf_le_left (le_sup_of_le_left le_sup_right)
    · -- Case η ≠ 1: split on η = 0
      apply le_trans (b := (η =ᴮ 0 ⊔ (η =ᴮ 0)ᶜ) ⊓ ((η =ᴮ 1)ᶜ ⊓ Γ))
      · simp [sup_compl_eq_top]
      apply bv_or_elim_left
      · -- Case η = 0: → z =ᴮ 0 ⊔ ...
        exact le_trans inf_le_left (le_sup_of_le_left le_sup_left)
      · -- Case η ≠ 0, η ≠ 1: use mem_a1_of_injects_into_omega_aux
        -- Context: (η=0)ᶜ ⊓ ((η=1)ᶜ ⊓ Γ)
        apply le_sup_of_le_right
        apply mem_a1_of_injects_into_omega_aux
        · exact inf_le_right.trans (inf_le_right.trans H_ord)  -- Γ → Ord η
        · exact inf_le_right.trans (inf_le_right.trans H_inj)  -- Γ → H_inj
        · exact inf_le_left  -- (η=0)ᶜ
        · exact inf_le_right.trans inf_le_left  -- (η=1)ᶜ

-- src/aleph_one.lean:802
lemma a1_transitive {Γ : 𝔹} : Γ ≤ is_transitive a1 := by
  unfold is_transitive
  apply le_iInf; intro z; rw [← deduction]
  rw [subset_unfold']; apply le_iInf; intro w; rw [← deduction]
  -- Goal: Γ ⊓ z ∈ a1 ⊓ w ∈ z ≤ w ∈ a1
  -- Case-split on z ∈ a1 ↔ (z = 0 ⊔ z = 1) ⊔ z ∈ a1_aux  (left-assoc via mem_a1_iff₀)
  have H_cases : Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z ≤ z =ᴮ 0 ⊔ z =ᴮ 1 ⊔ z ∈ᴮ a1_aux :=
    mem_a1_iff₀.mp (inf_le_left.trans inf_le_right)
  apply le_trans (b := (z =ᴮ 0 ⊔ z =ᴮ 1 ⊔ z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z))
  · exact le_inf H_cases le_rfl
  -- Goal: ((z=0 ⊔ z=1) ⊔ z∈a1_aux) ⊓ ctx ≤ w ∈ a1  (left-assoc)
  -- Outer split: z=0 ⊔ z=1 vs z∈a1_aux
  · apply bv_or_elim_left
    · -- Case z = 0 ⊔ z = 1: inner split
      apply bv_or_elim_left
      · -- Case z = 0: z = ∅, so w ∈ ∅ → contradiction
        apply bv_exfalso
        apply bv_absurd (w ∈ᴮ (∅ : bSet 𝔹))
        · -- w ∈ ∅ from w ∈ z and z =ᴮ 0 =ᴮ ∅
          apply mem_congr bv_refl
          · exact le_trans (le_inf inf_le_left zero_eq_empty) bv_eq_trans
          · exact inf_le_right.trans inf_le_right
        · exact (empty_iff_forall_not_mem.mp bv_refl).trans (iInf_le _ w)
      · -- Case z = 1: w ∈ 1 → w = 0 → w ∈ a1
        rw [mem_a1_iff₀]
        apply le_trans _ (le_sup_left.trans le_sup_left)
        apply eq_zero_of_mem_one
        exact mem_congr bv_refl inf_le_left (inf_le_right.trans inf_le_right)
    · -- Case z ∈ a1_aux: z is an ordinal injecting into omega
      -- Show w ∈ a1 using mem_a1_iff: w injects into omega too (via z's injection)
      -- Step 1: z injects into omega (from mem_a1_iff forward on z ∈ a1)
      have Hz_a1 : (z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z) ≤ z ∈ᴮ a1 :=
        inf_le_right.trans (inf_le_left.trans inf_le_right)
      have Hz_ord : (z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z) ≤ Ord z :=
        Ord_of_mem_a1 Hz_a1
      have Hz_inj : (z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z) ≤
          ⨆ f, is_injective_function z omega f :=
        (mem_a1_iff Hz_ord).mp Hz_a1
      -- Step 2: w ⊆ z (from w ∈ z and Ord z is transitive)
      have Hw_z : (z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z) ≤ w ∈ᴮ z :=
        inf_le_right.trans inf_le_right
      have Hw_sub : (z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z) ≤ w ⊆ᴮ z :=
        subset_of_mem_transitive (Hz_ord.trans inf_le_right) Hw_z
      -- Step 3: w injects into omega (via injects_into_of_subset + injects_into_trans)
      have Hw_ord : (z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z) ≤ Ord w :=
        Ord_of_mem_Ord Hw_z Hz_ord
      have Hw_inj_into_z : (z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z) ≤ injects_into w z :=
        injects_into_of_subset Hw_sub
      have Hz_inj_into_omega : (z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z) ≤
          injects_into z omega :=
        injects_into_of_injection_into Hz_inj
      have Hw_inj_into_omega : (z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z) ≤
          injects_into w omega :=
        injects_into_trans Hw_inj_into_z Hz_inj_into_omega
      -- Convert injects_into to ⨆ f, is_injective_function w omega f
      have Hw_inj : (z ∈ᴮ a1_aux) ⊓ (Γ ⊓ z ∈ᴮ a1 ⊓ w ∈ᴮ z) ≤
          ⨆ f, is_injective_function w omega f :=
        injection_into_of_injects_into Hw_inj_into_omega
      -- Step 4: w ∈ a1 by mem_a1_iff backward
      exact (mem_a1_iff Hw_ord).mpr Hw_inj

-- src/aleph_one.lean:818
lemma a1_ewo {Γ : 𝔹} : Γ ≤ ewo a1 := by
  unfold ewo epsilon_well_orders
  refine le_inf ?_ ?_
  · -- epsilon_trichotomy a1: all members of a1 are Ords and ordinals satisfy trichotomy
    apply epsilon_trichotomy_of_sub_Ord
    apply le_iInf; intro x; rw [← deduction]
    exact Ord_of_mem_a1 inf_le_right
  · -- epsilon_well_founded a1: regularity gives well-foundedness for any sub-Ord
    exact epsilon_wf_of_sub_Ord a1

-- src/aleph_one.lean:826
lemma a1_Ord {Γ : 𝔹} : Γ ≤ Ord a1 := le_inf a1_ewo a1_transitive

-- src/aleph_one.lean:828
lemma a1_not_le_omega {Γ : 𝔹} : Γ ≤ (injects_into a1 omega)ᶜ := by
  rw [← imp_bot, ← deduction]
  -- Goal: Γ ⊓ injects_into a1 omega ≤ ⊥
  apply bot_of_mem_self'
  -- Goal: Γ ⊓ injects_into a1 omega ≤ a1 ∈ a1
  apply (mem_a1_iff (inf_le_left.trans a1_Ord)).mpr
  -- Goal: Γ ⊓ injects_into a1 omega ≤ ⨆ f, is_injective_function a1 omega f = injection_into a1 omega
  exact injects_into_iff_injection_into.mp inf_le_right

-- src/aleph_one.lean:834
lemma a1_spec {Γ : 𝔹} : Γ ≤ aleph_one_Ord_spec a1 := by
  refine le_inf a1_not_le_omega (le_inf a1_Ord ?_)
  apply le_iInf; intro y; rw [← deduction, ← deduction]
  -- ctx := Γ ⊓ Ord y ⊓ (injects_into y omega)ᶜ, Goal: ctx ≤ a1 ⊆ y
  have H_Ord_y : Γ ⊓ Ord y ⊓ (injects_into y bSet.omega)ᶜ ≤ Ord y :=
    inf_le_left.trans inf_le_right
  have H_no_inj_y : Γ ⊓ Ord y ⊓ (injects_into y bSet.omega)ᶜ ≤ (injects_into y bSet.omega)ᶜ :=
    inf_le_right
  -- Show y ∉ a1 (if y ∈ a1 then injects_into y omega, contradiction)
  have H_not_mem_a1 : Γ ⊓ Ord y ⊓ (injects_into y bSet.omega)ᶜ ≤ (y ∈ᴮ a1)ᶜ := by
    apply (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr _))
    apply bv_absurd (injects_into y bSet.omega)
    · exact injects_into_of_injection_into ((mem_a1_iff (inf_le_left.trans H_Ord_y)).mp inf_le_right)
    · exact inf_le_left.trans H_no_inj_y
  -- Now prove a1 ⊆ y by trichotomy
  rw [Ord.le_iff_lt_or_eq a1_Ord H_Ord_y]
  -- Goal: ctx ≤ a1 ∈ y ⊔ a1 = y
  have H_tri := Ord.trichotomy a1_Ord H_Ord_y
  -- tri: ctx ≤ (a1 =ᴮ y ⊔ a1 ∈ᴮ y) ⊔ y ∈ᴮ a1
  apply le_trans (b := (a1 =ᴮ y ⊔ a1 ∈ᴮ y ⊔ y ∈ᴮ a1) ⊓
      (Γ ⊓ Ord y ⊓ (injects_into y bSet.omega)ᶜ))
  · exact le_inf H_tri le_rfl
  · apply bv_or_elim_left
    · -- Case (a1=y ⊔ a1∈y) ⊓ ctx
      apply bv_or_elim_left
      · -- a1=y: → a1∈y ⊔ a1=y (right branch)
        exact le_trans inf_le_left le_sup_right
      · -- a1∈y: → a1∈y ⊔ a1=y (left branch)
        exact le_trans inf_le_left le_sup_left
    · -- Case y∈a1 ⊓ ctx: contradicts H_not_mem_a1
      apply bv_exfalso
      exact bv_absurd _ inf_le_left (inf_le_right.trans H_not_mem_a1)

-- src/aleph_one.lean:862
set_option maxHeartbeats 800000 in
lemma a1_le_of_omega_lt {Γ : 𝔹} : Γ ≤ le_of_omega_lt a1 := by
  unfold le_of_omega_lt
  apply le_iInf; intro z; rw [← deduction, ← deduction]
  -- ctx := Γ ⊓ Ord z ⊓ (larger_than omega z)ᶜ
  -- Goal: ctx ≤ injects_into a1 z
  have H_Ord_z : Γ ⊓ Ord z ⊓ (larger_than bSet.omega z)ᶜ ≤ Ord z :=
    inf_le_left.trans inf_le_right
  have H_no_larger : Γ ⊓ Ord z ⊓ (larger_than bSet.omega z)ᶜ ≤ (larger_than bSet.omega z)ᶜ :=
    inf_le_right
  -- Helper: larger_than omega ∅ is trivially true
  have H_lt_empty : (⊤ : 𝔹) ≤ larger_than bSet.omega (∅ : bSet 𝔹) := by
    apply le_iSup_of_le (∅ : bSet 𝔹); apply le_iSup_of_le (∅ : bSet 𝔹)
    exact le_inf (le_inf empty_subset is_func'_empty) is_surj_empty
  -- Step 1: ¬(injects_into z omega)
  have H_no_inj : Γ ⊓ Ord z ⊓ (larger_than bSet.omega z)ᶜ ≤ (injects_into z bSet.omega)ᶜ := by
    apply (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr _))
    -- Goal: ctx ⊓ injects_into z omega ≤ ⊥
    apply bv_absurd (larger_than bSet.omega z)
    · -- Case split on z = ∅
      apply le_trans (b := (z =ᴮ ∅ ⊔ (z =ᴮ ∅)ᶜ) ⊓
          (Γ ⊓ Ord z ⊓ (larger_than bSet.omega z)ᶜ ⊓ injects_into z bSet.omega))
      · simp [sup_compl_eq_top]
      · apply bv_or_elim_left
        · -- Case z = ∅: larger_than omega ∅ by trivial empty function
          exact bv_rw' (H := inf_le_left) (h_congr := B_ext_larger_than_right)
            (H_new := le_top.trans H_lt_empty)
        · -- Case z ≠ ∅: surjects_onto_of_injects_into' gives larger_than
          apply larger_than_of_surjects_onto
          apply surjects_onto_of_injects_into'
          · exact inf_le_right.trans inf_le_right
          · exact nonempty_iff_exists_mem.mp inf_le_left
    · exact inf_le_left.trans H_no_larger
  -- Step 2: z ∉ a1 (via mem_a1_iff)
  have H_not_mem_a1 : Γ ⊓ Ord z ⊓ (larger_than bSet.omega z)ᶜ ≤ (z ∈ᴮ a1)ᶜ := by
    apply (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr _))
    -- Goal: ctx ⊓ z ∈ a1 ≤ ⊥
    apply bv_absurd (injects_into z bSet.omega)
    · exact injects_into_of_injection_into ((mem_a1_iff (inf_le_left.trans H_Ord_z)).mp inf_le_right)
    · exact inf_le_left.trans H_no_inj
  -- Step 3: by trichotomy a1_Ord vs Ord z, derive a1 ⊆ z
  have H_sub : Γ ⊓ Ord z ⊓ (larger_than bSet.omega z)ᶜ ≤ a1 ⊆ᴮ z := by
    rw [Ord.le_iff_lt_or_eq a1_Ord H_Ord_z]
    -- Goal: ctx ≤ a1 ∈ z ⊔ a1 = z
    have H_tri := Ord.trichotomy a1_Ord H_Ord_z
    -- tri: ctx ≤ a1 = z ⊔ a1 ∈ z ⊔ z ∈ a1  (left-assoc: (a1=z ⊔ a1∈z) ⊔ z∈a1)
    apply le_trans (b := (a1 =ᴮ z ⊔ a1 ∈ᴮ z ⊔ z ∈ᴮ a1) ⊓
        (Γ ⊓ Ord z ⊓ (larger_than bSet.omega z)ᶜ))
    · exact le_inf H_tri le_rfl
    · apply bv_or_elim_left
      · -- Case (a1=z ⊔ a1∈z) ⊓ ctx: split into subcases
        apply bv_or_elim_left
        · -- a1=z: → a1∈z ⊔ a1=z (right branch)
          exact le_trans inf_le_left le_sup_right
        · -- a1∈z: → a1∈z ⊔ a1=z (left branch)
          exact le_trans inf_le_left le_sup_left
      · -- Case z∈a1 ⊓ ctx: contradicts H_not_mem_a1
        apply bv_exfalso
        exact bv_absurd _ inf_le_left (inf_le_right.trans H_not_mem_a1)
  exact injects_into_of_subset H_sub

end a1

-- ============================================================
-- src/aleph_one.lean:890-926: final section
-- ============================================================

section

variable {𝔹 : Type u} [NontrivialCompleteBooleanAlgebra 𝔹]

-- src/aleph_one.lean:894
lemma injects_into_omega_of_mem_aleph_one_check {Γ : 𝔹} {z : bSet 𝔹}
    (H_mem : Γ ≤ z ∈ᴮ (check PSet.aleph_one : bSet 𝔹)) : Γ ≤ injects_into z bSet.omega := by
  rw [mem_unfold] at H_mem
  apply le_trans H_mem
  apply iSup_le; intro η
  simp only [check_bval_top, top_inf_eq, check_func]
  -- Goal: z =ᴮ check (PSet.aleph_one.Func (check_cast η)) ≤ injects_into z omega
  -- check (PSet.aleph_one.Func (check_cast η)) injects into omega (PSet fact)
  have h_pset : PSet.injects_into (PSet.aleph_one.Func (check_cast (𝔹 := 𝔹) η)) PSet.omega :=
    PSet.injects_into_omega_of_mem_aleph_one (PSet.func_mem PSet.aleph_one (check_cast (𝔹 := 𝔹) η))
  -- Lift to bSet
  have h_inj : (⊤ : 𝔹) ≤ injects_into (check (𝔹 := 𝔹) (PSet.aleph_one.Func (check_cast (𝔹 := 𝔹) η)))
      bSet.omega := check_injects_into h_pset
  -- From z =ᴮ w and injects_into w omega ≥ ⊤, derive injects_into z omega
  calc z =ᴮ check (𝔹 := 𝔹) (PSet.aleph_one.Func (check_cast (𝔹 := 𝔹) η))
      ≤ check (𝔹 := 𝔹) (PSet.aleph_one.Func (check_cast (𝔹 := 𝔹) η)) =ᴮ z ⊓
          injects_into (check (𝔹 := 𝔹) (PSet.aleph_one.Func (check_cast (𝔹 := 𝔹) η))) bSet.omega :=
        le_inf (bv_symm le_rfl) (le_trans le_top h_inj)
    _ ≤ injects_into z bSet.omega := B_ext_injects_into_left _ _

-- src/aleph_one.lean:905
lemma mem_aleph_one_of_injects_into_omega {x : bSet 𝔹} {Γ : 𝔹}
    (H_aleph_one : Γ ≤ aleph_one_Ord_spec x) {z : bSet 𝔹}
    (H_x_Ord : Γ ≤ Ord x) (H_z_Ord : Γ ≤ Ord z)
    (H_inj : Γ ≤ injects_into z bSet.omega) : Γ ≤ z ∈ᴮ x := by
  -- Proof by contradiction: assume z ∉ x, then x ⊆ z → x injects into omega → contradiction
  have hbot : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ ⊥ := by
    -- By Ord.resolve_lt: (z ∈ x)ᶜ → x ∈ z ⊔ x = z
    have H_z_Ord' : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ Ord z := le_trans inf_le_left H_z_Ord
    have H_x_Ord' : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ Ord x := le_trans inf_le_left H_x_Ord
    have H_not_mem : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ (z ∈ᴮ x)ᶜ := inf_le_right
    have H_tri := Ord.resolve_lt H_z_Ord' H_x_Ord' H_not_mem
    -- H_tri : Γ ⊓ (z ∈ x)ᶜ ≤ x ∈ z ⊔ x = z, so x ⊆ z
    have H_sub : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ x ⊆ᴮ z := by
      rw [Ord.le_iff_lt_or_eq H_x_Ord' H_z_Ord']
      exact H_tri.trans (sup_le le_sup_left le_sup_right)
    -- injects_into x omega
    have H_inj_x : Γ ⊓ (z ∈ᴮ x)ᶜ ≤ injects_into x bSet.omega :=
      injects_into_trans (injects_into_of_subset H_sub) (le_trans inf_le_left H_inj)
    -- aleph_one_Ord_spec x says (injects_into x omega)ᶜ
    exact bv_absurd _ H_inj_x (le_trans inf_le_left (bv_and_left H_aleph_one))
  -- Convert hbot to conclusion
  have : Γ ≤ (z ∈ᴮ x)ᶜ ⟹ ⊥ := deduction.mp hbot
  rwa [imp_bot, compl_compl] at this

-- src/aleph_one.lean:915
lemma aleph_one_check_sub_aleph_one_aux {x : bSet 𝔹} {Γ : 𝔹}
    (H_ord : Γ ≤ Ord x) (H_aleph_one : Γ ≤ aleph_one_Ord_spec x) :
    Γ ≤ (check PSet.aleph_one : bSet 𝔹) ⊆ᴮ x := by
  rw [subset_unfold']
  apply le_iInf; intro w; rw [← deduction]
  -- goal: Γ ⊓ w ∈ᴮ (check PSet.aleph_one) ≤ w ∈ᴮ x
  apply mem_aleph_one_of_injects_into_omega (le_trans inf_le_left H_aleph_one)
    (le_trans inf_le_left H_ord)
  · -- Ord w: w ∈ check PSet.aleph_one and PSet.aleph_one is an Ord
    exact Ord_of_mem_Ord inf_le_right (check_Ord PSet.aleph_one_Ord)
  · -- injects_into w omega
    exact injects_into_omega_of_mem_aleph_one_check inf_le_right

end

end bSet
