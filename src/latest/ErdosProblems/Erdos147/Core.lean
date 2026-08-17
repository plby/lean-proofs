import ErdosProblems.Erdos147.Basic

open Filter
open Asymptotics
open scoped SimpleGraph Topology

namespace Erdos147

set_option autoImplicit false

/-! ## A two-sided finite minimum-degree core -/

def relEdgeFinset {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] : Finset (L × R) :=
  Finset.univ.filter fun e ↦ B e.1 e.2

@[simp] lemma mem_relEdgeFinset {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)] (l : L) (r : R) :
    (l, r) ∈ relEdgeFinset B ↔ B l r := by
  simp [relEdgeFinset]

noncomputable def restrictedRelEdgeFinset {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) : Finset (L × R) := by
  classical
  exact (relEdgeFinset B).filter fun e ↦ e.1 ∈ S ∧ e.2 ∈ T

@[simp] lemma mem_restrictedRelEdgeFinset {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) (l : L) (r : R) :
    (l, r) ∈ restrictedRelEdgeFinset B S T ↔ B l r ∧ l ∈ S ∧ r ∈ T := by
  simp [restrictedRelEdgeFinset, and_assoc]

noncomputable def restrictedLeftDegree {L R : Type*} [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (T : Finset R) (l : L) : ℕ := by
  classical
  exact (T.filter fun r ↦ B l r).card

noncomputable def restrictedRightDegree {L R : Type*} [Fintype L]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (r : R) : ℕ := by
  classical
  exact (S.filter fun l ↦ B l r).card

lemma restrictedRelEdgeFinset_card_erase_left
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) {l : L} (hl : l ∈ S) :
    (restrictedRelEdgeFinset B (S.erase l) T).card +
        restrictedLeftDegree B T l =
      (restrictedRelEdgeFinset B S T).card := by
  classical
  let U := (relEdgeFinset B).filter fun e ↦ e.1 ∈ S ∧ e.2 ∈ T
  let A := U.filter fun e ↦ e.1 = l
  let C := U.filter fun e ↦ e.1 ≠ l
  have hdisj : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro e heA heC
    exact (Finset.mem_filter.mp heC).2 ((Finset.mem_filter.mp heA).2)
  have hunion : A ∪ C = U := by
    ext e
    by_cases h : e.1 = l <;> simp [A, C, h]
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcard
  have hA : A.card = restrictedLeftDegree B T l := by
    apply Finset.card_bij (fun e _ ↦ e.2)
    · intro e he
      have heA := Finset.mem_filter.mp (show e ∈ U.filter (fun e ↦ e.1 = l) from he)
      have heU := Finset.mem_filter.mp heA.1
      have hb : B e.1 e.2 := (mem_relEdgeFinset B e.1 e.2).mp heU.1
      have hb' : B l e.2 := by rwa [heA.2] at hb
      exact Finset.mem_filter.mpr ⟨heU.2.2, hb'⟩
    · intro e₁ he₁ e₂ he₂ h
      have he₁A := Finset.mem_filter.mp (show e₁ ∈ U.filter (fun e ↦ e.1 = l) from he₁)
      have he₂A := Finset.mem_filter.mp (show e₂ ∈ U.filter (fun e ↦ e.1 = l) from he₂)
      apply Prod.ext
      · exact he₁A.2.trans he₂A.2.symm
      · exact h
    · intro r hr
      simp only [restrictedLeftDegree, Finset.mem_filter] at hr
      refine ⟨(l, r), ?_, rfl⟩
      simp [A, U, hl, hr]
  have hC : C = restrictedRelEdgeFinset B (S.erase l) T := by
    ext e
    by_cases h : e.1 = l <;> simp [C, U, restrictedRelEdgeFinset, h, hl]
  have hU : U = restrictedRelEdgeFinset B S T := by
    ext e
    simp [U, restrictedRelEdgeFinset]
  rw [← hC, ← hA]
  rw [← hU]
  omega

lemma restrictedRelEdgeFinset_card_erase_right
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (S : Finset L) (T : Finset R) {r : R} (hr : r ∈ T) :
    (restrictedRelEdgeFinset B S (T.erase r)).card +
        restrictedRightDegree B S r =
      (restrictedRelEdgeFinset B S T).card := by
  classical
  let B' : R → L → Prop := fun r l ↦ B l r
  have h := restrictedRelEdgeFinset_card_erase_left B' T S hr
  have hcard (U : Finset R) (W : Finset L) :
      (restrictedRelEdgeFinset B' U W).card =
        (restrictedRelEdgeFinset B W U).card := by
    apply Finset.card_bij (fun e _ ↦ (e.2, e.1))
    · intro e he
      rw [mem_restrictedRelEdgeFinset] at he ⊢
      simpa [B', and_left_comm, and_comm] using he
    · intro e₁ h₁ e₂ h₂ he
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    · intro e he
      refine ⟨(e.2, e.1), ?_, rfl⟩
      rw [mem_restrictedRelEdgeFinset] at he ⊢
      simpa [B', and_left_comm, and_comm] using he
  simpa [B', restrictedRightDegree, restrictedLeftDegree, hcard] using h

noncomputable def relCorePotential {L R : Type*} [Fintype L] [Fintype R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (q : ℕ) (z : Finset L × Finset R) : ℤ :=
  4 * Fintype.card L * Fintype.card R *
      (restrictedRelEdgeFinset B z.1 z.2).card -
    q * Fintype.card R * z.1.card - q * Fintype.card L * z.2.card

/-- Every nonempty finite bipartite relation has a nonempty induced core in
which each left degree is at least one quarter of the original left average,
and similarly on the right.  The inequalities are cross-multiplied to avoid
rounding. -/
lemma exists_twoSided_relCore
    {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (B : L → R → Prop) [∀ l r, Decidable (B l r)]
    (hE : (relEdgeFinset B).Nonempty) :
    ∃ (S : Finset L) (T : Finset R), S.Nonempty ∧ T.Nonempty ∧
      (∀ l ∈ S, (relEdgeFinset B).card ≤
        4 * Fintype.card L * restrictedLeftDegree B T l) ∧
      (∀ r ∈ T, (relEdgeFinset B).card ≤
        4 * Fintype.card R * restrictedRightDegree B S r) := by
  classical
  let q := (relEdgeFinset B).card
  obtain ⟨z, hz⟩ := Finite.exists_max (relCorePotential B q)
  let S := z.1
  let T := z.2
  have hq : 0 < q := Finset.card_pos.mpr hE
  have hL : 0 < Fintype.card L := by
    obtain ⟨⟨l, r⟩, he⟩ := hE
    exact Fintype.card_pos_iff.mpr ⟨l⟩
  have hR : 0 < Fintype.card R := by
    obtain ⟨⟨l, r⟩, he⟩ := hE
    exact Fintype.card_pos_iff.mpr ⟨r⟩
  have hfull : relCorePotential B q (Finset.univ, Finset.univ) =
      2 * (Fintype.card L : ℤ) * Fintype.card R * q := by
    have heq : restrictedRelEdgeFinset B Finset.univ Finset.univ =
        relEdgeFinset B := by
      ext e
      rcases e with ⟨l, r⟩
      simp
    simp [relCorePotential, q, heq]
    ring
  have hpos : 0 < relCorePotential B q z := by
    have hle := hz (Finset.univ, Finset.univ)
    rw [hfull] at hle
    have hp : (0 : ℤ) < 2 * (Fintype.card L : ℤ) * Fintype.card R * q := by
      positivity
    exact hp.trans_le hle
  have hSne : S.Nonempty := by
    by_contra h
    have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have : relCorePotential B q z ≤ 0 := by
      change relCorePotential B q (S, T) ≤ 0
      rw [hS]
      simp [relCorePotential, restrictedRelEdgeFinset]
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)
    exact (not_lt_of_ge this) hpos
  have hTne : T.Nonempty := by
    by_contra h
    have hT : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have : relCorePotential B q z ≤ 0 := by
      change relCorePotential B q (S, T) ≤ 0
      rw [hT]
      simp [relCorePotential, restrictedRelEdgeFinset]
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)
    exact (not_lt_of_ge this) hpos
  refine ⟨S, T, hSne, hTne, ?_, ?_⟩
  · intro l hl
    have hmax := hz (S.erase l, T)
    have hedge := restrictedRelEdgeFinset_card_erase_left B S T hl
    change relCorePotential B q (S.erase l, T) ≤
      relCorePotential B q (S, T) at hmax
    simp only [relCorePotential, Prod.fst, Prod.snd, Finset.card_erase_of_mem hl] at hmax
    have hedgeZ :
        ((restrictedRelEdgeFinset B (S.erase l) T).card : ℤ) +
            restrictedLeftDegree B T l =
          (restrictedRelEdgeFinset B S T).card := by exact_mod_cast hedge
    have hScard : 1 ≤ S.card := Finset.one_le_card.mpr hSne
    rw [Nat.cast_sub hScard] at hmax
    rw [← hedgeZ] at hmax
    have hmul : (q : ℤ) * Fintype.card R ≤
        (4 * Fintype.card L * restrictedLeftDegree B T l : ℤ) *
          Fintype.card R := by
      push_cast at hmax
      ring_nf at hmax ⊢
      linarith
    have hcancel : (q : ℤ) ≤
        4 * Fintype.card L * restrictedLeftDegree B T l := by
      have hRz : (0 : ℤ) < Fintype.card R := by exact_mod_cast hR
      by_contra hn
      have hlt : (4 * Fintype.card L * restrictedLeftDegree B T l : ℤ) < q :=
        lt_of_not_ge hn
      nlinarith
    exact_mod_cast hcancel
  · intro r hr
    have hmax := hz (S, T.erase r)
    have hedge := restrictedRelEdgeFinset_card_erase_right B S T hr
    change relCorePotential B q (S, T.erase r) ≤
      relCorePotential B q (S, T) at hmax
    simp only [relCorePotential, Prod.fst, Prod.snd, Finset.card_erase_of_mem hr] at hmax
    have hedgeZ :
        ((restrictedRelEdgeFinset B S (T.erase r)).card : ℤ) +
            restrictedRightDegree B S r =
          (restrictedRelEdgeFinset B S T).card := by exact_mod_cast hedge
    have hTcard : 1 ≤ T.card := Finset.one_le_card.mpr hTne
    rw [Nat.cast_sub hTcard] at hmax
    rw [← hedgeZ] at hmax
    have hmul : (q : ℤ) * Fintype.card L ≤
        (4 * Fintype.card R * restrictedRightDegree B S r : ℤ) *
          Fintype.card L := by
      push_cast at hmax
      ring_nf at hmax ⊢
      linarith
    have hcancel : (q : ℤ) ≤
        4 * Fintype.card R * restrictedRightDegree B S r := by
      have hLz : (0 : ℤ) < Fintype.card L := by exact_mod_cast hL
      by_contra hn
      have hlt : (4 * Fintype.card R * restrictedRightDegree B S r : ℤ) < q :=
        lt_of_not_ge hn
      nlinarith
    exact_mod_cast hcancel

end Erdos147
