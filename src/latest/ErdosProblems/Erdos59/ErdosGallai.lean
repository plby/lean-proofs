import Mathlib

/-!
# The finite Erdős--Gallai bound for `P₅`

The result is stated directly in the form used in the FNV closed-neighbourhood
argument: a finite simple graph with no injective four-edge path has at most
`3 |V| / 2` edges.
-/

namespace Erdos59

noncomputable section

private lemma fin5_vector_injective {V : Type*} {a b c d e : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Function.Injective ![a, b, c, d, e] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private lemma exists_path5_of_min_degree_two_of_degree_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hmin : ∀ w : V, 2 ≤ H.degree w) {v : V} (hv : 4 ≤ H.degree v) :
    ∃ p : Fin 5 → V, Function.Injective p ∧
      H.Adj (p 0) (p 1) ∧ H.Adj (p 1) (p 2) ∧
        H.Adj (p 2) (p 3) ∧ H.Adj (p 3) (p 4) := by
  have hvcard : 3 < (H.neighborFinset v).card := by
    rw [H.card_neighborFinset_eq_degree]
    omega
  obtain ⟨a, b₀, c₀, d₀, ha, hb₀, hc₀, hd₀,
      hab₀, hac₀, had₀, hb₀c₀, hb₀d₀, hc₀d₀⟩ :=
    Finset.three_lt_card_iff.mp hvcard
  have hva : H.Adj v a := (H.mem_neighborFinset v a).1 ha
  have hav : a ≠ v := hva.ne.symm
  have hacard : 1 < (H.neighborFinset a).card := by
    rw [H.card_neighborFinset_eq_degree]
    exact (hmin a)
  obtain ⟨x, hxmem, hxv⟩ := Finset.exists_mem_ne hacard v
  have hax : H.Adj a x := (H.mem_neighborFinset a x).1 hxmem
  have hxa : x ≠ a := hax.ne.symm
  obtain ⟨b, c, hb, hc, hab, hac, hbc, hxb, hxc⟩ :
      ∃ b c : V, b ∈ H.neighborFinset v ∧ c ∈ H.neighborFinset v ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ x ≠ b ∧ x ≠ c := by
    by_cases hxb₀ : x = b₀
    · refine ⟨c₀, d₀, hc₀, hd₀, hac₀, had₀, hc₀d₀, ?_, ?_⟩
      · simpa [hxb₀] using hb₀c₀
      · simpa [hxb₀] using hb₀d₀
    · by_cases hxc₀ : x = c₀
      · refine ⟨b₀, d₀, hb₀, hd₀, hab₀, had₀, hb₀d₀,
          hxb₀, ?_⟩
        simpa [hxc₀] using hc₀d₀
      · exact ⟨b₀, c₀, hb₀, hc₀, hab₀, hac₀, hb₀c₀,
          hxb₀, hxc₀⟩
  have hvb : H.Adj v b := (H.mem_neighborFinset v b).1 hb
  have hvc : H.Adj v c := (H.mem_neighborFinset v c).1 hc
  have hbv : b ≠ v := hvb.ne.symm
  have hcv : c ≠ v := hvc.ne.symm
  have hbcard : 1 < (H.neighborFinset b).card := by
    rw [H.card_neighborFinset_eq_degree]
    exact hmin b
  obtain ⟨y, hymem, hyv⟩ := Finset.exists_mem_ne hbcard v
  have hby : H.Adj b y := (H.mem_neighborFinset b y).1 hymem
  have hyb : y ≠ b := hby.ne.symm
  by_cases hya : y = a
  · let p : Fin 5 → V := ![x, a, b, v, c]
    refine ⟨p, ?_, ?_⟩
    · exact fin5_vector_injective hxa hxb hxv hxc hab hav hac hbv hbc hcv.symm
    · dsimp [p]
      exact ⟨hax.symm, hya ▸ hby.symm, hvb.symm, hvc⟩
  · by_cases hyx : y = x
    · let p : Fin 5 → V := ![c, v, a, x, b]
      refine ⟨p, ?_, ?_⟩
      · exact fin5_vector_injective hcv hac.symm hxc.symm hbc.symm hav.symm
          hxv.symm hbv.symm hxa.symm hab hxb
      · dsimp [p]
        exact ⟨hvc.symm, hva, hax, hyx ▸ hby.symm⟩
    · let p : Fin 5 → V := ![x, a, v, b, y]
      refine ⟨p, ?_, ?_⟩
      · exact fin5_vector_injective hxa hxv hxb (Ne.symm hyx) hav hab (Ne.symm hya)
          hbv.symm hyv.symm hby.ne
      · dsimp [p]
        exact ⟨hax.symm, hva.symm, hvb, hby⟩

/-- The exact finite `P₅` case of the Erdős--Gallai path theorem. -/
theorem erdosGallai_path5
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hP5 : ¬ ∃ p : Fin 5 → V, Function.Injective p ∧
      H.Adj (p 0) (p 1) ∧ H.Adj (p 1) (p 2) ∧
        H.Adj (p 2) (p 3) ∧ H.Adj (p 3) (p 4)) :
    2 * H.edgeFinset.card ≤ 3 * Fintype.card V := by
  classical
  induction n : Fintype.card V using Nat.strong_induction_on generalizing V H with
  | h n ih =>
      by_cases hlow : ∃ v : V, H.degree v ≤ 1
      · obtain ⟨v, hv⟩ := hlow
        let W : Set V := {v}ᶜ
        let H' : SimpleGraph W := H.induce W
        have hcardW : Fintype.card W = Fintype.card V - 1 := by
          dsimp [W]
          rw [Fintype.card_compl_set]
          simp
        have hcard_ltV : Fintype.card W < Fintype.card V := by
          rw [hcardW]
          have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
          omega
        have hP5' : ¬ ∃ p : Fin 5 → W, Function.Injective p ∧
            H'.Adj (p 0) (p 1) ∧ H'.Adj (p 1) (p 2) ∧
              H'.Adj (p 2) (p 3) ∧ H'.Adj (p 3) (p 4) := by
          rintro ⟨p, hp, hp01, hp12, hp23, hp34⟩
          apply hP5
          refine ⟨fun i ↦ (p i).1, ?_, ?_, ?_, ?_, ?_⟩
          · intro i j hij
            exact hp (Subtype.ext hij)
          all_goals simpa [H'] using ‹H'.Adj _ _›
        have hind : 2 * H'.edgeFinset.card ≤ 3 * Fintype.card W :=
          ih (Fintype.card W) (by rw [← n]; exact hcard_ltV) H' hP5' rfl
        have hedge' : H'.edgeFinset.card = H.edgeFinset.card - H.degree v := by
          exact (H.card_edgeFinset_induce_compl_singleton v).trans
            (H.card_edgeFinset_deleteIncidenceSet v)
        have hdeg_edge : H.degree v ≤ H.edgeFinset.card := H.degree_le_card_edgeFinset v
        have hedge : H.edgeFinset.card = H'.edgeFinset.card + H.degree v := by
          rw [hedge', Nat.sub_add_cancel hdeg_edge]
        rw [hedge]
        have hcardrel : Fintype.card W + 1 = Fintype.card V := by
          rw [hcardW]
          have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
          omega
        omega
      · have hmin : ∀ v : V, 2 ≤ H.degree v := by
          intro v
          have : ¬ H.degree v ≤ 1 := fun hv ↦ hlow ⟨v, hv⟩
          omega
        have hmax : ∀ v : V, H.degree v ≤ 3 := by
          intro v
          by_contra hv
          have hv4 : 4 ≤ H.degree v := by omega
          exact hP5 (exists_path5_of_min_degree_two_of_degree_four H hmin hv4)
        rw [← H.sum_degrees_eq_twice_card_edges]
        calc
          ∑ v, H.degree v ≤ ∑ _v : V, 3 := Finset.sum_le_sum fun v _ ↦ hmax v
          _ = 3 * Fintype.card V := by simp [Nat.mul_comm]
          _ = _ := by omega

end

end Erdos59
