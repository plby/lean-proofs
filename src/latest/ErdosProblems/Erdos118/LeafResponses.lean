import ErdosProblems.Erdos118.StemResponses

/-!
Fixed-length leaf responses with exact ordinary/decorated extension equations.
Consuming a selected leaf slot preserves the pending-frame invariants.
-/

namespace Erdos118.LeafResponses

open LabelledExtensions LabelledFrames Negative Negative.Exact Erdos590.Larson

structure Setup (P : Position) (j : ℕ) where
  newWord : List ℕ
  length_eq : newWord.length = j - P.entries.length
  increasing : (P.decorated ++ newWord).Pairwise (· < ·)

theorem newWord_pairwise {P : Position} {j : ℕ} (A : Setup P j) :
    A.newWord.Pairwise (· < ·) := (List.pairwise_append.mp A.increasing).2.1

theorem setup_eq_of_prefix {P : Position} {j : ℕ} (A B : Setup P j)
    (h : A.newWord <+: B.newWord) : A = B := by
  have he := h.eq_of_length (A.length_eq.trans B.length_eq.symm)
  cases A with
  | mk a _ _ =>
    cases B with
    | mk b _ _ =>
      change a = b at he
      cases he
      rfl

def support {P : Position} {j : ℕ} (A : Setup P j) : Finset ℕ := A.newWord.toFinset

theorem support_injective (P : Position) (j : ℕ) :
    Function.Injective (support (P := P) (j := j)) := by
  intro A B hAB
  have hw : A.newWord = B.newWord := by
    rw [← sort_toFinset_eq_self_of_pairwise (newWord_pairwise A),
      ← sort_toFinset_eq_self_of_pairwise (newWord_pairwise B)]
    exact congrArg (fun s : Finset ℕ ↦ s.sort (· ≤ ·)) hAB
  exact setup_eq_of_prefix A B (hw ▸ List.prefix_rfl)

def family (P : Position) (j : ℕ) : Set (Finset ℕ) :=
  Set.range (support (P := P) (j := j))

theorem family_thin (P : Position) (j : ℕ) : NashWilliams.FinThin (family P j) := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩ hAB
  have hp := (pairwise_isPrefix_iff_initSeg (newWord_pairwise A) (newWord_pairwise B)).2 hAB
  exact congrArg support (setup_eq_of_prefix A B hp)

theorem setup_above (P : Position) (j : ℕ) {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ A : Setup P j, ∀ x ∈ A.newWord, x ∈ H ∧ b < x := by
  obtain ⟨v, hlen, hinc, hfresh⟩ := InteriorWords.fresh_list hH
    (max b P.decorated.sum) (j - P.entries.length)
  let A : Setup P j :=
    { newWord := v, length_eq := hlen
      increasing := by
        apply List.pairwise_append.mpr
        refine ⟨P.increasing, hinc, ?_⟩
        intro x hx y hy
        exact ((nat_le_sum_of_mem hx).trans (le_max_right _ _)).trans_lt (hfresh y hy).2 }
  exact ⟨A, fun x hx ↦ ⟨(hfresh x hx).1, (le_max_left _ _).trans_lt (hfresh x hx).2⟩⟩

theorem family_hits (P : Position) (j : ℕ) {H : Set ℕ} (hH : H.Infinite) :
    ∃ a ∈ family P j, (↑a : Set ℕ) ⊆ H := by
  obtain ⟨A, hA⟩ := setup_above P j hH 0
  exact ⟨support A, ⟨A, rfl⟩, fun x hx ↦ (hA x (List.mem_toFinset.mp hx)).1⟩

def responseFamily (P : Position) (j : ℕ) : RamseyGame.ResponseFamily where
  members := family P j
  thin := family_thin P j
  hits := fun _ hH ↦ family_hits P j hH

noncomputable def supportEquiv (P : Position) (j : ℕ) : Setup P j ≃ family P j :=
  Equiv.ofInjective support (support_injective P j)

@[simp] theorem supportEquiv_apply {P : Position} {j : ℕ} (A : Setup P j) :
    (supportEquiv P j A).1 = support A := rfl

@[simp] theorem support_symm {P : Position} {j : ℕ} (a : family P j) :
    support ((supportEquiv P j).symm a) = a.1 :=
  congrArg Subtype.val ((supportEquiv P j).apply_symm_apply a)

theorem newWord_ne_nil {P : Position} {j : ℕ} (A : Setup P j)
    (hpj : P.entries.length < j) : A.newWord ≠ [] := by
  intro he
  have hlen := A.length_eq
  simp only [he, List.length_nil] at hlen
  omega

def position {P : Position} {j : ℕ} (A : Setup P j)
    (hpj : P.entries.length < j) (hjn : j < P.size) : Position where
  stem := P.stem
  size := P.size
  label := P.label
  entries := P.entries ++ A.newWord
  room := P.room
  started := by simp only [List.length_append]; have h := P.started; omega
  unfinished := by
    rw [List.length_append, A.length_eq, Nat.add_sub_of_le hpj.le]
    exact hjn
  increasing := by
    simpa only [Position.decorated, List.append_assoc, List.cons_append] using A.increasing

theorem position_length {P : Position} {j : ℕ} (A : Setup P j)
    (hpj : P.entries.length < j) (hjn : j < P.size) :
    (position A hpj hjn).entries.length = j := by
  simp only [position, List.length_append, A.length_eq, Nat.add_sub_of_le hpj.le]

theorem position_decorated {P : Position} {j : ℕ} (A : Setup P j)
    (hpj : P.entries.length < j) (hjn : j < P.size) :
    (position A hpj hjn).decorated = P.decorated ++ A.newWord := by
  simp only [position, Position.decorated, List.append_assoc, List.cons_append]

theorem position_ordinary {P : Position} {j : ℕ} (A : Setup P j)
    (hpj : P.entries.length < j) (hjn : j < P.size) :
    (position A hpj hjn).ordinary = P.ordinary ++ A.newWord := by
  simp only [position, Position.ordinary, List.append_assoc, List.cons_append]

def toPending (F : Pending) (j : ℕ) (rest : List ℕ) (hF : F.leaves = j :: rest)
    (A : Setup F.position j) : Pending := by
  have hslot := F.leafSlots.bounded j (hF ▸ List.mem_cons_self ..)
  exact
    { position := position A hslot.1 hslot.2.1
      roots := F.roots
      leaves := rest
      rootSlots := F.rootSlots
      leafSlots := by
        rw [position_length]
        change Slots j F.position.size F.position.label rest
        exact Slots.tail (by simpa only [hF] using F.leafSlots)
      rootSelected := F.rootSelected
      leafSelected := by rw [position_length]; exact hslot.2.2 }

theorem toPending_phase (F : Pending) (j : ℕ) (rest : List ℕ) (hF : F.leaves = j :: rest)
    (A : Setup F.position j) :
    (Frame.pending (toPending F j rest hF A)).phase =
      PrefixRealization.Phase.pending F.roots.length rest.length := rfl

end Erdos118.LeafResponses
