import ErdosProblems.Erdos591.AtomicCoarsening

/-!
# Fast input sequences for finite construction stages

Every infinite input set has a strictly increasing sequence whose next
entry exceeds an arbitrary bound on the finite set already chosen.
Applying this to the proved retrospective bound supplies the numerical
spacing needed by every finite macro-extension with bounded label size.
-/

namespace Erdos591.Positive.Game

namespace ReplayBudget

theorem bound_mono (N : Set ℕ) (b : Position.LegalHistory N → ℕ)
    {F E : Finset ℕ} (hFE : F ⊆ E) {q r : ℕ} (hqr : q ≤ r) :
    bound N b F q ≤ bound N b E r := by
  have hh : (finite_histories N F q).toFinset ⊆ (finite_histories N E r).toFinset := by
    intro h ht
    have ht' := (finite_histories N F q).mem_toFinset.mp ht
    exact (finite_histories N E r).mem_toFinset.mpr ⟨ht'.1.trans hFE, ht'.2.trans hqr⟩
  exact Nat.succ_le_succ (max_le_max (Finset.sup_mono hFE) (Finset.sup_mono hh))

end ReplayBudget

namespace FastSequence

/-- The finite-set bound may be entirely arbitrary. No continuity,
computability, or monotonicity hypothesis is used in this construction. -/
theorem exists_above_finite_bounds {H : Set ℕ} (hH : H.Infinite)
    (F : Finset ℕ) (B : Finset ℕ → ℕ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (∀ n, f n ∈ H) ∧
      (∀ n, B (F ∪ (Finset.range n).image f) < f n) ∧
      (∀ n, (F ∪ (Finset.range n).image f).sup id < f n) := by
  classical
  choose pick hmem hgt using fun E : Finset ℕ => hH.exists_gt (max (B E) (E.sup id))
  let g : ℕ → Finset ℕ := Nat.rec F (fun _ E => insert (pick E) E)
  let f : ℕ → ℕ := fun n => pick (g n)
  have hg (n : ℕ) : g (n + 1) = insert (f n) (g n) := rfl
  have hsets (n : ℕ) : g n = F ∪ (Finset.range n).image f := by
    induction n with
    | zero => simp [g]
    | succ n ih => simp [hg, ih, Finset.range_add_one, Finset.union_insert]
  have hB (n : ℕ) : B (g n) < f n := (le_max_left _ _).trans_lt (hgt (g n))
  have hsup (n : ℕ) : (g n).sup id < f n := (le_max_right _ _).trans_lt (hgt (g n))
  have hmono : StrictMono f := by
    apply strictMono_nat_of_lt_succ
    intro n
    have hfn : f n ∈ g (n + 1) := by rw [hg]; exact Finset.mem_insert_self _ _
    exact (Finset.le_sup (f := id) hfn).trans_lt (hsup (n + 1))
  refine ⟨f, hmono, fun n => hmem (g n), ?_, ?_⟩
  · intro n
    simpa only [← hsets n] using hB n
  · intro n
    simpa only [← hsets n] using hsup n

theorem exists_retrospective_sequence {N H : Set ℕ} (hH : H.Infinite)
    (b : Concrete.Hist N → ℕ) (F : Finset ℕ) (q : ℕ) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ (∀ n, f n ∈ H) ∧
      (∀ n, ReplayBudget.bound N b (F ∪ (Finset.range n).image f) q < f n) ∧
      (∀ n, F.sup id < f n) := by
  obtain ⟨f, hmono, hmem, hb, hsup⟩ :=
    exists_above_finite_bounds hH F (fun E => ReplayBudget.bound N b E q)
  refine ⟨f, hmono, hmem, hb, ?_⟩
  intro n
  exact (Finset.sup_mono Finset.subset_union_left).trans_lt (hsup n)

end FastSequence

namespace Atomic

/-- Any increasing atomic word from a fast sequence inherits the
spacing certificate. The sequence may have unused entries between two
retained inputs; all old entries still precede the new atomic block. -/
theorem spaced_of_fast_sequence {N : Set ℕ} (b : Concrete.Hist N → ℕ)
    (F : Finset ℕ) (q : ℕ) (f : ℕ → ℕ) (hf : StrictMono f)
    (hfast : ∀ n, ReplayBudget.bound N b (F ∪ (Finset.range n).image f) q < f n)
    (xs : List Atom) (hinc : (inputs xs).Pairwise (· < ·))
    (hmem : ∀ x ∈ inputs xs, x ∈ Set.range f)
    (hsize : ∀ a ∈ xs, a.label.card ≤ q) : Spaced b F xs := by
  intro pre a tail heq
  have horder : (inputs pre ++ a.inputs ++ inputs tail).Pairwise (· < ·) := by
    simpa [heq, List.append_assoc] using hinc
  have hp := (List.pairwise_append.mp horder).1
  have haOrder : a.inputs.Pairwise (· < ·) := (List.pairwise_append.mp hp).2.1
  have hsep := (List.pairwise_append.mp hp).2.2
  obtain ⟨x, rest, hax⟩ := List.exists_cons_of_ne_nil a.inputs_ne_nil
  have hx : x ∈ a.inputs := by rw [hax]; simp
  have hxfull : x ∈ inputs xs := by
    rw [heq, inputs_append, inputs_cons]
    exact List.mem_append_right _ (List.mem_append_left _ hx)
  obtain ⟨n, hfn⟩ := hmem x hxfull
  refine ⟨F ∪ (Finset.range n).image f, q, ?_, hsize a ?_, ?_⟩
  · apply Finset.union_subset_union (Finset.Subset.refl _)
    intro y hy
    have hyl : y ∈ inputs pre := List.mem_toFinset.mp hy
    have hyfull : y ∈ inputs xs := by
      rw [heq, inputs_append]
      exact List.mem_append_left _ hyl
    obtain ⟨m, hfm⟩ := hmem y hyfull
    have hmn : m < n := (hf.lt_iff_lt).1 (by
      rw [hfm, hfn]
      exact hsep y hyl x hx)
    exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hmn, hfm⟩
  · rw [heq]
    exact List.mem_append_right _ (by simp)
  · intro y hy
    have hxy : x ≤ y := by
      have hy' : y = x ∨ y ∈ rest := by simpa [hax] using hy
      rcases hy' with rfl | hy'
      · exact le_refl _
      · have hh : (x :: rest).Pairwise (· < ·) := hax ▸ haOrder
        exact ((List.pairwise_cons.mp hh).1 y hy').le
    exact (hfn ▸ hfast n).trans_le hxy

#print axioms spaced_of_fast_sequence

end Atomic

end Erdos591.Positive.Game
