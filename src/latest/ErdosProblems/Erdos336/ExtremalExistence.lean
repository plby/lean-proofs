import Mathlib
import ErdosProblems.Erdos336.AutomaticBohrPatch
import ErdosProblems.Erdos336.Normalization

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Nonvacuity of the Erdős--Graham extremal function

An eventual family of finite cyclic removal bounds gives a finite bound for
every order: pad any smaller parent representation with zero up to an order
where the eventual theorem applies.  Hence every nonempty set of attainable
exact orders has a greatest element.
-/

namespace Erdos336

open Filter

/-- Exact order one is attainable at every positive variable order. -/
theorem admissible_one {r : ℕ} (hr : 1 ≤ r) : Admissible r 1 := by
  refine ⟨Set.univ, ?_, ?_⟩
  · refine ⟨0, ?_⟩
    intro n _hn
    refine ⟨1, hr, ?_⟩
    exact ⟨[n], by simp, by simp, by simp⟩
  · constructor
    · refine ⟨0, ?_⟩
      intro n _hn
      exact ⟨[n], by simp, by simp, by simp⟩
    · intro j hj hzero
      have hj0 : j = 0 := by omega
      subst j
      obtain ⟨N, hN⟩ := hzero
      obtain ⟨xs, hlen, _hmem, hsum⟩ := hN (N + 1) (by omega)
      have hnil : xs = [] := List.eq_nil_of_length_eq_zero hlen
      subst xs
      simp at hsum

/-- A cyclic removal bound at a larger parent length also works at every
smaller parent length, because zero belongs to the retained set. -/
theorem cyclicRemovalBound_of_le {h H M : ℕ} (hh : h ≤ H)
    (hH : CyclicRemovalBound H M) : CyclicRemovalBound h M := by
  intro N hN A x hzero hparent hexact y
  apply hH N hN A x hzero
  · intro z
    apply groupRepExactly_of_atMost_of_zero
    · exact ⟨h, hh, hparent z⟩
    · exact Or.inl hzero
  · exact hexact

/-- Eventual cyclic bounds imply the existence of some cyclic bound at every
specified parent length. -/
theorem exists_cyclicRemovalBound_of_eventually
    {M : ℕ → ℕ}
    (hMev : ∀ᶠ h : ℕ in atTop, CyclicRemovalBound h (M h))
    (h : ℕ) : ∃ C : ℕ, CyclicRemovalBound h C := by
  obtain ⟨a, ha⟩ := eventually_atTop.1 hMev
  let H := max a h
  refine ⟨M H, cyclicRemovalBound_of_le (Nat.le_max_right a h) ?_⟩
  exact ha H (Nat.le_max_left a h)

/-- A single finite cyclic bound gives a pointwise upper bound for every
attainable exact order, not merely for a preselected extremal function. -/
theorem admissible_upper_of_one_cyclic_bound
    {r k M : ℕ} (hr : 2 ≤ r) (hadm : Admissible r k)
    (hM : CyclicRemovalBound (r + 1) M) :
    k ≤ M + 4 * r + r := by
  obtain ⟨A, hatMost, horder⟩ := hadm
  obtain ⟨b, hbA⟩ := eventuallyAtMost_nonempty hatMost
  let D : Set ℤ := TranslateNatSet A b
  have hzeroD : (0 : ℤ) ∈ D := zero_mem_translateNatSet hbA
  have hparent : EventuallyWithOneExtra D (-(b : ℤ)) r :=
    eventuallyWithOneExtra_translate hatMost
  have hexactD : EventuallyExactlyZ D k :=
    eventuallyExactlyZ_translate horder.1
  have hboundD : EventuallyExactlyZ D (M + 4 * r + r) :=
    eventuallyExactlyZ_of_cyclic_bound_auto_patch hzeroD hparent hexactD hM
  have hboundA : EventuallyExactly A (M + 4 * r + r) :=
    eventuallyExactly_of_eventuallyExactlyZ_translate hboundD
  by_contra hnot
  exact horder.2 _ (Nat.lt_of_not_ge hnot) hboundA

/-- Eventual finite cyclic removal bounds make the extremal function genuinely
exist; consequently a limit theorem quantified over extremal functions is not
vacuous. -/
theorem exists_extremalFunction_of_eventual_cyclicRemovalBound
    {M : ℕ → ℕ}
    (hMev : ∀ᶠ h : ℕ in atTop, CyclicRemovalBound h (M h)) :
    ∃ H : ℕ → ℕ, IsExtremalFunction H := by
  classical
  have hAll : ∀ r : ℕ, ∃ C : ℕ, CyclicRemovalBound (r + 1) C := by
    intro r
    exact exists_cyclicRemovalBound_of_eventually hMev (r + 1)
  choose C hC using hAll
  let U : ℕ → ℕ := fun r => C r + 4 * r + r
  let H : ℕ → ℕ := fun r => Nat.findGreatest (Admissible r) (U r)
  refine ⟨H, ?_⟩
  intro r hr
  have hbase : Admissible r 1 := admissible_one (by omega)
  have hbaseBound : 1 ≤ U r := by
    dsimp [U]
    omega
  constructor
  · dsimp [H]
    exact Nat.findGreatest_spec hbaseBound hbase
  · intro k hk
    have hkU : k ≤ U r := by
      dsimp [U]
      exact admissible_upper_of_one_cyclic_bound hr hk (hC r)
    dsimp [H]
    exact Nat.le_findGreatest hkU hk

end Erdos336
