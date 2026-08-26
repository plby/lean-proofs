import ErdosProblems.Erdos538.SquarefreeDaisy
import ErdosProblems.Erdos538.PatternModel

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Transfer from cost-bin support rules to admissible integer families
-/

namespace Erdos538

/-- The multiset of cost labels attached to a finite labeled support.  Distinct
support elements may have the same cost, so this deliberately retains
multiplicity. -/
def supportSignature {α β : Type*} (cost : β → α) (S : Finset β) : Multiset α :=
  S.val.map cost

/-- Number of labeled support elements whose deletion leaves a selected cost
pattern. -/
noncomputable def patternSupportDeletionCount {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (cost : β → α) (F : Multiset α → Prop) (S : Finset β) : ℕ := by
  classical
  exact (S.filter fun x => F (supportSignature cost (S.erase x))).card

/-- Direct support form of the deletion cap. -/
def PatternSupportCap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (r : ℕ) (cost : β → α) (F : Multiset α → Prop) : Prop :=
  ∀ S : Finset β, patternSupportDeletionCount cost F S ≤ r

/-- The labeled support count is exactly the multiplicity-weighted multiset
count.  This is the formal reason equal cost bins must be counted with their
full occupancy. -/
theorem patternSupportDeletionCount_eq_patternDeletionCount
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (cost : β → α) (F : Multiset α → Prop) (S : Finset β) :
    patternSupportDeletionCount cost F S =
      patternDeletionCount F (supportSignature cost S) := by
  classical
  unfold patternSupportDeletionCount patternDeletionCount
  rw [Finset.card_def, Finset.filter_val]
  change
    (S.val.filter fun x => F (supportSignature cost (S.erase x))).card =
      ((S.val.map cost).filter fun c => F ((S.val.map cost).erase c)).card
  rw [Multiset.filter_map, Multiset.card_map]
  congr 1
  apply Multiset.filter_congr
  intro x hx
  have heq : supportSignature cost (S.erase x) =
      (supportSignature cost S).erase (cost x) := by
    rw [supportSignature, supportSignature, Finset.erase_val]
    exact Multiset.map_erase_of_mem cost S.val hx
  rw [heq]
  rfl

/-- A multiplicity-weighted multiset cap automatically gives the corresponding
cap on every finite labeled support, even when many labels have equal cost. -/
theorem patternCap_implies_supportCap
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {r : ℕ} (cost : β → α) (F : Multiset α → Prop)
    (hcap : PatternCap r F) : PatternSupportCap r cost F := by
  intro S
  rw [patternSupportDeletionCount_eq_patternDeletionCount]
  exact hcap (supportSignature cost S)

/-- Squarefree integers selected by a predicate on the multiset of cost labels
of their prime support. -/
noncomputable def patternIntegerFamily {α : Type*} [DecidableEq α]
    (N : ℕ) (cost : ℕ → α) (F : Multiset α → Prop) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    Squarefree n ∧ F (supportSignature cost n.primeFactors)

/-- Removing a prime divisor from a squarefree integer erases precisely that
prime from its finite prime support. -/
theorem primeFactors_div_prime_of_squarefree {m p : ℕ}
    (hm : Squarefree m) (hp : p ∈ m.primeFactors) :
    (m / p).primeFactors = m.primeFactors.erase p := by
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp
  calc
    (m / p).primeFactors = (m / m.gcd p).primeFactors := by
      rw [Nat.gcd_eq_right hpdvd]
    _ = m.primeFactors \ p.primeFactors :=
      Nat.primeFactors_div_gcd hm hpprime.ne_zero
    _ = m.primeFactors \ {p} := by rw [hpprime.primeFactors]
    _ = m.primeFactors.erase p := Finset.sdiff_singleton_eq_erase p m.primeFactors

/-- Any support rule obeying the labeled one-part-deletion cap induces an
admissible family of positive squarefree integers. -/
theorem patternIntegerFamily_admissible {α : Type*} [DecidableEq α]
    {r N : ℕ} (hr : 1 ≤ r) (cost : ℕ → α) (F : Multiset α → Prop)
    (hcap : PatternSupportCap r cost F) :
    Admissible r N (patternIntegerFamily N cost F) := by
  classical
  let A := patternIntegerFamily N cost F
  have hmem {a : ℕ} (ha : a ∈ A) :
      1 ≤ a ∧ a ≤ N ∧ Squarefree a ∧
        F (supportSignature cost a.primeFactors) := by
    rcases Finset.mem_filter.mp ha with ⟨haIcc, haSelect⟩
    exact ⟨(Finset.mem_Icc.mp haIcc).1, (Finset.mem_Icc.mp haIcc).2,
      haSelect.1, haSelect.2⟩
  have hpos : ∀ a ∈ A, 1 ≤ a := fun a ha => (hmem ha).1
  have hsq : ∀ a ∈ A, Squarefree a := fun a ha => (hmem ha).2.2.1
  apply (squarefree_admissible_iff hr hpos hsq).2
  refine ⟨?_, ?_⟩
  · intro a ha
    exact ⟨(hmem ha).1, (hmem ha).2.1⟩
  · intro m hm
    let selected := m.primeFactors.filter fun p =>
      F (supportSignature cost (m.primeFactors.erase p))
    have hsubset : quotientPrimes A m ⊆ selected := by
      intro p hpq
      rcases Finset.mem_filter.mp hpq with ⟨hp, hquotA⟩
      apply Finset.mem_filter.mpr
      refine ⟨hp, ?_⟩
      have hF := (hmem hquotA).2.2.2
      rw [primeFactors_div_prime_of_squarefree hm hp] at hF
      exact hF
    calc
      (quotientPrimes A m).card ≤ selected.card := Finset.card_le_card hsubset
      _ ≤ r := hcap m.primeFactors

/-- In particular, the abstract multiplicity-weighted pattern cap is by itself
sufficient for the induced squarefree integer family to solve the original
representation constraint. -/
theorem patternIntegerFamily_admissible_of_patternCap
    {α : Type*} [DecidableEq α] {r N : ℕ} (hr : 1 ≤ r)
    (cost : ℕ → α) (F : Multiset α → Prop) (hcap : PatternCap r F) :
    Admissible r N (patternIntegerFamily N cost F) :=
  patternIntegerFamily_admissible hr cost F
    (patternCap_implies_supportCap cost F hcap)

end Erdos538
