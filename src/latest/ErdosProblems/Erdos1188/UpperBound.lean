import ErdosProblems.Erdos1188.Basic

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# An explicit universal upper bound
-/

namespace Erdos1188

noncomputable section

/-- Record, for each potential modulus `n≤x`, the unique selected residue if
one exists. Values 0 and 1 are harmless unused coordinates. -/
def encodeDistinctSystem (x : ℕ) (S : Finset CongruenceClass) :
    Fin (x + 1) → Option (Fin (x + 1)) := fun n =>
  if h : ∃ a : Fin (x + 1), (n.val, a.val) ∈ S then
    some (Classical.choose h)
  else none

/-- For a distinct-modulus family, the encoding at `n` equals `some a`
exactly when `(n,a)` is in the family. -/
theorem encodeDistinctSystem_eq_some_iff (x : ℕ)
    (S : Finset CongruenceClass) (hdist : HasDistinctModuli S)
    (n a : Fin (x + 1)) :
    encodeDistinctSystem x S n = some a ↔ (n.val, a.val) ∈ S := by
  classical
  unfold encodeDistinctSystem
  split_ifs with h
  · let b := Classical.choose h
    have hb : (n.val, b.val) ∈ S := Classical.choose_spec h
    constructor
    · intro heq
      have hba : b = a := Option.some.inj heq
      simpa [b, hba] using hb
    · intro ha
      have hpairs : (n.val, b.val) = (n.val, a.val) :=
        hdist hb ha rfl
      have hba : b = a := Fin.ext (congrArg Prod.snd hpairs)
      exact congrArg some hba
  · constructor
    · simp
    · intro ha
      exact False.elim (h ⟨a, ha⟩)

/-- The encoding is injective on the systems counted by `coveringCount`. -/
theorem encodeDistinctSystem_injective (x : ℕ) :
    Function.Injective (fun S : ↥(MinimalDistinctCoveringSystemsUpTo x) =>
      encodeDistinctSystem x S.val) := by
  classical
  intro S T henc
  apply Subtype.ext
  apply Finset.ext
  intro c
  have hSdata : S.val ⊆ ClassesUpTo x ∧
      IsMinimalDistinctCoveringSystem S.val := by
    have hmem := S.property
    change S.val ∈ (ClassesUpTo x).powerset.filter
      IsMinimalDistinctCoveringSystem at hmem
    have hd := Finset.mem_filter.mp hmem
    exact ⟨Finset.mem_powerset.mp hd.1, hd.2⟩
  have hTdata : T.val ⊆ ClassesUpTo x ∧
      IsMinimalDistinctCoveringSystem T.val := by
    have hmem := T.property
    change T.val ∈ (ClassesUpTo x).powerset.filter
      IsMinimalDistinctCoveringSystem at hmem
    have hd := Finset.mem_filter.mp hmem
    exact ⟨Finset.mem_powerset.mp hd.1, hd.2⟩
  have hSmin := hSdata.2
  have hTmin := hTdata.2
  have hSsub := hSdata.1
  have hTsub := hTdata.1
  constructor
  · intro hcS
    have hcUp := hSsub hcS
    rcases c with ⟨n, a⟩
    have hn : n < x + 1 := by
      simp [ClassesUpTo] at hcUp
      omega
    have ha : a < x + 1 := by
      have hv := hSmin.1 (n, a) hcS
      change 2 ≤ n ∧ a < n at hv
      omega
    let nf : Fin (x + 1) := ⟨n, hn⟩
    let af : Fin (x + 1) := ⟨a, ha⟩
    have hs : encodeDistinctSystem x S.val nf = some af :=
      (encodeDistinctSystem_eq_some_iff x S.val hSmin.2.1 nf af).2 hcS
    have ht : encodeDistinctSystem x T.val nf = some af := by
      have he := congrFun henc nf
      change encodeDistinctSystem x S.val nf =
        encodeDistinctSystem x T.val nf at he
      rw [← he]
      exact hs
    exact (encodeDistinctSystem_eq_some_iff x T.val hTmin.2.1 nf af).1 ht
  · intro hcT
    have hcUp := hTsub hcT
    rcases c with ⟨n, a⟩
    have hn : n < x + 1 := by
      simp [ClassesUpTo] at hcUp
      omega
    have ha : a < x + 1 := by
      have hv := hTmin.1 (n, a) hcT
      change 2 ≤ n ∧ a < n at hv
      omega
    let nf : Fin (x + 1) := ⟨n, hn⟩
    let af : Fin (x + 1) := ⟨a, ha⟩
    have ht : encodeDistinctSystem x T.val nf = some af :=
      (encodeDistinctSystem_eq_some_iff x T.val hTmin.2.1 nf af).2 hcT
    have hs : encodeDistinctSystem x S.val nf = some af := by
      have he := congrFun henc nf
      change encodeDistinctSystem x S.val nf =
        encodeDistinctSystem x T.val nf at he
      rw [he]
      exact ht
    exact (encodeDistinctSystem_eq_some_iff x S.val hSmin.2.1 nf af).1 hs

/-- Explicit version of the standard `exp(O(x log x))` upper bound. -/
theorem coveringCount_le_elementary (x : ℕ) :
    coveringCount x ≤ (x + 2) ^ (x + 1) := by
  classical
  have hcard := Fintype.card_le_of_injective
    (fun S : ↥(MinimalDistinctCoveringSystemsUpTo x) =>
      encodeDistinctSystem x S.val)
    (encodeDistinctSystem_injective x)
  simpa [coveringCount] using hcard

end

end Erdos1188
