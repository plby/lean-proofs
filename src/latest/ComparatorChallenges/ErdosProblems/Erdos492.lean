/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

noncomputable section


namespace Erdos492

open scoped Classical in
structure NatSubdivision where
  seq : ℕ → ℕ
  pos : ∀ n, 0 < seq n
  strictMono : StrictMono seq
  ratio_tendsto :
    Tendsto (fun n ↦ (seq (n + 1) : ℝ) / (seq n : ℝ)) atTop (𝓝 1)

end Erdos492

namespace Erdos492

open scoped Classical in
noncomputable def intervalCount (u : ℕ → ℝ) (N : ℕ) (s t : ℝ) : ℕ :=
  ((Finset.range N).filter fun n ↦ u n ∈ Ico s t).card

end Erdos492

namespace Erdos492

open scoped Classical in
def IsUniformlyDistributed (u : ℕ → ℝ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
    Tendsto
      (fun N ↦ (intervalCount u N s t : ℝ) / N)
      atTop (𝓝 (t - s))

end Erdos492

namespace Erdos492.NatSubdivision

variable (A : NatSubdivision)

open scoped Classical in
lemma add_le_seq (n : ℕ) : A.seq 0 + n ≤ A.seq n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep : A.seq n + 1 ≤ A.seq (n + 1) :=
        Nat.succ_le_iff.mpr (A.strictMono (Nat.lt_succ_self n))
      omega

open scoped Classical in
lemma self_lt_seq (n : ℕ) : n < A.seq n := by
  have h0 := A.pos 0
  have h := A.add_le_seq n
  omega

open scoped Classical in
lemma exists_lt_seq_succ (x : ℝ) : ∃ i : ℕ, x < A.seq (i + 1) := by
  obtain ⟨n : ℕ, hn : x < n⟩ := exists_nat_gt x
  refine ⟨n, hn.trans_le ?_⟩
  exact_mod_cast (Nat.le_succ n).trans
    (Nat.le_of_lt (A.self_lt_seq (n + 1)))

open scoped Classical in
def cellIndex (x : ℝ) : ℕ :=
  Nat.find (A.exists_lt_seq_succ x)

end Erdos492.NatSubdivision

namespace Erdos492.NatSubdivision

variable (A : NatSubdivision)

open scoped Classical in
def fractionalPosition (x : ℝ) : ℝ :=
  if (A.seq 0 : ℝ) ≤ x then
    let i := A.cellIndex x
    (x - A.seq i) / ((A.seq (i + 1) : ℝ) - A.seq i)
  else 0

end Erdos492.NatSubdivision

namespace Erdos492

open scoped Classical in
def sampledSequence (A : NatSubdivision) (α : ℝ) : ℕ → ℝ :=
  fun n ↦ A.fractionalPosition (α * (n + 1))

end Erdos492

namespace Erdos492

open scoped Classical in
theorem erdos_492 (A : NatSubdivision) :
    ∀ᵐ α : ℝ ∂volume, 0 < α →
      IsUniformlyDistributed (sampledSequence A α) := by
  sorry

end Erdos492

end
