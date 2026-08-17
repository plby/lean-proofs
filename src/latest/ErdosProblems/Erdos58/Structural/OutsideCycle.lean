/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos58.Independent
import ErdosProblems.Erdos58.Linkage
import Mathlib.Tactic

/-!
# Odd cycles outside a longest odd cycle

This file isolates the splicing step in Gyárfás's proof of Erdős Problem 58.
If an odd cycle `D` is disjoint from a chosen longest odd cycle `C`, two
disjoint linking paths split both cycles into complementary arcs.  The four
possible splices are recorded by `TwoCycleSplice`.  The arithmetic in
`Linkage.lean` shows that one of these splices is an odd closed walk longer
than `C`; the simple-cycle fields below turn it into a genuine member of
`oddCycleLengths G`, contradicting maximality.

The certificate deliberately contains actual walks and `Walk.IsCycle`
proofs.  Thus the theorem below does not assume the desired strict length
inequality, nor does it replace graph cycles by bare natural numbers.  A
future direct Menger implementation only has to construct the certificate
from the supports of the two cycles.
-/

namespace Erdos58

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-! ## An odd cycle supported outside the designated longest cycle -/

/-- An actual odd simple cycle all of whose vertices lie outside `C`. -/
structure ExteriorOddCycle (C : LongestOddCycle G) where
  base : V
  cycle : G.Walk base base
  isCycle : cycle.IsCycle
  odd_length : Odd cycle.length
  support_outside : ∀ v ∈ cycle.support, v ∉ C.carrier

namespace ExteriorOddCycle

variable {C : LongestOddCycle G}

/-- The vertex set of the exterior cycle. -/
def carrier (D : ExteriorOddCycle C) : Set V :=
  {v | v ∈ D.cycle.support}

@[simp] theorem mem_carrier (D : ExteriorOddCycle C) (v : V) :
    v ∈ D.carrier ↔ v ∈ D.cycle.support :=
  Iff.rfl

theorem finite_carrier (D : ExteriorOddCycle C) : D.carrier.Finite := by
  exact Set.toFinite D.carrier

theorem disjoint_longest_carrier (D : ExteriorOddCycle C) :
    Disjoint C.carrier D.carrier := by
  rw [Set.disjoint_left]
  intro v hvC hvD
  exact D.support_outside v hvD hvC

theorem length_mem_oddCycleLengths (D : ExteriorOddCycle C) :
    D.cycle.length ∈ oddCycleLengths G :=
  ⟨D.odd_length, D.base, D.cycle, D.isCycle, rfl⟩

theorem length_le_longest (D : ExteriorOddCycle C) :
    D.cycle.length ≤ C.length :=
  C.maximal D.length_mem_oddCycleLengths

end ExteriorOddCycle

/-! ## Complementary arcs and the four genuine splices -/

/--
The geometric certificate obtained after splitting two linked cycles at the
four linkage endpoints.  The first pair of arcs lies on the chosen longest
cycle, the second pair on the exterior cycle.  Their length sums are the
lengths of the old cycles.

The four `IsCycle` fields state the support-disjointness conclusion of the
usual truncation of Menger paths: each displayed splice is not merely a
closed walk but a simple cycle.  Parity and strict growth are *proved* from
these data in `outside_odd_cycle_is_shorter_of_splice`.
-/
structure TwoCycleSplice {A B : Set V} (L : TwoLinkage G A B)
    (cLen dLen : ℕ) where
  c₁ : G.Walk L.a₁ L.a₂
  c₂ : G.Walk L.a₁ L.a₂
  d₁ : G.Walk L.b₁ L.b₂
  d₂ : G.Walk L.b₁ L.b₂
  c_length_sum : c₁.length + c₂.length = cLen
  d_length_sum : d₁.length + d₂.length = dLen
  parallel₁_isCycle :
    (SpliceData.close L.p d₁ L.q c₁).IsCycle
  parallel₂_isCycle :
    (SpliceData.close L.p d₂ L.q c₂).IsCycle
  crossed₁_isCycle :
    (SpliceData.close L.p d₂ L.q c₁).IsCycle
  crossed₂_isCycle :
    (SpliceData.close L.p d₁ L.q c₂).IsCycle

namespace TwoCycleSplice

variable {A B : Set V} {L : TwoLinkage G A B} {cLen dLen : ℕ}

/-- Forget the cycle proofs, retaining the walks needed by the arithmetic
splicing lemmas in `Linkage.lean`. -/
def data (S : TwoCycleSplice L cLen dLen) : SpliceData G where
  a₁ := L.a₁
  a₂ := L.a₂
  b₁ := L.b₁
  b₂ := L.b₂
  p := L.p
  q := L.q
  c₁ := S.c₁
  c₂ := S.c₂
  d₁ := S.d₁
  d₂ := S.d₂

@[simp] theorem data_parallel₁ (S : TwoCycleSplice L cLen dLen) :
    S.data.parallel₁ = SpliceData.close L.p S.d₁ L.q S.c₁ :=
  rfl

@[simp] theorem data_parallel₂ (S : TwoCycleSplice L cLen dLen) :
    S.data.parallel₂ = SpliceData.close L.p S.d₂ L.q S.c₂ :=
  rfl

@[simp] theorem data_crossed₁ (S : TwoCycleSplice L cLen dLen) :
    S.data.crossed₁ = SpliceData.close L.p S.d₂ L.q S.c₁ :=
  rfl

@[simp] theorem data_crossed₂ (S : TwoCycleSplice L cLen dLen) :
    S.data.crossed₂ = SpliceData.close L.p S.d₁ L.q S.c₂ :=
  rfl

theorem data_parallel₁_isCycle (S : TwoCycleSplice L cLen dLen) :
    S.data.parallel₁.IsCycle := by
  change (SpliceData.close L.p S.d₁ L.q S.c₁).IsCycle
  exact S.parallel₁_isCycle

theorem data_parallel₂_isCycle (S : TwoCycleSplice L cLen dLen) :
    S.data.parallel₂.IsCycle := by
  change (SpliceData.close L.p S.d₂ L.q S.c₂).IsCycle
  exact S.parallel₂_isCycle

theorem data_crossed₁_isCycle (S : TwoCycleSplice L cLen dLen) :
    S.data.crossed₁.IsCycle := by
  change (SpliceData.close L.p S.d₂ L.q S.c₁).IsCycle
  exact S.crossed₁_isCycle

theorem data_crossed₂_isCycle (S : TwoCycleSplice L cLen dLen) :
    S.data.crossed₂.IsCycle := by
  change (SpliceData.close L.p S.d₁ L.q S.c₂).IsCycle
  exact S.crossed₂_isCycle

/-- Any odd splice in the certificate is an actual odd cycle length of `G`. -/
theorem parallel₁_mem_oddCycleLengths (S : TwoCycleSplice L cLen dLen)
    (hodd : Odd S.data.parallel₁.length) :
    S.data.parallel₁.length ∈ oddCycleLengths G :=
  ⟨hodd, L.a₁, S.data.parallel₁, S.data_parallel₁_isCycle, rfl⟩

theorem parallel₂_mem_oddCycleLengths (S : TwoCycleSplice L cLen dLen)
    (hodd : Odd S.data.parallel₂.length) :
    S.data.parallel₂.length ∈ oddCycleLengths G :=
  ⟨hodd, L.a₁, S.data.parallel₂, S.data_parallel₂_isCycle, rfl⟩

theorem crossed₁_mem_oddCycleLengths (S : TwoCycleSplice L cLen dLen)
    (hodd : Odd S.data.crossed₁.length) :
    S.data.crossed₁.length ∈ oddCycleLengths G :=
  ⟨hodd, L.a₁, S.data.crossed₁, S.data_crossed₁_isCycle, rfl⟩

theorem crossed₂_mem_oddCycleLengths (S : TwoCycleSplice L cLen dLen)
    (hodd : Odd S.data.crossed₂.length) :
    S.data.crossed₂.length ∈ oddCycleLengths G :=
  ⟨hodd, L.a₁, S.data.crossed₂, S.data_crossed₂_isCycle, rfl⟩

end TwoCycleSplice

/-! ## The outside-cycle strict inequality -/

/--
An exterior odd cycle linked to the designated longest odd cycle by a valid
two-cycle splice is strictly shorter than the longest cycle.

The proof uses `SpliceData.exists_odd_longer_splice`: if the exterior cycle
were at least as long, the positive total linkage length would make one of
the four genuine splices both odd and longer than `C`, contradicting
`C.maximal`.
-/
theorem outside_odd_cycle_is_shorter_of_splice
    {C : LongestOddCycle G} (D : ExteriorOddCycle C)
    (L : TwoLinkage G C.carrier D.carrier)
    (S : TwoCycleSplice L C.length D.cycle.length) :
    D.cycle.length < C.length := by
  by_contra hnot
  have hCD : C.length ≤ D.cycle.length := by omega
  have hlink : 0 < L.p.length + L.q.length :=
    L.total_length_pos D.disjoint_longest_carrier
  have hlong := S.data.exists_odd_longer_splice
    S.c_length_sum S.d_length_sum C.odd D.odd_length hCD hlink
  rcases hlong with h | h | h | h
  · have hmax := C.maximal (S.parallel₁_mem_oddCycleLengths h.1)
    omega
  · have hmax := C.maximal (S.parallel₂_mem_oddCycleLengths h.1)
    omega
  · have hmax := C.maximal (S.crossed₁_mem_oddCycleLengths h.1)
    omega
  · have hmax := C.maximal (S.crossed₂_mem_oddCycleLengths h.1)
    omega

/-- Since both old cycle lengths are odd, strict shortness leaves a gap of at
least two.  This is the form used to separate the exterior length family
from the designated longest-cycle length in later counts. -/
theorem outside_odd_cycle_add_two_le_of_splice
    {C : LongestOddCycle G} (D : ExteriorOddCycle C)
    (L : TwoLinkage G C.carrier D.carrier)
    (S : TwoCycleSplice L C.length D.cycle.length) :
    D.cycle.length + 2 ≤ C.length := by
  have hlt := outside_odd_cycle_is_shorter_of_splice D L S
  rcases D.odd_length with ⟨d, hd⟩
  rcases C.odd with ⟨c, hc⟩
  omega

/-- Existential wrapper convenient after obtaining linkage and splice
certificates by separate construction lemmas. -/
theorem outside_odd_cycle_is_shorter
    {C : LongestOddCycle G} (D : ExteriorOddCycle C)
    (hsplice : ∃ (L : TwoLinkage G C.carrier D.carrier),
      Nonempty (TwoCycleSplice L C.length D.cycle.length)) :
    D.cycle.length < C.length := by
  obtain ⟨L, ⟨S⟩⟩ := hsplice
  exact outside_odd_cycle_is_shorter_of_splice D L S

/-- Existential form of the two-step odd-length gap. -/
theorem outside_odd_cycle_add_two_le
    {C : LongestOddCycle G} (D : ExteriorOddCycle C)
    (hsplice : ∃ (L : TwoLinkage G C.carrier D.carrier),
      Nonempty (TwoCycleSplice L C.length D.cycle.length)) :
    D.cycle.length + 2 ≤ C.length := by
  obtain ⟨L, ⟨S⟩⟩ := hsplice
  exact outside_odd_cycle_add_two_le_of_splice D L S

end Erdos58
