/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos58.Basic
import Mathlib.Tactic

/-!
# The three boundary counts in Gyárfás's odd-cycle argument

The last case split in Gyárfás's proof is entirely finite once the relevant
closed walks have been constructed.  This file isolates that finite part.
The input certificates contain actual `SimpleGraph.Walk`s and proofs that
they are simple cycles; consequently the output is a lower bound for the
genuine set `oddCycleLengths`, not for an auxiliary set of integers.

The four public conclusions correspond to the three boundary configurations
in the paper:

* `oneChordBoundary` is the `k ≥ 2` part of the configuration having one
  chord at each end of the longest outside path;
* `oneChordBoundary_one` is the explicit `k = 1` tail.  The positive
  `skipped` segment records the strict inequality obtained in each of the
  eight possible linear orders of the three marked positions;
* `sameNeighborhoodBoundary` is the no-chord/common-neighborhood case;
* `differentNeighborhoodBoundary` is the no-chord/different-neighborhood
  case, including both parity subcases and the unbalanced-prefix shortcut.

Keeping the geometric construction and the length count on opposite sides
of small certificate structures makes the later longest-cycle file usable:
it only has to fill fields by `Walk.append`, `Walk.reverse`, and the usual
support-disjointness cycle lemma.
-/

namespace Erdos58

open SimpleGraph

universe u

variable {V : Type u} [Finite V] {G : SimpleGraph V}

/-! ## Explicit cycles and the generic finite-family count -/

/-- A graph-theoretic certificate that `n` is the length of a simple cycle.
Unlike membership in `oddCycleLengths`, this structure does not include a
parity assertion. -/
def CycleAtLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (vertex : V) (walk : G.Walk vertex vertex),
    walk.IsCycle ∧ walk.length = n

namespace CycleAtLength

omit [Finite V] in
theorem mem_oddCycleLengths {n : ℕ} (h : CycleAtLength G n) (hn : Odd n) :
    n ∈ oddCycleLengths G := by
  obtain ⟨v, p, hp, hlen⟩ := h
  exact ⟨hn, v, p, hp, hlen⟩

end CycleAtLength

/-- An injective `Fin n`-indexed family of explicit odd cycles supplies at
least `n` different odd cycle lengths. -/
theorem ncard_oddCycleLengths_ge_of_injective {n : ℕ} (f : Fin n → ℕ)
    (hf : Function.Injective f) (hodd : ∀ i, Odd (f i))
    (hcycle : ∀ i, CycleAtLength G (f i)) :
    n ≤ (oddCycleLengths G).ncard := by
  let S : Set ℕ := Set.range f
  have hsub : S ⊆ oddCycleLengths G := by
    rintro _ ⟨i, rfl⟩
    exact (hcycle i).mem_oddCycleLengths (hodd i)
  calc
    n = S.ncard := by
      rw [Set.ncard_range_of_injective hf]
      simp
    _ ≤ (oddCycleLengths G).ncard :=
      Set.ncard_le_ncard hsub (oddCycleLengths_finite G)

/-- Finset form of the same counting principle. -/
theorem ncard_oddCycleLengths_ge_of_finset (L : Finset ℕ)
    (hodd : ∀ n ∈ L, Odd n) (hcycle : ∀ n ∈ L, CycleAtLength G n) :
    L.card ≤ (oddCycleLengths G).ncard := by
  have hsub : (L : Set ℕ) ⊆ oddCycleLengths G := by
    intro n hn
    exact (hcycle n hn).mem_oddCycleLengths (hodd n hn)
  simpa using Set.ncard_le_ncard hsub (oddCycleLengths_finite G)

/-! ## A reusable two-offset count -/

/-- The elementary count behind the nonexceptional part of the one-chord
boundary case.  The `k` lengths `b + r₁` are distinct, and the one length
`bMax + r₂` lies strictly above all of them. -/
theorem two_offset_boundary_count {k r₁ r₂ bMax : ℕ} (B : Finset ℕ)
    (hcard : B.card = k) (_hbMax : bMax ∈ B)
    (hmax : ∀ b ∈ B, b ≤ bMax) (hoff : r₁ < r₂)
    (hodd₁ : ∀ b ∈ B, Odd (b + r₁))
    (hodd₂ : Odd (bMax + r₂))
    (hcycle₁ : ∀ b ∈ B, CycleAtLength G (b + r₁))
    (hcycle₂ : CycleAtLength G (bMax + r₂)) :
    k + 1 ≤ (oddCycleLengths G).ncard := by
  let L : Finset ℕ := B.image (fun b => b + r₁)
  have hcardL : L.card = k := by
    rw [show L = B.image (fun b => b + r₁) by rfl,
      Finset.card_image_iff.mpr]
    · exact hcard
    · intro a ha b hb hab
      exact Nat.add_right_cancel hab
  have hextra : bMax + r₂ ∉ L := by
    intro hmem
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hmem
    have := hmax b hb
    omega
  let L' := insert (bMax + r₂) L
  have hcardL' : L'.card = k + 1 := by
    simp [L', hextra, hcardL]
  apply hcardL' ▸ ncard_oddCycleLengths_ge_of_finset (G := G) L'
  · intro n hn
    simp only [L', Finset.mem_insert, L, Finset.mem_image] at hn
    rcases hn with rfl | ⟨b, hb, rfl⟩
    · exact hodd₂
    · exact hodd₁ b hb
  · intro n hn
    simp only [L', Finset.mem_insert, L, Finset.mem_image] at hn
    rcases hn with rfl | ⟨b, hb, rfl⟩
    · exact hcycle₂
    · exact hcycle₁ b hb

/-! ## Lemma 6: one chord at each endpoint -/

/-- Certificate produced by the linear-order analysis in the one-chord
boundary case.  The paper's route calculation produces two same-parity
connection offsets `r₁ < r₂` and `k` ordered cyclic prefix lengths. -/
structure OneChordBoundaryCertificate (G : SimpleGraph V) (k : ℕ) where
  prefixes : Finset ℕ
  prefixMax : ℕ
  offset₁ : ℕ
  offset₂ : ℕ
  card_prefixes : prefixes.card = k
  prefixMax_mem : prefixMax ∈ prefixes
  prefix_le_max : ∀ b ∈ prefixes, b ≤ prefixMax
  offset_lt : offset₁ < offset₂
  first_odd : ∀ b ∈ prefixes, Odd (b + offset₁)
  last_odd : Odd (prefixMax + offset₂)
  first_cycles : ∀ b ∈ prefixes, CycleAtLength G (b + offset₁)
  last_cycle : CycleAtLength G (prefixMax + offset₂)

/-- Gyárfás boundary Lemma 6 for `k ≥ 2`, after the finite route-order
analysis has produced its walk certificate. -/
theorem oneChordBoundary {k : ℕ} (_hk : 2 ≤ k)
    (C : OneChordBoundaryCertificate G k) :
    k + 1 ≤ (oddCycleLengths G).ncard :=
  two_offset_boundary_count C.prefixes C.card_prefixes C.prefixMax_mem
    C.prefix_le_max C.offset_lt C.first_odd C.last_odd
    C.first_cycles C.last_cycle

/-- The explicit walk certificate for the `k = 1` tail of Lemma 6.  In each
of the eight orders considered in the mathematical proof, the second route
has the first route's length plus the positive segment `skipped`. -/
structure OneChordBoundaryOneCertificate (G : SimpleGraph V) where
  firstLength : ℕ
  skipped : ℕ
  skipped_pos : 0 < skipped
  first_odd : Odd firstLength
  first_cycle : CycleAtLength G firstLength
  second_cycle : CycleAtLength G (firstLength + skipped)
  second_odd : Odd (firstLength + skipped)

/-- The formerly implicit `k = 1` case: the two explicit closed walks have
different odd lengths because a nonempty path segment is skipped. -/
theorem oneChordBoundary_one (C : OneChordBoundaryOneCertificate G) :
    2 ≤ (oddCycleLengths G).ncard := by
  let f : Fin 2 → ℕ := fun i => if i = 0 then C.firstLength
    else C.firstLength + C.skipped
  apply ncard_oddCycleLengths_ge_of_injective (G := G) f
  · intro i j hij
    have hskip := C.skipped_pos
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
    all_goals omega
  · intro i
    fin_cases i
    · simpa [f] using C.first_odd
    · simpa [f] using C.second_odd
  · intro i
    fin_cases i
    · simpa [f] using C.first_cycle
    · simpa [f] using C.second_cycle

/-! ## Lemma 7: no endpoint chords and equal cycle neighborhoods -/

/-- The odd-`S` branch of the common-neighborhood boundary count.  `B` is
the selected `k`-element set of even proper cyclic prefix lengths. -/
theorem sameNeighborhoodBoundary_of_odd {k s : ℕ} (B : Finset ℕ)
    (hcard : B.card = k) (hpos : ∀ b ∈ B, 0 < b)
    (hs : Odd s) (hB : ∀ b ∈ B, Even b)
    (hbase : CycleAtLength G (s + 2))
    (hlong : ∀ b ∈ B, CycleAtLength G (b + s + 2)) :
    k + 1 ≤ (oddCycleLengths G).ncard := by
  let L : Finset ℕ := B.image (fun b => b + s + 2)
  have hcardL : L.card = k := by
    rw [show L = B.image (fun b => b + s + 2) by rfl,
      Finset.card_image_iff.mpr]
    · exact hcard
    · intro a ha b hb hab
      exact Nat.add_right_cancel (Nat.add_right_cancel hab)
  have hnot : s + 2 ∉ L := by
    intro hm
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hm
    have := hpos b hb
    omega
  let L' := insert (s + 2) L
  have hcardL' : L'.card = k + 1 := by simp [L', hnot, hcardL]
  apply hcardL' ▸ ncard_oddCycleLengths_ge_of_finset (G := G) L'
  · intro n hn
    simp only [L', Finset.mem_insert, L, Finset.mem_image] at hn
    rcases hn with rfl | ⟨b, hb, rfl⟩
    · rcases hs with ⟨t, rfl⟩
      exact ⟨t + 1, by omega⟩
    · rcases hs with ⟨t, ht⟩
      rcases hB b hb with ⟨q, hq⟩
      exact ⟨q + t + 1, by omega⟩
  · intro n hn
    simp only [L', Finset.mem_insert, L, Finset.mem_image] at hn
    rcases hn with rfl | ⟨b, hb, rfl⟩
    · exact hbase
    · exact hlong b hb

/-- The even-`S` branch of the common-neighborhood boundary count.  `B` is
the selected `k`-element set of odd proper cyclic prefix lengths. -/
theorem sameNeighborhoodBoundary_of_even {k s bMax : ℕ} (B : Finset ℕ)
    (hcard : B.card = k) (hspos : 0 < s) (hs : Even s)
    (hB : ∀ b ∈ B, Odd b) (hbMax : bMax ∈ B)
    (hmax : ∀ b ∈ B, b ≤ bMax)
    (hshort : ∀ b ∈ B, CycleAtLength G (b + 2))
    (hlong : CycleAtLength G (bMax + s + 2)) :
    k + 1 ≤ (oddCycleLengths G).ncard := by
  apply two_offset_boundary_count (G := G) B hcard hbMax hmax
    (show 2 < s + 2 by omega)
  · intro b hb
    rcases hB b hb with ⟨q, hq⟩
    exact ⟨q + 1, by omega⟩
  · rcases hB bMax hbMax with ⟨q, hq⟩
    rcases hs with ⟨t, ht⟩
    exact ⟨q + t + 1, by omega⟩
  · exact hshort
  · exact hlong

/-- A branch-complete certificate for Lemma 7.  It deliberately contains
both parity branches: at use sites `Nat.even_or_odd s` selects the applicable
one.  Only `2*k` of the common neighbors are used to construct these fields,
so the statement also covers the paper's final `2*k+1` invocation. -/
structure SameNeighborhoodCertificate (G : SimpleGraph V) (k s : ℕ) where
  path_pos : 0 < s
  oddPrefixes : Finset ℕ
  oddPrefixMax : ℕ
  evenPrefixes : Finset ℕ
  odd_card : oddPrefixes.card = k
  even_card : evenPrefixes.card = k
  odd_values : ∀ b ∈ oddPrefixes, Odd b
  even_values : ∀ b ∈ evenPrefixes, Even b
  oddPrefixMax_mem : oddPrefixMax ∈ oddPrefixes
  oddPrefix_le_max : ∀ b ∈ oddPrefixes, b ≤ oddPrefixMax
  even_pos : ∀ b ∈ evenPrefixes, 0 < b
  short_cycles : ∀ b ∈ oddPrefixes, CycleAtLength G (b + 2)
  even_path_long_cycle : CycleAtLength G (oddPrefixMax + s + 2)
  odd_path_base_cycle : CycleAtLength G (s + 2)
  odd_path_long_cycles : ∀ b ∈ evenPrefixes, CycleAtLength G (b + s + 2)

/-- Gyárfás boundary Lemma 7, including both parities of the outside path
and the `2*k`-subset form used when one more common neighbor is available. -/
theorem sameNeighborhoodBoundary {k s : ℕ}
    (C : SameNeighborhoodCertificate G k s) :
    k + 1 ≤ (oddCycleLengths G).ncard := by
  rcases Nat.even_or_odd s with hs | hs
  · exact sameNeighborhoodBoundary_of_even C.oddPrefixes C.odd_card
      C.path_pos hs C.odd_values C.oddPrefixMax_mem C.oddPrefix_le_max
      C.short_cycles C.even_path_long_cycle
  · exact sameNeighborhoodBoundary_of_odd C.evenPrefixes C.even_card
      C.even_pos hs C.even_values C.odd_path_base_cycle
      C.odd_path_long_cycles

/-! ## Lemma 8: no endpoint chords and different cycle neighborhoods -/

/-- If more than half of the `2*k` proper prefix lengths have one parity,
the ordinary two-edge fan cycles already give `k+1` lengths. -/
theorem differentNeighborhoodBoundary_unbalanced {k : ℕ}
    (P : Finset ℕ) (hcard : k + 1 ≤ P.card)
    (hodd : ∀ a ∈ P, Odd a)
    (hcycle : ∀ a ∈ P, CycleAtLength G (a + 2)) :
    k + 1 ≤ (oddCycleLengths G).ncard := by
  have hinj : Set.InjOn (fun a : ℕ => a + 2) P := by
    intro a _ b _ hab
    exact Nat.add_right_cancel hab
  have hfamily := ncard_oddCycleLengths_ge_of_finset (G := G)
    (P.image (fun a => a + 2))
    (by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
      rcases hodd a ha with ⟨q, hq⟩
      exact ⟨q + 1, by omega⟩)
    (by
      intro n hn
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hn
      exact hcycle a ha)
  rw [Finset.card_image_iff.mpr hinj] at hfamily
  exact hcard.trans hfamily

/-- First balanced-parity subcase of Lemma 8 (`a₁ + s` even). -/
theorem differentNeighborhoodBoundary_balanced_even {k a₁ s aMin : ℕ}
    (I : Finset ℕ) (hcard : I.card = k) (hspos : 0 < s)
    (haMin : aMin ∈ I) (ha₁ : ∀ a ∈ I, a₁ ≤ a)
    (hmin : ∀ a ∈ I, aMin ≤ a) (hparity : Even (a₁ + s))
    (hodd : ∀ a ∈ I, Odd (a + s + 2))
    (hlong : ∀ a ∈ I, CycleAtLength G (a + s + 2))
    (hshort : CycleAtLength G (aMin - a₁ + 2)) :
    k + 1 ≤ (oddCycleLengths G).ncard := by
  have hshortOdd : Odd (aMin - a₁ + 2) := by
    obtain ⟨u, hu⟩ := hparity
    obtain ⟨v, hv⟩ := hodd aMin haMin
    have hle := ha₁ aMin haMin
    refine ⟨v - u, ?_⟩
    omega
  let L : Finset ℕ := I.image (fun a => a + s + 2)
  have hcardL : L.card = k := by
    rw [show L = I.image (fun a => a + s + 2) by rfl,
      Finset.card_image_iff.mpr]
    · exact hcard
    · intro a ha b hb hab
      exact Nat.add_right_cancel (Nat.add_right_cancel hab)
  have hnot : aMin - a₁ + 2 ∉ L := by
    intro hm
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hm
    have h₁ := ha₁ aMin haMin
    have h₂ := hmin a ha
    omega
  let L' := insert (aMin - a₁ + 2) L
  have hcardL' : L'.card = k + 1 := by simp [L', hnot, hcardL]
  apply hcardL' ▸ ncard_oddCycleLengths_ge_of_finset (G := G) L'
  · intro n hn
    simp only [L', Finset.mem_insert, L, Finset.mem_image] at hn
    rcases hn with rfl | ⟨a, ha, rfl⟩
    · exact hshortOdd
    · exact hodd a ha
  · intro n hn
    simp only [L', Finset.mem_insert, L, Finset.mem_image] at hn
    rcases hn with rfl | ⟨a, ha, rfl⟩
    · exact hshort
    · exact hlong a ha

/-- Second balanced-parity subcase of Lemma 8 (`a₁ + s` odd). -/
theorem differentNeighborhoodBoundary_balanced_odd
    {k a₁ s cycleLength : ℕ} (I : Finset ℕ) (hcard : I.card = k)
    (hle : ∀ a ∈ I, a ≤ cycleLength)
    (hbaseOdd : Odd (a₁ + s + 2))
    (hcompOdd : ∀ a ∈ I, Odd (cycleLength - a + a₁ + 2))
    (hne : ∀ a ∈ I, cycleLength - a + a₁ + 2 ≠ a₁ + s + 2)
    (hbase : CycleAtLength G (a₁ + s + 2))
    (hcomp : ∀ a ∈ I,
      CycleAtLength G (cycleLength - a + a₁ + 2)) :
    k + 1 ≤ (oddCycleLengths G).ncard := by
  let L : Finset ℕ := I.image (fun a => cycleLength - a + a₁ + 2)
  have hinj : Set.InjOn (fun a : ℕ => cycleLength - a + a₁ + 2) I := by
    intro a ha b hb hab
    have ha' := hle a ha
    have hb' := hle b hb
    have hsub : cycleLength - a = cycleLength - b :=
      Nat.add_right_cancel (Nat.add_right_cancel hab)
    exact (tsub_right_inj ha' hb').mp hsub
  have hcardL : L.card = k := by
    rw [show L = I.image (fun a => cycleLength - a + a₁ + 2) by rfl,
      Finset.card_image_iff.mpr hinj, hcard]
  have hnot : a₁ + s + 2 ∉ L := by
    intro hm
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hm
    exact hne a ha heq
  let L' := insert (a₁ + s + 2) L
  have hcardL' : L'.card = k + 1 := by simp [L', hnot, hcardL]
  apply hcardL' ▸ ncard_oddCycleLengths_ge_of_finset (G := G) L'
  · intro n hn
    simp only [L', Finset.mem_insert, L, Finset.mem_image] at hn
    rcases hn with rfl | ⟨a, ha, rfl⟩
    · exact hbaseOdd
    · exact hcompOdd a ha
  · intro n hn
    simp only [L', Finset.mem_insert, L, Finset.mem_image] at hn
    rcases hn with rfl | ⟨a, ha, rfl⟩
    · exact hbase
    · exact hcomp a ha

/-- Branch-complete walk certificate for the different-neighborhood case.
`unbalanced` is the ordinary-fan shortcut.  If it is absent, the `2*k`
prefixes split evenly and `balanced_even`/`balanced_odd` provide the two
possible arithmetic constructions from the proof. -/
inductive DifferentNeighborhoodCertificate (G : SimpleGraph V) (k : ℕ) :
    Prop
  | unbalanced (P : Finset ℕ)
      (card : k + 1 ≤ P.card)
      (odd : ∀ a ∈ P, Odd a)
      (cycles : ∀ a ∈ P, CycleAtLength G (a + 2))
  | balanced_even (a₁ s aMin : ℕ) (I : Finset ℕ)
      (card : I.card = k) (path_pos : 0 < s)
      (min_mem : aMin ∈ I) (first_le : ∀ a ∈ I, a₁ ≤ a)
      (min_le : ∀ a ∈ I, aMin ≤ a) (parity : Even (a₁ + s))
      (odd : ∀ a ∈ I, Odd (a + s + 2))
      (long_cycles : ∀ a ∈ I, CycleAtLength G (a + s + 2))
      (short_cycle : CycleAtLength G (aMin - a₁ + 2))
  | balanced_odd (a₁ s cycleLength : ℕ) (I : Finset ℕ)
      (card : I.card = k) (le_cycle : ∀ a ∈ I, a ≤ cycleLength)
      (base_odd : Odd (a₁ + s + 2))
      (comp_odd : ∀ a ∈ I, Odd (cycleLength - a + a₁ + 2))
      (ne_base : ∀ a ∈ I,
        cycleLength - a + a₁ + 2 ≠ a₁ + s + 2)
      (base_cycle : CycleAtLength G (a₁ + s + 2))
      (comp_cycles : ∀ a ∈ I,
        CycleAtLength G (cycleLength - a + a₁ + 2))

/-- Gyárfás boundary Lemma 8, with the same/different-neighborhood split
already resolved to one of its three explicit finite walk certificates. -/
theorem differentNeighborhoodBoundary {k : ℕ}
    (C : DifferentNeighborhoodCertificate G k) :
    k + 1 ≤ (oddCycleLengths G).ncard := by
  cases C with
  | unbalanced P card odd cycles =>
      exact differentNeighborhoodBoundary_unbalanced P card odd cycles
  | balanced_even a₁ s aMin I card path_pos min_mem first_le min_le parity odd
      long_cycles short_cycle =>
      exact differentNeighborhoodBoundary_balanced_even I card path_pos
        min_mem first_le min_le parity odd long_cycles short_cycle
  | balanced_odd a₁ s cycleLength I card le_cycle base_odd comp_odd ne_base
      base_cycle comp_cycles =>
      exact differentNeighborhoodBoundary_balanced_odd I card le_cycle
        base_odd comp_odd ne_base base_cycle comp_cycles

end Erdos58
