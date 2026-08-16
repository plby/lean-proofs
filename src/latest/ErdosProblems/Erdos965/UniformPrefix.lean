import ErdosProblems.Erdos965.Countability
import ErdosProblems.Erdos965.CriticalPair

open Function Set

universe u v

namespace Erdos965

noncomputable section

/-! ## Ordered coordinates for fixed-cardinality finite sets -/

variable {ι : Type u} {α : Type v}

/-- The increasing enumeration of a finite set whose cardinality is known. -/
def finsetCoord [LinearOrder α] {n : ℕ} (F : ι → Finset α)
    (hcard : ∀ i, (F i).card = n) (i : ι) : Fin n → α :=
  (F i).orderEmbOfFin (hcard i)

theorem finsetCoord_mem [LinearOrder α] {n : ℕ} (F : ι → Finset α)
    (hcard : ∀ i, (F i).card = n) (i : ι) (j : Fin n) :
    finsetCoord F hcard i j ∈ F i := by
  exact Finset.orderEmbOfFin_mem _ _ _

theorem finsetCoord_injective [LinearOrder α] {n : ℕ} (F : ι → Finset α)
    (hcard : ∀ i, (F i).card = n) (i : ι) :
    Injective (finsetCoord F hcard i) := by
  exact ((F i).orderEmbOfFin (hcard i)).injective

theorem finsetCoord_strictMono [LinearOrder α] {n : ℕ} (F : ι → Finset α)
    (hcard : ∀ i, (F i).card = n) (i : ι) :
    StrictMono (finsetCoord F hcard i) := by
  exact ((F i).orderEmbOfFin (hcard i)).strictMono

theorem range_finsetCoord [LinearOrder α] {n : ℕ} (F : ι → Finset α)
    (hcard : ∀ i, (F i).card = n) (i : ι) :
    Set.range (finsetCoord F hcard i) = (F i : Set α) := by
  exact Finset.range_orderEmbOfFin _ _

/-! ## A common finite prefix separating one finite set -/

/-- One more than the largest first-difference level occurring among pairs
of elements of `s`.  Restriction to this many bits is injective on `s`. -/
def separationLength (s : Finset HamelIndex) : ℕ :=
  s.sup fun x ↦ s.sup fun y ↦ firstDiff x y + 1

theorem firstDiff_lt_separationLength {s : Finset HamelIndex} {x y : HamelIndex}
    (hx : x ∈ s) (hy : y ∈ s) :
    firstDiff x y < separationLength s := by
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  dsimp [separationLength]
  exact (Finset.le_sup (s := s) (f := fun y ↦ firstDiff x y + 1) hy).trans
    (Finset.le_sup (s := s) (f := fun x ↦
      s.sup fun y ↦ firstDiff x y + 1) hx)

/-- If two finite prefixes differ, the first differing bit occurs inside the
prefix. -/
theorem firstDiff_lt_of_res_ne {x y : HamelIndex} {L : ℕ}
    (hres : PiNat.res (binaryCode x) L ≠ PiNat.res (binaryCode y) L) :
    firstDiff x y < L := by
  by_contra h
  apply hres
  rw [PiNat.res_eq_res]
  intro m hm
  exact binaryCode_apply_eq_of_lt_firstDiff
    (hm.trans_le (le_of_not_gt h))

/-- A first difference inside the restriction length makes the restrictions
different. -/
theorem res_ne_of_firstDiff_lt {x y : HamelIndex} {L : ℕ}
    (hxy : x ≠ y) (hfd : firstDiff x y < L) :
    PiNat.res (binaryCode x) L ≠ PiNat.res (binaryCode y) L := by
  intro hres
  have heq := PiNat.res_eq_res.mp hres hfd
  exact binaryCode_apply_firstDiff_ne hxy heq

theorem res_separation_injOn (s : Finset HamelIndex) :
    Set.InjOn (fun x ↦ PiNat.res (binaryCode x) (separationLength s))
      (s : Set HamelIndex) := by
  intro x hx y hy hres
  by_contra hxy
  exact res_ne_of_firstDiff_lt hxy
    (firstDiff_lt_separationLength (by simpa using hx) (by simpa using hy)) hres

/-! ## Uniform-prefix thinning -/

/-- The common data retained when thinning a fixed-size family: a restriction
length, followed by one finite binary prefix for each ordered coordinate. -/
abbrev PrefixRecord (n : ℕ) := ℕ × (Fin n → List Bool)

instance prefixRecord_countable (n : ℕ) : Countable (PrefixRecord n) :=
  inferInstance

def prefixRecord {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) (i : ι) : PrefixRecord n :=
  let L := separationLength (F i)
  (L, fun j ↦ PiNat.res (binaryCode (finsetCoord F hcard i j)) L)

/-- An uncountable subfamily on which the separating restriction length and
all coordinate prefixes are constant. -/
structure UniformPrefixWitness {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) where
  carrier : Set ι
  uncountable : ¬ carrier.Countable
  L : ℕ
  prefixes : Fin n → List Bool
  prefixes_injective : Injective prefixes
  prefix_eq : ∀ i ∈ carrier, ∀ j,
    PiNat.res (binaryCode (finsetCoord F hcard i j)) L = prefixes j

/-- Thin an uncountable fixed-cardinality family to a uniform-prefix witness. -/
theorem exists_uniformPrefixWitness {n : ℕ} (F : ι → Finset HamelIndex)
    (hcard : ∀ i, (F i).card = n) {I : Set ι} (hI : ¬ I.Countable) :
    ∃ W : UniformPrefixWitness F hcard, W.carrier ⊆ I := by
  let recordOf : ι → PrefixRecord n := prefixRecord F hcard
  obtain ⟨r, hr⟩ := uncountable_fiber_of_countable_range recordOf hI
  let J : Set ι := {i ∈ I | recordOf i = r}
  have hJ : ¬ J.Countable := hr
  have hJne : J.Nonempty := by
    by_contra hn
    exact hJ (Set.not_nonempty_iff_eq_empty.mp hn ▸ Set.countable_empty)
  obtain ⟨i₀, hi₀J⟩ := hJne
  let L := r.1
  let p : Fin n → List Bool := r.2
  have hrecord₀ : recordOf i₀ = r := hi₀J.2
  have hL : separationLength (F i₀) = L := congrArg Prod.fst hrecord₀
  have hp : ∀ j, PiNat.res (binaryCode (finsetCoord F hcard i₀ j)) L = p j := by
    intro j
    have h := congrFun (congrArg Prod.snd hrecord₀) j
    simpa [recordOf, prefixRecord, L, p, hL] using h
  have hpinj : Injective p := by
    intro j k hjk
    apply finsetCoord_injective F hcard i₀
    apply res_separation_injOn (F i₀)
    · exact finsetCoord_mem F hcard i₀ j
    · exact finsetCoord_mem F hcard i₀ k
    change PiNat.res (binaryCode (finsetCoord F hcard i₀ j))
        (separationLength (F i₀)) =
      PiNat.res (binaryCode (finsetCoord F hcard i₀ k))
        (separationLength (F i₀))
    rw [hL, hp j, hp k, hjk]
  refine ⟨{
    carrier := J
    uncountable := hJ
    L := L
    prefixes := p
    prefixes_injective := hpinj
    prefix_eq := ?_ }, fun _ hi ↦ hi.1⟩
  intro i hi j
  have hrecord : recordOf i = r := hi.2
  have hLi : separationLength (F i) = L := congrArg Prod.fst hrecord
  have h := congrFun (congrArg Prod.snd hrecord) j
  simpa [recordOf, prefixRecord, L, p, hLi] using h

/-- Distinct ordered coordinates, even in two different members of the
uniform family, split before the common restriction length. -/
theorem UniformPrefixWitness.crossCoordinate_firstDiff_lt {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n)
    (W : UniformPrefixWitness F hcard) {i k : ι} (hi : i ∈ W.carrier)
    (hk : k ∈ W.carrier) {j l : Fin n} (hjl : j ≠ l) :
    firstDiff (finsetCoord F hcard i j) (finsetCoord F hcard k l) < W.L := by
  apply firstDiff_lt_of_res_ne
  rw [W.prefix_eq i hi j, W.prefix_eq k hk l]
  exact W.prefixes_injective.ne hjl

end

end Erdos965
