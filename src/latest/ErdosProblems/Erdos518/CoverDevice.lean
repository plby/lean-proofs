/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Cover
import ErdosProblems.Erdos518.Alternating
import ErdosProblems.Erdos518.Selection

/-!
# The Chen--Chen red covering device

This file formalizes Lemma 3.5 of Chen--Chen.  The ambient graph is the red graph.  The finite
sets `X`, `Y₀`, and `Y₁` are pairwise disjoint, `D ⊆ X`, every `Y₀`--`X` edge is red, and each
vertex of `Y₁` has at most `μ` non-red neighbours in `X`.

Paths in distinct members of a cover are allowed to reuse vertices of `Y₀` and `Y₁`; the path
predicate itself is `IsPath`, so every individual member remains duplicate-free.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

/-- The integer excess in Chen--Chen's covering device. -/
def coverDeviceP (D Y₀ : Finset V) (h : ℕ) : ℤ :=
  (D.card : ℤ) - (h * (Y₀.card + 1) : ℕ)

/-- The natural number of exceptional rows.  When `coverDeviceP > 0`, this is exactly
`min coverDeviceP h`, with both entries regarded as nonnegative integers. -/
def coverDeviceQ (D Y₀ : Finset V) (h : ℕ) : ℕ :=
  min (coverDeviceP D Y₀ h).toNat h

lemma coverDeviceP_nonpos_iff {D Y₀ : Finset V} {h : ℕ} :
    coverDeviceP D Y₀ h ≤ 0 ↔ D.card ≤ h * (Y₀.card + 1) := by
  simp only [coverDeviceP]
  omega

lemma coverDeviceP_pos_toNat {D Y₀ : Finset V} {h : ℕ}
    (hp : 0 < coverDeviceP D Y₀ h) :
    (coverDeviceP D Y₀ h).toNat = D.card - h * (Y₀.card + 1) := by
  simp only [coverDeviceP] at hp ⊢
  omega

/-- The canonical alternating path for a small `X`-block. -/
noncomputable def smallBlockPath (Y₀ : Finset V) (block : List V) : List V :=
  alternate block (Y₀.toList.take (block.length - 1))

lemma isPath_smallBlockPath {G : SimpleGraph V} {X Y₀ : Finset V} {block : List V}
    (hblock0 : block ≠ []) (hblockNodup : block.Nodup)
    (hblockX : ∀ x ∈ block, x ∈ X) (hblockCard : block.length ≤ Y₀.card + 1)
    (hXY₀ : Disjoint X Y₀)
    (hcomplete₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj y x) :
    IsPath G (smallBlockPath Y₀ block) := by
  classical
  let ys := Y₀.toList.take (block.length - 1)
  have hpos : 1 ≤ block.length := by
    cases block with
    | nil => contradiction
    | cons => simp
  have hsub : block.length - 1 ≤ Y₀.card := by omega
  have hysLen : ys.length = block.length - 1 := by
    simp [ys, List.length_take, hsub]
  have hlen : block.length = ys.length + 1 := by omega
  have hysNodup : ys.Nodup := (Finset.nodup_toList Y₀).take
  have hdisj : List.Disjoint block ys := by
    intro z hzBlock hzYs
    have hzX : z ∈ X := hblockX z hzBlock
    have hzY₀ : z ∈ Y₀ := by
      apply Finset.mem_toList.mp
      exact List.mem_of_mem_take hzYs
    exact Finset.disjoint_left.mp hXY₀ hzX hzY₀
  apply isPath_alternate_of_length_eq_add_one hlen hblockNodup hysNodup hdisj
  intro x hx y hy
  exact (hcomplete₀ y (Finset.mem_toList.mp (List.mem_of_mem_take hy)) x (hblockX x hx)).symm

/-- If `D` fits into `h` ordinary blocks of capacity `|Y₀|+1`, it has a red cover of size at
most `h`.  Empty terminal blocks are discarded, since paths are nonempty. -/
lemma coverDevice_small_blocks {G : SimpleGraph V} {X Y₀ D : Finset V} {h : ℕ}
    (hDX : D ⊆ X) (hcard : D.card ≤ h * (Y₀.card + 1))
    (hXY₀ : Disjoint X Y₀)
    (hcomplete₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj y x) :
    HasPathCoverOnAtMost G (D : Set V) h := by
  classical
  let capacity := Y₀.card + 1
  let sizes : List ℕ := List.replicate h capacity
  let blocks : List (List V) := sizes.splitLengths D.toList
  let liveBlocks := blocks.filter fun block ↦ block ≠ []
  let paths := liveBlocks.map (smallBlockPath Y₀)
  have hsizesSum : D.toList.length ≤ sizes.sum := by
    simp [sizes, capacity]
    simpa using hcard
  have hflatten : blocks.flatten = D.toList := by
    exact List.flatten_splitLengths D.toList sizes hsizesSum
  have hblocksNodup : ∀ block ∈ blocks, block.Nodup := by
    have h := List.nodup_flatten.mp (hflatten.symm ▸ Finset.nodup_toList D)
    exact h.1
  have hblockCapacity : ∀ block ∈ blocks, block.length ≤ capacity := by
    apply List.length_mem_splitLengths D.toList sizes capacity
    intro n hn
    simp [sizes] at hn
    omega
  refine ⟨paths, ?_, ?_⟩
  · calc
      paths.length = liveBlocks.length := by simp [paths]
      _ ≤ blocks.length := List.length_filter_le _ _
      _ = h := by simp [blocks, sizes]
  · constructor
    · intro path hpath
      obtain ⟨block, hblockLive, rfl⟩ := List.mem_map.mp hpath
      have hblock : block ∈ blocks := (List.mem_filter.mp hblockLive).1
      have hblock0 : block ≠ [] := by
        simpa using (List.mem_filter.mp hblockLive).2
      apply isPath_smallBlockPath hblock0 (hblocksNodup block hblock)
      · intro x hx
        apply hDX
        apply Finset.mem_toList.mp
        rw [← hflatten]
        exact List.mem_flatten.mpr ⟨block, hblock, hx⟩
      · exact hblockCapacity block hblock
      · exact hXY₀
      · exact hcomplete₀
    · intro x hxD
      have hxList : x ∈ D.toList := Finset.mem_toList.mpr hxD
      rw [← hflatten] at hxList
      obtain ⟨block, hblock, hxBlock⟩ := List.mem_flatten.mp hxList
      have hblock0 : block ≠ [] := fun hnil ↦ by simpa [hnil] using hxBlock
      have hblockLive : block ∈ liveBlocks := by
        exact List.mem_filter.mpr ⟨hblock, by simpa⟩
      refine ⟨smallBlockPath Y₀ block, List.mem_map.mpr ⟨block, hblockLive, rfl⟩, ?_⟩
      exact mem_alternate_left hxBlock

/-- Case (i) of Chen--Chen Lemma 3.5, stated with the paper's integer `p`. -/
theorem coverDevice_case_one {G : SimpleGraph V} {X Y₀ D : Finset V} {h : ℕ}
    (hDX : D ⊆ X) (hXY₀ : Disjoint X Y₀)
    (hcomplete₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj y x)
    (hp : coverDeviceP D Y₀ h ≤ 0) :
    HasPathCoverOnAtMost G (D : Set V) h := by
  exact coverDevice_small_blocks hDX (coverDeviceP_nonpos_iff.mp hp) hXY₀ hcomplete₀

/-! ## One exceptional block -/

/-- A two-vertex seed joined through `z`, followed by an ordinary alternating `Y₀` tail.  Inputs
other than a two-element seed are irrelevant and are assigned the empty list. -/
noncomputable def exceptionalBlockPathUV (z : V) (Y₀ : Finset V)
    (u v : V) (filler : List V) : List V :=
  u :: z :: alternate (v :: filler) (Y₀.toList.take filler.length)

noncomputable def exceptionalBlockPath (z : V) (Y₀ : Finset V)
    (seed filler : List V) : List V :=
  match seed with
  | [u, v] => exceptionalBlockPathUV z Y₀ u v filler
  | _ => []

lemma mem_exceptionalBlockPath_of_mem_seed {z : V} {Y₀ : Finset V}
    {seed filler : List V} (hseed : seed.length = 2) {x : V} (hx : x ∈ seed) :
    x ∈ exceptionalBlockPath z Y₀ seed filler := by
  obtain ⟨u, v, rfl⟩ : ∃ u v, seed = [u, v] := by
    cases seed with
    | nil => simp at hseed
    | cons u tail =>
        cases tail with
        | nil => simp at hseed
        | cons v tail =>
            cases tail with
            | nil => exact ⟨u, v, rfl⟩
            | cons w tail => simp only [List.length_cons, List.length_nil] at hseed; omega
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> simp [exceptionalBlockPath, exceptionalBlockPathUV]

lemma mem_exceptionalBlockPath_of_mem_filler {z : V} {Y₀ : Finset V}
    {seed filler : List V} (hseed : seed.length = 2) {x : V} (hx : x ∈ filler) :
    x ∈ exceptionalBlockPath z Y₀ seed filler := by
  obtain ⟨u, v, rfl⟩ : ∃ u v, seed = [u, v] := by
    cases seed with
    | nil => simp at hseed
    | cons u tail =>
        cases tail with
        | nil => simp at hseed
        | cons v tail =>
            cases tail with
            | nil => exact ⟨u, v, rfl⟩
            | cons w tail => simp only [List.length_cons, List.length_nil] at hseed; omega
  have hxa : x ∈ alternate (v :: filler) (Y₀.toList.take filler.length) :=
    mem_alternate_left (List.mem_cons_of_mem v hx)
  simp only [exceptionalBlockPath, exceptionalBlockPathUV, List.mem_cons]
  exact Or.inr (Or.inr hxa)

lemma isPath_exceptionalBlockPathUV {G : SimpleGraph V} {X Y₀ Y₁ : Finset V}
    {z u v : V} {filler : List V}
    (hz : z ∈ Y₁) (huX : u ∈ X) (hvX : v ∈ X) (huv : u ≠ v)
    (hfillerNodup : filler.Nodup) (hfillerX : ∀ x ∈ filler, x ∈ X)
    (huFiller : u ∉ filler) (hvFiller : v ∉ filler)
    (hfillerCard : filler.length ≤ Y₀.card)
    (hXY₀ : Disjoint X Y₀) (hXY₁ : Disjoint X Y₁) (hY₀Y₁ : Disjoint Y₀ Y₁)
    (hcomplete₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj y x)
    (huz : G.Adj z u) (hvz : G.Adj z v) :
    IsPath G (exceptionalBlockPathUV z Y₀ u v filler) := by
  classical
  let ys := Y₀.toList.take filler.length
  let tail := alternate (v :: filler) ys
  have hysLen : ys.length = filler.length := by
    simp [ys, List.length_take, hfillerCard]
  have htail : IsPath G tail := by
    apply isPath_alternate_of_length_eq_add_one
    · simp [hysLen]
    · exact List.nodup_cons.mpr ⟨hvFiller, hfillerNodup⟩
    · exact (Finset.nodup_toList Y₀).take
    · intro a haX haY
      have haX' : a ∈ X := by
        rcases (by simpa [tail] using haX : a = v ∨ a ∈ filler) with rfl | ha
        · exact hvX
        · exact hfillerX a ha
      have haY₀ : a ∈ Y₀ := Finset.mem_toList.mp (List.mem_of_mem_take haY)
      exact Finset.disjoint_left.mp hXY₀ haX' haY₀
    · intro x hx y hy
      have hxX : x ∈ X := by
        rcases (by simpa [tail] using hx : x = v ∨ x ∈ filler) with rfl | hx
        · exact hvX
        · exact hfillerX x hx
      exact (hcomplete₀ y (Finset.mem_toList.mp (List.mem_of_mem_take hy)) x hxX).symm
  have hzTail : z ∉ tail := by
    intro hzt
    rcases mem_alternate.mp hzt with hzX | hzY
    · have hzX' : z ∈ X := by
        rcases (by simpa [tail] using hzX : z = v ∨ z ∈ filler) with h | h
        · exact h ▸ hvX
        · exact hfillerX z h
      exact Finset.disjoint_left.mp hXY₁ hzX' hz
    · have hzY₀ : z ∈ Y₀ := Finset.mem_toList.mp (List.mem_of_mem_take hzY)
      exact Finset.disjoint_left.mp hY₀Y₁ hzY₀ hz
  have huTail : u ∉ tail := by
    intro hut
    rcases mem_alternate.mp hut with huXtail | huY
    · rcases (by simpa [tail] using huXtail : u = v ∨ u ∈ filler) with huv' | huf
      · exact huv huv'
      · exact huFiller huf
    · have huY₀ : u ∈ Y₀ := Finset.mem_toList.mp (List.mem_of_mem_take huY)
      exact Finset.disjoint_left.mp hXY₀ huX huY₀
  have huzNe : u ≠ z := by
    intro heq
    exact Finset.disjoint_left.mp hXY₁ huX (heq ▸ hz)
  have hnodup : (u :: z :: tail).Nodup := by
    simp only [List.nodup_cons]
    exact ⟨by simp [huzNe, huTail], hzTail, htail.2.1⟩
  have hchain : (u :: z :: tail).IsChain G.Adj := by
    rw [List.isChain_cons]
    refine ⟨by simpa using huz.symm, ?_⟩
    rw [List.isChain_cons]
    refine ⟨?_, htail.2.2⟩
    simpa [tail, ys] using hvz
  exact ⟨by simp [exceptionalBlockPathUV], hnodup, hchain⟩

lemma isPath_exceptionalBlockPath {G : SimpleGraph V} {X Y₀ Y₁ : Finset V}
    {z : V} {seed filler : List V}
    (hz : z ∈ Y₁) (hseedLen : seed.length = 2) (hseedNodup : seed.Nodup)
    (hfillerNodup : filler.Nodup) (hseedX : ∀ x ∈ seed, x ∈ X)
    (hfillerX : ∀ x ∈ filler, x ∈ X) (hseedFiller : List.Disjoint seed filler)
    (hfillerCard : filler.length ≤ Y₀.card)
    (hXY₀ : Disjoint X Y₀) (hXY₁ : Disjoint X Y₁) (hY₀Y₁ : Disjoint Y₀ Y₁)
    (hcomplete₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj y x)
    (hzSeed : ∀ x ∈ seed, G.Adj z x) :
    IsPath G (exceptionalBlockPath z Y₀ seed filler) := by
  classical
  obtain ⟨u, v, rfl⟩ : ∃ u v, seed = [u, v] := by
    cases seed with
    | nil => simp at hseedLen
    | cons u tail =>
        cases tail with
        | nil => simp at hseedLen
        | cons v tail =>
            cases tail with
            | nil => exact ⟨u, v, rfl⟩
            | cons w tail =>
                simp only [List.length_cons, List.length_nil] at hseedLen
                omega
  apply isPath_exceptionalBlockPathUV hz
  · exact hseedX u (by simp)
  · exact hseedX v (by simp)
  · simpa using hseedNodup
  · exact hfillerNodup
  · exact hfillerX
  · intro hu
    exact hseedFiller (by simp) hu
  · intro hv
    exact hseedFiller (by simp) hv
  · exact hfillerCard
  · exact hXY₀
  · exact hXY₁
  · exact hY₀Y₁
  · exact hcomplete₀
  · exact hzSeed u (by simp)
  · exact hzSeed v (by simp)

/-- Partition `D` into `p` exceptional blocks, each seeded by two vertices joined to `z`, and
`h-p` ordinary blocks.  The displayed cardinal identity is precisely the identity obtained from
the positive integer excess `p = d-h(a₀+1)`. -/
lemma coverDevice_exceptional_blocks {G : SimpleGraph V}
    {X Y₀ Y₁ D M : Finset V} {z : V} {h p : ℕ}
    (hDX : D ⊆ X) (hz : z ∈ Y₁) (hp : p ≤ h)
    (hcard : D.card = h * (Y₀.card + 1) + p)
    (hMD : M ⊆ D) (hMcard : M.card = 2 * p)
    (hzM : ∀ x ∈ M, G.Adj z x)
    (hXY₀ : Disjoint X Y₀) (hXY₁ : Disjoint X Y₁) (hY₀Y₁ : Disjoint Y₀ Y₁)
    (hcomplete₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj y x) :
    HasPathCoverOnAtMost G (D : Set V) h := by
  classical
  let R := D \ M
  let seedSizes : List ℕ := List.replicate p 2
  let seeds : List (List V) := seedSizes.splitLengths M.toList
  let fillerSizes : List ℕ :=
    List.replicate p Y₀.card ++ List.replicate (h - p) (Y₀.card + 1)
  let fillers : List (List V) := fillerSizes.splitLengths R.toList
  have hRcard : R.card = p * Y₀.card + (h - p) * (Y₀.card + 1) := by
    have hpBig : p ≤ h * (Y₀.card + 1) :=
      hp.trans (Nat.le_mul_of_pos_right h (by omega))
    have hmul : p * (Y₀.card + 1) ≤ h * (Y₀.card + 1) :=
      Nat.mul_le_mul_right (Y₀.card + 1) hp
    have sub_decomp (A B C : ℕ) (hABC : A + B ≤ C) :
        C - B = A + (C - (A + B)) := by
      omega
    calc
      R.card = D.card - M.card := by
        dsimp only [R]
        exact Finset.card_sdiff_of_subset hMD
      _ = h * (Y₀.card + 1) + p - 2 * p := by rw [hcard, hMcard]
      _ = h * (Y₀.card + 1) - p := by omega
      _ = p * Y₀.card + (h - p) * (Y₀.card + 1) := by
        rw [Nat.sub_mul]
        have hmul' : p * Y₀.card + p ≤ h * (Y₀.card + 1) := by
          simpa [Nat.mul_add, Nat.mul_one] using hmul
        simpa [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
          sub_decomp (p * Y₀.card) p (h * (Y₀.card + 1)) hmul'
  have hseedSum : seedSizes.sum = M.toList.length := by
    simp [seedSizes, hMcard]
    omega
  have hfillerSum : fillerSizes.sum = R.toList.length := by
    simp [fillerSizes, hRcard]
  have hseedsLength : seeds.length = p := by simp [seeds, seedSizes]
  have hfillersLength : fillers.length = h := by
    simp [fillers, fillerSizes, hp]
  have hseedsFlat : seeds.flatten = M.toList := by
    exact List.flatten_splitLengths M.toList seedSizes hseedSum.ge
  have hfillersFlat : fillers.flatten = R.toList := by
    exact List.flatten_splitLengths R.toList fillerSizes hfillerSum.ge
  have hseedsNodup : ∀ seed ∈ seeds, seed.Nodup :=
    (List.nodup_flatten.mp (hseedsFlat.symm ▸ Finset.nodup_toList M)).1
  have hfillersNodup : ∀ filler ∈ fillers, filler.Nodup :=
    (List.nodup_flatten.mp (hfillersFlat.symm ▸ Finset.nodup_toList R)).1
  have hseedLen : ∀ i (hi : i < seeds.length), seeds[i].length = 2 := by
    intro i hi
    have hle : seedSizes.sum ≤ M.toList.length := hseedSum.le
    have h := List.splitLengths_length_getElem M.toList seedSizes hle i hi
    simpa [seedSizes] using h
  have hfillerLen : ∀ i (hi : i < fillers.length), fillers[i].length =
      if i < p then Y₀.card else Y₀.card + 1 := by
    intro i hi
    have hle : fillerSizes.sum ≤ R.toList.length := hfillerSum.le
    have h := List.splitLengths_length_getElem R.toList fillerSizes hle i hi
    simp only [fillers, List.length_splitLengths] at hi
    simp [fillerSizes, hi, hp] at h ⊢
    split_ifs with hip
    · simpa [hip] using h
    · have hpi : p ≤ i := Nat.le_of_not_gt hip
      simpa [hip, hpi, Nat.sub_add_cancel hp] using h
  have hseedSubset : ∀ i (hi : i < seeds.length), ∀ x ∈ seeds[i], x ∈ M := by
    intro i hi x hx
    apply Finset.mem_toList.mp
    rw [← hseedsFlat]
    exact List.mem_flatten.mpr ⟨seeds[i], List.getElem_mem hi, hx⟩
  have hfillerSubset : ∀ i (hi : i < fillers.length), ∀ x ∈ fillers[i], x ∈ R := by
    intro i hi x hx
    apply Finset.mem_toList.mp
    rw [← hfillersFlat]
    exact List.mem_flatten.mpr ⟨fillers[i], List.getElem_mem hi, hx⟩
  let pathAt : Fin h → List V := fun i ↦
    if hip : i.1 < p then
      exceptionalBlockPath z Y₀
        (seeds[i.1]'(by simpa [hseedsLength] using hip))
        (fillers[i.1]'(by simpa [hfillersLength] using i.2))
    else
      smallBlockPath Y₀ (fillers[i.1]'(by simpa [hfillersLength] using i.2))
  let paths : List (List V) := List.ofFn pathAt
  have hpathAt (i : Fin h) : IsPath G (pathAt i) := by
    have hfi : i.1 < fillers.length := by simpa [hfillersLength] using i.2
    by_cases hip : i.1 < p
    · have hsi : i.1 < seeds.length := by simpa [hseedsLength] using hip
      simp only [pathAt, dif_pos hip]
      apply isPath_exceptionalBlockPath hz (hseedLen i.1 hsi)
      · exact hseedsNodup _ (List.getElem_mem hsi)
      · exact hfillersNodup _ (List.getElem_mem hfi)
      · intro x hx
        exact hDX (hMD (hseedSubset i.1 hsi x hx))
      · intro x hx
        exact hDX (Finset.sdiff_subset (hfillerSubset i.1 hfi x hx))
      · intro x hxSeed hxFiller
        have hxM : x ∈ M := hseedSubset i.1 hsi x hxSeed
        have hxR : x ∈ R := hfillerSubset i.1 hfi x hxFiller
        exact (Finset.mem_sdiff.mp hxR).2 hxM
      · simpa [hip] using (hfillerLen i.1 hfi).le
      · exact hXY₀
      · exact hXY₁
      · exact hY₀Y₁
      · exact hcomplete₀
      · intro x hx
        exact hzM x (hseedSubset i.1 hsi x hx)
    · simp only [pathAt, dif_neg hip]
      apply isPath_smallBlockPath
      · intro hempty
        have hlen := hfillerLen i.1 hfi
        rw [hempty] at hlen
        simp [hip] at hlen
      · exact hfillersNodup _ (List.getElem_mem hfi)
      · intro x hx
        exact hDX (Finset.sdiff_subset (hfillerSubset i.1 hfi x hx))
      · rw [hfillerLen i.1 hfi, if_neg hip]
      · exact hXY₀
      · exact hcomplete₀
  refine ⟨paths, by simp [paths], ?_⟩
  constructor
  · intro path hpath
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa [paths] using hpath)
    exact hpathAt i
  · intro x hxD
    by_cases hxM : x ∈ M
    · have hxList : x ∈ M.toList := Finset.mem_toList.mpr hxM
      rw [← hseedsFlat] at hxList
      obtain ⟨seed, hseedMem, hxSeed⟩ := List.mem_flatten.mp hxList
      obtain ⟨i, hi, hseedEq⟩ := List.mem_iff_getElem.mp hseedMem
      have hip : i < p := by simpa [hseedsLength] using hi
      have hih : i < h := hip.trans_le hp
      let j : Fin h := ⟨i, hih⟩
      refine ⟨pathAt j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
      simp only [pathAt, j, dif_pos hip]
      apply mem_exceptionalBlockPath_of_mem_seed (hseedLen i hi)
      simpa [hseedEq] using hxSeed
    · have hxR : x ∈ R := Finset.mem_sdiff.mpr ⟨hxD, hxM⟩
      have hxList : x ∈ R.toList := Finset.mem_toList.mpr hxR
      rw [← hfillersFlat] at hxList
      obtain ⟨filler, hfillerMem, hxFiller⟩ := List.mem_flatten.mp hxList
      obtain ⟨i, hi, hfillerEq⟩ := List.mem_iff_getElem.mp hfillerMem
      have hih : i < h := by simpa [hfillersLength] using hi
      let j : Fin h := ⟨i, hih⟩
      refine ⟨pathAt j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
      by_cases hip : i < p
      · simp only [pathAt, j, dif_pos hip]
        apply mem_exceptionalBlockPath_of_mem_filler
          (hseedLen i (by simpa [hseedsLength] using hip))
        simpa [hfillerEq] using hxFiller
      · simp only [pathAt, j, dif_neg hip]
        exact mem_alternate_left (by simpa [smallBlockPath, hfillerEq] using hxFiller)

/-! ## Red-neighbour cardinal estimates -/

noncomputable def redNeighboursIn (G : SimpleGraph V) (D : Finset V) (y : V) : Finset V := by
  classical
  exact D.filter fun x ↦ G.Adj y x

noncomputable def nonRedNeighboursIn (G : SimpleGraph V) (D : Finset V) (y : V) : Finset V := by
  classical
  exact D.filter fun x ↦ ¬G.Adj y x

lemma card_redNeighboursIn_add_nonRedNeighboursIn (G : SimpleGraph V)
    (D : Finset V) (y : V) :
    (redNeighboursIn G D y).card + (nonRedNeighboursIn G D y).card = D.card := by
  classical
  simpa [redNeighboursIn, nonRedNeighboursIn] using
    (D.card_filter_add_card_filter_not fun x ↦ G.Adj y x)

lemma card_nonRedNeighboursIn_le {G : SimpleGraph V} {X D : Finset V} {y : V} {μ : ℕ}
    (hDX : D ⊆ X) (hsparse : (nonRedNeighboursIn G X y).card ≤ μ) :
    (nonRedNeighboursIn G D y).card ≤ μ := by
  classical
  apply (Finset.card_le_card ?_).trans hsparse
  exact Finset.filter_subset_filter _ hDX

lemma card_le_redNeighboursIn_add {G : SimpleGraph V} {X D : Finset V} {y : V} {μ : ℕ}
    (hDX : D ⊆ X) (hsparse : (nonRedNeighboursIn G X y).card ≤ μ) :
    D.card ≤ (redNeighboursIn G D y).card + μ := by
  have hpartition := card_redNeighboursIn_add_nonRedNeighboursIn G D y
  have hnonred := card_nonRedNeighboursIn_le hDX hsparse
  omega

/-- Case (ii) of Chen--Chen Lemma 3.5. -/
theorem coverDevice_case_two {G : SimpleGraph V} {X Y₀ Y₁ D : Finset V} {h μ : ℕ}
    (hDX : D ⊆ X) (hY₁ : Y₁.Nonempty)
    (hXY₀ : Disjoint X Y₀) (hXY₁ : Disjoint X Y₁) (hY₀Y₁ : Disjoint Y₀ Y₁)
    (hcomplete₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj y x)
    (hsparse₁ : ∀ y ∈ Y₁, (nonRedNeighboursIn G X y).card ≤ μ)
    (hp0 : 0 < coverDeviceP D Y₀ h)
    (hpBound : coverDeviceP D Y₀ h ≤ (min h ((D.card - μ) / 2) : ℕ)) :
    HasPathCoverOnAtMost G (D : Set V) h := by
  classical
  let p := (coverDeviceP D Y₀ h).toNat
  have hpEq : p = D.card - h * (Y₀.card + 1) := coverDeviceP_pos_toNat hp0
  have hcard : D.card = h * (Y₀.card + 1) + p := by
    simp only [coverDeviceP] at hp0
    omega
  have hpNatBound : p ≤ min h ((D.card - μ) / 2) := by
    have hpCast : (p : ℤ) = coverDeviceP D Y₀ h := by
      dsimp only [p]
      exact Int.toNat_of_nonneg hp0.le
    omega
  have hph : p ≤ h := hpNatBound.trans (Nat.min_le_left _ _)
  have hpHalf : p ≤ (D.card - μ) / 2 := hpNatBound.trans (Nat.min_le_right _ _)
  have hmuD : μ ≤ D.card := by
    have hpPos : 0 < p := by
      have hpCast : (p : ℤ) = coverDeviceP D Y₀ h :=
        Int.toNat_of_nonneg hp0.le
      omega
    omega
  have htwo : 2 * p ≤ D.card - μ := by omega
  obtain ⟨z, hz⟩ := hY₁
  have hred : 2 * p ≤ (redNeighboursIn G D z).card := by
    have hdegree := card_le_redNeighboursIn_add hDX (hsparse₁ z hz)
    omega
  obtain ⟨M, hMsub, hMcard⟩ := Finset.exists_subset_card_eq hred
  apply coverDevice_exceptional_blocks hDX hz hph hcard
  · exact hMsub.trans (by simpa [redNeighboursIn] using
      (Finset.filter_subset (G.Adj z) D))
  · exact hMcard
  · intro x hxM
    exact (Finset.mem_filter.mp (by simpa [redNeighboursIn] using hMsub hxM)).2
  · exact hXY₀
  · exact hXY₁
  · exact hY₀Y₁
  · exact hcomplete₀

/-! ## Several exceptional rows -/

/-- Exact-edge version of the alternating-path constructor when the first side has one
extra vertex. -/
lemma coverDevice_isPath_alternate_of_aligned_edges_add_one
    {G : SimpleGraph V} {xs ys : List V}
    (hlen : xs.length = ys.length + 1)
    (hxy : List.Forall₂ G.Adj xs.dropLast ys)
    (hyx : List.Forall₂ G.Adj ys xs.tail)
    (hxs : xs.Nodup) (hys : ys.Nodup) (hdisj : List.Disjoint xs ys) :
    IsPath G (alternate xs ys) := by
  have hnonempty : xs ≠ [] := by
    intro h
    subst xs
    simp at hlen
  refine ⟨alternate_ne_nil_of_left_ne_nil hnonempty,
    nodup_alternate hxs hys hdisj, ?_⟩
  induction xs generalizing ys with
  | nil => contradiction
  | cons x xs ih =>
      cases ys with
      | nil =>
          have hxsLen : xs.length = 0 := by simpa using hlen
          have hxsNil : xs = [] := List.eq_nil_of_length_eq_zero hxsLen
          subst xs
          simp [alternate]
      | cons y ys =>
          have hxs0 : xs ≠ [] := by
            apply List.ne_nil_of_length_pos
            simp only [List.length_cons] at hlen
            omega
          cases xs with
          | nil => contradiction
          | cons x' xs =>
              have hlen' : (x' :: xs).length = ys.length + 1 := by
                simp only [List.length_cons] at hlen ⊢
                omega
              have hdrop : (x :: x' :: xs).dropLast = x :: (x' :: xs).dropLast := by
                simp
              rw [hdrop] at hxy
              simp only [List.tail_cons] at hyx
              cases hxy with
              | cons hfirst hxyTail =>
                  cases hyx with
                  | cons hsecond hyxTail =>
                      have htail : (alternate (x' :: xs) ys).IsChain G.Adj := by
                        apply ih hlen'
                        · exact hxyTail
                        · exact hyxTail
                        · exact hxs.tail
                        · exact hys.tail
                        · intro a ha hb
                          exact hdisj (List.mem_cons_of_mem x ha) (List.mem_cons_of_mem y hb)
                        · simp
                      have hconnect :
                          ∀ z ∈ (alternate (x' :: xs) ys).head?, G.Adj y z := by
                        intro z hz
                        rw [head?_alternate_of_left_ne_nil (by simp : x' :: xs ≠ [])] at hz
                        simp only [List.head?_cons, Option.mem_some_iff] at hz
                        subst z
                        exact hsecond
                      rw [alternate_cons_cons, List.isChain_cons_cons]
                      exact ⟨hfirst, htail.cons hconnect⟩

/-- Representatives of the sequential common-neighbour sets are adjacent to both
corresponding entries of the ordered `Y₁` row. -/
lemma coverDevice_representative_sequential_edges [DecidableEq V]
    {G : SimpleGraph V} {D : Finset V}
    {ys xs : List V}
    (hrep : IsRepresentativeList
      (sequentialCommonCandidates (redNeighboursIn G D) ys) xs) :
    List.Forall₂ (fun y x ↦ G.Adj y x) ys.dropLast xs ∧
      List.Forall₂ (fun x y ↦ G.Adj y x) xs ys.tail := by
  classical
  induction ys generalizing xs with
  | nil =>
      have hxs : xs = [] := by simpa using hrep.length_eq.symm
      subst xs
      simp
  | cons y ys ih =>
      cases ys with
      | nil =>
          have hxs : xs = [] := by simpa using hrep.length_eq.symm
          subst xs
          simp
      | cons y' ys =>
          cases xs with
          | nil => cases hrep
          | cons x xs =>
              cases hrep with
              | cons hx htail =>
                  obtain ⟨hleft, hright⟩ := ih htail
                  have hx' := Finset.mem_inter.mp hx
                  constructor
                  · simpa using List.Forall₂.cons (R := fun y x ↦ G.Adj y x)
                      (Finset.mem_filter.mp hx'.1).2 hleft
                  · simpa using List.Forall₂.cons (R := fun x y ↦ G.Adj y x)
                      (Finset.mem_filter.mp hx'.2).2 hright

lemma IsRepresentativeList.exists_candidate_of_mem
    {Cs : List (Finset V)} {xs : List V}
    (hrep : IsRepresentativeList Cs xs) {x : V} (hx : x ∈ xs) :
    ∃ C ∈ Cs, x ∈ C := by
  induction hrep with
  | nil => simp at hx
  | cons hC htail ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨_, by simp, hC⟩
      · obtain ⟨C, hCs, hxC⟩ := ih hx
        exact ⟨C, by simp [hCs], hxC⟩

lemma exists_pair_of_mem_coverDevice_sequentialCandidates [DecidableEq V]
    {N : V → Finset V} {ys : List V} {C : Finset V}
    (hC : C ∈ sequentialCommonCandidates N ys) :
    ∃ y ∈ ys, ∃ y' ∈ ys, C = N y ∩ N y' := by
  induction ys with
  | nil => simp at hC
  | cons y ys ih =>
      cases ys with
      | nil => simp at hC
      | cons y' ys =>
          simp only [sequentialCommonCandidates_cons_cons, List.mem_cons] at hC
          rcases hC with rfl | hC
          · exact ⟨y, by simp, y', by simp, rfl⟩
          · obtain ⟨u, hu, v, hv, rfl⟩ := ih hC
            exact ⟨u, by simp [hu], v, by simp [hv], rfl⟩

/-- A nonempty `Y₁` row together with distinct representatives for its two endpoints and
its sequential common-neighbour sets gives the alternating exceptional core. -/
lemma isPath_exceptionalRowCore [DecidableEq V] {G : SimpleGraph V} {X Y₁ D : Finset V}
    {ys common : List V} {left right : V}
    (hys0 : ys ≠ []) (hysNodup : ys.Nodup) (hysY₁ : ∀ y ∈ ys, y ∈ Y₁)
    (hcommon : IsRepresentativeList
      (sequentialCommonCandidates (redNeighboursIn G D) ys) common)
    (hleft : left ∈ redNeighboursIn G D (ys.head hys0))
    (hright : right ∈ redNeighboursIn G D (ys.getLast hys0))
    (hxsNodup : (left :: common ++ [right]).Nodup)
    (hDX : D ⊆ X) (hXY₁ : Disjoint X Y₁) :
    IsPath G (alternate (left :: common ++ [right]) ys) := by
  classical
  let xs := left :: common ++ [right]
  have hcommonLen : common.length = ys.length - 1 := by
    rw [← hcommon.length_eq, length_sequentialCommonCandidates]
  have hlen : xs.length = ys.length + 1 := by
    simp [xs]
    have hypos : 0 < ys.length := List.length_pos_iff.mpr hys0
    omega
  obtain ⟨hlefts, hrights⟩ := coverDevice_representative_sequential_edges hcommon
  have hleftAdj : G.Adj left (ys.head hys0) :=
    (Finset.mem_filter.mp hleft).2.symm
  have hrightAdj : G.Adj (ys.getLast hys0) right :=
    (Finset.mem_filter.mp hright).2
  have hxy : List.Forall₂ G.Adj xs.dropLast ys := by
    have hheadMem : ys.head hys0 ∈ ys.head? := by
      rw [List.head?_eq_some_head hys0]
      simp
    have hysEq : ys = ys.head hys0 :: ys.tail := (List.cons_head?_tail hheadMem).symm
    have hrightImp := hrights.imp fun x y h ↦ h.symm
    have hxsDrop : xs.dropLast = left :: common := by
      change ((left :: common) ++ [right]).dropLast = left :: common
      exact List.dropLast_concat
    rw [hysEq, hxsDrop]
    exact List.Forall₂.cons hleftAdj hrightImp
  have hyx : List.Forall₂ G.Adj ys xs.tail := by
    have hysEq : ys = ys.dropLast ++ [ys.getLast hys0] :=
      (List.dropLast_append_getLast hys0).symm
    rw [hysEq]
    simpa [xs] using List.rel_append hlefts
      (List.Forall₂.cons hrightAdj List.Forall₂.nil)
  apply coverDevice_isPath_alternate_of_aligned_edges_add_one
    hlen hxy hyx hxsNodup hysNodup
  intro x hx hy
  have hxD : x ∈ D := by
    rcases (by simpa [xs] using hx : x = left ∨ x ∈ common ∨ x = right) with rfl | hx | rfl
    · exact (Finset.mem_filter.mp hleft).1
    · obtain ⟨C, hC, hxC⟩ := hcommon.exists_candidate_of_mem hx
      obtain ⟨y, hy, y', hy', rfl⟩ :=
        exists_pair_of_mem_coverDevice_sequentialCandidates hC
      exact (Finset.mem_filter.mp (Finset.mem_inter.mp hxC).1).1
    · exact (Finset.mem_filter.mp hright).1
  have hxX := hDX hxD
  have hxY₁ := hysY₁ x hy
  exact Finset.disjoint_left.mp hXY₁ hxX hxY₁

/-- Extend an exceptional core through an ordinary `Y₀` tail. -/
noncomputable def exceptionalRowPath (Y₀ : Finset V) (xs ys filler : List V) : List V :=
  alternate xs ys ++ alternate Y₀.toList filler

lemma mem_exceptionalRowPath_of_mem_xs {Y₀ : Finset V} {xs ys filler : List V}
    {x : V} (hx : x ∈ xs) : x ∈ exceptionalRowPath Y₀ xs ys filler := by
  exact List.mem_append_left _ (mem_alternate_left hx)

lemma mem_exceptionalRowPath_of_mem_filler {Y₀ : Finset V} {xs ys filler : List V}
    {x : V} (hx : x ∈ filler) : x ∈ exceptionalRowPath Y₀ xs ys filler := by
  exact List.mem_append_right _ (mem_alternate_right hx)

lemma isPath_exceptionalRowPath {G : SimpleGraph V} {X Y₀ Y₁ D : Finset V}
    {xs ys filler : List V}
    (hcore : IsPath G (alternate xs ys))
    (hlen : xs.length = ys.length + 1)
    (hxsD : ∀ x ∈ xs, x ∈ D) (hysY₁ : ∀ y ∈ ys, y ∈ Y₁)
    (hfillerNodup : filler.Nodup) (hfillerD : ∀ x ∈ filler, x ∈ D)
    (hxsFiller : List.Disjoint xs filler) (hfillerLen : filler.length = Y₀.card)
    (hDX : D ⊆ X) (hXY₀ : Disjoint X Y₀) (hXY₁ : Disjoint X Y₁)
    (hY₀Y₁ : Disjoint Y₀ Y₁)
    (hcomplete₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj y x) :
    IsPath G (exceptionalRowPath Y₀ xs ys filler) := by
  classical
  let core := alternate xs ys
  let tail := alternate Y₀.toList filler
  have htailNodup : tail.Nodup := by
    apply nodup_alternate (Finset.nodup_toList Y₀) hfillerNodup
    intro z hzY₀ hzF
    exact Finset.disjoint_left.mp hXY₀ (hDX (hfillerD z hzF))
      (Finset.mem_toList.mp hzY₀)
  have htailChain : tail.IsChain G.Adj := by
    apply isChain_alternate_of_length_eq
    · simpa using hfillerLen.symm
    · intro y hy x hx
      exact hcomplete₀ y (Finset.mem_toList.mp hy) x (hDX (hfillerD x hx))
  have hcoreTail : List.Disjoint core tail := by
    intro z hzCore hzTail
    rcases mem_alternate.mp hzCore with hzXs | hzYs
    · rcases mem_alternate.mp hzTail with hzY₀ | hzF
      · exact Finset.disjoint_left.mp hXY₀ (hDX (hxsD z hzXs))
          (Finset.mem_toList.mp hzY₀)
      · exact hxsFiller hzXs hzF
    · rcases mem_alternate.mp hzTail with hzY₀ | hzF
      · exact Finset.disjoint_left.mp hY₀Y₁ (Finset.mem_toList.mp hzY₀)
          (hysY₁ z hzYs)
      · exact Finset.disjoint_left.mp hXY₁ (hDX (hfillerD z hzF))
          (hysY₁ z hzYs)
  refine ⟨?_, hcore.2.1.append htailNodup hcoreTail, ?_⟩
  · simpa [exceptionalRowPath, core, tail] using
      (List.append_ne_nil_of_left_ne_nil hcore.1 tail)
  · apply hcore.2.2.append htailChain
    intro x hxLast y hyHead
    have hxXs : x ∈ xs := by
      have hxCore : x ∈ core := List.mem_of_mem_getLast? hxLast
      rcases mem_alternate.mp hxCore with hxXs | hxYs
      · exact hxXs
      · have hlast := getLast?_alternate_of_length_eq_add_one hlen
        rw [hlast] at hxLast
        exact List.mem_of_mem_getLast? hxLast
    have hyY₀ : y ∈ Y₀ := by
      have hyTail : y ∈ tail := List.mem_of_mem_head? hyHead
      rcases mem_alternate.mp hyTail with hyY₀ | hyF
      · exact Finset.mem_toList.mp hyY₀
      · by_cases hY₀empty : Y₀.toList = []
        · have hcard0 : Y₀.card = 0 := by simpa using congrArg List.length hY₀empty
          have hfempty : filler = [] := List.eq_nil_of_length_eq_zero (by omega)
          simp [tail, hY₀empty, hfempty] at hyHead
        · rw [head?_alternate_of_left_ne_nil hY₀empty] at hyHead
          exact Finset.mem_toList.mp (List.mem_of_mem_head? hyHead)
    exact (hcomplete₀ y hyY₀ x (hDX (hxsD x hxXs))).symm

/-! ### Arithmetic and list infrastructure for the rows -/

/-- Split a positive demand `p` among `q` nonempty rows of capacity `a`. -/
lemma exists_coverDevice_rowSizes : ∀ (q p a : ℕ),
    q ≤ p → p ≤ q * a →
      ∃ bs : List ℕ, bs.length = q ∧ bs.sum = p ∧
        ∀ b ∈ bs, 1 ≤ b ∧ b ≤ a
  | 0, p, _a, _hqp, hcap => by
      have hp : p = 0 := by simpa using hcap
      subst p
      exact ⟨[], by simp⟩
  | q + 1, p, a, hqp, hcap => by
      have hpq : q + 1 ≤ p := hqp
      have ha : 1 ≤ a := by
        by_contra h
        have ha0 : a = 0 := by omega
        subst a
        simp at hcap
        omega
      let b := min a (p - q)
      let p' := p - b
      have hpqpos : 1 ≤ p - q := by omega
      have hbpos : 1 ≤ b := by
        dsimp only [b]
        exact le_min ha hpqpos
      have hba : b ≤ a := min_le_left _ _
      have hbrem : b ≤ p - q := min_le_right _ _
      have hqp' : q ≤ p' := by
        dsimp only [p']
        omega
      have hp'cap : p' ≤ q * a := by
        dsimp only [p', b]
        by_cases hab : a ≤ p - q
        · rw [min_eq_left hab]
          rw [Nat.succ_mul] at hcap
          omega
        · have hpa : p - q ≤ a := Nat.le_of_not_ge hab
          rw [min_eq_right hpa]
          have hpSub : p - (p - q) = q := by omega
          rw [hpSub]
          simpa using Nat.mul_le_mul_left q ha
      obtain ⟨bs, hlen, hsum, hbounds⟩ :=
        exists_coverDevice_rowSizes q p' a hqp' hp'cap
      refine ⟨b :: bs, by simp [hlen], ?_, ?_⟩
      · simp only [List.sum_cons, hsum]
        dsimp only [p']
        omega
      · intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact ⟨hbpos, hba⟩
        · exact hbounds c hc

lemma sum_pred_eq_sum_sub_length {bs : List ℕ}
    (hpos : ∀ b ∈ bs, 1 ≤ b) :
    (bs.map fun b ↦ b - 1).sum = bs.sum - bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      have hb := hpos b (by simp)
      have htail : ∀ c ∈ bs, 1 ≤ c := by
        intro c hc
        exact hpos c (by simp [hc])
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih htail]
      have hlenSum : bs.length ≤ bs.sum :=
        List.length_le_sum_of_one_le bs htail
      omega

/-- Simultaneous representatives for two tiers of candidate sets.  The common tier is
selected first; the endpoint tier is then selected after deleting the common representatives. -/
theorem exists_coverDevice_twoTierRepresentatives {A : Type*}
    (common endpoint : List (Finset A))
    (hcommon : ∀ C ∈ common, common.length ≤ C.card)
    (hendpoint : ∀ E ∈ endpoint,
      common.length + endpoint.length ≤ E.card) :
    ∃ commonReps endpointReps : List A,
      commonReps.Nodup ∧ endpointReps.Nodup ∧
        List.Disjoint commonReps endpointReps ∧
        IsRepresentativeList common commonReps ∧
        IsRepresentativeList endpoint endpointReps := by
  classical
  obtain ⟨commonReps, hcommonNodup, hcommonRep⟩ :=
    exists_nodup_representativeList common hcommon
  let used : Finset A := commonReps.toFinset
  let residualEndpoint : List (Finset A) := endpoint.map fun E ↦ E \ used
  have husedCard : used.card = common.length := by
    rw [List.toFinset_card_of_nodup hcommonNodup]
    exact hcommonRep.length_eq.symm
  have hresidualLength : residualEndpoint.length = endpoint.length := by
    simp [residualEndpoint]
  have hresidualCard : ∀ E ∈ residualEndpoint,
      residualEndpoint.length ≤ E.card := by
    intro E hE
    obtain ⟨E₀, hE₀, rfl⟩ := List.mem_map.mp hE
    have hlarge := hendpoint E₀ hE₀
    have hlower := Finset.le_card_sdiff used E₀
    rw [husedCard] at hlower
    rw [hresidualLength]
    omega
  obtain ⟨endpointReps, hendpointNodup, hresidualRep⟩ :=
    exists_nodup_representativeList residualEndpoint hresidualCard
  have hendpointRep : IsRepresentativeList endpoint endpointReps := by
    have hmap : IsRepresentativeList
        (endpoint.map fun E ↦ E \ used) endpointReps := by
      simpa [residualEndpoint] using hresidualRep
    rw [IsRepresentativeList, List.forall₂_map_left_iff] at hmap
    exact hmap.imp (fun E x hx ↦ (Finset.mem_sdiff.mp hx).1)
  have havoids : ∀ x ∈ endpointReps, x ∉ used := by
    have hmap : IsRepresentativeList
        (endpoint.map fun E ↦ E \ used) endpointReps := by
      simpa [residualEndpoint] using hresidualRep
    rw [IsRepresentativeList, List.forall₂_map_left_iff] at hmap
    have haux : ∀ {Cs : List (Finset A)} {xs : List A},
        List.Forall₂ (fun E x => x ∈ E \ used) Cs xs →
          ∀ x ∈ xs, x ∉ used := by
      intro Cs xs h
      induction h with
      | nil => simp
      | cons hx _ ih =>
          intro x hxmem
          rcases List.mem_cons.mp hxmem with rfl | hxmem
          · exact (Finset.mem_sdiff.mp hx).2
          · exact ih x hxmem
    exact haux hmap
  have hdisjoint : List.Disjoint commonReps endpointReps := by
    intro x hxCommon hxEndpoint
    exact havoids x hxEndpoint (by simpa [used] using hxCommon)
  exact ⟨commonReps, endpointReps, hcommonNodup, hendpointNodup,
    hdisjoint, hcommonRep, hendpointRep⟩

/-- Regroup a flat representative list according to the list-of-lists whose flattening
supplied its candidates. -/
lemma coverDevice_forall₂_splitLengths_flatten {A B : Type*} {R : A → B → Prop}
    {groups : List (List A)} {xs : List B}
    (h : List.Forall₂ R groups.flatten xs) :
    List.Forall₂ (List.Forall₂ R) groups
      ((groups.map List.length).splitLengths xs) := by
  induction groups generalizing xs with
  | nil =>
      have hxs : xs = [] := by simpa using h.length_eq.symm
      subst xs
      simp
  | cons group groups ih =>
      have hhead : List.Forall₂ R group (xs.take group.length) := by
        have ht := List.forall₂_take group.length h
        simpa using ht
      have htail : List.Forall₂ R groups.flatten (xs.drop group.length) := by
        have hd := List.forall₂_drop group.length h
        simpa using hd
      simpa only [List.map_cons, List.splitLengths_cons] using
        (List.Forall₂.cons hhead (ih htail))

/-- The two endpoint candidate sets for a nonempty row. -/
noncomputable def coverDeviceEndpointCandidates {A : Type*}
    (N : V → Finset A) (ys : List V) : List (Finset A) :=
  if hys : ys = [] then [] else [N (ys.head hys), N (ys.getLast hys)]

lemma coverDeviceEndpointCandidates_eq {A : Type*} {N : V → Finset A}
    {ys : List V} (hys : ys ≠ []) :
    coverDeviceEndpointCandidates N ys =
      [N (ys.head hys), N (ys.getLast hys)] := by
  simp only [coverDeviceEndpointCandidates, dif_neg hys]

lemma length_coverDeviceEndpointCandidates {A : Type*} {N : V → Finset A}
    {ys : List V} (hys : ys ≠ []) :
    (coverDeviceEndpointCandidates N ys).length = 2 := by
  rw [coverDeviceEndpointCandidates_eq hys]
  simp

lemma exists_of_mem_coverDeviceEndpointCandidates {A : Type*} {N : V → Finset A}
    {ys : List V} {C : Finset A} (hys : ys ≠ [])
    (hC : C ∈ coverDeviceEndpointCandidates N ys) :
    ∃ y ∈ ys, C = N y := by
  rw [coverDeviceEndpointCandidates_eq hys] at hC
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with hC | hC
  · exact ⟨ys.head hys, List.head_mem hys, hC⟩
  · exact ⟨ys.getLast hys, List.getLast_mem hys, hC⟩

lemma card_inter_redNeighboursIn_add_two_mul [DecidableEq V] {G : SimpleGraph V}
    {X D : Finset V} {y z : V} {μ : ℕ}
    (hDX : D ⊆ X)
    (hy : (nonRedNeighboursIn G X y).card ≤ μ)
    (hz : (nonRedNeighboursIn G X z).card ≤ μ) :
    D.card ≤ (redNeighboursIn G D y ∩ redNeighboursIn G D z).card + 2 * μ := by
  classical
  let A := redNeighboursIn G D y
  let B := redNeighboursIn G D z
  have hA := card_le_redNeighboursIn_add hDX hy
  have hB := card_le_redNeighboursIn_add hDX hz
  have hunionSub : A ∪ B ⊆ D := by
    apply Finset.union_subset
    · simpa [A, redNeighboursIn] using (Finset.filter_subset (G.Adj y) D)
    · simpa [B, redNeighboursIn] using (Finset.filter_subset (G.Adj z) D)
  have hunion := Finset.card_le_card hunionSub
  have hident := Finset.card_inter_add_card_union A B
  dsimp only [A, B] at hA hB hunion hident ⊢
  omega

/-- Case (iii) of Chen--Chen Lemma 3.5.  The positive excess is distributed among
`q = min p h` nonempty rows of `Y₁`; global distinct representatives for all consecutive
common-neighbour and endpoint requirements supply the red exceptional cores. -/
theorem coverDevice_case_three {G : SimpleGraph V} {X Y₀ Y₁ D : Finset V} {h μ : ℕ}
    (hDX : D ⊆ X) (hY₁ : Y₁.Nonempty)
    (hXY₀ : Disjoint X Y₀) (hXY₁ : Disjoint X Y₁) (hY₀Y₁ : Disjoint Y₀ Y₁)
    (hcomplete₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj y x)
    (hsparse₁ : ∀ y ∈ Y₁, (nonRedNeighboursIn G X y).card ≤ μ)
    (hp₀ : 0 < coverDeviceP D Y₀ h)
    (hpCapacity : coverDeviceP D Y₀ h ≤
      (coverDeviceQ D Y₀ h * Y₁.card : ℕ))
    (hcommonCapacity : coverDeviceP D Y₀ h - (coverDeviceQ D Y₀ h : ℕ) ≤
      (D.card : ℤ) - 2 * (μ : ℤ))
    (hendpointCapacity : coverDeviceP D Y₀ h + (coverDeviceQ D Y₀ h : ℕ) ≤
      (D.card : ℤ) - (μ : ℤ)) :
    HasPathCoverOnAtMost G (D : Set V) h := by
  classical
  let p := (coverDeviceP D Y₀ h).toNat
  let q := coverDeviceQ D Y₀ h
  have hpCast : (p : ℤ) = coverDeviceP D Y₀ h := by
    dsimp only [p]
    exact Int.toNat_of_nonneg hp₀.le
  have hpPos : 0 < p := by omega
  have hqDef : q = min p h := by rfl
  by_cases hph : p ≤ h
  · have hqEq : q = p := by simp [hqDef, hph]
    apply coverDevice_case_two hDX hY₁ hXY₀ hXY₁ hY₀Y₁ hcomplete₀ hsparse₁ hp₀
    have htwo : (2 * p : ℤ) ≤ (D.card : ℤ) - (μ : ℤ) := by
      have hend := hendpointCapacity
      rw [← hpCast] at hend
      change (p : ℤ) + (q : ℤ) ≤ (D.card : ℤ) - (μ : ℤ) at hend
      rw [hqEq] at hend
      omega
    have hmuD : μ ≤ D.card := by omega
    have htwoNat : 2 * p ≤ D.card - μ := by omega
    have hpHalf : p ≤ (D.card - μ) / 2 := by omega
    have hpMin : p ≤ min h ((D.card - μ) / 2) := (Nat.le_min).2 ⟨hph, hpHalf⟩
    omega
  · have hhp : h < p := Nat.lt_of_not_ge hph
    have hqEq : q = h := by simp [hqDef, Nat.min_eq_right hhp.le]
    have hhPos : 0 < h := by
      by_contra hh
      have hh₀ : h = 0 := by omega
      have hq₀ : q = 0 := by omega
      have hcap := hpCapacity
      rw [← hpCast] at hcap
      change (p : ℤ) ≤ (q * Y₁.card : ℕ) at hcap
      rw [hq₀] at hcap
      simp at hcap
      omega
    have hpEq : p = D.card - h * (Y₀.card + 1) := coverDeviceP_pos_toNat hp₀
    have hDcard : D.card = h * (Y₀.card + 1) + p := by
      simp only [coverDeviceP] at hp₀
      omega
    have hpCapNat : p ≤ h * Y₁.card := by
      have hcap := hpCapacity
      rw [← hpCast] at hcap
      change (p : ℤ) ≤ (q * Y₁.card : ℕ) at hcap
      rw [hqEq] at hcap
      exact_mod_cast hcap
    obtain ⟨bs, hbsLen, hbsSum, hbsBounds⟩ :=
      exists_coverDevice_rowSizes h p Y₁.card hhp.le hpCapNat
    let rows : List (List V) := bs.map fun b ↦ Y₁.toList.take b
    have hrowsLen : rows.length = h := by simp [rows, hbsLen]
    have hrowLen : ∀ i (hi : i < rows.length), rows[i].length =
        bs[i]'(by simpa [rows] using hi) := by
      intro i hi
      simp [rows, List.length_take, (hbsBounds bs[i] (List.getElem_mem (by
        simpa [rows] using hi))).2]
    have hrowNonempty : ∀ i (hi : i < rows.length), rows[i] ≠ [] := by
      intro i hi hempty
      have hb := (hbsBounds bs[i] (List.getElem_mem (by simpa [rows] using hi))).1
      have hl := hrowLen i hi
      rw [hempty] at hl
      simp at hl
      omega
    have hrowNodup : ∀ i (hi : i < rows.length), rows[i].Nodup := by
      intro i hi
      rw [List.nodup_iff_pairwise_ne]
      simpa only [rows, List.getElem_map] using
        (Finset.nodup_toList Y₁).take
    have hrowY₁ : ∀ i (hi : i < rows.length), ∀ y ∈ rows[i], y ∈ Y₁ := by
      intro i hi y hy
      apply Finset.mem_toList.mp
      exact List.mem_of_mem_take (by simpa [rows] using hy)
    let commonGroups : List (List (Finset V)) :=
      rows.map (sequentialCommonCandidates (redNeighboursIn G D))
    let endpointGroups : List (List (Finset V)) :=
      rows.map (coverDeviceEndpointCandidates (redNeighboursIn G D))
    let commonCandidates := commonGroups.flatten
    let endpointCandidates := endpointGroups.flatten
    have hcommonLen : commonCandidates.length = p - h := by
      calc
        commonCandidates.length = (rows.map fun ys ↦ ys.length - 1).sum := by
          simp only [commonCandidates, commonGroups, List.length_flatten, List.map_map]
          apply congrArg List.sum
          apply List.map_congr_left
          intro ys hys
          simpa only [Function.comp_apply] using
            (length_sequentialCommonCandidates (redNeighboursIn G D) ys)
        _ = (bs.map fun b ↦ b - 1).sum := by
          apply congrArg List.sum
          rw [List.map_map]
          apply List.map_congr_left
          intro b hb
          simp only [Function.comp_apply]
          rw [List.length_take]
          exact congrArg (· - 1) (min_eq_left (by simpa using (hbsBounds b hb).2))
        _ = p - h := by
          rw [sum_pred_eq_sum_sub_length (fun b hb ↦ (hbsBounds b hb).1), hbsSum, hbsLen]
    have hendpointLen : endpointCandidates.length = 2 * h := by
      calc
        endpointCandidates.length = (rows.map fun ys ↦
            (coverDeviceEndpointCandidates (redNeighboursIn G D) ys).length).sum := by
          simp only [endpointCandidates, endpointGroups, List.length_flatten, List.map_map]
          rfl
        _ = (rows.map fun _ ↦ 2).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro ys hys
          have hys₀ : ys ≠ [] := by
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hys
            exact hrowNonempty i hi
          rw [length_coverDeviceEndpointCandidates hys₀]
        _ = 2 * h := by simp [hrowsLen, Nat.mul_comm]
    have hcommonCard : ∀ C ∈ commonCandidates, commonCandidates.length ≤ C.card := by
      intro C hC
      obtain ⟨group, hgroup, hCgroup⟩ := List.mem_flatten.mp hC
      obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp (by simpa [commonGroups] using hgroup)
      obtain ⟨y, hy, z, hz, rfl⟩ :=
        exists_pair_of_mem_coverDevice_sequentialCandidates hCgroup
      have hyY₁ : y ∈ Y₁ := by
        obtain ⟨i, hi, hrow⟩ := List.mem_iff_getElem.mp hys
        exact hrowY₁ i hi y (by simpa [hrow] using hy)
      have hzY₁ : z ∈ Y₁ := by
        obtain ⟨i, hi, hrow⟩ := List.mem_iff_getElem.mp hys
        exact hrowY₁ i hi z (by simpa [hrow] using hz)
      have hcard := card_inter_redNeighboursIn_add_two_mul hDX
        (hsparse₁ y hyY₁) (hsparse₁ z hzY₁)
      rw [hcommonLen]
      have hcap := hcommonCapacity
      rw [← hpCast] at hcap
      change (p : ℤ) - (q : ℤ) ≤ (D.card : ℤ) - 2 * (μ : ℤ) at hcap
      rw [hqEq] at hcap
      omega
    have hendpointCard : ∀ E ∈ endpointCandidates,
        commonCandidates.length + endpointCandidates.length ≤ E.card := by
      intro E hE
      obtain ⟨group, hgroup, hEgroup⟩ := List.mem_flatten.mp hE
      obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp (by simpa [endpointGroups] using hgroup)
      have hys₀ : ys ≠ [] := by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hys
        exact hrowNonempty i hi
      obtain ⟨y, hy, rfl⟩ :=
        exists_of_mem_coverDeviceEndpointCandidates hys₀ hEgroup
      have hyY₁ : y ∈ Y₁ := by
        obtain ⟨i, hi, hrow⟩ := List.mem_iff_getElem.mp hys
        exact hrowY₁ i hi y (by simpa [hrow] using hy)
      have hcard := card_le_redNeighboursIn_add hDX (hsparse₁ y hyY₁)
      rw [hcommonLen, hendpointLen]
      have hcap := hendpointCapacity
      rw [← hpCast] at hcap
      change (p : ℤ) + (q : ℤ) ≤ (D.card : ℤ) - (μ : ℤ) at hcap
      rw [hqEq] at hcap
      omega
    obtain ⟨commonReps, endpointReps, hcommonRepsNodup, hendpointRepsNodup,
      hrepsDisjoint, hcommonRep, hendpointRep⟩ :=
      exists_coverDevice_twoTierRepresentatives commonCandidates endpointCandidates
        hcommonCard hendpointCard
    let commonBlocks : List (List V) :=
      (commonGroups.map List.length).splitLengths commonReps
    let endpointBlocks : List (List V) :=
      (endpointGroups.map List.length).splitLengths endpointReps
    have hcommonBlocksLen : commonBlocks.length = h := by
      simp [commonBlocks, commonGroups, hrowsLen]
    have hendpointBlocksLen : endpointBlocks.length = h := by
      simp [endpointBlocks, endpointGroups, hrowsLen]
    have hcommonBlocksFlat : commonBlocks.flatten = commonReps := by
      apply List.flatten_splitLengths
      rw [← List.length_flatten, hcommonRep.length_eq]
    have hendpointBlocksFlat : endpointBlocks.flatten = endpointReps := by
      apply List.flatten_splitLengths
      rw [← List.length_flatten, hendpointRep.length_eq]
    have hcommonBlocksRep : List.Forall₂
        (fun Cs xs ↦ IsRepresentativeList Cs xs) commonGroups commonBlocks := by
      apply coverDevice_forall₂_splitLengths_flatten
      exact hcommonRep
    have hendpointBlocksRep : List.Forall₂
        (fun Cs xs ↦ IsRepresentativeList Cs xs) endpointGroups endpointBlocks := by
      apply coverDevice_forall₂_splitLengths_flatten
      exact hendpointRep
    have hcommonBlockNodup : ∀ block ∈ commonBlocks, block.Nodup :=
      (List.nodup_flatten.mp (hcommonBlocksFlat.symm ▸ hcommonRepsNodup)).1
    have hendpointBlockNodup : ∀ block ∈ endpointBlocks, block.Nodup :=
      (List.nodup_flatten.mp (hendpointBlocksFlat.symm ▸ hendpointRepsNodup)).1
    have hcommonAt : ∀ i (hi : i < h), IsRepresentativeList
        (sequentialCommonCandidates (redNeighboursIn G D)
          (rows[i]'(by simpa [hrowsLen])))
        (commonBlocks[i]'(by simpa [hcommonBlocksLen])) := by
      intro i hi
      have hget := List.Forall₂.get hcommonBlocksRep (i := i)
        (by simpa [commonGroups, hrowsLen]) (by simpa [hcommonBlocksLen])
      simpa [commonGroups] using hget
    have hendpointAt : ∀ i (hi : i < h), IsRepresentativeList
        (coverDeviceEndpointCandidates (redNeighboursIn G D)
          (rows[i]'(by simpa [hrowsLen])))
        (endpointBlocks[i]'(by simpa [hendpointBlocksLen])) := by
      intro i hi
      have hget := List.Forall₂.get hendpointBlocksRep (i := i)
        (by simpa [endpointGroups, hrowsLen]) (by simpa [hendpointBlocksLen])
      simpa [endpointGroups] using hget
    have hendpointBlockLen : ∀ i (hi : i < h),
        (endpointBlocks[i]'(by simpa [hendpointBlocksLen])).length = 2 := by
      intro i hi
      rw [← (hendpointAt i hi).length_eq]
      exact length_coverDeviceEndpointCandidates
        (hrowNonempty i (by simpa [hrowsLen] using hi))
    let leftAt : Fin h → V := fun i ↦
      (endpointBlocks[i.1]'(by simpa [hendpointBlocksLen] using i.2))[0]'(by
        have := hendpointBlockLen i.1 i.2
        omega)
    let rightAt : Fin h → V := fun i ↦
      (endpointBlocks[i.1]'(by simpa [hendpointBlocksLen] using i.2))[1]'(by
        have := hendpointBlockLen i.1 i.2
        omega)
    let xsAt : Fin h → List V := fun i ↦
      leftAt i :: commonBlocks[i.1]'(by simpa [hcommonBlocksLen] using i.2) ++ [rightAt i]
    have hleftAt : ∀ i : Fin h, leftAt i ∈ redNeighboursIn G D
        ((rows[i.1]'(by simpa [hrowsLen] using i.2)).head
          (hrowNonempty i.1 (by simpa [hrowsLen] using i.2))) := by
      intro i
      have hrel := hendpointAt i.1 i.2
      rw [coverDeviceEndpointCandidates_eq
        (hrowNonempty i.1 (by simpa [hrowsLen] using i.2))] at hrel
      have hget := List.Forall₂.get hrel (i := 0) (by simp) (by
        have := hendpointBlockLen i.1 i.2
        omega)
      simpa [leftAt] using hget
    have hrightAt : ∀ i : Fin h, rightAt i ∈ redNeighboursIn G D
        ((rows[i.1]'(by simpa [hrowsLen] using i.2)).getLast
          (hrowNonempty i.1 (by simpa [hrowsLen] using i.2))) := by
      intro i
      have hrel := hendpointAt i.1 i.2
      rw [coverDeviceEndpointCandidates_eq
        (hrowNonempty i.1 (by simpa [hrowsLen] using i.2))] at hrel
      have hget := List.Forall₂.get hrel (i := 1) (by simp) (by
        have := hendpointBlockLen i.1 i.2
        omega)
      simpa [rightAt] using hget
    have hcommonMemReps : ∀ i : Fin h, ∀ x ∈
        commonBlocks[i.1]'(by simpa [hcommonBlocksLen] using i.2), x ∈ commonReps := by
      intro i x hx
      rw [← hcommonBlocksFlat]
      exact List.mem_flatten.mpr ⟨_, List.getElem_mem _, hx⟩
    have hendpointMemReps : ∀ i : Fin h, ∀ x ∈
        endpointBlocks[i.1]'(by simpa [hendpointBlocksLen] using i.2), x ∈ endpointReps := by
      intro i x hx
      rw [← hendpointBlocksFlat]
      exact List.mem_flatten.mpr ⟨_, List.getElem_mem _, hx⟩
    have hleftMemEndpoint (i : Fin h) : leftAt i ∈ endpointReps := by
      apply hendpointMemReps i
      dsimp only [leftAt]
      exact List.getElem_mem _
    have hrightMemEndpoint (i : Fin h) : rightAt i ∈ endpointReps := by
      apply hendpointMemReps i
      dsimp only [rightAt]
      exact List.getElem_mem _
    have hxsNodup : ∀ i : Fin h, (xsAt i).Nodup := by
      intro i
      have hci : i.1 < commonBlocks.length := by simpa [hcommonBlocksLen] using i.2
      have hei : i.1 < endpointBlocks.length := by simpa [hendpointBlocksLen] using i.2
      have hcN := hcommonBlockNodup _ (List.getElem_mem hci)
      have heN := hendpointBlockNodup _ (List.getElem_mem hei)
      have hlr : leftAt i ≠ rightAt i := by
        intro heq
        have heq' :
            (endpointBlocks[i.1]'hei)[0]'(by
              have := hendpointBlockLen i.1 i.2
              omega) =
            (endpointBlocks[i.1]'hei)[1]'(by
              have := hendpointBlockLen i.1 i.2
              omega) := by
          simpa only [leftAt, rightAt] using heq
        have hindices : (0 : ℕ) = 1 := heN.getElem_inj_iff.mp heq'
        omega
      dsimp only [xsAt]
      apply List.nodup_cons.mpr
      constructor
      · intro hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hrepsDisjoint (hcommonMemReps i _ hx) (hleftMemEndpoint i)
        · simpa using hlr (by simpa using hx)
      · apply hcN.append (by simp)
        intro x hx hxright
        have hxEq : x = rightAt i := by simpa using hxright
        subst x
        exact hrepsDisjoint (hcommonMemReps i _ hx) (hrightMemEndpoint i)
    have hxsD : ∀ i : Fin h, ∀ x ∈ xsAt i, x ∈ D := by
      intro i x hx
      rcases (by simpa [xsAt] using hx : x = leftAt i ∨
          x ∈ commonBlocks[i.1]'(by simpa [hcommonBlocksLen] using i.2) ∨
          x = rightAt i) with rfl | hx | rfl
      · exact (Finset.mem_filter.mp (hleftAt i)).1
      · obtain ⟨C, hC, hxC⟩ := (hcommonAt i.1 i.2).exists_candidate_of_mem hx
        obtain ⟨y, hy, z, hz, rfl⟩ :=
          exists_pair_of_mem_coverDevice_sequentialCandidates hC
        exact (Finset.mem_filter.mp (Finset.mem_inter.mp hxC).1).1
      · exact (Finset.mem_filter.mp (hrightAt i)).1
    have hxsLen : ∀ i : Fin h, (xsAt i).length =
        (rows[i.1]'(by simpa [hrowsLen] using i.2)).length + 1 := by
      intro i
      have hcLen := (hcommonAt i.1 i.2).length_eq
      rw [length_sequentialCommonCandidates] at hcLen
      have hrowPos : 0 < (rows[i.1]'(by simpa [hrowsLen] using i.2)).length :=
        List.length_pos_iff.mpr (hrowNonempty i.1 (by simpa [hrowsLen] using i.2))
      dsimp only [xsAt]
      simp only [List.length_cons, List.length_append, List.length_nil]
      rw [← hcLen]
      omega
    have hcore : ∀ i : Fin h, IsPath G (alternate (xsAt i)
        (rows[i.1]'(by simpa [hrowsLen] using i.2))) := by
      intro i
      apply isPath_exceptionalRowCore
        (hrowNonempty i.1 (by simpa [hrowsLen] using i.2))
        (hrowNodup i.1 (by simpa [hrowsLen] using i.2))
        (hrowY₁ i.1 (by simpa [hrowsLen] using i.2))
        (hcommonAt i.1 i.2) (hleftAt i) (hrightAt i)
      · exact hxsNodup i
      · exact hDX
      · exact hXY₁
    let used : Finset V := (commonReps ++ endpointReps).toFinset
    let R := D \ used
    have hrepsNodup : (commonReps ++ endpointReps).Nodup :=
      hcommonRepsNodup.append hendpointRepsNodup hrepsDisjoint
    have husedCard : used.card = p + h := by
      rw [show used.card = (commonReps ++ endpointReps).length by
        exact List.toFinset_card_of_nodup hrepsNodup]
      rw [List.length_append, ← hcommonRep.length_eq, ← hendpointRep.length_eq,
        hcommonLen, hendpointLen]
      omega
    have husedSubD : used ⊆ D := by
      intro x hx
      have hx' : x ∈ commonReps ∨ x ∈ endpointReps := by
        simpa [used] using hx
      rcases hx' with hxC | hxE
      · obtain ⟨C, hC, hxC'⟩ := hcommonRep.exists_candidate_of_mem hxC
        obtain ⟨group, hgroup, hCgroup⟩ := List.mem_flatten.mp hC
        obtain ⟨ys, _hys, rfl⟩ := List.mem_map.mp (by simpa [commonGroups] using hgroup)
        obtain ⟨y, hy, z, hz, rfl⟩ :=
          exists_pair_of_mem_coverDevice_sequentialCandidates hCgroup
        exact (Finset.mem_filter.mp (Finset.mem_inter.mp hxC').1).1
      · obtain ⟨E, hE, hxE'⟩ := hendpointRep.exists_candidate_of_mem hxE
        obtain ⟨group, hgroup, hEgroup⟩ := List.mem_flatten.mp hE
        obtain ⟨ys, hys, rfl⟩ := List.mem_map.mp (by simpa [endpointGroups] using hgroup)
        have hys₀ : ys ≠ [] := by
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hys
          exact hrowNonempty i hi
        obtain ⟨y, hy, rfl⟩ :=
          exists_of_mem_coverDeviceEndpointCandidates hys₀ hEgroup
        exact (Finset.mem_filter.mp hxE').1
    have hRcard : R.card = h * Y₀.card := by
      rw [show R.card = D.card - used.card from Finset.card_sdiff_of_subset husedSubD]
      rw [hDcard, husedCard, Nat.mul_add, Nat.mul_one]
      omega
    let fillerSizes : List ℕ := List.replicate h Y₀.card
    let fillers : List (List V) := fillerSizes.splitLengths R.toList
    have hfillerSum : fillerSizes.sum = R.toList.length := by
      simp [fillerSizes, hRcard]
    have hfillersLen : fillers.length = h := by simp [fillers, fillerSizes]
    have hfillersFlat : fillers.flatten = R.toList := by
      exact List.flatten_splitLengths R.toList fillerSizes hfillerSum.ge
    have hfillersNodup : ∀ filler ∈ fillers, filler.Nodup :=
      (List.nodup_flatten.mp (hfillersFlat.symm ▸ Finset.nodup_toList R)).1
    have hfillerLen : ∀ i (hi : i < h),
        (fillers[i]'(by simpa [hfillersLen] using hi)).length = Y₀.card := by
      intro i hi
      have hget := List.splitLengths_length_getElem R.toList fillerSizes hfillerSum.le i
        (by simpa [fillers, fillerSizes] using hi)
      simpa [fillerSizes] using hget
    have hfillerR : ∀ i : Fin h, ∀ x ∈
        fillers[i.1]'(by simpa [hfillersLen] using i.2), x ∈ R := by
      intro i x hx
      apply Finset.mem_toList.mp
      rw [← hfillersFlat]
      exact List.mem_flatten.mpr ⟨_, List.getElem_mem _, hx⟩
    have hxsUsed : ∀ i : Fin h, ∀ x ∈ xsAt i, x ∈ used := by
      intro i x hx
      rcases (by simpa [xsAt] using hx : x = leftAt i ∨
          x ∈ commonBlocks[i.1]'(by simpa [hcommonBlocksLen] using i.2) ∨
          x = rightAt i) with rfl | hx | rfl
      · simpa [used] using (show leftAt i ∈ commonReps ∨ leftAt i ∈ endpointReps from
          Or.inr (hleftMemEndpoint i))
      · simpa [used] using (show x ∈ commonReps ∨ x ∈ endpointReps from
          Or.inl (hcommonMemReps i x hx))
      · simpa [used] using (show rightAt i ∈ commonReps ∨ rightAt i ∈ endpointReps from
          Or.inr (hrightMemEndpoint i))
    let pathAt : Fin h → List V := fun i ↦ exceptionalRowPath Y₀ (xsAt i)
      (rows[i.1]'(by simpa [hrowsLen] using i.2))
      (fillers[i.1]'(by simpa [hfillersLen] using i.2))
    have hpathAt : ∀ i : Fin h, IsPath G (pathAt i) := by
      intro i
      apply isPath_exceptionalRowPath (hcore i) (hxsLen i) (hxsD i)
        (hrowY₁ i.1 (by simpa [hrowsLen] using i.2))
      · exact hfillersNodup _ (List.getElem_mem _)
      · intro x hx
        exact (Finset.mem_sdiff.mp (hfillerR i x hx)).1
      · intro x hxX hxF
        exact (Finset.mem_sdiff.mp (hfillerR i x hxF)).2 (hxsUsed i x hxX)
      · exact hfillerLen i.1 i.2
      · exact hDX
      · exact hXY₀
      · exact hXY₁
      · exact hY₀Y₁
      · exact hcomplete₀
    let paths : List (List V) := List.ofFn pathAt
    refine ⟨paths, by simp [paths], ?_⟩
    constructor
    · intro path hpath
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (by simpa [paths] using hpath)
      exact hpathAt i
    · intro x hxD
      by_cases hxUsed : x ∈ used
      · have hxRep : x ∈ commonReps ∨ x ∈ endpointReps := by
          simpa [used] using hxUsed
        rcases hxRep with hxCommon | hxEndpoint
        · have hxFlat : x ∈ commonBlocks.flatten := by simpa [hcommonBlocksFlat]
          obtain ⟨block, hblock, hxBlock⟩ := List.mem_flatten.mp hxFlat
          obtain ⟨i, hi, hblockEq⟩ := List.mem_iff_getElem.mp hblock
          subst block
          have hih : i < h := by simpa [hcommonBlocksLen] using hi
          let j : Fin h := ⟨i, hih⟩
          refine ⟨pathAt j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
          apply mem_exceptionalRowPath_of_mem_xs
          apply List.mem_cons_of_mem
          apply List.mem_append_left
          exact hxBlock
        · have hxFlat : x ∈ endpointBlocks.flatten := by simpa [hendpointBlocksFlat]
          obtain ⟨block, hblock, hxBlock⟩ := List.mem_flatten.mp hxFlat
          obtain ⟨i, hi, hblockEq⟩ := List.mem_iff_getElem.mp hblock
          subst block
          have hih : i < h := by simpa [hendpointBlocksLen] using hi
          let j : Fin h := ⟨i, hih⟩
          have hlen := hendpointBlockLen i hih
          have hxEnds : x = leftAt j ∨ x = rightAt j := by
            obtain ⟨k, hk, hxEq⟩ := List.mem_iff_getElem.mp hxBlock
            have hkCases : k = 0 ∨ k = 1 := by omega
            rcases hkCases with rfl | rfl
            · left
              simpa only [leftAt] using hxEq.symm
            · right
              simpa only [rightAt] using hxEq.symm
          refine ⟨pathAt j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
          apply mem_exceptionalRowPath_of_mem_xs
          rcases hxEnds with rfl | rfl
          · simp [xsAt]
          · simp [xsAt]
      · have hxR : x ∈ R := Finset.mem_sdiff.mpr ⟨hxD, hxUsed⟩
        have hxList : x ∈ R.toList := Finset.mem_toList.mpr hxR
        rw [← hfillersFlat] at hxList
        obtain ⟨filler, hfiller, hxFiller⟩ := List.mem_flatten.mp hxList
        obtain ⟨i, hi, hfillerEq⟩ := List.mem_iff_getElem.mp hfiller
        have hih : i < h := by simpa [hfillersLen] using hi
        let j : Fin h := ⟨i, hih⟩
        refine ⟨pathAt j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
        apply mem_exceptionalRowPath_of_mem_filler
        change x ∈ fillers[i]'hi
        rw [hfillerEq]
        exact hxFiller

/-- The three alternatives of Chen--Chen's covering device, packaged in the form used by
the main proof. -/
theorem coverDevice {G : SimpleGraph V} {X Y₀ Y₁ D : Finset V} {h mu : ℕ}
    (hDX : D ⊆ X) (_hh : 1 ≤ h)
    (hXY₀ : Disjoint X Y₀) (hXY₁ : Disjoint X Y₁) (hY₀Y₁ : Disjoint Y₀ Y₁)
    (hcomplete₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj y x)
    (hsparse₁ : ∀ y ∈ Y₁, (nonRedNeighboursIn G X y).card ≤ mu)
    (hY₁ : Y₁.Nonempty)
    (hcases : coverDeviceP D Y₀ h ≤ 0 ∨
      (0 < coverDeviceP D Y₀ h ∧
        coverDeviceP D Y₀ h ≤ (min h ((D.card - mu) / 2) : ℕ)) ∨
      (0 < coverDeviceP D Y₀ h ∧
        coverDeviceP D Y₀ h ≤ (coverDeviceQ D Y₀ h * Y₁.card : ℕ) ∧
        coverDeviceP D Y₀ h - (coverDeviceQ D Y₀ h : ℕ) ≤
          (D.card : ℤ) - 2 * (mu : ℤ) ∧
        coverDeviceP D Y₀ h + (coverDeviceQ D Y₀ h : ℕ) ≤
          (D.card : ℤ) - (mu : ℤ))) :
    HasPathCoverOnAtMost G (D : Set V) h := by
  rcases hcases with hp | ⟨hp₀, hp⟩ | ⟨hp₀, hpCapacity, hcommon, hendpoint⟩
  · exact coverDevice_case_one hDX hXY₀ hcomplete₀ hp
  · exact coverDevice_case_two hDX hY₁ hXY₀ hXY₁ hY₀Y₁ hcomplete₀ hsparse₁ hp₀ hp
  · exact coverDevice_case_three hDX hY₁ hXY₀ hXY₁ hY₀Y₁ hcomplete₀ hsparse₁
      hp₀ hpCapacity hcommon hendpoint

end Erdos518
