import ErdosProblems.Erdos587.Bohr

open scoped BigOperators Pointwise

namespace Erdos587

def cyclicPhaseBucket {N : ℕ} [NeZero N] (P : ℕ)
    (x k : ZMod N) : ℕ :=
  (x * k).val / (N / P + 1)

lemma cyclicPhaseBucket_lt {N P : ℕ} [NeZero N]
    (hP : 0 < P) (x k : ZMod N) : cyclicPhaseBucket P x k < P := by
  have hden : 0 < N / P + 1 := Nat.succ_pos _
  rw [cyclicPhaseBucket, Nat.div_lt_iff_lt_mul hden]
  exact (x * k).val_lt.trans (Nat.lt_mul_div_succ N hP)

def cyclicPhaseCell {N P : ℕ} [NeZero N]
    (Gamma : Finset (ZMod N)) (hP : 0 < P) (x : ZMod N) :
    Gamma → Fin P :=
  fun k => ⟨cyclicPhaseBucket P x k, cyclicPhaseBucket_lt hP x k⟩

lemma val_sub_natAbs_lt_of_phaseBucket_eq
    {N P : ℕ} [NeZero N] {x y k : ZMod N}
    (hxy : cyclicPhaseBucket P x k = cyclicPhaseBucket P y k) :
    (((x * k).val : ℤ) - (y * k).val).natAbs < N / P + 1 := by
  let L := N / P + 1
  have hL : 0 < L := Nat.succ_pos _
  have hmodx := Nat.mod_lt (x * k).val hL
  have hmody := Nat.mod_lt (y * k).val hL
  have hx := Nat.mod_add_div (x * k).val L
  have hy := Nat.mod_add_div (y * k).val L
  have hdiv : (x * k).val / L = (y * k).val / L := by
    simpa [cyclicPhaseBucket, L] using hxy
  have hxyNat : (x * k).val < (y * k).val + L := by
    calc
      (x * k).val = (x * k).val % L + L * ((x * k).val / L) := hx.symm
      _ < L + L * ((x * k).val / L) := by omega
      _ = L + L * ((y * k).val / L) := by rw [hdiv]
      _ ≤ (y * k).val + L := by omega
  have hyxNat : (y * k).val < (x * k).val + L := by
    calc
      (y * k).val = (y * k).val % L + L * ((y * k).val / L) := hy.symm
      _ < L + L * ((y * k).val / L) := by omega
      _ = L + L * ((x * k).val / L) := by rw [hdiv]
      _ ≤ (x * k).val + L := by omega
  have hxyZ : ((x * k).val : ℤ) - (y * k).val < L := by
    have hxyNatZ : ((x * k).val : ℤ) < (y * k).val + L := by
      exact_mod_cast hxyNat
    omega
  have hyxZ : -((L : ℕ) : ℤ) < ((x * k).val : ℤ) - (y * k).val := by
    have hyxNatZ : ((y * k).val : ℤ) < (x * k).val + L := by
      exact_mod_cast hyxNat
    omega
  by_cases hsign : 0 ≤ ((x * k).val : ℤ) - (y * k).val
  · have hcast :
        ((((x * k).val : ℤ) - (y * k).val).natAbs : ℤ) < L := by
      rw [Int.natAbs_of_nonneg hsign]
      exact hxyZ
    exact_mod_cast hcast
  · have hneg : 0 ≤ -(((x * k).val : ℤ) - (y * k).val) := by omega
    have hcast :
        ((((x * k).val : ℤ) - (y * k).val).natAbs : ℤ) < L := by
      rw [← Int.natAbs_neg, Int.natAbs_of_nonneg hneg]
      omega
    exact_mod_cast hcast

lemma phaseCell_eq_imp_stdAddChar_close
    {N P : ℕ} [NeZero N] (Gamma : Finset (ZMod N))
    (hP : 0 < P) (hsize : 16 * (N / P + 1) ≤ N)
    {x y : ZMod N}
    (hcell : cyclicPhaseCell Gamma hP x = cyclicPhaseCell Gamma hP y) :
    x - y ∈ cyclicBohrSet Gamma (1 / 2) := by
  rw [mem_cyclicBohrSet]
  intro k hk
  let ks : Gamma := ⟨k, hk⟩
  have hbucket : cyclicPhaseBucket P x k = cyclicPhaseBucket P y k := by
    have h := congrFun hcell ks
    exact congrArg Fin.val h
  let t : ℤ := ((x * k).val : ℤ) - (y * k).val
  have ht : t.natAbs < N / P + 1 := by
    exact val_sub_natAbs_lt_of_phaseBucket_eq hbucket
  have htN : 16 * t.natAbs ≤ N := by
    exact (Nat.mul_le_mul_left 16 ht.le).trans hsize
  have hcast : (t : ZMod N) = (x - y) * k := by
    dsimp [t]
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
      ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    ring
  rw [← hcast]
  exact stdAddChar_intCast_close t htN

theorem exists_large_phaseCell
    {N P : ℕ} [NeZero N] (Gamma : Finset (ZMod N))
    (hP : 0 < P) :
    ∃ F : Finset (ZMod N), F.Nonempty ∧
      N / P ^ Gamma.card ≤ F.card ∧
      ∀ x ∈ F, ∀ y ∈ F,
        cyclicPhaseCell Gamma hP x = cyclicPhaseCell Gamma hP y := by
  classical
  let f : ZMod N → (Gamma → Fin P) := cyclicPhaseCell Gamma hP
  let n := N / P ^ Gamma.card
  by_cases hn : n = 0
  · let x : ZMod N := 0
    let F : Finset (ZMod N) := {x}
    refine ⟨F, Finset.singleton_nonempty x, by simp [n, hn], ?_⟩
    intro a ha b hb
    have ha' : a = x := by simpa [F] using ha
    have hb' : b = x := by simpa [F] using hb
    rw [ha', hb']
  · obtain ⟨c, _hc, hcard⟩ :=
      Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := (Finset.univ : Finset (ZMod N)))
        (t := (Finset.univ : Finset (Gamma → Fin P))) (f := f)
        (fun _ _ => Finset.mem_univ _)
        ⟨fun _ => ⟨0, hP⟩, Finset.mem_univ _⟩
        (by
          simp only [Finset.card_univ, ZMod.card,
            Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
          exact Nat.mul_div_le N (P ^ Gamma.card))
    let F := (Finset.univ : Finset (ZMod N)).filter fun x => f x = c
    refine ⟨F, Finset.card_pos.mp ((Nat.pos_of_ne_zero hn).trans_le ?_), ?_, ?_⟩
    · simpa [F] using hcard
    · simpa [F, n] using hcard
    · intro x hx y hy
      have hfx : f x = c := (Finset.mem_filter.mp hx).2
      have hfy : f y = c := (Finset.mem_filter.mp hy).2
      exact hfx.trans hfy.symm

theorem exists_large_set_with_difference_subset_cyclicBohrSet
    {N P : ℕ} [NeZero N] (Gamma : Finset (ZMod N))
    (hP : 0 < P) (hsize : 16 * (N / P + 1) ≤ N) :
    ∃ F : Finset (ZMod N), F.Nonempty ∧
      N / P ^ Gamma.card ≤ F.card ∧
      F - F ⊆ cyclicBohrSet Gamma (1 / 2) := by
  obtain ⟨F, hF, hcard, hcell⟩ := exists_large_phaseCell Gamma hP
  refine ⟨F, hF, hcard, ?_⟩
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
  exact phaseCell_eq_imp_stdAddChar_close Gamma hP hsize (hcell x hx y hy)

theorem card_cyclicBohrSet_lower_bound
    {N P : ℕ} [NeZero N] (Gamma : Finset (ZMod N))
    (hP : 0 < P) (hsize : 16 * (N / P + 1) ≤ N) :
    N / P ^ Gamma.card ≤ (cyclicBohrSet Gamma (1 / 2)).card := by
  obtain ⟨F, hF, hcard, hdiff⟩ :=
    exists_large_set_with_difference_subset_cyclicBohrSet Gamma hP hsize
  obtain ⟨y, hy⟩ := hF
  let g : ZMod N → ZMod N := fun x => x - y
  have hginj : Function.Injective g := fun x z hxz => by
    dsimp [g] at hxz
    calc
      x = (x - y) + y := by abel
      _ = (z - y) + y := by rw [hxz]
      _ = z := by abel
  have hsub : F.image g ⊆ cyclicBohrSet Gamma (1 / 2) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hdiff (Finset.mem_sub.mpr ⟨x, hx, y, hy, rfl⟩)
  calc
    N / P ^ Gamma.card ≤ F.card := hcard
    _ = (F.image g).card := (Finset.card_image_of_injective F hginj).symm
    _ ≤ (cyclicBohrSet Gamma (1 / 2)).card := Finset.card_le_card hsub

end Erdos587
