import ErdosProblems.Erdos336.RectifiedPrimitiveExpansion
import ErdosProblems.Erdos336.LiftedModerateCertificate

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

set_option maxHeartbeats 1000000

open scoped Pointwise

variable {N m : ℕ} [NeZero N] [NeZero m]

/-- A finite strict-half arc with at least two quotient values can be translated
so that its occupied integer labels have genuine endpoints `0` and `L`. -/
theorem exists_normalized_strict_half_endpoints
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (α : ZMod m)
    (houter : ∀ x ∈ A,
      ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m))
    (himage2 : 2 ≤ (A.image π).card) :
    ∃ p ∈ A, ∃ q ∈ A, ∃ L : ℕ,
      0 < L ∧ 2 * L < m ∧
      π (q - p) = (L : ZMod m) ∧
      (∀ x ∈ A, ∃ k : ℕ, k ≤ L ∧ 2 * k < m ∧
        π (x - p) = (k : ZMod m)) := by
  classical
  let label : ZMod N → ℕ := fun x => halfIntervalLabel π α x
  let I := A.image label
  have hAne : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at himage2
    simp at himage2
  have hIne : I.Nonempty := hAne.image label
  have himageOne : 1 < (A.image π).card := by omega
  obtain ⟨u, huI, v, hvI, huv⟩ := Finset.one_lt_card.mp himageOne
  obtain ⟨a, haA, hau⟩ := Finset.mem_image.mp huI
  obtain ⟨b, hbA, hbv⟩ := Finset.mem_image.mp hvI
  have hlabne : label a ≠ label b := by
    intro h
    change halfIntervalLabel π α a = halfIntervalLabel π α b at h
    apply huv
    rw [← hau, ← hbv]
    have ha := (halfIntervalLabel_spec π α a (houter a haA)).2
    have hb := (halfIntervalLabel_spec π α b (houter b hbA)).2
    rw [ha, hb, h]
  have hlaI : label a ∈ I := Finset.mem_image.mpr ⟨a, haA, rfl⟩
  have hlbI : label b ∈ I := Finset.mem_image.mpr ⟨b, hbA, rfl⟩
  let lo := I.min' hIne
  let hi := I.max' hIne
  have hloI : lo ∈ I := Finset.min'_mem I hIne
  have hhiI : hi ∈ I := Finset.max'_mem I hIne
  have hlohi : lo < hi := Finset.min'_lt_max' I hlaI hlbI hlabne
  obtain ⟨p, hpA, hplabel⟩ := Finset.mem_image.mp hloI
  obtain ⟨q, hqA, hqlabel⟩ := Finset.mem_image.mp hhiI
  change halfIntervalLabel π α p = lo at hplabel
  change halfIntervalLabel π α q = hi at hqlabel
  let L := hi - lo
  have hL : 0 < L := by dsimp [L]; omega
  have hhiShort : 2 * hi < m := by
    rw [← hqlabel]
    exact (halfIntervalLabel_spec π α q (houter q hqA)).1
  have hLShort : 2 * L < m := by dsimp [L]; omega
  refine ⟨p, hpA, q, hqA, L, hL, hLShort, ?_, ?_⟩
  · have hpπ := (halfIntervalLabel_spec π α p (houter p hpA)).2
    have hqπ := (halfIntervalLabel_spec π α q (houter q hqA)).2
    rw [map_sub, hpπ, hqπ, hplabel, hqlabel]
    dsimp [L]
    have hlole : lo ≤ hi := Nat.le_of_lt hlohi
    have hdecomp : lo + (hi - lo) = hi := Nat.add_sub_of_le hlole
    have hcast := congrArg (fun n : ℕ => (n : ZMod m)) hdecomp
    simp only [Nat.cast_add] at hcast
    rw [← hcast]
    abel
  · intro x hxA
    have hxI : label x ∈ I := Finset.mem_image.mpr ⟨x, hxA, rfl⟩
    have hlox : lo ≤ label x := Finset.min'_le I (label x) hxI
    have hxhi : label x ≤ hi := Finset.le_max' I (label x) hxI
    let k := label x - lo
    have hkL : k ≤ L := by dsimp [k, L]; omega
    have hxShort := (halfIntervalLabel_spec π α x (houter x hxA)).1
    have hkShort : 2 * k < m := by dsimp [k]; omega
    refine ⟨k, hkL, hkShort, ?_⟩
    have hxπ := (halfIntervalLabel_spec π α x (houter x hxA)).2
    have hpπ := (halfIntervalLabel_spec π α p (houter p hpA)).2
    rw [map_sub, hxπ, hpπ, hplabel]
    dsimp [k]
    have hdecomp : lo + (label x - lo) = label x := Nat.add_sub_of_le hlox
    have hcast := congrArg (fun n : ℕ => (n : ZMod m)) hdecomp
    simp only [Nat.cast_add] at hcast
    rw [← hcast]
    abel

/-- Translating by the lower endpoint turns the preceding data into the exact
strict-half hypothesis based at zero. -/
theorem normalized_translate_outer
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m)
    (p : ZMod N) (L : ℕ)
    (hnorm : ∀ x ∈ A, ∃ k : ℕ, k ≤ L ∧ 2 * k < m ∧
      π (x - p) = (k : ZMod m)) :
    ∀ y ∈ (-p +ᵥ A),
      ∃ k : ℕ, k ≤ L ∧ 2 * k < m ∧ π y = (k : ZMod m) := by
  intro y hy
  obtain ⟨x, hxA, hxy⟩ := Finset.mem_vadd_finset.mp hy
  obtain ⟨k, hkL, hkshort, hkπ⟩ := hnorm x hxA
  refine ⟨k, hkL, hkshort, ?_⟩
  rw [← hxy]
  simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hkπ

/-- Under normalized strict-half data, the graph label is the displayed
integer coordinate and is bounded by the occupied endpoint `L`. -/
theorem halfIntervalLabel_eq_normalized
    (A : Finset (ZMod N)) (π : ZMod N →+ ZMod m) (L : ℕ)
    (houter : ∀ x ∈ A,
      ∃ k : ℕ, k ≤ L ∧ 2 * k < m ∧ π x = (k : ZMod m))
    {x : ZMod N} (hx : x ∈ A) :
    ∃ k : ℕ, k ≤ L ∧ halfIntervalLabel π 0 x = k := by
  obtain ⟨k, hkL, hkshort, hkπ⟩ := houter x hx
  have hs := halfIntervalLabel_spec π 0 x
    ⟨k, hkshort, by simpa using hkπ⟩
  refine ⟨k, hkL, ?_⟩
  apply short_zmod_cast_injective hs.1 hkshort
  simpa [hkπ] using hs.2.symm

end Erdos336
