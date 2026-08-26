import Mathlib
import ErdosProblems.Erdos336.Basic
import ErdosProblems.Erdos336.ThickAbsorption

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Normalizing an at-most basis and a removed element
-/

namespace Erdos336

/-- Translate a set of naturals by one of its elements, viewing the result in
`ℤ`. -/
def TranslateNatSet (A : Set ℕ) (b : ℕ) : Set ℤ :=
  {z | ∃ a : ℕ, a ∈ A ∧ z = (a : ℤ) - (b : ℤ)}

private lemma sum_map_nat_sub (xs : List ℕ) (b : ℕ) :
    (xs.map (fun a : ℕ => (a : ℤ) - (b : ℤ))).sum =
      (xs.sum : ℤ) - (xs.length : ℤ) * (b : ℤ) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih,
        Nat.cast_add, Nat.cast_one]
      ring

/-- Translating by a member puts zero in the translated set. -/
theorem zero_mem_translateNatSet {A : Set ℕ} {b : ℕ} (hb : b ∈ A) :
    (0 : ℤ) ∈ TranslateNatSet A b := by
  exact ⟨b, hb, by simp⟩

/-- An eventual at-most-`h` basis becomes an eventual exact-`h` parent after
adjoining zero; after translating by `b∈A`, the adjoined zero is the one
exceptional element `-b`.  This is the precise normalization used by the
thick-sumset transference argument. -/
theorem eventuallyWithOneExtra_translate
    {A : Set ℕ} {h b : ℕ}
    (hatMost : EventuallyAtMost A h) :
    EventuallyWithOneExtra (TranslateNatSet A b) (-(b : ℤ)) h := by
  obtain ⟨N, hN⟩ := hatMost
  refine ⟨(N : ℤ), ?_⟩
  intro n hn
  have hn0 : 0 ≤ n := by omega
  let m : ℕ := n.toNat + h * b
  have hmcast : (m : ℤ) = n + (h : ℤ) * (b : ℤ) := by
    dsimp [m]
    rw [Int.toNat_of_nonneg hn0]
  have hmN : N ≤ m := by
    have hprod : 0 ≤ (h : ℤ) * (b : ℤ) := mul_nonneg (by positivity) (by positivity)
    have hcastN : (N : ℤ) ≤ (m : ℤ) := by rw [hmcast]; omega
    exact_mod_cast hcastN
  obtain ⟨k, hkh, xs, hlen, hxmem, hxsum⟩ := hN m hmN
  let j := h - k
  refine ⟨j, Nat.sub_le _ _, ?_⟩
  have hlen' : k = h - j := by
    dsimp [j]
    omega
  let ys : List ℤ := xs.map (fun a : ℕ => (a : ℤ) - (b : ℤ))
  refine ⟨ys, ?_, ?_, ?_⟩
  · dsimp [ys]
    simp [hlen, hlen']
  · intro z hz
    simp only [ys, List.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, hxmem a ha, rfl⟩
  · rw [show ys.sum = (m : ℤ) - (k : ℤ) * (b : ℤ) by
      dsimp [ys]
      rw [sum_map_nat_sub, hlen, hxsum]]
    rw [hmcast]
    dsimp [j]
    have hsub : ((h - k : ℕ) : ℤ) = (h : ℤ) - (k : ℤ) := by omega
    rw [hsub]
    ring

/-- Exact eventual representations are preserved by translation into `ℤ`. -/
theorem eventuallyExactlyZ_translate
    {A : Set ℕ} {q b : ℕ}
    (hexact : EventuallyExactly A q) :
    EventuallyExactlyZ (TranslateNatSet A b) q := by
  obtain ⟨N, hN⟩ := hexact
  refine ⟨(N : ℤ), ?_⟩
  intro n hn
  have hn0 : 0 ≤ n := by omega
  let m : ℕ := n.toNat + q * b
  have hmcast : (m : ℤ) = n + (q : ℤ) * (b : ℤ) := by
    dsimp [m]
    rw [Int.toNat_of_nonneg hn0]
  have hmN : N ≤ m := by
    have hprod : 0 ≤ (q : ℤ) * (b : ℤ) := mul_nonneg (by positivity) (by positivity)
    have hcastN : (N : ℤ) ≤ (m : ℤ) := by rw [hmcast]; omega
    exact_mod_cast hcastN
  obtain ⟨xs, hlen, hxmem, hxsum⟩ := hN m hmN
  let ys : List ℤ := xs.map (fun a : ℕ => (a : ℤ) - (b : ℤ))
  refine ⟨ys, by simp [ys, hlen], ?_, ?_⟩
  · intro z hz
    simp only [ys, List.mem_map] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, hxmem a ha, rfl⟩
  · dsimp [ys]
    rw [sum_map_nat_sub, hlen, hxsum, hmcast]
    ring

private lemma lift_translate_list
    {A : Set ℕ} {b : ℕ} (zs : List ℤ)
    (hzs : ∀ z ∈ zs, z ∈ TranslateNatSet A b) :
    ∃ xs : List ℕ,
      xs.length = zs.length ∧
      (∀ a ∈ xs, a ∈ A) ∧
      (xs.sum : ℤ) = zs.sum + (zs.length : ℤ) * (b : ℤ) := by
  induction zs with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | cons z zs ih =>
      obtain ⟨a, haA, hza⟩ := hzs z (by simp)
      have htail : ∀ w ∈ zs, w ∈ TranslateNatSet A b := by
        intro w hw
        exact hzs w (by simp [hw])
      obtain ⟨xs, hlen, hxmem, hxsum⟩ := ih htail
      refine ⟨a :: xs, by simp [hlen], ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact haA
        · exact hxmem x hx
      · simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hxsum, hza]
        ring

/-- Conversely, eventual exact coverage of the integer translate gives
coverage of the original natural set at the same exact length. -/
theorem eventuallyExactly_of_eventuallyExactlyZ_translate
    {A : Set ℕ} {q b : ℕ}
    (hexact : EventuallyExactlyZ (TranslateNatSet A b) q) :
    EventuallyExactly A q := by
  obtain ⟨N, hN⟩ := hexact
  let N0 : ℕ := (N + (q : ℤ) * (b : ℤ)).toNat + 1
  refine ⟨N0, ?_⟩
  intro n hn
  let m : ℤ := (n : ℤ) - (q : ℤ) * (b : ℤ)
  have hmN : N ≤ m := by
    have hNbound : N + (q : ℤ) * (b : ℤ) < (N0 : ℕ) := by
      dsimp [N0]
      have hle : N + (q : ℤ) * (b : ℤ) ≤
          ((N + (q : ℤ) * (b : ℤ)).toNat : ℤ) := by
        rcases le_total 0 (N + (q : ℤ) * (b : ℤ)) with hp | hnneg
        · rw [Int.toNat_of_nonneg hp]
        · have hz : (0 : ℤ) ≤
              ((N + (q : ℤ) * (b : ℤ)).toNat : ℤ) := by positivity
          omega
      push_cast
      omega
    have hN0n : (N0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    dsimp [m]
    omega
  obtain ⟨zs, hlen, hzmem, hzsum⟩ := hN m hmN
  obtain ⟨xs, hxslen, hxmem, hxsum⟩ := lift_translate_list zs hzmem
  refine ⟨xs, by simpa [hlen] using hxslen, hxmem, ?_⟩
  have hxsum' := hxsum
  rw [hlen, hzsum] at hxsum'
  dsimp [m] at hxsum'
  have : (xs.sum : ℤ) = (n : ℤ) := by linarith
  exact_mod_cast this

/-- Every eventual at-most basis contains an element (the explicit positivity
assumption on the represented target rules out the empty list). -/
theorem eventuallyAtMost_nonempty
    {A : Set ℕ} {h : ℕ} (hatMost : EventuallyAtMost A h) : A.Nonempty := by
  obtain ⟨N, hN⟩ := hatMost
  obtain ⟨k, hk, xs, hlen, hxmem, hxsum⟩ := hN (N + 1) (by omega)
  have hxs : xs ≠ [] := by
    intro he
    subst xs
    simp at hxsum
  obtain ⟨a, xs, rfl⟩ := List.exists_cons_of_ne_nil hxs
  exact ⟨a, hxmem a (by simp)⟩

end Erdos336
