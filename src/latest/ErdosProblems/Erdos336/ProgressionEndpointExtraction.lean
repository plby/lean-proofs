import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Any nontrivial image supported in a finite cyclic interval has a
smallest endpoint-attaining subinterval, with the same orientation. -/
theorem exists_endpoint_subinterval {m L : ℕ} (π : G →+ ZMod m) {C : Set G} {α : ZMod m}
    (houter : ∀ x ∈ C, ∃ k : ℕ, k ≤ L ∧ π x = α + (k : ZMod m))
    (hpair : ∃ p ∈ C, ∃ q ∈ C, π p ≠ π q) :
    ∃ (α₀ : ZMod m) (L₀ : ℕ) (p q : G),
      0 < L₀ ∧ L₀ ≤ L ∧
      (∀ x ∈ C, ∃ k : ℕ, k ≤ L₀ ∧ π x = α₀ + (k : ZMod m)) ∧
      p ∈ C ∧ q ∈ C ∧ π q = π p + (L₀ : ZMod m) := by
  classical
  let I : Finset ℕ := (Finset.range (L + 1)).filter fun k =>
    ∃ x ∈ C, π x = α + (k : ZMod m)
  have hindex : ∀ x ∈ C, ∃ k ∈ I, π x = α + (k : ZMod m) := by
    intro x hx
    obtain ⟨k, hkL, hk⟩ := houter x hx
    refine ⟨k, ?_, hk⟩
    simp only [I, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ⟨x, hx, hk⟩⟩
  obtain ⟨p₁, hp₁, q₁, hq₁, hpq₁⟩ := hpair
  obtain ⟨kp, hkpI, hkp⟩ := hindex p₁ hp₁
  obtain ⟨kq, hkqI, hkq⟩ := hindex q₁ hq₁
  have hkpq : kp ≠ kq := by
    intro heq
    apply hpq₁
    rw [hkp, hkq, heq]
  have hI : I.Nonempty := ⟨kp, hkpI⟩
  let lo : ℕ := I.min' hI
  let hi : ℕ := I.max' hI
  have hlo_mem : lo ∈ I := Finset.min'_mem I hI
  have hhi_mem : hi ∈ I := Finset.max'_mem I hI
  have hlo_le (k : ℕ) (hk : k ∈ I) : lo ≤ k := Finset.min'_le I k hk
  have hle_hi (k : ℕ) (hk : k ∈ I) : k ≤ hi := Finset.le_max' I k hk
  have hlohi : lo < hi := by
    have hp_lo := hlo_le kp hkpI
    have hp_hi := hle_hi kp hkpI
    have hq_lo := hlo_le kq hkqI
    have hq_hi := hle_hi kq hkqI
    by_contra hnot
    have : hi ≤ lo := Nat.le_of_not_gt hnot
    have : kp = kq := by omega
    exact hkpq this
  have hhiL : hi ≤ L := by
    have := hhi_mem
    simp only [I, Finset.mem_filter, Finset.mem_range] at this
    omega
  have hlo_data := hlo_mem
  have hhi_data := hhi_mem
  simp only [I, Finset.mem_filter, Finset.mem_range] at hlo_data hhi_data
  obtain ⟨p, hpC, hpπ⟩ := hlo_data.2
  obtain ⟨q, hqC, hqπ⟩ := hhi_data.2
  let L₀ : ℕ := hi - lo
  let α₀ : ZMod m := α + (lo : ZMod m)
  refine ⟨α₀, L₀, p, q, ?_, ?_, ?_, hpC, hqC, ?_⟩
  · dsimp [L₀]
    omega
  · dsimp [L₀]
    omega
  · intro x hx
    obtain ⟨k, hkI, hkπ⟩ := hindex x hx
    have hlok := hlo_le k hkI
    have hkhi := hle_hi k hkI
    refine ⟨k - lo, by dsimp [L₀]; omega, ?_⟩
    rw [hkπ]
    dsimp [α₀]
    have hkdecomp : lo + (k - lo) = k := Nat.add_sub_of_le hlok
    calc
      α + (k : ZMod m) = α + ((lo + (k - lo) : ℕ) : ZMod m) := by rw [hkdecomp]
      _ = α + (lo : ZMod m) + (k - lo : ℕ) := by push_cast; abel
  · rw [hqπ, hpπ]
    dsimp [L₀]
    have hdecomp : lo + (hi - lo) = hi :=
      Nat.add_sub_of_le (Nat.le_of_lt hlohi)
    calc
      α + (hi : ZMod m) = α + ((lo + (hi - lo) : ℕ) : ZMod m) := by rw [hdecomp]
      _ = α + (lo : ZMod m) + (hi - lo : ℕ) := by push_cast; abel

end Erdos336
