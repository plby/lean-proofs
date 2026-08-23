import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph

/-- Shorten a path joining two sets until it meets each set only at the
corresponding endpoint. Any ambient vertex-avoidance constraint is preserved. -/
theorem exists_set_path_within {V : Type*} (G : SimpleGraph V) (A B S : Set V)
    (hex : ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsPath ∧ ∀ v ∈ p.support, v ∈ S) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsPath ∧ (∀ v ∈ p.support, v ∈ S) ∧
      (∀ v ∈ p.support, v ∈ A → v = a) ∧
      (∀ v ∈ p.support, v ∈ B → v = b) := by
  classical
  let Q (n : ℕ) := ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
    p.IsPath ∧ (∀ v ∈ p.support, v ∈ S) ∧ p.length = n
  have hQ : ∃ n, Q n := by
    obtain ⟨a, ha, b, hb, p, hp, hS⟩ := hex
    exact ⟨p.length, a, ha, b, hb, p, hp, hS, rfl⟩
  obtain ⟨a, ha, b, hb, p, hp, hS, hlen⟩ := Nat.find_spec hQ
  have hmin {x y : V} (hx : x ∈ A) (hy : y ∈ B) (q : G.Walk x y)
      (hq : q.IsPath) (hqS : ∀ v ∈ q.support, v ∈ S) : p.length ≤ q.length := by
    rw [hlen]
    exact Nat.find_min' hQ ⟨x, hx, y, hy, q, hq, hqS, rfl⟩
  refine ⟨a, ha, b, hb, p, hp, hS, ?_, ?_⟩
  · intro v hv hvA
    by_contra hne
    have hlt := p.length_dropUntil_lt_length hv hne
    have hle := hmin hvA hb (p.dropUntil v hv) (hp.dropUntil hv)
      (fun w hw ↦ hS w (p.support_dropUntil_subset_support hv hw))
    omega
  · intro v hv hvB
    by_contra hne
    have hlt := p.length_takeUntil_lt_length hv hne
    have hle := hmin ha hvB (p.takeUntil v hv) (hp.takeUntil hv)
      (fun w hw ↦ hS w (p.support_takeUntil_subset_support hv hw))
    omega

end Erdos1105

#print axioms Erdos1105.exists_set_path_within
