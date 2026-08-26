import ErdosProblems.Erdos941.RootData
import ErdosProblems.Erdos941.IntertwinerCounting

/-! # Transferring a lower bound for quadratic roots to a lower bound for sphere points -/

namespace Erdos941

open scoped Quaternion

theorem allRoot_finite_count_bound {v : Triple} {n : ℕ} (hn : 0 < n)
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℝ, 0 ≤ X → ∀ s : Finset (RootDatum n),
      (∀ d ∈ s, (d.modulus : ℝ) ≤ X) →
      (s.card : ℝ) ≤ 8 * (sphereCount n : ℝ) * X / Real.sqrt (n : ℝ) +
        K * Real.sqrt X + (sphereCount n : ℝ) := by
  classical
  choose K hK hcount using fun w : Triple => exists_integralIntertwiner_count hn hv hp w
  refine ⟨∑ w ∈ spherePoints n, K w, Finset.sum_nonneg (fun w _ => hK w), ?_⟩
  intro X hX s hs
  let point : RootDatum n → Triple := fun d => (allRootSphereWitness hv d).point
  have hfiber (w : Triple) :
      ((s.filter fun d => point d = w).card : ℝ) ≤
        8 * X / Real.sqrt (n : ℝ) + K w * Real.sqrt X + 1 := by
    let t := s.filter fun d => point d = w
    let f : {d // d ∈ t} → integralIntertwiners v w := fun d =>
      ⟨allRootQuaternionChoice hv d, by
        have hd := (Finset.mem_filter.mp d.property).2
        change (allRootSphereWitness hv d).point = w at hd
        change ((allRootSphereWitness hv d).quaternion : ℍ[ℚ]) * pureQuaternion v =
          pureQuaternion w * (allRootSphereWitness hv d).quaternion
        rw [← hd]
        exact (allRootSphereWitness hv d).intertwines⟩
    have hinj : Function.Injective f := by
      intro d e h
      apply Subtype.ext
      apply allRootQuaternionChoice_injective hv hp
      exact congrArg Subtype.val h
    have hnorm : ∀ q ∈ t.attach.image f, (hurwitzNorm q : ℝ) ≤ X := by
      intro q hq
      obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hq
      change (hurwitzNorm (allRootSphereWitness hv d).quaternion : ℝ) ≤ X
      rw [(allRootSphereWitness hv d).norm_eq]
      exact hs d (Finset.mem_filter.mp d.property).1
    have hh := hcount w X hX (t.attach.image f) hnorm
    rw [Finset.card_image_of_injective t.attach hinj, Finset.card_attach] at hh
    exact hh
  have hcard : s.card = ∑ w ∈ spherePoints n, (s.filter fun d => point d = w).card :=
    Finset.card_eq_sum_card_fiberwise (by
      intro d _
      exact (allRootSphereWitness hv d).point_mem)
  calc
    (s.card : ℝ) = ∑ w ∈ spherePoints n, ((s.filter fun d => point d = w).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ w ∈ spherePoints n, (8 * X / Real.sqrt (n : ℝ) + K w * Real.sqrt X + 1) :=
      Finset.sum_le_sum fun w _ => hfiber w
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
      dsimp [sphereCount]
      ring

end Erdos941
