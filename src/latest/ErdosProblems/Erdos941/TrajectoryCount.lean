import ErdosProblems.Erdos941.TrajectoryWords
import ErdosProblems.Erdos941.CardCollision

/-! # Finite trajectory counting from avoidance and shadowing -/

namespace Erdos941

noncomputable def allAvoidingCodes (p : ℕ) [NeZero (p ^ 2)] (t : ZMod (p ^ 2))
    (target : ModularTriple p → Prop) (k : ℕ) :
    Finset ((Axis × ModularTriple p) × List (Fin 3)) := by
  classical
  exact Finset.univ.biUnion fun s : Axis × ModularTriple p =>
    (avoidingWords (hitFlagStep (fun a v => linearTurn t a v) (modularBadTurn p target))
      hitFlagTarget k (s, false)).image fun w => (s, w)

theorem allAvoidingCodes_card_le (p : ℕ) [NeZero (p ^ 2)] (t : ZMod (p ^ 2))
    (target : ModularTriple p → Prop) (k B : ℕ)
    (hB : ∀ s : Axis × ModularTriple p, modularAvoidance p t target k (s, false) ≤ B) :
    (allAvoidingCodes p t target k).card ≤ Fintype.card (Axis × ModularTriple p) * B := by
  classical
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _s : Axis × ModularTriple p, B := by
      apply Finset.sum_le_sum
      intro s _
      exact Finset.card_image_le.trans ((card_avoidingWords_le _ _ k (s, false)).trans (hB s))
    _ = _ := by simp

theorem trajectoryCode_mem_allAvoidingCodes (p : ℕ) [NeZero (p ^ 2)] (t : ZMod (p ^ 2))
    (target : ModularTriple p → Prop) (ht : 3 * t = 1) (L : ℕ) (s : OrientedTriple)
    (hbad : ∀ i, i < 2 * L → ¬ modularBadTurn p target
      (orientedModState p (centeredState L s i)) (orientedChoice (centeredState L s i))) :
    trajectoryCode p L s ∈ allAvoidingCodes p t target (2 * L) := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨orientedModState p (centeredState L s 0), Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨trajectoryChoices (2 * L) (centeredState L s 0), ?_, rfl⟩
  apply (mem_avoidingWords _ _).mpr
  exact ⟨trajectoryChoices_length _ _, trajectoryChoices_avoid p t target ht _ _ hbad⟩

theorem trajectory_collision_card_le {A : Type*} [Fintype A] (p L n : ℕ)
    (o : A → OrientedTriple) (hinj : Function.Injective (fun a => (o a).1.2))
    (hn : n % 3 = 2) (hnorm : ∀ a, tripleNorm (o a).1.2 = n) :
    (collisionPairs Finset.univ (fun a => trajectoryCode p L (o a))).card ≤
      (shadowPairs n (3 ^ (2 * L))).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun ab : A × A => ((o ab.1).1.2, (o ab.2).1.2))
  · intro ab hab
    have hc := (Finset.mem_filter.mp hab).2
    exact trajectoryCode_eq_shadow hn (hnorm ab.1) (hnorm ab.2) hc
  · intro ab _ cd _ heq
    dsimp only at heq
    apply Prod.ext
    · exact hinj (congrArg (fun z : Triple × Triple => z.1) heq)
    · exact hinj (congrArg (fun z : Triple × Triple => z.2) heq)

theorem card_sq_le_avoidance_mul_shadow {A : Type*} [Fintype A]
    (p : ℕ) [NeZero (p ^ 2)] (t : ZMod (p ^ 2)) (target : ModularTriple p → Prop)
    (ht : 3 * t = 1) (L n B : ℕ) (o : A → OrientedTriple)
    (hinj : Function.Injective (fun a => (o a).1.2)) (hn : n % 3 = 2)
    (hnorm : ∀ a, tripleNorm (o a).1.2 = n)
    (hB : ∀ s : Axis × ModularTriple p, modularAvoidance p t target (2 * L) (s, false) ≤ B)
    (hbad : ∀ a i, i < 2 * L → ¬ modularBadTurn p target
      (orientedModState p (centeredState L (o a) i))
      (orientedChoice (centeredState L (o a) i))) :
    Fintype.card A ^ 2 ≤ (Fintype.card (Axis × ModularTriple p) * B) *
      (shadowPairs n (3 ^ (2 * L))).card := by
  classical
  have himage : (Finset.univ.image (fun a => trajectoryCode p L (o a))).card ≤
      Fintype.card (Axis × ModularTriple p) * B := by
    apply (Finset.card_le_card ?_).trans (allAvoidingCodes_card_le p t target (2 * L) B hB)
    intro c hc
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
    exact trajectoryCode_mem_allAvoidingCodes p t target ht L (o a) (hbad a)
  have hcollision := trajectory_collision_card_le p L n o hinj hn hnorm
  have h := card_sq_le_image_mul_collisions Finset.univ (fun a => trajectoryCode p L (o a))
  rw [Finset.card_univ] at h
  exact h.trans (Nat.mul_le_mul himage hcollision)

end Erdos941
