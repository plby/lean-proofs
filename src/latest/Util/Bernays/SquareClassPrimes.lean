import Util.Bernays.SignedProducts
import Util.Bernays.ClassPrimeDivergence

/-!
# Large prime packets outside proper subgroups of the square classes
-/

namespace Bernays

def classSquareMonoidHom {G : Type*} [CommGroup G] : G →* (classSquareSubgroup : Subgroup G) where
  toFun := classSquareElement
  map_one' := Subtype.ext (by simp [classSquareElement])
  map_mul' x y := Subtype.ext (by simp [classSquareElement, mul_pow])

theorem classSquareMonoidHom_surjective {G : Type*} [CommGroup G] :
    Function.Surjective (classSquareMonoidHom : G → (classSquareSubgroup : Subgroup G)) := by
  rintro ⟨y, x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

theorem squarePreimage_ne_top {G : Type*} [CommGroup G]
    (H : Subgroup (classSquareSubgroup : Subgroup G)) (hH : H ≠ ⊤) :
    H.comap classSquareMonoidHom ≠ ⊤ := by
  intro htop
  apply hH
  ext y
  obtain ⟨x, rfl⟩ := classSquareMonoidHom_surjective y
  have hx : x ∈ H.comap classSquareMonoidHom := htop ▸ Subgroup.mem_top x
  simp only [Subgroup.mem_top, iff_true]
  exact hx

theorem exists_squareBadPrimePacket {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (classSquareSubgroup : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b))),
      H ≠ ⊤ → ∀ R : ℝ, ∃ P : Finset (SplitPrime d b),
        (∀ s ∈ P, classSquareElement (s.idealClass hD) ∉ H) ∧
          R < ∑ s ∈ P, (s.1 : ℝ)⁻¹ := by
  classical
  let := quadraticOrderIsDomain hD
  intro H hH R
  let K := H.comap classSquareMonoidHom
  have hnot := not_summable_badSplitPrimeWeight hD K (squarePreimage_ne_top H hH)
  have hex : ∃ F : Finset (SplitPrime d b), R < ∑ s ∈ F, badSplitPrimeWeight hD K s := by
    by_contra! h
    exact hnot (summable_of_sum_le (badSplitPrimeWeight_nonneg hD K) h)
  obtain ⟨F, hF⟩ := hex
  let P := F.filter fun s => s.idealClass hD ∉ K
  refine ⟨P, fun s hs => (Finset.mem_filter.mp hs).2, ?_⟩
  have heq : ∑ s ∈ P, (s.1 : ℝ)⁻¹ = ∑ s ∈ F, badSplitPrimeWeight hD K s := by
    simp only [P, Finset.sum_filter, badSplitPrimeWeight]
  rwa [heq]

theorem SplitPrime.character_ne_neg_one {d b : ℤ} (hD : b ^ 2 + 4 * d ≠ 0)
    (s : SplitPrime d b) : discriminantCharacter (b ^ 2 + 4 * d) hD s.1 ≠ -1 := by
  by_cases hc : s.1.Coprime (discriminantLevel (b ^ 2 + 4 * d))
  · exact (discriminantCharacter_root_iff hD hc).mp s.2.2.2
  · have hz : discriminantCharacter (b ^ 2 + 4 * d) hD s.1 = 0 := by
      apply MulChar.map_nonunit
      rwa [ZMod.isUnit_iff_coprime]
    rw [hz]
    norm_num

end Bernays
