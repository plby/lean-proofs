import ErdosProblems.Erdos1148.PeriodIntegerUnit
import Mathlib.NumberTheory.NumberField.Units.Regulator

/-! # The real places and unit rank of the positive quadratic field -/

namespace Erdos1148.DukeArithmetic

open NumberField

noncomputable def quadraticRealPlace {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d) :
    InfinitePlace (QuadraticDiscrAlgebra d) :=
  InfinitePlace.mk (Complex.ofRealHom.comp (quadraticRealEmbedding hd).toRingHom)

lemma quadraticRealPlace_apply {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d)
    (w : QuadraticDiscrAlgebra d) :
    quadraticRealPlace hd w = |quadraticRealEmbedding hd w| := by
  simp [quadraticRealPlace, Complex.norm_real, Real.norm_eq_abs]

lemma quadraticRealPlace_isReal {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d) :
    InfinitePlace.IsReal (quadraticRealPlace hd) := by
  apply InfinitePlace.isReal_mk_iff.mpr
  apply ComplexEmbedding.isReal_iff.mpr
  ext w
  simp [ComplexEmbedding.conjugate_coe_eq]

theorem quadraticDiscrAlgebra_nrComplexPlaces {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d) :
    InfinitePlace.nrComplexPlaces (QuadraticDiscrAlgebra d) = 0 := by
  classical
  let : Nonempty {w : InfinitePlace (QuadraticDiscrAlgebra d) // InfinitePlace.IsReal w} :=
    ⟨⟨quadraticRealPlace hd, quadraticRealPlace_isReal hd⟩⟩
  have hpos : 0 < InfinitePlace.nrRealPlaces (QuadraticDiscrAlgebra d) := Fintype.card_pos
  have hsum := InfinitePlace.card_add_two_mul_card_eq_rank (QuadraticDiscrAlgebra d)
  rw [quadraticDiscrAlgebra_finrank] at hsum
  omega

theorem quadraticDiscrAlgebra_nrRealPlaces {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d) :
    InfinitePlace.nrRealPlaces (QuadraticDiscrAlgebra d) = 2 := by
  have hsum := InfinitePlace.card_add_two_mul_card_eq_rank (QuadraticDiscrAlgebra d)
  rw [quadraticDiscrAlgebra_finrank, quadraticDiscrAlgebra_nrComplexPlaces hd] at hsum
  omega

theorem quadraticDiscrAlgebra_card_infinitePlace {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d) :
    Fintype.card (InfinitePlace (QuadraticDiscrAlgebra d)) = 2 := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    quadraticDiscrAlgebra_nrRealPlaces hd, quadraticDiscrAlgebra_nrComplexPlaces hd]

theorem quadraticDiscrAlgebra_unitRank {d : ℤ} [Fact (¬IsSquare d)] (hd : 0 < d) :
    NumberField.Units.rank (QuadraticDiscrAlgebra d) = 1 := by
  rw [NumberField.Units.rank, quadraticDiscrAlgebra_card_infinitePlace hd]

end Erdos1148.DukeArithmetic
