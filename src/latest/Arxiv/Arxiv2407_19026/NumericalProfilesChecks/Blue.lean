import Arxiv.Arxiv2407_19026.KernelBounds
import Arxiv.Arxiv2407_19026.NumericalProfilesChecks.ULower

namespace Arxiv2407_19026
namespace Beta0Affine

open KernelBounds

noncomputable section

private def blueCorrectionPolynomial (z : ℝ) : ℝ :=
  -1 / 4 + 41 / 100 * z + 4 / 25 * z ^ 2 - 2 / 25 * z ^ 3

private lemma blue_correction_polynomial_abs_le {z : ℝ}
    (hz : z ∈ Set.Icc 0 1) :
    |blueCorrectionPolynomial z| ≤ 1 / 4 := by
  rw [abs_le]
  constructor
  · have hbracket :
        0 ≤ (41 / 100 : ℝ) + 4 / 25 * z - 2 / 25 * z ^ 2 := by
      nlinarith [hz.1, hz.2, mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hfactor :
        blueCorrectionPolynomial z + 1 / 4 =
          z * (41 / 100 + 4 / 25 * z - 2 / 25 * z ^ 2) := by
      unfold blueCorrectionPolynomial
      ring
    nlinarith [mul_nonneg hz.1 hbracket]
  · have hbracket :
        0 ≤ (49 / 100 : ℝ) + 2 / 25 * z - 2 / 25 * z ^ 2 := by
      nlinarith [hz.1, hz.2, mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
    have hfactor :
        1 / 4 - blueCorrectionPolynomial z =
          1 / 100 + (1 - z) *
            (49 / 100 + 2 / 25 * z - 2 / 25 * z ^ 2) := by
      unfold blueCorrectionPolynomial
      ring
    nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) hbracket]

private lemma blue_correction_lower {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    blueCorrectionPolynomial z * expNegTaylor9 z -
        expNegError10 z / 4 ≤
      beta0CorrectionSlope z := by
  have happ := exp_neg_approx hz
  have hs := blue_correction_polynomial_abs_le hz
  have he : 0 ≤ expNegError10 z := by
    unfold expNegError10
    positivity
  have hmul :
      |blueCorrectionPolynomial z *
          (Real.exp (-z) - expNegTaylor9 z)| ≤
        expNegError10 z / 4 := by
    rw [abs_mul]
    calc
      |blueCorrectionPolynomial z| *
          |Real.exp (-z) - expNegTaylor9 z| ≤
          (1 / 4 : ℝ) * expNegError10 z :=
        mul_le_mul hs happ (abs_nonneg _) (by norm_num)
      _ = expNegError10 z / 4 := by ring
  have hlower := neg_le_of_abs_le hmul
  unfold beta0CorrectionSlope blueCorrectionPolynomial at *
  ring_nf at *
  nlinarith

private def blueProduct (z : ℝ) : ℝ :=
  (1 + z) * (9999 / 10000) * beta0U z

private def blueCorrectionLower (z : ℝ) : ℝ :=
  blueCorrectionPolynomial z * expNegTaylor9 z -
    expNegError10 z / 4

private lemma blue_product_pos {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    0 < blueProduct z := by
  have hu : (0 : ℝ) < beta0U z :=
    lt_of_lt_of_le (by norm_num) (u_lower z hz)
  unfold blueProduct
  exact mul_pos (mul_pos (by linarith [hz.1]) (by norm_num)) hu

set_option maxRecDepth 10000 in
private lemma blue_low_product_numerator_nonneg {z : ℝ}
    (hz : z ∈ Set.Icc 0 1) :
    0 ≤
      2 * blueProduct z *
          (blueCorrectionLower z - 1 / 100000) +
        blueProduct z ^ 2 - 1 := by
  let coeffs : List ℕ := [
    248321392265878667519510634069616009920,
    3580768080047255366690418714703484097600,
    24760936029908475717238003646988224637840,
    112205294768499100447318831229134696599600,
    386153821509512079014518571011943704588860,
    1105149980282392539825358330661264697912120,
    2760592737215107399472081092770587167972500,
    6078513767709159827797868398229160710502000,
    11641465192756503431638746199282692030997140,
    19040193370220724802296239603828798704454280,
    26231723517430516937032849518893096001167220,
    30207148741121477830996078943593089205947120,
    28970129170821560428166198337105422615940240,
    23096827919479380288425435331072178403758560,
    15272266019102112753635218019132173272407880,
    8333232566759162198638623735204435921956880,
    3715321287379567666718022733088476365249900,
    1331256069486407794600521057034494930543480,
    373888950347783422468779332260874197334220,
    79339172569779292268799086262044237028960,
    12002783418813609369100590543653855948640,
    1158268082552543941080001452921096368640,
    53180123088952863817665462249036914880]
  have hsum := bernstein_sum_nonneg 22 coeffs hz
  have hidentity :
      (33331662000000000000000000000000000000000 : ℝ) *
          (2 * blueProduct z *
              (blueCorrectionLower z - 1 / 100000) +
            blueProduct z ^ 2 - 1) =
        ∑ i ∈ Finset.range 23,
          (coeffs.getD i 0 : ℝ) * z ^ i * (1 - z) ^ (22 - i) := by
    norm_num [coeffs, Finset.sum_range_succ, blueProduct,
      blueCorrectionLower, blueCorrectionPolynomial,
      expNegTaylor9, expNegError10, beta0U, Nat.factorial]
    ring
  rw [← hidentity] at hsum
  nlinarith

set_option maxRecDepth 10000 in
private lemma blue_high_product_numerator_nonneg {z : ℝ}
    (hz : z ∈ Set.Icc 0 1) :
    0 ≤
      (blueCorrectionLower z - 1 / 100000) *
          3 * (blueProduct z + 1) ^ 3 +
        6 * (blueProduct z - 1) * (blueProduct z + 1) ^ 2 +
        2 * (blueProduct z - 1) ^ 3 := by
  let coeffs : List ℕ := [
    140410525270801235837955267591912242542768235999622368729643155713228800,
    6186409637697857226059719691856382938040229733238944705446910463861555200,
    131549962890647328429553219261879920235546345821569406030984528549819187200,
    1809629676502543009899036442597438019985532171910886975551780929837865164800,
    18153100633337003293793804847645506868850960051011037906779373759959582720000,
    141696248163763392302152319756366708242455899698288960913885786309426020300800,
    896141270683149419890719139942013283051671577382133503274656690669641527270400,
    4720146712296264989904873314458730348793073947079367296730262206584962984345600,
    21122212241917676806214169325598819559374303194157833472030069201340486372480000,
    81519615485498779747570705212158556301073039207304582672097684573945349423769600,
    274548414467127681200744059301617988883442986764935957524481641037237094852044800,
    814454977510553094547690584334960816717131559499003704592193097801424390100710400,
    2144262538758371387871947749266843878378543652899147910724005218130074247106982400,
    5040859575312302388425762640093742100376551235893342035762774280747975747655283200,
    10634055723553968579385114109465416470920803867233371545328194450996924618566024000,
    20211488814294395311695559501615530866409809096083091356416859130285321822562405600,
    34720998161714486789543250463775647588625889039158767230123154203702340259876454000,
    54047445784023633143518824508843594577533315154527942361148925218789003215311953600,
    76381688118878413291164004088277517161153017803658592258617070795066806353482530400,
    98142569840182327898921693250361231676920364490035410242694970647018935762653791200,
    114764879084246217075308720301915745059752691555241205082632864599577150229282302400,
    122207326119938082379068371657693054354842922619058801182711448553358559295189215200,
    118524873111668793344291510246611792777400232424892012115359772232224580860695665200,
    104681552698828880361702541521475990316605605514567767798467916736865158601073463200,
    84146596059071487135982477455330619865481706623833737432524194160220499685355699200,
    61501850545701017916011564686412158921067604765347285382062302597528541451757956000,
    40814014805100382776311023582227511147135111437694333424287634534807195569269428400,
    24545111813833862476881365731896767518010271469877485356642876410342672865839515200,
    13343511385177073057027607324143540145298614813009336151657376986864596206284788000,
    6536574339899672511049090206399651280082171542099584917770827742421751209670590400,
    2874034635912280054105329290298972526358037845551709581651844531739759522252230400,
    1128702802987211213112521227611917087073397743016537028144395983570754427430705600,
    393558381099339207563941801231519790133688672208414959963248132557874737009770800,
    120940148941390273422943704594627833740737814792766653662250489838886466157066400,
    32454580568856698974286066368590915313740947710956603359578722857048952949263600,
    7518013410552722453172402122823776269257328614878284229556176195756485108884000,
    1481117938687697366619787280517152268709187096713280471093760554492155406718000,
    243313622836620235636179705244826850421715286124430084511527114224031619105600,
    32432878484972433898351534148946580499651314910852818399554876523948241179200,
    3370393223067306834472761909178135977362076338401452927006382807073237145600,
    256159918507159098826143027739292278409593671054196382354485288753155360000,
    12660585522922044888810667258055620152567953352832597657297961038577894400,
    305076011429746089654584263027849033069123896260052673539188536890854400]
  have hsum := bernstein_sum_nonneg 42 coeffs hz
  have hidentity :
      (14720844750500528640000000000000000000000000000000000000000000000000000000 : ℝ) *
          ((blueCorrectionLower z - 1 / 100000) *
              3 * (blueProduct z + 1) ^ 3 +
            6 * (blueProduct z - 1) * (blueProduct z + 1) ^ 2 +
            2 * (blueProduct z - 1) ^ 3) =
        ∑ i ∈ Finset.range 43,
          (coeffs.getD i 0 : ℝ) * z ^ i * (1 - z) ^ (42 - i) := by
    norm_num [coeffs, Finset.sum_range_succ, blueProduct,
      blueCorrectionLower, blueCorrectionPolynomial,
      expNegTaylor9, expNegError10, beta0U, Nat.factorial]
    ring
  rw [← hidentity] at hsum
  nlinarith

private lemma blue_log_product {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    Real.log (blueProduct z) =
      Real.log (1 + z) + Real.log (9999 / 10000) +
        Real.log (beta0U z) := by
  have hz1 : 1 + z ≠ 0 := by linarith [hz.1]
  have hc : (9999 / 10000 : ℝ) ≠ 0 := by norm_num
  have hu : beta0U z ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (u_lower z hz))
  rw [blueProduct, Real.log_mul (mul_ne_zero hz1 hc) hu,
    Real.log_mul hz1 hc]

private lemma blue_algebraic_lower {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    0 ≤ blueCorrectionLower z - 1 / 100000 +
      Real.log (blueProduct z) := by
  have hx := blue_product_pos hz
  by_cases hx1 : blueProduct z ≤ 1
  · have hlog := log_lower_of_le_one hx hx1
    have hnum := blue_low_product_numerator_nonneg hz
    have hidentity :
        2 * blueProduct z *
            (blueCorrectionLower z - 1 / 100000 +
              (blueProduct z - (blueProduct z)⁻¹) / 2) =
          2 * blueProduct z *
              (blueCorrectionLower z - 1 / 100000) +
            blueProduct z ^ 2 - 1 := by
      field_simp [hx.ne']
      ring
    rw [← hidentity] at hnum
    have hrat :
        0 ≤ blueCorrectionLower z - 1 / 100000 +
          (blueProduct z - (blueProduct z)⁻¹) / 2 :=
      (mul_nonneg_iff_of_pos_left (mul_pos two_pos hx)).mp hnum
    linarith
  · have hx1' : 1 ≤ blueProduct z := le_of_lt (lt_of_not_ge hx1)
    let y := (blueProduct z - 1) / (blueProduct z + 1)
    have hlog := log_lower_of_one_le hx1'
    have hnum := blue_high_product_numerator_nonneg hz
    have hxp1 : 0 < blueProduct z + 1 := by positivity
    have hidentity :
        3 * (blueProduct z + 1) ^ 3 *
            (blueCorrectionLower z - 1 / 100000 +
              2 * (y + y ^ 3 / 3)) =
          (blueCorrectionLower z - 1 / 100000) *
              3 * (blueProduct z + 1) ^ 3 +
            6 * (blueProduct z - 1) * (blueProduct z + 1) ^ 2 +
            2 * (blueProduct z - 1) ^ 3 := by
      dsimp [y]
      field_simp [hxp1.ne']
      ring
    rw [← hidentity] at hnum
    have hrat :
        0 ≤ blueCorrectionLower z - 1 / 100000 +
          2 * (y + y ^ 3 / 3) :=
      (mul_nonneg_iff_of_pos_left
        (mul_pos (by norm_num) (pow_pos hxp1 3))).mp hnum
    dsimp only at hlog
    linarith

lemma blue_lower :
    ∀ z ∈ Set.Icc (0 : ℝ) 1,
      (1 / 100000 : ℝ) ≤ beta0PolynomialBlueLogMargin z := by
  intro z hz
  have hcorr := blue_correction_lower hz
  have halg := blue_algebraic_lower hz
  have hlog := blue_log_product hz
  change blueCorrectionLower z ≤ beta0CorrectionSlope z at hcorr
  unfold beta0PolynomialBlueLogMargin
  linarith [hlog]

end
end Beta0Affine
end Arxiv2407_19026
