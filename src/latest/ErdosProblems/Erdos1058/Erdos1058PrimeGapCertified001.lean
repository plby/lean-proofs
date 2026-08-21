import ErdosProblems.Erdos1058.Erdos1058PrimeGapBase
import ErdosProblems.Erdos1058.Erdos1058PrimeCertificate

namespace Erdos1058

namespace PrimeGap210Certificate

private def primeGapCert_1_2 : PrimeCertificate := .two

private def primeGapCert_1_3 : PrimeCertificate :=
  .lucas 3 2 (.cons primeGapCert_1_2 (.nil))

private def primeGapCert_1_5 : PrimeCertificate :=
  .lucas 5 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.nil)))

private def primeGapCert_1_7 : PrimeCertificate :=
  .lucas 7 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.nil)))

private def primeGapCert_1_11 : PrimeCertificate :=
  .lucas 11 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.nil)))

private def primeGapCert_1_13 : PrimeCertificate :=
  .lucas 13 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.nil))))

private def primeGapCert_1_17 : PrimeCertificate :=
  .lucas 17 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.nil)))))

private def primeGapCert_1_19 : PrimeCertificate :=
  .lucas 19 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.nil))))

private def primeGapCert_1_23 : PrimeCertificate :=
  .lucas 23 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.nil)))

private def primeGapCert_1_29 : PrimeCertificate :=
  .lucas 29 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.nil))))

private def primeGapCert_1_31 : PrimeCertificate :=
  .lucas 31 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.nil))))

private def primeGapCert_1_37 : PrimeCertificate :=
  .lucas 37 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.nil)))))

private def primeGapCert_1_41 : PrimeCertificate :=
  .lucas 41 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.nil)))))

private def primeGapCert_1_43 : PrimeCertificate :=
  .lucas 43 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.nil))))

private def primeGapCert_1_47 : PrimeCertificate :=
  .lucas 47 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_23 (.nil)))

private def primeGapCert_1_53 : PrimeCertificate :=
  .lucas 53 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.nil))))

private def primeGapCert_1_59 : PrimeCertificate :=
  .lucas 59 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_29 (.nil)))

private def primeGapCert_1_61 : PrimeCertificate :=
  .lucas 61 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.nil)))))

private def primeGapCert_1_67 : PrimeCertificate :=
  .lucas 67 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.nil))))

private def primeGapCert_1_71 : PrimeCertificate :=
  .lucas 71 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.nil))))

private def primeGapCert_1_73 : PrimeCertificate :=
  .lucas 73 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.nil))))))

private def primeGapCert_1_79 : PrimeCertificate :=
  .lucas 79 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.nil))))

private def primeGapCert_1_83 : PrimeCertificate :=
  .lucas 83 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_41 (.nil)))

private def primeGapCert_1_89 : PrimeCertificate :=
  .lucas 89 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.nil)))))

private def primeGapCert_1_97 : PrimeCertificate :=
  .lucas 97 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.nil)))))))

private def primeGapCert_1_101 : PrimeCertificate :=
  .lucas 101 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.nil)))))

private def primeGapCert_1_103 : PrimeCertificate :=
  .lucas 103 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.nil))))

private def primeGapCert_1_107 : PrimeCertificate :=
  .lucas 107 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_53 (.nil)))

private def primeGapCert_1_109 : PrimeCertificate :=
  .lucas 109 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.nil))))))

private def primeGapCert_1_113 : PrimeCertificate :=
  .lucas 113 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.nil))))))

private def primeGapCert_1_127 : PrimeCertificate :=
  .lucas 127 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.nil)))))

private def primeGapCert_1_131 : PrimeCertificate :=
  .lucas 131 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.nil))))

private def primeGapCert_1_137 : PrimeCertificate :=
  .lucas 137 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.nil)))))

private def primeGapCert_1_139 : PrimeCertificate :=
  .lucas 139 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_23 (.nil))))

private def primeGapCert_1_149 : PrimeCertificate :=
  .lucas 149 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_37 (.nil))))

private def primeGapCert_1_151 : PrimeCertificate :=
  .lucas 151 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.nil)))))

private def primeGapCert_1_157 : PrimeCertificate :=
  .lucas 157 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.nil)))))

private def primeGapCert_1_163 : PrimeCertificate :=
  .lucas 163 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.nil))))))

private def primeGapCert_1_167 : PrimeCertificate :=
  .lucas 167 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_83 (.nil)))

private def primeGapCert_1_173 : PrimeCertificate :=
  .lucas 173 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_43 (.nil))))

private def primeGapCert_1_179 : PrimeCertificate :=
  .lucas 179 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_89 (.nil)))

private def primeGapCert_1_181 : PrimeCertificate :=
  .lucas 181 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.nil))))))

private def primeGapCert_1_191 : PrimeCertificate :=
  .lucas 191 19 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_19 (.nil))))

private def primeGapCert_1_193 : PrimeCertificate :=
  .lucas 193 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.nil))))))))

private def primeGapCert_1_197 : PrimeCertificate :=
  .lucas 197 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.nil)))))

private def primeGapCert_1_199 : PrimeCertificate :=
  .lucas 199 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.nil)))))

private def primeGapCert_1_211 : PrimeCertificate :=
  .lucas 211 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.nil)))))

private def primeGapCert_1_223 : PrimeCertificate :=
  .lucas 223 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_37 (.nil))))

private def primeGapCert_1_227 : PrimeCertificate :=
  .lucas 227 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_113 (.nil)))

private def primeGapCert_1_229 : PrimeCertificate :=
  .lucas 229 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_19 (.nil)))))

private def primeGapCert_1_233 : PrimeCertificate :=
  .lucas 233 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_29 (.nil)))))

private def primeGapCert_1_239 : PrimeCertificate :=
  .lucas 239 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_17 (.nil))))

private def primeGapCert_1_241 : PrimeCertificate :=
  .lucas 241 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.nil)))))))

private def primeGapCert_1_251 : PrimeCertificate :=
  .lucas 251 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.nil)))))

private def primeGapCert_1_257 : PrimeCertificate :=
  .lucas 257 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.nil)))))))))

private def primeGapCert_1_263 : PrimeCertificate :=
  .lucas 263 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_131 (.nil)))

private def primeGapCert_1_269 : PrimeCertificate :=
  .lucas 269 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_67 (.nil))))

private def primeGapCert_1_271 : PrimeCertificate :=
  .lucas 271 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.nil))))))

private def primeGapCert_1_277 : PrimeCertificate :=
  .lucas 277 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_23 (.nil)))))

private def primeGapCert_1_281 : PrimeCertificate :=
  .lucas 281 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.nil))))))

private def primeGapCert_1_283 : PrimeCertificate :=
  .lucas 283 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_47 (.nil))))

private def primeGapCert_1_293 : PrimeCertificate :=
  .lucas 293 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_73 (.nil))))

private def primeGapCert_1_307 : PrimeCertificate :=
  .lucas 307 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.nil)))))

private def primeGapCert_1_311 : PrimeCertificate :=
  .lucas 311 17 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_31 (.nil))))

private def primeGapCert_1_313 : PrimeCertificate :=
  .lucas 313 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.nil))))))

private def primeGapCert_1_331 : PrimeCertificate :=
  .lucas 331 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.nil)))))

private def primeGapCert_1_337 : PrimeCertificate :=
  .lucas 337 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.nil)))))))

private def primeGapCert_1_347 : PrimeCertificate :=
  .lucas 347 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_173 (.nil)))

private def primeGapCert_1_349 : PrimeCertificate :=
  .lucas 349 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_29 (.nil)))))

private def primeGapCert_1_353 : PrimeCertificate :=
  .lucas 353 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.nil)))))))

private def primeGapCert_1_359 : PrimeCertificate :=
  .lucas 359 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_179 (.nil)))

private def primeGapCert_1_367 : PrimeCertificate :=
  .lucas 367 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_61 (.nil))))

private def primeGapCert_1_373 : PrimeCertificate :=
  .lucas 373 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_31 (.nil)))))

private def primeGapCert_1_379 : PrimeCertificate :=
  .lucas 379 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.nil))))))

private def primeGapCert_1_383 : PrimeCertificate :=
  .lucas 383 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_191 (.nil)))

private def primeGapCert_1_389 : PrimeCertificate :=
  .lucas 389 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_97 (.nil))))

private def primeGapCert_1_397 : PrimeCertificate :=
  .lucas 397 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.nil))))))

private def primeGapCert_1_401 : PrimeCertificate :=
  .lucas 401 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.nil)))))))

private def primeGapCert_1_409 : PrimeCertificate :=
  .lucas 409 21 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.nil))))))

private def primeGapCert_1_419 : PrimeCertificate :=
  .lucas 419 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_19 (.nil))))

private def primeGapCert_1_421 : PrimeCertificate :=
  .lucas 421 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.nil))))))

private def primeGapCert_1_431 : PrimeCertificate :=
  .lucas 431 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_43 (.nil))))

private def primeGapCert_1_433 : PrimeCertificate :=
  .lucas 433 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.nil))))))))

private def primeGapCert_1_439 : PrimeCertificate :=
  .lucas 439 15 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_73 (.nil))))

private def primeGapCert_1_443 : PrimeCertificate :=
  .lucas 443 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_17 (.nil))))

private def primeGapCert_1_449 : PrimeCertificate :=
  .lucas 449 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.nil))))))))

private def primeGapCert_1_457 : PrimeCertificate :=
  .lucas 457 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_19 (.nil))))))

private def primeGapCert_1_461 : PrimeCertificate :=
  .lucas 461 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_23 (.nil)))))

private def primeGapCert_1_463 : PrimeCertificate :=
  .lucas 463 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_11 (.nil)))))

private def primeGapCert_1_467 : PrimeCertificate :=
  .lucas 467 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_233 (.nil)))

private def primeGapCert_1_479 : PrimeCertificate :=
  .lucas 479 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_239 (.nil)))

private def primeGapCert_1_487 : PrimeCertificate :=
  .lucas 487 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.nil)))))))

private def primeGapCert_1_503 : PrimeCertificate :=
  .lucas 503 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_251 (.nil)))

private def primeGapCert_1_509 : PrimeCertificate :=
  .lucas 509 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_127 (.nil))))

private def primeGapCert_1_521 : PrimeCertificate :=
  .lucas 521 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.nil))))))

private def primeGapCert_1_523 : PrimeCertificate :=
  .lucas 523 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_29 (.nil)))))

private def primeGapCert_1_541 : PrimeCertificate :=
  .lucas 541 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.nil)))))))

private def primeGapCert_1_547 : PrimeCertificate :=
  .lucas 547 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_13 (.nil)))))

private def primeGapCert_1_557 : PrimeCertificate :=
  .lucas 557 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_139 (.nil))))

private def primeGapCert_1_563 : PrimeCertificate :=
  .lucas 563 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_281 (.nil)))

private def primeGapCert_1_569 : PrimeCertificate :=
  .lucas 569 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_71 (.nil)))))

private def primeGapCert_1_593 : PrimeCertificate :=
  .lucas 593 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_37 (.nil))))))

private def primeGapCert_1_599 : PrimeCertificate :=
  .lucas 599 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_23 (.nil))))

private def primeGapCert_1_607 : PrimeCertificate :=
  .lucas 607 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_101 (.nil))))

private def primeGapCert_1_619 : PrimeCertificate :=
  .lucas 619 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_103 (.nil))))

private def primeGapCert_1_631 : PrimeCertificate :=
  .lucas 631 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.nil))))))

private def primeGapCert_1_641 : PrimeCertificate :=
  .lucas 641 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.nil)))))))))

private def primeGapCert_1_653 : PrimeCertificate :=
  .lucas 653 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_163 (.nil))))

private def primeGapCert_1_659 : PrimeCertificate :=
  .lucas 659 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_47 (.nil))))

private def primeGapCert_1_661 : PrimeCertificate :=
  .lucas 661 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.nil))))))

private def primeGapCert_1_673 : PrimeCertificate :=
  .lucas 673 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.nil))))))))

private def primeGapCert_1_683 : PrimeCertificate :=
  .lucas 683 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_31 (.nil))))

private def primeGapCert_1_701 : PrimeCertificate :=
  .lucas 701 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.nil))))))

private def primeGapCert_1_719 : PrimeCertificate :=
  .lucas 719 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_359 (.nil)))

private def primeGapCert_1_727 : PrimeCertificate :=
  .lucas 727 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_11 (.nil)))))

private def primeGapCert_1_733 : PrimeCertificate :=
  .lucas 733 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_61 (.nil)))))

private def primeGapCert_1_743 : PrimeCertificate :=
  .lucas 743 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_53 (.nil))))

private def primeGapCert_1_751 : PrimeCertificate :=
  .lucas 751 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.nil))))))

private def primeGapCert_1_761 : PrimeCertificate :=
  .lucas 761 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_19 (.nil))))))

private def primeGapCert_1_773 : PrimeCertificate :=
  .lucas 773 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_193 (.nil))))

private def primeGapCert_1_787 : PrimeCertificate :=
  .lucas 787 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_131 (.nil))))

private def primeGapCert_1_797 : PrimeCertificate :=
  .lucas 797 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_199 (.nil))))

private def primeGapCert_1_823 : PrimeCertificate :=
  .lucas 823 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_137 (.nil))))

private def primeGapCert_1_839 : PrimeCertificate :=
  .lucas 839 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_419 (.nil)))

private def primeGapCert_1_863 : PrimeCertificate :=
  .lucas 863 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_431 (.nil)))

private def primeGapCert_1_881 : PrimeCertificate :=
  .lucas 881 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.nil)))))))

private def primeGapCert_1_919 : PrimeCertificate :=
  .lucas 919 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.nil))))))

private def primeGapCert_1_941 : PrimeCertificate :=
  .lucas 941 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_47 (.nil)))))

private def primeGapCert_1_953 : PrimeCertificate :=
  .lucas 953 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_17 (.nil))))))

private def primeGapCert_1_967 : PrimeCertificate :=
  .lucas 967 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_23 (.nil)))))

private def primeGapCert_1_971 : PrimeCertificate :=
  .lucas 971 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_97 (.nil))))

private def primeGapCert_1_1013 : PrimeCertificate :=
  .lucas 1013 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_23 (.nil)))))

private def primeGapCert_1_1019 : PrimeCertificate :=
  .lucas 1019 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_509 (.nil)))

private def primeGapCert_1_1031 : PrimeCertificate :=
  .lucas 1031 14 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_103 (.nil))))

private def primeGapCert_1_1049 : PrimeCertificate :=
  .lucas 1049 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_131 (.nil)))))

private def primeGapCert_1_1063 : PrimeCertificate :=
  .lucas 1063 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_59 (.nil)))))

private def primeGapCert_1_1087 : PrimeCertificate :=
  .lucas 1087 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_181 (.nil))))

private def primeGapCert_1_1091 : PrimeCertificate :=
  .lucas 1091 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_109 (.nil))))

private def primeGapCert_1_1093 : PrimeCertificate :=
  .lucas 1093 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_13 (.nil))))))

private def primeGapCert_1_1097 : PrimeCertificate :=
  .lucas 1097 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_137 (.nil)))))

private def primeGapCert_1_1109 : PrimeCertificate :=
  .lucas 1109 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_277 (.nil))))

private def primeGapCert_1_1129 : PrimeCertificate :=
  .lucas 1129 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_47 (.nil))))))

private def primeGapCert_1_1181 : PrimeCertificate :=
  .lucas 1181 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_59 (.nil)))))

private def primeGapCert_1_1193 : PrimeCertificate :=
  .lucas 1193 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_149 (.nil)))))

private def primeGapCert_1_1201 : PrimeCertificate :=
  .lucas 1201 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.nil))))))))

private def primeGapCert_1_1229 : PrimeCertificate :=
  .lucas 1229 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_307 (.nil))))

private def primeGapCert_1_1249 : PrimeCertificate :=
  .lucas 1249 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.nil))))))))

private def primeGapCert_1_1259 : PrimeCertificate :=
  .lucas 1259 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_37 (.nil))))

private def primeGapCert_1_1283 : PrimeCertificate :=
  .lucas 1283 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_641 (.nil)))

private def primeGapCert_1_1301 : PrimeCertificate :=
  .lucas 1301 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.nil))))))

private def primeGapCert_1_1303 : PrimeCertificate :=
  .lucas 1303 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_31 (.nil)))))

private def primeGapCert_1_1327 : PrimeCertificate :=
  .lucas 1327 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_17 (.nil)))))

private def primeGapCert_1_1361 : PrimeCertificate :=
  .lucas 1361 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_17 (.nil)))))))

private def primeGapCert_1_1367 : PrimeCertificate :=
  .lucas 1367 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_683 (.nil)))

private def primeGapCert_1_1373 : PrimeCertificate :=
  .lucas 1373 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.nil))))))

private def primeGapCert_1_1381 : PrimeCertificate :=
  .lucas 1381 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_23 (.nil))))))

private def primeGapCert_1_1429 : PrimeCertificate :=
  .lucas 1429 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_17 (.nil))))))

private def primeGapCert_1_1439 : PrimeCertificate :=
  .lucas 1439 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_719 (.nil)))

private def primeGapCert_1_1451 : PrimeCertificate :=
  .lucas 1451 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_29 (.nil)))))

private def primeGapCert_1_1459 : PrimeCertificate :=
  .lucas 1459 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.nil))))))))

private def primeGapCert_1_1493 : PrimeCertificate :=
  .lucas 1493 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_373 (.nil))))

private def primeGapCert_1_1511 : PrimeCertificate :=
  .lucas 1511 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_151 (.nil))))

private def primeGapCert_1_1531 : PrimeCertificate :=
  .lucas 1531 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_17 (.nil))))))

private def primeGapCert_1_1543 : PrimeCertificate :=
  .lucas 1543 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_257 (.nil))))

private def primeGapCert_1_1567 : PrimeCertificate :=
  .lucas 1567 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_29 (.nil))))))

private def primeGapCert_1_1579 : PrimeCertificate :=
  .lucas 1579 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_263 (.nil))))

private def primeGapCert_1_1583 : PrimeCertificate :=
  .lucas 1583 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_113 (.nil))))

private def primeGapCert_1_1601 : PrimeCertificate :=
  .lucas 1601 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.nil)))))))))

private def primeGapCert_1_1627 : PrimeCertificate :=
  .lucas 1627 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_271 (.nil))))

private def primeGapCert_1_1657 : PrimeCertificate :=
  .lucas 1657 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_23 (.nil)))))))

private def primeGapCert_1_1669 : PrimeCertificate :=
  .lucas 1669 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_139 (.nil)))))

private def primeGapCert_1_1693 : PrimeCertificate :=
  .lucas 1693 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_47 (.nil))))))

private def primeGapCert_1_1699 : PrimeCertificate :=
  .lucas 1699 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_283 (.nil))))

private def primeGapCert_1_1721 : PrimeCertificate :=
  .lucas 1721 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_43 (.nil))))))

private def primeGapCert_1_1733 : PrimeCertificate :=
  .lucas 1733 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_433 (.nil))))

private def primeGapCert_1_1753 : PrimeCertificate :=
  .lucas 1753 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_73 (.nil))))))

private def primeGapCert_1_1759 : PrimeCertificate :=
  .lucas 1759 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_293 (.nil))))

private def primeGapCert_1_1787 : PrimeCertificate :=
  .lucas 1787 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_19 (.cons primeGapCert_1_47 (.nil))))

private def primeGapCert_1_1879 : PrimeCertificate :=
  .lucas 1879 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_313 (.nil))))

private def primeGapCert_1_1907 : PrimeCertificate :=
  .lucas 1907 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_953 (.nil)))

private def primeGapCert_1_1973 : PrimeCertificate :=
  .lucas 1973 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_29 (.nil)))))

private def primeGapCert_1_1987 : PrimeCertificate :=
  .lucas 1987 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_331 (.nil))))

private def primeGapCert_1_2017 : PrimeCertificate :=
  .lucas 2017 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.nil)))))))))

private def primeGapCert_1_2027 : PrimeCertificate :=
  .lucas 2027 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1013 (.nil)))

private def primeGapCert_1_2063 : PrimeCertificate :=
  .lucas 2063 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1031 (.nil)))

private def primeGapCert_1_2069 : PrimeCertificate :=
  .lucas 2069 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_47 (.nil)))))

private def primeGapCert_1_2081 : PrimeCertificate :=
  .lucas 2081 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.nil))))))))

private def primeGapCert_1_2099 : PrimeCertificate :=
  .lucas 2099 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1049 (.nil)))

private def primeGapCert_1_2143 : PrimeCertificate :=
  .lucas 2143 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_17 (.nil))))))

private def primeGapCert_1_2213 : PrimeCertificate :=
  .lucas 2213 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_79 (.nil)))))

private def primeGapCert_1_2237 : PrimeCertificate :=
  .lucas 2237 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_43 (.nil)))))

private def primeGapCert_1_2243 : PrimeCertificate :=
  .lucas 2243 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_19 (.cons primeGapCert_1_59 (.nil))))

private def primeGapCert_1_2339 : PrimeCertificate :=
  .lucas 2339 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_167 (.nil))))

private def primeGapCert_1_2357 : PrimeCertificate :=
  .lucas 2357 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_19 (.cons primeGapCert_1_31 (.nil)))))

private def primeGapCert_1_2371 : PrimeCertificate :=
  .lucas 2371 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_79 (.nil)))))

private def primeGapCert_1_2383 : PrimeCertificate :=
  .lucas 2383 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_397 (.nil))))

private def primeGapCert_1_2399 : PrimeCertificate :=
  .lucas 2399 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_109 (.nil))))

private def primeGapCert_1_2417 : PrimeCertificate :=
  .lucas 2417 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_151 (.nil))))))

private def primeGapCert_1_2441 : PrimeCertificate :=
  .lucas 2441 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_61 (.nil))))))

private def primeGapCert_1_2459 : PrimeCertificate :=
  .lucas 2459 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1229 (.nil)))

private def primeGapCert_1_2467 : PrimeCertificate :=
  .lucas 2467 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_137 (.nil)))))

private def primeGapCert_1_2617 : PrimeCertificate :=
  .lucas 2617 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_109 (.nil))))))

private def primeGapCert_1_2693 : PrimeCertificate :=
  .lucas 2693 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_673 (.nil))))

private def primeGapCert_1_2729 : PrimeCertificate :=
  .lucas 2729 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_31 (.nil))))))

private def primeGapCert_1_2741 : PrimeCertificate :=
  .lucas 2741 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_137 (.nil)))))

private def primeGapCert_1_2753 : PrimeCertificate :=
  .lucas 2753 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_43 (.nil))))))))

private def primeGapCert_1_2791 : PrimeCertificate :=
  .lucas 2791 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_31 (.nil))))))

private def primeGapCert_1_2801 : PrimeCertificate :=
  .lucas 2801 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.nil))))))))

private def primeGapCert_1_2861 : PrimeCertificate :=
  .lucas 2861 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_13 (.nil))))))

private def primeGapCert_1_2879 : PrimeCertificate :=
  .lucas 2879 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1439 (.nil)))

private def primeGapCert_1_2939 : PrimeCertificate :=
  .lucas 2939 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_113 (.nil))))

private def primeGapCert_1_2971 : PrimeCertificate :=
  .lucas 2971 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.nil)))))))

private def primeGapCert_1_3109 : PrimeCertificate :=
  .lucas 3109 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_37 (.nil))))))

private def primeGapCert_1_3137 : PrimeCertificate :=
  .lucas 3137 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.nil)))))))))

private def primeGapCert_1_3203 : PrimeCertificate :=
  .lucas 3203 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1601 (.nil)))

private def primeGapCert_1_3253 : PrimeCertificate :=
  .lucas 3253 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_271 (.nil)))))

private def primeGapCert_1_3301 : PrimeCertificate :=
  .lucas 3301 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.nil)))))))

private def primeGapCert_1_3307 : PrimeCertificate :=
  .lucas 3307 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_19 (.cons primeGapCert_1_29 (.nil)))))

private def primeGapCert_1_3329 : PrimeCertificate :=
  .lucas 3329 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.nil))))))))))

private def primeGapCert_1_3347 : PrimeCertificate :=
  .lucas 3347 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_239 (.nil))))

private def primeGapCert_1_3407 : PrimeCertificate :=
  .lucas 3407 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_131 (.nil))))

private def primeGapCert_1_3457 : PrimeCertificate :=
  .lucas 3457 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.nil)))))))))))

private def primeGapCert_1_3461 : PrimeCertificate :=
  .lucas 3461 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_173 (.nil)))))

private def primeGapCert_1_3557 : PrimeCertificate :=
  .lucas 3557 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_127 (.nil)))))

private def primeGapCert_1_3559 : PrimeCertificate :=
  .lucas 3559 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_593 (.nil))))

private def primeGapCert_1_3593 : PrimeCertificate :=
  .lucas 3593 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_449 (.nil)))))

private def primeGapCert_1_3673 : PrimeCertificate :=
  .lucas 3673 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.nil))))))))

private def primeGapCert_1_3691 : PrimeCertificate :=
  .lucas 3691 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_41 (.nil))))))

private def primeGapCert_1_3761 : PrimeCertificate :=
  .lucas 3761 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_47 (.nil)))))))

private def primeGapCert_1_3823 : PrimeCertificate :=
  .lucas 3823 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_13 (.nil))))))

private def primeGapCert_1_3907 : PrimeCertificate :=
  .lucas 3907 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_31 (.nil))))))

private def primeGapCert_1_3931 : PrimeCertificate :=
  .lucas 3931 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_131 (.nil)))))

private def primeGapCert_1_4013 : PrimeCertificate :=
  .lucas 4013 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_59 (.nil)))))

private def primeGapCert_1_4051 : PrimeCertificate :=
  .lucas 4051 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.nil))))))))

private def primeGapCert_1_4073 : PrimeCertificate :=
  .lucas 4073 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_509 (.nil)))))

private def primeGapCert_1_4099 : PrimeCertificate :=
  .lucas 4099 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_683 (.nil))))

private def primeGapCert_1_4177 : PrimeCertificate :=
  .lucas 4177 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_29 (.nil))))))))

private def primeGapCert_1_4201 : PrimeCertificate :=
  .lucas 4201 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.nil))))))))

private def primeGapCert_1_4211 : PrimeCertificate :=
  .lucas 4211 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_421 (.nil))))

private def primeGapCert_1_4229 : PrimeCertificate :=
  .lucas 4229 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_151 (.nil)))))

private def primeGapCert_1_4243 : PrimeCertificate :=
  .lucas 4243 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_101 (.nil)))))

private def primeGapCert_1_4253 : PrimeCertificate :=
  .lucas 4253 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1063 (.nil))))

private def primeGapCert_1_4339 : PrimeCertificate :=
  .lucas 4339 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_241 (.nil)))))

private def primeGapCert_1_4349 : PrimeCertificate :=
  .lucas 4349 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1087 (.nil))))

private def primeGapCert_1_4373 : PrimeCertificate :=
  .lucas 4373 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1093 (.nil))))

private def primeGapCert_1_4391 : PrimeCertificate :=
  .lucas 4391 14 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_439 (.nil))))

private def primeGapCert_1_4457 : PrimeCertificate :=
  .lucas 4457 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_557 (.nil)))))

private def primeGapCert_1_4517 : PrimeCertificate :=
  .lucas 4517 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1129 (.nil))))

private def primeGapCert_1_4561 : PrimeCertificate :=
  .lucas 4561 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_19 (.nil))))))))

private def primeGapCert_1_4729 : PrimeCertificate :=
  .lucas 4729 17 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_197 (.nil))))))

private def primeGapCert_1_4793 : PrimeCertificate :=
  .lucas 4793 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_599 (.nil)))))

private def primeGapCert_1_4813 : PrimeCertificate :=
  .lucas 4813 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_401 (.nil)))))

private def primeGapCert_1_4909 : PrimeCertificate :=
  .lucas 4909 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_409 (.nil)))))

private def primeGapCert_1_4933 : PrimeCertificate :=
  .lucas 4933 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_137 (.nil))))))

private def primeGapCert_1_4999 : PrimeCertificate :=
  .lucas 4999 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_17 (.nil))))))

private def primeGapCert_1_5021 : PrimeCertificate :=
  .lucas 5021 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_251 (.nil)))))

private def primeGapCert_1_5051 : PrimeCertificate :=
  .lucas 5051 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_101 (.nil)))))

private def primeGapCert_1_5059 : PrimeCertificate :=
  .lucas 5059 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_281 (.nil)))))

private def primeGapCert_1_5231 : PrimeCertificate :=
  .lucas 5231 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_523 (.nil))))

private def primeGapCert_1_5387 : PrimeCertificate :=
  .lucas 5387 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2693 (.nil)))

private def primeGapCert_1_5393 : PrimeCertificate :=
  .lucas 5393 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_337 (.nil))))))

private def primeGapCert_1_5413 : PrimeCertificate :=
  .lucas 5413 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_41 (.nil))))))

private def primeGapCert_1_5483 : PrimeCertificate :=
  .lucas 5483 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2741 (.nil)))

private def primeGapCert_1_5531 : PrimeCertificate :=
  .lucas 5531 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_79 (.nil)))))

private def primeGapCert_1_5557 : PrimeCertificate :=
  .lucas 5557 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_463 (.nil)))))

private def primeGapCert_1_5563 : PrimeCertificate :=
  .lucas 5563 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_103 (.nil))))))

private def primeGapCert_1_5581 : PrimeCertificate :=
  .lucas 5581 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_31 (.nil)))))))

private def primeGapCert_1_5651 : PrimeCertificate :=
  .lucas 5651 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_113 (.nil)))))

private def primeGapCert_1_5653 : PrimeCertificate :=
  .lucas 5653 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_157 (.nil))))))

private def primeGapCert_1_5903 : PrimeCertificate :=
  .lucas 5903 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_227 (.nil))))

private def primeGapCert_1_5953 : PrimeCertificate :=
  .lucas 5953 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_31 (.nil)))))))))

private def primeGapCert_1_6113 : PrimeCertificate :=
  .lucas 6113 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_191 (.nil)))))))

private def primeGapCert_1_6257 : PrimeCertificate :=
  .lucas 6257 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_23 (.nil)))))))

private def primeGapCert_1_6353 : PrimeCertificate :=
  .lucas 6353 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_397 (.nil))))))

private def primeGapCert_1_6373 : PrimeCertificate :=
  .lucas 6373 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_59 (.nil)))))))

private def primeGapCert_1_6427 : PrimeCertificate :=
  .lucas 6427 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_17 (.nil)))))))

private def primeGapCert_1_6823 : PrimeCertificate :=
  .lucas 6823 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_379 (.nil)))))

private def primeGapCert_1_6967 : PrimeCertificate :=
  .lucas 6967 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_43 (.nil)))))))

private def primeGapCert_1_7013 : PrimeCertificate :=
  .lucas 7013 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1753 (.nil))))

private def primeGapCert_1_7283 : PrimeCertificate :=
  .lucas 7283 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_331 (.nil))))

private def primeGapCert_1_7417 : PrimeCertificate :=
  .lucas 7417 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_103 (.nil)))))))

private def primeGapCert_1_7523 : PrimeCertificate :=
  .lucas 7523 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3761 (.nil)))

private def primeGapCert_1_7583 : PrimeCertificate :=
  .lucas 7583 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_223 (.nil))))

private def primeGapCert_1_7621 : PrimeCertificate :=
  .lucas 7621 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_127 (.nil))))))

private def primeGapCert_1_7829 : PrimeCertificate :=
  .lucas 7829 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_19 (.cons primeGapCert_1_103 (.nil)))))

private def primeGapCert_1_8233 : PrimeCertificate :=
  .lucas 8233 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.nil))))))))

private def primeGapCert_1_8269 : PrimeCertificate :=
  .lucas 8269 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_53 (.nil))))))

private def primeGapCert_1_8447 : PrimeCertificate :=
  .lucas 8447 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_41 (.cons primeGapCert_1_103 (.nil))))

private def primeGapCert_1_8527 : PrimeCertificate :=
  .lucas 8527 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_29 (.nil))))))

private def primeGapCert_1_8699 : PrimeCertificate :=
  .lucas 8699 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_4349 (.nil)))

private def primeGapCert_1_8707 : PrimeCertificate :=
  .lucas 8707 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1451 (.nil))))

private def primeGapCert_1_9133 : PrimeCertificate :=
  .lucas 9133 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_761 (.nil)))))

private def primeGapCert_1_9239 : PrimeCertificate :=
  .lucas 9239 19 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31 (.cons primeGapCert_1_149 (.nil))))

private def primeGapCert_1_9473 : PrimeCertificate :=
  .lucas 9473 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_37 (.nil))))))))))

private def primeGapCert_1_9631 : PrimeCertificate :=
  .lucas 9631 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_107 (.nil))))))

private def primeGapCert_1_9719 : PrimeCertificate :=
  .lucas 9719 17 (.cons primeGapCert_1_2 (.cons primeGapCert_1_43 (.cons primeGapCert_1_113 (.nil))))

private def primeGapCert_1_9929 : PrimeCertificate :=
  .lucas 9929 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_73 (.nil))))))

private def primeGapCert_1_9941 : PrimeCertificate :=
  .lucas 9941 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_71 (.nil))))))

private def primeGapCert_1_10103 : PrimeCertificate :=
  .lucas 10103 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5051 (.nil)))

private def primeGapCert_1_10111 : PrimeCertificate :=
  .lucas 10111 12 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_337 (.nil)))))

private def primeGapCert_1_10133 : PrimeCertificate :=
  .lucas 10133 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_149 (.nil)))))

private def primeGapCert_1_10427 : PrimeCertificate :=
  .lucas 10427 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_401 (.nil))))

private def primeGapCert_1_10433 : PrimeCertificate :=
  .lucas 10433 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_163 (.nil))))))))

private def primeGapCert_1_10531 : PrimeCertificate :=
  .lucas 10531 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.nil))))))))

private def primeGapCert_1_10723 : PrimeCertificate :=
  .lucas 10723 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1787 (.nil))))

private def primeGapCert_1_10789 : PrimeCertificate :=
  .lucas 10789 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_29 (.cons primeGapCert_1_31 (.nil))))))

private def primeGapCert_1_10889 : PrimeCertificate :=
  .lucas 10889 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1361 (.nil)))))

private def primeGapCert_1_11161 : PrimeCertificate :=
  .lucas 11161 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_31 (.nil))))))))

private def primeGapCert_1_11243 : PrimeCertificate :=
  .lucas 11243 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_11 (.cons primeGapCert_1_73 (.nil)))))

private def primeGapCert_1_11299 : PrimeCertificate :=
  .lucas 11299 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_269 (.nil)))))

private def primeGapCert_1_11311 : PrimeCertificate :=
  .lucas 11311 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.cons primeGapCert_1_29 (.nil))))))

private def primeGapCert_1_11383 : PrimeCertificate :=
  .lucas 11383 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_271 (.nil)))))

private def primeGapCert_1_11633 : PrimeCertificate :=
  .lucas 11633 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_727 (.nil))))))

private def primeGapCert_1_12163 : PrimeCertificate :=
  .lucas 12163 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2027 (.nil))))

private def primeGapCert_1_12227 : PrimeCertificate :=
  .lucas 12227 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_6113 (.nil)))

private def primeGapCert_1_12241 : PrimeCertificate :=
  .lucas 12241 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_17 (.nil)))))))))

private def primeGapCert_1_12329 : PrimeCertificate :=
  .lucas 12329 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_23 (.cons primeGapCert_1_67 (.nil))))))

private def primeGapCert_1_12379 : PrimeCertificate :=
  .lucas 12379 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2063 (.nil))))

private def primeGapCert_1_12413 : PrimeCertificate :=
  .lucas 12413 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_29 (.cons primeGapCert_1_107 (.nil)))))

private def primeGapCert_1_12517 : PrimeCertificate :=
  .lucas 12517 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_149 (.nil))))))

private def primeGapCert_1_12601 : PrimeCertificate :=
  .lucas 12601 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.nil)))))))))

private def primeGapCert_1_13933 : PrimeCertificate :=
  .lucas 13933 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_43 (.nil))))))))

private def primeGapCert_1_14057 : PrimeCertificate :=
  .lucas 14057 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_251 (.nil))))))

private def primeGapCert_1_16453 : PrimeCertificate :=
  .lucas 16453 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_457 (.nil))))))

private def primeGapCert_1_16553 : PrimeCertificate :=
  .lucas 16553 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2069 (.nil)))))

private def primeGapCert_1_16747 : PrimeCertificate :=
  .lucas 16747 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2791 (.nil))))

private def primeGapCert_1_16879 : PrimeCertificate :=
  .lucas 16879 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_29 (.cons primeGapCert_1_97 (.nil)))))

private def primeGapCert_1_16931 : PrimeCertificate :=
  .lucas 16931 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_1693 (.nil))))

private def primeGapCert_1_17183 : PrimeCertificate :=
  .lucas 17183 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_11 (.cons primeGapCert_1_71 (.nil)))))

private def primeGapCert_1_17827 : PrimeCertificate :=
  .lucas 17827 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2971 (.nil))))

private def primeGapCert_1_18301 : PrimeCertificate :=
  .lucas 18301 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_61 (.nil)))))))

private def primeGapCert_1_18713 : PrimeCertificate :=
  .lucas 18713 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2339 (.nil)))))

private def primeGapCert_1_18947 : PrimeCertificate :=
  .lucas 18947 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_9473 (.nil)))

private def primeGapCert_1_19031 : PrimeCertificate :=
  .lucas 19031 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_173 (.nil)))))

private def primeGapCert_1_19183 : PrimeCertificate :=
  .lucas 19183 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_23 (.cons primeGapCert_1_139 (.nil)))))

private def primeGapCert_1_19211 : PrimeCertificate :=
  .lucas 19211 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_17 (.cons primeGapCert_1_113 (.nil)))))

private def primeGapCert_1_19709 : PrimeCertificate :=
  .lucas 19709 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_379 (.nil)))))

private def primeGapCert_1_20359 : PrimeCertificate :=
  .lucas 20359 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_29 (.nil)))))))

private def primeGapCert_1_20563 : PrimeCertificate :=
  .lucas 20563 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_23 (.cons primeGapCert_1_149 (.nil)))))

private def primeGapCert_1_21011 : PrimeCertificate :=
  .lucas 21011 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_191 (.nil)))))

private def primeGapCert_1_21143 : PrimeCertificate :=
  .lucas 21143 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_31 (.cons primeGapCert_1_31 (.nil)))))

private def primeGapCert_1_21277 : PrimeCertificate :=
  .lucas 21277 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_197 (.nil)))))))

private def primeGapCert_1_21821 : PrimeCertificate :=
  .lucas 21821 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_1091 (.nil)))))

private def primeGapCert_1_22481 : PrimeCertificate :=
  .lucas 22481 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_281 (.nil)))))))

private def primeGapCert_1_23669 : PrimeCertificate :=
  .lucas 23669 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_61 (.cons primeGapCert_1_97 (.nil)))))

private def primeGapCert_1_23747 : PrimeCertificate :=
  .lucas 23747 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31 (.cons primeGapCert_1_383 (.nil))))

private def primeGapCert_1_23911 : PrimeCertificate :=
  .lucas 23911 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_797 (.nil)))))

private def primeGapCert_1_25237 : PrimeCertificate :=
  .lucas 25237 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_701 (.nil))))))

private def primeGapCert_1_25717 : PrimeCertificate :=
  .lucas 25717 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2143 (.nil)))))

private def primeGapCert_1_25951 : PrimeCertificate :=
  .lucas 25951 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_173 (.nil))))))

private def primeGapCert_1_26777 : PrimeCertificate :=
  .lucas 26777 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3347 (.nil)))))

private def primeGapCert_1_27103 : PrimeCertificate :=
  .lucas 27103 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_4517 (.nil))))

private def primeGapCert_1_27763 : PrimeCertificate :=
  .lucas 27763 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_661 (.nil)))))

private def primeGapCert_1_28597 : PrimeCertificate :=
  .lucas 28597 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2383 (.nil)))))

private def primeGapCert_1_29327 : PrimeCertificate :=
  .lucas 29327 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_31 (.cons primeGapCert_1_43 (.nil)))))

private def primeGapCert_1_30113 : PrimeCertificate :=
  .lucas 30113 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_941 (.nil)))))))

private def primeGapCert_1_30181 : PrimeCertificate :=
  .lucas 30181 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_503 (.nil))))))

private def primeGapCert_1_31663 : PrimeCertificate :=
  .lucas 31663 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1759 (.nil)))))

private def primeGapCert_1_32323 : PrimeCertificate :=
  .lucas 32323 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5387 (.nil))))

private def primeGapCert_1_32479 : PrimeCertificate :=
  .lucas 32479 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5413 (.nil))))

private def primeGapCert_1_32531 : PrimeCertificate :=
  .lucas 32531 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_3253 (.nil))))

private def primeGapCert_1_32933 : PrimeCertificate :=
  .lucas 32933 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_8233 (.nil))))

private def primeGapCert_1_33037 : PrimeCertificate :=
  .lucas 33037 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2753 (.nil)))))

private def primeGapCert_1_33071 : PrimeCertificate :=
  .lucas 33071 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_3307 (.nil))))

private def primeGapCert_1_33479 : PrimeCertificate :=
  .lucas 33479 17 (.cons primeGapCert_1_2 (.cons primeGapCert_1_19 (.cons primeGapCert_1_881 (.nil))))

private def primeGapCert_1_34849 : PrimeCertificate :=
  .lucas 34849 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_11 (.nil))))))))))

private def primeGapCert_1_35617 : PrimeCertificate :=
  .lucas 35617 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_53 (.nil)))))))))

private def primeGapCert_1_36313 : PrimeCertificate :=
  .lucas 36313 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_89 (.nil)))))))

private def primeGapCert_1_37699 : PrimeCertificate :=
  .lucas 37699 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_61 (.cons primeGapCert_1_103 (.nil)))))

private def primeGapCert_1_39419 : PrimeCertificate :=
  .lucas 39419 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_19709 (.nil)))

private def primeGapCert_1_40063 : PrimeCertificate :=
  .lucas 40063 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_607 (.nil)))))

private def primeGapCert_1_41621 : PrimeCertificate :=
  .lucas 41621 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_2081 (.nil)))))

private def primeGapCert_1_42073 : PrimeCertificate :=
  .lucas 42073 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1753 (.nil))))))

private def primeGapCert_1_42433 : PrimeCertificate :=
  .lucas 42433 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_17 (.nil))))))))))

private def primeGapCert_1_43633 : PrimeCertificate :=
  .lucas 43633 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_101 (.nil)))))))))

private def primeGapCert_1_44293 : PrimeCertificate :=
  .lucas 44293 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3691 (.nil)))))

private def primeGapCert_1_44449 : PrimeCertificate :=
  .lucas 44449 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_463 (.nil))))))))

private def primeGapCert_1_45013 : PrimeCertificate :=
  .lucas 45013 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_11 (.cons primeGapCert_1_31 (.nil)))))))

private def primeGapCert_1_45949 : PrimeCertificate :=
  .lucas 45949 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_547 (.nil))))))

private def primeGapCert_1_46819 : PrimeCertificate :=
  .lucas 46819 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_17 (.nil))))))))

private def primeGapCert_1_47287 : PrimeCertificate :=
  .lucas 47287 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_37 (.cons primeGapCert_1_71 (.nil))))))

private def primeGapCert_1_47797 : PrimeCertificate :=
  .lucas 47797 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_569 (.nil))))))

private def primeGapCert_1_48757 : PrimeCertificate :=
  .lucas 48757 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_239 (.nil))))))

private def primeGapCert_1_49811 : PrimeCertificate :=
  .lucas 49811 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_17 (.cons primeGapCert_1_293 (.nil)))))

private def primeGapCert_1_50741 : PrimeCertificate :=
  .lucas 50741 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_43 (.cons primeGapCert_1_59 (.nil))))))

private def primeGapCert_1_52163 : PrimeCertificate :=
  .lucas 52163 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_2371 (.nil))))

private def primeGapCert_1_52571 : PrimeCertificate :=
  .lucas 52571 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_751 (.nil)))))

private def primeGapCert_1_54101 : PrimeCertificate :=
  .lucas 54101 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_541 (.nil))))))

private def primeGapCert_1_54293 : PrimeCertificate :=
  .lucas 54293 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_277 (.nil))))))

private def primeGapCert_1_55631 : PrimeCertificate :=
  .lucas 55631 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5563 (.nil))))

private def primeGapCert_1_55733 : PrimeCertificate :=
  .lucas 55733 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13933 (.nil))))

private def primeGapCert_1_57149 : PrimeCertificate :=
  .lucas 57149 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_13 (.cons primeGapCert_1_157 (.nil))))))

private def primeGapCert_1_60149 : PrimeCertificate :=
  .lucas 60149 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_1367 (.nil)))))

private def primeGapCert_1_60251 : PrimeCertificate :=
  .lucas 60251 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_241 (.nil))))))

private def primeGapCert_1_62099 : PrimeCertificate :=
  .lucas 62099 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_61 (.cons primeGapCert_1_509 (.nil))))

private def primeGapCert_1_64439 : PrimeCertificate :=
  .lucas 64439 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_29 (.cons primeGapCert_1_101 (.nil)))))

private def primeGapCert_1_64853 : PrimeCertificate :=
  .lucas 64853 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31 (.cons primeGapCert_1_523 (.nil)))))

private def primeGapCert_1_65063 : PrimeCertificate :=
  .lucas 65063 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_32531 (.nil)))

private def primeGapCert_1_66959 : PrimeCertificate :=
  .lucas 66959 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_33479 (.nil)))

private def primeGapCert_1_67169 : PrimeCertificate :=
  .lucas 67169 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2099 (.nil)))))))

private def primeGapCert_1_67559 : PrimeCertificate :=
  .lucas 67559 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_1987 (.nil))))

private def primeGapCert_1_68171 : PrimeCertificate :=
  .lucas 68171 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_17 (.cons primeGapCert_1_401 (.nil)))))

private def primeGapCert_1_69593 : PrimeCertificate :=
  .lucas 69593 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_8699 (.nil)))))

private def primeGapCert_1_70313 : PrimeCertificate :=
  .lucas 70313 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_17 (.cons primeGapCert_1_47 (.nil)))))))

private def primeGapCert_1_73751 : PrimeCertificate :=
  .lucas 73751 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_59 (.nil)))))))

private def primeGapCert_1_75503 : PrimeCertificate :=
  .lucas 75503 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_5393 (.nil))))

private def primeGapCert_1_77543 : PrimeCertificate :=
  .lucas 77543 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_137 (.cons primeGapCert_1_283 (.nil))))

private def primeGapCert_1_78233 : PrimeCertificate :=
  .lucas 78233 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_11 (.cons primeGapCert_1_127 (.nil)))))))

private def primeGapCert_1_78839 : PrimeCertificate :=
  .lucas 78839 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_39419 (.nil)))

private def primeGapCert_1_79433 : PrimeCertificate :=
  .lucas 79433 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_9929 (.nil)))))

private def primeGapCert_1_81563 : PrimeCertificate :=
  .lucas 81563 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_3137 (.nil))))

private def primeGapCert_1_83243 : PrimeCertificate :=
  .lucas 83243 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_41621 (.nil)))

private def primeGapCert_1_85691 : PrimeCertificate :=
  .lucas 85691 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_19 (.cons primeGapCert_1_41 (.nil))))))

private def primeGapCert_1_87071 : PrimeCertificate :=
  .lucas 87071 17 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_8707 (.nil))))

private def primeGapCert_1_91373 : PrimeCertificate :=
  .lucas 91373 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_53 (.cons primeGapCert_1_431 (.nil)))))

private def primeGapCert_1_91583 : PrimeCertificate :=
  .lucas 91583 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_29 (.cons primeGapCert_1_1579 (.nil))))

private def primeGapCert_1_92003 : PrimeCertificate :=
  .lucas 92003 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_157 (.cons primeGapCert_1_293 (.nil))))

private def primeGapCert_1_99623 : PrimeCertificate :=
  .lucas 99623 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_49811 (.nil)))

private def primeGapCert_1_101483 : PrimeCertificate :=
  .lucas 101483 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_50741 (.nil)))

private def primeGapCert_1_102301 : PrimeCertificate :=
  .lucas 102301 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_31 (.nil))))))))

private def primeGapCert_1_102503 : PrimeCertificate :=
  .lucas 102503 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_53 (.cons primeGapCert_1_967 (.nil))))

private def primeGapCert_1_102701 : PrimeCertificate :=
  .lucas 102701 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.cons primeGapCert_1_79 (.nil)))))))

private def primeGapCert_1_102911 : PrimeCertificate :=
  .lucas 102911 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_41 (.cons primeGapCert_1_251 (.nil)))))

private def primeGapCert_1_103099 : PrimeCertificate :=
  .lucas 103099 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17183 (.nil))))

private def primeGapCert_1_103307 : PrimeCertificate :=
  .lucas 103307 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_47 (.cons primeGapCert_1_157 (.nil)))))

private def primeGapCert_1_103511 : PrimeCertificate :=
  .lucas 103511 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_941 (.nil)))))

private def primeGapCert_1_103703 : PrimeCertificate :=
  .lucas 103703 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_19 (.cons primeGapCert_1_2729 (.nil))))

private def primeGapCert_1_103913 : PrimeCertificate :=
  .lucas 103913 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31 (.cons primeGapCert_1_419 (.nil))))))

private def primeGapCert_1_104123 : PrimeCertificate :=
  .lucas 104123 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_79 (.cons primeGapCert_1_659 (.nil))))

private def primeGapCert_1_104327 : PrimeCertificate :=
  .lucas 104327 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_52163 (.nil)))

private def primeGapCert_1_104537 : PrimeCertificate :=
  .lucas 104537 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_73 (.cons primeGapCert_1_179 (.nil))))))

private def primeGapCert_1_104743 : PrimeCertificate :=
  .lucas 104743 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_23 (.cons primeGapCert_1_23 (.nil)))))))

private def primeGapCert_1_104953 : PrimeCertificate :=
  .lucas 104953 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_4373 (.nil))))))

private def primeGapCert_1_105143 : PrimeCertificate :=
  .lucas 105143 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_52571 (.nil)))

private def primeGapCert_1_105341 : PrimeCertificate :=
  .lucas 105341 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_23 (.cons primeGapCert_1_229 (.nil))))))

private def primeGapCert_1_105541 : PrimeCertificate :=
  .lucas 105541 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_1759 (.nil))))))

private def primeGapCert_1_105751 : PrimeCertificate :=
  .lucas 105751 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_47 (.nil))))))))

private def primeGapCert_1_105953 : PrimeCertificate :=
  .lucas 105953 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_11 (.cons primeGapCert_1_43 (.nil)))))))))

private def primeGapCert_1_106163 : PrimeCertificate :=
  .lucas 106163 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7583 (.nil))))

private def primeGapCert_1_106373 : PrimeCertificate :=
  .lucas 106373 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_29 (.cons primeGapCert_1_131 (.nil))))))

private def primeGapCert_1_106543 : PrimeCertificate :=
  .lucas 106543 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1973 (.nil))))))

private def primeGapCert_1_106753 : PrimeCertificate :=
  .lucas 106753 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_139 (.nil)))))))))))

private def primeGapCert_1_106963 : PrimeCertificate :=
  .lucas 106963 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17827 (.nil))))

private def primeGapCert_1_107171 : PrimeCertificate :=
  .lucas 107171 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1531 (.nil)))))

private def primeGapCert_1_107377 : PrimeCertificate :=
  .lucas 107377 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2237 (.nil)))))))

private def primeGapCert_1_107581 : PrimeCertificate :=
  .lucas 107581 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_163 (.nil)))))))

private def primeGapCert_1_107791 : PrimeCertificate :=
  .lucas 107791 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_3593 (.nil)))))

private def primeGapCert_1_107999 : PrimeCertificate :=
  .lucas 107999 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_4909 (.nil))))

private def primeGapCert_1_108203 : PrimeCertificate :=
  .lucas 108203 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_54101 (.nil)))

private def primeGapCert_1_108413 : PrimeCertificate :=
  .lucas 108413 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_27103 (.nil))))

private def primeGapCert_1_108587 : PrimeCertificate :=
  .lucas 108587 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_54293 (.nil)))

private def primeGapCert_1_108793 : PrimeCertificate :=
  .lucas 108793 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1511 (.nil)))))))

private def primeGapCert_1_109001 : PrimeCertificate :=
  .lucas 109001 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_109 (.nil))))))))

private def primeGapCert_1_109211 : PrimeCertificate :=
  .lucas 109211 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_67 (.cons primeGapCert_1_163 (.nil)))))

private def primeGapCert_1_109397 : PrimeCertificate :=
  .lucas 109397 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_3907 (.nil)))))

private def primeGapCert_1_109597 : PrimeCertificate :=
  .lucas 109597 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_9133 (.nil)))))

private def primeGapCert_1_109807 : PrimeCertificate :=
  .lucas 109807 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_18301 (.nil))))

private def primeGapCert_1_110017 : PrimeCertificate :=
  .lucas 110017 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_191 (.nil))))))))))

private def primeGapCert_1_110221 : PrimeCertificate :=
  .lucas 110221 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_167 (.nil)))))))

private def primeGapCert_1_110431 : PrimeCertificate :=
  .lucas 110431 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_409 (.nil)))))))

private def primeGapCert_1_110641 : PrimeCertificate :=
  .lucas 110641 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_461 (.nil))))))))

private def primeGapCert_1_110849 : PrimeCertificate :=
  .lucas 110849 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_433 (.nil))))))))))

private def primeGapCert_1_111053 : PrimeCertificate :=
  .lucas 111053 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_27763 (.nil))))

private def primeGapCert_1_111263 : PrimeCertificate :=
  .lucas 111263 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_55631 (.nil)))

private def primeGapCert_1_111467 : PrimeCertificate :=
  .lucas 111467 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_55733 (.nil)))

private def primeGapCert_1_111667 : PrimeCertificate :=
  .lucas 111667 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_37 (.cons primeGapCert_1_503 (.nil)))))

private def primeGapCert_1_111871 : PrimeCertificate :=
  .lucas 111871 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_113 (.nil)))))))

private def primeGapCert_1_112069 : PrimeCertificate :=
  .lucas 112069 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_283 (.nil)))))))

private def primeGapCert_1_112279 : PrimeCertificate :=
  .lucas 112279 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_18713 (.nil))))

private def primeGapCert_1_112481 : PrimeCertificate :=
  .lucas 112481 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_19 (.cons primeGapCert_1_37 (.nil)))))))))

private def primeGapCert_1_112691 : PrimeCertificate :=
  .lucas 112691 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_59 (.cons primeGapCert_1_191 (.nil)))))

private def primeGapCert_1_112901 : PrimeCertificate :=
  .lucas 112901 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_1129 (.nil))))))

private def primeGapCert_1_113111 : PrimeCertificate :=
  .lucas 113111 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11311 (.nil))))

private def primeGapCert_1_113287 : PrimeCertificate :=
  .lucas 113287 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_79 (.cons primeGapCert_1_239 (.nil)))))

private def primeGapCert_1_113497 : PrimeCertificate :=
  .lucas 113497 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_4729 (.nil))))))

private def primeGapCert_1_113683 : PrimeCertificate :=
  .lucas 113683 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_18947 (.nil))))

private def primeGapCert_1_113891 : PrimeCertificate :=
  .lucas 113891 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1627 (.nil)))))

private def primeGapCert_1_114089 : PrimeCertificate :=
  .lucas 114089 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_1097 (.nil))))))

private def primeGapCert_1_114299 : PrimeCertificate :=
  .lucas 114299 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_57149 (.nil)))

private def primeGapCert_1_114493 : PrimeCertificate :=
  .lucas 114493 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_29 (.cons primeGapCert_1_47 (.nil)))))))

private def primeGapCert_1_114691 : PrimeCertificate :=
  .lucas 114691 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_3823 (.nil)))))

private def primeGapCert_1_114901 : PrimeCertificate :=
  .lucas 114901 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_383 (.nil)))))))

private def primeGapCert_1_115099 : PrimeCertificate :=
  .lucas 115099 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_19183 (.nil))))

private def primeGapCert_1_115309 : PrimeCertificate :=
  .lucas 115309 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3203 (.nil))))))

private def primeGapCert_1_115513 : PrimeCertificate :=
  .lucas 115513 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_4813 (.nil))))))

private def primeGapCert_1_115693 : PrimeCertificate :=
  .lucas 115693 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_31 (.cons primeGapCert_1_311 (.nil))))))

private def primeGapCert_1_115903 : PrimeCertificate :=
  .lucas 115903 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_47 (.cons primeGapCert_1_137 (.nil))))))

private def primeGapCert_1_116113 : PrimeCertificate :=
  .lucas 116113 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_41 (.cons primeGapCert_1_59 (.nil))))))))

private def primeGapCert_1_116293 : PrimeCertificate :=
  .lucas 116293 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_881 (.nil))))))

private def primeGapCert_1_116491 : PrimeCertificate :=
  .lucas 116491 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_353 (.nil))))))

private def primeGapCert_1_116689 : PrimeCertificate :=
  .lucas 116689 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_13 (.cons primeGapCert_1_17 (.nil)))))))))

private def primeGapCert_1_116881 : PrimeCertificate :=
  .lucas 116881 17 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_487 (.nil))))))))

private def primeGapCert_1_117071 : PrimeCertificate :=
  .lucas 117071 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_23 (.cons primeGapCert_1_509 (.nil)))))

private def primeGapCert_1_117281 : PrimeCertificate :=
  .lucas 117281 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_733 (.nil))))))))

private def primeGapCert_1_117443 : PrimeCertificate :=
  .lucas 117443 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_4517 (.nil))))

private def primeGapCert_1_117643 : PrimeCertificate :=
  .lucas 117643 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_2801 (.nil)))))

private def primeGapCert_1_117851 : PrimeCertificate :=
  .lucas 117851 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_2357 (.nil)))))

private def primeGapCert_1_118061 : PrimeCertificate :=
  .lucas 118061 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5903 (.nil)))))

private def primeGapCert_1_118259 : PrimeCertificate :=
  .lucas 118259 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_8447 (.nil))))

private def primeGapCert_1_118463 : PrimeCertificate :=
  .lucas 118463 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_61 (.cons primeGapCert_1_971 (.nil))))

private def primeGapCert_1_118673 : PrimeCertificate :=
  .lucas 118673 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7417 (.nil))))))

private def primeGapCert_1_118873 : PrimeCertificate :=
  .lucas 118873 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_127 (.nil))))))))

private def primeGapCert_1_119083 : PrimeCertificate :=
  .lucas 119083 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_89 (.cons primeGapCert_1_223 (.nil)))))

private def primeGapCert_1_119293 : PrimeCertificate :=
  .lucas 119293 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_9941 (.nil)))))

private def primeGapCert_1_119503 : PrimeCertificate :=
  .lucas 119503 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2213 (.nil))))))

private def primeGapCert_1_119701 : PrimeCertificate :=
  .lucas 119701 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_19 (.nil)))))))))

private def primeGapCert_1_119891 : PrimeCertificate :=
  .lucas 119891 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_19 (.cons primeGapCert_1_631 (.nil)))))

private def primeGapCert_1_120097 : PrimeCertificate :=
  .lucas 120097 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_139 (.nil))))))))))

private def primeGapCert_1_120299 : PrimeCertificate :=
  .lucas 120299 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_60149 (.nil)))

private def primeGapCert_1_120503 : PrimeCertificate :=
  .lucas 120503 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_60251 (.nil)))

private def primeGapCert_1_120713 : PrimeCertificate :=
  .lucas 120713 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_79 (.cons primeGapCert_1_191 (.nil))))))

private def primeGapCert_1_120919 : PrimeCertificate :=
  .lucas 120919 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_2879 (.nil)))))

private def primeGapCert_1_121123 : PrimeCertificate :=
  .lucas 121123 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2243 (.nil))))))

private def primeGapCert_1_121333 : PrimeCertificate :=
  .lucas 121333 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_10111 (.nil)))))

private def primeGapCert_1_121531 : PrimeCertificate :=
  .lucas 121531 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_4051 (.nil)))))

private def primeGapCert_1_121727 : PrimeCertificate :=
  .lucas 121727 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_11 (.cons primeGapCert_1_503 (.nil)))))

private def primeGapCert_1_121937 : PrimeCertificate :=
  .lucas 121937 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7621 (.nil))))))

private def primeGapCert_1_122147 : PrimeCertificate :=
  .lucas 122147 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_157 (.cons primeGapCert_1_389 (.nil))))

private def primeGapCert_1_122347 : PrimeCertificate :=
  .lucas 122347 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_971 (.nil))))))

private def primeGapCert_1_122557 : PrimeCertificate :=
  .lucas 122557 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1459 (.nil))))))

private def primeGapCert_1_122761 : PrimeCertificate :=
  .lucas 122761 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_31 (.nil)))))))))

private def primeGapCert_1_122971 : PrimeCertificate :=
  .lucas 122971 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_4099 (.nil)))))

private def primeGapCert_1_123169 : PrimeCertificate :=
  .lucas 123169 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1283 (.nil))))))))

private def primeGapCert_1_123379 : PrimeCertificate :=
  .lucas 123379 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_20563 (.nil))))

private def primeGapCert_1_123583 : PrimeCertificate :=
  .lucas 123583 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_43 (.cons primeGapCert_1_479 (.nil)))))

private def primeGapCert_1_123791 : PrimeCertificate :=
  .lucas 123791 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_12379 (.nil))))

private def primeGapCert_1_124001 : PrimeCertificate :=
  .lucas 124001 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_31 (.nil))))))))))

private def primeGapCert_1_124199 : PrimeCertificate :=
  .lucas 124199 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_62099 (.nil)))

private def primeGapCert_1_124367 : PrimeCertificate :=
  .lucas 124367 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_5653 (.nil))))

private def primeGapCert_1_124577 : PrimeCertificate :=
  .lucas 124577 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_229 (.nil))))))))

private def primeGapCert_1_124783 : PrimeCertificate :=
  .lucas 124783 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_2971 (.nil)))))

private def primeGapCert_1_124991 : PrimeCertificate :=
  .lucas 124991 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_29 (.cons primeGapCert_1_431 (.nil)))))

private def primeGapCert_1_125201 : PrimeCertificate :=
  .lucas 125201 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_313 (.nil))))))))

private def primeGapCert_1_125407 : PrimeCertificate :=
  .lucas 125407 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_6967 (.nil)))))

private def primeGapCert_1_125617 : PrimeCertificate :=
  .lucas 125617 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2617 (.nil)))))))

private def primeGapCert_1_125821 : PrimeCertificate :=
  .lucas 125821 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_233 (.nil))))))))

private def primeGapCert_1_126031 : PrimeCertificate :=
  .lucas 126031 12 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_4201 (.nil)))))

private def primeGapCert_1_126241 : PrimeCertificate :=
  .lucas 126241 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_263 (.nil)))))))))

private def primeGapCert_1_126443 : PrimeCertificate :=
  .lucas 126443 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_191 (.cons primeGapCert_1_331 (.nil))))

private def primeGapCert_1_126653 : PrimeCertificate :=
  .lucas 126653 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31663 (.nil))))

private def primeGapCert_1_126859 : PrimeCertificate :=
  .lucas 126859 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_21143 (.nil))))

private def primeGapCert_1_127051 : PrimeCertificate :=
  .lucas 127051 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_11 (.cons primeGapCert_1_11 (.nil))))))))

private def primeGapCert_1_127261 : PrimeCertificate :=
  .lucas 127261 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_101 (.nil))))))))

private def primeGapCert_1_127453 : PrimeCertificate :=
  .lucas 127453 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_19 (.cons primeGapCert_1_43 (.nil)))))))

private def primeGapCert_1_127663 : PrimeCertificate :=
  .lucas 127663 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_21277 (.nil))))

private def primeGapCert_1_127873 : PrimeCertificate :=
  .lucas 127873 15 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_37 (.nil))))))))))))

private def primeGapCert_1_128053 : PrimeCertificate :=
  .lucas 128053 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3557 (.nil))))))

private def primeGapCert_1_128257 : PrimeCertificate :=
  .lucas 128257 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_167 (.nil)))))))))))

private def primeGapCert_1_128467 : PrimeCertificate :=
  .lucas 128467 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_61 (.nil))))))))

private def primeGapCert_1_128677 : PrimeCertificate :=
  .lucas 128677 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_10723 (.nil)))))

private def primeGapCert_1_128879 : PrimeCertificate :=
  .lucas 128879 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_64439 (.nil)))

private def primeGapCert_1_129089 : PrimeCertificate :=
  .lucas 129089 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2017 (.nil))))))))

private def primeGapCert_1_129293 : PrimeCertificate :=
  .lucas 129293 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_32323 (.nil))))

private def primeGapCert_1_129499 : PrimeCertificate :=
  .lucas 129499 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_113 (.cons primeGapCert_1_191 (.nil)))))

private def primeGapCert_1_129707 : PrimeCertificate :=
  .lucas 129707 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_64853 (.nil)))

private def primeGapCert_1_129917 : PrimeCertificate :=
  .lucas 129917 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_32479 (.nil))))

private def primeGapCert_1_130127 : PrimeCertificate :=
  .lucas 130127 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_65063 (.nil)))

private def primeGapCert_1_130337 : PrimeCertificate :=
  .lucas 130337 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_4073 (.nil)))))))

private def primeGapCert_1_130547 : PrimeCertificate :=
  .lucas 130547 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_5021 (.nil))))

private def primeGapCert_1_130729 : PrimeCertificate :=
  .lucas 130729 29 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_419 (.nil)))))))

private def primeGapCert_1_130927 : PrimeCertificate :=
  .lucas 130927 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_21821 (.nil))))

private def primeGapCert_1_131129 : PrimeCertificate :=
  .lucas 131129 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_37 (.cons primeGapCert_1_443 (.nil))))))

private def primeGapCert_1_131321 : PrimeCertificate :=
  .lucas 131321 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_67 (.nil))))))))

private def primeGapCert_1_131519 : PrimeCertificate :=
  .lucas 131519 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_19 (.cons primeGapCert_1_3461 (.nil))))

private def primeGapCert_1_131713 : PrimeCertificate :=
  .lucas 131713 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.nil))))))))))))

private def primeGapCert_1_131909 : PrimeCertificate :=
  .lucas 131909 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_673 (.nil))))))

private def primeGapCert_1_132113 : PrimeCertificate :=
  .lucas 132113 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_23 (.cons primeGapCert_1_359 (.nil)))))))

private def primeGapCert_1_132313 : PrimeCertificate :=
  .lucas 132313 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_37 (.cons primeGapCert_1_149 (.nil)))))))

private def primeGapCert_1_132523 : PrimeCertificate :=
  .lucas 132523 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_1699 (.nil)))))

private def primeGapCert_1_132721 : PrimeCertificate :=
  .lucas 132721 22 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_79 (.nil)))))))))

private def primeGapCert_1_132929 : PrimeCertificate :=
  .lucas 132929 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31 (.cons primeGapCert_1_67 (.nil)))))))))

private def primeGapCert_1_133121 : PrimeCertificate :=
  .lucas 133121 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.nil))))))))))))))

private def primeGapCert_1_133327 : PrimeCertificate :=
  .lucas 133327 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_823 (.nil)))))))

private def primeGapCert_1_133519 : PrimeCertificate :=
  .lucas 133519 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_11 (.cons primeGapCert_1_17 (.cons primeGapCert_1_17 (.nil)))))))

private def primeGapCert_1_133723 : PrimeCertificate :=
  .lucas 133723 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_19 (.cons primeGapCert_1_23 (.nil)))))))

private def primeGapCert_1_133919 : PrimeCertificate :=
  .lucas 133919 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_66959 (.nil)))

private def primeGapCert_1_134129 : PrimeCertificate :=
  .lucas 134129 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_83 (.cons primeGapCert_1_101 (.nil)))))))

private def primeGapCert_1_134339 : PrimeCertificate :=
  .lucas 134339 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_67169 (.nil)))

private def primeGapCert_1_134513 : PrimeCertificate :=
  .lucas 134513 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1201 (.nil)))))))

private def primeGapCert_1_134707 : PrimeCertificate :=
  .lucas 134707 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_13 (.cons primeGapCert_1_157 (.nil))))))

private def primeGapCert_1_134917 : PrimeCertificate :=
  .lucas 134917 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11243 (.nil)))))

private def primeGapCert_1_135119 : PrimeCertificate :=
  .lucas 135119 17 (.cons primeGapCert_1_2 (.cons primeGapCert_1_67559 (.nil)))

private def primeGapCert_1_135329 : PrimeCertificate :=
  .lucas 135329 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_4229 (.nil)))))))

private def primeGapCert_1_135533 : PrimeCertificate :=
  .lucas 135533 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31 (.cons primeGapCert_1_1093 (.nil)))))

private def primeGapCert_1_135743 : PrimeCertificate :=
  .lucas 135743 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_67 (.cons primeGapCert_1_1013 (.nil))))

private def primeGapCert_1_135937 : PrimeCertificate :=
  .lucas 135937 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_59 (.nil))))))))))))

private def primeGapCert_1_136139 : PrimeCertificate :=
  .lucas 136139 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_43 (.cons primeGapCert_1_1583 (.nil))))

private def primeGapCert_1_136343 : PrimeCertificate :=
  .lucas 136343 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_68171 (.nil)))

private def primeGapCert_1_136547 : PrimeCertificate :=
  .lucas 136547 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_67 (.cons primeGapCert_1_1019 (.nil))))

private def primeGapCert_1_136753 : PrimeCertificate :=
  .lucas 136753 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_11 (.cons primeGapCert_1_37 (.nil)))))))))

private def primeGapCert_1_136963 : PrimeCertificate :=
  .lucas 136963 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1087 (.nil))))))

private def primeGapCert_1_137153 : PrimeCertificate :=
  .lucas 137153 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2143 (.nil))))))))

private def primeGapCert_1_137363 : PrimeCertificate :=
  .lucas 137363 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_173 (.cons primeGapCert_1_397 (.nil))))

private def primeGapCert_1_137573 : PrimeCertificate :=
  .lucas 137573 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_163 (.cons primeGapCert_1_211 (.nil)))))

private def primeGapCert_1_137777 : PrimeCertificate :=
  .lucas 137777 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_79 (.cons primeGapCert_1_109 (.nil)))))))

private def primeGapCert_1_137983 : PrimeCertificate :=
  .lucas 137983 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_29 (.cons primeGapCert_1_61 (.nil))))))

private def primeGapCert_1_138191 : PrimeCertificate :=
  .lucas 138191 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.cons primeGapCert_1_1063 (.nil)))))

private def primeGapCert_1_138401 : PrimeCertificate :=
  .lucas 138401 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_173 (.nil)))))))))

private def primeGapCert_1_138599 : PrimeCertificate :=
  .lucas 138599 23 (.cons primeGapCert_1_2 (.cons primeGapCert_1_23 (.cons primeGapCert_1_23 (.cons primeGapCert_1_131 (.nil)))))

private def primeGapCert_1_138799 : PrimeCertificate :=
  .lucas 138799 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_701 (.nil))))))

private def primeGapCert_1_138977 : PrimeCertificate :=
  .lucas 138977 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_43 (.cons primeGapCert_1_101 (.nil))))))))

private def primeGapCert_1_139187 : PrimeCertificate :=
  .lucas 139187 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_69593 (.nil)))

private def primeGapCert_1_139397 : PrimeCertificate :=
  .lucas 139397 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_34849 (.nil))))

private def primeGapCert_1_139597 : PrimeCertificate :=
  .lucas 139597 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11633 (.nil)))))

private def primeGapCert_1_139801 : PrimeCertificate :=
  .lucas 139801 19 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_233 (.nil))))))))

private def primeGapCert_1_140009 : PrimeCertificate :=
  .lucas 140009 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_37 (.cons primeGapCert_1_43 (.nil)))))))

private def primeGapCert_1_140207 : PrimeCertificate :=
  .lucas 140207 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_6373 (.nil))))

private def primeGapCert_1_140417 : PrimeCertificate :=
  .lucas 140417 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_1097 (.nil)))))))))

private def primeGapCert_1_140627 : PrimeCertificate :=
  .lucas 140627 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_70313 (.nil)))

private def primeGapCert_1_140837 : PrimeCertificate :=
  .lucas 140837 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_137 (.cons primeGapCert_1_257 (.nil)))))

private def primeGapCert_1_141041 : PrimeCertificate :=
  .lucas 141041 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_41 (.cons primeGapCert_1_43 (.nil))))))))

private def primeGapCert_1_141241 : PrimeCertificate :=
  .lucas 141241 19 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_107 (.nil))))))))

private def primeGapCert_1_141443 : PrimeCertificate :=
  .lucas 141443 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_10103 (.nil))))

private def primeGapCert_1_141653 : PrimeCertificate :=
  .lucas 141653 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_5059 (.nil)))))

private def primeGapCert_1_141863 : PrimeCertificate :=
  .lucas 141863 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_10133 (.nil))))

private def primeGapCert_1_142067 : PrimeCertificate :=
  .lucas 142067 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_251 (.cons primeGapCert_1_283 (.nil))))

private def primeGapCert_1_142271 : PrimeCertificate :=
  .lucas 142271 23 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_41 (.cons primeGapCert_1_347 (.nil)))))

private def primeGapCert_1_142469 : PrimeCertificate :=
  .lucas 142469 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_35617 (.nil))))

private def primeGapCert_1_142673 : PrimeCertificate :=
  .lucas 142673 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_37 (.cons primeGapCert_1_241 (.nil)))))))

private def primeGapCert_1_142873 : PrimeCertificate :=
  .lucas 142873 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5953 (.nil))))))

private def primeGapCert_1_143063 : PrimeCertificate :=
  .lucas 143063 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_233 (.cons primeGapCert_1_307 (.nil))))

private def primeGapCert_1_143263 : PrimeCertificate :=
  .lucas 143263 29 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_379 (.nil)))))))

private def primeGapCert_1_143467 : PrimeCertificate :=
  .lucas 143467 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_23911 (.nil))))

private def primeGapCert_1_143677 : PrimeCertificate :=
  .lucas 143677 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_307 (.nil)))))))

private def primeGapCert_1_143881 : PrimeCertificate :=
  .lucas 143881 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_109 (.nil))))))))

private def primeGapCert_1_144073 : PrimeCertificate :=
  .lucas 144073 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_23 (.cons primeGapCert_1_29 (.nil)))))))))

private def primeGapCert_1_144271 : PrimeCertificate :=
  .lucas 144271 12 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_229 (.nil)))))))

private def primeGapCert_1_144481 : PrimeCertificate :=
  .lucas 144481 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_43 (.nil))))))))))

private def primeGapCert_1_144671 : PrimeCertificate :=
  .lucas 144671 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_17 (.cons primeGapCert_1_23 (.cons primeGapCert_1_37 (.nil))))))

private def primeGapCert_1_144847 : PrimeCertificate :=
  .lucas 144847 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_619 (.nil))))))

private def primeGapCert_1_145043 : PrimeCertificate :=
  .lucas 145043 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_47 (.cons primeGapCert_1_1543 (.nil))))

private def primeGapCert_1_145253 : PrimeCertificate :=
  .lucas 145253 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_36313 (.nil))))

private def primeGapCert_1_145463 : PrimeCertificate :=
  .lucas 145463 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_257 (.cons primeGapCert_1_283 (.nil))))

private def primeGapCert_1_145661 : PrimeCertificate :=
  .lucas 145661 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7283 (.nil)))))

private def primeGapCert_1_145861 : PrimeCertificate :=
  .lucas 145861 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_13 (.cons primeGapCert_1_17 (.nil))))))))

private def primeGapCert_1_146063 : PrimeCertificate :=
  .lucas 146063 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_10433 (.nil))))

private def primeGapCert_1_146273 : PrimeCertificate :=
  .lucas 146273 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_653 (.nil))))))))

private def primeGapCert_1_146477 : PrimeCertificate :=
  .lucas 146477 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_3329 (.nil)))))

private def primeGapCert_1_146683 : PrimeCertificate :=
  .lucas 146683 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_29 (.cons primeGapCert_1_281 (.nil))))))

private def primeGapCert_1_146893 : PrimeCertificate :=
  .lucas 146893 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_12241 (.nil)))))

private def primeGapCert_1_147097 : PrimeCertificate :=
  .lucas 147097 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_227 (.nil)))))))))

private def primeGapCert_1_147299 : PrimeCertificate :=
  .lucas 147299 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_47 (.cons primeGapCert_1_1567 (.nil))))

private def primeGapCert_1_147503 : PrimeCertificate :=
  .lucas 147503 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_73751 (.nil)))

private def primeGapCert_1_147709 : PrimeCertificate :=
  .lucas 147709 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_373 (.nil)))))))

private def primeGapCert_1_147919 : PrimeCertificate :=
  .lucas 147919 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_89 (.cons primeGapCert_1_277 (.nil)))))

private def primeGapCert_1_148123 : PrimeCertificate :=
  .lucas 148123 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_211 (.nil)))))))

private def primeGapCert_1_148331 : PrimeCertificate :=
  .lucas 148331 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_13 (.cons primeGapCert_1_163 (.nil))))))

private def primeGapCert_1_148537 : PrimeCertificate :=
  .lucas 148537 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2063 (.nil)))))))

private def primeGapCert_1_148747 : PrimeCertificate :=
  .lucas 148747 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_1907 (.nil)))))

private def primeGapCert_1_148957 : PrimeCertificate :=
  .lucas 148957 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_12413 (.nil)))))

private def primeGapCert_1_149161 : PrimeCertificate :=
  .lucas 149161 17 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_113 (.nil))))))))

private def primeGapCert_1_149371 : PrimeCertificate :=
  .lucas 149371 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.cons primeGapCert_1_383 (.nil))))))

private def primeGapCert_1_149579 : PrimeCertificate :=
  .lucas 149579 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_13 (.cons primeGapCert_1_523 (.nil)))))

private def primeGapCert_1_149771 : PrimeCertificate :=
  .lucas 149771 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_17 (.cons primeGapCert_1_881 (.nil)))))

private def primeGapCert_1_149971 : PrimeCertificate :=
  .lucas 149971 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_4999 (.nil)))))

private def primeGapCert_1_150169 : PrimeCertificate :=
  .lucas 150169 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_6257 (.nil))))))

private def primeGapCert_1_150379 : PrimeCertificate :=
  .lucas 150379 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_71 (.cons primeGapCert_1_353 (.nil)))))

private def primeGapCert_1_150589 : PrimeCertificate :=
  .lucas 150589 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_47 (.cons primeGapCert_1_89 (.nil)))))))

private def primeGapCert_1_150797 : PrimeCertificate :=
  .lucas 150797 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_37699 (.nil))))

private def primeGapCert_1_151007 : PrimeCertificate :=
  .lucas 151007 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_75503 (.nil)))

private def primeGapCert_1_151213 : PrimeCertificate :=
  .lucas 151213 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_12601 (.nil)))))

private def primeGapCert_1_151423 : PrimeCertificate :=
  .lucas 151423 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_25237 (.nil))))

private def primeGapCert_1_151631 : PrimeCertificate :=
  .lucas 151631 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_59 (.cons primeGapCert_1_257 (.nil)))))

private def primeGapCert_1_151841 : PrimeCertificate :=
  .lucas 151841 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.cons primeGapCert_1_73 (.nil)))))))))

private def primeGapCert_1_152041 : PrimeCertificate :=
  .lucas 152041 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_181 (.nil))))))))

private def primeGapCert_1_152249 : PrimeCertificate :=
  .lucas 152249 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_19031 (.nil)))))

private def primeGapCert_1_152459 : PrimeCertificate :=
  .lucas 152459 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31 (.cons primeGapCert_1_2459 (.nil))))

private def primeGapCert_1_152657 : PrimeCertificate :=
  .lucas 152657 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_29 (.cons primeGapCert_1_47 (.nil))))))))

private def primeGapCert_1_152857 : PrimeCertificate :=
  .lucas 152857 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_193 (.nil))))))))

private def primeGapCert_1_153067 : PrimeCertificate :=
  .lucas 153067 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_97 (.cons primeGapCert_1_263 (.nil)))))

private def primeGapCert_1_153277 : PrimeCertificate :=
  .lucas 153277 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_53 (.cons primeGapCert_1_241 (.nil))))))

private def primeGapCert_1_153487 : PrimeCertificate :=
  .lucas 153487 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_8527 (.nil)))))

private def primeGapCert_1_153689 : PrimeCertificate :=
  .lucas 153689 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_19211 (.nil)))))

private def primeGapCert_1_153889 : PrimeCertificate :=
  .lucas 153889 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_229 (.nil)))))))))

private def primeGapCert_1_154097 : PrimeCertificate :=
  .lucas 154097 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_9631 (.nil))))))

private def primeGapCert_1_154303 : PrimeCertificate :=
  .lucas 154303 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_25717 (.nil))))

private def primeGapCert_1_154501 : PrimeCertificate :=
  .lucas 154501 17 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_103 (.nil))))))))

private def primeGapCert_1_154699 : PrimeCertificate :=
  .lucas 154699 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_19 (.cons primeGapCert_1_23 (.cons primeGapCert_1_59 (.nil))))))

private def primeGapCert_1_154897 : PrimeCertificate :=
  .lucas 154897 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_461 (.nil))))))))

private def primeGapCert_1_155087 : PrimeCertificate :=
  .lucas 155087 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_77543 (.nil)))

private def primeGapCert_1_155291 : PrimeCertificate :=
  .lucas 155291 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_53 (.cons primeGapCert_1_293 (.nil)))))

private def primeGapCert_1_155501 : PrimeCertificate :=
  .lucas 155501 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_311 (.nil)))))))

private def primeGapCert_1_155707 : PrimeCertificate :=
  .lucas 155707 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_25951 (.nil))))

private def primeGapCert_1_155893 : PrimeCertificate :=
  .lucas 155893 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_1181 (.nil))))))

private def primeGapCert_1_156089 : PrimeCertificate :=
  .lucas 156089 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_109 (.cons primeGapCert_1_179 (.nil))))))

private def primeGapCert_1_156269 : PrimeCertificate :=
  .lucas 156269 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_5581 (.nil)))))

private def primeGapCert_1_156467 : PrimeCertificate :=
  .lucas 156467 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_78233 (.nil)))

private def primeGapCert_1_156677 : PrimeCertificate :=
  .lucas 156677 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_23 (.cons primeGapCert_1_131 (.nil))))))

private def primeGapCert_1_156887 : PrimeCertificate :=
  .lucas 156887 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_47 (.cons primeGapCert_1_1669 (.nil))))

private def primeGapCert_1_157081 : PrimeCertificate :=
  .lucas 157081 26 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_11 (.cons primeGapCert_1_17 (.nil)))))))))

private def primeGapCert_1_157291 : PrimeCertificate :=
  .lucas 157291 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_107 (.nil)))))))

private def primeGapCert_1_157489 : PrimeCertificate :=
  .lucas 157489 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_193 (.nil))))))))

private def primeGapCert_1_157679 : PrimeCertificate :=
  .lucas 157679 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_78839 (.nil)))

private def primeGapCert_1_157889 : PrimeCertificate :=
  .lucas 157889 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2467 (.nil))))))))

private def primeGapCert_1_158077 : PrimeCertificate :=
  .lucas 158077 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_4391 (.nil))))))

private def primeGapCert_1_158269 : PrimeCertificate :=
  .lucas 158269 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_11 (.cons primeGapCert_1_109 (.nil)))))))

private def primeGapCert_1_158449 : PrimeCertificate :=
  .lucas 158449 19 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3301 (.nil)))))))

private def primeGapCert_1_158657 : PrimeCertificate :=
  .lucas 158657 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_37 (.cons primeGapCert_1_67 (.nil)))))))))

private def primeGapCert_1_158867 : PrimeCertificate :=
  .lucas 158867 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_79433 (.nil)))

private def primeGapCert_1_159073 : PrimeCertificate :=
  .lucas 159073 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1657 (.nil))))))))

private def primeGapCert_1_159233 : PrimeCertificate :=
  .lucas 159233 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_311 (.nil)))))))))))

private def primeGapCert_1_159437 : PrimeCertificate :=
  .lucas 159437 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_23 (.cons primeGapCert_1_1733 (.nil)))))

private def primeGapCert_1_159631 : PrimeCertificate :=
  .lucas 159631 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_17 (.cons primeGapCert_1_313 (.nil))))))

private def primeGapCert_1_159839 : PrimeCertificate :=
  .lucas 159839 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_233 (.nil))))))

private def primeGapCert_1_160049 : PrimeCertificate :=
  .lucas 160049 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1429 (.nil)))))))

private def primeGapCert_1_160253 : PrimeCertificate :=
  .lucas 160253 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_40063 (.nil))))

private def primeGapCert_1_160453 : PrimeCertificate :=
  .lucas 160453 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_4457 (.nil))))))

private def primeGapCert_1_160663 : PrimeCertificate :=
  .lucas 160663 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_26777 (.nil))))

private def primeGapCert_1_160861 : PrimeCertificate :=
  .lucas 160861 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_383 (.nil)))))))

private def primeGapCert_1_161071 : PrimeCertificate :=
  .lucas 161071 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_13 (.cons primeGapCert_1_59 (.nil)))))))

private def primeGapCert_1_161281 : PrimeCertificate :=
  .lucas 161281 23 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.nil))))))))))))))

private def primeGapCert_1_161471 : PrimeCertificate :=
  .lucas 161471 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_67 (.cons primeGapCert_1_241 (.nil)))))

private def primeGapCert_1_161659 : PrimeCertificate :=
  .lucas 161659 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1283 (.nil))))))

private def primeGapCert_1_161869 : PrimeCertificate :=
  .lucas 161869 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_41 (.cons primeGapCert_1_47 (.nil)))))))

private def primeGapCert_1_162079 : PrimeCertificate :=
  .lucas 162079 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_17 (.cons primeGapCert_1_227 (.nil))))))

private def primeGapCert_1_162289 : PrimeCertificate :=
  .lucas 162289 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_23 (.nil))))))))))

private def primeGapCert_1_162499 : PrimeCertificate :=
  .lucas 162499 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_53 (.cons primeGapCert_1_73 (.nil))))))

private def primeGapCert_1_162709 : PrimeCertificate :=
  .lucas 162709 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_13 (.cons primeGapCert_1_149 (.nil)))))))

private def primeGapCert_1_162917 : PrimeCertificate :=
  .lucas 162917 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_13 (.cons primeGapCert_1_241 (.nil))))))

private def primeGapCert_1_163127 : PrimeCertificate :=
  .lucas 163127 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_81563 (.nil)))

private def primeGapCert_1_163337 : PrimeCertificate :=
  .lucas 163337 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_1201 (.nil))))))

private def primeGapCert_1_163543 : PrimeCertificate :=
  .lucas 163543 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_97 (.cons primeGapCert_1_281 (.nil)))))

private def primeGapCert_1_163753 : PrimeCertificate :=
  .lucas 163753 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_6823 (.nil))))))

private def primeGapCert_1_163927 : PrimeCertificate :=
  .lucas 163927 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1301 (.nil))))))

private def primeGapCert_1_164117 : PrimeCertificate :=
  .lucas 164117 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_89 (.cons primeGapCert_1_461 (.nil)))))

private def primeGapCert_1_164321 : PrimeCertificate :=
  .lucas 164321 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.cons primeGapCert_1_79 (.nil)))))))))

private def primeGapCert_1_164531 : PrimeCertificate :=
  .lucas 164531 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_16453 (.nil))))

private def primeGapCert_1_164729 : PrimeCertificate :=
  .lucas 164729 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_59 (.cons primeGapCert_1_349 (.nil))))))

private def primeGapCert_1_164911 : PrimeCertificate :=
  .lucas 164911 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_23 (.cons primeGapCert_1_239 (.nil))))))

private def primeGapCert_1_165103 : PrimeCertificate :=
  .lucas 165103 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_3931 (.nil)))))

private def primeGapCert_1_165313 : PrimeCertificate :=
  .lucas 165313 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_41 (.nil)))))))))))

private def primeGapCert_1_165523 : PrimeCertificate :=
  .lucas 165523 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_563 (.nil))))))

private def primeGapCert_1_165721 : PrimeCertificate :=
  .lucas 165721 14 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_1381 (.nil)))))))

private def primeGapCert_1_165931 : PrimeCertificate :=
  .lucas 165931 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5531 (.nil)))))

private def primeGapCert_1_166099 : PrimeCertificate :=
  .lucas 166099 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_19 (.cons primeGapCert_1_31 (.cons primeGapCert_1_47 (.nil))))))

private def primeGapCert_1_166303 : PrimeCertificate :=
  .lucas 166303 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_9239 (.nil)))))

private def primeGapCert_1_166487 : PrimeCertificate :=
  .lucas 166487 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_83243 (.nil)))

private def primeGapCert_1_166693 : PrimeCertificate :=
  .lucas 166693 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_29 (.cons primeGapCert_1_479 (.nil))))))

private def primeGapCert_1_166871 : PrimeCertificate :=
  .lucas 166871 43 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_37 (.cons primeGapCert_1_41 (.nil))))))

private def primeGapCert_1_167081 : PrimeCertificate :=
  .lucas 167081 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_4177 (.nil))))))

private def primeGapCert_1_167269 : PrimeCertificate :=
  .lucas 167269 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_53 (.cons primeGapCert_1_263 (.nil))))))

private def primeGapCert_1_167471 : PrimeCertificate :=
  .lucas 167471 19 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_16747 (.nil))))

private def primeGapCert_1_167677 : PrimeCertificate :=
  .lucas 167677 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_89 (.cons primeGapCert_1_157 (.nil))))))

private def primeGapCert_1_167887 : PrimeCertificate :=
  .lucas 167887 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3109 (.nil))))))

private def primeGapCert_1_168089 : PrimeCertificate :=
  .lucas 168089 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_21011 (.nil)))))

private def primeGapCert_1_168293 : PrimeCertificate :=
  .lucas 168293 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_42073 (.nil))))

private def primeGapCert_1_168499 : PrimeCertificate :=
  .lucas 168499 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_23 (.cons primeGapCert_1_37 (.nil)))))))

private def primeGapCert_1_168697 : PrimeCertificate :=
  .lucas 168697 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_71 (.nil)))))))))

private def primeGapCert_1_168901 : PrimeCertificate :=
  .lucas 168901 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_563 (.nil)))))))

private def primeGapCert_1_169111 : PrimeCertificate :=
  .lucas 169111 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_1879 (.nil))))))

private def primeGapCert_1_169321 : PrimeCertificate :=
  .lucas 169321 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_17 (.cons primeGapCert_1_83 (.nil))))))))

private def primeGapCert_1_169531 : PrimeCertificate :=
  .lucas 169531 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5651 (.nil)))))

private def primeGapCert_1_169733 : PrimeCertificate :=
  .lucas 169733 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_42433 (.nil))))

private def primeGapCert_1_169943 : PrimeCertificate :=
  .lucas 169943 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31 (.cons primeGapCert_1_2741 (.nil))))

private def primeGapCert_1_170141 : PrimeCertificate :=
  .lucas 170141 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_47 (.cons primeGapCert_1_181 (.nil))))))

private def primeGapCert_1_170351 : PrimeCertificate :=
  .lucas 170351 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_3407 (.nil)))))

private def primeGapCert_1_170557 : PrimeCertificate :=
  .lucas 170557 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_61 (.cons primeGapCert_1_233 (.nil))))))

private def primeGapCert_1_170767 : PrimeCertificate :=
  .lucas 170767 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_53 (.cons primeGapCert_1_179 (.nil))))))

private def primeGapCert_1_170971 : PrimeCertificate :=
  .lucas 170971 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_41 (.cons primeGapCert_1_139 (.nil))))))

private def primeGapCert_1_171179 : PrimeCertificate :=
  .lucas 171179 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_12227 (.nil))))

private def primeGapCert_1_171383 : PrimeCertificate :=
  .lucas 171383 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_85691 (.nil)))

private def primeGapCert_1_171583 : PrimeCertificate :=
  .lucas 171583 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_28597 (.nil))))

private def primeGapCert_1_171793 : PrimeCertificate :=
  .lucas 171793 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1193 (.nil))))))))

private def primeGapCert_1_172001 : PrimeCertificate :=
  .lucas 172001 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_43 (.nil))))))))))

private def primeGapCert_1_172199 : PrimeCertificate :=
  .lucas 172199 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_37 (.cons primeGapCert_1_179 (.nil)))))

private def primeGapCert_1_172399 : PrimeCertificate :=
  .lucas 172399 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_59 (.cons primeGapCert_1_487 (.nil)))))

private def primeGapCert_1_172607 : PrimeCertificate :=
  .lucas 172607 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_12329 (.nil))))

private def primeGapCert_1_172807 : PrimeCertificate :=
  .lucas 172807 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_83 (.cons primeGapCert_1_347 (.nil)))))

private def primeGapCert_1_172999 : PrimeCertificate :=
  .lucas 172999 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1373 (.nil))))))

private def primeGapCert_1_173209 : PrimeCertificate :=
  .lucas 173209 23 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1031 (.nil)))))))

private def primeGapCert_1_173359 : PrimeCertificate :=
  .lucas 173359 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_9631 (.nil)))))

private def primeGapCert_1_173561 : PrimeCertificate :=
  .lucas 173561 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_4339 (.nil))))))

private def primeGapCert_1_173743 : PrimeCertificate :=
  .lucas 173743 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_23 (.cons primeGapCert_1_1259 (.nil)))))

private def primeGapCert_1_173933 : PrimeCertificate :=
  .lucas 173933 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_59 (.cons primeGapCert_1_67 (.nil))))))

private def primeGapCert_1_174143 : PrimeCertificate :=
  .lucas 174143 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_87071 (.nil)))

private def primeGapCert_1_174347 : PrimeCertificate :=
  .lucas 174347 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_179 (.cons primeGapCert_1_487 (.nil))))

private def primeGapCert_1_174533 : PrimeCertificate :=
  .lucas 174533 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_43633 (.nil))))

private def primeGapCert_1_174737 : PrimeCertificate :=
  .lucas 174737 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_67 (.cons primeGapCert_1_163 (.nil)))))))

private def primeGapCert_1_174943 : PrimeCertificate :=
  .lucas 174943 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_9719 (.nil)))))

private def primeGapCert_1_175141 : PrimeCertificate :=
  .lucas 175141 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_139 (.nil))))))))

private def primeGapCert_1_175349 : PrimeCertificate :=
  .lucas 175349 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_59 (.cons primeGapCert_1_743 (.nil)))))

private def primeGapCert_1_175543 : PrimeCertificate :=
  .lucas 175543 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_1721 (.nil)))))

private def primeGapCert_1_175753 : PrimeCertificate :=
  .lucas 175753 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_2441 (.nil)))))))

private def primeGapCert_1_175963 : PrimeCertificate :=
  .lucas 175963 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_29327 (.nil))))

private def primeGapCert_1_176161 : PrimeCertificate :=
  .lucas 176161 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_367 (.nil)))))))))

private def primeGapCert_1_176369 : PrimeCertificate :=
  .lucas 176369 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_73 (.cons primeGapCert_1_151 (.nil)))))))

private def primeGapCert_1_176573 : PrimeCertificate :=
  .lucas 176573 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_4013 (.nil)))))

private def primeGapCert_1_176779 : PrimeCertificate :=
  .lucas 176779 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_23 (.cons primeGapCert_1_61 (.nil)))))))

private def primeGapCert_1_176989 : PrimeCertificate :=
  .lucas 176989 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_43 (.nil))))))))

private def primeGapCert_1_177173 : PrimeCertificate :=
  .lucas 177173 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_44293 (.nil))))

private def primeGapCert_1_177383 : PrimeCertificate :=
  .lucas 177383 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31 (.cons primeGapCert_1_2861 (.nil))))

private def primeGapCert_1_177589 : PrimeCertificate :=
  .lucas 177589 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_4933 (.nil))))))

private def primeGapCert_1_177797 : PrimeCertificate :=
  .lucas 177797 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_44449 (.nil))))

private def primeGapCert_1_178001 : PrimeCertificate :=
  .lucas 178001 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_89 (.nil)))))))))

private def primeGapCert_1_178207 : PrimeCertificate :=
  .lucas 178207 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_4243 (.nil)))))

private def primeGapCert_1_178417 : PrimeCertificate :=
  .lucas 178417 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_59 (.nil))))))))))

private def primeGapCert_1_178627 : PrimeCertificate :=
  .lucas 178627 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_4253 (.nil)))))

private def primeGapCert_1_178831 : PrimeCertificate :=
  .lucas 178831 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_1987 (.nil))))))

private def primeGapCert_1_179041 : PrimeCertificate :=
  .lucas 179041 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_373 (.nil)))))))))

private def primeGapCert_1_179243 : PrimeCertificate :=
  .lucas 179243 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_7 (.cons primeGapCert_1_31 (.cons primeGapCert_1_59 (.nil))))))

private def primeGapCert_1_179453 : PrimeCertificate :=
  .lucas 179453 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_13 (.cons primeGapCert_1_17 (.cons primeGapCert_1_29 (.nil)))))))

private def primeGapCert_1_179659 : PrimeCertificate :=
  .lucas 179659 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1109 (.nil)))))))

private def primeGapCert_1_179849 : PrimeCertificate :=
  .lucas 179849 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_22481 (.nil)))))

private def primeGapCert_1_180053 : PrimeCertificate :=
  .lucas 180053 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_45013 (.nil))))

private def primeGapCert_1_180263 : PrimeCertificate :=
  .lucas 180263 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_193 (.cons primeGapCert_1_467 (.nil))))

private def primeGapCert_1_180473 : PrimeCertificate :=
  .lucas 180473 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_1327 (.nil))))))

private def primeGapCert_1_180679 : PrimeCertificate :=
  .lucas 180679 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_30113 (.nil))))

private def primeGapCert_1_180883 : PrimeCertificate :=
  .lucas 180883 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_773 (.nil))))))

private def primeGapCert_1_181087 : PrimeCertificate :=
  .lucas 181087 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_30181 (.nil))))

private def primeGapCert_1_181297 : PrimeCertificate :=
  .lucas 181297 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1259 (.nil))))))))

private def primeGapCert_1_181501 : PrimeCertificate :=
  .lucas 181501 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_11 (.nil)))))))))

private def primeGapCert_1_181711 : PrimeCertificate :=
  .lucas 181711 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_673 (.nil)))))))

private def primeGapCert_1_181919 : PrimeCertificate :=
  .lucas 181919 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11 (.cons primeGapCert_1_8269 (.nil))))

private def primeGapCert_1_182129 : PrimeCertificate :=
  .lucas 182129 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_11383 (.nil))))))

private def primeGapCert_1_182339 : PrimeCertificate :=
  .lucas 182339 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_7013 (.nil))))

private def primeGapCert_1_182549 : PrimeCertificate :=
  .lucas 182549 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_47 (.cons primeGapCert_1_971 (.nil)))))

private def primeGapCert_1_182747 : PrimeCertificate :=
  .lucas 182747 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_91373 (.nil)))

private def primeGapCert_1_182957 : PrimeCertificate :=
  .lucas 182957 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_53 (.cons primeGapCert_1_863 (.nil)))))

private def primeGapCert_1_183167 : PrimeCertificate :=
  .lucas 183167 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_91583 (.nil)))

private def primeGapCert_1_183377 : PrimeCertificate :=
  .lucas 183377 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_73 (.cons primeGapCert_1_157 (.nil)))))))

private def primeGapCert_1_183587 : PrimeCertificate :=
  .lucas 183587 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_23 (.cons primeGapCert_1_307 (.nil)))))

private def primeGapCert_1_183797 : PrimeCertificate :=
  .lucas 183797 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_45949 (.nil))))

private def primeGapCert_1_184007 : PrimeCertificate :=
  .lucas 184007 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_92003 (.nil)))

private def primeGapCert_1_184211 : PrimeCertificate :=
  .lucas 184211 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_13 (.cons primeGapCert_1_13 (.cons primeGapCert_1_109 (.nil))))))

private def primeGapCert_1_184417 : PrimeCertificate :=
  .lucas 184417 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_113 (.nil)))))))))

private def primeGapCert_1_184627 : PrimeCertificate :=
  .lucas 184627 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_263 (.nil)))))))

private def primeGapCert_1_184837 : PrimeCertificate :=
  .lucas 184837 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_73 (.cons primeGapCert_1_211 (.nil))))))

private def primeGapCert_1_185027 : PrimeCertificate :=
  .lucas 185027 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_71 (.cons primeGapCert_1_1303 (.nil))))

private def primeGapCert_1_185233 : PrimeCertificate :=
  .lucas 185233 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_227 (.nil))))))))

private def primeGapCert_1_185441 : PrimeCertificate :=
  .lucas 185441 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_19 (.cons primeGapCert_1_61 (.nil)))))))))

private def primeGapCert_1_185651 : PrimeCertificate :=
  .lucas 185651 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_47 (.cons primeGapCert_1_79 (.nil))))))

private def primeGapCert_1_185849 : PrimeCertificate :=
  .lucas 185849 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_1787 (.nil))))))

private def primeGapCert_1_186049 : PrimeCertificate :=
  .lucas 186049 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_19 (.nil)))))))))))

private def primeGapCert_1_186259 : PrimeCertificate :=
  .lucas 186259 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_37 (.cons primeGapCert_1_839 (.nil)))))

private def primeGapCert_1_186469 : PrimeCertificate :=
  .lucas 186469 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_41 (.cons primeGapCert_1_379 (.nil))))))

private def primeGapCert_1_186679 : PrimeCertificate :=
  .lucas 186679 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3457 (.nil))))))

private def primeGapCert_1_186889 : PrimeCertificate :=
  .lucas 186889 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_599 (.nil)))))))

private def primeGapCert_1_187091 : PrimeCertificate :=
  .lucas 187091 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_53 (.cons primeGapCert_1_353 (.nil)))))

private def primeGapCert_1_187277 : PrimeCertificate :=
  .lucas 187277 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_46819 (.nil))))

private def primeGapCert_1_187477 : PrimeCertificate :=
  .lucas 187477 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_919 (.nil))))))

private def primeGapCert_1_187687 : PrimeCertificate :=
  .lucas 187687 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_10427 (.nil)))))

private def primeGapCert_1_187897 : PrimeCertificate :=
  .lucas 187897 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7829 (.nil))))))

private def primeGapCert_1_188107 : PrimeCertificate :=
  .lucas 188107 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_107 (.cons primeGapCert_1_293 (.nil)))))

private def primeGapCert_1_188317 : PrimeCertificate :=
  .lucas 188317 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5231 (.nil))))))

private def primeGapCert_1_188527 : PrimeCertificate :=
  .lucas 188527 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_2417 (.nil)))))

private def primeGapCert_1_188729 : PrimeCertificate :=
  .lucas 188729 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_31 (.cons primeGapCert_1_761 (.nil))))))

private def primeGapCert_1_188939 : PrimeCertificate :=
  .lucas 188939 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_5557 (.nil))))

private def primeGapCert_1_189149 : PrimeCertificate :=
  .lucas 189149 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_47287 (.nil))))

private def primeGapCert_1_189353 : PrimeCertificate :=
  .lucas 189353 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_23669 (.nil)))))

private def primeGapCert_1_189559 : PrimeCertificate :=
  .lucas 189559 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_10531 (.nil)))))

private def primeGapCert_1_189767 : PrimeCertificate :=
  .lucas 189767 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_239 (.cons primeGapCert_1_397 (.nil))))

private def primeGapCert_1_189977 : PrimeCertificate :=
  .lucas 189977 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_23747 (.nil)))))

private def primeGapCert_1_190181 : PrimeCertificate :=
  .lucas 190181 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_37 (.cons primeGapCert_1_257 (.nil))))))

private def primeGapCert_1_190391 : PrimeCertificate :=
  .lucas 190391 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_79 (.cons primeGapCert_1_241 (.nil)))))

private def primeGapCert_1_190591 : PrimeCertificate :=
  .lucas 190591 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_6353 (.nil)))))

private def primeGapCert_1_190793 : PrimeCertificate :=
  .lucas 190793 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_3407 (.nil))))))

private def primeGapCert_1_190997 : PrimeCertificate :=
  .lucas 190997 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_3673 (.nil)))))

private def primeGapCert_1_191189 : PrimeCertificate :=
  .lucas 191189 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_47797 (.nil))))

private def primeGapCert_1_191353 : PrimeCertificate :=
  .lucas 191353 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_17 (.cons primeGapCert_1_67 (.nil))))))))

private def primeGapCert_1_191563 : PrimeCertificate :=
  .lucas 191563 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_4561 (.nil)))))

private def primeGapCert_1_191773 : PrimeCertificate :=
  .lucas 191773 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_761 (.nil)))))))

private def primeGapCert_1_191977 : PrimeCertificate :=
  .lucas 191977 10 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_19 (.cons primeGapCert_1_421 (.nil)))))))

private def primeGapCert_1_192187 : PrimeCertificate :=
  .lucas 192187 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3559 (.nil))))))

private def primeGapCert_1_192391 : PrimeCertificate :=
  .lucas 192391 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_11 (.cons primeGapCert_1_11 (.cons primeGapCert_1_53 (.nil)))))))

private def primeGapCert_1_192601 : PrimeCertificate :=
  .lucas 192601 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_107 (.nil)))))))))

private def primeGapCert_1_192811 : PrimeCertificate :=
  .lucas 192811 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_6427 (.nil)))))

private def primeGapCert_1_193013 : PrimeCertificate :=
  .lucas 193013 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_73 (.cons primeGapCert_1_661 (.nil)))))

private def primeGapCert_1_193201 : PrimeCertificate :=
  .lucas 193201 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_7 (.cons primeGapCert_1_23 (.nil))))))))))

private def primeGapCert_1_193393 : PrimeCertificate :=
  .lucas 193393 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_79 (.nil)))))))))

private def primeGapCert_1_193603 : PrimeCertificate :=
  .lucas 193603 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_41 (.cons primeGapCert_1_787 (.nil)))))

private def primeGapCert_1_193813 : PrimeCertificate :=
  .lucas 193813 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_31 (.cons primeGapCert_1_521 (.nil))))))

private def primeGapCert_1_194017 : PrimeCertificate :=
  .lucas 194017 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_43 (.cons primeGapCert_1_47 (.nil)))))))))

private def primeGapCert_1_194203 : PrimeCertificate :=
  .lucas 194203 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_10789 (.nil)))))

private def primeGapCert_1_194413 : PrimeCertificate :=
  .lucas 194413 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_17 (.cons primeGapCert_1_953 (.nil))))))

private def primeGapCert_1_194609 : PrimeCertificate :=
  .lucas 194609 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_12163 (.nil))))))

private def primeGapCert_1_194819 : PrimeCertificate :=
  .lucas 194819 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_59 (.cons primeGapCert_1_127 (.nil)))))

private def primeGapCert_1_195029 : PrimeCertificate :=
  .lucas 195029 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_48757 (.nil))))

private def primeGapCert_1_195229 : PrimeCertificate :=
  .lucas 195229 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11 (.cons primeGapCert_1_17 (.cons primeGapCert_1_29 (.nil))))))))

private def primeGapCert_1_195427 : PrimeCertificate :=
  .lucas 195427 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_11 (.cons primeGapCert_1_47 (.nil))))))))

private def primeGapCert_1_195599 : PrimeCertificate :=
  .lucas 195599 17 (.cons primeGapCert_1_2 (.cons primeGapCert_1_13 (.cons primeGapCert_1_7523 (.nil))))

private def primeGapCert_1_195809 : PrimeCertificate :=
  .lucas 195809 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_29 (.cons primeGapCert_1_211 (.nil))))))))

private def primeGapCert_1_196003 : PrimeCertificate :=
  .lucas 196003 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_10889 (.nil)))))

private def primeGapCert_1_196201 : PrimeCertificate :=
  .lucas 196201 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_5 (.cons primeGapCert_1_109 (.nil)))))))))

private def primeGapCert_1_196387 : PrimeCertificate :=
  .lucas 196387 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_71 (.cons primeGapCert_1_461 (.nil)))))

private def primeGapCert_1_196597 : PrimeCertificate :=
  .lucas 196597 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_43 (.cons primeGapCert_1_127 (.nil)))))))

private def primeGapCert_1_196799 : PrimeCertificate :=
  .lucas 196799 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_14057 (.nil))))

private def primeGapCert_1_197009 : PrimeCertificate :=
  .lucas 197009 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_1759 (.nil)))))))

private def primeGapCert_1_197207 : PrimeCertificate :=
  .lucas 197207 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_151 (.cons primeGapCert_1_653 (.nil))))

private def primeGapCert_1_197389 : PrimeCertificate :=
  .lucas 197389 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5483 (.nil))))))

private def primeGapCert_1_197599 : PrimeCertificate :=
  .lucas 197599 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_32933 (.nil))))

private def primeGapCert_1_197807 : PrimeCertificate :=
  .lucas 197807 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_71 (.cons primeGapCert_1_199 (.nil)))))

private def primeGapCert_1_198017 : PrimeCertificate :=
  .lucas 198017 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_7 (.cons primeGapCert_1_13 (.cons primeGapCert_1_17 (.nil)))))))))))

private def primeGapCert_1_198223 : PrimeCertificate :=
  .lucas 198223 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_33037 (.nil))))

private def primeGapCert_1_198427 : PrimeCertificate :=
  .lucas 198427 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_33071 (.nil))))

private def primeGapCert_1_198637 : PrimeCertificate :=
  .lucas 198637 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_16553 (.nil)))))

private def primeGapCert_1_198841 : PrimeCertificate :=
  .lucas 198841 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_5 (.cons primeGapCert_1_1657 (.nil)))))))

private def primeGapCert_1_199049 : PrimeCertificate :=
  .lucas 199049 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_139 (.cons primeGapCert_1_179 (.nil))))))

private def primeGapCert_1_199247 : PrimeCertificate :=
  .lucas 199247 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_99623 (.nil)))

private def primeGapCert_1_199457 : PrimeCertificate :=
  .lucas 199457 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_23 (.cons primeGapCert_1_271 (.nil))))))))

private def primeGapCert_1_199657 : PrimeCertificate :=
  .lucas 199657 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_47 (.cons primeGapCert_1_59 (.nil))))))))

private def primeGapCert_1_199853 : PrimeCertificate :=
  .lucas 199853 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_17 (.cons primeGapCert_1_2939 (.nil)))))

private def primeGapCert_1_200063 : PrimeCertificate :=
  .lucas 200063 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_67 (.cons primeGapCert_1_1493 (.nil))))

private def primeGapCert_1_200273 : PrimeCertificate :=
  .lucas 200273 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_12517 (.nil))))))

private def primeGapCert_1_200483 : PrimeCertificate :=
  .lucas 200483 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_59 (.cons primeGapCert_1_1699 (.nil))))

private def primeGapCert_1_200689 : PrimeCertificate :=
  .lucas 200689 7 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_37 (.cons primeGapCert_1_113 (.nil))))))))

private def primeGapCert_1_200899 : PrimeCertificate :=
  .lucas 200899 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11161 (.nil)))))

private def primeGapCert_1_201107 : PrimeCertificate :=
  .lucas 201107 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_193 (.cons primeGapCert_1_521 (.nil))))

private def primeGapCert_1_201307 : PrimeCertificate :=
  .lucas 201307 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_4793 (.nil)))))

private def primeGapCert_1_201517 : PrimeCertificate :=
  .lucas 201517 11 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_7 (.cons primeGapCert_1_2399 (.nil))))))

private def primeGapCert_1_201709 : PrimeCertificate :=
  .lucas 201709 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_13 (.cons primeGapCert_1_431 (.nil)))))))

private def primeGapCert_1_201919 : PrimeCertificate :=
  .lucas 201919 3 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_73 (.cons primeGapCert_1_461 (.nil)))))

private def primeGapCert_1_202129 : PrimeCertificate :=
  .lucas 202129 13 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_4211 (.nil)))))))

private def primeGapCert_1_202339 : PrimeCertificate :=
  .lucas 202339 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_1249 (.nil)))))))

private def primeGapCert_1_202549 : PrimeCertificate :=
  .lucas 202549 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_16879 (.nil)))))

private def primeGapCert_1_202757 : PrimeCertificate :=
  .lucas 202757 2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_173 (.cons primeGapCert_1_293 (.nil)))))

private def primeGapCert_1_202967 : PrimeCertificate :=
  .lucas 202967 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_101483 (.nil)))

private def primeGapCert_1_203173 : PrimeCertificate :=
  .lucas 203173 5 (.cons primeGapCert_1_2 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_16931 (.nil)))))

private def primeGapCert_1_203383 : PrimeCertificate :=
  .lucas 203383 6 (.cons primeGapCert_1_2 (.cons primeGapCert_1_3 (.cons primeGapCert_1_3 (.cons primeGapCert_1_11299 (.nil)))))

private def primeGapCert_1_203591 : PrimeCertificate :=
  .lucas 203591 22 (.cons primeGapCert_1_2 (.cons primeGapCert_1_5 (.cons primeGapCert_1_20359 (.nil))))

private def primeGapCertifiedCerts_1_0 : List PrimeCertificate :=
  [primeGapCert_1_102301, primeGapCert_1_102503, primeGapCert_1_102701, primeGapCert_1_102911, primeGapCert_1_103099, primeGapCert_1_103307, primeGapCert_1_103511, primeGapCert_1_103703, primeGapCert_1_103913, primeGapCert_1_104123, primeGapCert_1_104327, primeGapCert_1_104537, primeGapCert_1_104743, primeGapCert_1_104953, primeGapCert_1_105143, primeGapCert_1_105341, primeGapCert_1_105541, primeGapCert_1_105751, primeGapCert_1_105953, primeGapCert_1_106163, primeGapCert_1_106373, primeGapCert_1_106543, primeGapCert_1_106753, primeGapCert_1_106963, primeGapCert_1_107171, primeGapCert_1_107377, primeGapCert_1_107581, primeGapCert_1_107791, primeGapCert_1_107999, primeGapCert_1_108203, primeGapCert_1_108413, primeGapCert_1_108587, primeGapCert_1_108793, primeGapCert_1_109001, primeGapCert_1_109211, primeGapCert_1_109397, primeGapCert_1_109597, primeGapCert_1_109807, primeGapCert_1_110017, primeGapCert_1_110221]

private def primeGapCertified_1_0 : List ℕ :=
  [102301, 102503, 102701, 102911, 103099, 103307, 103511, 103703, 103913, 104123, 104327, 104537, 104743, 104953, 105143, 105341, 105541, 105751, 105953, 106163, 106373, 106543, 106753, 106963, 107171, 107377, 107581, 107791, 107999, 108203, 108413, 108587, 108793, 109001, 109211, 109397, 109597, 109807, 110017, 110221]

private lemma primeGapCertified_1_0_values :
    primeGapCertifiedCerts_1_0.map PrimeCertificate.value = primeGapCertified_1_0 := by
  rfl

private lemma primeGapCertified_1_0_primes : primeGapCertified_1_0.Forall Nat.Prime := by
  rw [← primeGapCertified_1_0_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_0_chain : primeGapCertified_1_0.IsChain GapStep := by
  norm_num [primeGapCertified_1_0, List.IsChain, GapStep]

private lemma primeGapCertified_1_0_segment :
    CertifiedSegment primeGapCertified_1_0 102301 110221 :=
  ⟨primeGapCertified_1_0_primes, primeGapCertified_1_0_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_1 : List PrimeCertificate :=
  [primeGapCert_1_110431, primeGapCert_1_110641, primeGapCert_1_110849, primeGapCert_1_111053, primeGapCert_1_111263, primeGapCert_1_111467, primeGapCert_1_111667, primeGapCert_1_111871, primeGapCert_1_112069, primeGapCert_1_112279, primeGapCert_1_112481, primeGapCert_1_112691, primeGapCert_1_112901, primeGapCert_1_113111, primeGapCert_1_113287, primeGapCert_1_113497, primeGapCert_1_113683, primeGapCert_1_113891, primeGapCert_1_114089, primeGapCert_1_114299, primeGapCert_1_114493, primeGapCert_1_114691, primeGapCert_1_114901, primeGapCert_1_115099, primeGapCert_1_115309, primeGapCert_1_115513, primeGapCert_1_115693, primeGapCert_1_115903, primeGapCert_1_116113, primeGapCert_1_116293, primeGapCert_1_116491, primeGapCert_1_116689, primeGapCert_1_116881, primeGapCert_1_117071, primeGapCert_1_117281, primeGapCert_1_117443, primeGapCert_1_117643, primeGapCert_1_117851, primeGapCert_1_118061, primeGapCert_1_118259]

private def primeGapCertified_1_1 : List ℕ :=
  [110431, 110641, 110849, 111053, 111263, 111467, 111667, 111871, 112069, 112279, 112481, 112691, 112901, 113111, 113287, 113497, 113683, 113891, 114089, 114299, 114493, 114691, 114901, 115099, 115309, 115513, 115693, 115903, 116113, 116293, 116491, 116689, 116881, 117071, 117281, 117443, 117643, 117851, 118061, 118259]

private lemma primeGapCertified_1_1_values :
    primeGapCertifiedCerts_1_1.map PrimeCertificate.value = primeGapCertified_1_1 := by
  rfl

private lemma primeGapCertified_1_1_primes : primeGapCertified_1_1.Forall Nat.Prime := by
  rw [← primeGapCertified_1_1_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_1_chain : primeGapCertified_1_1.IsChain GapStep := by
  norm_num [primeGapCertified_1_1, List.IsChain, GapStep]

private lemma primeGapCertified_1_1_segment :
    CertifiedSegment primeGapCertified_1_1 110431 118259 :=
  ⟨primeGapCertified_1_1_primes, primeGapCertified_1_1_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_2 : List PrimeCertificate :=
  [primeGapCert_1_118463, primeGapCert_1_118673, primeGapCert_1_118873, primeGapCert_1_119083, primeGapCert_1_119293, primeGapCert_1_119503, primeGapCert_1_119701, primeGapCert_1_119891, primeGapCert_1_120097, primeGapCert_1_120299, primeGapCert_1_120503, primeGapCert_1_120713, primeGapCert_1_120919, primeGapCert_1_121123, primeGapCert_1_121333, primeGapCert_1_121531, primeGapCert_1_121727, primeGapCert_1_121937, primeGapCert_1_122147, primeGapCert_1_122347, primeGapCert_1_122557, primeGapCert_1_122761, primeGapCert_1_122971, primeGapCert_1_123169, primeGapCert_1_123379, primeGapCert_1_123583, primeGapCert_1_123791, primeGapCert_1_124001, primeGapCert_1_124199, primeGapCert_1_124367, primeGapCert_1_124577, primeGapCert_1_124783, primeGapCert_1_124991, primeGapCert_1_125201, primeGapCert_1_125407, primeGapCert_1_125617, primeGapCert_1_125821, primeGapCert_1_126031, primeGapCert_1_126241, primeGapCert_1_126443]

private def primeGapCertified_1_2 : List ℕ :=
  [118463, 118673, 118873, 119083, 119293, 119503, 119701, 119891, 120097, 120299, 120503, 120713, 120919, 121123, 121333, 121531, 121727, 121937, 122147, 122347, 122557, 122761, 122971, 123169, 123379, 123583, 123791, 124001, 124199, 124367, 124577, 124783, 124991, 125201, 125407, 125617, 125821, 126031, 126241, 126443]

private lemma primeGapCertified_1_2_values :
    primeGapCertifiedCerts_1_2.map PrimeCertificate.value = primeGapCertified_1_2 := by
  rfl

private lemma primeGapCertified_1_2_primes : primeGapCertified_1_2.Forall Nat.Prime := by
  rw [← primeGapCertified_1_2_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_2_chain : primeGapCertified_1_2.IsChain GapStep := by
  norm_num [primeGapCertified_1_2, List.IsChain, GapStep]

private lemma primeGapCertified_1_2_segment :
    CertifiedSegment primeGapCertified_1_2 118463 126443 :=
  ⟨primeGapCertified_1_2_primes, primeGapCertified_1_2_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_3 : List PrimeCertificate :=
  [primeGapCert_1_126653, primeGapCert_1_126859, primeGapCert_1_127051, primeGapCert_1_127261, primeGapCert_1_127453, primeGapCert_1_127663, primeGapCert_1_127873, primeGapCert_1_128053, primeGapCert_1_128257, primeGapCert_1_128467, primeGapCert_1_128677, primeGapCert_1_128879, primeGapCert_1_129089, primeGapCert_1_129293, primeGapCert_1_129499, primeGapCert_1_129707, primeGapCert_1_129917, primeGapCert_1_130127, primeGapCert_1_130337, primeGapCert_1_130547, primeGapCert_1_130729, primeGapCert_1_130927, primeGapCert_1_131129, primeGapCert_1_131321, primeGapCert_1_131519, primeGapCert_1_131713, primeGapCert_1_131909, primeGapCert_1_132113, primeGapCert_1_132313, primeGapCert_1_132523, primeGapCert_1_132721, primeGapCert_1_132929, primeGapCert_1_133121, primeGapCert_1_133327, primeGapCert_1_133519, primeGapCert_1_133723, primeGapCert_1_133919, primeGapCert_1_134129, primeGapCert_1_134339, primeGapCert_1_134513]

private def primeGapCertified_1_3 : List ℕ :=
  [126653, 126859, 127051, 127261, 127453, 127663, 127873, 128053, 128257, 128467, 128677, 128879, 129089, 129293, 129499, 129707, 129917, 130127, 130337, 130547, 130729, 130927, 131129, 131321, 131519, 131713, 131909, 132113, 132313, 132523, 132721, 132929, 133121, 133327, 133519, 133723, 133919, 134129, 134339, 134513]

private lemma primeGapCertified_1_3_values :
    primeGapCertifiedCerts_1_3.map PrimeCertificate.value = primeGapCertified_1_3 := by
  rfl

private lemma primeGapCertified_1_3_primes : primeGapCertified_1_3.Forall Nat.Prime := by
  rw [← primeGapCertified_1_3_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_3_chain : primeGapCertified_1_3.IsChain GapStep := by
  norm_num [primeGapCertified_1_3, List.IsChain, GapStep]

private lemma primeGapCertified_1_3_segment :
    CertifiedSegment primeGapCertified_1_3 126653 134513 :=
  ⟨primeGapCertified_1_3_primes, primeGapCertified_1_3_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_4 : List PrimeCertificate :=
  [primeGapCert_1_134707, primeGapCert_1_134917, primeGapCert_1_135119, primeGapCert_1_135329, primeGapCert_1_135533, primeGapCert_1_135743, primeGapCert_1_135937, primeGapCert_1_136139, primeGapCert_1_136343, primeGapCert_1_136547, primeGapCert_1_136753, primeGapCert_1_136963, primeGapCert_1_137153, primeGapCert_1_137363, primeGapCert_1_137573, primeGapCert_1_137777, primeGapCert_1_137983, primeGapCert_1_138191, primeGapCert_1_138401, primeGapCert_1_138599, primeGapCert_1_138799, primeGapCert_1_138977, primeGapCert_1_139187, primeGapCert_1_139397, primeGapCert_1_139597, primeGapCert_1_139801, primeGapCert_1_140009, primeGapCert_1_140207, primeGapCert_1_140417, primeGapCert_1_140627, primeGapCert_1_140837, primeGapCert_1_141041, primeGapCert_1_141241, primeGapCert_1_141443, primeGapCert_1_141653, primeGapCert_1_141863, primeGapCert_1_142067, primeGapCert_1_142271, primeGapCert_1_142469, primeGapCert_1_142673]

private def primeGapCertified_1_4 : List ℕ :=
  [134707, 134917, 135119, 135329, 135533, 135743, 135937, 136139, 136343, 136547, 136753, 136963, 137153, 137363, 137573, 137777, 137983, 138191, 138401, 138599, 138799, 138977, 139187, 139397, 139597, 139801, 140009, 140207, 140417, 140627, 140837, 141041, 141241, 141443, 141653, 141863, 142067, 142271, 142469, 142673]

private lemma primeGapCertified_1_4_values :
    primeGapCertifiedCerts_1_4.map PrimeCertificate.value = primeGapCertified_1_4 := by
  rfl

private lemma primeGapCertified_1_4_primes : primeGapCertified_1_4.Forall Nat.Prime := by
  rw [← primeGapCertified_1_4_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_4_chain : primeGapCertified_1_4.IsChain GapStep := by
  norm_num [primeGapCertified_1_4, List.IsChain, GapStep]

private lemma primeGapCertified_1_4_segment :
    CertifiedSegment primeGapCertified_1_4 134707 142673 :=
  ⟨primeGapCertified_1_4_primes, primeGapCertified_1_4_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_5 : List PrimeCertificate :=
  [primeGapCert_1_142873, primeGapCert_1_143063, primeGapCert_1_143263, primeGapCert_1_143467, primeGapCert_1_143677, primeGapCert_1_143881, primeGapCert_1_144073, primeGapCert_1_144271, primeGapCert_1_144481, primeGapCert_1_144671, primeGapCert_1_144847, primeGapCert_1_145043, primeGapCert_1_145253, primeGapCert_1_145463, primeGapCert_1_145661, primeGapCert_1_145861, primeGapCert_1_146063, primeGapCert_1_146273, primeGapCert_1_146477, primeGapCert_1_146683, primeGapCert_1_146893, primeGapCert_1_147097, primeGapCert_1_147299, primeGapCert_1_147503, primeGapCert_1_147709, primeGapCert_1_147919, primeGapCert_1_148123, primeGapCert_1_148331, primeGapCert_1_148537, primeGapCert_1_148747, primeGapCert_1_148957, primeGapCert_1_149161, primeGapCert_1_149371, primeGapCert_1_149579, primeGapCert_1_149771, primeGapCert_1_149971, primeGapCert_1_150169, primeGapCert_1_150379, primeGapCert_1_150589, primeGapCert_1_150797]

private def primeGapCertified_1_5 : List ℕ :=
  [142873, 143063, 143263, 143467, 143677, 143881, 144073, 144271, 144481, 144671, 144847, 145043, 145253, 145463, 145661, 145861, 146063, 146273, 146477, 146683, 146893, 147097, 147299, 147503, 147709, 147919, 148123, 148331, 148537, 148747, 148957, 149161, 149371, 149579, 149771, 149971, 150169, 150379, 150589, 150797]

private lemma primeGapCertified_1_5_values :
    primeGapCertifiedCerts_1_5.map PrimeCertificate.value = primeGapCertified_1_5 := by
  rfl

private lemma primeGapCertified_1_5_primes : primeGapCertified_1_5.Forall Nat.Prime := by
  rw [← primeGapCertified_1_5_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_5_chain : primeGapCertified_1_5.IsChain GapStep := by
  norm_num [primeGapCertified_1_5, List.IsChain, GapStep]

private lemma primeGapCertified_1_5_segment :
    CertifiedSegment primeGapCertified_1_5 142873 150797 :=
  ⟨primeGapCertified_1_5_primes, primeGapCertified_1_5_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_6 : List PrimeCertificate :=
  [primeGapCert_1_151007, primeGapCert_1_151213, primeGapCert_1_151423, primeGapCert_1_151631, primeGapCert_1_151841, primeGapCert_1_152041, primeGapCert_1_152249, primeGapCert_1_152459, primeGapCert_1_152657, primeGapCert_1_152857, primeGapCert_1_153067, primeGapCert_1_153277, primeGapCert_1_153487, primeGapCert_1_153689, primeGapCert_1_153889, primeGapCert_1_154097, primeGapCert_1_154303, primeGapCert_1_154501, primeGapCert_1_154699, primeGapCert_1_154897, primeGapCert_1_155087, primeGapCert_1_155291, primeGapCert_1_155501, primeGapCert_1_155707, primeGapCert_1_155893, primeGapCert_1_156089, primeGapCert_1_156269, primeGapCert_1_156467, primeGapCert_1_156677, primeGapCert_1_156887, primeGapCert_1_157081, primeGapCert_1_157291, primeGapCert_1_157489, primeGapCert_1_157679, primeGapCert_1_157889, primeGapCert_1_158077, primeGapCert_1_158269, primeGapCert_1_158449, primeGapCert_1_158657, primeGapCert_1_158867]

private def primeGapCertified_1_6 : List ℕ :=
  [151007, 151213, 151423, 151631, 151841, 152041, 152249, 152459, 152657, 152857, 153067, 153277, 153487, 153689, 153889, 154097, 154303, 154501, 154699, 154897, 155087, 155291, 155501, 155707, 155893, 156089, 156269, 156467, 156677, 156887, 157081, 157291, 157489, 157679, 157889, 158077, 158269, 158449, 158657, 158867]

private lemma primeGapCertified_1_6_values :
    primeGapCertifiedCerts_1_6.map PrimeCertificate.value = primeGapCertified_1_6 := by
  rfl

private lemma primeGapCertified_1_6_primes : primeGapCertified_1_6.Forall Nat.Prime := by
  rw [← primeGapCertified_1_6_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_6_chain : primeGapCertified_1_6.IsChain GapStep := by
  norm_num [primeGapCertified_1_6, List.IsChain, GapStep]

private lemma primeGapCertified_1_6_segment :
    CertifiedSegment primeGapCertified_1_6 151007 158867 :=
  ⟨primeGapCertified_1_6_primes, primeGapCertified_1_6_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_7 : List PrimeCertificate :=
  [primeGapCert_1_159073, primeGapCert_1_159233, primeGapCert_1_159437, primeGapCert_1_159631, primeGapCert_1_159839, primeGapCert_1_160049, primeGapCert_1_160253, primeGapCert_1_160453, primeGapCert_1_160663, primeGapCert_1_160861, primeGapCert_1_161071, primeGapCert_1_161281, primeGapCert_1_161471, primeGapCert_1_161659, primeGapCert_1_161869, primeGapCert_1_162079, primeGapCert_1_162289, primeGapCert_1_162499, primeGapCert_1_162709, primeGapCert_1_162917, primeGapCert_1_163127, primeGapCert_1_163337, primeGapCert_1_163543, primeGapCert_1_163753, primeGapCert_1_163927, primeGapCert_1_164117, primeGapCert_1_164321, primeGapCert_1_164531, primeGapCert_1_164729, primeGapCert_1_164911, primeGapCert_1_165103, primeGapCert_1_165313, primeGapCert_1_165523, primeGapCert_1_165721, primeGapCert_1_165931, primeGapCert_1_166099, primeGapCert_1_166303, primeGapCert_1_166487, primeGapCert_1_166693, primeGapCert_1_166871]

private def primeGapCertified_1_7 : List ℕ :=
  [159073, 159233, 159437, 159631, 159839, 160049, 160253, 160453, 160663, 160861, 161071, 161281, 161471, 161659, 161869, 162079, 162289, 162499, 162709, 162917, 163127, 163337, 163543, 163753, 163927, 164117, 164321, 164531, 164729, 164911, 165103, 165313, 165523, 165721, 165931, 166099, 166303, 166487, 166693, 166871]

private lemma primeGapCertified_1_7_values :
    primeGapCertifiedCerts_1_7.map PrimeCertificate.value = primeGapCertified_1_7 := by
  rfl

private lemma primeGapCertified_1_7_primes : primeGapCertified_1_7.Forall Nat.Prime := by
  rw [← primeGapCertified_1_7_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_7_chain : primeGapCertified_1_7.IsChain GapStep := by
  norm_num [primeGapCertified_1_7, List.IsChain, GapStep]

private lemma primeGapCertified_1_7_segment :
    CertifiedSegment primeGapCertified_1_7 159073 166871 :=
  ⟨primeGapCertified_1_7_primes, primeGapCertified_1_7_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_8 : List PrimeCertificate :=
  [primeGapCert_1_167081, primeGapCert_1_167269, primeGapCert_1_167471, primeGapCert_1_167677, primeGapCert_1_167887, primeGapCert_1_168089, primeGapCert_1_168293, primeGapCert_1_168499, primeGapCert_1_168697, primeGapCert_1_168901, primeGapCert_1_169111, primeGapCert_1_169321, primeGapCert_1_169531, primeGapCert_1_169733, primeGapCert_1_169943, primeGapCert_1_170141, primeGapCert_1_170351, primeGapCert_1_170557, primeGapCert_1_170767, primeGapCert_1_170971, primeGapCert_1_171179, primeGapCert_1_171383, primeGapCert_1_171583, primeGapCert_1_171793, primeGapCert_1_172001, primeGapCert_1_172199, primeGapCert_1_172399, primeGapCert_1_172607, primeGapCert_1_172807, primeGapCert_1_172999, primeGapCert_1_173209, primeGapCert_1_173359, primeGapCert_1_173561, primeGapCert_1_173743, primeGapCert_1_173933, primeGapCert_1_174143, primeGapCert_1_174347, primeGapCert_1_174533, primeGapCert_1_174737, primeGapCert_1_174943]

private def primeGapCertified_1_8 : List ℕ :=
  [167081, 167269, 167471, 167677, 167887, 168089, 168293, 168499, 168697, 168901, 169111, 169321, 169531, 169733, 169943, 170141, 170351, 170557, 170767, 170971, 171179, 171383, 171583, 171793, 172001, 172199, 172399, 172607, 172807, 172999, 173209, 173359, 173561, 173743, 173933, 174143, 174347, 174533, 174737, 174943]

private lemma primeGapCertified_1_8_values :
    primeGapCertifiedCerts_1_8.map PrimeCertificate.value = primeGapCertified_1_8 := by
  rfl

private lemma primeGapCertified_1_8_primes : primeGapCertified_1_8.Forall Nat.Prime := by
  rw [← primeGapCertified_1_8_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_8_chain : primeGapCertified_1_8.IsChain GapStep := by
  norm_num [primeGapCertified_1_8, List.IsChain, GapStep]

private lemma primeGapCertified_1_8_segment :
    CertifiedSegment primeGapCertified_1_8 167081 174943 :=
  ⟨primeGapCertified_1_8_primes, primeGapCertified_1_8_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_9 : List PrimeCertificate :=
  [primeGapCert_1_175141, primeGapCert_1_175349, primeGapCert_1_175543, primeGapCert_1_175753, primeGapCert_1_175963, primeGapCert_1_176161, primeGapCert_1_176369, primeGapCert_1_176573, primeGapCert_1_176779, primeGapCert_1_176989, primeGapCert_1_177173, primeGapCert_1_177383, primeGapCert_1_177589, primeGapCert_1_177797, primeGapCert_1_178001, primeGapCert_1_178207, primeGapCert_1_178417, primeGapCert_1_178627, primeGapCert_1_178831, primeGapCert_1_179041, primeGapCert_1_179243, primeGapCert_1_179453, primeGapCert_1_179659, primeGapCert_1_179849, primeGapCert_1_180053, primeGapCert_1_180263, primeGapCert_1_180473, primeGapCert_1_180679, primeGapCert_1_180883, primeGapCert_1_181087, primeGapCert_1_181297, primeGapCert_1_181501, primeGapCert_1_181711, primeGapCert_1_181919, primeGapCert_1_182129, primeGapCert_1_182339, primeGapCert_1_182549, primeGapCert_1_182747, primeGapCert_1_182957, primeGapCert_1_183167]

private def primeGapCertified_1_9 : List ℕ :=
  [175141, 175349, 175543, 175753, 175963, 176161, 176369, 176573, 176779, 176989, 177173, 177383, 177589, 177797, 178001, 178207, 178417, 178627, 178831, 179041, 179243, 179453, 179659, 179849, 180053, 180263, 180473, 180679, 180883, 181087, 181297, 181501, 181711, 181919, 182129, 182339, 182549, 182747, 182957, 183167]

private lemma primeGapCertified_1_9_values :
    primeGapCertifiedCerts_1_9.map PrimeCertificate.value = primeGapCertified_1_9 := by
  rfl

private lemma primeGapCertified_1_9_primes : primeGapCertified_1_9.Forall Nat.Prime := by
  rw [← primeGapCertified_1_9_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_9_chain : primeGapCertified_1_9.IsChain GapStep := by
  norm_num [primeGapCertified_1_9, List.IsChain, GapStep]

private lemma primeGapCertified_1_9_segment :
    CertifiedSegment primeGapCertified_1_9 175141 183167 :=
  ⟨primeGapCertified_1_9_primes, primeGapCertified_1_9_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_10 : List PrimeCertificate :=
  [primeGapCert_1_183377, primeGapCert_1_183587, primeGapCert_1_183797, primeGapCert_1_184007, primeGapCert_1_184211, primeGapCert_1_184417, primeGapCert_1_184627, primeGapCert_1_184837, primeGapCert_1_185027, primeGapCert_1_185233, primeGapCert_1_185441, primeGapCert_1_185651, primeGapCert_1_185849, primeGapCert_1_186049, primeGapCert_1_186259, primeGapCert_1_186469, primeGapCert_1_186679, primeGapCert_1_186889, primeGapCert_1_187091, primeGapCert_1_187277, primeGapCert_1_187477, primeGapCert_1_187687, primeGapCert_1_187897, primeGapCert_1_188107, primeGapCert_1_188317, primeGapCert_1_188527, primeGapCert_1_188729, primeGapCert_1_188939, primeGapCert_1_189149, primeGapCert_1_189353, primeGapCert_1_189559, primeGapCert_1_189767, primeGapCert_1_189977, primeGapCert_1_190181, primeGapCert_1_190391, primeGapCert_1_190591, primeGapCert_1_190793, primeGapCert_1_190997, primeGapCert_1_191189, primeGapCert_1_191353]

private def primeGapCertified_1_10 : List ℕ :=
  [183377, 183587, 183797, 184007, 184211, 184417, 184627, 184837, 185027, 185233, 185441, 185651, 185849, 186049, 186259, 186469, 186679, 186889, 187091, 187277, 187477, 187687, 187897, 188107, 188317, 188527, 188729, 188939, 189149, 189353, 189559, 189767, 189977, 190181, 190391, 190591, 190793, 190997, 191189, 191353]

private lemma primeGapCertified_1_10_values :
    primeGapCertifiedCerts_1_10.map PrimeCertificate.value = primeGapCertified_1_10 := by
  rfl

private lemma primeGapCertified_1_10_primes : primeGapCertified_1_10.Forall Nat.Prime := by
  rw [← primeGapCertified_1_10_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_10_chain : primeGapCertified_1_10.IsChain GapStep := by
  norm_num [primeGapCertified_1_10, List.IsChain, GapStep]

private lemma primeGapCertified_1_10_segment :
    CertifiedSegment primeGapCertified_1_10 183377 191353 :=
  ⟨primeGapCertified_1_10_primes, primeGapCertified_1_10_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_11 : List PrimeCertificate :=
  [primeGapCert_1_191563, primeGapCert_1_191773, primeGapCert_1_191977, primeGapCert_1_192187, primeGapCert_1_192391, primeGapCert_1_192601, primeGapCert_1_192811, primeGapCert_1_193013, primeGapCert_1_193201, primeGapCert_1_193393, primeGapCert_1_193603, primeGapCert_1_193813, primeGapCert_1_194017, primeGapCert_1_194203, primeGapCert_1_194413, primeGapCert_1_194609, primeGapCert_1_194819, primeGapCert_1_195029, primeGapCert_1_195229, primeGapCert_1_195427, primeGapCert_1_195599, primeGapCert_1_195809, primeGapCert_1_196003, primeGapCert_1_196201, primeGapCert_1_196387, primeGapCert_1_196597, primeGapCert_1_196799, primeGapCert_1_197009, primeGapCert_1_197207, primeGapCert_1_197389, primeGapCert_1_197599, primeGapCert_1_197807, primeGapCert_1_198017, primeGapCert_1_198223, primeGapCert_1_198427, primeGapCert_1_198637, primeGapCert_1_198841, primeGapCert_1_199049, primeGapCert_1_199247, primeGapCert_1_199457]

private def primeGapCertified_1_11 : List ℕ :=
  [191563, 191773, 191977, 192187, 192391, 192601, 192811, 193013, 193201, 193393, 193603, 193813, 194017, 194203, 194413, 194609, 194819, 195029, 195229, 195427, 195599, 195809, 196003, 196201, 196387, 196597, 196799, 197009, 197207, 197389, 197599, 197807, 198017, 198223, 198427, 198637, 198841, 199049, 199247, 199457]

private lemma primeGapCertified_1_11_values :
    primeGapCertifiedCerts_1_11.map PrimeCertificate.value = primeGapCertified_1_11 := by
  rfl

private lemma primeGapCertified_1_11_primes : primeGapCertified_1_11.Forall Nat.Prime := by
  rw [← primeGapCertified_1_11_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_11_chain : primeGapCertified_1_11.IsChain GapStep := by
  norm_num [primeGapCertified_1_11, List.IsChain, GapStep]

private lemma primeGapCertified_1_11_segment :
    CertifiedSegment primeGapCertified_1_11 191563 199457 :=
  ⟨primeGapCertified_1_11_primes, primeGapCertified_1_11_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_1_12 : List PrimeCertificate :=
  [primeGapCert_1_199657, primeGapCert_1_199853, primeGapCert_1_200063, primeGapCert_1_200273, primeGapCert_1_200483, primeGapCert_1_200689, primeGapCert_1_200899, primeGapCert_1_201107, primeGapCert_1_201307, primeGapCert_1_201517, primeGapCert_1_201709, primeGapCert_1_201919, primeGapCert_1_202129, primeGapCert_1_202339, primeGapCert_1_202549, primeGapCert_1_202757, primeGapCert_1_202967, primeGapCert_1_203173, primeGapCert_1_203383, primeGapCert_1_203591]

private def primeGapCertified_1_12 : List ℕ :=
  [199657, 199853, 200063, 200273, 200483, 200689, 200899, 201107, 201307, 201517, 201709, 201919, 202129, 202339, 202549, 202757, 202967, 203173, 203383, 203591]

private lemma primeGapCertified_1_12_values :
    primeGapCertifiedCerts_1_12.map PrimeCertificate.value = primeGapCertified_1_12 := by
  rfl

private lemma primeGapCertified_1_12_primes : primeGapCertified_1_12.Forall Nat.Prime := by
  rw [← primeGapCertified_1_12_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_1_12_chain : primeGapCertified_1_12.IsChain GapStep := by
  norm_num [primeGapCertified_1_12, List.IsChain, GapStep]

private lemma primeGapCertified_1_12_segment :
    CertifiedSegment primeGapCertified_1_12 199657 203591 :=
  ⟨primeGapCertified_1_12_primes, primeGapCertified_1_12_chain, by rfl, by rfl⟩

private def primeGapCertifiedGroup1Step0 : List ℕ := primeGapCertified_1_0

private lemma primeGapCertifiedGroup1Step0_segment :
    CertifiedSegment primeGapCertifiedGroup1Step0 102301 110221 := by
  unfold primeGapCertifiedGroup1Step0
  exact primeGapCertified_1_0_segment

private def primeGapCertifiedGroup1Step1 : List ℕ :=
  primeGapCertifiedGroup1Step0 ++ primeGapCertified_1_1

private lemma primeGapCertifiedGroup1Step1_segment :
    CertifiedSegment primeGapCertifiedGroup1Step1 102301 118259 := by
  unfold primeGapCertifiedGroup1Step1
  exact primeGapCertifiedGroup1Step0_segment.append primeGapCertified_1_1_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step2 : List ℕ :=
  primeGapCertifiedGroup1Step1 ++ primeGapCertified_1_2

private lemma primeGapCertifiedGroup1Step2_segment :
    CertifiedSegment primeGapCertifiedGroup1Step2 102301 126443 := by
  unfold primeGapCertifiedGroup1Step2
  exact primeGapCertifiedGroup1Step1_segment.append primeGapCertified_1_2_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step3 : List ℕ :=
  primeGapCertifiedGroup1Step2 ++ primeGapCertified_1_3

private lemma primeGapCertifiedGroup1Step3_segment :
    CertifiedSegment primeGapCertifiedGroup1Step3 102301 134513 := by
  unfold primeGapCertifiedGroup1Step3
  exact primeGapCertifiedGroup1Step2_segment.append primeGapCertified_1_3_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step4 : List ℕ :=
  primeGapCertifiedGroup1Step3 ++ primeGapCertified_1_4

private lemma primeGapCertifiedGroup1Step4_segment :
    CertifiedSegment primeGapCertifiedGroup1Step4 102301 142673 := by
  unfold primeGapCertifiedGroup1Step4
  exact primeGapCertifiedGroup1Step3_segment.append primeGapCertified_1_4_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step5 : List ℕ :=
  primeGapCertifiedGroup1Step4 ++ primeGapCertified_1_5

private lemma primeGapCertifiedGroup1Step5_segment :
    CertifiedSegment primeGapCertifiedGroup1Step5 102301 150797 := by
  unfold primeGapCertifiedGroup1Step5
  exact primeGapCertifiedGroup1Step4_segment.append primeGapCertified_1_5_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step6 : List ℕ :=
  primeGapCertifiedGroup1Step5 ++ primeGapCertified_1_6

private lemma primeGapCertifiedGroup1Step6_segment :
    CertifiedSegment primeGapCertifiedGroup1Step6 102301 158867 := by
  unfold primeGapCertifiedGroup1Step6
  exact primeGapCertifiedGroup1Step5_segment.append primeGapCertified_1_6_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step7 : List ℕ :=
  primeGapCertifiedGroup1Step6 ++ primeGapCertified_1_7

private lemma primeGapCertifiedGroup1Step7_segment :
    CertifiedSegment primeGapCertifiedGroup1Step7 102301 166871 := by
  unfold primeGapCertifiedGroup1Step7
  exact primeGapCertifiedGroup1Step6_segment.append primeGapCertified_1_7_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step8 : List ℕ :=
  primeGapCertifiedGroup1Step7 ++ primeGapCertified_1_8

private lemma primeGapCertifiedGroup1Step8_segment :
    CertifiedSegment primeGapCertifiedGroup1Step8 102301 174943 := by
  unfold primeGapCertifiedGroup1Step8
  exact primeGapCertifiedGroup1Step7_segment.append primeGapCertified_1_8_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step9 : List ℕ :=
  primeGapCertifiedGroup1Step8 ++ primeGapCertified_1_9

private lemma primeGapCertifiedGroup1Step9_segment :
    CertifiedSegment primeGapCertifiedGroup1Step9 102301 183167 := by
  unfold primeGapCertifiedGroup1Step9
  exact primeGapCertifiedGroup1Step8_segment.append primeGapCertified_1_9_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step10 : List ℕ :=
  primeGapCertifiedGroup1Step9 ++ primeGapCertified_1_10

private lemma primeGapCertifiedGroup1Step10_segment :
    CertifiedSegment primeGapCertifiedGroup1Step10 102301 191353 := by
  unfold primeGapCertifiedGroup1Step10
  exact primeGapCertifiedGroup1Step9_segment.append primeGapCertified_1_10_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step11 : List ℕ :=
  primeGapCertifiedGroup1Step10 ++ primeGapCertified_1_11

private lemma primeGapCertifiedGroup1Step11_segment :
    CertifiedSegment primeGapCertifiedGroup1Step11 102301 199457 := by
  unfold primeGapCertifiedGroup1Step11
  exact primeGapCertifiedGroup1Step10_segment.append primeGapCertified_1_11_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup1Step12 : List ℕ :=
  primeGapCertifiedGroup1Step11 ++ primeGapCertified_1_12

private lemma primeGapCertifiedGroup1Step12_segment :
    CertifiedSegment primeGapCertifiedGroup1Step12 102301 203591 := by
  unfold primeGapCertifiedGroup1Step12
  exact primeGapCertifiedGroup1Step11_segment.append primeGapCertified_1_12_segment
    (by norm_num [GapStep])

def primeGapCertifiedGroup1 : List ℕ := primeGapCertifiedGroup1Step12

lemma primeGapCertifiedGroup1_segment :
    CertifiedSegment primeGapCertifiedGroup1 102301 203591 := by
  unfold primeGapCertifiedGroup1
  exact primeGapCertifiedGroup1Step12_segment

end PrimeGap210Certificate

end Erdos1058
