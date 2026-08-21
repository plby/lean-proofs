import ErdosProblems.Erdos1058.Erdos1058PrimeGapBase
import ErdosProblems.Erdos1058.Erdos1058PrimeCertificate

namespace Erdos1058

namespace PrimeGap210Certificate

private def primeGapCertBatch36_2 : PrimeCertificate := .two

private def primeGapCertBatch36_3 : PrimeCertificate :=
  .lucas 3 2 (.cons primeGapCertBatch36_2 (.nil))

private def primeGapCertBatch36_5 : PrimeCertificate :=
  .lucas 5 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.nil)))

private def primeGapCertBatch36_7 : PrimeCertificate :=
  .lucas 7 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.nil)))

private def primeGapCertBatch36_11 : PrimeCertificate :=
  .lucas 11 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.nil)))

private def primeGapCertBatch36_13 : PrimeCertificate :=
  .lucas 13 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.nil))))

private def primeGapCertBatch36_17 : PrimeCertificate :=
  .lucas 17 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.nil)))))

private def primeGapCertBatch36_19 : PrimeCertificate :=
  .lucas 19 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.nil))))

private def primeGapCertBatch36_23 : PrimeCertificate :=
  .lucas 23 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.nil)))

private def primeGapCertBatch36_29 : PrimeCertificate :=
  .lucas 29 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.nil))))

private def primeGapCertBatch36_31 : PrimeCertificate :=
  .lucas 31 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil))))

private def primeGapCertBatch36_37 : PrimeCertificate :=
  .lucas 37 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.nil)))))

private def primeGapCertBatch36_41 : PrimeCertificate :=
  .lucas 41 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.nil)))))

private def primeGapCertBatch36_43 : PrimeCertificate :=
  .lucas 43 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.nil))))

private def primeGapCertBatch36_47 : PrimeCertificate :=
  .lucas 47 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.nil)))

private def primeGapCertBatch36_53 : PrimeCertificate :=
  .lucas 53 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.nil))))

private def primeGapCertBatch36_59 : PrimeCertificate :=
  .lucas 59 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.nil)))

private def primeGapCertBatch36_61 : PrimeCertificate :=
  .lucas 61 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil)))))

private def primeGapCertBatch36_67 : PrimeCertificate :=
  .lucas 67 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.nil))))

private def primeGapCertBatch36_71 : PrimeCertificate :=
  .lucas 71 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.nil))))

private def primeGapCertBatch36_73 : PrimeCertificate :=
  .lucas 73 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.nil))))))

private def primeGapCertBatch36_79 : PrimeCertificate :=
  .lucas 79 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.nil))))

private def primeGapCertBatch36_83 : PrimeCertificate :=
  .lucas 83 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_41 (.nil)))

private def primeGapCertBatch36_89 : PrimeCertificate :=
  .lucas 89 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.nil)))))

private def primeGapCertBatch36_97 : PrimeCertificate :=
  .lucas 97 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.nil)))))))

private def primeGapCertBatch36_101 : PrimeCertificate :=
  .lucas 101 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.nil)))))

private def primeGapCertBatch36_103 : PrimeCertificate :=
  .lucas 103 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.nil))))

private def primeGapCertBatch36_107 : PrimeCertificate :=
  .lucas 107 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_53 (.nil)))

private def primeGapCertBatch36_109 : PrimeCertificate :=
  .lucas 109 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.nil))))))

private def primeGapCertBatch36_113 : PrimeCertificate :=
  .lucas 113 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.nil))))))

private def primeGapCertBatch36_127 : PrimeCertificate :=
  .lucas 127 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.nil)))))

private def primeGapCertBatch36_131 : PrimeCertificate :=
  .lucas 131 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.nil))))

private def primeGapCertBatch36_137 : PrimeCertificate :=
  .lucas 137 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.nil)))))

private def primeGapCertBatch36_139 : PrimeCertificate :=
  .lucas 139 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.nil))))

private def primeGapCertBatch36_149 : PrimeCertificate :=
  .lucas 149 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_37 (.nil))))

private def primeGapCertBatch36_151 : PrimeCertificate :=
  .lucas 151 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.nil)))))

private def primeGapCertBatch36_157 : PrimeCertificate :=
  .lucas 157 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.nil)))))

private def primeGapCertBatch36_163 : PrimeCertificate :=
  .lucas 163 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.nil))))))

private def primeGapCertBatch36_167 : PrimeCertificate :=
  .lucas 167 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_83 (.nil)))

private def primeGapCertBatch36_173 : PrimeCertificate :=
  .lucas 173 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_43 (.nil))))

private def primeGapCertBatch36_179 : PrimeCertificate :=
  .lucas 179 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_89 (.nil)))

private def primeGapCertBatch36_181 : PrimeCertificate :=
  .lucas 181 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil))))))

private def primeGapCertBatch36_191 : PrimeCertificate :=
  .lucas 191 19 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.nil))))

private def primeGapCertBatch36_193 : PrimeCertificate :=
  .lucas 193 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.nil))))))))

private def primeGapCertBatch36_197 : PrimeCertificate :=
  .lucas 197 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.nil)))))

private def primeGapCertBatch36_199 : PrimeCertificate :=
  .lucas 199 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.nil)))))

private def primeGapCertBatch36_211 : PrimeCertificate :=
  .lucas 211 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.nil)))))

private def primeGapCertBatch36_223 : PrimeCertificate :=
  .lucas 223 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_37 (.nil))))

private def primeGapCertBatch36_227 : PrimeCertificate :=
  .lucas 227 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_113 (.nil)))

private def primeGapCertBatch36_229 : PrimeCertificate :=
  .lucas 229 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.nil)))))

private def primeGapCertBatch36_233 : PrimeCertificate :=
  .lucas 233 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.nil)))))

private def primeGapCertBatch36_239 : PrimeCertificate :=
  .lucas 239 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.nil))))

private def primeGapCertBatch36_241 : PrimeCertificate :=
  .lucas 241 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil)))))))

private def primeGapCertBatch36_251 : PrimeCertificate :=
  .lucas 251 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.nil)))))

private def primeGapCertBatch36_257 : PrimeCertificate :=
  .lucas 257 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.nil)))))))))

private def primeGapCertBatch36_263 : PrimeCertificate :=
  .lucas 263 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_131 (.nil)))

private def primeGapCertBatch36_269 : PrimeCertificate :=
  .lucas 269 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_67 (.nil))))

private def primeGapCertBatch36_271 : PrimeCertificate :=
  .lucas 271 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil))))))

private def primeGapCertBatch36_277 : PrimeCertificate :=
  .lucas 277 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.nil)))))

private def primeGapCertBatch36_281 : PrimeCertificate :=
  .lucas 281 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.nil))))))

private def primeGapCertBatch36_283 : PrimeCertificate :=
  .lucas 283 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_47 (.nil))))

private def primeGapCertBatch36_293 : PrimeCertificate :=
  .lucas 293 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_73 (.nil))))

private def primeGapCertBatch36_307 : PrimeCertificate :=
  .lucas 307 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.nil)))))

private def primeGapCertBatch36_311 : PrimeCertificate :=
  .lucas 311 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_31 (.nil))))

private def primeGapCertBatch36_313 : PrimeCertificate :=
  .lucas 313 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.nil))))))

private def primeGapCertBatch36_317 : PrimeCertificate :=
  .lucas 317 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_79 (.nil))))

private def primeGapCertBatch36_331 : PrimeCertificate :=
  .lucas 331 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.nil)))))

private def primeGapCertBatch36_337 : PrimeCertificate :=
  .lucas 337 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.nil)))))))

private def primeGapCertBatch36_347 : PrimeCertificate :=
  .lucas 347 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_173 (.nil)))

private def primeGapCertBatch36_349 : PrimeCertificate :=
  .lucas 349 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.nil)))))

private def primeGapCertBatch36_353 : PrimeCertificate :=
  .lucas 353 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.nil)))))))

private def primeGapCertBatch36_359 : PrimeCertificate :=
  .lucas 359 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_179 (.nil)))

private def primeGapCertBatch36_367 : PrimeCertificate :=
  .lucas 367 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_61 (.nil))))

private def primeGapCertBatch36_373 : PrimeCertificate :=
  .lucas 373 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_31 (.nil)))))

private def primeGapCertBatch36_379 : PrimeCertificate :=
  .lucas 379 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.nil))))))

private def primeGapCertBatch36_383 : PrimeCertificate :=
  .lucas 383 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_191 (.nil)))

private def primeGapCertBatch36_397 : PrimeCertificate :=
  .lucas 397 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.nil))))))

private def primeGapCertBatch36_401 : PrimeCertificate :=
  .lucas 401 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.nil)))))))

private def primeGapCertBatch36_409 : PrimeCertificate :=
  .lucas 409 21 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.nil))))))

private def primeGapCertBatch36_419 : PrimeCertificate :=
  .lucas 419 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_19 (.nil))))

private def primeGapCertBatch36_421 : PrimeCertificate :=
  .lucas 421 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.nil))))))

private def primeGapCertBatch36_431 : PrimeCertificate :=
  .lucas 431 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_43 (.nil))))

private def primeGapCertBatch36_433 : PrimeCertificate :=
  .lucas 433 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.nil))))))))

private def primeGapCertBatch36_439 : PrimeCertificate :=
  .lucas 439 15 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_73 (.nil))))

private def primeGapCertBatch36_443 : PrimeCertificate :=
  .lucas 443 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_17 (.nil))))

private def primeGapCertBatch36_449 : PrimeCertificate :=
  .lucas 449 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.nil))))))))

private def primeGapCertBatch36_457 : PrimeCertificate :=
  .lucas 457 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.nil))))))

private def primeGapCertBatch36_461 : PrimeCertificate :=
  .lucas 461 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_23 (.nil)))))

private def primeGapCertBatch36_463 : PrimeCertificate :=
  .lucas 463 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.nil)))))

private def primeGapCertBatch36_467 : PrimeCertificate :=
  .lucas 467 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_233 (.nil)))

private def primeGapCertBatch36_479 : PrimeCertificate :=
  .lucas 479 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_239 (.nil)))

private def primeGapCertBatch36_487 : PrimeCertificate :=
  .lucas 487 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.nil)))))))

private def primeGapCertBatch36_491 : PrimeCertificate :=
  .lucas 491 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.nil)))))

private def primeGapCertBatch36_499 : PrimeCertificate :=
  .lucas 499 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_83 (.nil))))

private def primeGapCertBatch36_503 : PrimeCertificate :=
  .lucas 503 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_251 (.nil)))

private def primeGapCertBatch36_509 : PrimeCertificate :=
  .lucas 509 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_127 (.nil))))

private def primeGapCertBatch36_521 : PrimeCertificate :=
  .lucas 521 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.nil))))))

private def primeGapCertBatch36_523 : PrimeCertificate :=
  .lucas 523 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.nil)))))

private def primeGapCertBatch36_541 : PrimeCertificate :=
  .lucas 541 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil)))))))

private def primeGapCertBatch36_547 : PrimeCertificate :=
  .lucas 547 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.nil)))))

private def primeGapCertBatch36_557 : PrimeCertificate :=
  .lucas 557 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_139 (.nil))))

private def primeGapCertBatch36_563 : PrimeCertificate :=
  .lucas 563 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_281 (.nil)))

private def primeGapCertBatch36_577 : PrimeCertificate :=
  .lucas 577 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.nil)))))))))

private def primeGapCertBatch36_587 : PrimeCertificate :=
  .lucas 587 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_293 (.nil)))

private def primeGapCertBatch36_593 : PrimeCertificate :=
  .lucas 593 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_37 (.nil))))))

private def primeGapCertBatch36_599 : PrimeCertificate :=
  .lucas 599 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_23 (.nil))))

private def primeGapCertBatch36_601 : PrimeCertificate :=
  .lucas 601 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.nil)))))))

private def primeGapCertBatch36_607 : PrimeCertificate :=
  .lucas 607 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_101 (.nil))))

private def primeGapCertBatch36_613 : PrimeCertificate :=
  .lucas 613 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.nil))))))

private def primeGapCertBatch36_617 : PrimeCertificate :=
  .lucas 617 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.nil))))))

private def primeGapCertBatch36_619 : PrimeCertificate :=
  .lucas 619 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_103 (.nil))))

private def primeGapCertBatch36_631 : PrimeCertificate :=
  .lucas 631 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.nil))))))

private def primeGapCertBatch36_641 : PrimeCertificate :=
  .lucas 641 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.nil)))))))))

private def primeGapCertBatch36_643 : PrimeCertificate :=
  .lucas 643 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_107 (.nil))))

private def primeGapCertBatch36_647 : PrimeCertificate :=
  .lucas 647 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_19 (.nil))))

private def primeGapCertBatch36_653 : PrimeCertificate :=
  .lucas 653 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_163 (.nil))))

private def primeGapCertBatch36_659 : PrimeCertificate :=
  .lucas 659 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_47 (.nil))))

private def primeGapCertBatch36_661 : PrimeCertificate :=
  .lucas 661 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.nil))))))

private def primeGapCertBatch36_673 : PrimeCertificate :=
  .lucas 673 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.nil))))))))

private def primeGapCertBatch36_677 : PrimeCertificate :=
  .lucas 677 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_13 (.nil)))))

private def primeGapCertBatch36_683 : PrimeCertificate :=
  .lucas 683 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_31 (.nil))))

private def primeGapCertBatch36_701 : PrimeCertificate :=
  .lucas 701 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.nil))))))

private def primeGapCertBatch36_719 : PrimeCertificate :=
  .lucas 719 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_359 (.nil)))

private def primeGapCertBatch36_733 : PrimeCertificate :=
  .lucas 733 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_61 (.nil)))))

private def primeGapCertBatch36_739 : PrimeCertificate :=
  .lucas 739 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_41 (.nil)))))

private def primeGapCertBatch36_743 : PrimeCertificate :=
  .lucas 743 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_53 (.nil))))

private def primeGapCertBatch36_751 : PrimeCertificate :=
  .lucas 751 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.nil))))))

private def primeGapCertBatch36_761 : PrimeCertificate :=
  .lucas 761 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.nil))))))

private def primeGapCertBatch36_769 : PrimeCertificate :=
  .lucas 769 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.nil))))))))))

private def primeGapCertBatch36_773 : PrimeCertificate :=
  .lucas 773 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_193 (.nil))))

private def primeGapCertBatch36_797 : PrimeCertificate :=
  .lucas 797 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_199 (.nil))))

private def primeGapCertBatch36_809 : PrimeCertificate :=
  .lucas 809 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_101 (.nil)))))

private def primeGapCertBatch36_811 : PrimeCertificate :=
  .lucas 811 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil)))))))

private def primeGapCertBatch36_821 : PrimeCertificate :=
  .lucas 821 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_41 (.nil)))))

private def primeGapCertBatch36_823 : PrimeCertificate :=
  .lucas 823 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_137 (.nil))))

private def primeGapCertBatch36_853 : PrimeCertificate :=
  .lucas 853 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_71 (.nil)))))

private def primeGapCertBatch36_857 : PrimeCertificate :=
  .lucas 857 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_107 (.nil)))))

private def primeGapCertBatch36_887 : PrimeCertificate :=
  .lucas 887 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_443 (.nil)))

private def primeGapCertBatch36_907 : PrimeCertificate :=
  .lucas 907 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_151 (.nil))))

private def primeGapCertBatch36_911 : PrimeCertificate :=
  .lucas 911 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.nil)))))

private def primeGapCertBatch36_929 : PrimeCertificate :=
  .lucas 929 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.nil)))))))

private def primeGapCertBatch36_937 : PrimeCertificate :=
  .lucas 937 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.nil)))))))

private def primeGapCertBatch36_941 : PrimeCertificate :=
  .lucas 941 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_47 (.nil)))))

private def primeGapCertBatch36_947 : PrimeCertificate :=
  .lucas 947 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_43 (.nil))))

private def primeGapCertBatch36_953 : PrimeCertificate :=
  .lucas 953 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.nil))))))

private def primeGapCertBatch36_967 : PrimeCertificate :=
  .lucas 967 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.nil)))))

private def primeGapCertBatch36_971 : PrimeCertificate :=
  .lucas 971 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_97 (.nil))))

private def primeGapCertBatch36_983 : PrimeCertificate :=
  .lucas 983 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_491 (.nil)))

private def primeGapCertBatch36_991 : PrimeCertificate :=
  .lucas 991 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.nil))))))

private def primeGapCertBatch36_1009 : PrimeCertificate :=
  .lucas 1009 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.nil))))))))

private def primeGapCertBatch36_1013 : PrimeCertificate :=
  .lucas 1013 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_23 (.nil)))))

private def primeGapCertBatch36_1019 : PrimeCertificate :=
  .lucas 1019 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_509 (.nil)))

private def primeGapCertBatch36_1021 : PrimeCertificate :=
  .lucas 1021 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.nil))))))

private def primeGapCertBatch36_1031 : PrimeCertificate :=
  .lucas 1031 14 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_103 (.nil))))

private def primeGapCertBatch36_1033 : PrimeCertificate :=
  .lucas 1033 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_43 (.nil))))))

private def primeGapCertBatch36_1039 : PrimeCertificate :=
  .lucas 1039 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_173 (.nil))))

private def primeGapCertBatch36_1049 : PrimeCertificate :=
  .lucas 1049 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_131 (.nil)))))

private def primeGapCertBatch36_1051 : PrimeCertificate :=
  .lucas 1051 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.nil))))))

private def primeGapCertBatch36_1063 : PrimeCertificate :=
  .lucas 1063 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_59 (.nil)))))

private def primeGapCertBatch36_1069 : PrimeCertificate :=
  .lucas 1069 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_89 (.nil)))))

private def primeGapCertBatch36_1091 : PrimeCertificate :=
  .lucas 1091 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_109 (.nil))))

private def primeGapCertBatch36_1097 : PrimeCertificate :=
  .lucas 1097 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_137 (.nil)))))

private def primeGapCertBatch36_1103 : PrimeCertificate :=
  .lucas 1103 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_29 (.nil))))

private def primeGapCertBatch36_1109 : PrimeCertificate :=
  .lucas 1109 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_277 (.nil))))

private def primeGapCertBatch36_1201 : PrimeCertificate :=
  .lucas 1201 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.nil))))))))

private def primeGapCertBatch36_1213 : PrimeCertificate :=
  .lucas 1213 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_101 (.nil)))))

private def primeGapCertBatch36_1217 : PrimeCertificate :=
  .lucas 1217 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.nil))))))))

private def primeGapCertBatch36_1229 : PrimeCertificate :=
  .lucas 1229 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_307 (.nil))))

private def primeGapCertBatch36_1231 : PrimeCertificate :=
  .lucas 1231 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_41 (.nil)))))

private def primeGapCertBatch36_1249 : PrimeCertificate :=
  .lucas 1249 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.nil))))))))

private def primeGapCertBatch36_1259 : PrimeCertificate :=
  .lucas 1259 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_37 (.nil))))

private def primeGapCertBatch36_1291 : PrimeCertificate :=
  .lucas 1291 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_43 (.nil)))))

private def primeGapCertBatch36_1297 : PrimeCertificate :=
  .lucas 1297 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.nil)))))))))

private def primeGapCertBatch36_1301 : PrimeCertificate :=
  .lucas 1301 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.nil))))))

private def primeGapCertBatch36_1321 : PrimeCertificate :=
  .lucas 1321 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.nil)))))))

private def primeGapCertBatch36_1327 : PrimeCertificate :=
  .lucas 1327 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_17 (.nil)))))

private def primeGapCertBatch36_1367 : PrimeCertificate :=
  .lucas 1367 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_683 (.nil)))

private def primeGapCertBatch36_1373 : PrimeCertificate :=
  .lucas 1373 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.nil))))))

private def primeGapCertBatch36_1409 : PrimeCertificate :=
  .lucas 1409 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.nil)))))))))

private def primeGapCertBatch36_1429 : PrimeCertificate :=
  .lucas 1429 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.nil))))))

private def primeGapCertBatch36_1433 : PrimeCertificate :=
  .lucas 1433 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_179 (.nil)))))

private def primeGapCertBatch36_1453 : PrimeCertificate :=
  .lucas 1453 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_11 (.nil))))))

private def primeGapCertBatch36_1459 : PrimeCertificate :=
  .lucas 1459 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.nil))))))))

private def primeGapCertBatch36_1481 : PrimeCertificate :=
  .lucas 1481 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_37 (.nil))))))

private def primeGapCertBatch36_1487 : PrimeCertificate :=
  .lucas 1487 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_743 (.nil)))

private def primeGapCertBatch36_1489 : PrimeCertificate :=
  .lucas 1489 14 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_31 (.nil)))))))

private def primeGapCertBatch36_1493 : PrimeCertificate :=
  .lucas 1493 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_373 (.nil))))

private def primeGapCertBatch36_1499 : PrimeCertificate :=
  .lucas 1499 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_107 (.nil))))

private def primeGapCertBatch36_1511 : PrimeCertificate :=
  .lucas 1511 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_151 (.nil))))

private def primeGapCertBatch36_1523 : PrimeCertificate :=
  .lucas 1523 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_761 (.nil)))

private def primeGapCertBatch36_1543 : PrimeCertificate :=
  .lucas 1543 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_257 (.nil))))

private def primeGapCertBatch36_1553 : PrimeCertificate :=
  .lucas 1553 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_97 (.nil))))))

private def primeGapCertBatch36_1559 : PrimeCertificate :=
  .lucas 1559 19 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_41 (.nil))))

private def primeGapCertBatch36_1579 : PrimeCertificate :=
  .lucas 1579 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_263 (.nil))))

private def primeGapCertBatch36_1583 : PrimeCertificate :=
  .lucas 1583 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_113 (.nil))))

private def primeGapCertBatch36_1597 : PrimeCertificate :=
  .lucas 1597 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_19 (.nil))))))

private def primeGapCertBatch36_1607 : PrimeCertificate :=
  .lucas 1607 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_73 (.nil))))

private def primeGapCertBatch36_1619 : PrimeCertificate :=
  .lucas 1619 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_809 (.nil)))

private def primeGapCertBatch36_1621 : PrimeCertificate :=
  .lucas 1621 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil))))))))

private def primeGapCertBatch36_1637 : PrimeCertificate :=
  .lucas 1637 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_409 (.nil))))

private def primeGapCertBatch36_1667 : PrimeCertificate :=
  .lucas 1667 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.nil)))))

private def primeGapCertBatch36_1697 : PrimeCertificate :=
  .lucas 1697 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_53 (.nil)))))))

private def primeGapCertBatch36_1699 : PrimeCertificate :=
  .lucas 1699 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_283 (.nil))))

private def primeGapCertBatch36_1733 : PrimeCertificate :=
  .lucas 1733 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_433 (.nil))))

private def primeGapCertBatch36_1777 : PrimeCertificate :=
  .lucas 1777 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_37 (.nil)))))))

private def primeGapCertBatch36_1783 : PrimeCertificate :=
  .lucas 1783 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.nil)))))))

private def primeGapCertBatch36_1787 : PrimeCertificate :=
  .lucas 1787 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_47 (.nil))))

private def primeGapCertBatch36_1789 : PrimeCertificate :=
  .lucas 1789 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_149 (.nil)))))

private def primeGapCertBatch36_1823 : PrimeCertificate :=
  .lucas 1823 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_911 (.nil)))

private def primeGapCertBatch36_1831 : PrimeCertificate :=
  .lucas 1831 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_61 (.nil)))))

private def primeGapCertBatch36_1847 : PrimeCertificate :=
  .lucas 1847 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_71 (.nil))))

private def primeGapCertBatch36_1867 : PrimeCertificate :=
  .lucas 1867 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_311 (.nil))))

private def primeGapCertBatch36_1871 : PrimeCertificate :=
  .lucas 1871 14 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_17 (.nil)))))

private def primeGapCertBatch36_1873 : PrimeCertificate :=
  .lucas 1873 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.nil))))))))

private def primeGapCertBatch36_1889 : PrimeCertificate :=
  .lucas 1889 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_59 (.nil)))))))

private def primeGapCertBatch36_1999 : PrimeCertificate :=
  .lucas 1999 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_37 (.nil))))))

private def primeGapCertBatch36_2011 : PrimeCertificate :=
  .lucas 2011 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_67 (.nil)))))

private def primeGapCertBatch36_2083 : PrimeCertificate :=
  .lucas 2083 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_347 (.nil))))

private def primeGapCertBatch36_2099 : PrimeCertificate :=
  .lucas 2099 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1049 (.nil)))

private def primeGapCertBatch36_2129 : PrimeCertificate :=
  .lucas 2129 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_19 (.nil)))))))

private def primeGapCertBatch36_2153 : PrimeCertificate :=
  .lucas 2153 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_269 (.nil)))))

private def primeGapCertBatch36_2203 : PrimeCertificate :=
  .lucas 2203 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_367 (.nil))))

private def primeGapCertBatch36_2213 : PrimeCertificate :=
  .lucas 2213 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_79 (.nil)))))

private def primeGapCertBatch36_2243 : PrimeCertificate :=
  .lucas 2243 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_59 (.nil))))

private def primeGapCertBatch36_2287 : PrimeCertificate :=
  .lucas 2287 19 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_127 (.nil)))))

private def primeGapCertBatch36_2293 : PrimeCertificate :=
  .lucas 2293 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_191 (.nil)))))

private def primeGapCertBatch36_2339 : PrimeCertificate :=
  .lucas 2339 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_167 (.nil))))

private def primeGapCertBatch36_2347 : PrimeCertificate :=
  .lucas 2347 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_23 (.nil)))))

private def primeGapCertBatch36_2417 : PrimeCertificate :=
  .lucas 2417 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_151 (.nil))))))

private def primeGapCertBatch36_2437 : PrimeCertificate :=
  .lucas 2437 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_29 (.nil))))))

private def primeGapCertBatch36_2459 : PrimeCertificate :=
  .lucas 2459 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1229 (.nil)))

private def primeGapCertBatch36_2467 : PrimeCertificate :=
  .lucas 2467 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_137 (.nil)))))

private def primeGapCertBatch36_2503 : PrimeCertificate :=
  .lucas 2503 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_139 (.nil)))))

private def primeGapCertBatch36_2521 : PrimeCertificate :=
  .lucas 2521 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.nil))))))))

private def primeGapCertBatch36_2539 : PrimeCertificate :=
  .lucas 2539 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_47 (.nil))))))

private def primeGapCertBatch36_2543 : PrimeCertificate :=
  .lucas 2543 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_41 (.nil))))

private def primeGapCertBatch36_2633 : PrimeCertificate :=
  .lucas 2633 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_47 (.nil))))))

private def primeGapCertBatch36_2663 : PrimeCertificate :=
  .lucas 2663 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_11 (.nil)))))

private def primeGapCertBatch36_2671 : PrimeCertificate :=
  .lucas 2671 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_89 (.nil)))))

private def primeGapCertBatch36_2677 : PrimeCertificate :=
  .lucas 2677 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_223 (.nil)))))

private def primeGapCertBatch36_2683 : PrimeCertificate :=
  .lucas 2683 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_149 (.nil)))))

private def primeGapCertBatch36_2687 : PrimeCertificate :=
  .lucas 2687 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_79 (.nil))))

private def primeGapCertBatch36_2699 : PrimeCertificate :=
  .lucas 2699 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_71 (.nil))))

private def primeGapCertBatch36_2707 : PrimeCertificate :=
  .lucas 2707 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_41 (.nil)))))

private def primeGapCertBatch36_2741 : PrimeCertificate :=
  .lucas 2741 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_137 (.nil)))))

private def primeGapCertBatch36_2753 : PrimeCertificate :=
  .lucas 2753 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_43 (.nil))))))))

private def primeGapCertBatch36_2789 : PrimeCertificate :=
  .lucas 2789 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_41 (.nil)))))

private def primeGapCertBatch36_2843 : PrimeCertificate :=
  .lucas 2843 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_29 (.nil)))))

private def primeGapCertBatch36_2851 : PrimeCertificate :=
  .lucas 2851 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.nil))))))

private def primeGapCertBatch36_2927 : PrimeCertificate :=
  .lucas 2927 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_19 (.nil)))))

private def primeGapCertBatch36_2939 : PrimeCertificate :=
  .lucas 2939 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_113 (.nil))))

private def primeGapCertBatch36_2963 : PrimeCertificate :=
  .lucas 2963 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1481 (.nil)))

private def primeGapCertBatch36_2969 : PrimeCertificate :=
  .lucas 2969 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_53 (.nil))))))

private def primeGapCertBatch36_3011 : PrimeCertificate :=
  .lucas 3011 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_43 (.nil)))))

private def primeGapCertBatch36_3023 : PrimeCertificate :=
  .lucas 3023 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1511 (.nil)))

private def primeGapCertBatch36_3061 : PrimeCertificate :=
  .lucas 3061 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.nil)))))))

private def primeGapCertBatch36_3067 : PrimeCertificate :=
  .lucas 3067 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_73 (.nil)))))

private def primeGapCertBatch36_3109 : PrimeCertificate :=
  .lucas 3109 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_37 (.nil))))))

private def primeGapCertBatch36_3119 : PrimeCertificate :=
  .lucas 3119 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1559 (.nil)))

private def primeGapCertBatch36_3167 : PrimeCertificate :=
  .lucas 3167 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1583 (.nil)))

private def primeGapCertBatch36_3169 : PrimeCertificate :=
  .lucas 3169 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.nil)))))))))

private def primeGapCertBatch36_3259 : PrimeCertificate :=
  .lucas 3259 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_181 (.nil)))))

private def primeGapCertBatch36_3307 : PrimeCertificate :=
  .lucas 3307 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_29 (.nil)))))

private def primeGapCertBatch36_3323 : PrimeCertificate :=
  .lucas 3323 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_151 (.nil))))

private def primeGapCertBatch36_3361 : PrimeCertificate :=
  .lucas 3361 22 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.nil)))))))))

private def primeGapCertBatch36_3373 : PrimeCertificate :=
  .lucas 3373 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_281 (.nil)))))

private def primeGapCertBatch36_3413 : PrimeCertificate :=
  .lucas 3413 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_853 (.nil))))

private def primeGapCertBatch36_3469 : PrimeCertificate :=
  .lucas 3469 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_17 (.nil))))))

private def primeGapCertBatch36_3491 : PrimeCertificate :=
  .lucas 3491 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_349 (.nil))))

private def primeGapCertBatch36_3527 : PrimeCertificate :=
  .lucas 3527 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_43 (.nil))))

private def primeGapCertBatch36_3529 : PrimeCertificate :=
  .lucas 3529 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.nil))))))))

private def primeGapCertBatch36_3541 : PrimeCertificate :=
  .lucas 3541 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_59 (.nil))))))

private def primeGapCertBatch36_3571 : PrimeCertificate :=
  .lucas 3571 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.nil))))))

private def primeGapCertBatch36_3607 : PrimeCertificate :=
  .lucas 3607 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_601 (.nil))))

private def primeGapCertBatch36_3613 : PrimeCertificate :=
  .lucas 3613 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_43 (.nil))))))

private def primeGapCertBatch36_3643 : PrimeCertificate :=
  .lucas 3643 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_607 (.nil))))

private def primeGapCertBatch36_3673 : PrimeCertificate :=
  .lucas 3673 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.nil))))))))

private def primeGapCertBatch36_3761 : PrimeCertificate :=
  .lucas 3761 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_47 (.nil)))))))

private def primeGapCertBatch36_3767 : PrimeCertificate :=
  .lucas 3767 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_269 (.nil))))

private def primeGapCertBatch36_3779 : PrimeCertificate :=
  .lucas 3779 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1889 (.nil)))

private def primeGapCertBatch36_3793 : PrimeCertificate :=
  .lucas 3793 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_79 (.nil)))))))

private def primeGapCertBatch36_3847 : PrimeCertificate :=
  .lucas 3847 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_641 (.nil))))

private def primeGapCertBatch36_3907 : PrimeCertificate :=
  .lucas 3907 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_31 (.nil))))))

private def primeGapCertBatch36_3923 : PrimeCertificate :=
  .lucas 3923 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_53 (.nil))))

private def primeGapCertBatch36_3931 : PrimeCertificate :=
  .lucas 3931 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_131 (.nil)))))

private def primeGapCertBatch36_4001 : PrimeCertificate :=
  .lucas 4001 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.nil)))))))))

private def primeGapCertBatch36_4027 : PrimeCertificate :=
  .lucas 4027 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_61 (.nil)))))

private def primeGapCertBatch36_4073 : PrimeCertificate :=
  .lucas 4073 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_509 (.nil)))))

private def primeGapCertBatch36_4153 : PrimeCertificate :=
  .lucas 4153 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_173 (.nil))))))

private def primeGapCertBatch36_4157 : PrimeCertificate :=
  .lucas 4157 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1039 (.nil))))

private def primeGapCertBatch36_4211 : PrimeCertificate :=
  .lucas 4211 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_421 (.nil))))

private def primeGapCertBatch36_4219 : PrimeCertificate :=
  .lucas 4219 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_37 (.nil)))))

private def primeGapCertBatch36_4253 : PrimeCertificate :=
  .lucas 4253 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1063 (.nil))))

private def primeGapCertBatch36_4259 : PrimeCertificate :=
  .lucas 4259 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2129 (.nil)))

private def primeGapCertBatch36_4273 : PrimeCertificate :=
  .lucas 4273 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_89 (.nil)))))))

private def primeGapCertBatch36_4457 : PrimeCertificate :=
  .lucas 4457 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_557 (.nil)))))

private def primeGapCertBatch36_4463 : PrimeCertificate :=
  .lucas 4463 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_97 (.nil))))

private def primeGapCertBatch36_4583 : PrimeCertificate :=
  .lucas 4583 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_79 (.nil))))

private def primeGapCertBatch36_4673 : PrimeCertificate :=
  .lucas 4673 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_73 (.nil))))))))

private def primeGapCertBatch36_4679 : PrimeCertificate :=
  .lucas 4679 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2339 (.nil)))

private def primeGapCertBatch36_4759 : PrimeCertificate :=
  .lucas 4759 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_61 (.nil)))))

private def primeGapCertBatch36_4861 : PrimeCertificate :=
  .lucas 4861 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil)))))))))

private def primeGapCertBatch36_4919 : PrimeCertificate :=
  .lucas 4919 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2459 (.nil)))

private def primeGapCertBatch36_4931 : PrimeCertificate :=
  .lucas 4931 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_29 (.nil)))))

private def primeGapCertBatch36_4951 : PrimeCertificate :=
  .lucas 4951 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.nil)))))))

private def primeGapCertBatch36_4993 : PrimeCertificate :=
  .lucas 4993 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.nil))))))))))

private def primeGapCertBatch36_4999 : PrimeCertificate :=
  .lucas 4999 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.nil))))))

private def primeGapCertBatch36_5003 : PrimeCertificate :=
  .lucas 5003 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_61 (.nil))))

private def primeGapCertBatch36_5051 : PrimeCertificate :=
  .lucas 5051 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_101 (.nil)))))

private def primeGapCertBatch36_5119 : PrimeCertificate :=
  .lucas 5119 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_853 (.nil))))

private def primeGapCertBatch36_5153 : PrimeCertificate :=
  .lucas 5153 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.nil))))))))

private def primeGapCertBatch36_5171 : PrimeCertificate :=
  .lucas 5171 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_47 (.nil)))))

private def primeGapCertBatch36_5273 : PrimeCertificate :=
  .lucas 5273 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_659 (.nil)))))

private def primeGapCertBatch36_5281 : PrimeCertificate :=
  .lucas 5281 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.nil)))))))))

private def primeGapCertBatch36_5309 : PrimeCertificate :=
  .lucas 5309 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1327 (.nil))))

private def primeGapCertBatch36_5323 : PrimeCertificate :=
  .lucas 5323 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_887 (.nil))))

private def primeGapCertBatch36_5333 : PrimeCertificate :=
  .lucas 5333 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_43 (.nil)))))

private def primeGapCertBatch36_5347 : PrimeCertificate :=
  .lucas 5347 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.nil))))))))

private def primeGapCertBatch36_5399 : PrimeCertificate :=
  .lucas 5399 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2699 (.nil)))

private def primeGapCertBatch36_5407 : PrimeCertificate :=
  .lucas 5407 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_53 (.nil)))))

private def primeGapCertBatch36_5413 : PrimeCertificate :=
  .lucas 5413 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_41 (.nil))))))

private def primeGapCertBatch36_5437 : PrimeCertificate :=
  .lucas 5437 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_151 (.nil))))))

private def primeGapCertBatch36_5449 : PrimeCertificate :=
  .lucas 5449 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_227 (.nil))))))

private def primeGapCertBatch36_5483 : PrimeCertificate :=
  .lucas 5483 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2741 (.nil)))

private def primeGapCertBatch36_5503 : PrimeCertificate :=
  .lucas 5503 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_131 (.nil)))))

private def primeGapCertBatch36_5507 : PrimeCertificate :=
  .lucas 5507 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2753 (.nil)))

private def primeGapCertBatch36_5531 : PrimeCertificate :=
  .lucas 5531 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_79 (.nil)))))

private def primeGapCertBatch36_5737 : PrimeCertificate :=
  .lucas 5737 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_239 (.nil))))))

private def primeGapCertBatch36_5783 : PrimeCertificate :=
  .lucas 5783 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_59 (.nil)))))

private def primeGapCertBatch36_5813 : PrimeCertificate :=
  .lucas 5813 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1453 (.nil))))

private def primeGapCertBatch36_5939 : PrimeCertificate :=
  .lucas 5939 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2969 (.nil)))

private def primeGapCertBatch36_6079 : PrimeCertificate :=
  .lucas 6079 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1013 (.nil))))

private def primeGapCertBatch36_6247 : PrimeCertificate :=
  .lucas 6247 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_347 (.nil)))))

private def primeGapCertBatch36_6287 : PrimeCertificate :=
  .lucas 6287 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_449 (.nil))))

private def primeGapCertBatch36_6473 : PrimeCertificate :=
  .lucas 6473 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_809 (.nil)))))

private def primeGapCertBatch36_6481 : PrimeCertificate :=
  .lucas 6481 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil))))))))))

private def primeGapCertBatch36_6491 : PrimeCertificate :=
  .lucas 6491 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_59 (.nil)))))

private def primeGapCertBatch36_6691 : PrimeCertificate :=
  .lucas 6691 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_223 (.nil)))))

private def primeGapCertBatch36_6763 : PrimeCertificate :=
  .lucas 6763 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.nil))))))

private def primeGapCertBatch36_6781 : PrimeCertificate :=
  .lucas 6781 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_113 (.nil))))))

private def primeGapCertBatch36_6833 : PrimeCertificate :=
  .lucas 6833 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_61 (.nil)))))))

private def primeGapCertBatch36_6983 : PrimeCertificate :=
  .lucas 6983 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3491 (.nil)))

private def primeGapCertBatch36_7039 : PrimeCertificate :=
  .lucas 7039 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_23 (.nil))))))

private def primeGapCertBatch36_7103 : PrimeCertificate :=
  .lucas 7103 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_67 (.nil))))

private def primeGapCertBatch36_7193 : PrimeCertificate :=
  .lucas 7193 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_31 (.nil))))))

private def primeGapCertBatch36_7207 : PrimeCertificate :=
  .lucas 7207 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1201 (.nil))))

private def primeGapCertBatch36_7433 : PrimeCertificate :=
  .lucas 7433 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_929 (.nil)))))

private def primeGapCertBatch36_7487 : PrimeCertificate :=
  .lucas 7487 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_197 (.nil))))

private def primeGapCertBatch36_7573 : PrimeCertificate :=
  .lucas 7573 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_631 (.nil)))))

private def primeGapCertBatch36_7649 : PrimeCertificate :=
  .lucas 7649 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_239 (.nil)))))))

private def primeGapCertBatch36_7717 : PrimeCertificate :=
  .lucas 7717 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_643 (.nil)))))

private def primeGapCertBatch36_7723 : PrimeCertificate :=
  .lucas 7723 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_13 (.nil)))))))

private def primeGapCertBatch36_7753 : PrimeCertificate :=
  .lucas 7753 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_19 (.nil)))))))

private def primeGapCertBatch36_7841 : PrimeCertificate :=
  .lucas 7841 12 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.nil)))))))))

private def primeGapCertBatch36_7937 : PrimeCertificate :=
  .lucas 7937 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_31 (.nil))))))))))

private def primeGapCertBatch36_8221 : PrimeCertificate :=
  .lucas 8221 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_137 (.nil))))))

private def primeGapCertBatch36_8353 : PrimeCertificate :=
  .lucas 8353 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.nil)))))))))

private def primeGapCertBatch36_8389 : PrimeCertificate :=
  .lucas 8389 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_233 (.nil))))))

private def primeGapCertBatch36_8423 : PrimeCertificate :=
  .lucas 8423 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4211 (.nil)))

private def primeGapCertBatch36_8741 : PrimeCertificate :=
  .lucas 8741 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_23 (.nil))))))

private def primeGapCertBatch36_9221 : PrimeCertificate :=
  .lucas 9221 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_461 (.nil)))))

private def primeGapCertBatch36_9227 : PrimeCertificate :=
  .lucas 9227 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_659 (.nil))))

private def primeGapCertBatch36_9239 : PrimeCertificate :=
  .lucas 9239 19 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_149 (.nil))))

private def primeGapCertBatch36_9293 : PrimeCertificate :=
  .lucas 9293 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_101 (.nil)))))

private def primeGapCertBatch36_9343 : PrimeCertificate :=
  .lucas 9343 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_173 (.nil))))))

private def primeGapCertBatch36_9349 : PrimeCertificate :=
  .lucas 9349 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_41 (.nil))))))

private def primeGapCertBatch36_9371 : PrimeCertificate :=
  .lucas 9371 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_937 (.nil))))

private def primeGapCertBatch36_9473 : PrimeCertificate :=
  .lucas 9473 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_37 (.nil))))))))))

private def primeGapCertBatch36_9491 : PrimeCertificate :=
  .lucas 9491 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_73 (.nil)))))

private def primeGapCertBatch36_9643 : PrimeCertificate :=
  .lucas 9643 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1607 (.nil))))

private def primeGapCertBatch36_9677 : PrimeCertificate :=
  .lucas 9677 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_59 (.nil)))))

private def primeGapCertBatch36_9923 : PrimeCertificate :=
  .lucas 9923 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_41 (.nil)))))

private def primeGapCertBatch36_10037 : PrimeCertificate :=
  .lucas 10037 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_193 (.nil)))))

private def primeGapCertBatch36_10103 : PrimeCertificate :=
  .lucas 10103 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5051 (.nil)))

private def primeGapCertBatch36_10321 : PrimeCertificate :=
  .lucas 10321 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_43 (.nil))))))))

private def primeGapCertBatch36_10331 : PrimeCertificate :=
  .lucas 10331 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1033 (.nil))))

private def primeGapCertBatch36_10337 : PrimeCertificate :=
  .lucas 10337 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_19 (.nil))))))))

private def primeGapCertBatch36_10343 : PrimeCertificate :=
  .lucas 10343 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5171 (.nil)))

private def primeGapCertBatch36_10499 : PrimeCertificate :=
  .lucas 10499 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_181 (.nil))))

private def primeGapCertBatch36_10567 : PrimeCertificate :=
  .lucas 10567 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_587 (.nil)))))

private def primeGapCertBatch36_10691 : PrimeCertificate :=
  .lucas 10691 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1069 (.nil))))

private def primeGapCertBatch36_10733 : PrimeCertificate :=
  .lucas 10733 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2683 (.nil))))

private def primeGapCertBatch36_10799 : PrimeCertificate :=
  .lucas 10799 19 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5399 (.nil)))

private def primeGapCertBatch36_11071 : PrimeCertificate :=
  .lucas 11071 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_41 (.nil)))))))

private def primeGapCertBatch36_11083 : PrimeCertificate :=
  .lucas 11083 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1847 (.nil))))

private def primeGapCertBatch36_11117 : PrimeCertificate :=
  .lucas 11117 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_397 (.nil)))))

private def primeGapCertBatch36_11317 : PrimeCertificate :=
  .lucas 11317 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_41 (.nil))))))

private def primeGapCertBatch36_11447 : PrimeCertificate :=
  .lucas 11447 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_97 (.nil))))

private def primeGapCertBatch36_11833 : PrimeCertificate :=
  .lucas 11833 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_29 (.nil)))))))

private def primeGapCertBatch36_11867 : PrimeCertificate :=
  .lucas 11867 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_349 (.nil))))

private def primeGapCertBatch36_11887 : PrimeCertificate :=
  .lucas 11887 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_283 (.nil)))))

private def primeGapCertBatch36_11927 : PrimeCertificate :=
  .lucas 11927 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_67 (.cons primeGapCertBatch36_89 (.nil))))

private def primeGapCertBatch36_12161 : PrimeCertificate :=
  .lucas 12161 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.nil))))))))))

private def primeGapCertBatch36_12301 : PrimeCertificate :=
  .lucas 12301 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_41 (.nil)))))))

private def primeGapCertBatch36_12329 : PrimeCertificate :=
  .lucas 12329 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_67 (.nil))))))

private def primeGapCertBatch36_12421 : PrimeCertificate :=
  .lucas 12421 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_23 (.nil))))))))

private def primeGapCertBatch36_12473 : PrimeCertificate :=
  .lucas 12473 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1559 (.nil)))))

private def primeGapCertBatch36_12611 : PrimeCertificate :=
  .lucas 12611 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_97 (.nil)))))

private def primeGapCertBatch36_12713 : PrimeCertificate :=
  .lucas 12713 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_227 (.nil))))))

private def primeGapCertBatch36_12781 : PrimeCertificate :=
  .lucas 12781 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_71 (.nil)))))))

private def primeGapCertBatch36_12841 : PrimeCertificate :=
  .lucas 12841 21 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_107 (.nil)))))))

private def primeGapCertBatch36_12953 : PrimeCertificate :=
  .lucas 12953 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1619 (.nil)))))

private def primeGapCertBatch36_13241 : PrimeCertificate :=
  .lucas 13241 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_331 (.nil))))))

private def primeGapCertBatch36_13613 : PrimeCertificate :=
  .lucas 13613 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_83 (.nil)))))

private def primeGapCertBatch36_13789 : PrimeCertificate :=
  .lucas 13789 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_383 (.nil))))))

private def primeGapCertBatch36_13831 : PrimeCertificate :=
  .lucas 13831 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_461 (.nil)))))

private def primeGapCertBatch36_13877 : PrimeCertificate :=
  .lucas 13877 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3469 (.nil))))

private def primeGapCertBatch36_13883 : PrimeCertificate :=
  .lucas 13883 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_631 (.nil))))

private def primeGapCertBatch36_13967 : PrimeCertificate :=
  .lucas 13967 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_6983 (.nil)))

private def primeGapCertBatch36_14221 : PrimeCertificate :=
  .lucas 14221 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_79 (.nil)))))))

private def primeGapCertBatch36_14387 : PrimeCertificate :=
  .lucas 14387 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7193 (.nil)))

private def primeGapCertBatch36_14669 : PrimeCertificate :=
  .lucas 14669 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_193 (.nil)))))

private def primeGapCertBatch36_14713 : PrimeCertificate :=
  .lucas 14713 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_613 (.nil))))))

private def primeGapCertBatch36_14779 : PrimeCertificate :=
  .lucas 14779 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_821 (.nil)))))

private def primeGapCertBatch36_14851 : PrimeCertificate :=
  .lucas 14851 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.nil))))))))

private def primeGapCertBatch36_15569 : PrimeCertificate :=
  .lucas 15569 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_139 (.nil)))))))

private def primeGapCertBatch36_15971 : PrimeCertificate :=
  .lucas 15971 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1597 (.nil))))

private def primeGapCertBatch36_16253 : PrimeCertificate :=
  .lucas 16253 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_239 (.nil)))))

private def primeGapCertBatch36_16361 : PrimeCertificate :=
  .lucas 16361 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_409 (.nil))))))

private def primeGapCertBatch36_16433 : PrimeCertificate :=
  .lucas 16433 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_79 (.nil)))))))

private def primeGapCertBatch36_16477 : PrimeCertificate :=
  .lucas 16477 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1373 (.nil)))))

private def primeGapCertBatch36_16927 : PrimeCertificate :=
  .lucas 16927 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_31 (.nil))))))

private def primeGapCertBatch36_17099 : PrimeCertificate :=
  .lucas 17099 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_103 (.nil))))

private def primeGapCertBatch36_17729 : PrimeCertificate :=
  .lucas 17729 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_277 (.nil))))))))

private def primeGapCertBatch36_17737 : PrimeCertificate :=
  .lucas 17737 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_739 (.nil))))))

private def primeGapCertBatch36_17837 : PrimeCertificate :=
  .lucas 17837 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.nil)))))))

private def primeGapCertBatch36_17921 : PrimeCertificate :=
  .lucas 17921 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.nil))))))))))))

private def primeGapCertBatch36_18061 : PrimeCertificate :=
  .lucas 18061 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_43 (.nil)))))))

private def primeGapCertBatch36_18287 : PrimeCertificate :=
  .lucas 18287 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_223 (.nil))))

private def primeGapCertBatch36_18341 : PrimeCertificate :=
  .lucas 18341 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_131 (.nil))))))

private def primeGapCertBatch36_18493 : PrimeCertificate :=
  .lucas 18493 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_67 (.nil))))))

private def primeGapCertBatch36_18517 : PrimeCertificate :=
  .lucas 18517 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1543 (.nil)))))

private def primeGapCertBatch36_18701 : PrimeCertificate :=
  .lucas 18701 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_17 (.nil)))))))

private def primeGapCertBatch36_18947 : PrimeCertificate :=
  .lucas 18947 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_9473 (.nil)))

private def primeGapCertBatch36_19073 : PrimeCertificate :=
  .lucas 19073 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_149 (.nil)))))))))

private def primeGapCertBatch36_19973 : PrimeCertificate :=
  .lucas 19973 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4993 (.nil))))

private def primeGapCertBatch36_20101 : PrimeCertificate :=
  .lucas 20101 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_67 (.nil)))))))

private def primeGapCertBatch36_20269 : PrimeCertificate :=
  .lucas 20269 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_563 (.nil))))))

private def primeGapCertBatch36_20693 : PrimeCertificate :=
  .lucas 20693 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_739 (.nil)))))

private def primeGapCertBatch36_21313 : PrimeCertificate :=
  .lucas 21313 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_37 (.nil))))))))))

private def primeGapCertBatch36_21377 : PrimeCertificate :=
  .lucas 21377 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_167 (.nil)))))))))

private def primeGapCertBatch36_21379 : PrimeCertificate :=
  .lucas 21379 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_509 (.nil)))))

private def primeGapCertBatch36_21383 : PrimeCertificate :=
  .lucas 21383 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_10691 (.nil)))

private def primeGapCertBatch36_21467 : PrimeCertificate :=
  .lucas 21467 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_10733 (.nil)))

private def primeGapCertBatch36_21601 : PrimeCertificate :=
  .lucas 21601 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.nil)))))))))))

private def primeGapCertBatch36_21673 : PrimeCertificate :=
  .lucas 21673 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_43 (.nil))))))))

private def primeGapCertBatch36_21863 : PrimeCertificate :=
  .lucas 21863 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_643 (.nil))))

private def primeGapCertBatch36_22031 : PrimeCertificate :=
  .lucas 22031 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_2203 (.nil))))

private def primeGapCertBatch36_22453 : PrimeCertificate :=
  .lucas 22453 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1871 (.nil)))))

private def primeGapCertBatch36_22567 : PrimeCertificate :=
  .lucas 22567 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3761 (.nil))))

private def primeGapCertBatch36_23053 : PrimeCertificate :=
  .lucas 23053 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_113 (.nil))))))

private def primeGapCertBatch36_23539 : PrimeCertificate :=
  .lucas 23539 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3923 (.nil))))

private def primeGapCertBatch36_23887 : PrimeCertificate :=
  .lucas 23887 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1327 (.nil)))))

private def primeGapCertBatch36_23971 : PrimeCertificate :=
  .lucas 23971 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_47 (.nil))))))

private def primeGapCertBatch36_24091 : PrimeCertificate :=
  .lucas 24091 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_73 (.nil))))))

private def primeGapCertBatch36_24113 : PrimeCertificate :=
  .lucas 24113 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_137 (.nil)))))))

private def primeGapCertBatch36_24223 : PrimeCertificate :=
  .lucas 24223 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_367 (.nil)))))

private def primeGapCertBatch36_24251 : PrimeCertificate :=
  .lucas 24251 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_97 (.nil))))))

private def primeGapCertBatch36_24337 : PrimeCertificate :=
  .lucas 24337 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_13 (.nil)))))))))

private def primeGapCertBatch36_24371 : PrimeCertificate :=
  .lucas 24371 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_2437 (.nil))))

private def primeGapCertBatch36_24439 : PrimeCertificate :=
  .lucas 24439 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_4073 (.nil))))

private def primeGapCertBatch36_24683 : PrimeCertificate :=
  .lucas 24683 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_43 (.nil)))))

private def primeGapCertBatch36_24691 : PrimeCertificate :=
  .lucas 24691 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_823 (.nil)))))

private def primeGapCertBatch36_24979 : PrimeCertificate :=
  .lucas 24979 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_181 (.nil)))))

private def primeGapCertBatch36_24989 : PrimeCertificate :=
  .lucas 24989 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_6247 (.nil))))

private def primeGapCertBatch36_25309 : PrimeCertificate :=
  .lucas 25309 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_37 (.nil)))))))

private def primeGapCertBatch36_25423 : PrimeCertificate :=
  .lucas 25423 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_223 (.nil)))))

private def primeGapCertBatch36_27073 : PrimeCertificate :=
  .lucas 27073 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_47 (.nil))))))))))

private def primeGapCertBatch36_27241 : PrimeCertificate :=
  .lucas 27241 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_227 (.nil)))))))

private def primeGapCertBatch36_28411 : PrimeCertificate :=
  .lucas 28411 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_947 (.nil)))))

private def primeGapCertBatch36_28663 : PrimeCertificate :=
  .lucas 28663 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_281 (.nil)))))

private def primeGapCertBatch36_29063 : PrimeCertificate :=
  .lucas 29063 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_1321 (.nil))))

private def primeGapCertBatch36_29179 : PrimeCertificate :=
  .lucas 29179 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1621 (.nil)))))

private def primeGapCertBatch36_29339 : PrimeCertificate :=
  .lucas 29339 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_14669 (.nil)))

private def primeGapCertBatch36_29581 : PrimeCertificate :=
  .lucas 29581 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_29 (.nil)))))))

private def primeGapCertBatch36_29833 : PrimeCertificate :=
  .lucas 29833 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_113 (.nil)))))))

private def primeGapCertBatch36_30137 : PrimeCertificate :=
  .lucas 30137 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3767 (.nil)))))

private def primeGapCertBatch36_31513 : PrimeCertificate :=
  .lucas 31513 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_101 (.nil)))))))

private def primeGapCertBatch36_32569 : PrimeCertificate :=
  .lucas 32569 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_59 (.nil)))))))

private def primeGapCertBatch36_33071 : PrimeCertificate :=
  .lucas 33071 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3307 (.nil))))

private def primeGapCertBatch36_33073 : PrimeCertificate :=
  .lucas 33073 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_53 (.nil))))))))

private def primeGapCertBatch36_35281 : PrimeCertificate :=
  .lucas 35281 23 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.nil))))))))))

private def primeGapCertBatch36_35603 : PrimeCertificate :=
  .lucas 35603 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_2543 (.nil))))

private def primeGapCertBatch36_35977 : PrimeCertificate :=
  .lucas 35977 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1499 (.nil))))))

private def primeGapCertBatch36_36011 : PrimeCertificate :=
  .lucas 36011 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_277 (.nil)))))

private def primeGapCertBatch36_36683 : PrimeCertificate :=
  .lucas 36683 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_18341 (.nil)))

private def primeGapCertBatch36_37019 : PrimeCertificate :=
  .lucas 37019 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_223 (.nil))))

private def primeGapCertBatch36_37201 : PrimeCertificate :=
  .lucas 37201 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_31 (.nil)))))))))

private def primeGapCertBatch36_37501 : PrimeCertificate :=
  .lucas 37501 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.nil)))))))))

private def primeGapCertBatch36_38953 : PrimeCertificate :=
  .lucas 38953 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_541 (.nil)))))))

private def primeGapCertBatch36_40433 : PrimeCertificate :=
  .lucas 40433 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_19 (.nil))))))))

private def primeGapCertBatch36_41647 : PrimeCertificate :=
  .lucas 41647 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_631 (.nil)))))

private def primeGapCertBatch36_42473 : PrimeCertificate :=
  .lucas 42473 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5309 (.nil)))))

private def primeGapCertBatch36_44501 : PrimeCertificate :=
  .lucas 44501 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_89 (.nil)))))))

private def primeGapCertBatch36_45553 : PrimeCertificate :=
  .lucas 45553 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_73 (.nil))))))))

private def primeGapCertBatch36_46141 : PrimeCertificate :=
  .lucas 46141 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_769 (.nil))))))

private def primeGapCertBatch36_46751 : PrimeCertificate :=
  .lucas 46751 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_17 (.nil)))))))

private def primeGapCertBatch36_46807 : PrimeCertificate :=
  .lucas 46807 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_269 (.nil)))))

private def primeGapCertBatch36_47513 : PrimeCertificate :=
  .lucas 47513 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5939 (.nil)))))

private def primeGapCertBatch36_47591 : PrimeCertificate :=
  .lucas 47591 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_4759 (.nil))))

private def primeGapCertBatch36_47623 : PrimeCertificate :=
  .lucas 47623 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7937 (.nil))))

private def primeGapCertBatch36_49171 : PrimeCertificate :=
  .lucas 49171 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_149 (.nil))))))

private def primeGapCertBatch36_49367 : PrimeCertificate :=
  .lucas 49367 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_24683 (.nil)))

private def primeGapCertBatch36_50177 : PrimeCertificate :=
  .lucas 50177 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.nil)))))))))))))

private def primeGapCertBatch36_50539 : PrimeCertificate :=
  .lucas 50539 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_8423 (.nil))))

private def primeGapCertBatch36_51109 : PrimeCertificate :=
  .lucas 51109 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_4259 (.nil)))))

private def primeGapCertBatch36_52361 : PrimeCertificate :=
  .lucas 52361 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_17 (.nil))))))))

private def primeGapCertBatch36_53551 : PrimeCertificate :=
  .lucas 53551 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.nil))))))))

private def primeGapCertBatch36_55621 : PrimeCertificate :=
  .lucas 55621 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_103 (.nil))))))))

private def primeGapCertBatch36_55799 : PrimeCertificate :=
  .lucas 55799 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_1213 (.nil))))

private def primeGapCertBatch36_58679 : PrimeCertificate :=
  .lucas 58679 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29339 (.nil)))

private def primeGapCertBatch36_71563 : PrimeCertificate :=
  .lucas 71563 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11927 (.nil))))

private def primeGapCertBatch36_72287 : PrimeCertificate :=
  .lucas 72287 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_769 (.nil))))

private def primeGapCertBatch36_73973 : PrimeCertificate :=
  .lucas 73973 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_18493 (.nil))))

private def primeGapCertBatch36_74071 : PrimeCertificate :=
  .lucas 74071 14 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_823 (.nil))))))

private def primeGapCertBatch36_74293 : PrimeCertificate :=
  .lucas 74293 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_151 (.nil))))))

private def primeGapCertBatch36_74573 : PrimeCertificate :=
  .lucas 74573 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_103 (.cons primeGapCertBatch36_181 (.nil)))))

private def primeGapCertBatch36_74857 : PrimeCertificate :=
  .lucas 74857 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3119 (.nil))))))

private def primeGapCertBatch36_74869 : PrimeCertificate :=
  .lucas 74869 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_367 (.nil))))))

private def primeGapCertBatch36_76819 : PrimeCertificate :=
  .lucas 76819 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_59 (.nil))))))

private def primeGapCertBatch36_77167 : PrimeCertificate :=
  .lucas 77167 21 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1429 (.nil))))))

private def primeGapCertBatch36_77761 : PrimeCertificate :=
  .lucas 77761 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.nil)))))))))))))

private def primeGapCertBatch36_78059 : PrimeCertificate :=
  .lucas 78059 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_1259 (.nil))))

private def primeGapCertBatch36_78893 : PrimeCertificate :=
  .lucas 78893 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_163 (.nil))))))

private def primeGapCertBatch36_79813 : PrimeCertificate :=
  .lucas 79813 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_739 (.nil)))))))

private def primeGapCertBatch36_80917 : PrimeCertificate :=
  .lucas 80917 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_613 (.nil))))))

private def primeGapCertBatch36_80963 : PrimeCertificate :=
  .lucas 80963 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_5783 (.nil))))

private def primeGapCertBatch36_82787 : PrimeCertificate :=
  .lucas 82787 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_71 (.nil)))))

private def primeGapCertBatch36_83231 : PrimeCertificate :=
  .lucas 83231 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_41 (.nil))))))

private def primeGapCertBatch36_83891 : PrimeCertificate :=
  .lucas 83891 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_8389 (.nil))))

private def primeGapCertBatch36_85513 : PrimeCertificate :=
  .lucas 85513 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_509 (.nil)))))))

private def primeGapCertBatch36_87719 : PrimeCertificate :=
  .lucas 87719 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_719 (.nil))))

private def primeGapCertBatch36_88019 : PrimeCertificate :=
  .lucas 88019 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_6287 (.nil))))

private def primeGapCertBatch36_89003 : PrimeCertificate :=
  .lucas 89003 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_44501 (.nil)))

private def primeGapCertBatch36_90437 : PrimeCertificate :=
  .lucas 90437 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_983 (.nil)))))

private def primeGapCertBatch36_92219 : PrimeCertificate :=
  .lucas 92219 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_941 (.nil)))))

private def primeGapCertBatch36_92221 : PrimeCertificate :=
  .lucas 92221 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_53 (.nil)))))))

private def primeGapCertBatch36_93503 : PrimeCertificate :=
  .lucas 93503 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_46751 (.nil)))

private def primeGapCertBatch36_98729 : PrimeCertificate :=
  .lucas 98729 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_43 (.nil)))))))

private def primeGapCertBatch36_101653 : PrimeCertificate :=
  .lucas 101653 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_197 (.nil))))))

private def primeGapCertBatch36_101693 : PrimeCertificate :=
  .lucas 101693 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_25423 (.nil))))

private def primeGapCertBatch36_102241 : PrimeCertificate :=
  .lucas 102241 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_71 (.nil))))))))))

private def primeGapCertBatch36_105871 : PrimeCertificate :=
  .lucas 105871 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3529 (.nil)))))

private def primeGapCertBatch36_107119 : PrimeCertificate :=
  .lucas 107119 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_541 (.nil))))))

private def primeGapCertBatch36_108293 : PrimeCertificate :=
  .lucas 108293 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_27073 (.nil))))

private def primeGapCertBatch36_108923 : PrimeCertificate :=
  .lucas 108923 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_4951 (.nil))))

private def primeGapCertBatch36_108929 : PrimeCertificate :=
  .lucas 108929 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_37 (.nil))))))))))

private def primeGapCertBatch36_111103 : PrimeCertificate :=
  .lucas 111103 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_18517 (.nil))))

private def primeGapCertBatch36_119701 : PrimeCertificate :=
  .lucas 119701 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_19 (.nil)))))))))

private def primeGapCertBatch36_119839 : PrimeCertificate :=
  .lucas 119839 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19973 (.nil))))

private def primeGapCertBatch36_124981 : PrimeCertificate :=
  .lucas 124981 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_2083 (.nil))))))

private def primeGapCertBatch36_126683 : PrimeCertificate :=
  .lucas 126683 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_97 (.cons primeGapCertBatch36_653 (.nil))))

private def primeGapCertBatch36_129341 : PrimeCertificate :=
  .lucas 129341 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_223 (.nil))))))

private def primeGapCertBatch36_141443 : PrimeCertificate :=
  .lucas 141443 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_10103 (.nil))))

private def primeGapCertBatch36_142733 : PrimeCertificate :=
  .lucas 142733 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_2099 (.nil)))))

private def primeGapCertBatch36_142841 : PrimeCertificate :=
  .lucas 142841 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3571 (.nil))))))

private def primeGapCertBatch36_146023 : PrimeCertificate :=
  .lucas 146023 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_24337 (.nil))))

private def primeGapCertBatch36_149729 : PrimeCertificate :=
  .lucas 149729 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4679 (.nil)))))))

private def primeGapCertBatch36_154981 : PrimeCertificate :=
  .lucas 154981 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_41 (.nil)))))))))

private def primeGapCertBatch36_156119 : PrimeCertificate :=
  .lucas 156119 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_78059 (.nil)))

private def primeGapCertBatch36_156131 : PrimeCertificate :=
  .lucas 156131 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_1201 (.nil)))))

private def primeGapCertBatch36_160639 : PrimeCertificate :=
  .lucas 160639 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_653 (.nil)))))

private def primeGapCertBatch36_166303 : PrimeCertificate :=
  .lucas 166303 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_9239 (.nil)))))

private def primeGapCertBatch36_166597 : PrimeCertificate :=
  .lucas 166597 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13883 (.nil)))))

private def primeGapCertBatch36_176369 : PrimeCertificate :=
  .lucas 176369 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_73 (.cons primeGapCertBatch36_151 (.nil)))))))

private def primeGapCertBatch36_178183 : PrimeCertificate :=
  .lucas 178183 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_521 (.nil))))))

private def primeGapCertBatch36_181717 : PrimeCertificate :=
  .lucas 181717 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_797 (.nil))))))

private def primeGapCertBatch36_187373 : PrimeCertificate :=
  .lucas 187373 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_139 (.cons primeGapCertBatch36_337 (.nil)))))

private def primeGapCertBatch36_189337 : PrimeCertificate :=
  .lucas 189337 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.nil)))))))))

private def primeGapCertBatch36_193243 : PrimeCertificate :=
  .lucas 193243 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_107 (.nil))))))

private def primeGapCertBatch36_199811 : PrimeCertificate :=
  .lucas 199811 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_53 (.nil))))))

private def primeGapCertBatch36_201919 : PrimeCertificate :=
  .lucas 201919 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_73 (.cons primeGapCertBatch36_461 (.nil)))))

private def primeGapCertBatch36_204163 : PrimeCertificate :=
  .lucas 204163 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_4861 (.nil)))))

private def primeGapCertBatch36_204427 : PrimeCertificate :=
  .lucas 204427 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_277 (.nil))))))

private def primeGapCertBatch36_204437 : PrimeCertificate :=
  .lucas 204437 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_51109 (.nil))))

private def primeGapCertBatch36_209071 : PrimeCertificate :=
  .lucas 209071 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_101 (.nil)))))))

private def primeGapCertBatch36_211427 : PrimeCertificate :=
  .lucas 211427 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_1733 (.nil))))

private def primeGapCertBatch36_213791 : PrimeCertificate :=
  .lucas 213791 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_21379 (.nil))))

private def primeGapCertBatch36_222073 : PrimeCertificate :=
  .lucas 222073 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_487 (.nil)))))))

private def primeGapCertBatch36_224611 : PrimeCertificate :=
  .lucas 224611 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7487 (.nil)))))

private def primeGapCertBatch36_227531 : PrimeCertificate :=
  .lucas 227531 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_373 (.nil)))))

private def primeGapCertBatch36_230761 : PrimeCertificate :=
  .lucas 230761 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_641 (.nil))))))))

private def primeGapCertBatch36_233353 : PrimeCertificate :=
  .lucas 233353 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_463 (.nil))))))))

private def primeGapCertBatch36_233509 : PrimeCertificate :=
  .lucas 233509 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_61 (.nil)))))))

private def primeGapCertBatch36_249383 : PrimeCertificate :=
  .lucas 249383 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_379 (.nil)))))

private def primeGapCertBatch36_249943 : PrimeCertificate :=
  .lucas 249943 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_541 (.nil))))))

private def primeGapCertBatch36_256589 : PrimeCertificate :=
  .lucas 256589 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_2789 (.nil)))))

private def primeGapCertBatch36_260191 : PrimeCertificate :=
  .lucas 260191 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_59 (.nil))))))))

private def primeGapCertBatch36_260849 : PrimeCertificate :=
  .lucas 260849 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_137 (.nil))))))))

private def primeGapCertBatch36_264359 : PrimeCertificate :=
  .lucas 264359 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_131 (.cons primeGapCertBatch36_1009 (.nil))))

private def primeGapCertBatch36_268607 : PrimeCertificate :=
  .lucas 268607 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_10331 (.nil))))

private def primeGapCertBatch36_276637 : PrimeCertificate :=
  .lucas 276637 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23053 (.nil)))))

private def primeGapCertBatch36_280597 : PrimeCertificate :=
  .lucas 280597 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_67 (.cons primeGapCertBatch36_349 (.nil))))))

private def primeGapCertBatch36_299473 : PrimeCertificate :=
  .lucas 299473 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_367 (.nil))))))))

private def primeGapCertBatch36_299749 : PrimeCertificate :=
  .lucas 299749 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_24979 (.nil)))))

private def primeGapCertBatch36_304687 : PrimeCertificate :=
  .lucas 304687 21 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_16927 (.nil)))))

private def primeGapCertBatch36_309623 : PrimeCertificate :=
  .lucas 309623 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_149 (.cons primeGapCertBatch36_1039 (.nil))))

private def primeGapCertBatch36_315083 : PrimeCertificate :=
  .lucas 315083 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_257 (.cons primeGapCertBatch36_613 (.nil))))

private def primeGapCertBatch36_320657 : PrimeCertificate :=
  .lucas 320657 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_409 (.nil))))))))

private def primeGapCertBatch36_320821 : PrimeCertificate :=
  .lucas 320821 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5347 (.nil))))))

private def primeGapCertBatch36_332837 : PrimeCertificate :=
  .lucas 332837 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11887 (.nil)))))

private def primeGapCertBatch36_333049 : PrimeCertificate :=
  .lucas 333049 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13877 (.nil))))))

private def primeGapCertBatch36_352739 : PrimeCertificate :=
  .lucas 352739 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_176369 (.nil)))

private def primeGapCertBatch36_359279 : PrimeCertificate :=
  .lucas 359279 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_10567 (.nil))))

private def primeGapCertBatch36_366677 : PrimeCertificate :=
  .lucas 366677 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_109 (.nil))))))

private def primeGapCertBatch36_367259 : PrimeCertificate :=
  .lucas 367259 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_3907 (.nil))))

private def primeGapCertBatch36_374797 : PrimeCertificate :=
  .lucas 374797 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_359 (.nil)))))))

private def primeGapCertBatch36_374837 : PrimeCertificate :=
  .lucas 374837 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_1217 (.nil))))))

private def primeGapCertBatch36_408953 : PrimeCertificate :=
  .lucas 408953 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_97 (.nil)))))))

private def primeGapCertBatch36_461051 : PrimeCertificate :=
  .lucas 461051 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_9221 (.nil)))))

private def primeGapCertBatch36_461059 : PrimeCertificate :=
  .lucas 461059 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_257 (.nil))))))

private def primeGapCertBatch36_461441 : PrimeCertificate :=
  .lucas 461441 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_103 (.nil)))))))))))

private def primeGapCertBatch36_528719 : PrimeCertificate :=
  .lucas 528719 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_264359 (.nil)))

private def primeGapCertBatch36_561307 : PrimeCertificate :=
  .lucas 561307 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_5503 (.nil)))))

private def primeGapCertBatch36_580631 : PrimeCertificate :=
  .lucas 580631 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_1873 (.nil)))))

private def primeGapCertBatch36_598711 : PrimeCertificate :=
  .lucas 598711 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_2851 (.nil))))))

private def primeGapCertBatch36_598973 : PrimeCertificate :=
  .lucas 598973 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_13613 (.nil)))))

private def primeGapCertBatch36_599273 : PrimeCertificate :=
  .lucas 599273 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_173 (.cons primeGapCertBatch36_433 (.nil))))))

private def primeGapCertBatch36_599303 : PrimeCertificate :=
  .lucas 599303 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_27241 (.nil))))

private def primeGapCertBatch36_599663 : PrimeCertificate :=
  .lucas 599663 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_211 (.nil))))))

private def primeGapCertBatch36_599701 : PrimeCertificate :=
  .lucas 599701 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1999 (.nil)))))))

private def primeGapCertBatch36_619207 : PrimeCertificate :=
  .lucas 619207 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_641 (.nil))))))

private def primeGapCertBatch36_641681 : PrimeCertificate :=
  .lucas 641681 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_617 (.nil))))))))

private def primeGapCertBatch36_642557 : PrimeCertificate :=
  .lucas 642557 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_160639 (.nil))))

private def primeGapCertBatch36_642799 : PrimeCertificate :=
  .lucas 642799 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_67 (.nil)))))))

private def primeGapCertBatch36_665267 : PrimeCertificate :=
  .lucas 665267 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_61 (.nil))))))

private def primeGapCertBatch36_666427 : PrimeCertificate :=
  .lucas 666427 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_109 (.cons primeGapCertBatch36_1019 (.nil)))))

private def primeGapCertBatch36_718547 : PrimeCertificate :=
  .lucas 718547 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_443 (.cons primeGapCertBatch36_811 (.nil))))

private def primeGapCertBatch36_718559 : PrimeCertificate :=
  .lucas 718559 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_359279 (.nil)))

private def primeGapCertBatch36_748057 : PrimeCertificate :=
  .lucas 748057 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_71 (.cons primeGapCertBatch36_439 (.nil)))))))

private def primeGapCertBatch36_748691 : PrimeCertificate :=
  .lucas 748691 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_74869 (.nil))))

private def primeGapCertBatch36_748981 : PrimeCertificate :=
  .lucas 748981 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_73 (.nil)))))))))

private def primeGapCertBatch36_749899 : PrimeCertificate :=
  .lucas 749899 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1543 (.nil))))))))

private def primeGapCertBatch36_816653 : PrimeCertificate :=
  .lucas 816653 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_204163 (.nil))))

private def primeGapCertBatch36_817013 : PrimeCertificate :=
  .lucas 817013 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_29179 (.nil)))))

private def primeGapCertBatch36_817709 : PrimeCertificate :=
  .lucas 817709 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_204427 (.nil))))

private def primeGapCertBatch36_854951 : PrimeCertificate :=
  .lucas 854951 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17099 (.nil)))))

private def primeGapCertBatch36_855709 : PrimeCertificate :=
  .lucas 855709 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_167 (.nil)))))))

private def primeGapCertBatch36_856711 : PrimeCertificate :=
  .lucas 856711 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_167 (.nil))))))))

private def primeGapCertBatch36_856799 : PrimeCertificate :=
  .lucas 856799 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_137 (.nil)))))

private def primeGapCertBatch36_856909 : PrimeCertificate :=
  .lucas 856909 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_1831 (.nil)))))))

private def primeGapCertBatch36_898189 : PrimeCertificate :=
  .lucas 898189 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_89 (.nil)))))))

private def primeGapCertBatch36_998071 : PrimeCertificate :=
  .lucas 998071 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_103 (.nil)))))))

private def primeGapCertBatch36_999433 : PrimeCertificate :=
  .lucas 999433 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_661 (.nil)))))))))

private def primeGapCertBatch36_1056169 : PrimeCertificate :=
  .lucas 1056169 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_14669 (.nil)))))))

private def primeGapCertBatch36_1057489 : PrimeCertificate :=
  .lucas 1057489 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_22031 (.nil)))))))

private def primeGapCertBatch36_1122389 : PrimeCertificate :=
  .lucas 1122389 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_280597 (.nil))))

private def primeGapCertBatch36_1122533 : PrimeCertificate :=
  .lucas 1122533 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_9677 (.nil)))))

private def primeGapCertBatch36_1124293 : PrimeCertificate :=
  .lucas 1124293 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_7207 (.nil))))))

private def primeGapCertBatch36_1197011 : PrimeCertificate :=
  .lucas 1197011 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_119701 (.nil))))

private def primeGapCertBatch36_1197113 : PrimeCertificate :=
  .lucas 1197113 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_21377 (.nil))))))

private def primeGapCertBatch36_1198607 : PrimeCertificate :=
  .lucas 1198607 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_599303 (.nil)))

private def primeGapCertBatch36_1198997 : PrimeCertificate :=
  .lucas 1198997 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_299749 (.nil))))

private def primeGapCertBatch36_1199167 : PrimeCertificate :=
  .lucas 1199167 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_67 (.cons primeGapCertBatch36_157 (.nil))))))

private def primeGapCertBatch36_1282577 : PrimeCertificate :=
  .lucas 1282577 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_4219 (.nil)))))))

private def primeGapCertBatch36_1382207 : PrimeCertificate :=
  .lucas 1382207 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_98729 (.nil))))

private def primeGapCertBatch36_1496669 : PrimeCertificate :=
  .lucas 1496669 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_419 (.nil))))))

private def primeGapCertBatch36_1498309 : PrimeCertificate :=
  .lucas 1498309 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17837 (.nil))))))

private def primeGapCertBatch36_1498729 : PrimeCertificate :=
  .lucas 1498729 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_811 (.nil))))))))

private def primeGapCertBatch36_1499189 : PrimeCertificate :=
  .lucas 1499189 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_374797 (.nil))))

private def primeGapCertBatch36_1499429 : PrimeCertificate :=
  .lucas 1499429 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_53551 (.nil)))))

private def primeGapCertBatch36_1632079 : PrimeCertificate :=
  .lucas 1632079 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_12953 (.nil))))))

private def primeGapCertBatch36_1798001 : PrimeCertificate :=
  .lucas 1798001 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_31 (.nil))))))))))

private def primeGapCertBatch36_1798289 : PrimeCertificate :=
  .lucas 1798289 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_71 (.cons primeGapCertBatch36_1583 (.nil)))))))

private def primeGapCertBatch36_1995211 : PrimeCertificate :=
  .lucas 1995211 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_3167 (.nil)))))))

private def primeGapCertBatch36_1995547 : PrimeCertificate :=
  .lucas 1995547 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_47513 (.nil)))))

private def primeGapCertBatch36_2244779 : PrimeCertificate :=
  .lucas 2244779 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1122389 (.nil)))

private def primeGapCertBatch36_2248537 : PrimeCertificate :=
  .lucas 2248537 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_4931 (.nil)))))))

private def primeGapCertBatch36_2565257 : PrimeCertificate :=
  .lucas 2565257 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_320657 (.nil)))))

private def primeGapCertBatch36_2565947 : PrimeCertificate :=
  .lucas 2565947 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_163 (.cons primeGapCertBatch36_463 (.nil)))))

private def primeGapCertBatch36_2565989 : PrimeCertificate :=
  .lucas 2565989 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_1777 (.nil))))))

private def primeGapCertBatch36_2566709 : PrimeCertificate :=
  .lucas 2566709 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_1213 (.nil))))))

private def primeGapCertBatch36_2567639 : PrimeCertificate :=
  .lucas 2567639 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_24223 (.nil))))

private def primeGapCertBatch36_2568473 : PrimeCertificate :=
  .lucas 2568473 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_11071 (.nil))))))

private def primeGapCertBatch36_2571197 : PrimeCertificate :=
  .lucas 2571197 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_642799 (.nil))))

private def primeGapCertBatch36_2993521 : PrimeCertificate :=
  .lucas 2993521 19 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_12473 (.nil))))))))

private def primeGapCertBatch36_2994113 : PrimeCertificate :=
  .lucas 2994113 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_4253 (.nil)))))))))

private def primeGapCertBatch36_2994281 : PrimeCertificate :=
  .lucas 2994281 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_74857 (.nil))))))

private def primeGapCertBatch36_2994731 : PrimeCertificate :=
  .lucas 2994731 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_299473 (.nil))))

private def primeGapCertBatch36_2997283 : PrimeCertificate :=
  .lucas 2997283 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_109 (.cons primeGapCertBatch36_4583 (.nil)))))

private def primeGapCertBatch36_2998199 : PrimeCertificate :=
  .lucas 2998199 14 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_331 (.cons primeGapCertBatch36_647 (.nil)))))

private def primeGapCertBatch36_2998663 : PrimeCertificate :=
  .lucas 2998663 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_311 (.cons primeGapCertBatch36_1607 (.nil)))))

private def primeGapCertBatch36_2998859 : PrimeCertificate :=
  .lucas 2998859 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1499429 (.nil)))

private def primeGapCertBatch36_2999333 : PrimeCertificate :=
  .lucas 2999333 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_107119 (.nil)))))

private def primeGapCertBatch36_2999509 : PrimeCertificate :=
  .lucas 2999509 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_5813 (.nil))))))

private def primeGapCertBatch36_2999813 : PrimeCertificate :=
  .lucas 2999813 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_20269 (.nil)))))

private def primeGapCertBatch36_3591769 : PrimeCertificate :=
  .lucas 3591769 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_109 (.cons primeGapCertBatch36_1373 (.nil)))))))

private def primeGapCertBatch36_3591871 : PrimeCertificate :=
  .lucas 3591871 12 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_67 (.cons primeGapCertBatch36_1787 (.nil))))))

private def primeGapCertBatch36_3593077 : PrimeCertificate :=
  .lucas 3593077 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_67 (.cons primeGapCertBatch36_109 (.nil)))))))

private def primeGapCertBatch36_3594541 : PrimeCertificate :=
  .lucas 3594541 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_139 (.cons primeGapCertBatch36_431 (.nil)))))))

private def primeGapCertBatch36_3595051 : PrimeCertificate :=
  .lucas 3595051 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_2663 (.nil))))))))

private def primeGapCertBatch36_3595639 : PrimeCertificate :=
  .lucas 3595639 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_599273 (.nil))))

private def primeGapCertBatch36_3596059 : PrimeCertificate :=
  .lucas 3596059 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_83 (.nil)))))))

private def primeGapCertBatch36_3596419 : PrimeCertificate :=
  .lucas 3596419 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_73 (.nil))))))))

private def primeGapCertBatch36_3596521 : PrimeCertificate :=
  .lucas 3596521 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_43 (.nil)))))))))

private def primeGapCertBatch36_3596557 : PrimeCertificate :=
  .lucas 3596557 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_157 (.nil)))))))

private def primeGapCertBatch36_3597541 : PrimeCertificate :=
  .lucas 3597541 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_3527 (.nil)))))))

private def primeGapCertBatch36_4488343 : PrimeCertificate :=
  .lucas 4488343 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_748057 (.nil))))

private def primeGapCertBatch36_4489559 : PrimeCertificate :=
  .lucas 4489559 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2244779 (.nil)))

private def primeGapCertBatch36_4493837 : PrimeCertificate :=
  .lucas 4493837 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_79 (.cons primeGapCertBatch36_14221 (.nil)))))

private def primeGapCertBatch36_4496777 : PrimeCertificate :=
  .lucas 4496777 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_24439 (.nil))))))

private def primeGapCertBatch36_4497221 : PrimeCertificate :=
  .lucas 4497221 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_353 (.nil))))))))

private def primeGapCertBatch36_4498847 : PrimeCertificate :=
  .lucas 4498847 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_523 (.nil))))))

private def primeGapCertBatch36_4498873 : PrimeCertificate :=
  .lucas 4498873 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_439 (.nil))))))))

private def primeGapCertBatch36_5988427 : PrimeCertificate :=
  .lucas 5988427 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_998071 (.nil))))

private def primeGapCertBatch36_5989463 : PrimeCertificate :=
  .lucas 5989463 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2994731 (.nil)))

private def primeGapCertBatch36_5989897 : PrimeCertificate :=
  .lucas 5989897 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_2521 (.nil)))))))))

private def primeGapCertBatch36_5990297 : PrimeCertificate :=
  .lucas 5990297 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_239 (.cons primeGapCertBatch36_241 (.nil)))))))

private def primeGapCertBatch36_5990731 : PrimeCertificate :=
  .lucas 5990731 14 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_397 (.cons primeGapCertBatch36_503 (.nil))))))

private def primeGapCertBatch36_5991457 : PrimeCertificate :=
  .lucas 5991457 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_139 (.cons primeGapCertBatch36_449 (.nil)))))))))

private def primeGapCertBatch36_5991883 : PrimeCertificate :=
  .lucas 5991883 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_76819 (.nil)))))

private def primeGapCertBatch36_5992403 : PrimeCertificate :=
  .lucas 5992403 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_17729 (.nil)))))

private def primeGapCertBatch36_5992697 : PrimeCertificate :=
  .lucas 5992697 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_32569 (.nil))))))

private def primeGapCertBatch36_5993237 : PrimeCertificate :=
  .lucas 5993237 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1498309 (.nil))))

private def primeGapCertBatch36_5998207 : PrimeCertificate :=
  .lucas 5998207 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_107 (.cons primeGapCertBatch36_9343 (.nil)))))

private def primeGapCertBatch36_5998667 : PrimeCertificate :=
  .lucas 5998667 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2999333 (.nil)))

private def primeGapCertBatch36_5999053 : PrimeCertificate :=
  .lucas 5999053 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_163 (.cons primeGapCertBatch36_3067 (.nil))))))

private def primeGapCertBatch36_5999627 : PrimeCertificate :=
  .lucas 5999627 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2999813 (.nil)))

private def primeGapCertBatch36_8977333 : PrimeCertificate :=
  .lucas 8977333 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_8221 (.nil)))))))

private def primeGapCertBatch36_8984293 : PrimeCertificate :=
  .lucas 8984293 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_748691 (.nil)))))

private def primeGapCertBatch36_8988079 : PrimeCertificate :=
  .lucas 8988079 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_191 (.nil)))))))

private def primeGapCertBatch36_8988949 : PrimeCertificate :=
  .lucas 8988949 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_83231 (.nil)))))))

private def primeGapCertBatch36_8995267 : PrimeCertificate :=
  .lucas 8995267 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_449 (.nil))))))))

private def primeGapCertBatch36_8996527 : PrimeCertificate :=
  .lucas 8996527 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_6491 (.nil)))))))

private def primeGapCertBatch36_17953373 : PrimeCertificate :=
  .lucas 17953373 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4488343 (.nil))))

private def primeGapCertBatch36_17956079 : PrimeCertificate :=
  .lucas 17956079 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_1282577 (.nil))))

private def primeGapCertBatch36_17964473 : PrimeCertificate :=
  .lucas 17964473 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_89 (.cons primeGapCertBatch36_1097 (.nil)))))))

private def primeGapCertBatch36_17973383 : PrimeCertificate :=
  .lucas 17973383 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_811 (.cons primeGapCertBatch36_1583 (.nil)))))

private def primeGapCertBatch36_17976239 : PrimeCertificate :=
  .lucas 17976239 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_3109 (.nil))))))

private def primeGapCertBatch36_17976929 : PrimeCertificate :=
  .lucas 17976929 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_337 (.cons primeGapCertBatch36_1667 (.nil))))))))

private def primeGapCertBatch36_17977703 : PrimeCertificate :=
  .lucas 17977703 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_547 (.cons primeGapCertBatch36_16433 (.nil))))

private def primeGapCertBatch36_17980799 : PrimeCertificate :=
  .lucas 17980799 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_131 (.cons primeGapCertBatch36_367 (.nil))))))

private def primeGapCertBatch36_17983391 : PrimeCertificate :=
  .lucas 17983391 29 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_683 (.cons primeGapCertBatch36_2633 (.nil)))))

private def primeGapCertBatch36_17985059 : PrimeCertificate :=
  .lucas 17985059 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_743 (.nil)))))))

private def primeGapCertBatch36_17988689 : PrimeCertificate :=
  .lucas 17988689 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1124293 (.nil))))))

private def primeGapCertBatch36_17990363 : PrimeCertificate :=
  .lucas 17990363 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_18701 (.nil)))))

private def primeGapCertBatch36_17990723 : PrimeCertificate :=
  .lucas 17990723 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2707 (.cons primeGapCertBatch36_3323 (.nil))))

private def primeGapCertBatch36_17993933 : PrimeCertificate :=
  .lucas 17993933 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_408953 (.nil)))))

private def primeGapCertBatch36_17995493 : PrimeCertificate :=
  .lucas 17995493 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4498873 (.nil))))

private def primeGapCertBatch36_35904553 : PrimeCertificate :=
  .lucas 35904553 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_79 (.cons primeGapCertBatch36_653 (.nil))))))))

private def primeGapCertBatch36_35904761 : PrimeCertificate :=
  .lucas 35904761 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_263 (.cons primeGapCertBatch36_3413 (.nil)))))))

private def primeGapCertBatch36_35904949 : PrimeCertificate :=
  .lucas 35904949 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_193 (.cons primeGapCertBatch36_419 (.nil)))))))

private def primeGapCertBatch36_35905153 : PrimeCertificate :=
  .lucas 35905153 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_93503 (.nil))))))))))

private def primeGapCertBatch36_35905349 : PrimeCertificate :=
  .lucas 35905349 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_107 (.cons primeGapCertBatch36_83891 (.nil)))))

private def primeGapCertBatch36_35905531 : PrimeCertificate :=
  .lucas 35905531 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_3061 (.nil)))))))

private def primeGapCertBatch36_35905739 : PrimeCertificate :=
  .lucas 35905739 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_1632079 (.nil))))

private def primeGapCertBatch36_35905949 : PrimeCertificate :=
  .lucas 35905949 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_127 (.cons primeGapCertBatch36_5437 (.nil))))))

private def primeGapCertBatch36_35906149 : PrimeCertificate :=
  .lucas 35906149 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_769 (.cons primeGapCertBatch36_1297 (.nil)))))))

private def primeGapCertBatch36_35906359 : PrimeCertificate :=
  .lucas 35906359 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_260191 (.nil)))))

private def primeGapCertBatch36_35906557 : PrimeCertificate :=
  .lucas 35906557 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_13789 (.nil)))))))

private def primeGapCertBatch36_35906747 : PrimeCertificate :=
  .lucas 35906747 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17953373 (.nil)))

private def primeGapCertBatch36_35906957 : PrimeCertificate :=
  .lucas 35906957 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_277 (.cons primeGapCertBatch36_1409 (.nil))))))

private def primeGapCertBatch36_35907161 : PrimeCertificate :=
  .lucas 35907161 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_353 (.cons primeGapCertBatch36_2543 (.nil)))))))

private def primeGapCertBatch36_35907371 : PrimeCertificate :=
  .lucas 35907371 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_156119 (.nil)))))

private def primeGapCertBatch36_35907581 : PrimeCertificate :=
  .lucas 35907581 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_971 (.nil)))))))

private def primeGapCertBatch36_35907743 : PrimeCertificate :=
  .lucas 35907743 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_47623 (.nil)))))

private def primeGapCertBatch36_35907943 : PrimeCertificate :=
  .lucas 35907943 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_854951 (.nil)))))

private def primeGapCertBatch36_35908153 : PrimeCertificate :=
  .lucas 35908153 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_9293 (.nil))))))))

private def primeGapCertBatch36_35908357 : PrimeCertificate :=
  .lucas 35908357 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_199 (.cons primeGapCertBatch36_1367 (.nil)))))))

private def primeGapCertBatch36_35908559 : PrimeCertificate :=
  .lucas 35908559 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_107 (.cons primeGapCertBatch36_23971 (.nil)))))

private def primeGapCertBatch36_35908751 : PrimeCertificate :=
  .lucas 35908751 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_1249 (.nil))))))))

private def primeGapCertBatch36_35908921 : PrimeCertificate :=
  .lucas 35908921 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11083 (.nil))))))))))

private def primeGapCertBatch36_35909131 : PrimeCertificate :=
  .lucas 35909131 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_227 (.cons primeGapCertBatch36_5273 (.nil))))))

private def primeGapCertBatch36_35909333 : PrimeCertificate :=
  .lucas 35909333 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_8977333 (.nil))))

private def primeGapCertBatch36_35909543 : PrimeCertificate :=
  .lucas 35909543 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_89 (.cons primeGapCertBatch36_11867 (.nil)))))

private def primeGapCertBatch36_35909747 : PrimeCertificate :=
  .lucas 35909747 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_1056169 (.nil))))

private def primeGapCertBatch36_35909953 : PrimeCertificate :=
  .lucas 35909953 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_14387 (.nil))))))))))

private def primeGapCertBatch36_35910131 : PrimeCertificate :=
  .lucas 35910131 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_156131 (.nil)))))

private def primeGapCertBatch36_35910331 : PrimeCertificate :=
  .lucas 35910331 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1197011 (.nil)))))

private def primeGapCertBatch36_35910533 : PrimeCertificate :=
  .lucas 35910533 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_9643 (.nil)))))))

private def primeGapCertBatch36_35910739 : PrimeCertificate :=
  .lucas 35910739 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_193 (.cons primeGapCertBatch36_10337 (.nil))))))

private def primeGapCertBatch36_35910947 : PrimeCertificate :=
  .lucas 35910947 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_227 (.cons primeGapCertBatch36_953 (.nil)))))

private def primeGapCertBatch36_35911153 : PrimeCertificate :=
  .lucas 35911153 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_249383 (.nil))))))))

private def primeGapCertBatch36_35911357 : PrimeCertificate :=
  .lucas 35911357 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_211 (.cons primeGapCertBatch36_1091 (.nil)))))))

private def primeGapCertBatch36_35911549 : PrimeCertificate :=
  .lucas 35911549 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_58679 (.nil)))))))

private def primeGapCertBatch36_35911753 : PrimeCertificate :=
  .lucas 35911753 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_88019 (.nil)))))))

private def primeGapCertBatch36_35911951 : PrimeCertificate :=
  .lucas 35911951 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_7723 (.nil)))))))

private def primeGapCertBatch36_35912159 : PrimeCertificate :=
  .lucas 35912159 41 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17956079 (.nil)))

private def primeGapCertBatch36_35912369 : PrimeCertificate :=
  .lucas 35912369 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_71 (.cons primeGapCertBatch36_101 (.cons primeGapCertBatch36_313 (.nil))))))))

private def primeGapCertBatch36_35912579 : PrimeCertificate :=
  .lucas 35912579 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_251 (.cons primeGapCertBatch36_5503 (.nil)))))

private def primeGapCertBatch36_35912777 : PrimeCertificate :=
  .lucas 35912777 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1579 (.cons primeGapCertBatch36_2843 (.nil))))))

private def primeGapCertBatch36_35912971 : PrimeCertificate :=
  .lucas 35912971 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_14779 (.nil)))))))))

private def primeGapCertBatch36_35913181 : PrimeCertificate :=
  .lucas 35913181 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_137 (.cons primeGapCertBatch36_257 (.nil))))))))

private def primeGapCertBatch36_35913391 : PrimeCertificate :=
  .lucas 35913391 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1197113 (.nil)))))

private def primeGapCertBatch36_35913599 : PrimeCertificate :=
  .lucas 35913599 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_2565257 (.nil))))

private def primeGapCertBatch36_35913799 : PrimeCertificate :=
  .lucas 35913799 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1995211 (.nil)))))

private def primeGapCertBatch36_35914007 : PrimeCertificate :=
  .lucas 35914007 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_619207 (.nil))))

private def primeGapCertBatch36_35914181 : PrimeCertificate :=
  .lucas 35914181 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_3259 (.nil)))))))

private def primeGapCertBatch36_35914363 : PrimeCertificate :=
  .lucas 35914363 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_401 (.nil)))))))

private def primeGapCertBatch36_35914561 : PrimeCertificate :=
  .lucas 35914561 26 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_179 (.nil))))))))))))

private def primeGapCertBatch36_35914733 : PrimeCertificate :=
  .lucas 35914733 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_211 (.cons primeGapCertBatch36_6079 (.nil))))))

private def primeGapCertBatch36_35914927 : PrimeCertificate :=
  .lucas 35914927 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_353 (.cons primeGapCertBatch36_547 (.nil))))))

private def primeGapCertBatch36_35915107 : PrimeCertificate :=
  .lucas 35915107 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_181 (.cons primeGapCertBatch36_33071 (.nil)))))

private def primeGapCertBatch36_35915309 : PrimeCertificate :=
  .lucas 35915309 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_1697 (.nil)))))))

private def primeGapCertBatch36_35915461 : PrimeCertificate :=
  .lucas 35915461 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_85513 (.nil)))))))

private def primeGapCertBatch36_35915669 : PrimeCertificate :=
  .lucas 35915669 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_491 (.cons primeGapCertBatch36_18287 (.nil)))))

private def primeGapCertBatch36_35915851 : PrimeCertificate :=
  .lucas 35915851 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_79813 (.nil)))))))

private def primeGapCertBatch36_35916059 : PrimeCertificate :=
  .lucas 35916059 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_509 (.cons primeGapCertBatch36_35281 (.nil))))

private def primeGapCertBatch36_35916269 : PrimeCertificate :=
  .lucas 35916269 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_309623 (.nil)))))

private def primeGapCertBatch36_35916473 : PrimeCertificate :=
  .lucas 35916473 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4489559 (.nil)))))

private def primeGapCertBatch36_35916679 : PrimeCertificate :=
  .lucas 35916679 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_4673 (.nil)))))))

private def primeGapCertBatch36_35916889 : PrimeCertificate :=
  .lucas 35916889 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_213791 (.nil)))))))

private def primeGapCertBatch36_35917081 : PrimeCertificate :=
  .lucas 35917081 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_10321 (.nil))))))))

private def primeGapCertBatch36_35917279 : PrimeCertificate :=
  .lucas 35917279 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_181 (.cons primeGapCertBatch36_33073 (.nil)))))

private def primeGapCertBatch36_35917487 : PrimeCertificate :=
  .lucas 35917487 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_2963 (.nil))))))

private def primeGapCertBatch36_35917691 : PrimeCertificate :=
  .lucas 35917691 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3591769 (.nil))))

private def primeGapCertBatch36_35917901 : PrimeCertificate :=
  .lucas 35917901 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_8353 (.nil)))))))

private def primeGapCertBatch36_35918101 : PrimeCertificate :=
  .lucas 35918101 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_251 (.nil))))))))))

private def primeGapCertBatch36_35918299 : PrimeCertificate :=
  .lucas 35918299 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_67 (.cons primeGapCertBatch36_79 (.nil))))))))

private def primeGapCertBatch36_35918507 : PrimeCertificate :=
  .lucas 35918507 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_383 (.cons primeGapCertBatch36_3607 (.nil)))))

private def primeGapCertBatch36_35918711 : PrimeCertificate :=
  .lucas 35918711 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3591871 (.nil))))

private def primeGapCertBatch36_35918921 : PrimeCertificate :=
  .lucas 35918921 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_73 (.cons primeGapCertBatch36_12301 (.nil)))))))

private def primeGapCertBatch36_35919131 : PrimeCertificate :=
  .lucas 35919131 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_16253 (.nil))))))

private def primeGapCertBatch36_35919287 : PrimeCertificate :=
  .lucas 35919287 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_457 (.cons primeGapCertBatch36_3023 (.nil)))))

private def primeGapCertBatch36_35919463 : PrimeCertificate :=
  .lucas 35919463 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_315083 (.nil)))))

private def primeGapCertBatch36_35919647 : PrimeCertificate :=
  .lucas 35919647 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_52361 (.nil))))))

private def primeGapCertBatch36_35919847 : PrimeCertificate :=
  .lucas 35919847 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1995547 (.nil)))))

private def primeGapCertBatch36_35920057 : PrimeCertificate :=
  .lucas 35920057 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1496669 (.nil))))))

private def primeGapCertBatch36_35920259 : PrimeCertificate :=
  .lucas 35920259 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_1699 (.nil))))))

private def primeGapCertBatch36_35920459 : PrimeCertificate :=
  .lucas 35920459 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_97 (.cons primeGapCertBatch36_2939 (.nil)))))))

private def primeGapCertBatch36_35920669 : PrimeCertificate :=
  .lucas 35920669 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_79 (.cons primeGapCertBatch36_5413 (.nil)))))))

private def primeGapCertBatch36_35920853 : PrimeCertificate :=
  .lucas 35920853 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_101 (.cons primeGapCertBatch36_137 (.nil)))))))

private def primeGapCertBatch36_35921057 : PrimeCertificate :=
  .lucas 35921057 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1122533 (.nil)))))))

private def primeGapCertBatch36_35921261 : PrimeCertificate :=
  .lucas 35921261 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_181 (.cons primeGapCertBatch36_9923 (.nil))))))

private def primeGapCertBatch36_35921449 : PrimeCertificate :=
  .lucas 35921449 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_166303 (.nil))))))))

private def primeGapCertBatch36_35921659 : PrimeCertificate :=
  .lucas 35921659 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_146023 (.nil)))))

private def primeGapCertBatch36_35921869 : PrimeCertificate :=
  .lucas 35921869 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_103 (.cons primeGapCertBatch36_29063 (.nil))))))

private def primeGapCertBatch36_35922049 : PrimeCertificate :=
  .lucas 35922049 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_139 (.cons primeGapCertBatch36_673 (.nil)))))))))))

private def primeGapCertBatch36_35922253 : PrimeCertificate :=
  .lucas 35922253 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_2993521 (.nil)))))

private def primeGapCertBatch36_35922461 : PrimeCertificate :=
  .lucas 35922461 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_256589 (.nil))))))

private def primeGapCertBatch36_35922661 : PrimeCertificate :=
  .lucas 35922661 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_598711 (.nil))))))

private def primeGapCertBatch36_35922871 : PrimeCertificate :=
  .lucas 35922871 12 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_443 (.nil))))))))

private def primeGapCertBatch36_35923049 : PrimeCertificate :=
  .lucas 35923049 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_20693 (.nil)))))))

private def primeGapCertBatch36_35923259 : PrimeCertificate :=
  .lucas 35923259 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_2565947 (.nil))))

private def primeGapCertBatch36_35923441 : PrimeCertificate :=
  .lucas 35923441 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_21383 (.nil)))))))))

private def primeGapCertBatch36_35923649 : PrimeCertificate :=
  .lucas 35923649 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_561307 (.nil))))))))

private def primeGapCertBatch36_35923847 : PrimeCertificate :=
  .lucas 35923847 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_2565989 (.nil))))

private def primeGapCertBatch36_35924051 : PrimeCertificate :=
  .lucas 35924051 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_743 (.cons primeGapCertBatch36_967 (.nil))))))

private def primeGapCertBatch36_35924209 : PrimeCertificate :=
  .lucas 35924209 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_617 (.cons primeGapCertBatch36_1213 (.nil))))))))

private def primeGapCertBatch36_35924419 : PrimeCertificate :=
  .lucas 35924419 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_665267 (.nil))))))

private def primeGapCertBatch36_35924627 : PrimeCertificate :=
  .lucas 35924627 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_251 (.cons primeGapCertBatch36_71563 (.nil))))

private def primeGapCertBatch36_35924821 : PrimeCertificate :=
  .lucas 35924821 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_31513 (.nil)))))))

private def primeGapCertBatch36_35924989 : PrimeCertificate :=
  .lucas 35924989 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_11833 (.nil)))))))

private def primeGapCertBatch36_35925191 : PrimeCertificate :=
  .lucas 35925191 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_191 (.cons primeGapCertBatch36_2687 (.nil))))))

private def primeGapCertBatch36_35925391 : PrimeCertificate :=
  .lucas 35925391 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_149 (.nil)))))))))

private def primeGapCertBatch36_35925583 : PrimeCertificate :=
  .lucas 35925583 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_77761 (.nil))))))

private def primeGapCertBatch36_35925761 : PrimeCertificate :=
  .lucas 35925761 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_127 (.nil)))))))))))))

private def primeGapCertBatch36_35925959 : PrimeCertificate :=
  .lucas 35925959 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_479 (.cons primeGapCertBatch36_37501 (.nil))))

private def primeGapCertBatch36_35926129 : PrimeCertificate :=
  .lucas 35926129 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_1229 (.nil))))))))))

private def primeGapCertBatch36_35926313 : PrimeCertificate :=
  .lucas 35926313 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_593 (.cons primeGapCertBatch36_7573 (.nil))))))

private def primeGapCertBatch36_35926523 : PrimeCertificate :=
  .lucas 35926523 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_127 (.cons primeGapCertBatch36_141443 (.nil))))

private def primeGapCertBatch36_35926733 : PrimeCertificate :=
  .lucas 35926733 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_179 (.cons primeGapCertBatch36_50177 (.nil)))))

private def primeGapCertBatch36_35926939 : PrimeCertificate :=
  .lucas 35926939 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_157 (.cons primeGapCertBatch36_12713 (.nil))))))

private def primeGapCertBatch36_35927149 : PrimeCertificate :=
  .lucas 35927149 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_80917 (.nil))))))

private def primeGapCertBatch36_35927351 : PrimeCertificate :=
  .lucas 35927351 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_718547 (.nil)))))

private def primeGapCertBatch36_35927561 : PrimeCertificate :=
  .lucas 35927561 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_898189 (.nil))))))

private def primeGapCertBatch36_35927741 : PrimeCertificate :=
  .lucas 35927741 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_1033 (.nil)))))))

private def primeGapCertBatch36_35927951 : PrimeCertificate :=
  .lucas 35927951 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_718559 (.nil)))))

private def primeGapCertBatch36_35928161 : PrimeCertificate :=
  .lucas 35928161 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_431 (.cons primeGapCertBatch36_521 (.nil)))))))))

private def primeGapCertBatch36_35928371 : PrimeCertificate :=
  .lucas 35928371 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_149 (.cons primeGapCertBatch36_24113 (.nil)))))

private def primeGapCertBatch36_35928577 : PrimeCertificate :=
  .lucas 35928577 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_113 (.nil)))))))))))))))

private def primeGapCertBatch36_35928757 : PrimeCertificate :=
  .lucas 35928757 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_16361 (.nil)))))))

private def primeGapCertBatch36_35928947 : PrimeCertificate :=
  .lucas 35928947 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17964473 (.nil)))

private def primeGapCertBatch36_35929147 : PrimeCertificate :=
  .lucas 35929147 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_14713 (.nil))))))

private def primeGapCertBatch36_35929357 : PrimeCertificate :=
  .lucas 35929357 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_2994113 (.nil)))))

private def primeGapCertBatch36_35929559 : PrimeCertificate :=
  .lucas 35929559 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_82787 (.nil)))))

private def primeGapCertBatch36_35929739 : PrimeCertificate :=
  .lucas 35929739 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_37 (.nil))))))))

private def primeGapCertBatch36_35929939 : PrimeCertificate :=
  .lucas 35929939 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_9227 (.nil))))))

private def primeGapCertBatch36_35930149 : PrimeCertificate :=
  .lucas 35930149 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_79 (.cons primeGapCertBatch36_151 (.cons primeGapCertBatch36_251 (.nil)))))))

private def primeGapCertBatch36_35930353 : PrimeCertificate :=
  .lucas 35930353 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_97 (.cons primeGapCertBatch36_7717 (.nil))))))))

private def primeGapCertBatch36_35930563 : PrimeCertificate :=
  .lucas 35930563 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5988427 (.nil))))

private def primeGapCertBatch36_35930771 : PrimeCertificate :=
  .lucas 35930771 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3593077 (.nil))))

private def primeGapCertBatch36_35930981 : PrimeCertificate :=
  .lucas 35930981 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_467 (.cons primeGapCertBatch36_3847 (.nil))))))

private def primeGapCertBatch36_35931167 : PrimeCertificate :=
  .lucas 35931167 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_55621 (.nil)))))

private def primeGapCertBatch36_35931373 : PrimeCertificate :=
  .lucas 35931373 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_2994281 (.nil)))))

private def primeGapCertBatch36_35931583 : PrimeCertificate :=
  .lucas 35931583 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_193 (.cons primeGapCertBatch36_10343 (.nil))))))

private def primeGapCertBatch36_35931757 : PrimeCertificate :=
  .lucas 35931757 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_103 (.cons primeGapCertBatch36_4153 (.nil)))))))

private def primeGapCertBatch36_35931953 : PrimeCertificate :=
  .lucas 35931953 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_320821 (.nil)))))))

private def primeGapCertBatch36_35932159 : PrimeCertificate :=
  .lucas 35932159 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_42473 (.nil))))))

private def primeGapCertBatch36_35932361 : PrimeCertificate :=
  .lucas 35932361 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_79 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_137 (.nil))))))))

private def primeGapCertBatch36_35932549 : PrimeCertificate :=
  .lucas 35932549 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1489 (.cons primeGapCertBatch36_2011 (.nil))))))

private def primeGapCertBatch36_35932733 : PrimeCertificate :=
  .lucas 35932733 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_816653 (.nil)))))

private def primeGapCertBatch36_35932927 : PrimeCertificate :=
  .lucas 35932927 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_631 (.cons primeGapCertBatch36_9491 (.nil)))))

private def primeGapCertBatch36_35933137 : PrimeCertificate :=
  .lucas 35933137 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_739 (.cons primeGapCertBatch36_1013 (.nil))))))))

private def primeGapCertBatch36_35933329 : PrimeCertificate :=
  .lucas 35933329 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_223 (.cons primeGapCertBatch36_373 (.nil))))))))))

private def primeGapCertBatch36_35933533 : PrimeCertificate :=
  .lucas 35933533 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_157 (.cons primeGapCertBatch36_19073 (.nil))))))

private def primeGapCertBatch36_35933719 : PrimeCertificate :=
  .lucas 35933719 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_281 (.cons primeGapCertBatch36_21313 (.nil)))))

private def primeGapCertBatch36_35933927 : PrimeCertificate :=
  .lucas 35933927 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_2566709 (.nil))))

private def primeGapCertBatch36_35934137 : PrimeCertificate :=
  .lucas 35934137 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_641681 (.nil))))))

private def primeGapCertBatch36_35934347 : PrimeCertificate :=
  .lucas 35934347 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_366677 (.nil)))))

private def primeGapCertBatch36_35934557 : PrimeCertificate :=
  .lucas 35934557 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_55799 (.nil))))))

private def primeGapCertBatch36_35934751 : PrimeCertificate :=
  .lucas 35934751 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_15971 (.nil))))))))

private def primeGapCertBatch36_35934961 : PrimeCertificate :=
  .lucas 35934961 22 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_149729 (.nil))))))))

private def primeGapCertBatch36_35935171 : PrimeCertificate :=
  .lucas 35935171 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_821 (.cons primeGapCertBatch36_1459 (.nil))))))

private def primeGapCertBatch36_35935381 : PrimeCertificate :=
  .lucas 35935381 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_5119 (.nil)))))))))

private def primeGapCertBatch36_35935583 : PrimeCertificate :=
  .lucas 35935583 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_113 (.cons primeGapCertBatch36_5483 (.nil)))))

private def primeGapCertBatch36_35935759 : PrimeCertificate :=
  .lucas 35935759 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_21467 (.nil)))))))

private def primeGapCertBatch36_35935957 : PrimeCertificate :=
  .lucas 35935957 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_2417 (.nil))))))))

private def primeGapCertBatch36_35936167 : PrimeCertificate :=
  .lucas 35936167 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_37201 (.nil))))))

private def primeGapCertBatch36_35936363 : PrimeCertificate :=
  .lucas 35936363 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_233353 (.nil)))))

private def primeGapCertBatch36_35936569 : PrimeCertificate :=
  .lucas 35936569 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_5737 (.nil)))))))))

private def primeGapCertBatch36_35936779 : PrimeCertificate :=
  .lucas 35936779 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5989463 (.nil))))

private def primeGapCertBatch36_35936969 : PrimeCertificate :=
  .lucas 35936969 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_131 (.cons primeGapCertBatch36_647 (.nil)))))))

private def primeGapCertBatch36_35937173 : PrimeCertificate :=
  .lucas 35937173 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_8984293 (.nil))))

private def primeGapCertBatch36_35937383 : PrimeCertificate :=
  .lucas 35937383 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_1382207 (.nil))))

private def primeGapCertBatch36_35937557 : PrimeCertificate :=
  .lucas 35937557 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_9349 (.nil))))))

private def primeGapCertBatch36_35937761 : PrimeCertificate :=
  .lucas 35937761 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_224611 (.nil))))))))

private def primeGapCertBatch36_35937961 : PrimeCertificate :=
  .lucas 35937961 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_449 (.nil)))))))))

private def primeGapCertBatch36_35938171 : PrimeCertificate :=
  .lucas 35938171 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_283 (.nil))))))))

private def primeGapCertBatch36_35938381 : PrimeCertificate :=
  .lucas 35938381 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_598973 (.nil))))))

private def primeGapCertBatch36_35938571 : PrimeCertificate :=
  .lucas 35938571 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_661 (.cons primeGapCertBatch36_5437 (.nil)))))

private def primeGapCertBatch36_35938781 : PrimeCertificate :=
  .lucas 35938781 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_71 (.cons primeGapCertBatch36_25309 (.nil))))))

private def primeGapCertBatch36_35938979 : PrimeCertificate :=
  .lucas 35938979 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_499 (.cons primeGapCertBatch36_36011 (.nil))))

private def primeGapCertBatch36_35939177 : PrimeCertificate :=
  .lucas 35939177 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_49367 (.nil)))))))

private def primeGapCertBatch36_35939383 : PrimeCertificate :=
  .lucas 35939383 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5989897 (.nil))))

private def primeGapCertBatch36_35939573 : PrimeCertificate :=
  .lucas 35939573 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_223 (.cons primeGapCertBatch36_937 (.nil))))))

private def primeGapCertBatch36_35939779 : PrimeCertificate :=
  .lucas 35939779 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_855709 (.nil)))))

private def primeGapCertBatch36_35939983 : PrimeCertificate :=
  .lucas 35939983 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_24251 (.nil))))))

private def primeGapCertBatch36_35940173 : PrimeCertificate :=
  .lucas 35940173 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_12781 (.nil))))))

private def primeGapCertBatch36_35940379 : PrimeCertificate :=
  .lucas 35940379 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_619 (.cons primeGapCertBatch36_9677 (.nil)))))

private def primeGapCertBatch36_35940589 : PrimeCertificate :=
  .lucas 35940589 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_149 (.cons primeGapCertBatch36_20101 (.nil))))))

private def primeGapCertBatch36_35940769 : PrimeCertificate :=
  .lucas 35940769 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_71 (.cons primeGapCertBatch36_5273 (.nil)))))))))

private def primeGapCertBatch36_35940977 : PrimeCertificate :=
  .lucas 35940977 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_2671 (.nil))))))))

private def primeGapCertBatch36_35941181 : PrimeCertificate :=
  .lucas 35941181 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_7103 (.nil)))))))

private def primeGapCertBatch36_35941391 : PrimeCertificate :=
  .lucas 35941391 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_199 (.cons primeGapCertBatch36_18061 (.nil)))))

private def primeGapCertBatch36_35941583 : PrimeCertificate :=
  .lucas 35941583 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_89 (.cons primeGapCertBatch36_201919 (.nil))))

private def primeGapCertBatch36_35941783 : PrimeCertificate :=
  .lucas 35941783 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5990297 (.nil))))

private def primeGapCertBatch36_35941973 : PrimeCertificate :=
  .lucas 35941973 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_499 (.cons primeGapCertBatch36_1637 (.nil))))))

private def primeGapCertBatch36_35942183 : PrimeCertificate :=
  .lucas 35942183 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_491 (.cons primeGapCertBatch36_2153 (.nil)))))

private def primeGapCertBatch36_35942381 : PrimeCertificate :=
  .lucas 35942381 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_97 (.cons primeGapCertBatch36_97 (.cons primeGapCertBatch36_191 (.nil)))))))

private def primeGapCertBatch36_35942591 : PrimeCertificate :=
  .lucas 35942591 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_211427 (.nil)))))

private def primeGapCertBatch36_35942801 : PrimeCertificate :=
  .lucas 35942801 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_1523 (.nil)))))))))

private def primeGapCertBatch36_35942993 : PrimeCertificate :=
  .lucas 35942993 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_257 (.cons primeGapCertBatch36_8741 (.nil)))))))

private def primeGapCertBatch36_35943199 : PrimeCertificate :=
  .lucas 35943199 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_193243 (.nil)))))

private def primeGapCertBatch36_35943403 : PrimeCertificate :=
  .lucas 35943403 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_28663 (.nil))))))

private def primeGapCertBatch36_35943581 : PrimeCertificate :=
  .lucas 35943581 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_157 (.cons primeGapCertBatch36_11447 (.nil))))))

private def primeGapCertBatch36_35943773 : PrimeCertificate :=
  .lucas 35943773 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_373 (.cons primeGapCertBatch36_24091 (.nil)))))

private def primeGapCertBatch36_35943979 : PrimeCertificate :=
  .lucas 35943979 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_233 (.cons primeGapCertBatch36_3673 (.nil))))))

private def primeGapCertBatch36_35944187 : PrimeCertificate :=
  .lucas 35944187 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_241 (.cons primeGapCertBatch36_74573 (.nil))))

private def primeGapCertBatch36_35944387 : PrimeCertificate :=
  .lucas 35944387 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5990731 (.nil))))

private def primeGapCertBatch36_35944591 : PrimeCertificate :=
  .lucas 35944591 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_108923 (.nil))))))

private def primeGapCertBatch36_35944793 : PrimeCertificate :=
  .lucas 35944793 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_577 (.cons primeGapCertBatch36_599 (.nil)))))))

private def primeGapCertBatch36_35945003 : PrimeCertificate :=
  .lucas 35945003 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4027 (.cons primeGapCertBatch36_4463 (.nil))))

private def primeGapCertBatch36_35945201 : PrimeCertificate :=
  .lucas 35945201 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_73 (.cons primeGapCertBatch36_1231 (.nil)))))))))

private def primeGapCertBatch36_35945411 : PrimeCertificate :=
  .lucas 35945411 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3594541 (.nil))))

private def primeGapCertBatch36_35945617 : PrimeCertificate :=
  .lucas 35945617 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_31 (.nil)))))))))))

private def primeGapCertBatch36_35945827 : PrimeCertificate :=
  .lucas 35945827 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_127 (.cons primeGapCertBatch36_293 (.nil)))))))

private def primeGapCertBatch36_35945989 : PrimeCertificate :=
  .lucas 35945989 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_7433 (.nil)))))))

private def primeGapCertBatch36_35946193 : PrimeCertificate :=
  .lucas 35946193 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_409 (.cons primeGapCertBatch36_1831 (.nil))))))))

private def primeGapCertBatch36_35946397 : PrimeCertificate :=
  .lucas 35946397 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_332837 (.nil)))))))

private def primeGapCertBatch36_35946571 : PrimeCertificate :=
  .lucas 35946571 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_108929 (.nil))))))

private def primeGapCertBatch36_35946767 : PrimeCertificate :=
  .lucas 35946767 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17973383 (.nil)))

private def primeGapCertBatch36_35946947 : PrimeCertificate :=
  .lucas 35946947 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_2567639 (.nil))))

private def primeGapCertBatch36_35947157 : PrimeCertificate :=
  .lucas 35947157 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_137 (.cons primeGapCertBatch36_9371 (.nil))))))

private def primeGapCertBatch36_35947363 : PrimeCertificate :=
  .lucas 35947363 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_151 (.cons primeGapCertBatch36_3607 (.nil))))))

private def primeGapCertBatch36_35947573 : PrimeCertificate :=
  .lucas 35947573 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_80963 (.nil))))))

private def primeGapCertBatch36_35947777 : PrimeCertificate :=
  .lucas 35947777 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_46807 (.nil)))))))))))

private def primeGapCertBatch36_35947973 : PrimeCertificate :=
  .lucas 35947973 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_131 (.cons primeGapCertBatch36_2213 (.nil))))))

private def primeGapCertBatch36_35948167 : PrimeCertificate :=
  .lucas 35948167 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_197 (.cons primeGapCertBatch36_1789 (.nil))))))

private def primeGapCertBatch36_35948369 : PrimeCertificate :=
  .lucas 35948369 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_541 (.cons primeGapCertBatch36_4153 (.nil)))))))

private def primeGapCertBatch36_35948573 : PrimeCertificate :=
  .lucas 35948573 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_817013 (.nil)))))

private def primeGapCertBatch36_35948743 : PrimeCertificate :=
  .lucas 35948743 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5991457 (.nil))))

private def primeGapCertBatch36_35948929 : PrimeCertificate :=
  .lucas 35948929 23 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_179 (.cons primeGapCertBatch36_523 (.nil)))))))))))

private def primeGapCertBatch36_35949139 : PrimeCertificate :=
  .lucas 35949139 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_337 (.cons primeGapCertBatch36_773 (.nil))))))

private def primeGapCertBatch36_35949341 : PrimeCertificate :=
  .lucas 35949341 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_36683 (.nil)))))))

private def primeGapCertBatch36_35949527 : PrimeCertificate :=
  .lucas 35949527 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_17921 (.nil)))))

private def primeGapCertBatch36_35949737 : PrimeCertificate :=
  .lucas 35949737 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_4157 (.nil)))))))

private def primeGapCertBatch36_35949899 : PrimeCertificate :=
  .lucas 35949899 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_79 (.cons primeGapCertBatch36_227531 (.nil))))

private def primeGapCertBatch36_35950097 : PrimeCertificate :=
  .lucas 35950097 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_24691 (.nil))))))))

private def primeGapCertBatch36_35950301 : PrimeCertificate :=
  .lucas 35950301 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_7649 (.nil)))))))

private def primeGapCertBatch36_35950511 : PrimeCertificate :=
  .lucas 35950511 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3595051 (.nil))))

private def primeGapCertBatch36_35950697 : PrimeCertificate :=
  .lucas 35950697 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4493837 (.nil)))))

private def primeGapCertBatch36_35950879 : PrimeCertificate :=
  .lucas 35950879 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_73973 (.nil))))))))

private def primeGapCertBatch36_35951089 : PrimeCertificate :=
  .lucas 35951089 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_748981 (.nil)))))))

private def primeGapCertBatch36_35951299 : PrimeCertificate :=
  .lucas 35951299 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5991883 (.nil))))

private def primeGapCertBatch36_35951501 : PrimeCertificate :=
  .lucas 35951501 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_5531 (.nil))))))))

private def primeGapCertBatch36_35951701 : PrimeCertificate :=
  .lucas 35951701 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_119839 (.nil)))))))

private def primeGapCertBatch36_35951899 : PrimeCertificate :=
  .lucas 35951899 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_241 (.nil)))))))

private def primeGapCertBatch36_35952109 : PrimeCertificate :=
  .lucas 35952109 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_443 (.cons primeGapCertBatch36_6763 (.nil))))))

private def primeGapCertBatch36_35952317 : PrimeCertificate :=
  .lucas 35952317 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_8988079 (.nil))))

private def primeGapCertBatch36_35952479 : PrimeCertificate :=
  .lucas 35952479 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17976239 (.nil)))

private def primeGapCertBatch36_35952689 : PrimeCertificate :=
  .lucas 35952689 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_131 (.cons primeGapCertBatch36_1009 (.nil))))))))

private def primeGapCertBatch36_35952893 : PrimeCertificate :=
  .lucas 35952893 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_528719 (.nil)))))

private def primeGapCertBatch36_35953067 : PrimeCertificate :=
  .lucas 35953067 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_304687 (.nil))))

private def primeGapCertBatch36_35953277 : PrimeCertificate :=
  .lucas 35953277 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_108293 (.nil)))))

private def primeGapCertBatch36_35953481 : PrimeCertificate :=
  .lucas 35953481 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_907 (.cons primeGapCertBatch36_991 (.nil)))))))

private def primeGapCertBatch36_35953651 : PrimeCertificate :=
  .lucas 35953651 14 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_109 (.cons primeGapCertBatch36_733 (.nil))))))))

private def primeGapCertBatch36_35953859 : PrimeCertificate :=
  .lucas 35953859 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17976929 (.nil)))

private def primeGapCertBatch36_35954059 : PrimeCertificate :=
  .lucas 35954059 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_347 (.cons primeGapCertBatch36_2467 (.nil))))))

private def primeGapCertBatch36_35954257 : PrimeCertificate :=
  .lucas 35954257 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_157 (.cons primeGapCertBatch36_367 (.nil)))))))))

private def primeGapCertBatch36_35954419 : PrimeCertificate :=
  .lucas 35954419 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5992403 (.nil))))

private def primeGapCertBatch36_35954627 : PrimeCertificate :=
  .lucas 35954627 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_1057489 (.nil))))

private def primeGapCertBatch36_35954801 : PrimeCertificate :=
  .lucas 35954801 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_12841 (.nil)))))))))

private def primeGapCertBatch36_35955001 : PrimeCertificate :=
  .lucas 35955001 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_47 (.nil))))))))))))

private def primeGapCertBatch36_35955197 : PrimeCertificate :=
  .lucas 35955197 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_271 (.cons primeGapCertBatch36_809 (.nil))))))

private def primeGapCertBatch36_35955407 : PrimeCertificate :=
  .lucas 35955407 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17977703 (.nil)))

private def primeGapCertBatch36_35955593 : PrimeCertificate :=
  .lucas 35955593 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_154981 (.nil))))))

private def primeGapCertBatch36_35955797 : PrimeCertificate :=
  .lucas 35955797 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_8988949 (.nil))))

private def primeGapCertBatch36_35955979 : PrimeCertificate :=
  .lucas 35955979 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1783 (.cons primeGapCertBatch36_3361 (.nil)))))

private def primeGapCertBatch36_35956183 : PrimeCertificate :=
  .lucas 35956183 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5992697 (.nil))))

private def primeGapCertBatch36_35956391 : PrimeCertificate :=
  .lucas 35956391 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3595639 (.nil))))

private def primeGapCertBatch36_35956589 : PrimeCertificate :=
  .lucas 35956589 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_73 (.cons primeGapCertBatch36_6481 (.nil))))))

private def primeGapCertBatch36_35956799 : PrimeCertificate :=
  .lucas 35956799 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_139 (.cons primeGapCertBatch36_129341 (.nil))))

private def primeGapCertBatch36_35957003 : PrimeCertificate :=
  .lucas 35957003 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_127 (.cons primeGapCertBatch36_2671 (.nil)))))

private def primeGapCertBatch36_35957213 : PrimeCertificate :=
  .lucas 35957213 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_101 (.cons primeGapCertBatch36_89003 (.nil)))))

private def primeGapCertBatch36_35957413 : PrimeCertificate :=
  .lucas 35957413 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_223 (.cons primeGapCertBatch36_1493 (.nil))))))))

private def primeGapCertBatch36_35957611 : PrimeCertificate :=
  .lucas 35957611 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_73 (.cons primeGapCertBatch36_421 (.nil))))))))

private def primeGapCertBatch36_35957813 : PrimeCertificate :=
  .lucas 35957813 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_74293 (.nil))))))

private def primeGapCertBatch36_35958001 : PrimeCertificate :=
  .lucas 35958001 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_461 (.nil)))))))))))

private def primeGapCertBatch36_35958211 : PrimeCertificate :=
  .lucas 35958211 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1198607 (.nil)))))

private def primeGapCertBatch36_35958421 : PrimeCertificate :=
  .lucas 35958421 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_107 (.cons primeGapCertBatch36_1867 (.nil))))))))

private def primeGapCertBatch36_35958623 : PrimeCertificate :=
  .lucas 35958623 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_2568473 (.nil))))

private def primeGapCertBatch36_35958827 : PrimeCertificate :=
  .lucas 35958827 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2293 (.cons primeGapCertBatch36_7841 (.nil))))

private def primeGapCertBatch36_35959031 : PrimeCertificate :=
  .lucas 35959031 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_101 (.cons primeGapCertBatch36_35603 (.nil)))))

private def primeGapCertBatch36_35959219 : PrimeCertificate :=
  .lucas 35959219 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1031 (.cons primeGapCertBatch36_5813 (.nil)))))

private def primeGapCertBatch36_35959423 : PrimeCertificate :=
  .lucas 35959423 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5993237 (.nil))))

private def primeGapCertBatch36_35959621 : PrimeCertificate :=
  .lucas 35959621 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_587 (.cons primeGapCertBatch36_1021 (.nil)))))))

private def primeGapCertBatch36_35959823 : PrimeCertificate :=
  .lucas 35959823 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_233 (.cons primeGapCertBatch36_77167 (.nil))))

private def primeGapCertBatch36_35960021 : PrimeCertificate :=
  .lucas 35960021 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1798001 (.nil)))))

private def primeGapCertBatch36_35960213 : PrimeCertificate :=
  .lucas 35960213 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_209071 (.nil)))))

private def primeGapCertBatch36_35960387 : PrimeCertificate :=
  .lucas 35960387 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_233509 (.nil)))))

private def primeGapCertBatch36_35960591 : PrimeCertificate :=
  .lucas 35960591 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3596059 (.nil))))

private def primeGapCertBatch36_35960789 : PrimeCertificate :=
  .lucas 35960789 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2287 (.cons primeGapCertBatch36_3931 (.nil)))))

private def primeGapCertBatch36_35960989 : PrimeCertificate :=
  .lucas 35960989 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_107 (.cons primeGapCertBatch36_4001 (.nil)))))))

private def primeGapCertBatch36_35961199 : PrimeCertificate :=
  .lucas 35961199 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_97 (.cons primeGapCertBatch36_97 (.nil))))))))

private def primeGapCertBatch36_35961407 : PrimeCertificate :=
  .lucas 35961407 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_73 (.cons primeGapCertBatch36_18947 (.nil)))))

private def primeGapCertBatch36_35961599 : PrimeCertificate :=
  .lucas 35961599 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17980799 (.nil)))

private def primeGapCertBatch36_35961799 : PrimeCertificate :=
  .lucas 35961799 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_113 (.nil)))))))

private def primeGapCertBatch36_35961979 : PrimeCertificate :=
  .lucas 35961979 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_461051 (.nil)))))

private def primeGapCertBatch36_35962189 : PrimeCertificate :=
  .lucas 35962189 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_563 (.cons primeGapCertBatch36_5323 (.nil))))))

private def primeGapCertBatch36_35962397 : PrimeCertificate :=
  .lucas 35962397 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2539 (.cons primeGapCertBatch36_3541 (.nil)))))

private def primeGapCertBatch36_35962603 : PrimeCertificate :=
  .lucas 35962603 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_461059 (.nil)))))

private def primeGapCertBatch36_35962811 : PrimeCertificate :=
  .lucas 35962811 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_276637 (.nil)))))

private def primeGapCertBatch36_35963017 : PrimeCertificate :=
  .lucas 35963017 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_163 (.cons primeGapCertBatch36_317 (.nil))))))))

private def primeGapCertBatch36_35963201 : PrimeCertificate :=
  .lucas 35963201 15 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_19 (.nil)))))))))))))

private def primeGapCertBatch36_35963401 : PrimeCertificate :=
  .lucas 35963401 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_5449 (.nil)))))))))

private def primeGapCertBatch36_35963611 : PrimeCertificate :=
  .lucas 35963611 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_227 (.cons primeGapCertBatch36_5281 (.nil))))))

private def primeGapCertBatch36_35963803 : PrimeCertificate :=
  .lucas 35963803 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_79 (.cons primeGapCertBatch36_3613 (.nil)))))))

private def primeGapCertBatch36_35963989 : PrimeCertificate :=
  .lucas 35963989 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_463 (.cons primeGapCertBatch36_6473 (.nil))))))

private def primeGapCertBatch36_35964191 : PrimeCertificate :=
  .lucas 35964191 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3596419 (.nil))))

private def primeGapCertBatch36_35964391 : PrimeCertificate :=
  .lucas 35964391 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_15569 (.nil)))))))

private def primeGapCertBatch36_35964583 : PrimeCertificate :=
  .lucas 35964583 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_139 (.cons primeGapCertBatch36_1487 (.nil))))))

private def primeGapCertBatch36_35964791 : PrimeCertificate :=
  .lucas 35964791 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_87719 (.nil)))))

private def primeGapCertBatch36_35965001 : PrimeCertificate :=
  .lucas 35965001 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7193 (.nil)))))))))

private def primeGapCertBatch36_35965211 : PrimeCertificate :=
  .lucas 35965211 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3596521 (.nil))))

private def primeGapCertBatch36_35965411 : PrimeCertificate :=
  .lucas 35965411 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_92219 (.nil))))))

private def primeGapCertBatch36_35965571 : PrimeCertificate :=
  .lucas 35965571 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3596557 (.nil))))

private def primeGapCertBatch36_35965781 : PrimeCertificate :=
  .lucas 35965781 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1798289 (.nil)))))

private def primeGapCertBatch36_35965981 : PrimeCertificate :=
  .lucas 35965981 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_199811 (.nil)))))))

private def primeGapCertBatch36_35966191 : PrimeCertificate :=
  .lucas 35966191 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_92221 (.nil))))))

private def primeGapCertBatch36_35966377 : PrimeCertificate :=
  .lucas 35966377 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_269 (.cons primeGapCertBatch36_619 (.nil)))))))))

private def primeGapCertBatch36_35966573 : PrimeCertificate :=
  .lucas 35966573 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_12611 (.nil))))))

private def primeGapCertBatch36_35966783 : PrimeCertificate :=
  .lucas 35966783 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17983391 (.nil)))

private def primeGapCertBatch36_35966977 : PrimeCertificate :=
  .lucas 35966977 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_2927 (.nil)))))))))))))))

private def primeGapCertBatch36_35967187 : PrimeCertificate :=
  .lucas 35967187 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_179 (.nil))))))))

private def primeGapCertBatch36_35967397 : PrimeCertificate :=
  .lucas 35967397 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_2997283 (.nil)))))

private def primeGapCertBatch36_35967593 : PrimeCertificate :=
  .lucas 35967593 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_191 (.cons primeGapCertBatch36_23539 (.nil))))))

private def primeGapCertBatch36_35967751 : PrimeCertificate :=
  .lucas 35967751 12 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_31 (.nil))))))))))

private def primeGapCertBatch36_35967941 : PrimeCertificate :=
  .lucas 35967941 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_349 (.cons primeGapCertBatch36_5153 (.nil))))))

private def primeGapCertBatch36_35968151 : PrimeCertificate :=
  .lucas 35968151 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_227 (.cons primeGapCertBatch36_3169 (.nil))))))

private def primeGapCertBatch36_35968327 : PrimeCertificate :=
  .lucas 35968327 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_211 (.cons primeGapCertBatch36_28411 (.nil)))))

private def primeGapCertBatch36_35968523 : PrimeCertificate :=
  .lucas 35968523 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3779 (.cons primeGapCertBatch36_4759 (.nil))))

private def primeGapCertBatch36_35968717 : PrimeCertificate :=
  .lucas 35968717 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_142733 (.nil)))))))

private def primeGapCertBatch36_35968913 : PrimeCertificate :=
  .lucas 35968913 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_6833 (.nil))))))))

private def primeGapCertBatch36_35969123 : PrimeCertificate :=
  .lucas 35969123 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_173 (.cons primeGapCertBatch36_14851 (.nil)))))

private def primeGapCertBatch36_35969293 : PrimeCertificate :=
  .lucas 35969293 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_333049 (.nil)))))))

private def primeGapCertBatch36_35969497 : PrimeCertificate :=
  .lucas 35969497 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1498729 (.nil))))))

private def primeGapCertBatch36_35969707 : PrimeCertificate :=
  .lucas 35969707 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_89 (.cons primeGapCertBatch36_22453 (.nil))))))

private def primeGapCertBatch36_35969911 : PrimeCertificate :=
  .lucas 35969911 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1198997 (.nil)))))

private def primeGapCertBatch36_35970119 : PrimeCertificate :=
  .lucas 35970119 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17985059 (.nil)))

private def primeGapCertBatch36_35970313 : PrimeCertificate :=
  .lucas 35970313 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_73 (.cons primeGapCertBatch36_419 (.nil)))))))))

private def primeGapCertBatch36_35970497 : PrimeCertificate :=
  .lucas 35970497 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_29581 (.nil)))))))))

private def primeGapCertBatch36_35970637 : PrimeCertificate :=
  .lucas 35970637 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_17737 (.nil)))))))

private def primeGapCertBatch36_35970841 : PrimeCertificate :=
  .lucas 35970841 19 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_163 (.cons primeGapCertBatch36_613 (.nil)))))))))

private def primeGapCertBatch36_35971037 : PrimeCertificate :=
  .lucas 35971037 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_263 (.cons primeGapCertBatch36_1103 (.nil))))))

private def primeGapCertBatch36_35971217 : PrimeCertificate :=
  .lucas 35971217 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_181 (.cons primeGapCertBatch36_12421 (.nil)))))))

private def primeGapCertBatch36_35971399 : PrimeCertificate :=
  .lucas 35971399 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_751 (.cons primeGapCertBatch36_887 (.nil)))))))

private def primeGapCertBatch36_35971597 : PrimeCertificate :=
  .lucas 35971597 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_24371 (.nil)))))))

private def primeGapCertBatch36_35971799 : PrimeCertificate :=
  .lucas 35971799 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_797 (.cons primeGapCertBatch36_22567 (.nil))))

private def primeGapCertBatch36_35971993 : PrimeCertificate :=
  .lucas 35971993 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_643 (.nil))))))))))

private def primeGapCertBatch36_35972201 : PrimeCertificate :=
  .lucas 35972201 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_197 (.nil)))))))))

private def primeGapCertBatch36_35972401 : PrimeCertificate :=
  .lucas 35972401 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_967 (.nil))))))))))

private def primeGapCertBatch36_35972609 : PrimeCertificate :=
  .lucas 35972609 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_10037 (.nil))))))))))))

private def primeGapCertBatch36_35972819 : PrimeCertificate :=
  .lucas 35972819 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_251 (.cons primeGapCertBatch36_353 (.nil))))))

private def primeGapCertBatch36_35973029 : PrimeCertificate :=
  .lucas 35973029 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_2671 (.nil)))))))

private def primeGapCertBatch36_35973233 : PrimeCertificate :=
  .lucas 35973233 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_73 (.cons primeGapCertBatch36_1621 (.nil))))))))

private def primeGapCertBatch36_35973433 : PrimeCertificate :=
  .lucas 35973433 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_857 (.nil)))))))))

private def primeGapCertBatch36_35973629 : PrimeCertificate :=
  .lucas 35973629 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_199 (.cons primeGapCertBatch36_1051 (.nil))))))

private def primeGapCertBatch36_35973823 : PrimeCertificate :=
  .lucas 35973823 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_251 (.cons primeGapCertBatch36_23887 (.nil)))))

private def primeGapCertBatch36_35974031 : PrimeCertificate :=
  .lucas 35974031 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_189337 (.nil)))))

private def primeGapCertBatch36_35974217 : PrimeCertificate :=
  .lucas 35974217 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4496777 (.nil)))))

private def primeGapCertBatch36_35974427 : PrimeCertificate :=
  .lucas 35974427 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_163 (.cons primeGapCertBatch36_163 (.cons primeGapCertBatch36_677 (.nil)))))

private def primeGapCertBatch36_35974613 : PrimeCertificate :=
  .lucas 35974613 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_809 (.cons primeGapCertBatch36_11117 (.nil)))))

private def primeGapCertBatch36_35974817 : PrimeCertificate :=
  .lucas 35974817 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_479 (.cons primeGapCertBatch36_2347 (.nil))))))))

private def primeGapCertBatch36_35975011 : PrimeCertificate :=
  .lucas 35975011 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1199167 (.nil)))))

private def primeGapCertBatch36_35975209 : PrimeCertificate :=
  .lucas 35975209 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_78893 (.nil)))))))

private def primeGapCertBatch36_35975411 : PrimeCertificate :=
  .lucas 35975411 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_3597541 (.nil))))

private def primeGapCertBatch36_35975617 : PrimeCertificate :=
  .lucas 35975617 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_187373 (.nil)))))))))

private def primeGapCertBatch36_35975827 : PrimeCertificate :=
  .lucas 35975827 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_222073 (.nil)))))))

private def primeGapCertBatch36_35976023 : PrimeCertificate :=
  .lucas 35976023 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1459 (.cons primeGapCertBatch36_12329 (.nil))))

private def primeGapCertBatch36_35976221 : PrimeCertificate :=
  .lucas 35976221 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_313 (.cons primeGapCertBatch36_821 (.nil)))))))

private def primeGapCertBatch36_35976419 : PrimeCertificate :=
  .lucas 35976419 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3373 (.cons primeGapCertBatch36_5333 (.nil))))

private def primeGapCertBatch36_35976593 : PrimeCertificate :=
  .lucas 35976593 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2248537 (.nil))))))

private def primeGapCertBatch36_35976799 : PrimeCertificate :=
  .lucas 35976799 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_1553 (.nil)))))))))

private def primeGapCertBatch36_35977001 : PrimeCertificate :=
  .lucas 35977001 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_35977 (.nil))))))))

private def primeGapCertBatch36_35977181 : PrimeCertificate :=
  .lucas 35977181 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_21673 (.nil))))))

private def primeGapCertBatch36_35977379 : PrimeCertificate :=
  .lucas 35977379 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17988689 (.nil)))

private def primeGapCertBatch36_35977567 : PrimeCertificate :=
  .lucas 35977567 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_4919 (.nil))))))

private def primeGapCertBatch36_35977769 : PrimeCertificate :=
  .lucas 35977769 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4497221 (.nil)))))

private def primeGapCertBatch36_35977973 : PrimeCertificate :=
  .lucas 35977973 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_71 (.cons primeGapCertBatch36_126683 (.nil)))))

private def primeGapCertBatch36_35978179 : PrimeCertificate :=
  .lucas 35978179 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1109 (.cons primeGapCertBatch36_5407 (.nil)))))

private def primeGapCertBatch36_35978389 : PrimeCertificate :=
  .lucas 35978389 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_2998199 (.nil)))))

private def primeGapCertBatch36_35978599 : PrimeCertificate :=
  .lucas 35978599 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_67 (.cons primeGapCertBatch36_29833 (.nil))))))

private def primeGapCertBatch36_35978797 : PrimeCertificate :=
  .lucas 35978797 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_47591 (.nil))))))))

private def primeGapCertBatch36_35978993 : PrimeCertificate :=
  .lucas 35978993 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_13967 (.nil))))))))

private def primeGapCertBatch36_35979197 : PrimeCertificate :=
  .lucas 35979197 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_817709 (.nil)))))

private def primeGapCertBatch36_35979379 : PrimeCertificate :=
  .lucas 35979379 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_352739 (.nil)))))

private def primeGapCertBatch36_35979589 : PrimeCertificate :=
  .lucas 35979589 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_999433 (.nil))))))

private def primeGapCertBatch36_35979781 : PrimeCertificate :=
  .lucas 35979781 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_599663 (.nil))))))

private def primeGapCertBatch36_35979967 : PrimeCertificate :=
  .lucas 35979967 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_181717 (.nil))))))

private def primeGapCertBatch36_35980171 : PrimeCertificate :=
  .lucas 35980171 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_929 (.cons primeGapCertBatch36_1291 (.nil))))))

private def primeGapCertBatch36_35980363 : PrimeCertificate :=
  .lucas 35980363 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_331 (.nil)))))))))

private def primeGapCertBatch36_35980537 : PrimeCertificate :=
  .lucas 35980537 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1499189 (.nil))))))

private def primeGapCertBatch36_35980727 : PrimeCertificate :=
  .lucas 35980727 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17990363 (.nil)))

private def primeGapCertBatch36_35980913 : PrimeCertificate :=
  .lucas 35980913 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_204437 (.nil)))))))

private def primeGapCertBatch36_35981069 : PrimeCertificate :=
  .lucas 35981069 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_8995267 (.nil))))

private def primeGapCertBatch36_35981251 : PrimeCertificate :=
  .lucas 35981251 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_101 (.nil))))))))))

private def primeGapCertBatch36_35981447 : PrimeCertificate :=
  .lucas 35981447 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17990723 (.nil)))

private def primeGapCertBatch36_35981657 : PrimeCertificate :=
  .lucas 35981657 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_79 (.cons primeGapCertBatch36_197 (.nil))))))))

private def primeGapCertBatch36_35981863 : PrimeCertificate :=
  .lucas 35981863 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_856711 (.nil)))))

private def primeGapCertBatch36_35982061 : PrimeCertificate :=
  .lucas 35982061 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_599701 (.nil))))))

private def primeGapCertBatch36_35982269 : PrimeCertificate :=
  .lucas 35982269 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_10799 (.nil)))))))

private def primeGapCertBatch36_35982469 : PrimeCertificate :=
  .lucas 35982469 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_37019 (.nil)))))))))

private def primeGapCertBatch36_35982631 : PrimeCertificate :=
  .lucas 35982631 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_1433 (.nil)))))))))

private def primeGapCertBatch36_35982803 : PrimeCertificate :=
  .lucas 35982803 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_4999 (.nil)))))

private def primeGapCertBatch36_35983009 : PrimeCertificate :=
  .lucas 35983009 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_41647 (.nil))))))))))

private def primeGapCertBatch36_35983193 : PrimeCertificate :=
  .lucas 35983193 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_642557 (.nil))))))

private def primeGapCertBatch36_35983369 : PrimeCertificate :=
  .lucas 35983369 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_71 (.cons primeGapCertBatch36_7039 (.nil))))))))

private def primeGapCertBatch36_35983579 : PrimeCertificate :=
  .lucas 35983579 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_199 (.cons primeGapCertBatch36_30137 (.nil)))))

private def primeGapCertBatch36_35983769 : PrimeCertificate :=
  .lucas 35983769 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_89 (.cons primeGapCertBatch36_50539 (.nil))))))

private def primeGapCertBatch36_35983957 : PrimeCertificate :=
  .lucas 35983957 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_2998663 (.nil)))))

private def primeGapCertBatch36_35984161 : PrimeCertificate :=
  .lucas 35984161 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_24989 (.nil))))))))))

private def primeGapCertBatch36_35984353 : PrimeCertificate :=
  .lucas 35984353 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_374837 (.nil))))))))

private def primeGapCertBatch36_35984539 : PrimeCertificate :=
  .lucas 35984539 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_683 (.cons primeGapCertBatch36_2927 (.nil))))))

private def primeGapCertBatch36_35984743 : PrimeCertificate :=
  .lucas 35984743 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_107 (.cons primeGapCertBatch36_2437 (.nil))))))

private def primeGapCertBatch36_35984953 : PrimeCertificate :=
  .lucas 35984953 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_166597 (.nil))))))))

private def primeGapCertBatch36_35985163 : PrimeCertificate :=
  .lucas 35985163 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_101653 (.nil)))))

private def primeGapCertBatch36_35985371 : PrimeCertificate :=
  .lucas 35985371 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_89 (.cons primeGapCertBatch36_40433 (.nil)))))

private def primeGapCertBatch36_35985559 : PrimeCertificate :=
  .lucas 35985559 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_856799 (.nil)))))

private def primeGapCertBatch36_35985769 : PrimeCertificate :=
  .lucas 35985769 11 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_16477 (.nil))))))))

private def primeGapCertBatch36_35985977 : PrimeCertificate :=
  .lucas 35985977 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_229 (.cons primeGapCertBatch36_1511 (.nil)))))))

private def primeGapCertBatch36_35986109 : PrimeCertificate :=
  .lucas 35986109 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_8996527 (.nil))))

private def primeGapCertBatch36_35986309 : PrimeCertificate :=
  .lucas 35986309 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_2998859 (.nil)))))

private def primeGapCertBatch36_35986499 : PrimeCertificate :=
  .lucas 35986499 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_823 (.cons primeGapCertBatch36_21863 (.nil))))

private def primeGapCertBatch36_35986693 : PrimeCertificate :=
  .lucas 35986693 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_191 (.cons primeGapCertBatch36_2243 (.nil)))))))

private def primeGapCertBatch36_35986871 : PrimeCertificate :=
  .lucas 35986871 7 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_79 (.cons primeGapCertBatch36_45553 (.nil)))))

private def primeGapCertBatch36_35987059 : PrimeCertificate :=
  .lucas 35987059 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_666427 (.nil))))))

private def primeGapCertBatch36_35987267 : PrimeCertificate :=
  .lucas 35987267 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_21601 (.nil))))))

private def primeGapCertBatch36_35987473 : PrimeCertificate :=
  .lucas 35987473 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_3011 (.nil)))))))))

private def primeGapCertBatch36_35987681 : PrimeCertificate :=
  .lucas 35987681 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_6079 (.nil)))))))))

private def primeGapCertBatch36_35987867 : PrimeCertificate :=
  .lucas 35987867 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17993933 (.nil)))

private def primeGapCertBatch36_35988061 : PrimeCertificate :=
  .lucas 35988061 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_53 (.cons primeGapCertBatch36_11317 (.nil)))))))

private def primeGapCertBatch36_35988263 : PrimeCertificate :=
  .lucas 35988263 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1301 (.cons primeGapCertBatch36_13831 (.nil))))

private def primeGapCertBatch36_35988467 : PrimeCertificate :=
  .lucas 35988467 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_113 (.cons primeGapCertBatch36_2699 (.nil)))))

private def primeGapCertBatch36_35988661 : PrimeCertificate :=
  .lucas 35988661 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_619 (.nil)))))))))

private def primeGapCertBatch36_35988833 : PrimeCertificate :=
  .lucas 35988833 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_102241 (.nil))))))))

private def primeGapCertBatch36_35989039 : PrimeCertificate :=
  .lucas 35989039 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_151 (.cons primeGapCertBatch36_13241 (.nil))))))

private def primeGapCertBatch36_35989243 : PrimeCertificate :=
  .lucas 35989243 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5998207 (.nil))))

private def primeGapCertBatch36_35989427 : PrimeCertificate :=
  .lucas 35989427 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_211 (.cons primeGapCertBatch36_7753 (.nil)))))

private def primeGapCertBatch36_35989631 : PrimeCertificate :=
  .lucas 35989631 13 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_131 (.cons primeGapCertBatch36_331 (.nil))))))

private def primeGapCertBatch36_35989801 : PrimeCertificate :=
  .lucas 35989801 43 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_41 (.nil)))))))))))

private def primeGapCertBatch36_35989981 : PrimeCertificate :=
  .lucas 35989981 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_46141 (.nil)))))))

private def primeGapCertBatch36_35990179 : PrimeCertificate :=
  .lucas 35990179 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_856909 (.nil)))))

private def primeGapCertBatch36_35990371 : PrimeCertificate :=
  .lucas 35990371 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_1619 (.nil))))))))

private def primeGapCertBatch36_35990573 : PrimeCertificate :=
  .lucas 35990573 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_857 (.cons primeGapCertBatch36_10499 (.nil)))))

private def primeGapCertBatch36_35990777 : PrimeCertificate :=
  .lucas 35990777 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_4498847 (.nil)))))

private def primeGapCertBatch36_35990987 : PrimeCertificate :=
  .lucas 35990987 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_17995493 (.nil)))

private def primeGapCertBatch36_35991173 : PrimeCertificate :=
  .lucas 35991173 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_167 (.cons primeGapCertBatch36_179 (.nil)))))))

private def primeGapCertBatch36_35991383 : PrimeCertificate :=
  .lucas 35991383 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_367259 (.nil)))))

private def primeGapCertBatch36_35991583 : PrimeCertificate :=
  .lucas 35991583 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_109 (.cons primeGapCertBatch36_5003 (.nil))))))

private def primeGapCertBatch36_35991793 : PrimeCertificate :=
  .lucas 35991793 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_249943 (.nil))))))))

private def primeGapCertBatch36_35992003 : PrimeCertificate :=
  .lucas 35992003 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5998667 (.nil))))

private def primeGapCertBatch36_35992211 : PrimeCertificate :=
  .lucas 35992211 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_1031 (.cons primeGapCertBatch36_3491 (.nil)))))

private def primeGapCertBatch36_35992399 : PrimeCertificate :=
  .lucas 35992399 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_461441 (.nil)))))

private def primeGapCertBatch36_35992573 : PrimeCertificate :=
  .lucas 35992573 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_38953 (.nil)))))))

private def primeGapCertBatch36_35992771 : PrimeCertificate :=
  .lucas 35992771 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_29 (.cons primeGapCertBatch36_3761 (.nil)))))))

private def primeGapCertBatch36_35992967 : PrimeCertificate :=
  .lucas 35992967 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_101 (.cons primeGapCertBatch36_178183 (.nil))))

private def primeGapCertBatch36_35993173 : PrimeCertificate :=
  .lucas 35993173 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_49171 (.nil))))))

private def primeGapCertBatch36_35993339 : PrimeCertificate :=
  .lucas 35993339 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_67 (.cons primeGapCertBatch36_268607 (.nil))))

private def primeGapCertBatch36_35993549 : PrimeCertificate :=
  .lucas 35993549 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_1327 (.cons primeGapCertBatch36_6781 (.nil)))))

private def primeGapCertBatch36_35993753 : PrimeCertificate :=
  .lucas 35993753 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_43 (.cons primeGapCertBatch36_5507 (.nil)))))))

private def primeGapCertBatch36_35993927 : PrimeCertificate :=
  .lucas 35993927 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_199 (.cons primeGapCertBatch36_90437 (.nil))))

private def primeGapCertBatch36_35994109 : PrimeCertificate :=
  .lucas 35994109 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_2999509 (.nil)))))

private def primeGapCertBatch36_35994319 : PrimeCertificate :=
  .lucas 35994319 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5999053 (.nil))))

private def primeGapCertBatch36_35994529 : PrimeCertificate :=
  .lucas 35994529 31 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_124981 (.nil)))))))))

private def primeGapCertBatch36_35994733 : PrimeCertificate :=
  .lucas 35994733 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_673 (.cons primeGapCertBatch36_4457 (.nil))))))

private def primeGapCertBatch36_35994943 : PrimeCertificate :=
  .lucas 35994943 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_2677 (.nil))))))))

private def primeGapCertBatch36_35995153 : PrimeCertificate :=
  .lucas 35995153 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_749899 (.nil)))))))

private def primeGapCertBatch36_35995361 : PrimeCertificate :=
  .lucas 35995361 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_367 (.cons primeGapCertBatch36_613 (.nil)))))))))

private def primeGapCertBatch36_35995571 : PrimeCertificate :=
  .lucas 35995571 10 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_73 (.cons primeGapCertBatch36_3793 (.nil))))))

private def primeGapCertBatch36_35995753 : PrimeCertificate :=
  .lucas 35995753 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_4273 (.nil))))))))))

private def primeGapCertBatch36_35995933 : PrimeCertificate :=
  .lucas 35995933 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_142841 (.nil)))))))

private def primeGapCertBatch36_35996141 : PrimeCertificate :=
  .lucas 35996141 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_105871 (.nil))))))

private def primeGapCertBatch36_35996351 : PrimeCertificate :=
  .lucas 35996351 17 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_79 (.cons primeGapCertBatch36_701 (.nil)))))))

private def primeGapCertBatch36_35996561 : PrimeCertificate :=
  .lucas 35996561 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_37 (.cons primeGapCertBatch36_12161 (.nil))))))))

private def primeGapCertBatch36_35996759 : PrimeCertificate :=
  .lucas 35996759 14 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_2571197 (.nil))))

private def primeGapCertBatch36_35996959 : PrimeCertificate :=
  .lucas 35996959 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_1097 (.cons primeGapCertBatch36_1823 (.nil))))))

private def primeGapCertBatch36_35997163 : PrimeCertificate :=
  .lucas 35997163 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_260849 (.nil)))))

private def primeGapCertBatch36_35997373 : PrimeCertificate :=
  .lucas 35997373 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_111103 (.nil))))))))

private def primeGapCertBatch36_35997581 : PrimeCertificate :=
  .lucas 35997581 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_269 (.cons primeGapCertBatch36_6691 (.nil))))))

private def primeGapCertBatch36_35997763 : PrimeCertificate :=
  .lucas 35997763 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5999627 (.nil))))

private def primeGapCertBatch36_35997943 : PrimeCertificate :=
  .lucas 35997943 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_139 (.cons primeGapCertBatch36_2539 (.nil))))))

private def primeGapCertBatch36_35998147 : PrimeCertificate :=
  .lucas 35998147 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_47 (.cons primeGapCertBatch36_2503 (.nil)))))))

private def primeGapCertBatch36_35998351 : PrimeCertificate :=
  .lucas 35998351 6 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_5 (.cons primeGapCertBatch36_17 (.cons primeGapCertBatch36_19 (.cons primeGapCertBatch36_743 (.nil))))))))

private def primeGapCertBatch36_35998507 : PrimeCertificate :=
  .lucas 35998507 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_74071 (.nil))))))))

private def primeGapCertBatch36_35998717 : PrimeCertificate :=
  .lucas 35998717 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_13 (.cons primeGapCertBatch36_230761 (.nil))))))

private def primeGapCertBatch36_35998927 : PrimeCertificate :=
  .lucas 35998927 5 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_72287 (.nil)))))

private def primeGapCertBatch36_35999123 : PrimeCertificate :=
  .lucas 35999123 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_31 (.cons primeGapCertBatch36_580631 (.nil))))

private def primeGapCertBatch36_35999323 : PrimeCertificate :=
  .lucas 35999323 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_59 (.cons primeGapCertBatch36_101693 (.nil)))))

private def primeGapCertBatch36_35999533 : PrimeCertificate :=
  .lucas 35999533 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_257 (.cons primeGapCertBatch36_1297 (.nil))))))))

private def primeGapCertBatch36_35999723 : PrimeCertificate :=
  .lucas 35999723 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_11 (.cons primeGapCertBatch36_41 (.cons primeGapCertBatch36_107 (.cons primeGapCertBatch36_373 (.nil))))))

private def primeGapCertBatch36_35999923 : PrimeCertificate :=
  .lucas 35999923 2 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_7 (.cons primeGapCertBatch36_23 (.cons primeGapCertBatch36_83 (.cons primeGapCertBatch36_449 (.nil)))))))

private def primeGapCertBatch36_36000127 : PrimeCertificate :=
  .lucas 36000127 3 (.cons primeGapCertBatch36_2 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_3 (.cons primeGapCertBatch36_61 (.cons primeGapCertBatch36_3643 (.nil))))))))

private def primeGapCertifiedCerts_362_0 : List PrimeCertificate :=
  [primeGapCertBatch36_35904553, primeGapCertBatch36_35904761, primeGapCertBatch36_35904949, primeGapCertBatch36_35905153, primeGapCertBatch36_35905349, primeGapCertBatch36_35905531, primeGapCertBatch36_35905739, primeGapCertBatch36_35905949, primeGapCertBatch36_35906149, primeGapCertBatch36_35906359, primeGapCertBatch36_35906557, primeGapCertBatch36_35906747, primeGapCertBatch36_35906957, primeGapCertBatch36_35907161, primeGapCertBatch36_35907371, primeGapCertBatch36_35907581, primeGapCertBatch36_35907743, primeGapCertBatch36_35907943, primeGapCertBatch36_35908153, primeGapCertBatch36_35908357, primeGapCertBatch36_35908559, primeGapCertBatch36_35908751, primeGapCertBatch36_35908921, primeGapCertBatch36_35909131, primeGapCertBatch36_35909333, primeGapCertBatch36_35909543, primeGapCertBatch36_35909747, primeGapCertBatch36_35909953, primeGapCertBatch36_35910131, primeGapCertBatch36_35910331, primeGapCertBatch36_35910533, primeGapCertBatch36_35910739, primeGapCertBatch36_35910947, primeGapCertBatch36_35911153, primeGapCertBatch36_35911357, primeGapCertBatch36_35911549, primeGapCertBatch36_35911753, primeGapCertBatch36_35911951, primeGapCertBatch36_35912159, primeGapCertBatch36_35912369]

private def primeGapCertified_362_0 : List ℕ :=
  [35904553, 35904761, 35904949, 35905153, 35905349, 35905531, 35905739, 35905949, 35906149, 35906359, 35906557, 35906747, 35906957, 35907161, 35907371, 35907581, 35907743, 35907943, 35908153, 35908357, 35908559, 35908751, 35908921, 35909131, 35909333, 35909543, 35909747, 35909953, 35910131, 35910331, 35910533, 35910739, 35910947, 35911153, 35911357, 35911549, 35911753, 35911951, 35912159, 35912369]

private lemma primeGapCertified_362_0_values :
    primeGapCertifiedCerts_362_0.map PrimeCertificate.value = primeGapCertified_362_0 := by
  rfl

private lemma primeGapCertified_362_0_primes : primeGapCertified_362_0.Forall Nat.Prime := by
  rw [← primeGapCertified_362_0_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_0_chain : primeGapCertified_362_0.IsChain GapStep := by
  norm_num [primeGapCertified_362_0, List.IsChain, GapStep]

private lemma primeGapCertified_362_0_segment :
    CertifiedSegment primeGapCertified_362_0 35904553 35912369 :=
  ⟨primeGapCertified_362_0_primes, primeGapCertified_362_0_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_1 : List PrimeCertificate :=
  [primeGapCertBatch36_35912579, primeGapCertBatch36_35912777, primeGapCertBatch36_35912971, primeGapCertBatch36_35913181, primeGapCertBatch36_35913391, primeGapCertBatch36_35913599, primeGapCertBatch36_35913799, primeGapCertBatch36_35914007, primeGapCertBatch36_35914181, primeGapCertBatch36_35914363, primeGapCertBatch36_35914561, primeGapCertBatch36_35914733, primeGapCertBatch36_35914927, primeGapCertBatch36_35915107, primeGapCertBatch36_35915309, primeGapCertBatch36_35915461, primeGapCertBatch36_35915669, primeGapCertBatch36_35915851, primeGapCertBatch36_35916059, primeGapCertBatch36_35916269, primeGapCertBatch36_35916473, primeGapCertBatch36_35916679, primeGapCertBatch36_35916889, primeGapCertBatch36_35917081, primeGapCertBatch36_35917279, primeGapCertBatch36_35917487, primeGapCertBatch36_35917691, primeGapCertBatch36_35917901, primeGapCertBatch36_35918101, primeGapCertBatch36_35918299, primeGapCertBatch36_35918507, primeGapCertBatch36_35918711, primeGapCertBatch36_35918921, primeGapCertBatch36_35919131, primeGapCertBatch36_35919287, primeGapCertBatch36_35919463, primeGapCertBatch36_35919647, primeGapCertBatch36_35919847, primeGapCertBatch36_35920057, primeGapCertBatch36_35920259]

private def primeGapCertified_362_1 : List ℕ :=
  [35912579, 35912777, 35912971, 35913181, 35913391, 35913599, 35913799, 35914007, 35914181, 35914363, 35914561, 35914733, 35914927, 35915107, 35915309, 35915461, 35915669, 35915851, 35916059, 35916269, 35916473, 35916679, 35916889, 35917081, 35917279, 35917487, 35917691, 35917901, 35918101, 35918299, 35918507, 35918711, 35918921, 35919131, 35919287, 35919463, 35919647, 35919847, 35920057, 35920259]

private lemma primeGapCertified_362_1_values :
    primeGapCertifiedCerts_362_1.map PrimeCertificate.value = primeGapCertified_362_1 := by
  rfl

private lemma primeGapCertified_362_1_primes : primeGapCertified_362_1.Forall Nat.Prime := by
  rw [← primeGapCertified_362_1_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_1_chain : primeGapCertified_362_1.IsChain GapStep := by
  norm_num [primeGapCertified_362_1, List.IsChain, GapStep]

private lemma primeGapCertified_362_1_segment :
    CertifiedSegment primeGapCertified_362_1 35912579 35920259 :=
  ⟨primeGapCertified_362_1_primes, primeGapCertified_362_1_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_2 : List PrimeCertificate :=
  [primeGapCertBatch36_35920459, primeGapCertBatch36_35920669, primeGapCertBatch36_35920853, primeGapCertBatch36_35921057, primeGapCertBatch36_35921261, primeGapCertBatch36_35921449, primeGapCertBatch36_35921659, primeGapCertBatch36_35921869, primeGapCertBatch36_35922049, primeGapCertBatch36_35922253, primeGapCertBatch36_35922461, primeGapCertBatch36_35922661, primeGapCertBatch36_35922871, primeGapCertBatch36_35923049, primeGapCertBatch36_35923259, primeGapCertBatch36_35923441, primeGapCertBatch36_35923649, primeGapCertBatch36_35923847, primeGapCertBatch36_35924051, primeGapCertBatch36_35924209, primeGapCertBatch36_35924419, primeGapCertBatch36_35924627, primeGapCertBatch36_35924821, primeGapCertBatch36_35924989, primeGapCertBatch36_35925191, primeGapCertBatch36_35925391, primeGapCertBatch36_35925583, primeGapCertBatch36_35925761, primeGapCertBatch36_35925959, primeGapCertBatch36_35926129, primeGapCertBatch36_35926313, primeGapCertBatch36_35926523, primeGapCertBatch36_35926733, primeGapCertBatch36_35926939, primeGapCertBatch36_35927149, primeGapCertBatch36_35927351, primeGapCertBatch36_35927561, primeGapCertBatch36_35927741, primeGapCertBatch36_35927951, primeGapCertBatch36_35928161]

private def primeGapCertified_362_2 : List ℕ :=
  [35920459, 35920669, 35920853, 35921057, 35921261, 35921449, 35921659, 35921869, 35922049, 35922253, 35922461, 35922661, 35922871, 35923049, 35923259, 35923441, 35923649, 35923847, 35924051, 35924209, 35924419, 35924627, 35924821, 35924989, 35925191, 35925391, 35925583, 35925761, 35925959, 35926129, 35926313, 35926523, 35926733, 35926939, 35927149, 35927351, 35927561, 35927741, 35927951, 35928161]

private lemma primeGapCertified_362_2_values :
    primeGapCertifiedCerts_362_2.map PrimeCertificate.value = primeGapCertified_362_2 := by
  rfl

private lemma primeGapCertified_362_2_primes : primeGapCertified_362_2.Forall Nat.Prime := by
  rw [← primeGapCertified_362_2_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_2_chain : primeGapCertified_362_2.IsChain GapStep := by
  norm_num [primeGapCertified_362_2, List.IsChain, GapStep]

private lemma primeGapCertified_362_2_segment :
    CertifiedSegment primeGapCertified_362_2 35920459 35928161 :=
  ⟨primeGapCertified_362_2_primes, primeGapCertified_362_2_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_3 : List PrimeCertificate :=
  [primeGapCertBatch36_35928371, primeGapCertBatch36_35928577, primeGapCertBatch36_35928757, primeGapCertBatch36_35928947, primeGapCertBatch36_35929147, primeGapCertBatch36_35929357, primeGapCertBatch36_35929559, primeGapCertBatch36_35929739, primeGapCertBatch36_35929939, primeGapCertBatch36_35930149, primeGapCertBatch36_35930353, primeGapCertBatch36_35930563, primeGapCertBatch36_35930771, primeGapCertBatch36_35930981, primeGapCertBatch36_35931167, primeGapCertBatch36_35931373, primeGapCertBatch36_35931583, primeGapCertBatch36_35931757, primeGapCertBatch36_35931953, primeGapCertBatch36_35932159, primeGapCertBatch36_35932361, primeGapCertBatch36_35932549, primeGapCertBatch36_35932733, primeGapCertBatch36_35932927, primeGapCertBatch36_35933137, primeGapCertBatch36_35933329, primeGapCertBatch36_35933533, primeGapCertBatch36_35933719, primeGapCertBatch36_35933927, primeGapCertBatch36_35934137, primeGapCertBatch36_35934347, primeGapCertBatch36_35934557, primeGapCertBatch36_35934751, primeGapCertBatch36_35934961, primeGapCertBatch36_35935171, primeGapCertBatch36_35935381, primeGapCertBatch36_35935583, primeGapCertBatch36_35935759, primeGapCertBatch36_35935957, primeGapCertBatch36_35936167]

private def primeGapCertified_362_3 : List ℕ :=
  [35928371, 35928577, 35928757, 35928947, 35929147, 35929357, 35929559, 35929739, 35929939, 35930149, 35930353, 35930563, 35930771, 35930981, 35931167, 35931373, 35931583, 35931757, 35931953, 35932159, 35932361, 35932549, 35932733, 35932927, 35933137, 35933329, 35933533, 35933719, 35933927, 35934137, 35934347, 35934557, 35934751, 35934961, 35935171, 35935381, 35935583, 35935759, 35935957, 35936167]

private lemma primeGapCertified_362_3_values :
    primeGapCertifiedCerts_362_3.map PrimeCertificate.value = primeGapCertified_362_3 := by
  rfl

private lemma primeGapCertified_362_3_primes : primeGapCertified_362_3.Forall Nat.Prime := by
  rw [← primeGapCertified_362_3_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_3_chain : primeGapCertified_362_3.IsChain GapStep := by
  norm_num [primeGapCertified_362_3, List.IsChain, GapStep]

private lemma primeGapCertified_362_3_segment :
    CertifiedSegment primeGapCertified_362_3 35928371 35936167 :=
  ⟨primeGapCertified_362_3_primes, primeGapCertified_362_3_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_4 : List PrimeCertificate :=
  [primeGapCertBatch36_35936363, primeGapCertBatch36_35936569, primeGapCertBatch36_35936779, primeGapCertBatch36_35936969, primeGapCertBatch36_35937173, primeGapCertBatch36_35937383, primeGapCertBatch36_35937557, primeGapCertBatch36_35937761, primeGapCertBatch36_35937961, primeGapCertBatch36_35938171, primeGapCertBatch36_35938381, primeGapCertBatch36_35938571, primeGapCertBatch36_35938781, primeGapCertBatch36_35938979, primeGapCertBatch36_35939177, primeGapCertBatch36_35939383, primeGapCertBatch36_35939573, primeGapCertBatch36_35939779, primeGapCertBatch36_35939983, primeGapCertBatch36_35940173, primeGapCertBatch36_35940379, primeGapCertBatch36_35940589, primeGapCertBatch36_35940769, primeGapCertBatch36_35940977, primeGapCertBatch36_35941181, primeGapCertBatch36_35941391, primeGapCertBatch36_35941583, primeGapCertBatch36_35941783, primeGapCertBatch36_35941973, primeGapCertBatch36_35942183, primeGapCertBatch36_35942381, primeGapCertBatch36_35942591, primeGapCertBatch36_35942801, primeGapCertBatch36_35942993, primeGapCertBatch36_35943199, primeGapCertBatch36_35943403, primeGapCertBatch36_35943581, primeGapCertBatch36_35943773, primeGapCertBatch36_35943979, primeGapCertBatch36_35944187]

private def primeGapCertified_362_4 : List ℕ :=
  [35936363, 35936569, 35936779, 35936969, 35937173, 35937383, 35937557, 35937761, 35937961, 35938171, 35938381, 35938571, 35938781, 35938979, 35939177, 35939383, 35939573, 35939779, 35939983, 35940173, 35940379, 35940589, 35940769, 35940977, 35941181, 35941391, 35941583, 35941783, 35941973, 35942183, 35942381, 35942591, 35942801, 35942993, 35943199, 35943403, 35943581, 35943773, 35943979, 35944187]

private lemma primeGapCertified_362_4_values :
    primeGapCertifiedCerts_362_4.map PrimeCertificate.value = primeGapCertified_362_4 := by
  rfl

private lemma primeGapCertified_362_4_primes : primeGapCertified_362_4.Forall Nat.Prime := by
  rw [← primeGapCertified_362_4_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_4_chain : primeGapCertified_362_4.IsChain GapStep := by
  norm_num [primeGapCertified_362_4, List.IsChain, GapStep]

private lemma primeGapCertified_362_4_segment :
    CertifiedSegment primeGapCertified_362_4 35936363 35944187 :=
  ⟨primeGapCertified_362_4_primes, primeGapCertified_362_4_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_5 : List PrimeCertificate :=
  [primeGapCertBatch36_35944387, primeGapCertBatch36_35944591, primeGapCertBatch36_35944793, primeGapCertBatch36_35945003, primeGapCertBatch36_35945201, primeGapCertBatch36_35945411, primeGapCertBatch36_35945617, primeGapCertBatch36_35945827, primeGapCertBatch36_35945989, primeGapCertBatch36_35946193, primeGapCertBatch36_35946397, primeGapCertBatch36_35946571, primeGapCertBatch36_35946767, primeGapCertBatch36_35946947, primeGapCertBatch36_35947157, primeGapCertBatch36_35947363, primeGapCertBatch36_35947573, primeGapCertBatch36_35947777, primeGapCertBatch36_35947973, primeGapCertBatch36_35948167, primeGapCertBatch36_35948369, primeGapCertBatch36_35948573, primeGapCertBatch36_35948743, primeGapCertBatch36_35948929, primeGapCertBatch36_35949139, primeGapCertBatch36_35949341, primeGapCertBatch36_35949527, primeGapCertBatch36_35949737, primeGapCertBatch36_35949899, primeGapCertBatch36_35950097, primeGapCertBatch36_35950301, primeGapCertBatch36_35950511, primeGapCertBatch36_35950697, primeGapCertBatch36_35950879, primeGapCertBatch36_35951089, primeGapCertBatch36_35951299, primeGapCertBatch36_35951501, primeGapCertBatch36_35951701, primeGapCertBatch36_35951899, primeGapCertBatch36_35952109]

private def primeGapCertified_362_5 : List ℕ :=
  [35944387, 35944591, 35944793, 35945003, 35945201, 35945411, 35945617, 35945827, 35945989, 35946193, 35946397, 35946571, 35946767, 35946947, 35947157, 35947363, 35947573, 35947777, 35947973, 35948167, 35948369, 35948573, 35948743, 35948929, 35949139, 35949341, 35949527, 35949737, 35949899, 35950097, 35950301, 35950511, 35950697, 35950879, 35951089, 35951299, 35951501, 35951701, 35951899, 35952109]

private lemma primeGapCertified_362_5_values :
    primeGapCertifiedCerts_362_5.map PrimeCertificate.value = primeGapCertified_362_5 := by
  rfl

private lemma primeGapCertified_362_5_primes : primeGapCertified_362_5.Forall Nat.Prime := by
  rw [← primeGapCertified_362_5_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_5_chain : primeGapCertified_362_5.IsChain GapStep := by
  norm_num [primeGapCertified_362_5, List.IsChain, GapStep]

private lemma primeGapCertified_362_5_segment :
    CertifiedSegment primeGapCertified_362_5 35944387 35952109 :=
  ⟨primeGapCertified_362_5_primes, primeGapCertified_362_5_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_6 : List PrimeCertificate :=
  [primeGapCertBatch36_35952317, primeGapCertBatch36_35952479, primeGapCertBatch36_35952689, primeGapCertBatch36_35952893, primeGapCertBatch36_35953067, primeGapCertBatch36_35953277, primeGapCertBatch36_35953481, primeGapCertBatch36_35953651, primeGapCertBatch36_35953859, primeGapCertBatch36_35954059, primeGapCertBatch36_35954257, primeGapCertBatch36_35954419, primeGapCertBatch36_35954627, primeGapCertBatch36_35954801, primeGapCertBatch36_35955001, primeGapCertBatch36_35955197, primeGapCertBatch36_35955407, primeGapCertBatch36_35955593, primeGapCertBatch36_35955797, primeGapCertBatch36_35955979, primeGapCertBatch36_35956183, primeGapCertBatch36_35956391, primeGapCertBatch36_35956589, primeGapCertBatch36_35956799, primeGapCertBatch36_35957003, primeGapCertBatch36_35957213, primeGapCertBatch36_35957413, primeGapCertBatch36_35957611, primeGapCertBatch36_35957813, primeGapCertBatch36_35958001, primeGapCertBatch36_35958211, primeGapCertBatch36_35958421, primeGapCertBatch36_35958623, primeGapCertBatch36_35958827, primeGapCertBatch36_35959031, primeGapCertBatch36_35959219, primeGapCertBatch36_35959423, primeGapCertBatch36_35959621, primeGapCertBatch36_35959823, primeGapCertBatch36_35960021]

private def primeGapCertified_362_6 : List ℕ :=
  [35952317, 35952479, 35952689, 35952893, 35953067, 35953277, 35953481, 35953651, 35953859, 35954059, 35954257, 35954419, 35954627, 35954801, 35955001, 35955197, 35955407, 35955593, 35955797, 35955979, 35956183, 35956391, 35956589, 35956799, 35957003, 35957213, 35957413, 35957611, 35957813, 35958001, 35958211, 35958421, 35958623, 35958827, 35959031, 35959219, 35959423, 35959621, 35959823, 35960021]

private lemma primeGapCertified_362_6_values :
    primeGapCertifiedCerts_362_6.map PrimeCertificate.value = primeGapCertified_362_6 := by
  rfl

private lemma primeGapCertified_362_6_primes : primeGapCertified_362_6.Forall Nat.Prime := by
  rw [← primeGapCertified_362_6_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_6_chain : primeGapCertified_362_6.IsChain GapStep := by
  norm_num [primeGapCertified_362_6, List.IsChain, GapStep]

private lemma primeGapCertified_362_6_segment :
    CertifiedSegment primeGapCertified_362_6 35952317 35960021 :=
  ⟨primeGapCertified_362_6_primes, primeGapCertified_362_6_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_7 : List PrimeCertificate :=
  [primeGapCertBatch36_35960213, primeGapCertBatch36_35960387, primeGapCertBatch36_35960591, primeGapCertBatch36_35960789, primeGapCertBatch36_35960989, primeGapCertBatch36_35961199, primeGapCertBatch36_35961407, primeGapCertBatch36_35961599, primeGapCertBatch36_35961799, primeGapCertBatch36_35961979, primeGapCertBatch36_35962189, primeGapCertBatch36_35962397, primeGapCertBatch36_35962603, primeGapCertBatch36_35962811, primeGapCertBatch36_35963017, primeGapCertBatch36_35963201, primeGapCertBatch36_35963401, primeGapCertBatch36_35963611, primeGapCertBatch36_35963803, primeGapCertBatch36_35963989, primeGapCertBatch36_35964191, primeGapCertBatch36_35964391, primeGapCertBatch36_35964583, primeGapCertBatch36_35964791, primeGapCertBatch36_35965001, primeGapCertBatch36_35965211, primeGapCertBatch36_35965411, primeGapCertBatch36_35965571, primeGapCertBatch36_35965781, primeGapCertBatch36_35965981, primeGapCertBatch36_35966191, primeGapCertBatch36_35966377, primeGapCertBatch36_35966573, primeGapCertBatch36_35966783, primeGapCertBatch36_35966977, primeGapCertBatch36_35967187, primeGapCertBatch36_35967397, primeGapCertBatch36_35967593, primeGapCertBatch36_35967751, primeGapCertBatch36_35967941]

private def primeGapCertified_362_7 : List ℕ :=
  [35960213, 35960387, 35960591, 35960789, 35960989, 35961199, 35961407, 35961599, 35961799, 35961979, 35962189, 35962397, 35962603, 35962811, 35963017, 35963201, 35963401, 35963611, 35963803, 35963989, 35964191, 35964391, 35964583, 35964791, 35965001, 35965211, 35965411, 35965571, 35965781, 35965981, 35966191, 35966377, 35966573, 35966783, 35966977, 35967187, 35967397, 35967593, 35967751, 35967941]

private lemma primeGapCertified_362_7_values :
    primeGapCertifiedCerts_362_7.map PrimeCertificate.value = primeGapCertified_362_7 := by
  rfl

private lemma primeGapCertified_362_7_primes : primeGapCertified_362_7.Forall Nat.Prime := by
  rw [← primeGapCertified_362_7_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_7_chain : primeGapCertified_362_7.IsChain GapStep := by
  norm_num [primeGapCertified_362_7, List.IsChain, GapStep]

private lemma primeGapCertified_362_7_segment :
    CertifiedSegment primeGapCertified_362_7 35960213 35967941 :=
  ⟨primeGapCertified_362_7_primes, primeGapCertified_362_7_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_8 : List PrimeCertificate :=
  [primeGapCertBatch36_35968151, primeGapCertBatch36_35968327, primeGapCertBatch36_35968523, primeGapCertBatch36_35968717, primeGapCertBatch36_35968913, primeGapCertBatch36_35969123, primeGapCertBatch36_35969293, primeGapCertBatch36_35969497, primeGapCertBatch36_35969707, primeGapCertBatch36_35969911, primeGapCertBatch36_35970119, primeGapCertBatch36_35970313, primeGapCertBatch36_35970497, primeGapCertBatch36_35970637, primeGapCertBatch36_35970841, primeGapCertBatch36_35971037, primeGapCertBatch36_35971217, primeGapCertBatch36_35971399, primeGapCertBatch36_35971597, primeGapCertBatch36_35971799, primeGapCertBatch36_35971993, primeGapCertBatch36_35972201, primeGapCertBatch36_35972401, primeGapCertBatch36_35972609, primeGapCertBatch36_35972819, primeGapCertBatch36_35973029, primeGapCertBatch36_35973233, primeGapCertBatch36_35973433, primeGapCertBatch36_35973629, primeGapCertBatch36_35973823, primeGapCertBatch36_35974031, primeGapCertBatch36_35974217, primeGapCertBatch36_35974427, primeGapCertBatch36_35974613, primeGapCertBatch36_35974817, primeGapCertBatch36_35975011, primeGapCertBatch36_35975209, primeGapCertBatch36_35975411, primeGapCertBatch36_35975617, primeGapCertBatch36_35975827]

private def primeGapCertified_362_8 : List ℕ :=
  [35968151, 35968327, 35968523, 35968717, 35968913, 35969123, 35969293, 35969497, 35969707, 35969911, 35970119, 35970313, 35970497, 35970637, 35970841, 35971037, 35971217, 35971399, 35971597, 35971799, 35971993, 35972201, 35972401, 35972609, 35972819, 35973029, 35973233, 35973433, 35973629, 35973823, 35974031, 35974217, 35974427, 35974613, 35974817, 35975011, 35975209, 35975411, 35975617, 35975827]

private lemma primeGapCertified_362_8_values :
    primeGapCertifiedCerts_362_8.map PrimeCertificate.value = primeGapCertified_362_8 := by
  rfl

private lemma primeGapCertified_362_8_primes : primeGapCertified_362_8.Forall Nat.Prime := by
  rw [← primeGapCertified_362_8_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_8_chain : primeGapCertified_362_8.IsChain GapStep := by
  norm_num [primeGapCertified_362_8, List.IsChain, GapStep]

private lemma primeGapCertified_362_8_segment :
    CertifiedSegment primeGapCertified_362_8 35968151 35975827 :=
  ⟨primeGapCertified_362_8_primes, primeGapCertified_362_8_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_9 : List PrimeCertificate :=
  [primeGapCertBatch36_35976023, primeGapCertBatch36_35976221, primeGapCertBatch36_35976419, primeGapCertBatch36_35976593, primeGapCertBatch36_35976799, primeGapCertBatch36_35977001, primeGapCertBatch36_35977181, primeGapCertBatch36_35977379, primeGapCertBatch36_35977567, primeGapCertBatch36_35977769, primeGapCertBatch36_35977973, primeGapCertBatch36_35978179, primeGapCertBatch36_35978389, primeGapCertBatch36_35978599, primeGapCertBatch36_35978797, primeGapCertBatch36_35978993, primeGapCertBatch36_35979197, primeGapCertBatch36_35979379, primeGapCertBatch36_35979589, primeGapCertBatch36_35979781, primeGapCertBatch36_35979967, primeGapCertBatch36_35980171, primeGapCertBatch36_35980363, primeGapCertBatch36_35980537, primeGapCertBatch36_35980727, primeGapCertBatch36_35980913, primeGapCertBatch36_35981069, primeGapCertBatch36_35981251, primeGapCertBatch36_35981447, primeGapCertBatch36_35981657, primeGapCertBatch36_35981863, primeGapCertBatch36_35982061, primeGapCertBatch36_35982269, primeGapCertBatch36_35982469, primeGapCertBatch36_35982631, primeGapCertBatch36_35982803, primeGapCertBatch36_35983009, primeGapCertBatch36_35983193, primeGapCertBatch36_35983369, primeGapCertBatch36_35983579]

private def primeGapCertified_362_9 : List ℕ :=
  [35976023, 35976221, 35976419, 35976593, 35976799, 35977001, 35977181, 35977379, 35977567, 35977769, 35977973, 35978179, 35978389, 35978599, 35978797, 35978993, 35979197, 35979379, 35979589, 35979781, 35979967, 35980171, 35980363, 35980537, 35980727, 35980913, 35981069, 35981251, 35981447, 35981657, 35981863, 35982061, 35982269, 35982469, 35982631, 35982803, 35983009, 35983193, 35983369, 35983579]

private lemma primeGapCertified_362_9_values :
    primeGapCertifiedCerts_362_9.map PrimeCertificate.value = primeGapCertified_362_9 := by
  rfl

private lemma primeGapCertified_362_9_primes : primeGapCertified_362_9.Forall Nat.Prime := by
  rw [← primeGapCertified_362_9_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_9_chain : primeGapCertified_362_9.IsChain GapStep := by
  norm_num [primeGapCertified_362_9, List.IsChain, GapStep]

private lemma primeGapCertified_362_9_segment :
    CertifiedSegment primeGapCertified_362_9 35976023 35983579 :=
  ⟨primeGapCertified_362_9_primes, primeGapCertified_362_9_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_10 : List PrimeCertificate :=
  [primeGapCertBatch36_35983769, primeGapCertBatch36_35983957, primeGapCertBatch36_35984161, primeGapCertBatch36_35984353, primeGapCertBatch36_35984539, primeGapCertBatch36_35984743, primeGapCertBatch36_35984953, primeGapCertBatch36_35985163, primeGapCertBatch36_35985371, primeGapCertBatch36_35985559, primeGapCertBatch36_35985769, primeGapCertBatch36_35985977, primeGapCertBatch36_35986109, primeGapCertBatch36_35986309, primeGapCertBatch36_35986499, primeGapCertBatch36_35986693, primeGapCertBatch36_35986871, primeGapCertBatch36_35987059, primeGapCertBatch36_35987267, primeGapCertBatch36_35987473, primeGapCertBatch36_35987681, primeGapCertBatch36_35987867, primeGapCertBatch36_35988061, primeGapCertBatch36_35988263, primeGapCertBatch36_35988467, primeGapCertBatch36_35988661, primeGapCertBatch36_35988833, primeGapCertBatch36_35989039, primeGapCertBatch36_35989243, primeGapCertBatch36_35989427, primeGapCertBatch36_35989631, primeGapCertBatch36_35989801, primeGapCertBatch36_35989981, primeGapCertBatch36_35990179, primeGapCertBatch36_35990371, primeGapCertBatch36_35990573, primeGapCertBatch36_35990777, primeGapCertBatch36_35990987, primeGapCertBatch36_35991173, primeGapCertBatch36_35991383]

private def primeGapCertified_362_10 : List ℕ :=
  [35983769, 35983957, 35984161, 35984353, 35984539, 35984743, 35984953, 35985163, 35985371, 35985559, 35985769, 35985977, 35986109, 35986309, 35986499, 35986693, 35986871, 35987059, 35987267, 35987473, 35987681, 35987867, 35988061, 35988263, 35988467, 35988661, 35988833, 35989039, 35989243, 35989427, 35989631, 35989801, 35989981, 35990179, 35990371, 35990573, 35990777, 35990987, 35991173, 35991383]

private lemma primeGapCertified_362_10_values :
    primeGapCertifiedCerts_362_10.map PrimeCertificate.value = primeGapCertified_362_10 := by
  rfl

private lemma primeGapCertified_362_10_primes : primeGapCertified_362_10.Forall Nat.Prime := by
  rw [← primeGapCertified_362_10_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_10_chain : primeGapCertified_362_10.IsChain GapStep := by
  norm_num [primeGapCertified_362_10, List.IsChain, GapStep]

private lemma primeGapCertified_362_10_segment :
    CertifiedSegment primeGapCertified_362_10 35983769 35991383 :=
  ⟨primeGapCertified_362_10_primes, primeGapCertified_362_10_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_11 : List PrimeCertificate :=
  [primeGapCertBatch36_35991583, primeGapCertBatch36_35991793, primeGapCertBatch36_35992003, primeGapCertBatch36_35992211, primeGapCertBatch36_35992399, primeGapCertBatch36_35992573, primeGapCertBatch36_35992771, primeGapCertBatch36_35992967, primeGapCertBatch36_35993173, primeGapCertBatch36_35993339, primeGapCertBatch36_35993549, primeGapCertBatch36_35993753, primeGapCertBatch36_35993927, primeGapCertBatch36_35994109, primeGapCertBatch36_35994319, primeGapCertBatch36_35994529, primeGapCertBatch36_35994733, primeGapCertBatch36_35994943, primeGapCertBatch36_35995153, primeGapCertBatch36_35995361, primeGapCertBatch36_35995571, primeGapCertBatch36_35995753, primeGapCertBatch36_35995933, primeGapCertBatch36_35996141, primeGapCertBatch36_35996351, primeGapCertBatch36_35996561, primeGapCertBatch36_35996759, primeGapCertBatch36_35996959, primeGapCertBatch36_35997163, primeGapCertBatch36_35997373, primeGapCertBatch36_35997581, primeGapCertBatch36_35997763, primeGapCertBatch36_35997943, primeGapCertBatch36_35998147, primeGapCertBatch36_35998351, primeGapCertBatch36_35998507, primeGapCertBatch36_35998717, primeGapCertBatch36_35998927, primeGapCertBatch36_35999123, primeGapCertBatch36_35999323]

private def primeGapCertified_362_11 : List ℕ :=
  [35991583, 35991793, 35992003, 35992211, 35992399, 35992573, 35992771, 35992967, 35993173, 35993339, 35993549, 35993753, 35993927, 35994109, 35994319, 35994529, 35994733, 35994943, 35995153, 35995361, 35995571, 35995753, 35995933, 35996141, 35996351, 35996561, 35996759, 35996959, 35997163, 35997373, 35997581, 35997763, 35997943, 35998147, 35998351, 35998507, 35998717, 35998927, 35999123, 35999323]

private lemma primeGapCertified_362_11_values :
    primeGapCertifiedCerts_362_11.map PrimeCertificate.value = primeGapCertified_362_11 := by
  rfl

private lemma primeGapCertified_362_11_primes : primeGapCertified_362_11.Forall Nat.Prime := by
  rw [← primeGapCertified_362_11_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_11_chain : primeGapCertified_362_11.IsChain GapStep := by
  norm_num [primeGapCertified_362_11, List.IsChain, GapStep]

private lemma primeGapCertified_362_11_segment :
    CertifiedSegment primeGapCertified_362_11 35991583 35999323 :=
  ⟨primeGapCertified_362_11_primes, primeGapCertified_362_11_chain, by rfl, by rfl⟩

private def primeGapCertifiedCerts_362_12 : List PrimeCertificate :=
  [primeGapCertBatch36_35999533, primeGapCertBatch36_35999723, primeGapCertBatch36_35999923, primeGapCertBatch36_36000127]

private def primeGapCertified_362_12 : List ℕ :=
  [35999533, 35999723, 35999923, 36000127]

private lemma primeGapCertified_362_12_values :
    primeGapCertifiedCerts_362_12.map PrimeCertificate.value = primeGapCertified_362_12 := by
  rfl

private lemma primeGapCertified_362_12_primes : primeGapCertified_362_12.Forall Nat.Prime := by
  rw [← primeGapCertified_362_12_values]
  exact PrimeCertificate.forall_prime_of_all_check (by rfl)

private lemma primeGapCertified_362_12_chain : primeGapCertified_362_12.IsChain GapStep := by
  norm_num [primeGapCertified_362_12, List.IsChain, GapStep]

private lemma primeGapCertified_362_12_segment :
    CertifiedSegment primeGapCertified_362_12 35999533 36000127 :=
  ⟨primeGapCertified_362_12_primes, primeGapCertified_362_12_chain, by rfl, by rfl⟩

private def primeGapCertifiedGroup362Step0 : List ℕ := primeGapCertified_362_0

private lemma primeGapCertifiedGroup362Step0_segment :
    CertifiedSegment primeGapCertifiedGroup362Step0 35904553 35912369 := by
  unfold primeGapCertifiedGroup362Step0
  exact primeGapCertified_362_0_segment

private def primeGapCertifiedGroup362Step1 : List ℕ :=
  primeGapCertifiedGroup362Step0 ++ primeGapCertified_362_1

private lemma primeGapCertifiedGroup362Step1_segment :
    CertifiedSegment primeGapCertifiedGroup362Step1 35904553 35920259 := by
  unfold primeGapCertifiedGroup362Step1
  exact primeGapCertifiedGroup362Step0_segment.append primeGapCertified_362_1_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step2 : List ℕ :=
  primeGapCertifiedGroup362Step1 ++ primeGapCertified_362_2

private lemma primeGapCertifiedGroup362Step2_segment :
    CertifiedSegment primeGapCertifiedGroup362Step2 35904553 35928161 := by
  unfold primeGapCertifiedGroup362Step2
  exact primeGapCertifiedGroup362Step1_segment.append primeGapCertified_362_2_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step3 : List ℕ :=
  primeGapCertifiedGroup362Step2 ++ primeGapCertified_362_3

private lemma primeGapCertifiedGroup362Step3_segment :
    CertifiedSegment primeGapCertifiedGroup362Step3 35904553 35936167 := by
  unfold primeGapCertifiedGroup362Step3
  exact primeGapCertifiedGroup362Step2_segment.append primeGapCertified_362_3_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step4 : List ℕ :=
  primeGapCertifiedGroup362Step3 ++ primeGapCertified_362_4

private lemma primeGapCertifiedGroup362Step4_segment :
    CertifiedSegment primeGapCertifiedGroup362Step4 35904553 35944187 := by
  unfold primeGapCertifiedGroup362Step4
  exact primeGapCertifiedGroup362Step3_segment.append primeGapCertified_362_4_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step5 : List ℕ :=
  primeGapCertifiedGroup362Step4 ++ primeGapCertified_362_5

private lemma primeGapCertifiedGroup362Step5_segment :
    CertifiedSegment primeGapCertifiedGroup362Step5 35904553 35952109 := by
  unfold primeGapCertifiedGroup362Step5
  exact primeGapCertifiedGroup362Step4_segment.append primeGapCertified_362_5_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step6 : List ℕ :=
  primeGapCertifiedGroup362Step5 ++ primeGapCertified_362_6

private lemma primeGapCertifiedGroup362Step6_segment :
    CertifiedSegment primeGapCertifiedGroup362Step6 35904553 35960021 := by
  unfold primeGapCertifiedGroup362Step6
  exact primeGapCertifiedGroup362Step5_segment.append primeGapCertified_362_6_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step7 : List ℕ :=
  primeGapCertifiedGroup362Step6 ++ primeGapCertified_362_7

private lemma primeGapCertifiedGroup362Step7_segment :
    CertifiedSegment primeGapCertifiedGroup362Step7 35904553 35967941 := by
  unfold primeGapCertifiedGroup362Step7
  exact primeGapCertifiedGroup362Step6_segment.append primeGapCertified_362_7_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step8 : List ℕ :=
  primeGapCertifiedGroup362Step7 ++ primeGapCertified_362_8

private lemma primeGapCertifiedGroup362Step8_segment :
    CertifiedSegment primeGapCertifiedGroup362Step8 35904553 35975827 := by
  unfold primeGapCertifiedGroup362Step8
  exact primeGapCertifiedGroup362Step7_segment.append primeGapCertified_362_8_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step9 : List ℕ :=
  primeGapCertifiedGroup362Step8 ++ primeGapCertified_362_9

private lemma primeGapCertifiedGroup362Step9_segment :
    CertifiedSegment primeGapCertifiedGroup362Step9 35904553 35983579 := by
  unfold primeGapCertifiedGroup362Step9
  exact primeGapCertifiedGroup362Step8_segment.append primeGapCertified_362_9_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step10 : List ℕ :=
  primeGapCertifiedGroup362Step9 ++ primeGapCertified_362_10

private lemma primeGapCertifiedGroup362Step10_segment :
    CertifiedSegment primeGapCertifiedGroup362Step10 35904553 35991383 := by
  unfold primeGapCertifiedGroup362Step10
  exact primeGapCertifiedGroup362Step9_segment.append primeGapCertified_362_10_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step11 : List ℕ :=
  primeGapCertifiedGroup362Step10 ++ primeGapCertified_362_11

private lemma primeGapCertifiedGroup362Step11_segment :
    CertifiedSegment primeGapCertifiedGroup362Step11 35904553 35999323 := by
  unfold primeGapCertifiedGroup362Step11
  exact primeGapCertifiedGroup362Step10_segment.append primeGapCertified_362_11_segment
    (by norm_num [GapStep])

private def primeGapCertifiedGroup362Step12 : List ℕ :=
  primeGapCertifiedGroup362Step11 ++ primeGapCertified_362_12

private lemma primeGapCertifiedGroup362Step12_segment :
    CertifiedSegment primeGapCertifiedGroup362Step12 35904553 36000127 := by
  unfold primeGapCertifiedGroup362Step12
  exact primeGapCertifiedGroup362Step11_segment.append primeGapCertified_362_12_segment
    (by norm_num [GapStep])

def primeGapCertifiedGroup362 : List ℕ := primeGapCertifiedGroup362Step12

lemma primeGapCertifiedGroup362_segment :
    CertifiedSegment primeGapCertifiedGroup362 35904553 36000127 := by
  unfold primeGapCertifiedGroup362
  exact primeGapCertifiedGroup362Step12_segment

end PrimeGap210Certificate

end Erdos1058
