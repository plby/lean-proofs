/-

This is a Lean formalization of a solution to Erdős Problem 56.
https://www.erdosproblems.com/56

The original human proof was found by: Rudolf Ahlswede and Levon H. Khachatrian

Ahlswede, Rudolf; Khachatrian, Levon H. On extremal sets without coprimes. Acta Arithmetica 66(1): 89–99 (1994).

ChatGPT from OpenAI explained some proof of this result (not
necessarily the original human proof, instead prioritizing clarity).

The LaTeX file output from the previous step was auto-formalized into
Lean by Aristotle from Harmonic.

The final theorem statement is from the Formal Conjectures project
organized by Google DeepMind.  (Note: it was modified slightly by
hand, because Aristotle found that it was missing a condition!)

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.deprecated false
set_option aesop.warn.nonterminal false

namespace Erdos56

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option linter.style.cases false
set_option linter.style.cdot false
set_option linter.style.longLine false
set_option linter.style.multiGoal false
set_option linter.style.openClassical false
set_option linter.style.refine false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option aesop.warn.nonterminal false

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

section PrimeCertificates

private lemma not_prime_of_divisor {d n : ℕ} (hdvd : d ∣ n) (hd : 2 ≤ d) (hdn : d < n) :
    ¬ Nat.Prime n :=
  Nat.not_prime_of_dvd_of_lt hdvd hd hdn

private lemma prime_of_no_small_divisors {n : ℕ}
    (hn : 2 ≤ n)
    (h : ∀ d, 2 ≤ d → d ≤ Nat.sqrt n → ¬ d ∣ n) :
    Nat.Prime n :=
  Nat.prime_def_le_sqrt.mpr ⟨hn, h⟩

syntax "prime_cert " num : command
macro_rules
  | `(prime_cert $n:num) => do
    let name := Lean.mkIdent <| Lean.Name.mkSimple s!"prime_{n.getNat}"
    `(@[local simp] lemma $name : Nat.Prime $n :=
        prime_of_no_small_divisors (by norm_num) (by
          intro d hd hds
          interval_cases d <;> norm_num))

syntax "not_prime_cert " num " divisor " num : command
macro_rules
  | `(not_prime_cert $n:num divisor $d:num) => do
    let name := Lean.mkIdent <| Lean.Name.mkSimple s!"not_prime_{n.getNat}"
    `(@[local simp] lemma $name : ¬ Nat.Prime $n :=
        not_prime_of_divisor (d := $d) (by norm_num) (by norm_num) (by norm_num))

@[local simp] lemma not_prime_0 : ¬ Nat.Prime 0 := Nat.not_prime_zero
@[local simp] lemma not_prime_1 : ¬ Nat.Prime 1 := Nat.not_prime_one

not_prime_cert 4 divisor 2
not_prime_cert 6 divisor 2
not_prime_cert 8 divisor 2
not_prime_cert 9 divisor 3
not_prime_cert 10 divisor 2
not_prime_cert 12 divisor 2
not_prime_cert 14 divisor 2
not_prime_cert 15 divisor 3
not_prime_cert 16 divisor 2
not_prime_cert 18 divisor 2
not_prime_cert 20 divisor 2
not_prime_cert 21 divisor 3
not_prime_cert 22 divisor 2
not_prime_cert 24 divisor 2
not_prime_cert 25 divisor 5
not_prime_cert 26 divisor 2
not_prime_cert 27 divisor 3
not_prime_cert 28 divisor 2
not_prime_cert 30 divisor 2
not_prime_cert 32 divisor 2
not_prime_cert 33 divisor 3
not_prime_cert 34 divisor 2
not_prime_cert 35 divisor 5
not_prime_cert 36 divisor 2
not_prime_cert 38 divisor 2
not_prime_cert 39 divisor 3
not_prime_cert 40 divisor 2
not_prime_cert 42 divisor 2
not_prime_cert 44 divisor 2
not_prime_cert 45 divisor 3
not_prime_cert 46 divisor 2
not_prime_cert 48 divisor 2
not_prime_cert 49 divisor 7
not_prime_cert 50 divisor 2
not_prime_cert 51 divisor 3
not_prime_cert 52 divisor 2
not_prime_cert 54 divisor 2
not_prime_cert 55 divisor 5
not_prime_cert 56 divisor 2
not_prime_cert 57 divisor 3
not_prime_cert 58 divisor 2
not_prime_cert 60 divisor 2
not_prime_cert 62 divisor 2
not_prime_cert 63 divisor 3
not_prime_cert 64 divisor 2
not_prime_cert 65 divisor 5
not_prime_cert 66 divisor 2
not_prime_cert 68 divisor 2
not_prime_cert 69 divisor 3
not_prime_cert 70 divisor 2
not_prime_cert 72 divisor 2
not_prime_cert 74 divisor 2
not_prime_cert 75 divisor 3
not_prime_cert 76 divisor 2
not_prime_cert 77 divisor 7
not_prime_cert 78 divisor 2
not_prime_cert 80 divisor 2
not_prime_cert 81 divisor 3
not_prime_cert 82 divisor 2
not_prime_cert 84 divisor 2
not_prime_cert 85 divisor 5
not_prime_cert 86 divisor 2
not_prime_cert 87 divisor 3
not_prime_cert 88 divisor 2
not_prime_cert 90 divisor 2
not_prime_cert 91 divisor 7
not_prime_cert 92 divisor 2
not_prime_cert 93 divisor 3
not_prime_cert 94 divisor 2
not_prime_cert 95 divisor 5
not_prime_cert 96 divisor 2
not_prime_cert 98 divisor 2
not_prime_cert 99 divisor 3
not_prime_cert 100 divisor 2
not_prime_cert 102 divisor 2
not_prime_cert 104 divisor 2
not_prime_cert 105 divisor 3
not_prime_cert 106 divisor 2
not_prime_cert 108 divisor 2
not_prime_cert 110 divisor 2
not_prime_cert 111 divisor 3
not_prime_cert 112 divisor 2
not_prime_cert 114 divisor 2
not_prime_cert 115 divisor 5
not_prime_cert 116 divisor 2
not_prime_cert 117 divisor 3
not_prime_cert 118 divisor 2
not_prime_cert 119 divisor 7
not_prime_cert 120 divisor 2
not_prime_cert 121 divisor 11
not_prime_cert 122 divisor 2
not_prime_cert 123 divisor 3
not_prime_cert 124 divisor 2
not_prime_cert 125 divisor 5
not_prime_cert 126 divisor 2
not_prime_cert 128 divisor 2
not_prime_cert 129 divisor 3
not_prime_cert 130 divisor 2
not_prime_cert 132 divisor 2
not_prime_cert 133 divisor 7
not_prime_cert 134 divisor 2
not_prime_cert 135 divisor 3
not_prime_cert 136 divisor 2
not_prime_cert 138 divisor 2
not_prime_cert 140 divisor 2
not_prime_cert 141 divisor 3
not_prime_cert 142 divisor 2
not_prime_cert 143 divisor 11
not_prime_cert 144 divisor 2
not_prime_cert 145 divisor 5
not_prime_cert 146 divisor 2
not_prime_cert 147 divisor 3
not_prime_cert 148 divisor 2
not_prime_cert 150 divisor 2
not_prime_cert 152 divisor 2
not_prime_cert 153 divisor 3
not_prime_cert 154 divisor 2
not_prime_cert 155 divisor 5
not_prime_cert 156 divisor 2
not_prime_cert 158 divisor 2
not_prime_cert 159 divisor 3
not_prime_cert 160 divisor 2
not_prime_cert 161 divisor 7
not_prime_cert 162 divisor 2
not_prime_cert 164 divisor 2
not_prime_cert 165 divisor 3
not_prime_cert 166 divisor 2
not_prime_cert 168 divisor 2
not_prime_cert 169 divisor 13
not_prime_cert 170 divisor 2
not_prime_cert 171 divisor 3
not_prime_cert 172 divisor 2
not_prime_cert 174 divisor 2
not_prime_cert 175 divisor 5
not_prime_cert 176 divisor 2
not_prime_cert 177 divisor 3
not_prime_cert 178 divisor 2
not_prime_cert 180 divisor 2
not_prime_cert 182 divisor 2
not_prime_cert 183 divisor 3
not_prime_cert 184 divisor 2
not_prime_cert 185 divisor 5
not_prime_cert 186 divisor 2
not_prime_cert 187 divisor 11
not_prime_cert 188 divisor 2
not_prime_cert 189 divisor 3
not_prime_cert 190 divisor 2
not_prime_cert 192 divisor 2
not_prime_cert 194 divisor 2
not_prime_cert 195 divisor 3
not_prime_cert 196 divisor 2
not_prime_cert 198 divisor 2
not_prime_cert 200 divisor 2
not_prime_cert 201 divisor 3
not_prime_cert 202 divisor 2
not_prime_cert 203 divisor 7
not_prime_cert 204 divisor 2
not_prime_cert 205 divisor 5
not_prime_cert 206 divisor 2
not_prime_cert 207 divisor 3
not_prime_cert 208 divisor 2
not_prime_cert 209 divisor 11
not_prime_cert 210 divisor 2
not_prime_cert 212 divisor 2
not_prime_cert 213 divisor 3
not_prime_cert 214 divisor 2
not_prime_cert 215 divisor 5
not_prime_cert 216 divisor 2
not_prime_cert 217 divisor 7
not_prime_cert 218 divisor 2
not_prime_cert 219 divisor 3
not_prime_cert 220 divisor 2
not_prime_cert 221 divisor 13
not_prime_cert 222 divisor 2
not_prime_cert 224 divisor 2
not_prime_cert 225 divisor 3
not_prime_cert 226 divisor 2
not_prime_cert 228 divisor 2
not_prime_cert 230 divisor 2
not_prime_cert 231 divisor 3
not_prime_cert 232 divisor 2
not_prime_cert 234 divisor 2
not_prime_cert 235 divisor 5
not_prime_cert 236 divisor 2
not_prime_cert 237 divisor 3
not_prime_cert 238 divisor 2
not_prime_cert 240 divisor 2
not_prime_cert 242 divisor 2
not_prime_cert 243 divisor 3
not_prime_cert 244 divisor 2
not_prime_cert 245 divisor 5
not_prime_cert 246 divisor 2
not_prime_cert 247 divisor 13
not_prime_cert 248 divisor 2
not_prime_cert 249 divisor 3
not_prime_cert 250 divisor 2
not_prime_cert 252 divisor 2
not_prime_cert 253 divisor 11
not_prime_cert 254 divisor 2
not_prime_cert 255 divisor 3
not_prime_cert 256 divisor 2
not_prime_cert 258 divisor 2
not_prime_cert 259 divisor 7
not_prime_cert 260 divisor 2
not_prime_cert 261 divisor 3
not_prime_cert 262 divisor 2
not_prime_cert 264 divisor 2
not_prime_cert 265 divisor 5
not_prime_cert 266 divisor 2
not_prime_cert 267 divisor 3
not_prime_cert 268 divisor 2
not_prime_cert 270 divisor 2
not_prime_cert 272 divisor 2
not_prime_cert 273 divisor 3
not_prime_cert 274 divisor 2
not_prime_cert 275 divisor 5
not_prime_cert 276 divisor 2
not_prime_cert 278 divisor 2
not_prime_cert 279 divisor 3
not_prime_cert 280 divisor 2
not_prime_cert 282 divisor 2
not_prime_cert 284 divisor 2
not_prime_cert 285 divisor 3
not_prime_cert 286 divisor 2
not_prime_cert 287 divisor 7
not_prime_cert 288 divisor 2
not_prime_cert 289 divisor 17
not_prime_cert 290 divisor 2
not_prime_cert 291 divisor 3
not_prime_cert 292 divisor 2
not_prime_cert 294 divisor 2
not_prime_cert 295 divisor 5
not_prime_cert 296 divisor 2
not_prime_cert 297 divisor 3
not_prime_cert 298 divisor 2
not_prime_cert 299 divisor 13
not_prime_cert 300 divisor 2
not_prime_cert 301 divisor 7
not_prime_cert 302 divisor 2
not_prime_cert 303 divisor 3
not_prime_cert 304 divisor 2
not_prime_cert 305 divisor 5
not_prime_cert 306 divisor 2
not_prime_cert 308 divisor 2
not_prime_cert 309 divisor 3
not_prime_cert 310 divisor 2
not_prime_cert 312 divisor 2
not_prime_cert 314 divisor 2
not_prime_cert 315 divisor 3
not_prime_cert 316 divisor 2
not_prime_cert 318 divisor 2
not_prime_cert 319 divisor 11
not_prime_cert 320 divisor 2
not_prime_cert 321 divisor 3
not_prime_cert 322 divisor 2
not_prime_cert 323 divisor 17
not_prime_cert 324 divisor 2
not_prime_cert 325 divisor 5
not_prime_cert 326 divisor 2
not_prime_cert 327 divisor 3
not_prime_cert 328 divisor 2
not_prime_cert 329 divisor 7
not_prime_cert 330 divisor 2
not_prime_cert 332 divisor 2
not_prime_cert 333 divisor 3
not_prime_cert 334 divisor 2
not_prime_cert 335 divisor 5
not_prime_cert 336 divisor 2
not_prime_cert 338 divisor 2
not_prime_cert 339 divisor 3
not_prime_cert 340 divisor 2
not_prime_cert 341 divisor 11
not_prime_cert 342 divisor 2
not_prime_cert 343 divisor 7
not_prime_cert 344 divisor 2
not_prime_cert 345 divisor 3
not_prime_cert 346 divisor 2
not_prime_cert 348 divisor 2
not_prime_cert 350 divisor 2
not_prime_cert 351 divisor 3
not_prime_cert 352 divisor 2
not_prime_cert 354 divisor 2
not_prime_cert 355 divisor 5
not_prime_cert 356 divisor 2
not_prime_cert 357 divisor 3
not_prime_cert 358 divisor 2
not_prime_cert 360 divisor 2
not_prime_cert 361 divisor 19
not_prime_cert 362 divisor 2
not_prime_cert 363 divisor 3
not_prime_cert 364 divisor 2
not_prime_cert 365 divisor 5
not_prime_cert 366 divisor 2
not_prime_cert 368 divisor 2
not_prime_cert 369 divisor 3
not_prime_cert 370 divisor 2
not_prime_cert 371 divisor 7
not_prime_cert 372 divisor 2
not_prime_cert 374 divisor 2
not_prime_cert 375 divisor 3
not_prime_cert 376 divisor 2
not_prime_cert 377 divisor 13
not_prime_cert 378 divisor 2
not_prime_cert 380 divisor 2
not_prime_cert 381 divisor 3
not_prime_cert 382 divisor 2
not_prime_cert 384 divisor 2
not_prime_cert 385 divisor 5
not_prime_cert 386 divisor 2
not_prime_cert 387 divisor 3
not_prime_cert 388 divisor 2
not_prime_cert 390 divisor 2
not_prime_cert 391 divisor 17
not_prime_cert 392 divisor 2
not_prime_cert 393 divisor 3
not_prime_cert 394 divisor 2
not_prime_cert 395 divisor 5
not_prime_cert 396 divisor 2
not_prime_cert 398 divisor 2
not_prime_cert 399 divisor 3
not_prime_cert 400 divisor 2
not_prime_cert 402 divisor 2
not_prime_cert 403 divisor 13
not_prime_cert 404 divisor 2
not_prime_cert 405 divisor 3
not_prime_cert 406 divisor 2
not_prime_cert 407 divisor 11
not_prime_cert 408 divisor 2
not_prime_cert 410 divisor 2
not_prime_cert 411 divisor 3
not_prime_cert 412 divisor 2
not_prime_cert 413 divisor 7
not_prime_cert 414 divisor 2
not_prime_cert 415 divisor 5
not_prime_cert 416 divisor 2
not_prime_cert 417 divisor 3
not_prime_cert 418 divisor 2
not_prime_cert 420 divisor 2
not_prime_cert 422 divisor 2
not_prime_cert 423 divisor 3
not_prime_cert 424 divisor 2
not_prime_cert 425 divisor 5
not_prime_cert 426 divisor 2
not_prime_cert 427 divisor 7
not_prime_cert 428 divisor 2
not_prime_cert 429 divisor 3
not_prime_cert 430 divisor 2
not_prime_cert 432 divisor 2
not_prime_cert 434 divisor 2
not_prime_cert 435 divisor 3
not_prime_cert 436 divisor 2
not_prime_cert 437 divisor 19
not_prime_cert 438 divisor 2
not_prime_cert 440 divisor 2
not_prime_cert 441 divisor 3
not_prime_cert 442 divisor 2
not_prime_cert 444 divisor 2
not_prime_cert 445 divisor 5
not_prime_cert 446 divisor 2
not_prime_cert 447 divisor 3
not_prime_cert 448 divisor 2
not_prime_cert 450 divisor 2
not_prime_cert 451 divisor 11
not_prime_cert 452 divisor 2
not_prime_cert 453 divisor 3
not_prime_cert 454 divisor 2
not_prime_cert 455 divisor 5
not_prime_cert 456 divisor 2
not_prime_cert 458 divisor 2
not_prime_cert 459 divisor 3
not_prime_cert 460 divisor 2
not_prime_cert 462 divisor 2
not_prime_cert 464 divisor 2
not_prime_cert 465 divisor 3
not_prime_cert 466 divisor 2
not_prime_cert 468 divisor 2
not_prime_cert 469 divisor 7
not_prime_cert 470 divisor 2
not_prime_cert 471 divisor 3
not_prime_cert 472 divisor 2
not_prime_cert 473 divisor 11
not_prime_cert 474 divisor 2
not_prime_cert 475 divisor 5
not_prime_cert 476 divisor 2
not_prime_cert 477 divisor 3
not_prime_cert 478 divisor 2
not_prime_cert 480 divisor 2
not_prime_cert 481 divisor 13
not_prime_cert 482 divisor 2
not_prime_cert 483 divisor 3
not_prime_cert 484 divisor 2
not_prime_cert 485 divisor 5
not_prime_cert 486 divisor 2
not_prime_cert 488 divisor 2
not_prime_cert 489 divisor 3
not_prime_cert 490 divisor 2
not_prime_cert 492 divisor 2
not_prime_cert 493 divisor 17
not_prime_cert 494 divisor 2
not_prime_cert 495 divisor 3
not_prime_cert 496 divisor 2
not_prime_cert 497 divisor 7
not_prime_cert 498 divisor 2
not_prime_cert 500 divisor 2
not_prime_cert 501 divisor 3
not_prime_cert 502 divisor 2
not_prime_cert 504 divisor 2
not_prime_cert 505 divisor 5
not_prime_cert 506 divisor 2
not_prime_cert 507 divisor 3
not_prime_cert 508 divisor 2
not_prime_cert 510 divisor 2
not_prime_cert 511 divisor 7
not_prime_cert 512 divisor 2
not_prime_cert 513 divisor 3
not_prime_cert 514 divisor 2
not_prime_cert 515 divisor 5
not_prime_cert 516 divisor 2
not_prime_cert 517 divisor 11
not_prime_cert 518 divisor 2
not_prime_cert 519 divisor 3
not_prime_cert 520 divisor 2
not_prime_cert 522 divisor 2
not_prime_cert 524 divisor 2
not_prime_cert 525 divisor 3
not_prime_cert 526 divisor 2
not_prime_cert 527 divisor 17
not_prime_cert 528 divisor 2
not_prime_cert 529 divisor 23
not_prime_cert 530 divisor 2
not_prime_cert 531 divisor 3
not_prime_cert 532 divisor 2
not_prime_cert 533 divisor 13
not_prime_cert 534 divisor 2
not_prime_cert 535 divisor 5
not_prime_cert 536 divisor 2
not_prime_cert 537 divisor 3
not_prime_cert 538 divisor 2
not_prime_cert 539 divisor 7
not_prime_cert 540 divisor 2
not_prime_cert 542 divisor 2
not_prime_cert 543 divisor 3
not_prime_cert 544 divisor 2
not_prime_cert 545 divisor 5
not_prime_cert 546 divisor 2
not_prime_cert 548 divisor 2
not_prime_cert 549 divisor 3
not_prime_cert 550 divisor 2
not_prime_cert 551 divisor 19
not_prime_cert 552 divisor 2
not_prime_cert 553 divisor 7
not_prime_cert 554 divisor 2
not_prime_cert 555 divisor 3
not_prime_cert 556 divisor 2
not_prime_cert 558 divisor 2
not_prime_cert 559 divisor 13
not_prime_cert 560 divisor 2
not_prime_cert 561 divisor 3
not_prime_cert 562 divisor 2
not_prime_cert 564 divisor 2
not_prime_cert 565 divisor 5
not_prime_cert 566 divisor 2
not_prime_cert 567 divisor 3
not_prime_cert 568 divisor 2
not_prime_cert 570 divisor 2
not_prime_cert 572 divisor 2
not_prime_cert 573 divisor 3
not_prime_cert 574 divisor 2
not_prime_cert 575 divisor 5
not_prime_cert 576 divisor 2
not_prime_cert 578 divisor 2
not_prime_cert 579 divisor 3
not_prime_cert 580 divisor 2
not_prime_cert 581 divisor 7
not_prime_cert 582 divisor 2
not_prime_cert 583 divisor 11
not_prime_cert 584 divisor 2
not_prime_cert 585 divisor 3
not_prime_cert 586 divisor 2
not_prime_cert 588 divisor 2
not_prime_cert 589 divisor 19
not_prime_cert 590 divisor 2
not_prime_cert 591 divisor 3
not_prime_cert 592 divisor 2
not_prime_cert 594 divisor 2
not_prime_cert 595 divisor 5
not_prime_cert 596 divisor 2
not_prime_cert 597 divisor 3
not_prime_cert 598 divisor 2
not_prime_cert 600 divisor 2
not_prime_cert 602 divisor 2
not_prime_cert 603 divisor 3
not_prime_cert 604 divisor 2
not_prime_cert 605 divisor 5
not_prime_cert 606 divisor 2
not_prime_cert 608 divisor 2
not_prime_cert 609 divisor 3
not_prime_cert 610 divisor 2
not_prime_cert 611 divisor 13
not_prime_cert 612 divisor 2
not_prime_cert 614 divisor 2
not_prime_cert 615 divisor 3
not_prime_cert 616 divisor 2
not_prime_cert 618 divisor 2
not_prime_cert 620 divisor 2
not_prime_cert 621 divisor 3
not_prime_cert 622 divisor 2
not_prime_cert 623 divisor 7
not_prime_cert 624 divisor 2
not_prime_cert 625 divisor 5
not_prime_cert 626 divisor 2
not_prime_cert 627 divisor 3
not_prime_cert 628 divisor 2
not_prime_cert 629 divisor 17
not_prime_cert 630 divisor 2
not_prime_cert 632 divisor 2
not_prime_cert 633 divisor 3
not_prime_cert 634 divisor 2
not_prime_cert 635 divisor 5
not_prime_cert 636 divisor 2
not_prime_cert 637 divisor 7
not_prime_cert 638 divisor 2
not_prime_cert 639 divisor 3
not_prime_cert 640 divisor 2
not_prime_cert 642 divisor 2
not_prime_cert 644 divisor 2
not_prime_cert 645 divisor 3
not_prime_cert 646 divisor 2
not_prime_cert 648 divisor 2
not_prime_cert 649 divisor 11
not_prime_cert 650 divisor 2
not_prime_cert 651 divisor 3
not_prime_cert 652 divisor 2
not_prime_cert 654 divisor 2
not_prime_cert 655 divisor 5
not_prime_cert 656 divisor 2
not_prime_cert 657 divisor 3
not_prime_cert 658 divisor 2
not_prime_cert 660 divisor 2
not_prime_cert 662 divisor 2
not_prime_cert 663 divisor 3
not_prime_cert 664 divisor 2
not_prime_cert 665 divisor 5
not_prime_cert 666 divisor 2
not_prime_cert 667 divisor 23
not_prime_cert 668 divisor 2
not_prime_cert 669 divisor 3
not_prime_cert 670 divisor 2
not_prime_cert 671 divisor 11
not_prime_cert 672 divisor 2
not_prime_cert 674 divisor 2
not_prime_cert 675 divisor 3
not_prime_cert 676 divisor 2
not_prime_cert 678 divisor 2
not_prime_cert 679 divisor 7
not_prime_cert 680 divisor 2
not_prime_cert 681 divisor 3
not_prime_cert 682 divisor 2
not_prime_cert 684 divisor 2
not_prime_cert 685 divisor 5
not_prime_cert 686 divisor 2
not_prime_cert 687 divisor 3
not_prime_cert 688 divisor 2
not_prime_cert 689 divisor 13
not_prime_cert 690 divisor 2
not_prime_cert 692 divisor 2
not_prime_cert 693 divisor 3
not_prime_cert 694 divisor 2
not_prime_cert 695 divisor 5
not_prime_cert 696 divisor 2
not_prime_cert 697 divisor 17
not_prime_cert 698 divisor 2
not_prime_cert 699 divisor 3
not_prime_cert 700 divisor 2
not_prime_cert 702 divisor 2
not_prime_cert 703 divisor 19
not_prime_cert 704 divisor 2
not_prime_cert 705 divisor 3
not_prime_cert 706 divisor 2
not_prime_cert 707 divisor 7
not_prime_cert 708 divisor 2
not_prime_cert 710 divisor 2
not_prime_cert 711 divisor 3
not_prime_cert 712 divisor 2
not_prime_cert 713 divisor 23
not_prime_cert 714 divisor 2
not_prime_cert 715 divisor 5
not_prime_cert 716 divisor 2
not_prime_cert 717 divisor 3
not_prime_cert 718 divisor 2
not_prime_cert 720 divisor 2
not_prime_cert 721 divisor 7
not_prime_cert 722 divisor 2
not_prime_cert 723 divisor 3
not_prime_cert 724 divisor 2
not_prime_cert 725 divisor 5
not_prime_cert 726 divisor 2
not_prime_cert 728 divisor 2
not_prime_cert 729 divisor 3
not_prime_cert 730 divisor 2
not_prime_cert 731 divisor 17
not_prime_cert 732 divisor 2
not_prime_cert 734 divisor 2
not_prime_cert 735 divisor 3
not_prime_cert 736 divisor 2
not_prime_cert 737 divisor 11
not_prime_cert 738 divisor 2
not_prime_cert 740 divisor 2
not_prime_cert 741 divisor 3
not_prime_cert 742 divisor 2
not_prime_cert 744 divisor 2
not_prime_cert 745 divisor 5
not_prime_cert 746 divisor 2
not_prime_cert 747 divisor 3
not_prime_cert 748 divisor 2
not_prime_cert 749 divisor 7
not_prime_cert 750 divisor 2
not_prime_cert 752 divisor 2
not_prime_cert 753 divisor 3
not_prime_cert 754 divisor 2
not_prime_cert 755 divisor 5
not_prime_cert 756 divisor 2
not_prime_cert 758 divisor 2
not_prime_cert 759 divisor 3
not_prime_cert 760 divisor 2
not_prime_cert 762 divisor 2
not_prime_cert 763 divisor 7
not_prime_cert 764 divisor 2
not_prime_cert 765 divisor 3
not_prime_cert 766 divisor 2
not_prime_cert 767 divisor 13
not_prime_cert 768 divisor 2
not_prime_cert 770 divisor 2
not_prime_cert 771 divisor 3
not_prime_cert 772 divisor 2
not_prime_cert 774 divisor 2
not_prime_cert 775 divisor 5
not_prime_cert 776 divisor 2
not_prime_cert 777 divisor 3
not_prime_cert 778 divisor 2
not_prime_cert 779 divisor 19
not_prime_cert 780 divisor 2
not_prime_cert 781 divisor 11
not_prime_cert 782 divisor 2
not_prime_cert 783 divisor 3
not_prime_cert 784 divisor 2
not_prime_cert 785 divisor 5
not_prime_cert 786 divisor 2
not_prime_cert 788 divisor 2
not_prime_cert 789 divisor 3
not_prime_cert 790 divisor 2
not_prime_cert 791 divisor 7
not_prime_cert 792 divisor 2
not_prime_cert 793 divisor 13
not_prime_cert 794 divisor 2
not_prime_cert 795 divisor 3
not_prime_cert 796 divisor 2
not_prime_cert 798 divisor 2
not_prime_cert 799 divisor 17
not_prime_cert 800 divisor 2
not_prime_cert 801 divisor 3
not_prime_cert 802 divisor 2
not_prime_cert 803 divisor 11
not_prime_cert 804 divisor 2
not_prime_cert 805 divisor 5
not_prime_cert 806 divisor 2
not_prime_cert 807 divisor 3
not_prime_cert 808 divisor 2
not_prime_cert 810 divisor 2
not_prime_cert 812 divisor 2
not_prime_cert 813 divisor 3
not_prime_cert 814 divisor 2
not_prime_cert 815 divisor 5
not_prime_cert 816 divisor 2
not_prime_cert 817 divisor 19
not_prime_cert 818 divisor 2
not_prime_cert 819 divisor 3
not_prime_cert 820 divisor 2
not_prime_cert 822 divisor 2
not_prime_cert 824 divisor 2
not_prime_cert 825 divisor 3
not_prime_cert 826 divisor 2
not_prime_cert 828 divisor 2
not_prime_cert 830 divisor 2
not_prime_cert 831 divisor 3
not_prime_cert 832 divisor 2
not_prime_cert 833 divisor 7
not_prime_cert 834 divisor 2
not_prime_cert 835 divisor 5
not_prime_cert 836 divisor 2
not_prime_cert 837 divisor 3
not_prime_cert 838 divisor 2
not_prime_cert 840 divisor 2
not_prime_cert 841 divisor 29
not_prime_cert 842 divisor 2
not_prime_cert 843 divisor 3
not_prime_cert 844 divisor 2
not_prime_cert 845 divisor 5
not_prime_cert 846 divisor 2
not_prime_cert 847 divisor 7
not_prime_cert 848 divisor 2
not_prime_cert 849 divisor 3
not_prime_cert 850 divisor 2
not_prime_cert 851 divisor 23
not_prime_cert 852 divisor 2
not_prime_cert 854 divisor 2
not_prime_cert 855 divisor 3
not_prime_cert 856 divisor 2
not_prime_cert 858 divisor 2
not_prime_cert 860 divisor 2
not_prime_cert 861 divisor 3
not_prime_cert 862 divisor 2
not_prime_cert 864 divisor 2
not_prime_cert 865 divisor 5
not_prime_cert 866 divisor 2
not_prime_cert 867 divisor 3
not_prime_cert 868 divisor 2
not_prime_cert 869 divisor 11
not_prime_cert 870 divisor 2
not_prime_cert 871 divisor 13
not_prime_cert 872 divisor 2
not_prime_cert 873 divisor 3
not_prime_cert 874 divisor 2
not_prime_cert 875 divisor 5
not_prime_cert 876 divisor 2
not_prime_cert 878 divisor 2
not_prime_cert 879 divisor 3
not_prime_cert 880 divisor 2
not_prime_cert 882 divisor 2
not_prime_cert 884 divisor 2
not_prime_cert 885 divisor 3
not_prime_cert 886 divisor 2
not_prime_cert 888 divisor 2
not_prime_cert 889 divisor 7
not_prime_cert 890 divisor 2
not_prime_cert 891 divisor 3
not_prime_cert 892 divisor 2
not_prime_cert 893 divisor 19
not_prime_cert 894 divisor 2
not_prime_cert 895 divisor 5
not_prime_cert 896 divisor 2
not_prime_cert 897 divisor 3
not_prime_cert 898 divisor 2
not_prime_cert 899 divisor 29
not_prime_cert 900 divisor 2
not_prime_cert 901 divisor 17
not_prime_cert 902 divisor 2
not_prime_cert 903 divisor 3
not_prime_cert 904 divisor 2
not_prime_cert 905 divisor 5
not_prime_cert 906 divisor 2
not_prime_cert 908 divisor 2
not_prime_cert 909 divisor 3
not_prime_cert 910 divisor 2
not_prime_cert 912 divisor 2
not_prime_cert 913 divisor 11
not_prime_cert 914 divisor 2
not_prime_cert 915 divisor 3
not_prime_cert 916 divisor 2
not_prime_cert 917 divisor 7
not_prime_cert 918 divisor 2
not_prime_cert 920 divisor 2
not_prime_cert 921 divisor 3
not_prime_cert 922 divisor 2
not_prime_cert 923 divisor 13
not_prime_cert 924 divisor 2
not_prime_cert 925 divisor 5
not_prime_cert 926 divisor 2
not_prime_cert 927 divisor 3
not_prime_cert 928 divisor 2
not_prime_cert 930 divisor 2
not_prime_cert 931 divisor 7
not_prime_cert 932 divisor 2
not_prime_cert 933 divisor 3
not_prime_cert 934 divisor 2
not_prime_cert 935 divisor 5
not_prime_cert 936 divisor 2
not_prime_cert 938 divisor 2
not_prime_cert 939 divisor 3
not_prime_cert 940 divisor 2
not_prime_cert 942 divisor 2
not_prime_cert 943 divisor 23
not_prime_cert 944 divisor 2
not_prime_cert 945 divisor 3
not_prime_cert 946 divisor 2
not_prime_cert 948 divisor 2
not_prime_cert 949 divisor 13
not_prime_cert 950 divisor 2
not_prime_cert 951 divisor 3
not_prime_cert 952 divisor 2
not_prime_cert 954 divisor 2
not_prime_cert 955 divisor 5
not_prime_cert 956 divisor 2
not_prime_cert 957 divisor 3
not_prime_cert 958 divisor 2
not_prime_cert 959 divisor 7
not_prime_cert 960 divisor 2
not_prime_cert 961 divisor 31
not_prime_cert 962 divisor 2
not_prime_cert 963 divisor 3
not_prime_cert 964 divisor 2
not_prime_cert 965 divisor 5
not_prime_cert 966 divisor 2
not_prime_cert 968 divisor 2
not_prime_cert 969 divisor 3
not_prime_cert 970 divisor 2
not_prime_cert 972 divisor 2
not_prime_cert 973 divisor 7
not_prime_cert 974 divisor 2
not_prime_cert 975 divisor 3
not_prime_cert 976 divisor 2
not_prime_cert 978 divisor 2
not_prime_cert 979 divisor 11
not_prime_cert 980 divisor 2
not_prime_cert 981 divisor 3
not_prime_cert 982 divisor 2
not_prime_cert 984 divisor 2
not_prime_cert 985 divisor 5
not_prime_cert 986 divisor 2
not_prime_cert 987 divisor 3
not_prime_cert 988 divisor 2
not_prime_cert 989 divisor 23
not_prime_cert 990 divisor 2
not_prime_cert 992 divisor 2
not_prime_cert 993 divisor 3
not_prime_cert 994 divisor 2
not_prime_cert 995 divisor 5
not_prime_cert 996 divisor 2
not_prime_cert 998 divisor 2
not_prime_cert 999 divisor 3
not_prime_cert 1000 divisor 2
not_prime_cert 1001 divisor 7
not_prime_cert 1002 divisor 2
not_prime_cert 1003 divisor 17
not_prime_cert 1004 divisor 2
not_prime_cert 1005 divisor 3
not_prime_cert 1006 divisor 2
not_prime_cert 1007 divisor 19
not_prime_cert 1008 divisor 2
not_prime_cert 1010 divisor 2
not_prime_cert 1011 divisor 3
not_prime_cert 1012 divisor 2
not_prime_cert 1014 divisor 2
not_prime_cert 1015 divisor 5
not_prime_cert 1016 divisor 2
not_prime_cert 1017 divisor 3
not_prime_cert 1018 divisor 2
not_prime_cert 1020 divisor 2
not_prime_cert 1022 divisor 2
not_prime_cert 1023 divisor 3
not_prime_cert 1024 divisor 2
not_prime_cert 1025 divisor 5
not_prime_cert 1026 divisor 2
not_prime_cert 1027 divisor 13
not_prime_cert 1028 divisor 2
not_prime_cert 1029 divisor 3
not_prime_cert 1030 divisor 2
not_prime_cert 1032 divisor 2
not_prime_cert 1034 divisor 2
not_prime_cert 1035 divisor 3
not_prime_cert 1036 divisor 2
not_prime_cert 1037 divisor 17
not_prime_cert 1038 divisor 2
not_prime_cert 1040 divisor 2
not_prime_cert 1041 divisor 3
not_prime_cert 1042 divisor 2
not_prime_cert 1043 divisor 7
not_prime_cert 1044 divisor 2
not_prime_cert 1045 divisor 5
not_prime_cert 1046 divisor 2
not_prime_cert 1047 divisor 3
not_prime_cert 1048 divisor 2
not_prime_cert 1050 divisor 2
not_prime_cert 1052 divisor 2
not_prime_cert 1053 divisor 3
not_prime_cert 1054 divisor 2
not_prime_cert 1055 divisor 5
not_prime_cert 1056 divisor 2
not_prime_cert 1057 divisor 7
not_prime_cert 1058 divisor 2
not_prime_cert 1059 divisor 3
not_prime_cert 1060 divisor 2
not_prime_cert 1062 divisor 2
not_prime_cert 1064 divisor 2
not_prime_cert 1065 divisor 3
not_prime_cert 1066 divisor 2
not_prime_cert 1067 divisor 11
not_prime_cert 1068 divisor 2
not_prime_cert 1070 divisor 2
not_prime_cert 1071 divisor 3
not_prime_cert 1072 divisor 2
not_prime_cert 1073 divisor 29
not_prime_cert 1074 divisor 2
not_prime_cert 1075 divisor 5
not_prime_cert 1076 divisor 2
not_prime_cert 1077 divisor 3
not_prime_cert 1078 divisor 2
not_prime_cert 1079 divisor 13
not_prime_cert 1080 divisor 2
not_prime_cert 1081 divisor 23
not_prime_cert 1082 divisor 2
not_prime_cert 1083 divisor 3
not_prime_cert 1084 divisor 2
not_prime_cert 1085 divisor 5
not_prime_cert 1086 divisor 2
not_prime_cert 1088 divisor 2
not_prime_cert 1089 divisor 3
not_prime_cert 1090 divisor 2
not_prime_cert 1092 divisor 2
not_prime_cert 1094 divisor 2
not_prime_cert 1095 divisor 3
not_prime_cert 1096 divisor 2
not_prime_cert 1098 divisor 2
not_prime_cert 1099 divisor 7
not_prime_cert 1100 divisor 2
not_prime_cert 1101 divisor 3
not_prime_cert 1102 divisor 2
not_prime_cert 1104 divisor 2
not_prime_cert 1105 divisor 5
not_prime_cert 1106 divisor 2
not_prime_cert 1107 divisor 3
not_prime_cert 1108 divisor 2
not_prime_cert 1110 divisor 2
not_prime_cert 1111 divisor 11
not_prime_cert 1112 divisor 2
not_prime_cert 1113 divisor 3
not_prime_cert 1114 divisor 2
not_prime_cert 1115 divisor 5
not_prime_cert 1116 divisor 2
not_prime_cert 1118 divisor 2
not_prime_cert 1119 divisor 3
not_prime_cert 1120 divisor 2
not_prime_cert 1121 divisor 19
not_prime_cert 1122 divisor 2
not_prime_cert 1124 divisor 2
not_prime_cert 1125 divisor 3
not_prime_cert 1126 divisor 2
not_prime_cert 1127 divisor 7
not_prime_cert 1128 divisor 2
not_prime_cert 1130 divisor 2
not_prime_cert 1131 divisor 3
not_prime_cert 1132 divisor 2
not_prime_cert 1133 divisor 11
not_prime_cert 1134 divisor 2
not_prime_cert 1135 divisor 5
not_prime_cert 1136 divisor 2
not_prime_cert 1137 divisor 3
not_prime_cert 1138 divisor 2
not_prime_cert 1139 divisor 17
not_prime_cert 1140 divisor 2
not_prime_cert 1141 divisor 7
not_prime_cert 1142 divisor 2
not_prime_cert 1143 divisor 3
not_prime_cert 1144 divisor 2
not_prime_cert 1145 divisor 5
not_prime_cert 1146 divisor 2
not_prime_cert 1147 divisor 31
not_prime_cert 1148 divisor 2
not_prime_cert 1149 divisor 3
not_prime_cert 1150 divisor 2
not_prime_cert 1152 divisor 2
not_prime_cert 1154 divisor 2
not_prime_cert 1155 divisor 3
not_prime_cert 1156 divisor 2
not_prime_cert 1157 divisor 13
not_prime_cert 1158 divisor 2
not_prime_cert 1159 divisor 19
not_prime_cert 1160 divisor 2
not_prime_cert 1161 divisor 3
not_prime_cert 1162 divisor 2
not_prime_cert 1164 divisor 2
not_prime_cert 1165 divisor 5
not_prime_cert 1166 divisor 2
not_prime_cert 1167 divisor 3
not_prime_cert 1168 divisor 2
not_prime_cert 1169 divisor 7
not_prime_cert 1170 divisor 2
not_prime_cert 1172 divisor 2
not_prime_cert 1173 divisor 3
not_prime_cert 1174 divisor 2
not_prime_cert 1175 divisor 5
not_prime_cert 1176 divisor 2
not_prime_cert 1177 divisor 11
not_prime_cert 1178 divisor 2
not_prime_cert 1179 divisor 3
not_prime_cert 1180 divisor 2
not_prime_cert 1182 divisor 2
not_prime_cert 1183 divisor 7
not_prime_cert 1184 divisor 2
not_prime_cert 1185 divisor 3
not_prime_cert 1186 divisor 2
not_prime_cert 1188 divisor 2
not_prime_cert 1189 divisor 29
not_prime_cert 1190 divisor 2
not_prime_cert 1191 divisor 3
not_prime_cert 1192 divisor 2
not_prime_cert 1194 divisor 2
not_prime_cert 1195 divisor 5
not_prime_cert 1196 divisor 2
not_prime_cert 1197 divisor 3
not_prime_cert 1198 divisor 2
not_prime_cert 1199 divisor 11
not_prime_cert 1200 divisor 2
not_prime_cert 1202 divisor 2
not_prime_cert 1203 divisor 3
not_prime_cert 1204 divisor 2
not_prime_cert 1205 divisor 5
not_prime_cert 1206 divisor 2
not_prime_cert 1207 divisor 17
not_prime_cert 1208 divisor 2
not_prime_cert 1209 divisor 3
not_prime_cert 1210 divisor 2
not_prime_cert 1211 divisor 7
not_prime_cert 1212 divisor 2
not_prime_cert 1214 divisor 2
not_prime_cert 1215 divisor 3
not_prime_cert 1216 divisor 2
not_prime_cert 1218 divisor 2
not_prime_cert 1219 divisor 23
not_prime_cert 1220 divisor 2
not_prime_cert 1221 divisor 3
not_prime_cert 1222 divisor 2
not_prime_cert 1224 divisor 2
not_prime_cert 1225 divisor 5
not_prime_cert 1226 divisor 2
not_prime_cert 1227 divisor 3
not_prime_cert 1228 divisor 2
not_prime_cert 1230 divisor 2
not_prime_cert 1232 divisor 2
not_prime_cert 1233 divisor 3
not_prime_cert 1234 divisor 2
not_prime_cert 1235 divisor 5
not_prime_cert 1236 divisor 2
not_prime_cert 1238 divisor 2
not_prime_cert 1239 divisor 3
not_prime_cert 1240 divisor 2
not_prime_cert 1241 divisor 17
not_prime_cert 1242 divisor 2
not_prime_cert 1243 divisor 11
not_prime_cert 1244 divisor 2
not_prime_cert 1245 divisor 3
not_prime_cert 1246 divisor 2
not_prime_cert 1247 divisor 29
not_prime_cert 1248 divisor 2
not_prime_cert 1250 divisor 2
not_prime_cert 1251 divisor 3
not_prime_cert 1252 divisor 2
not_prime_cert 1253 divisor 7
not_prime_cert 1254 divisor 2
not_prime_cert 1255 divisor 5
not_prime_cert 1256 divisor 2
not_prime_cert 1257 divisor 3
not_prime_cert 1258 divisor 2
not_prime_cert 1260 divisor 2
not_prime_cert 1261 divisor 13
not_prime_cert 1262 divisor 2
not_prime_cert 1263 divisor 3
not_prime_cert 1264 divisor 2
not_prime_cert 1265 divisor 5
not_prime_cert 1266 divisor 2
not_prime_cert 1267 divisor 7
not_prime_cert 1268 divisor 2
not_prime_cert 1269 divisor 3
not_prime_cert 1270 divisor 2
not_prime_cert 1271 divisor 31
not_prime_cert 1272 divisor 2
not_prime_cert 1273 divisor 19
not_prime_cert 1274 divisor 2
not_prime_cert 1275 divisor 3
not_prime_cert 1276 divisor 2
not_prime_cert 1278 divisor 2
not_prime_cert 1280 divisor 2
not_prime_cert 1281 divisor 3
not_prime_cert 1282 divisor 2
not_prime_cert 1284 divisor 2
not_prime_cert 1285 divisor 5
not_prime_cert 1286 divisor 2
not_prime_cert 1287 divisor 3
not_prime_cert 1288 divisor 2
not_prime_cert 1290 divisor 2
not_prime_cert 1292 divisor 2
not_prime_cert 1293 divisor 3
not_prime_cert 1294 divisor 2
not_prime_cert 1295 divisor 5
not_prime_cert 1296 divisor 2
not_prime_cert 1298 divisor 2
not_prime_cert 1299 divisor 3
not_prime_cert 1300 divisor 2
not_prime_cert 1302 divisor 2
not_prime_cert 1304 divisor 2
not_prime_cert 1305 divisor 3
not_prime_cert 1306 divisor 2
not_prime_cert 1308 divisor 2
not_prime_cert 1309 divisor 7
not_prime_cert 1310 divisor 2
not_prime_cert 1311 divisor 3
not_prime_cert 1312 divisor 2
not_prime_cert 1313 divisor 13
not_prime_cert 1314 divisor 2
not_prime_cert 1315 divisor 5
not_prime_cert 1316 divisor 2
not_prime_cert 1317 divisor 3
not_prime_cert 1318 divisor 2
not_prime_cert 1320 divisor 2
not_prime_cert 1322 divisor 2
not_prime_cert 1323 divisor 3
not_prime_cert 1324 divisor 2
not_prime_cert 1325 divisor 5
not_prime_cert 1326 divisor 2
not_prime_cert 1328 divisor 2
not_prime_cert 1329 divisor 3
not_prime_cert 1330 divisor 2
not_prime_cert 1331 divisor 11
not_prime_cert 1332 divisor 2
not_prime_cert 1333 divisor 31
not_prime_cert 1334 divisor 2
not_prime_cert 1335 divisor 3
not_prime_cert 1336 divisor 2
not_prime_cert 1337 divisor 7
not_prime_cert 1338 divisor 2
not_prime_cert 1339 divisor 13
not_prime_cert 1340 divisor 2
not_prime_cert 1341 divisor 3
not_prime_cert 1342 divisor 2
not_prime_cert 1343 divisor 17
not_prime_cert 1344 divisor 2
not_prime_cert 1345 divisor 5
not_prime_cert 1346 divisor 2
not_prime_cert 1347 divisor 3
not_prime_cert 1348 divisor 2
not_prime_cert 1349 divisor 19
not_prime_cert 1350 divisor 2
not_prime_cert 1351 divisor 7
not_prime_cert 1352 divisor 2
not_prime_cert 1353 divisor 3
not_prime_cert 1354 divisor 2
not_prime_cert 1355 divisor 5
not_prime_cert 1356 divisor 2
not_prime_cert 1357 divisor 23
not_prime_cert 1358 divisor 2
not_prime_cert 1359 divisor 3
not_prime_cert 1360 divisor 2

prime_cert 2
prime_cert 3
prime_cert 5
prime_cert 7
prime_cert 11
prime_cert 13
prime_cert 17
prime_cert 19
prime_cert 23
prime_cert 29
prime_cert 31
prime_cert 37
prime_cert 41
prime_cert 43
prime_cert 47
prime_cert 53
prime_cert 59
prime_cert 61
prime_cert 67
prime_cert 71
prime_cert 73
prime_cert 79
prime_cert 83
prime_cert 89
prime_cert 97
prime_cert 101
prime_cert 103
prime_cert 107
prime_cert 109
prime_cert 113
prime_cert 127
prime_cert 131
prime_cert 137
prime_cert 139
prime_cert 149
prime_cert 151
prime_cert 157
prime_cert 163
prime_cert 167
prime_cert 173
prime_cert 179
prime_cert 181
prime_cert 191
prime_cert 193
prime_cert 197
prime_cert 199
prime_cert 211
prime_cert 223
prime_cert 227
prime_cert 229
prime_cert 233
prime_cert 239
prime_cert 241
prime_cert 251
prime_cert 257
prime_cert 263
prime_cert 269
prime_cert 271
prime_cert 277
prime_cert 281
prime_cert 283
prime_cert 293
prime_cert 307
prime_cert 311
prime_cert 313
prime_cert 317
prime_cert 331
prime_cert 337
prime_cert 347
prime_cert 349
prime_cert 353
prime_cert 359
prime_cert 367
prime_cert 373
prime_cert 379
prime_cert 383
prime_cert 389
prime_cert 397
prime_cert 401
prime_cert 409
prime_cert 419
prime_cert 421
prime_cert 431
prime_cert 433
prime_cert 439
prime_cert 443
prime_cert 449
prime_cert 457
prime_cert 461
prime_cert 463
prime_cert 467
prime_cert 479
prime_cert 487
prime_cert 491
prime_cert 499
prime_cert 503
prime_cert 509
prime_cert 521
prime_cert 523
prime_cert 541
prime_cert 547
prime_cert 557
prime_cert 563
prime_cert 569
prime_cert 571
prime_cert 577
prime_cert 587
prime_cert 593
prime_cert 599
prime_cert 601
prime_cert 607
prime_cert 613
prime_cert 617
prime_cert 619
prime_cert 631
prime_cert 641
prime_cert 643
prime_cert 647
prime_cert 653
prime_cert 659
prime_cert 661
prime_cert 673
prime_cert 677
prime_cert 683
prime_cert 691
prime_cert 701
prime_cert 709
prime_cert 719
prime_cert 727
prime_cert 733
prime_cert 739
prime_cert 743
prime_cert 751
prime_cert 757
prime_cert 761
prime_cert 769
prime_cert 773
prime_cert 787
prime_cert 797
prime_cert 809
prime_cert 811
prime_cert 821
prime_cert 823
prime_cert 827
prime_cert 829
prime_cert 839
prime_cert 853
prime_cert 857
prime_cert 859
prime_cert 863
prime_cert 877
prime_cert 881
prime_cert 883
prime_cert 887
prime_cert 907
prime_cert 911
prime_cert 919
prime_cert 929
prime_cert 937
prime_cert 941
prime_cert 947
prime_cert 953
prime_cert 967
prime_cert 971
prime_cert 977
prime_cert 983
prime_cert 991
prime_cert 997
prime_cert 1009
prime_cert 1013
prime_cert 1019
prime_cert 1021
prime_cert 1031
prime_cert 1033
prime_cert 1039
prime_cert 1049
prime_cert 1051
prime_cert 1061
prime_cert 1063
prime_cert 1069
prime_cert 1087
prime_cert 1091
prime_cert 1093
prime_cert 1097
prime_cert 1103
prime_cert 1109
prime_cert 1117
prime_cert 1123
prime_cert 1129
prime_cert 1151
prime_cert 1153
prime_cert 1163
prime_cert 1171
prime_cert 1181
prime_cert 1187
prime_cert 1193
prime_cert 1201
prime_cert 1213
prime_cert 1217
prime_cert 1223
prime_cert 1229
prime_cert 1231
prime_cert 1237
prime_cert 1249
prime_cert 1259
prime_cert 1277
prime_cert 1279
prime_cert 1283
prime_cert 1289
prime_cert 1291
prime_cert 1297
prime_cert 1301
prime_cert 1303
prime_cert 1307
prime_cert 1319
prime_cert 1321
prime_cert 1327
prime_cert 1361

set_option maxRecDepth 12000 in
lemma count_prime_1289 : Nat.count Nat.Prime 1289 = 208 := by
  simp [Nat.count_succ]

set_option maxRecDepth 12000 in
lemma count_prime_1291 : Nat.count Nat.Prime 1291 = 209 := by
  simp [Nat.count_succ]

set_option maxRecDepth 12000 in
lemma count_prime_1297 : Nat.count Nat.Prime 1297 = 210 := by
  simp [Nat.count_succ]

set_option maxRecDepth 12000 in
lemma count_prime_1301 : Nat.count Nat.Prime 1301 = 211 := by
  simp [Nat.count_succ]

set_option maxRecDepth 12000 in
lemma count_prime_1303 : Nat.count Nat.Prime 1303 = 212 := by
  simp [Nat.count_succ]

set_option maxRecDepth 12000 in
lemma count_prime_1307 : Nat.count Nat.Prime 1307 = 213 := by
  simp [Nat.count_succ]

set_option maxRecDepth 12000 in
lemma count_prime_1319 : Nat.count Nat.Prime 1319 = 214 := by
  simp [Nat.count_succ]

set_option maxRecDepth 12000 in
lemma count_prime_1321 : Nat.count Nat.Prime 1321 = 215 := by
  simp [Nat.count_succ]

set_option maxRecDepth 12000 in
lemma count_prime_1327 : Nat.count Nat.Prime 1327 = 216 := by
  simp [Nat.count_succ]

set_option maxRecDepth 12000 in
lemma count_prime_1361 : Nat.count Nat.Prime 1361 = 217 := by
  simp [Nat.count_succ]

set_option maxRecDepth 12000 in
lemma count_prime_1362 : Nat.count Nat.Prime 1362 = 218 := by
  simp [Nat.count_succ]

lemma count_prime_1362_gt_217 : 217 < Nat.count Nat.Prime 1362 := by
  rw [count_prime_1362]
  norm_num

end PrimeCertificates
def P (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

def E (n k : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun m => m.gcd (P k) > 1)

def has_no_k_plus_1_coprime (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ S ⊆ A, (S : Set ℕ).Pairwise Nat.Coprime → S.card ≤ k

noncomputable def f (n k : ℕ) : ℕ :=
  ((Finset.powerset (Finset.Icc 1 n)).filter (fun A => has_no_k_plus_1_coprime A k)).sup Finset.card

def t_val : ℕ := 209
def k_val : ℕ := 212

def p (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

def C_set : Finset ℕ :=
  ((Finset.range 9).product (Finset.range 9)).image
    (fun x => p (t_val + x.1) * p (t_val + x.2))
  |>.filter (fun m => ∃ i j, 0 ≤ i ∧ i < j ∧ j ≤ 8 ∧ m = p (t_val + i) * p (t_val + j))

def B_set (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun m => m.gcd (P (t_val - 1)) > 1)

def A_set (n : ℕ) : Finset ℕ := B_set n ∪ C_set

def satisfies_H (t : ℕ) : Prop :=
  p (t + 7) * p (t + 8) < p t * p (t + 9) ∧ p (t + 9) < (p t) ^ 2

def interval_start (t : ℕ) : ℕ := p (t + 7) * p (t + 8)
def interval_end (t : ℕ) : ℕ := p t * p (t + 9)

def B (t n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun m => m.gcd (P (t - 1)) > 1)

def C (t : ℕ) : Finset ℕ :=
  ((Finset.range 9).product (Finset.range 9)).image
    (fun x => p (t + x.1) * p (t + x.2))
  |>.filter (fun m => ∃ i j, i < j ∧ j ≤ 8 ∧ m = p (t + i) * p (t + j))

def A (t n : ℕ) : Finset ℕ := B t n ∪ C t

def D (t n : ℕ) : Finset ℕ := (E n (t + 3)) \ (B t n)

lemma E_no_k_plus_1 (n k : ℕ) : has_no_k_plus_1_coprime (E n k) k := by
  intro S hS_sub hS_coprime
  -- For each element $s \in S$, there exists a prime $p_j$ in the set $\{p_1, p_2, \ldots, p_k\}$ such that $p_j \mid s$.
  have h_prime_divisors : ∀ s ∈ S, ∃ j ∈ Finset.range k, Nat.Prime (Nat.nth Nat.Prime j) ∧ Nat.nth Nat.Prime j ∣ s := by
    intro s hs; specialize hS_sub hs; unfold E at hS_sub; aesop;
    -- Since $\gcd(s, P(k)) > 1$, there exists a prime $p$ such that $p \mid s$ and $p \mid P(k)$.
    obtain ⟨p, hp_prime, hp_div_s, hp_div_Pk⟩ : ∃ p, Nat.Prime p ∧ p ∣ s ∧ p ∣ P k := by
      -- Since $\gcd(s, P(k)) > 1$, there exists a prime $p$ that divides both $s$ and $P(k)$ by the definition of gcd.
      exact Nat.Prime.not_coprime_iff_dvd.mp (ne_of_gt right)
      -- Since $p \mid P(k)$, we know that $p$ is one of the first $k$ primes.
    have hp_prime_index : p ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range k) := by
      unfold P at hp_div_Pk
      have hp_div_prime : ∃ i ∈ Finset.range k, p ∣ Nat.nth Nat.Prime i := by
        exact (Prime.dvd_finset_prod_iff
          (show Prime p from hp_prime.prime) (fun i => Nat.nth Nat.Prime i)).1 hp_div_Pk
      obtain ⟨ i, hi, hi' ⟩ := hp_div_prime
      exact Finset.mem_image.mpr
        ⟨ i, hi, ((Nat.prime_dvd_prime_iff_eq hp_prime ( Nat.prime_nth_prime i )).mp hi').symm ⟩
    obtain ⟨j, hj, hj_eq⟩ := Finset.mem_image.mp hp_prime_index
    exact ⟨j, Finset.mem_range.mp hj, by rw [hj_eq]; exact hp_div_s⟩
  choose! f hf using h_prime_divisors;
  have h_distinct_primes : Finset.card (Finset.image f S) ≤ k := by
    exact le_trans ( Finset.card_le_card ( Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr ( hf x hx |>.1 |> Finset.mem_range.mp ) ) ) ( by simpa );
  rwa [ Finset.card_image_of_injOn fun x hx y hy hxy => Classical.not_not.1 fun h => Nat.Prime.not_dvd_one ( hf x hx |>.2.1 ) <| hS_coprime hx hy h |> fun h => h.gcd_eq_one ▸ Nat.dvd_gcd ( hf x hx |>.2.2 ) ( hxy.symm ▸ hf y hy |>.2.2 ) ] at h_distinct_primes


lemma C_subset_n (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) : C t ⊆ Finset.Icc 1 n := by
  intro x hx;
  -- Since $x \in C t$, we have $x = p(t+i) * p(t+j)$ for some $0 \leq i < j \leq 8$.
  obtain ⟨i, j, hi, hj, hx_eq⟩ : ∃ i j, 0 ≤ i ∧ i < j ∧ j ≤ 8 ∧ x = p (t + i) * p (t + j) := by
    unfold C at hx; aesop;
  -- Since $p$ is strictly increasing, $p(t+i) \leq p(t+7)$ and $p(t+j) \leq p(t+8)$.
  have h_p_le : p (t + i) ≤ p (t + 7) ∧ p (t + j) ≤ p (t + 8) := by
    -- Since $p$ is strictly increasing, if $i < j$, then $p(t+i) < p(t+j)$. Also, since $j \leq 8$, we have $p(t+j) \leq p(t+8)$.
    have h_p_le : ∀ i j : ℕ, i < j → j ≤ 8 → p (t + i) ≤ p (t + 7) ∧ p (t + j) ≤ p (t + 8) := by
      intros i j hij hj8;
      exact ⟨ Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by omega ), Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by omega ) ⟩;
    exact h_p_le i j hj hx_eq.1;
  exact Finset.mem_Icc.mpr ⟨ by nlinarith only [ hx_eq.2, h_p_le, Nat.Prime.pos ( show Nat.Prime ( p ( t + i ) ) from Nat.prime_nth_prime _ ), Nat.Prime.pos ( show Nat.Prime ( p ( t + j ) ) from Nat.prime_nth_prime _ ) ], by nlinarith only [ hx_eq.2, h_p_le, h_n, show interval_start t = p ( t + 7 ) * p ( t + 8 ) from rfl ] ⟩

lemma B_disjoint_C (t n : ℕ) : Disjoint (B t n) (C t) := by
  -- If $x \in B t n$, then $x$ is not coprime with $P(t-1)$, which means $x$ has a prime factor $q \leq p(t-1)$.
  have hB_factor : ∀ x ∈ B t n, ∃ q, Nat.Prime q ∧ q ∣ x ∧ q ≤ p (t - 1) := by
    -- Since $x$ is not coprime with $P(t-1)$, it must have a prime factor $q$ that divides $P(t-1)$.
    intro x hx
    obtain ⟨q, hq_prime, hq_div⟩ : ∃ q, Nat.Prime q ∧ q ∣ x ∧ q ∣ P (t - 1) := by
      -- Since $x$ is not coprime with $P(t-1)$, their greatest common divisor is greater than 1, which implies there exists a prime $q$ that divides both $x$ and $P(t-1)$.
      have h_gcd : Nat.gcd x (P (t - 1)) > 1 := by
        unfold B at hx; aesop;
      -- Since the gcd of x and P(t-1) is greater than 1, there exists a prime q that divides both x and P(t-1).
      apply Nat.Prime.not_coprime_iff_dvd.mp; exact ne_of_gt h_gcd;
    refine' ⟨ q, hq_prime, hq_div.1, _ ⟩;
    -- Since $q$ divides $P(t-1)$, it must be one of the prime factors of $P(t-1)$.
    have hq_factor : q ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t - 1)) := by
      have hq_prime_div : q ∣ ∏ i ∈ Finset.range (t - 1), Nat.nth Nat.Prime i := by
        exact hq_div.2;
      simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ];
      obtain ⟨ a, ha₁, ha₂ ⟩ := hq_prime_div; exact ⟨ a, ha₁, by have := Nat.coprime_primes hq_prime ( Nat.prime_nth_prime a ) ; aesop ⟩ ;
    norm_num +zetaDelta at *;
    obtain ⟨ a, ha₁, ha₂ ⟩ := hq_factor; exact ha₂ ▸ Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( Nat.le_sub_one_of_lt ha₁ ) ;
  -- If $x \in C t$, then $x$ is a product of primes $p(t+i)$ and $p(t+j)$ where $i, j \geq 0$. Since $p$ is strictly increasing, $p(t+i) \geq p(t)$ and $p(t+j) \geq p(t)$.
  have hC_factor : ∀ x ∈ C t, ∀ q, Nat.Prime q → q ∣ x → q ≥ p t := by
    -- Since $p$ is strictly increasing, $p(t+i) \geq p(t)$ and $p(t+j) \geq p(t)$ for any $i, j \geq 0$.
    have h_prime_factors : ∀ i j : ℕ, 0 ≤ i → i < j → j ≤ 8 → p (t + i) ≥ p t ∧ p (t + j) ≥ p t := by
      -- Since $p$ is strictly increasing, for any $m \geq n$, we have $p(m) \geq p(n)$.
      have h_prime_mono : ∀ m n : ℕ, m ≥ n → p m ≥ p n := by
        aesop;
        unfold p;
        rw [ Nat.nth_le_nth _ ];
        · omega;
        · exact Nat.infinite_setOf_prime;
      exact fun i j hi hj hj' => ⟨ h_prime_mono _ _ ( by linarith ), h_prime_mono _ _ ( by linarith ) ⟩;
    -- Since $x \in C t$, we can write $x = p(t+i) * p(t+j)$ for some $0 \leq i < j \leq 8$.
    intro x hx q hq_prime hq_div
    obtain ⟨i, j, hi, hj, hx_eq⟩ : ∃ i j : ℕ, 0 ≤ i ∧ i < j ∧ j ≤ 8 ∧ x = p (t + i) * p (t + j) := by
      unfold C at hx; aesop;
    simp_all +decide [ Nat.Prime.dvd_mul ];
    rcases hq_div with ( h | h ) <;> have := Nat.prime_dvd_prime_iff_eq hq_prime ( show Nat.Prime ( p ( t + i ) ) from Nat.prime_nth_prime _ ) <;> have := Nat.prime_dvd_prime_iff_eq hq_prime ( show Nat.Prime ( p ( t + j ) ) from Nat.prime_nth_prime _ ) <;> aesop;
    · linarith [ h_prime_factors i j hj left ];
    · linarith [ h_prime_factors i j hj left ];
  -- If there exists an element $x$ in both $B t n$ and $C t$, then by $hB_factor$, there exists a prime $q$ such that $q \mid x$ and $q \leq p(t-1)$. But by $hC_factor$, any prime divisor of $x$ must be $\geq p(t)$. This is a contradiction because $p(t-1) < p(t)$.
  have h_contradiction : ∀ x, x ∈ B t n → x ∈ C t → False := by
    -- If there exists an element $x$ in both $B t n$ and $C t$, then by $hB_factor$, there exists a prime $q$ such that $q \mid x$ and $q \leq p(t-1)$. But by $hC_factor$, any prime divisor of $x$ must be $\geq p(t)$. This is a contradiction because $p(t-1) < p(t)$, so $q$ cannot be both $\leq p(t-1)$ and $\geq p(t)$.
    intros x hx_B hx_C
    obtain ⟨q, hq_prime, hq_div_x, hq_le⟩ := hB_factor x hx_B
    have hq_ge : q ≥ p t := hC_factor x hx_C q hq_prime hq_div_x
    have h_contradiction : p t ≤ p (t - 1) := by
      grind
    rcases t with ( _ | _ | t )
    · simp_all +decide [ Nat.nth_zero ]
      unfold B at hx_B; unfold C at hx_C; aesop;
      unfold P at right; aesop;
    · simp_all +decide [ Nat.nth_zero ]
      unfold B C at * ; aesop;
      unfold P at * ; aesop;
    · simp_all +decide [ Nat.nth_zero ]
      exact (not_lt_of_ge h_contradiction) ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( Nat.lt_succ_self _ ) );
  exact Finset.disjoint_left.mpr h_contradiction


lemma t_ge_one_of_satisfies_H (t : ℕ) (h : satisfies_H t) : t ≥ 1 := by
  contrapose! h; aesop; ( unfold satisfies_H at *; aesop );
  unfold p at * ; norm_num at *;
  linarith [ Nat.Prime.two_le ( Nat.prime_nth_prime 6 ), Nat.Prime.two_le ( Nat.prime_nth_prime 7 ), Nat.Prime.two_le ( Nat.prime_nth_prime 8 ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 6 < 7 by norm_num ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 7 < 8 by norm_num ) ]

lemma C_map_injective (t : ℕ) (ht : t ≥ 1) :
  ∀ i j k l, 0 ≤ i ∧ i < j ∧ j ≤ 8 → 0 ≤ k ∧ k < l ∧ l ≤ 8 →
  p (t + i) * p (t + j) = p (t + k) * p (t + l) → i = k ∧ j = l := by
    -- By the uniqueness of prime factorization, the sets {p(t+i), p(t+j)} and {p(t+k), p(t+l)} must be equal.
    intros i j k l hi hj h_eq
    have h_set_eq : ({p (t + i), p (t + j)} : Finset ℕ) = ({p (t + k), p (t + l)} : Finset ℕ) := by
      -- Since $p$ is injective, the sets $\{p(t+i), p(t+j)\}$ and $\{p(t+k), p(t+l)\}$ must be equal.
      have h_prime_factors : ∀ {a b c d : ℕ}, Nat.Prime a → Nat.Prime b → Nat.Prime c → Nat.Prime d → a * b = c * d → ({a, b} : Finset ℕ) = ({c, d} : Finset ℕ) := by
        -- Since $a$ and $b$ are primes, the prime factors of $a * b$ are exactly $a$ and $b$. Similarly, the prime factors of $c * d$ are $c$ and $d$. Therefore, the sets $\{a, b\}$ and $\{c, d\}$ must be equal.
        intros a b c d ha hb hc hd h_eq
        have h_prime_factors : Nat.primeFactors (a * b) = {a, b} ∧ Nat.primeFactors (c * d) = {c, d} := by
          rw [ Nat.primeFactors_mul, Nat.primeFactors_mul ] <;> aesop;
        aesop;
      exact h_prime_factors ( Nat.prime_nth_prime _ ) ( Nat.prime_nth_prime _ ) ( Nat.prime_nth_prime _ ) ( Nat.prime_nth_prime _ ) h_eq;
    -- Since $p$ is strictly increasing, we have $p(t+i) = p(t+k)$ and $p(t+j) = p(t+l)$ or $p(t+i) = p(t+l)$ and $p(t+j) = p(t+k)$.
    have h_cases : p (t + i) = p (t + k) ∧ p (t + j) = p (t + l) ∨ p (t + i) = p (t + l) ∧ p (t + j) = p (t + k) := by
      rw [ Finset.ext_iff ] at h_set_eq ; aesop;
      cases h_set_eq ( p ( t + i ) ) ; cases h_set_eq ( p ( t + j ) ) ; aesop;
    unfold p at *;
    aesop;
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) left_2; omega;
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) right_2; aesop;
      omega;
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) left_2; have := Nat.nth_injective ( Nat.infinite_setOf_prime ) right_2; aesop;
      omega;
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) left_2; have := Nat.nth_injective ( Nat.infinite_setOf_prime ) right_2; omega;

lemma card_C (t : ℕ) (h : satisfies_H t) : (C t).card = 36 := by
  -- By definition of $C$, the set $C t$ is the image of the set of pairs $(i, j)$ with $0 \leq i < j \leq 8$ under the map $(i, j) \mapsto p(t+i)p(t+j)$.
  have hC_image : C t = Finset.image (fun (x : ℕ × ℕ) => Nat.nth Nat.Prime (t + x.1 - 1) * Nat.nth Nat.Prime (t + x.2 - 1)) (Finset.filter (fun x => x.1 < x.2 ∧ x.2 ≤ 8) (Finset.product (Finset.range 9) (Finset.range 9))) := by
    -- By definition of $C$, we know that $C t$ is the image of the set of pairs $(i, j)$ with $0 \leq i < j \leq 8$ under the map $(i, j) \mapsto p(t+i)p(t+j)$.
    ext; simp [C];
    constructor;
    · rintro ⟨ ⟨ a, b, ⟨ ha, hb ⟩, rfl ⟩, i, j, hij, hj, h ⟩ ; use i, j ; aesop;
      · linarith;
      · linarith;
    · aesop;
  -- To prove the cardinality, we show that the function (i, j) ↦ p(t+i)p(t+j) is injective on the set of pairs (i, j) with 0 ≤ i < j ≤ 8.
  have h_inj : ∀ i j k l : ℕ, 0 ≤ i → i < j → j ≤ 8 → 0 ≤ k → k < l → l ≤ 8 → Nat.nth Nat.Prime (t + i - 1) * Nat.nth Nat.Prime (t + j - 1) = Nat.nth Nat.Prime (t + k - 1) * Nat.nth Nat.Prime (t + l - 1) → i = k ∧ j = l := by
    -- Since the primes are distinct and ordered, the equality of the products implies the equality of the indices.
    intros i j k l hi hj hj8 hk hl hl8 h_eq
    have h_prime_eq : Nat.nth Nat.Prime (t + i - 1) = Nat.nth Nat.Prime (t + k - 1) ∧ Nat.nth Nat.Prime (t + j - 1) = Nat.nth Nat.Prime (t + l - 1) ∨ Nat.nth Nat.Prime (t + i - 1) = Nat.nth Nat.Prime (t + l - 1) ∧ Nat.nth Nat.Prime (t + j - 1) = Nat.nth Nat.Prime (t + k - 1) := by
      have := congr_arg ( fun x => x.factorization ( Nat.nth Nat.Prime ( t + i - 1 ) ) ) h_eq ; norm_num [ Nat.factorization_mul, Nat.Prime.ne_zero ] at this;
      rw [ Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply ] at this ; aesop;
      · exact absurd h_2 ( Nat.Prime.ne_zero ( Nat.prime_nth_prime _ ) );
      · nlinarith [ Nat.Prime.one_lt ( Nat.prime_nth_prime ( t + i - 1 ) ) ];
    cases h_prime_eq <;> simp_all +decide [ Nat.nth_injective ];
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) ( by tauto : Nat.nth Nat.Prime ( t + i - 1 ) = Nat.nth Nat.Prime ( t + k - 1 ) ) ; ( have := Nat.nth_injective ( Nat.infinite_setOf_prime ) ( by tauto : Nat.nth Nat.Prime ( t + j - 1 ) = Nat.nth Nat.Prime ( t + l - 1 ) ) ; aesop; );
      · rcases t with ( _ | _ | t ) <;> simp_all +arith +decide;
        have := h.1; ( have := h.2; ( norm_num [ Nat.nth_zero ] at *; ) );
        unfold p at * ; simp_all +decide [ Nat.Prime.two_le ];
        linarith [ Nat.Prime.two_le ( Nat.prime_nth_prime 6 ), Nat.Prime.two_le ( Nat.prime_nth_prime 7 ), Nat.Prime.two_le ( Nat.prime_nth_prime 8 ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 6 < 7 by norm_num ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 7 < 8 by norm_num ) ];
      · omega;
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) ( by aesop : Nat.nth Nat.Prime ( t + i - 1 ) = Nat.nth Nat.Prime ( t + l - 1 ) ) ; have := Nat.nth_injective ( Nat.infinite_setOf_prime ) ( by aesop : Nat.nth Nat.Prime ( t + j - 1 ) = Nat.nth Nat.Prime ( t + k - 1 ) ) ; omega;
  exact hC_image.symm ▸ Finset.card_image_of_injOn ( fun x hx y hy hxy => by specialize h_inj x.1 x.2 y.1 y.2; aesop )

lemma card_A (t n : ℕ) (h_disjoint : Disjoint (B t n) (C t)) (h : satisfies_H t) : (A t n).card = (B t n).card + 36 := by
  -- By definition of C, we know that its cardinality is 36.
  have h_C_card : (C t).card = 36 := by
    -- Let's prove that the map $x \mapsto p_{t+x}$ is injective for $0 \leq x \leq 8$.
    have h_map_injective : Function.Injective (fun x : ℕ => p (t + x)) := by
      have h_inj : StrictMono (fun x => p (t + x)) := by
        refine' strictMono_nat_of_lt_succ fun x => _;
        apply Nat.nth_strictMono;
        · exact Nat.infinite_setOf_prime;
        · simp +zetaDelta at *;
          contrapose! h; aesop;
          cases a ; aesop;
          unfold p at *;
          norm_num [ Nat.nth_zero ] at *;
          rw [ show InfSet.sInf ( setOf Nat.Prime ) = 2 by exact le_antisymm ( Nat.sInf_le Nat.prime_two ) ( le_csInf ⟨ 2, Nat.prime_two ⟩ fun x hx => Nat.Prime.two_le hx ) ] at * ; norm_num at *;
          linarith [ Nat.Prime.two_le ( Nat.prime_nth_prime 6 ), Nat.Prime.two_le ( Nat.prime_nth_prime 7 ), Nat.Prime.two_le ( Nat.prime_nth_prime 8 ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 6 < 7 by norm_num ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 7 < 8 by norm_num ) ];
      exact h_inj.injective;
    -- Since the map $x \mapsto p_{t+x}$ is injective, the image of the set of pairs $\{(i,j) \mid 0 \leq i < j \leq 8\}$ under this map has the same cardinality as the set of pairs itself.
    have h_image_card : (Finset.image (fun (x : ℕ × ℕ) => p (t + x.1) * p (t + x.2)) (Finset.filter (fun (x : ℕ × ℕ) => x.1 < x.2 ∧ x.2 ≤ 8) (Finset.product (Finset.range 9) (Finset.range 9)))).card = (Finset.filter (fun (x : ℕ × ℕ) => x.1 < x.2 ∧ x.2 ≤ 8) (Finset.product (Finset.range 9) (Finset.range 9))).card := by
      apply Finset.card_image_of_injOn;
      intros x hx y hy hxy;
      -- Since the primes are distinct, the products being equal implies that the sets {p(t+x.1), p(t+x.2)} and {p(t+y.1), p(t+y.2)} are the same.
      have h_sets_eq : ({p (t + x.1), p (t + x.2)} : Finset ℕ) = ({p (t + y.1), p (t + y.2)} : Finset ℕ) := by
        have h_prime_factors : Nat.primeFactors (p (t + x.1) * p (t + x.2)) = {p (t + x.1), p (t + x.2)} ∧ Nat.primeFactors (p (t + y.1) * p (t + y.2)) = {p (t + y.1), p (t + y.2)} := by
          have h_prime_factors : ∀ i j : ℕ, Nat.Prime (p (t + i)) ∧ Nat.Prime (p (t + j)) → i ≠ j → Nat.primeFactors (p (t + i) * p (t + j)) = {p (t + i), p (t + j)} := by
            intros i j h_prime_factors h_neq; rw [ Nat.primeFactors_mul ] <;> aesop;
          exact ⟨ h_prime_factors _ _ ⟨ Nat.prime_nth_prime _, Nat.prime_nth_prime _ ⟩ ( by aesop ), h_prime_factors _ _ ⟨ Nat.prime_nth_prime _, Nat.prime_nth_prime _ ⟩ ( by aesop ) ⟩;
        grind;
      simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
      simp_all +decide [ h_map_injective.eq_iff ];
      grind +ring;
    -- Since $C t$ is defined as the image of the set of pairs under the map, we can conclude that their cardinalities are equal.
    have h_C_eq_image : C t = Finset.image (fun (x : ℕ × ℕ) => p (t + x.1) * p (t + x.2)) (Finset.filter (fun (x : ℕ × ℕ) => x.1 < x.2 ∧ x.2 ≤ 8) (Finset.product (Finset.range 9) (Finset.range 9))) := by
      ext; simp [C];
      constructor;
      · rintro ⟨ ⟨ a, b, ⟨ ha, hb ⟩, rfl ⟩, i, j, hij, hj, h ⟩ ; exact ⟨ i, j, ⟨ ⟨ by linarith, by linarith ⟩, hij, hj ⟩, h.symm ⟩;
      · rintro ⟨ a, b, ⟨ ⟨ ha, hb ⟩, hab, hb' ⟩, rfl ⟩ ; exact ⟨ ⟨ a, b, ⟨ ha, hb ⟩, rfl ⟩, a, b, hab, hb', rfl ⟩;
    exact h_C_eq_image ▸ h_image_card;
  rw [ ← h_C_card, ← Finset.card_union_of_disjoint h_disjoint, A ]


lemma p_strictMono_new {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : p i < p j := by
  apply Nat.nth_strictMono;
  · exact Nat.infinite_setOf_prime;
  · -- Since $i < j$, subtracting 1 from both sides preserves the inequality.
    apply Nat.sub_lt_sub_right; exact hi; exact hij

lemma t_ge_one_of_satisfies_H_new (t : ℕ) (h : satisfies_H t) : t ≥ 1 := by
  exact t_ge_one_of_satisfies_H t h

lemma C_map_injective_new (t : ℕ) (ht : t ≥ 1) :
  ∀ i j k l, 0 ≤ i ∧ i < j ∧ j ≤ 8 → 0 ≤ k ∧ k < l ∧ l ≤ 8 →
  p (t + i) * p (t + j) = p (t + k) * p (t + l) → i = k ∧ j = l := by
    -- Apply the uniqueness factorization lemma.
    apply C_map_injective t ht

lemma card_C_new (t : ℕ) (h : satisfies_H t) : (C t).card = 36 := by
  -- Apply the lemma `card_C` with the given `h`.
  apply card_C; assumption

lemma card_A_new (t n : ℕ) (h_disjoint : Disjoint (B t n) (C t)) (h : satisfies_H t) : (A t n).card = (B t n).card + 36 := by
  rw [ show A t n = B t n ∪ C t from rfl, ← card_C t h, Finset.card_union_of_disjoint h_disjoint ]


lemma max_B (t n : ℕ) : has_no_k_plus_1_coprime (B t n) (t - 1) := by
  -- For each $u \in B$, there exists a prime $p_i$ in the set $\{p_1, p_2, \dots, p_{t-1}\}$ such that $p_i \mid u$.
  have h_prime_divisor (u : ℕ) (hu : u ∈ B t n) : ∃ i ∈ Finset.range (t - 1), Nat.nth Nat.Prime i ∣ u := by
    unfold B at hu; aesop;
    contrapose! right;
    exact le_of_eq ( Nat.Coprime.prod_right fun i hi => Nat.coprime_comm.mp <| Nat.Prime.coprime_iff_not_dvd ( Nat.prime_nth_prime i ) |>.2 <| right i <| Finset.mem_range.mp hi );
  -- For any pairwise coprime subset S of B, each element in S must be associated with a unique prime from the set {p_1, ..., p_{t-1}}.
  have h_association (S : Finset ℕ) (hS : S ⊆ B t n) (h_pairwise_coprime : (S : Set ℕ).Pairwise Nat.Coprime) : S.card ≤ (Finset.range (t - 1)).card := by
    -- Since each element in S is divisible by some prime in the first t-1 primes, we can map each element of S to one of these primes.
    have h_map : ∃ f : ℕ → ℕ, ∀ u ∈ S, f u ∈ Finset.range (t - 1) ∧ Nat.nth Nat.Prime (f u) ∣ u := by
      choose! f hf using h_prime_divisor;
      exact ⟨ f, fun u hu => hf u ( hS hu ) ⟩;
    -- Since $f$ is injective, the cardinality of $S$ is bounded by the cardinality of the image of $S$ under $f$, which is a subset of the range $(t-1)$.
    obtain ⟨f, hf⟩ := h_map
    have h_inj : ∀ u v, u ∈ S → v ∈ S → f u = f v → u = v := by
      -- If $f u = f v$, then $u$ and $v$ are both divisible by the same prime $p_{f u}$, which contradicts the pairwise coprimality of $S$.
      intros u v hu hv h_eq
      have h_div : Nat.nth Nat.Prime (f u) ∣ u ∧ Nat.nth Nat.Prime (f u) ∣ v := by
        grind;
      have := Nat.dvd_gcd h_div.1 h_div.2; by_cases hu : u = v <;> aesop;
      exact Nat.Prime.not_dvd_one ( Nat.prime_nth_prime _ ) ( this.trans ( by simpa [ hu ] using h_pairwise_coprime hu_1 hv hu ) );
    exact Finset.card_le_card ( show S.image f ⊆ Finset.range ( t - 1 ) from Finset.image_subset_iff.2 fun u hu => by aesop ) |> le_trans ( by rw [ Finset.card_image_of_injOn fun u hu v hv huv => h_inj u v hu hv huv ] )
  aesop


lemma max_C (t : ℕ) : has_no_k_plus_1_coprime (C t) 4 := by
  -- Define the function f that maps each element of C t to its corresponding pair of indices.
  set f : ℕ → Finset ℕ := fun x => Finset.filter (fun i => x % p (t + i) = 0) (Finset.range 9);
  -- Let $S$ be a pairwise coprime subset of $C$.
  intro S hS hS_coprime
  have h_disjoint : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (f x) (f y) := by
    -- If there exists an $i$ such that $p(t+i)$ divides both $x$ and $y$, then $p(t+i)$ would divide their gcd, which is 1. This is impossible since $p(t+i)$ is a prime number greater than 1.
    intros x hx y hy hxy
    by_contra h_inter
    obtain ⟨i, hi⟩ : ∃ i, i ∈ f x ∧ i ∈ f y := by
      -- By definition of disjointness, if two sets are not disjoint, then there exists an element in their intersection.
      apply Finset.not_disjoint_iff.mp h_inter;
    have h_div : p (t + i) ∣ Nat.gcd x y := by
      exact Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero ( Finset.mem_filter.mp hi.1 |>.2 ) ) ( Nat.dvd_of_mod_eq_zero ( Finset.mem_filter.mp hi.2 |>.2 ) );
    have := hS_coprime hx hy hxy; simp_all +decide [ Nat.dvd_gcd_iff ] ;
    exact Nat.Prime.ne_one ( Nat.prime_nth_prime _ ) h_div;
  -- The union of the images of S under f is a subset of {0, 1, ..., 8}, which has 9 elements.
  have h_union_card : (Finset.biUnion S f).card ≤ 9 := by
    -- Since each $f(x)$ is a subset of $\{0, 1, ..., 8\}$, the union of these subsets is also a subset of $\{0, 1, ..., 8\}$.
    have h_union_subset : Finset.biUnion S f ⊆ Finset.range 9 := by
      exact Finset.biUnion_subset.mpr fun x hx => Finset.filter_subset _ _;
    -- Since the union of the images of S under f is a subset of {0, 1, ..., 8}, its cardinality is at most 9.
    apply Finset.card_le_card h_union_subset;
  -- Since each element in S contributes at least 2 elements to the union, we have $2 * S.card \leq 9$.
  have h_card_f : ∀ x ∈ S, (f x).card ≥ 2 := by
    -- Since each element in S is of the form p(t+i) * p(t+j) with i < j, the set f x will contain at least i and j, making its cardinality at least 2.
    intros x hx
    obtain ⟨i, j, hij, hx_eq⟩ : ∃ i j, 0 ≤ i ∧ i < j ∧ j ≤ 8 ∧ x = p (t + i) * p (t + j) := by
      have := hS hx; unfold C at this; aesop;
    refine Finset.one_lt_card.mpr ⟨ i, ?_, j, ?_, ?_ ⟩ <;> aesop;
    · linarith;
    · linarith;
  -- Since the f(x) are pairwise disjoint, the sum of their cardinalities is equal to the cardinality of their union.
  have h_sum_card : ∑ x ∈ S, (f x).card = (Finset.biUnion S f).card := by
    rw [ Finset.card_biUnion ] ; aesop;
  exact Nat.le_of_lt_succ ( by have := Finset.sum_le_sum h_card_f; norm_num at *; linarith )


lemma p_t_injective (t : ℕ) (ht : t ≥ 1) : Function.Injective (fun i => p (t + i)) := by
  -- Since $p$ is strictly increasing, if $p(t + i) = p(t + j)$, then $t + i = t + j$, which implies $i = j$.
  have h_inj : StrictMono (fun i => p (t + i)) := by
    exact fun i j hij => p_strictMono_new ( by linarith ) ( by linarith );
  exact StrictMono.injective h_inj

def prime_indices (t x : ℕ) : Finset ℕ := (Finset.range 9).filter (fun i => p (t + i) ∣ x)

lemma prime_indices_card (t x : ℕ) (hx : x ∈ C t) (ht : t ≥ 1) : (prime_indices t x).card = 2 := by
  -- Since $x \in C t$, there exist $a$ and $b$ such that $x = p(t+a) * p(t+b)$ and $0 \leq a < b \leq 8$.
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b, 0 ≤ a ∧ a < b ∧ b ≤ 8 ∧ x = p (t + a) * p (t + b) := by
    unfold C at hx; aesop;
  -- Since $p(t+i)$ divides $x$ if and only if $i = a$ or $i = b$, the set $\{i \mid p(t+i) \mid x\}$ is exactly $\{a, b\}$.
  have h_set_eq : {i | p (t + i) ∣ x} = {a, b} := by
    ext i; aesop;
    -- Since $p(t+i)$ divides $p(t+a) * p(t+b)$ and $p$ is injective, it must divide one of $p(t+a)$ or $p(t+b)$.
    have h_div : p (t + i) ∣ p (t + a) ∨ p (t + i) ∣ p (t + b) := by
      convert Nat.Prime.dvd_mul ( show Nat.Prime ( p ( t + i ) ) from Nat.prime_nth_prime _ ) |>.1 a_1 using 1;
    -- Since $p$ is injective, if $p(t+i)$ divides $p(t+a)$, then $t+i = t+a$, implying $i = a$. Similarly, if $p(t+i)$ divides $p(t+b)$, then $t+i = t+b$, implying $i = b$.
    have h_inj : ∀ i j, p (t + i) = p (t + j) → i = j := by
      exact fun i j hij => by simpa using StrictMono.injective ( show StrictMono ( fun x => p ( t + x ) ) from fun i j hij => by simpa using p_strictMono_new ( by linarith ) ( by linarith ) ) hij;
    exact Or.imp ( fun h => h_inj _ _ <| Nat.prime_dvd_prime_iff_eq ( by exact Nat.prime_nth_prime _ ) ( by exact Nat.prime_nth_prime _ ) |>.1 h ) ( fun h => h_inj _ _ <| Nat.prime_dvd_prime_iff_eq ( by exact Nat.prime_nth_prime _ ) ( by exact Nat.prime_nth_prime _ ) |>.1 h ) h_div;
  unfold prime_indices;
  rw [ Set.ext_iff ] at h_set_eq;
  rw [ Finset.card_eq_two ];
  exact ⟨ a, b, ne_of_lt hb, by ext i; aesop <;> linarith ⟩

lemma prime_indices_disjoint (t x y : ℕ) (hx : x ∈ C t) (hy : y ∈ C t) (h : Nat.Coprime x y) : Disjoint (prime_indices t x) (prime_indices t y) := by
  -- If $p(t+i)$ divides both $x$ and $y$, then it divides their gcd, which is 1. But since $p(t+i)$ is a prime, it can't divide 1. Hence, $i$ can't be in both prime_indices $t$ $x$ and prime_indices $t$ $y$.
  have h_not_div : ∀ i, p (t + i) ∣ x → p (t + i) ∣ y → False := by
    exact fun i hi hy => absurd ( Nat.dvd_gcd hi hy ) ( by rw [ h.gcd_eq_one ] ; exact Nat.Prime.not_dvd_one ( Nat.prime_nth_prime _ ) );
  exact Finset.disjoint_left.mpr fun i hi₁ hi₂ => h_not_div i ( Finset.mem_filter.mp hi₁ |>.2 ) ( Finset.mem_filter.mp hi₂ |>.2 )


lemma max_C_bound (t : ℕ) (ht : t ≥ 1) : has_no_k_plus_1_coprime (C t) 4 := by
  exact max_C t


lemma card_union_indices (t : ℕ) (ht : t ≥ 1) (S : Finset ℕ) (hS : S ⊆ C t) (h_coprime : (S : Set ℕ).Pairwise Nat.Coprime) :
  (Finset.biUnion S (prime_indices t)).card = 2 * S.card := by
    -- Since each element in S has exactly two prime indices, and the prime indices sets are pairwise disjoint, the cardinality of the union is the sum of the cardinalities of each prime indices set.
    have h_card_union : (S.biUnion (prime_indices t)).card = ∑ x ∈ S, (prime_indices t x).card := by
      rw [ Finset.card_biUnion ];
      exact fun x hx y hy hxy => prime_indices_disjoint t x y ( hS hx ) ( hS hy ) ( h_coprime hx hy hxy );
    rw [ h_card_union, Finset.sum_congr rfl fun x hx => prime_indices_card t x ( hS hx ) ht ] ; simp +decide [ mul_comm ]

lemma card_union_le_nine (t : ℕ) (S : Finset ℕ) (hS : S ⊆ C t) :
  (Finset.biUnion S (prime_indices t)).card ≤ 9 := by
    exact le_trans ( Finset.card_le_card ( Finset.biUnion_subset.mpr fun x hx => Finset.filter_subset _ _ ) ) ( by norm_num )

lemma max_C_bound_final (t : ℕ) (ht : t ≥ 1) : has_no_k_plus_1_coprime (C t) 4 := by
  exact max_C_bound t ht


lemma max_C_proven (t : ℕ) (ht : t ≥ 1) : has_no_k_plus_1_coprime (C t) 4 := by
  intro S hS h_coprime
  have h1 := card_union_indices t ht S hS h_coprime
  have h2 := card_union_le_nine t S hS
  rw [h1] at h2
  linarith

lemma card_split (A B S : Finset ℕ) (h_disjoint : Disjoint A B) (h_subset : S ⊆ A ∪ B) :
  S.card = (S ∩ A).card + (S ∩ B).card := by
    -- We can use the fact that for any finite sets $X$ and $Y$, if $X$ and $Y$ are disjoint then $|X \cup Y| = |X| + |Y|$.
    have h_card_union : (S ∩ A ∪ S ∩ B).card = (S ∩ A).card + (S ∩ B).card := by
      exact Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx hx' => Finset.disjoint_left.mp h_disjoint ( Finset.mem_of_mem_inter_right hx ) ( Finset.mem_of_mem_inter_right hx' ) ) |> Eq.trans <| by aesop;
    convert h_card_union using 2 ; ext ; aesop;
    -- Since $S \subseteq A \cup B$, if $a \in S$, then $a \in A \cup B$.
    apply Finset.mem_union.mp; exact h_subset a_1


lemma A_no_k_plus_1 (t n : ℕ) (h_H : satisfies_H t) : has_no_k_plus_1_coprime (A t n) (t + 3) := by
  -- Let S be a pairwise coprime subset of A(t, n). Then S can be split into S ∩ B(t, n) and S ∩ C(t).
  intro S hS
  have h_split : S.card = (S ∩ B t n).card + (S ∩ C t).card := by
    -- Since $B t n$ and $C t$ are disjoint, the intersection of $S$ with $B t n$ and $S$ with $C t$ are also disjoint.
    have h_disjoint : Disjoint (S ∩ B t n) (S ∩ C t) := by
      exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp ( B_disjoint_C t n ) ( Finset.mem_inter.mp hx₁ |>.2 ) ( Finset.mem_inter.mp hx₂ |>.2 );
    rw [ ← Finset.card_union_of_disjoint h_disjoint, ← Finset.inter_union_distrib_left ];
    rw [ Finset.inter_eq_left.mpr ] ; aesop;
  -- Since $S$ is pairwise coprime, both $S \cap B(t, n)$ and $S \cap C(t)$ must also be pairwise coprime.
  intro h_pairwise_coprime
  have h_B : (S ∩ B t n).card ≤ t - 1 := by
    have := max_B t n;
    exact this _ ( Finset.inter_subset_right ) ( fun x hx y hy hxy => h_pairwise_coprime ( Finset.mem_of_mem_inter_left hx ) ( Finset.mem_of_mem_inter_left hy ) hxy ) |> le_trans ( by aesop )
  have h_C : (S ∩ C t).card ≤ 4 := by
    have := max_C_proven t ( t_ge_one_of_satisfies_H_new t h_H );
    exact this _ ( Finset.inter_subset_right ) ( fun x hx y hy hxy => h_pairwise_coprime ( Finset.mem_of_mem_inter_left hx ) ( Finset.mem_of_mem_inter_left hy ) hxy );
  linarith [ Nat.sub_add_cancel ( show 1 ≤ t from t_ge_one_of_satisfies_H t h_H ) ]


lemma C_map_injective_final (t : ℕ) (ht : t ≥ 1) :
  ∀ i j k l, 0 ≤ i ∧ i < j ∧ j ≤ 8 → 0 ≤ k ∧ k < l ∧ l ≤ 8 →
  p (t + i) * p (t + j) = p (t + k) * p (t + l) → i = k ∧ j = l := by
    exact fun i j k l a a_1 a_2 ↦ C_map_injective t ht i j k l a a_1 a_2

lemma card_C_eq_36 (t : ℕ) (ht : t ≥ 1) : (C t).card = 36 := by
  -- Since $C t$ is the image of the set of pairs $(i, j)$ with $0 \leq i < j \leq 8$ under the injective map $(i, j) \mapsto p (t + i) * p (t + j)$, it must have the same cardinality as the domain.
  have h_card_eq : (Finset.image (fun x => p (t + x.1) * p (t + x.2)) (Finset.filter (fun x => x.1 < x.2) (Finset.product (Finset.range 9) (Finset.range 9)))).card = 36 := by
    rw [ Finset.card_image_of_injOn ];
    · decide;
    · intros x hx y hy hxy;
      have := C_map_injective_new t ht x.1 x.2 y.1 y.2 ; aesop;
      · exact this ( by linarith ) ( by linarith ) |>.1;
      · exact this ( by linarith ) ( by linarith ) |>.2;
  -- Since the function is injective, the cardinality of the image is equal to the cardinality of the domain.
  have h_card_eq : (Finset.image (fun x => p (t + x.1) * p (t + x.2)) (Finset.filter (fun x => x.1 < x.2) (Finset.product (Finset.range 9) (Finset.range 9)))).card = (C t).card := by
    -- Since the function is injective, the cardinality of the image is equal to the cardinality of the domain. Therefore, we can conclude that the cardinality of the image is 36.
    apply congr_arg Finset.card;
    ext; simp [C];
    exact ⟨ fun ⟨ a, b, h, h' ⟩ => ⟨ ⟨ a, b, ⟨ h.1, h' ⟩ ⟩, ⟨ a, b, h.2, by linarith, h'.symm ⟩ ⟩, fun ⟨ ⟨ a, b, ⟨ h₁, h₂ ⟩ ⟩, ⟨ i, j, h₃, h₄, h₅ ⟩ ⟩ => ⟨ i, j, ⟨ ⟨ by linarith, by linarith ⟩, h₃ ⟩, h₅.symm ⟩ ⟩;
  grind

lemma has_no_k_plus_1_coprime_union (B C : Finset ℕ) (k_B k_C : ℕ)
  (h_disjoint : Disjoint B C)
  (h_B : has_no_k_plus_1_coprime B k_B)
  (h_C : has_no_k_plus_1_coprime C k_C) :
  has_no_k_plus_1_coprime (B ∪ C) (k_B + k_C) := by
    intro S hS h_coprime;
    -- By card_split, we have |S| = |S ∩ B| + |S ∩ C|.
    have h_card_split : S.card = (S ∩ B).card + (S ∩ C).card := by
      rw [ ← Finset.card_union_of_disjoint ];
      · rw [ ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS ];
      · simp_all +decide [ Finset.disjoint_left ];
    refine' h_card_split ▸ add_le_add ( h_B _ _ _ ) ( h_C _ _ _ );
    · exact Finset.inter_subset_right;
    · exact fun x hx y hy hxy => h_coprime ( Finset.mem_of_mem_inter_left hx ) ( Finset.mem_of_mem_inter_left hy ) hxy;
    · exact Finset.inter_subset_right;
    · exact fun x hx y hy hxy => h_coprime ( by aesop ) ( by aesop ) hxy

lemma A_no_k_plus_1_final (t n : ℕ) (h_H : satisfies_H t) (h_disjoint : Disjoint (B t n) (C t)) :
  has_no_k_plus_1_coprime (A t n) (t + 3) := by
    exact A_no_k_plus_1 t n h_H

def D_primes (t : ℕ) : Finset ℕ := (Finset.range 4).image (fun i => p (t + i))
def D_squares (t : ℕ) : Finset ℕ := (Finset.range 4).image (fun i => p (t + i) ^ 2)
def D_products (t : ℕ) : Finset ℕ :=
  ((Finset.range 4).product (Finset.range 9)).image (fun x => p (t + x.1) * p (t + x.2))
  |>.filter (fun m => ∃ i j, 0 ≤ i ∧ i ≤ 3 ∧ 1 ≤ j ∧ j ≤ 8 ∧ i < j ∧ m = p (t + i) * p (t + j))

def D_union (t : ℕ) : Finset ℕ := D_primes t ∪ D_squares t ∪ D_products t

lemma D_union_subset_D (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) :
  D_union t ⊆ D t n := by
    intro x hx;
    unfold D at *; aesop;
    · -- By definition of $D_union$, we know that $x$ is either in $D_primes$, $D_squares$, or $D_products$.
      cases' Finset.mem_union.mp hx with hx_prime hx_square hx_product;
      · unfold D_primes D_squares at hx_prime; aesop;
        · unfold E; aesop;
          · exact Nat.Prime.pos ( by unfold p; exact Nat.prime_nth_prime _ );
          · -- Since $p(t+w)$ is a prime number and $p(t+7) * p(t+8) \leq n$, it follows that $p(t+w) \leq p(t+8)$.
            have h_prime_le : p (t + w) ≤ p (t + 8) := by
              -- Since $p$ is strictly increasing, we have $p(t + w) \leq p(t + 8)$ for $w < 4$.
              have h_prime_le : StrictMono (fun i => p (t + i)) := by
                exact fun i j hij => p_strictMono_new ( by linarith [ t_ge_one_of_satisfies_H t h_H ] ) ( by linarith );
              exact h_prime_le.monotone ( by linarith );
            -- Since $p(t+7) * p(t+8) \leq n$, we have $p(t+8) \leq n$.
            have h_prime_le_n : p (t + 8) ≤ n := by
              have h_prime_le_n : p (t + 8) ≤ p (t + 7) * p (t + 8) := by
                exact le_mul_of_one_le_left ( Nat.zero_le _ ) ( Nat.Prime.pos ( by unfold p; exact Nat.prime_nth_prime _ ) );
              exact le_trans h_prime_le_n h_n;
            linarith;
          · -- Since $p(t+w)$ is a prime number greater than $t$, it must divide $P(t+3)$.
            have h_div : p (t + w) ∣ P (t + 3) := by
              have h_div : p (t + w) ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t + 3)) := by
                unfold p; aesop;
                exact ⟨ t + w - 1, by omega, rfl ⟩;
              unfold P; aesop;
              exact right ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr left_1 );
            rw [ Nat.gcd_eq_left h_div ] ; exact Nat.Prime.one_lt ( by unfold p; exact Nat.prime_nth_prime _ );
        · -- Since $p(t + w)$ is a prime number, $p(t + w)^2$ is greater than 1 and less than or equal to $n$.
          have h_bounds : 1 ≤ p (t + w) ^ 2 ∧ p (t + w) ^ 2 ≤ n := by
            have h_bounds : p (t + w) ^ 2 ≤ p (t + 3) * p (t + 8) := by
              have h_bounds : p (t + w) ≤ p (t + 3) := by
                interval_cases w <;> norm_num [ p ];
                · rw [ Nat.nth_le_nth _ ];
                  · omega;
                  · exact Nat.infinite_setOf_prime;
                · rw [ Nat.nth_le_nth _ ];
                  · linarith;
                  · exact Nat.infinite_setOf_prime;
                · rw [ Nat.nth_le_nth _ ];
                  · linarith;
                  · exact Nat.infinite_setOf_prime;
              nlinarith [ show p ( t + 8 ) ≥ p ( t + 3 ) from Nat.le_of_lt ( p_strictMono_new ( by linarith [ t_ge_one_of_satisfies_H t h_H ] ) ( by linarith ) ) ];
            unfold interval_start at h_n;
            unfold p at * ; aesop;
            · exact Nat.one_le_pow _ _ ( Nat.Prime.pos ( by aesop ) );
            · refine le_trans h_bounds ?_;
              exact le_trans ( Nat.mul_le_mul ( Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by linarith ) ) le_rfl ) h_n;
          unfold E; aesop;
          -- Since $p(t + w)$ is a prime number, $p(t + w)$ divides $P(t + 3)$.
          have h_div : p (t + w) ∣ P (t + 3) := by
            have h_div : p (t + w) ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t + 3)) := by
              interval_cases w <;> norm_num [ Finset.mem_image, Finset.mem_range ];
              · exact ⟨ t - 1, by omega, rfl ⟩;
              · unfold p; aesop;
              · exact ⟨ t + 2 - 1, by omega, by rfl ⟩;
              · unfold p; aesop;
            unfold P; aesop;
            exact right_1 ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr left_2 );
          exact lt_of_lt_of_le ( by nlinarith only [ show p ( t + w ) > 1 from Nat.Prime.one_lt ( by unfold p; exact Nat.prime_nth_prime _ ) ] ) ( Nat.le_of_dvd ( Nat.gcd_pos_of_pos_left _ ( by positivity ) ) ( Nat.dvd_gcd ( dvd_pow_self _ two_ne_zero ) h_div ) );
      · unfold D_products at hx_square; aesop;
        unfold E; aesop;
        · exact Nat.mul_pos ( Nat.Prime.pos ( by unfold p; aesop ) ) ( Nat.Prime.pos ( by unfold p; aesop ) );
        · -- Since $p(t + w_1) * p(t + w_3)$ is a product of two primes in the range $[t, t+8]$, and $interval_start t = p(t+7) * p(t+8)$, we have $p(t + w_1) * p(t + w_3) \leq p(t+7) * p(t+8)$.
          have h_prod_le_interval_start : p (t + w_1) * p (t + w_3) ≤ p (t + 7) * p (t + 8) := by
            gcongr;
            · apply_rules [ Nat.nth_monotone ];
              · exact Nat.infinite_setOf_prime;
              · omega;
            · apply_rules [ Nat.nth_monotone ];
              · exact Nat.infinite_setOf_prime;
              · omega;
          exact le_trans h_prod_le_interval_start h_n;
        · refine' lt_of_lt_of_le _ ( Nat.le_of_dvd _ ( Nat.dvd_gcd ( dvd_mul_right _ _ ) ( Finset.dvd_prod_of_mem _ _ ) ) );
          · exact Nat.Prime.one_lt ( Nat.prime_nth_prime _ );
          · exact Nat.gcd_pos_of_pos_right _ ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by aesop ) );
          · exact Finset.mem_range.mpr ( by omega );
    · -- Since $x \in D_union t$, we know that $x$ is coprime with $P(t-1)$.
      have h_coprime : Nat.gcd x (P (t - 1)) = 1 := by
        have h_coprime : ∀ i ∈ Finset.range (t - 1), Nat.gcd x (Nat.nth Nat.Prime i) = 1 := by
          unfold D_union at hx; aesop;
          · unfold D_primes at h; aesop;
            rw [ Nat.gcd_comm ];
            have h_coprime : Nat.nth Nat.Prime i ≠ p (t + w) := by
              refine' ne_of_lt ( Nat.nth_strictMono _ _ );
              · exact Nat.infinite_setOf_prime;
              · omega;
            exact Nat.coprime_iff_gcd_eq_one.mpr ( by have := Nat.coprime_primes ( Nat.prime_nth_prime i ) ( show Nat.Prime ( p ( t + w ) ) from Nat.prime_nth_prime _ ) ; aesop );
          · unfold D_squares at h; aesop;
            rw [ Nat.coprime_primes ] <;> norm_num;
            · refine' ne_of_gt _;
              refine' Nat.nth_strictMono _ _;
              · exact Nat.infinite_setOf_prime;
              · omega;
            · exact Nat.prime_nth_prime _;
          · unfold D_products at h_2; aesop;
            -- Since $p(t+w_1)$ and $p(t+w_3)$ are primes greater than $i$, they are coprime with $Nat.nth Nat.Prime i$.
            have h_coprime : Nat.gcd (p (t + w_1)) (Nat.nth Nat.Prime i) = 1 ∧ Nat.gcd (p (t + w_3)) (Nat.nth Nat.Prime i) = 1 := by
              have h_coprime : p (t + w_1) > Nat.nth Nat.Prime i ∧ p (t + w_3) > Nat.nth Nat.Prime i := by
                have h_coprime : ∀ j > i, Nat.nth Nat.Prime j > Nat.nth Nat.Prime i := by
                  intro j hj; rw [ gt_iff_lt ] ; rw [ Nat.nth_lt_nth ] ; aesop;
                  exact Nat.infinite_setOf_prime;
                exact ⟨ h_coprime _ ( by omega ), h_coprime _ ( by omega ) ⟩;
              exact ⟨ Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( show Nat.Prime ( p ( t + w_1 ) ) from Nat.prime_nth_prime _ ) ( show Nat.Prime ( Nat.nth Nat.Prime i ) from Nat.prime_nth_prime _ ) ; aesop, Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( show Nat.Prime ( p ( t + w_3 ) ) from Nat.prime_nth_prime _ ) ( show Nat.Prime ( Nat.nth Nat.Prime i ) from Nat.prime_nth_prime _ ) ; aesop ⟩;
            exact Nat.Coprime.mul h_coprime.1 h_coprime.2;
        exact Nat.Coprime.prod_right h_coprime;
      unfold B at a; aesop;


lemma D_primes_subset (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) :
  D_primes t ⊆ D t n := by
    -- Each element of D_primes t is in E(n, t+3) and not in B t n, hence in D t n.
    intros x hx
    obtain ⟨i, hi⟩ : ∃ i ∈ Finset.range 4, x = p (t + i) := by
      -- By definition of $D_primes$, if $x \in D_primes t$, then there exists $i \in \{0, 1, 2, 3\}$ such that $x = p (t + i)$.
      simp [D_primes] at hx;
      aesop;
    -- Since $x \in D_primes t$, we have $x \in D_union t$.
    have hx_D_union : x ∈ D_union t := by
      unfold D_union; aesop;
    exact D_union_subset_D t n h_H h_n hx_D_union

lemma D_squares_subset (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) :
  D_squares t ⊆ D t n := by
    intro x hx; unfold D_squares at hx; aesop;
    -- Since $p(t + w)$ is a prime number, $p(t + w)^2$ is divisible by $p(t + w)$, which is one of the primes in $P(t+3)$. Therefore, $p(t + w)^2$ is in $E(n, t+3)$.
    have h_in_E : p (t + w) ^ 2 ∈ E n (t + 3) := by
      -- Since $p(t+w)$ is a prime number, $p(t+w)^2$ is in the interval $[1, n]$ and not coprime with $P(t+3)$.
      have h_interval : p (t + w) ^ 2 ≤ n := by
        -- Since $p(t+w)$ is a prime number, $p(t+w)^2$ is in the interval $[1, n]$ and not coprime with $P(t+3)$, thus $p(t+w)^2 \leq n$.
        have h_interval : p (t + w) ^ 2 ≤ p (t + 3) ^ 2 := by
          -- Since $p$ is the nth prime and primes are strictly increasing, if $w < 4$, then $t + w \leq t + 3$.
          have h_prime_le : p (t + w) ≤ p (t + 3) := by
            apply_rules [ monotone_nat_of_le_succ, Nat.le_of_lt_succ ];
            · unfold p;
              intro n; cases n <;> norm_num [ Nat.nth_zero ] ; exact Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by linarith ) ;
            · grind;
          exact Nat.pow_le_pow_left h_prime_le 2;
        have h_interval : p (t + 3) ^ 2 < p (t + 7) * p (t + 8) := by
          have h_interval : p (t + 3) < p (t + 7) ∧ p (t + 3) < p (t + 8) := by
            exact ⟨ p_strictMono_new ( by linarith [ t_ge_one_of_satisfies_H t h_H ] ) ( by linarith ), p_strictMono_new ( by linarith [ t_ge_one_of_satisfies_H t h_H ] ) ( by linarith ) ⟩;
          nlinarith only [ h_interval ];
        exact le_trans ‹_› ( le_trans h_interval.le h_n );
      unfold E; aesop;
      · exact Nat.one_le_pow _ _ ( Nat.Prime.pos ( by unfold p; exact Nat.prime_nth_prime _ ) );
      · -- Since $p(t+w)$ is a prime number, it divides $P(t+3)$.
        have h_div : p (t + w) ∣ P (t + 3) := by
          have h_div : p (t + w) ∣ ∏ i ∈ Finset.range (t + 3), Nat.nth Nat.Prime i := by
            have h_prime : p (t + w) ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t + 3)) := by
              unfold p; aesop;
              exact ⟨ t + w - 1, by omega, rfl ⟩
            rw [ Finset.mem_image ] at h_prime; obtain ⟨ i, hi, hi' ⟩ := h_prime; exact hi'.symm ▸ Finset.dvd_prod_of_mem _ hi;
          exact h_div;
        exact lt_of_lt_of_le ( Nat.Prime.one_lt ( by unfold p; exact Nat.prime_nth_prime _ ) ) ( Nat.le_of_dvd ( Nat.gcd_pos_of_pos_left _ ( pow_pos ( Nat.Prime.pos ( by unfold p; exact Nat.prime_nth_prime _ ) ) _ ) ) ( Nat.dvd_gcd ( dvd_pow_self _ two_ne_zero ) h_div ) );
    unfold D; aesop;
    unfold B at a; unfold E at h_in_E; aesop;
    -- Since $p(t + w)$ is a prime number, $p(t + w)^2$ is coprime to $P(t-1)$.
    have h_coprime : Nat.gcd (p (t + w)) (P (t - 1)) = 1 := by
      -- Since $p(t + w)$ is a prime number and $P(t - 1)$ is the product of the first $t - 1$ primes, $p(t + w)$ cannot divide any of the primes in $P(t - 1)$.
      have h_not_div : ∀ i < t - 1, ¬(p (t + w) ∣ Nat.nth Nat.Prime i) := by
        -- Since $p(t + w)$ is a prime number and $i < t - 1$, $p(t + w)$ cannot divide any prime number less than or equal to $p(t - 1)$.
        intros i hi
        have h_prime_gt : p (t + w) > Nat.nth Nat.Prime i := by
          refine' Nat.nth_strictMono _ _;
          · exact Nat.infinite_setOf_prime;
          · omega;
        exact Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos ( by aesop ) ) h_prime_gt;
      refine' Nat.Coprime.prod_right fun i hi => _;
      exact Nat.Prime.coprime_iff_not_dvd ( show Nat.Prime ( p ( t + w ) ) from Nat.prime_nth_prime _ ) |>.2 ( h_not_div i ( Finset.mem_range.mp hi ) );
    simp_all +decide [ Nat.Coprime, Nat.Coprime.pow_left ]

lemma D_products_subset (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) :
  D_products t ⊆ D t n := by
    -- To show that D_products t is a subset of D t n, we need to verify that each element of D_products t is in E(n, t+3) and not in B(t, n).
    intro x hx
    obtain ⟨i, j, hi, hj, h_prod⟩ : ∃ i j, 0 ≤ i ∧ i ≤ 3 ∧ 1 ≤ j ∧ j ≤ 8 ∧ i < j ∧ x = p (t + i) * p (t + j) := by
      unfold D_products at hx; aesop;
    refine' Finset.mem_sdiff.mpr ⟨ _, _ ⟩;
    · -- Since $p(t+i)$ is a prime factor of $P(t+3)$ and $x = p(t+i) * p(t+j)$, it follows that $x$ is not coprime with $P(t+3)$.
      have h_not_coprime : ¬Nat.Coprime x (P (t + 3)) := by
        -- Since $p(t+i)$ is a prime factor of $P(t+3)$ and $x = p(t+i) * p(t+j)$, it follows that $p(t+i)$ divides $x$ and $P(t+3)$.
        have h_div : p (t + i) ∣ x ∧ p (t + i) ∣ P (t + 3) := by
          aesop;
          -- Since $p(t+i)$ is a prime factor of $P(t+3)$, it must divide $P(t+3)$.
          have h_factor : p (t + i) ∈ Finset.image (fun k => Nat.nth Nat.Prime k) (Finset.range (t + 3)) := by
            unfold p; aesop;
            exact ⟨ t + i - 1, by omega, rfl ⟩;
          unfold P; aesop;
          exact right ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr left_3 );
        exact fun h => Nat.Prime.not_dvd_one ( show Nat.Prime ( p ( t + i ) ) from Nat.prime_nth_prime _ ) ( h.gcd_eq_one ▸ Nat.dvd_gcd h_div.1 h_div.2 );
      unfold E; aesop;
      · exact Nat.mul_pos ( Nat.Prime.pos ( by unfold p; aesop ) ) ( Nat.Prime.pos ( by unfold p; aesop ) );
      · -- Since $p(t+i)$ and $p(t+j)$ are primes greater than or equal to $p(t)$, we have $p(t+i) \leq p(t+3)$ and $p(t+j) \leq p(t+8)$.
        have h_pi_le_pt3 : p (t + i) ≤ p (t + 3) := by
          apply_rules [ Nat.nth_monotone ];
          · exact Nat.infinite_setOf_prime;
          · omega
        have h_pj_le_pt8 : p (t + j) ≤ p (t + 8) := by
          unfold p; interval_cases j <;> norm_num;
          all_goals exact Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by linarith ) ;
        -- Since $p(t+3) < p(t+7)$ and $p(t+8) < p(t+8)$, we have $p(t+3) * p(t+8) < p(t+7) * p(t+8)$.
        have h_prod_lt_interval : p (t + 3) * p (t + 8) < p (t + 7) * p (t + 8) := by
          -- Since $p(t+3)$ and $p(t+7)$ are primes, and primes are strictly increasing, we have $p(t+3) < p(t+7)$.
          have h_prime_lt : Nat.nth Nat.Prime (t + 2) < Nat.nth Nat.Prime (t + 6) := by
            rw [ Nat.nth_lt_nth ] <;> norm_num;
            -- The set of primes is infinite, so we can conclude that the set of primes is infinite.
            apply Nat.infinite_setOf_prime;
          exact Nat.mul_lt_mul_of_pos_right h_prime_lt ( Nat.Prime.pos ( Nat.prime_nth_prime _ ) )
        exact le_trans ( Nat.mul_le_mul h_pi_le_pt3 h_pj_le_pt8 ) ( le_trans h_prod_lt_interval.le h_n );
      · -- Since the gcd is not 1, it must be greater than 1.
        apply Nat.lt_of_le_of_ne; exact Nat.gcd_pos_of_pos_right _ (by
        exact Finset.prod_pos fun i hi => Nat.Prime.pos <| by aesop); exact Ne.symm h_not_coprime;
    · unfold B; aesop;
      -- Since $p(t+i)$ and $p(t+j)$ are primes greater than $p(t-1)$, they are coprime with $P(t-1)$.
      have h_coprime : Nat.gcd (p (t + i)) (P (t - 1)) = 1 ∧ Nat.gcd (p (t + j)) (P (t - 1)) = 1 := by
        have h_coprime : ∀ k, k ≥ t → Nat.gcd (p k) (P (t - 1)) = 1 := by
          unfold P p; aesop;
          refine' Nat.Coprime.prod_right fun i hi => _;
          rw [ Nat.coprime_primes ] <;> aesop;
          exact absurd a_3 ( ne_of_gt ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( by omega ) ) );
        exact ⟨ h_coprime _ ( by linarith ), h_coprime _ ( by linarith ) ⟩;
      exact Nat.le_of_eq ( Nat.Coprime.mul h_coprime.1 h_coprime.2 )

lemma D_union_subset (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) :
  D_union t ⊆ D t n := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · rcases Finset.mem_union.mp h with h_prime | h_square
    · exact D_primes_subset t n h_H h_n h_prime
    · exact D_squares_subset t n h_H h_n h_square
  · exact D_products_subset t n h_H h_n h


lemma p_lt_interval_start (t : ℕ) (ht : t ≥ 1) : p (t + 3) < interval_start t := by
  -- Since $p$ is strictly increasing for indices $\geq 1$, we have $p(t+3) < p(t+7)$ and $p(t+3) < p(t+8)$.
  have h_p_lt : p (t + 3) < p (t + 7) ∧ p (t + 3) < p (t + 8) := by
    exact ⟨ p_strictMono_new ( by linarith ) ( by linarith ), p_strictMono_new ( by linarith ) ( by linarith ) ⟩;
  -- Since $p(t+7)$ and $p(t+8)$ are primes, their product $p(t+7) * p(t+8)$ is greater than either of them.
  have h_prod_gt : p (t + 7) * p (t + 8) > p (t + 7) ∧ p (t + 7) * p (t + 8) > p (t + 8) := by
    exact ⟨ lt_mul_of_one_lt_right ( Nat.Prime.pos ( by exact Nat.prime_nth_prime _ ) ) ( Nat.Prime.one_lt ( by exact Nat.prime_nth_prime _ ) ), lt_mul_of_one_lt_left ( Nat.Prime.pos ( by exact Nat.prime_nth_prime _ ) ) ( Nat.Prime.one_lt ( by exact Nat.prime_nth_prime _ ) ) ⟩;
  -- Since $p(t+3) < p(t+7)$ and $p(t+3) < p(t+8)$, and $p(t+7) * p(t+8) > p(t+7)$ and $p(t+7) * p(t+8) > p(t+8)$, it follows that $p(t+3) < p(t+7) * p(t+8)$.
  apply lt_of_lt_of_le h_p_lt.left (Nat.le_of_lt h_prod_gt.left)


lemma D_prime_factors_ge_pt (t n : ℕ) (u : ℕ) (hu : u ∈ D t n) :
  ∀ q, Nat.Prime q → q ∣ u → q ≥ p t := by
    -- Since $u \in D t n$, we have $u \notin B t n$, which means $\gcd(u, P(t-1)) = 1$.
    have h_gcd : Nat.gcd u (P (t - 1)) = 1 := by
      unfold D at hu; aesop;
      unfold B at right; aesop;
      unfold E at left; aesop;
      exact le_antisymm right ( Nat.gcd_pos_of_pos_left _ left );
    -- Since $P(t-1)$ is the product of the first $t-1$ primes, if $q$ divides $u$ and $\gcd(u, P(t-1)) = 1$, then $q$ cannot be any of the first $t-1$ primes.
    have h_not_first_t_minus_1_primes : ∀ q, Nat.Prime q → q ∣ u → ¬(q ∈ Finset.image (Nat.nth Nat.Prime) (Finset.range (t - 1))) := by
      -- If $q$ is in the image of the first $t-1$ primes, then $q$ divides $P(t-1)$.
      intros q hq_prime hq_div_u hq_image
      have hq_div_P : q ∣ P (t - 1) := by
        aesop;
        exact Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr left );
      exact hq_prime.not_dvd_one <| h_gcd ▸ Nat.dvd_gcd hq_div_u hq_div_P;
    -- Since $q$ is not in the first $t-1$ primes, it must be one of the primes starting from $p_t$ onwards.
    have h_q_ge_pt : ∀ q, Nat.Prime q → q ∣ u → ∃ i ≥ t - 1, q = Nat.nth Nat.Prime i := by
      intros q hq_prime hq_div
      obtain ⟨i, hi⟩ : ∃ i, q = Nat.nth Nat.Prime i := by
        use Nat.count (Nat.Prime) q;
        -- By definition of Nat.nth, we know that q is the (Nat.count Nat.Prime q)-th prime.
        apply Eq.symm; exact Nat.nth_count hq_prime
      exact ⟨ i, not_lt.mp fun contra => h_not_first_t_minus_1_primes q hq_prime hq_div <| hi ▸ Finset.mem_image.mpr ⟨ i, Finset.mem_range.mpr contra, rfl ⟩, hi ⟩;
    intro q hq hq'; cases t <;> aesop;
    · unfold p; aesop;
      exact hq.two_le;
    · obtain ⟨ i, hi, rfl ⟩ := h_q_ge_pt q hq hq'; have := Nat.nth_monotone ( Nat.infinite_setOf_prime ) hi; aesop;


lemma D_prime_factors_ge_pt_new (t n : ℕ) (u : ℕ) (hu : u ∈ D t n) :
  ∀ q, Nat.Prime q → q ∣ u → q ≥ p t := by
    exact fun q a a_1 ↦ D_prime_factors_ge_pt t n u hu q a a_1


lemma prime_dvd_P_of_lt_pt (t : ℕ) (q : ℕ) (hq : Nat.Prime q) (h_lt : q < p t) :
  q ∣ P (t - 1) := by
    -- Since $q$ is a prime less than $p(t)$, it must be one of the primes in the set $\{p(1), p(2), \ldots, p(t-1)\}$.
    have h_prime_in_set : q ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t - 1)) := by
      -- Since $q$ is a prime less than $p(t)$, and $p(t)$ is the $t$-th prime, $q$ must be one of the first $t-1$ primes.
      have h_prime_in_range : ∃ i ∈ Finset.range (t - 1), Nat.nth Nat.Prime i = q := by
        have h_prime_lt_pt : q < Nat.nth Nat.Prime (t - 1) := by
          convert h_lt using 1
        -- Since $q$ is a prime less than the $(t-1)$th prime, and the primes are ordered, $q$ must be one of the primes in the first $t-1$ primes.
        have h_prime_in_range : ∃ i, Nat.nth Nat.Prime i = q := by
          -- Since $q$ is a prime number, and the nth prime function is surjective onto the set of primes, there must exist some $i$ such that $Nat.nth Nat.Prime i = q$.
          use Nat.count (Nat.Prime) q;
          exact Nat.nth_count hq;
        aesop;
          exact ⟨ w, Nat.lt_of_not_ge fun h => (not_le_of_gt h_prime_lt_pt) <| Nat.nth_monotone ( Nat.infinite_setOf_prime ) h, rfl ⟩;
      aesop;
    rw [ Finset.mem_image ] at h_prime_in_set; obtain ⟨ i, hi, rfl ⟩ := h_prime_in_set; exact Finset.dvd_prod_of_mem _ hi;

lemma D_prime_factors_ge_pt_final (t n : ℕ) (u : ℕ) (hu : u ∈ D t n) :
  ∀ q, Nat.Prime q → q ∣ u → q ≥ p t := by
    exact fun q a a_1 ↦ D_prime_factors_ge_pt_new t n u hu q a a_1


lemma D_has_small_prime_factor (t n : ℕ) (u : ℕ) (hu : u ∈ D t n) :
  ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ≤ p (t + 3) := by
    -- Since $u \in E(n, t+3)$, there exists a prime $q$ such that $q \mid u$ and $q \mid P(t+3)$.
    obtain ⟨q, hq_prime, hq_div_u, hq_div_P⟩ : ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ∣ P (t + 3) := by
      have h_prime_factor : Nat.gcd u (P (t + 3)) > 1 := by
        unfold D at hu; aesop;
        -- By definition of $E(n, k)$, if $u \in E(n, t+3)$, then $\gcd(u, P(t+3)) > 1$.
        apply Finset.mem_filter.mp left |>.2;
      exact Nat.Prime.not_coprime_iff_dvd.mp h_prime_factor.ne';
    -- Since $q$ divides $P(t+3)$, it must be one of the primes in the product $P(t+3)$.
    have hq_prime_divisors : q ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t + 3)) := by
      have hq_prime_divisors : q ∣ ∏ i ∈ Finset.range (t + 3), Nat.nth Nat.Prime i := by
        exact hq_div_P;
      simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ];
      -- Since $q$ is prime and not coprime with $Nat.nth Nat.Prime x$, it must be that $q = Nat.nth Nat.Prime x$.
      obtain ⟨x, hx₁, hx₂⟩ := hq_prime_divisors
      have hx₃ : q = Nat.nth Nat.Prime x := by
        have := Nat.coprime_primes hq_prime ( Nat.prime_nth_prime x ) ; aesop;
      aesop;
    unfold p; aesop;
    exact ⟨ _, Nat.prime_nth_prime _, hq_div_u, Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by linarith ) ⟩


lemma has_no_k_plus_1_coprime_union_v2 (B C : Finset ℕ) (k_B k_C : ℕ)
  (h_disjoint : Disjoint B C)
  (h_B : has_no_k_plus_1_coprime B k_B)
  (h_C : has_no_k_plus_1_coprime C k_C) :
  has_no_k_plus_1_coprime (B ∪ C) (k_B + k_C) := by
  intro S hS h_coprime
  rw [card_split B C S h_disjoint hS]
  apply add_le_add
  · apply h_B
    · exact Finset.inter_subset_right
    · exact h_coprime.mono (Finset.inter_subset_left)
  · apply h_C
    · exact Finset.inter_subset_right
    · exact h_coprime.mono (Finset.inter_subset_left)

lemma D_prime_factors_ge_pt_v7 (t n : ℕ) (u : ℕ) (hu : u ∈ D t n) :
  ∀ q, Nat.Prime q → q ∣ u → q ≥ p t := by
  intro q hq hqu
  by_contra h_lt
  push Not at h_lt
  have h_div_P : q ∣ P (t - 1) := prime_dvd_P_of_lt_pt t q hq h_lt
  have h_coprime : Nat.gcd u (P (t - 1)) = 1 := by
    have h_not_in_B : u ∉ B t n := (Finset.mem_sdiff.mp hu).2
    have h_in_E : u ∈ E n (t + 3) := (Finset.mem_sdiff.mp hu).1
    have h_in_Icc : u ∈ Finset.Icc 1 n := (Finset.mem_filter.mp h_in_E).1
    have h_u_pos : u > 0 := (Finset.mem_Icc.mp h_in_Icc).1
    have h_P_pos : P (t - 1) > 0 := by
      unfold P
      apply Finset.prod_pos
      intros
      exact Nat.Prime.pos (Nat.prime_nth_prime _)
    by_contra h_gcd_ne_1
    have h_gcd_gt_1 : u.gcd (P (t - 1)) > 1 := by
      apply Nat.lt_of_le_of_ne (Nat.gcd_pos_of_pos_left (P (t - 1)) h_u_pos) (Ne.symm h_gcd_ne_1)
    apply h_not_in_B
    rw [B, Finset.mem_filter]
    exact ⟨h_in_Icc, h_gcd_gt_1⟩
  have h_div_gcd : q ∣ Nat.gcd u (P (t - 1)) := Nat.dvd_gcd hqu h_div_P
  rw [h_coprime] at h_div_gcd
  exact Nat.Prime.not_dvd_one hq h_div_gcd


def D_extra (t : ℕ) : Finset ℕ := {p t * p (t + 9)}

def D_plus (t : ℕ) : Finset ℕ := D_union t ∪ D_extra t

lemma nth_prime_eq_of_count (p n : ℕ) (hp : Nat.Prime p) (hc : Nat.count Nat.Prime p = n) :
    Nat.nth Nat.Prime n = p := by
  rw [← hc]
  exact Nat.nth_count hp

lemma satisfies_H_209 : satisfies_H 209 := by
  -- We'll use that $p_{209} = 1289$, $p_{210} = 1291$, ..., $p_{218} = 1361$, and $p_{219} = 1373$.
  have h_p_values : Nat.nth Nat.Prime 208 = 1289 ∧ Nat.nth Nat.Prime 209 = 1291 ∧ Nat.nth Nat.Prime 210 = 1297 ∧ Nat.nth Nat.Prime 211 = 1301 ∧ Nat.nth Nat.Prime 212 = 1303 ∧ Nat.nth Nat.Prime 213 = 1307 ∧ Nat.nth Nat.Prime 214 = 1319 ∧ Nat.nth Nat.Prime 215 = 1321 ∧ Nat.nth Nat.Prime 216 = 1327 ∧ Nat.nth Nat.Prime 217 = 1361 := by
    constructor
    · exact nth_prime_eq_of_count _ _ (by norm_num) count_prime_1289
    constructor
    · exact nth_prime_eq_of_count _ _ (by norm_num) count_prime_1291
    constructor
    · exact nth_prime_eq_of_count _ _ (by norm_num) count_prime_1297
    constructor
    · exact nth_prime_eq_of_count _ _ (by norm_num) count_prime_1301
    constructor
    · exact nth_prime_eq_of_count _ _ (by norm_num) count_prime_1303
    constructor
    · exact nth_prime_eq_of_count _ _ (by norm_num) count_prime_1307
    constructor
    · exact nth_prime_eq_of_count _ _ (by norm_num) count_prime_1319
    constructor
    · exact nth_prime_eq_of_count _ _ (by norm_num) count_prime_1321
    constructor
    · exact nth_prime_eq_of_count _ _ (by norm_num) count_prime_1327
    · exact nth_prime_eq_of_count _ _ (by norm_num) count_prime_1361
  unfold satisfies_H; norm_num [ h_p_values ] ;
  unfold p; norm_num [ h_p_values ] ;

lemma m_structure (t : ℕ) (m : ℕ) (h_t : t = 209) (hm_le : m ≤ p (t + 9)) (hm_factors : ∀ r, Nat.Prime r → r ∣ m → p t ≤ r) : m = 1 ∨ Nat.Prime m := by
  -- If $m$ is composite, then $m = a * b$ for some $a, b > 1$.
  by_cases h_composite : ∃ a b, 1 < a ∧ 1 < b ∧ m = a * b;
  · -- Since $a$ and $b$ are both greater than 1, their prime factors are all at least $p t$. Therefore, $a \geq p t$ and $b \geq p t$.
    obtain ⟨a, b, ha, hb, hm⟩ := h_composite
    have ha_ge_pt : a ≥ p t := by
      exact hm_factors _ ( Nat.minFac_prime ha.ne' ) ( hm.symm ▸ dvd_mul_of_dvd_left ( Nat.minFac_dvd _ ) _ ) |> le_trans <| Nat.minFac_le ha.le
    have hb_ge_pt : b ≥ p t := by
      exact hm_factors _ ( Nat.minFac_prime ( by linarith ) ) ( hm.symm ▸ dvd_mul_of_dvd_right ( Nat.minFac_dvd _ ) _ ) |> le_trans <| Nat.minFac_le <| by linarith;
    -- Since $p t$ is the 209th prime, we have $p t \geq 1289$.
    have h_pt_ge_1289 : p t ≥ 1289 := by
      subst h_t;
      unfold p;
      rw [ Nat.nth_eq_sInf ];
      refine' le_csInf _ _;
      · exact ⟨ _, Nat.prime_nth_prime 208, fun k hk => Nat.nth_strictMono ( Nat.infinite_setOf_prime ) hk ⟩;
      ·
        -- Since the 208th prime is 1289, any prime greater than all the first 208 primes must be at least 1289.
        have h_prime_208 : Nat.nth Nat.Prime 208 = 1289 := by
          -- We can use the fact that the nth prime is the nth element in the list of primes.
          have h_prime_list : Nat.nth Nat.Prime 208 = 1289 := by
            have h_prime_list : Nat.nth Nat.Prime 208 = Nat.nth Nat.Prime (Nat.count Nat.Prime 1289) := by
              rw [ count_prime_1289 ]
            rw [ h_prime_list, Nat.nth_count ];
            norm_num;
          exact h_prime_list;
        -- Since the 208th prime is 1289, any prime greater than all the first 208 primes must be at least 1289. Hence, $b \geq 1289$.
        intros b hb
        have hb_ge_1289 : Nat.nth Nat.Prime 208 ≤ b := by
          -- Since $b$ is greater than all the first 208 primes, it must be greater than or equal to the 208th prime.
          have hb_ge_208th_prime : ∀ k < 208, Nat.nth Nat.Prime k < b := by
            exact hb.2;
          rw [ Nat.nth_eq_sInf ];
          exact Nat.sInf_le ⟨ hb.1, hb_ge_208th_prime ⟩;
        linarith
    -- Since $p (t + 9)$ is the 218th prime, we have $p (t + 9) \leq 1361$.
    have h_pt9_le_1361 : p (t + 9) ≤ 1361 := by
      subst h_t;
      exact Nat.le_of_lt_succ ( Nat.nth_lt_of_lt_count count_prime_1362_gt_217 );
    nlinarith only [ ha_ge_pt, hb_ge_pt, h_pt_ge_1289, h_pt9_le_1361, hm_le, hm ];
  · rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.prime_def_lt' ];
    · contrapose! hm_factors;
      exact ⟨ 2, by norm_num, by intros; linarith, by rw [ show p 209 = Nat.nth Nat.Prime 208 by rfl ] ; exact Nat.lt_of_le_of_lt ( Nat.Prime.two_le <| Nat.prime_nth_prime 0 ) <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) <| by norm_num ⟩;
    · exact fun x hx₁ hx₂ hx₃ => h_composite x hx₁ ( ( m + 1 + 1 ) / x ) ( by nlinarith [ Nat.div_mul_cancel hx₃ ] ) ( by nlinarith [ Nat.div_mul_cancel hx₃ ] )


def D_extra_v3 (t : ℕ) : Finset ℕ := {p t * p (t + 9)}

def D_plus_v3 (t : ℕ) : Finset ℕ := D_union t ∪ D_extra_v3 t

lemma p_t_sq_gt_p_t_plus_9_v3 (t : ℕ) (h_t : t = 209) : p t ^ 2 > p (t + 9) := by
  -- By definition of $p$, we know that $p 209 = 1289$ and $p 218 = 1361$.
  have h_p209 : p 209 = 1289 := by
    -- We can use the fact that the 209th prime is known to be 1289.
    have h_prime_209 : Nat.nth Nat.Prime 208 = 1289 := by
      have h_prime_list : Nat.nth Nat.Prime 208 = 1289 := by
        have h_prime_count : Nat.count Nat.Prime 1289 = 208 := by
          exact count_prime_1289
        rw [ ← h_prime_count, Nat.nth_count ];
        exact prime_1289
      exact h_prime_list;
    exact h_prime_209
  have h_p218 : p 218 = 1361 := by
    -- We'll use the fact that $p_{218}$ is the $218$-th prime number.
    have h_prime_218 : Nat.nth Nat.Prime 217 = 1361 := by
      have : Nat.count (Nat.Prime) 1361 = 217 := by
        exact count_prime_1361
      rw [ ← this, Nat.nth_count ];
      norm_num;
    exact h_prime_218;
  norm_num [ h_t, h_p209, h_p218 ]

lemma m_is_prime_or_one_v3 (t : ℕ) (m : ℕ) (h_t : t = 209) (hm_le : m ≤ p (t + 9)) (hm_factors : ∀ r, Nat.Prime r → r ∣ m → p t ≤ r) : m = 1 ∨ Nat.Prime m := by
  exact m_structure t m h_t hm_le hm_factors


lemma D_subset_D_plus_final (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) : D t n ⊆ D_plus t := by
  intro u hu
  obtain ⟨hu_E, hu_B⟩ := Finset.mem_sdiff.mp hu
  have hu_prime_factors : ∀ q, Nat.Prime q → q ∣ u → q ≥ p t := by
    exact fun q a a_1 ↦ D_prime_factors_ge_pt_new t n u hu q a a_1
  have hu_product : ∃ q m, u = q * m ∧ q ∈ D_primes t ∧ m ≤ p (t + 9) := by
    -- Since $u \in E n (t + 3)$, there exists a prime $q$ such that $q \mid u$ and $q \le p (t + 3)$.
    obtain ⟨q, hq_prime, hq_div, hq_le⟩ : ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ≤ p (t + 3) := by
      exact D_has_small_prime_factor t n u hu
    -- Since $q$ is a prime divisor of $u$ and $q \leq p(t+3)$, and $p(t)$ is the $t$-th prime, $q$ must be one of $p(t)$, $p(t+1)$, $p(t+2)$, or $p(t+3)$. Therefore, $q \in D_primes t$.
    have hq_in_D_primes : q ∈ D_primes t := by
      have hq_in_D_primes : ∃ i ∈ Finset.range 4, q = p (t + i) := by
        have hq_in_D_primes : ∃ i, t ≤ i ∧ i ≤ t + 3 ∧ q = Nat.nth Nat.Prime (i - 1) := by
            have hq_in_D_primes : ∃ i, q = Nat.nth Nat.Prime i := by
              exact ⟨ Nat.count ( Nat.Prime ) q, by rw [ Nat.nth_count ] ; aesop ⟩;
            obtain ⟨ i, rfl ⟩ := hq_in_D_primes
            use i + 1
            constructor
            · by_contra hlt
              have hi_lt : i + 1 < t := Nat.lt_of_not_ge hlt
              have hsmall : Nat.nth Nat.Prime i < p t := by
                unfold p
                exact Nat.nth_strictMono (Nat.infinite_setOf_prime) (by omega)
              exact (not_le_of_gt hsmall) (hu_prime_factors _ (Nat.prime_nth_prime i) hq_div)
            constructor
            · have h_prime_le : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime (t + 2) := by
                simpa [p, Nat.add_assoc] using hq_le
              have hi_le : i ≤ t + 2 := by
                exact Nat.le_of_not_lt fun hi =>
                  (not_lt_of_ge h_prime_le) (Nat.nth_strictMono (Nat.infinite_setOf_prime) hi)
              omega
            · simp
        obtain ⟨ i, hi₁, hi₂, hi₃ ⟩ := hq_in_D_primes; use i - t; aesop; omega;
      aesop;
      exact Finset.mem_image.mpr ⟨ w, Finset.mem_range.mpr left, rfl ⟩;
    obtain ⟨ m, rfl ⟩ := hq_div; use q, m; aesop;
    have hm_le : q * m ≤ p 209 * p 218 := by
      unfold E at hu_E; aesop;
    generalize_proofs at *;
    nlinarith [ hu_prime_factors q hq_prime ( dvd_mul_right q m ), Nat.Prime.two_le hq_prime ]
  obtain ⟨q, m, hu_eq, hq_prime_factors, hm_le⟩ := hu_product
  have hm_factors : ∀ r, Nat.Prime r → r ∣ m → p t ≤ r := by
    -- Since $m \mid u$ and $u \in D t n$, any prime divisor of $m$ must also divide $u$. Therefore, by $hu_prime_factors$, those primes must be at least $p t$.
    intros r hr_prime hr_div_m
    have hr_div_u : r ∣ u := by
      exact hu_eq.symm ▸ dvd_mul_of_dvd_right hr_div_m _
    exact hu_prime_factors r hr_prime hr_div_u
  have hm_is_prime_or_one : m = 1 ∨ Nat.Prime m := by
    simp +zetaDelta at *;
    exact m_structure t m h_t hm_le hm_factors
  have hu_in_D_plus : u ∈ D_plus t := by
    cases hm_is_prime_or_one <;> simp_all +decide [ Finset.subset_iff ];
    · -- Since $q \in D_{\text{primes}} 209$, and $D_{\text{primes}} 209 \subseteq D_{\text{union}} 209$, it follows that $q \in D_{\text{plus}} 209$.
      have hq_in_D_union : q ∈ D_union 209 := by
        exact Finset.mem_union_left _ ( Finset.mem_union_left _ hq_prime_factors )
      exact Finset.mem_union_left _ hq_in_D_union;
    · -- Since $m$ is prime and $m \leq p (t + 9)$, we have $m \in \{p t, \dots, p (t + 9)\}$.
      have hm_prime_factors : m ∈ Finset.image (fun i => p (209 + i)) (Finset.range 10) := by
        have hm_prime_factors : ∃ i ∈ Finset.range 10, m = p (209 + i) := by
          have h_prime_factors : ∃ i, m = p i := by
            use Nat.count ( Nat.Prime ) m + 1;
            unfold p; aesop;
          obtain ⟨i, hi⟩ := h_prime_factors
          have h_prime_factors : i ≤ 218 := by
            contrapose! hm_le;
            exact hi.symm ▸ p_strictMono_new ( by linarith ) hm_le;
          have h_prime_factors : i ≥ 209 := by
            contrapose! hm_factors; aesop;
            exact ⟨ p i, h, dvd_rfl, by
              apply_rules [ Nat.nth_strictMono ];
              · exact Nat.infinite_setOf_prime;
              · omega ⟩;
          exact ⟨ i - 209, Finset.mem_range.mpr ( by omega ), by rw [ hi, add_tsub_cancel_of_le h_prime_factors ] ⟩;
        aesop;
      aesop;
      by_cases hw : w = 9;
      · subst hw; unfold D_plus; aesop;
        -- Since $q$ is in $D_primes 209$, $q$ must be one of $p 209$, $p 210$, $p 211$, or $p 212$. However, if $q$ were any of the latter three, then $q * p 218$ would be larger than $interval_end 209$, contradicting the fact that $q * p 218$ is in $D 209 (interval_end 209)$. Therefore, $q$ must be $p 209$.
        have hq_eq_p209 : q = p 209 := by
          unfold D_primes at hq_prime_factors; aesop;
          have hq_le_p209 : p (209 + w) * p 218 ≤ p 209 * p 218 := by
            unfold E at hu_E; aesop;
          exact le_antisymm ( by nlinarith [ Nat.Prime.two_le h ] ) ( hu_prime_factors _ ( Nat.prime_nth_prime _ ) ( dvd_mul_right _ _ ) );
        exact Or.inr ( by unfold D_extra; aesop );
      · -- Since $w \neq 9$, we have $w \leq 8$, so $p (209 + w) \in \{p 209, \dots, p 217\}$.
        have hw_le_8 : w ≤ 8 := by
          omega;
        have hw_le_8 : q * p (209 + w) ∈ D_products 209 ∪ D_squares 209 := by
          unfold D_primes at hq_prime_factors; aesop;
          -- Since $w_1 < 4$ and $w \leq 8$, we can check all possible pairs $(w_1, w)$ to see if their product is in $D_products 209$ or $D_squares 209$.
          by_cases h_cases : w_1 = w;
          · unfold D_squares; aesop;
            exact Or.inr ⟨ w_1, left_1, by ring ⟩;
          · -- Since $w_1 \neq w$, we have either $w_1 < w$ or $w < w_1$. In either case, $p (209 + w_1) * p (209 + w)$ is in $D_products 209$.
            have h_prod : p (209 + w_1) * p (209 + w) ∈ D_products 209 := by
              apply Finset.mem_filter.mpr;
              cases lt_or_gt_of_ne h_cases <;> first | exact ⟨ Finset.mem_image.mpr ⟨ ( w_1, w ), Finset.mem_product.mpr ⟨ Finset.mem_range.mpr left_1, Finset.mem_range.mpr ( by linarith ) ⟩, rfl ⟩, w_1, w, by linarith, by linarith, by linarith, by linarith, by linarith, rfl ⟩ | exact ⟨ Finset.mem_image.mpr ⟨ ( w, w_1 ), Finset.mem_product.mpr ⟨ Finset.mem_range.mpr ( by linarith ), Finset.mem_range.mpr ( by linarith ) ⟩, by ring ⟩, w, w_1, by linarith, by linarith, by linarith, by linarith, by linarith, by ring ⟩ ;
            exact Or.inl h_prod;
        simp +decide +zetaDelta (disch := grind) at *;
        -- Since $q * p (209 + w)$ is in $D_products 209$ or $D_squares 209$, and $D_plus 209$ is the union of $D_union 209$ and $D_extra 209$, it follows that $q * p (209 + w)$ is in $D_plus 209$.
        apply Finset.mem_union_left; exact (by
        unfold D_union; aesop;)
  exact hu_in_D_plus

lemma card_D_plus_final (t : ℕ) (h_t : t = 209) : (D_plus t).card ≤ 35 := by
  -- By definition of $D_union$, we know that its cardinality is at most 34.
  have hD_union_card : (D_union t).card ≤ 34 := by
    -- Let's calculate the cardinality of each component of D_union t.
    have hD_primes_card : (D_primes t).card = 4 := by
      -- Since $p$ is injective, the image of $p (t + i)$ over the range $0$ to $3$ has cardinality $4$.
      have hD_primes_card : (Finset.image (fun i => p (t + i)) (Finset.range 4)).card = 4 := by
        exact Finset.card_image_of_injective _ fun x y hxy => by simpa using StrictMono.injective ( show StrictMono ( fun i => p ( t + i ) ) from by exact fun i j hij => p_strictMono_new ( by linarith ) ( by linarith ) ) hxy;
      exact hD_primes_card
    have hD_squares_card : (D_squares t).card = 4 := by
      rw [ show D_squares t = Finset.image ( fun i => p ( t + i ) ^ 2 ) ( Finset.range 4 ) from rfl, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, h_t ];
      unfold p; aesop;
      have := Nat.nth_injective ( Nat.infinite_setOf_prime ) a ; aesop
    have hD_products_card : (D_products t).card ≤ 26 := by
      simp +arith +decide [ D_products ];
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.image ( fun x : ℕ × ℕ => p ( t + x.1 ) * p ( t + x.2 ) ) ( Finset.filter ( fun x : ℕ × ℕ => x.1 ≤ 3 ∧ 1 ≤ x.2 ∧ x.2 ≤ 8 ∧ x.1 < x.2 ) ( Finset.range 4 ×ˢ Finset.range 9 ) );
      · simp ( config := { contextual := Bool.true } ) [ Finset.subset_iff ];
        exact fun x i j hi hj hx k hk l hl hl' hkl hx' => ⟨ k, l, ⟨ ⟨ by linarith, by linarith ⟩, by linarith, by linarith, by linarith, by linarith ⟩, hx' ▸ rfl ⟩;
      · exact Finset.card_image_le.trans ( by decide );
    refine' le_trans ( Finset.card_union_le _ _ ) _ ; linarith [ Finset.card_union_le ( D_primes t ∪ D_squares t ) ( D_products t ), Finset.card_union_le ( D_primes t ) ( D_squares t ) ];
  -- Since $D_{\text{extra}} t$ is a singleton set, its cardinality is 1.
  have hD_extra_card : (D_extra t).card = 1 := by
    -- Since $p t$ and $p (t + 9)$ are primes, their product is a single element. Therefore, the set $\{p t * p (t + 9)\}$ has exactly one element.
    simp [D_extra];
  exact le_trans ( Finset.card_union_le _ _ ) ( by linarith )

lemma card_C_209_final (t : ℕ) (h_t : t = 209) : (C t).card = 36 := by
  subst h_t; exact card_C 209 satisfies_H_209;


lemma D_decomp_final (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) (u : ℕ) (hu : u ∈ D t n) :
  ∃ q ∈ D_primes t, ∃ m, u = q * m ∧ (m = 1 ∨ (Nat.Prime m ∧ p t ≤ m)) ∧ m ≤ p (t + 9) := by
    -- Since $u \in D t n$, it must have a prime factor $q$ that divides $P(t + 3)$ but not $P(t - 1)$. Therefore, $q \in \{p t, p (t + 1), p (t + 2), p (t + 3)\}$.
    obtain ⟨q, hq_prime, hq_div⟩ : ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ∈ D_primes t := by
      -- Since $u \in D t n$, it must have a prime factor $q$ that divides $P(t + 3)$ but not $P(t - 1)$. Therefore, $q \in \{p t, p (t + 1), p (t + 2), p (t + 3)\}$ by definition of $D t n$.
      obtain ⟨q, hq_prime, hq_div⟩ : ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ∣ P (t + 3) ∧ ¬(q ∣ P (t - 1)) := by
        unfold D at hu; aesop;
        unfold E B at * ; aesop;
        obtain ⟨ q, hq_prime, hq_div_u, hq_div_P ⟩ :=
          Nat.Prime.not_coprime_iff_dvd.mp ( ne_of_gt right_1 );
        exact ⟨ q, hq_prime, hq_div_u, hq_div_P, fun h => (not_lt_of_ge right) <|
          Nat.lt_of_lt_of_le ( Nat.Prime.one_lt hq_prime ) <|
            Nat.le_of_dvd ( Nat.gcd_pos_of_pos_left _ left ) <| Nat.dvd_gcd hq_div_u h ⟩;
      unfold P at *; aesop;
      -- Since $q$ divides the product of the first 212 primes but not the product of the first 208 primes, $q$ must be one of the primes in the range from 208 to 211.
      have hq_range : ∃ i ∈ Finset.range 4, q = Nat.nth Nat.Prime (208 + i) := by
        have hq_range : ∃ i ∈ Finset.range 212, q = Nat.nth Nat.Prime i := by
          simp_all +contextual [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff, Nat.coprime_prod_left_iff ];
          obtain ⟨ i, hi, hi' ⟩ := left_1; use i; aesop;
          have := Nat.coprime_primes hq_prime ( Nat.prime_nth_prime i ) ; aesop;
        obtain ⟨ i, hi, rfl ⟩ := hq_range;
        exact ⟨ i - 208, Finset.mem_range.mpr ( by rw [ tsub_lt_iff_left ] <;> linarith [ Finset.mem_range.mp hi, show i ≥ 208 from Nat.le_of_not_lt fun hi' => right <| Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr hi' ] ), by rw [ add_tsub_cancel_of_le <| by linarith [ Finset.mem_range.mp hi, show i ≥ 208 from Nat.le_of_not_lt fun hi' => right <| Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr hi' ] ] ⟩;
      obtain ⟨ w, hw, hq_eq ⟩ := hq_range
      refine' ⟨ q, hq_prime, left, _ ⟩
      unfold D_primes
      exact Finset.mem_image.mpr ⟨ w, hw, by rw [hq_eq]; unfold p; congr; omega ⟩
    -- Since $u \in D t n$, we have $u \leq n = p t p (t + 9)$. Therefore, $m = u / q \leq p (t + 9)$.
    obtain ⟨m, hm⟩ : ∃ m, u = q * m ∧ m ≤ p (t + 9) := by
      -- Since $u \in D t n$, we have $u \leq n = p t p (t + 9)$. Therefore, $m = u / q \leq p (t + 9)$ because $q \geq p t$.
      have hm_le : u ≤ p t * p (t + 9) := by
        unfold D at hu; aesop;
        unfold E at left_1; aesop;
      -- Since $q \geq p t$ and $u \leq p t * p (t + 9)$, we have $m = u / q \leq p (t + 9)$.
      have hm_le : q ≥ p t := by
        -- Since $q \in D_primes t$, we have $q \geq p t$ by definition of $D_primes t$.
        have hq_ge_pt : q ∈ Finset.image (fun i => p (t + i)) (Finset.range 4) := by
          exact hq_div.2;
        aesop;
        interval_cases w <;> exact Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by norm_num );
      exact ⟨ u / q, by rw [ Nat.mul_div_cancel' hq_div.1 ], Nat.div_le_of_le_mul <| by nlinarith ⟩;
    have hm_factors : ∀ r, Nat.Prime r → r ∣ m → p t ≤ r := by
      intros r hr hr_div
      have hr_div_u : r ∣ u := by
        exact hm.1.symm ▸ dvd_mul_of_dvd_right hr_div _;
      exact D_prime_factors_ge_pt_new t n u hu r hr hr_div_u
    have := m_is_prime_or_one_v3 t m h_t hm.2 hm_factors; aesop;

lemma D_subset_D_plus_final_v2 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) : D t n ⊆ D_plus t := by
  aesop;
  -- Apply the lemma that states D t n is a subset of D_plus t.
  apply D_subset_D_plus_final; norm_num; norm_num

lemma card_D_plus_final_v2 (t : ℕ) (h_t : t = 209) : (D_plus t).card ≤ 35 := by
  -- Apply the lemma `card_D_plus_final` with the given `h_t`.
  rw [h_t]
  apply card_D_plus_final
  norm_cast

lemma card_C_209_final_v2 (t : ℕ) (h_t : t = 209) : (C t).card = 36 := by
  subst h_t;
  exact card_C_209_final 209 rfl


lemma D_decomp_final_v3 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) (u : ℕ) (hu : u ∈ D t n) :
  ∃ q ∈ D_primes t, ∃ m, u = q * m ∧ (m = 1 ∨ (Nat.Prime m ∧ p t ≤ m)) ∧ m ≤ p (t + 9) := by
    exact D_decomp_final t n h_t h_n u hu

lemma D_subset_D_plus_final_v3 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) : D t n ⊆ D_plus t := by
  exact D_subset_D_plus_final t n h_t h_n

lemma card_D_plus_final_v3 (t : ℕ) (h_t : t = 209) : (D_plus t).card ≤ 35 := by
  exact h_t.symm ▸ card_D_plus_final_v2 _ rfl

lemma card_C_209_final_v3 (t : ℕ) (h_t : t = 209) : (C t).card = 36 := by
  -- By definition of $C$, we know that its cardinality is 36 when $t = 209$.
  apply card_C_209_final_v2 t h_t


lemma D_subset_D_plus_v5 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) : D t n ⊆ D_plus_v3 t := by
  apply_rules [ D_subset_D_plus_final_v2 ]

lemma card_D_plus_v5 (t : ℕ) (h_t : t = 209) : (D_plus_v3 t).card ≤ 35 := by
  subst h_t
  -- Apply the lemma `card_D_plus_final_v3` with `t = 209`.
  apply card_D_plus_final_v3 209 rfl

lemma card_C_209_v5 (t : ℕ) (h_t : t = 209) : (C t).card = 36 := by
  -- By definition of $C$, we know that its cardinality is 36.
  apply card_C_209_final_v3 t h_t


lemma gcd_P_iff (k u : ℕ) : Nat.gcd u (P k) > 1 ↔ ∃ q, Nat.Prime q ∧ q ∣ u ∧ ∃ i < k, q = Nat.nth Nat.Prime i := by
  apply Iff.intro
  · intro h_gcd
    obtain ⟨q, hq_prime, hq_div_u, hq_div_Pk⟩ : ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ∣ P k := by
      exact Nat.Prime.not_coprime_iff_dvd.mp h_gcd.ne'
    have hq_div_prime : ∃ i ∈ Finset.range k, q ∣ Nat.nth Nat.Prime i := by
      unfold P at hq_div_Pk
      exact (Prime.dvd_finset_prod_iff
        (show Prime q from hq_prime.prime) (fun i => Nat.nth Nat.Prime i)).1 hq_div_Pk
    obtain ⟨i, hi, hdiv⟩ := hq_div_prime
    exact ⟨q, hq_prime, hq_div_u, i, Finset.mem_range.mp hi,
      (Nat.prime_dvd_prime_iff_eq hq_prime (Nat.prime_nth_prime i)).mp hdiv⟩
  · rintro ⟨q, hq_prime, hq_div_u, i, hi, hq_eq⟩
    have hq_div_P : q ∣ P k := by
      unfold P
      rw [hq_eq]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hi)
    have hP_pos : 0 < P k := by
      unfold P
      exact Finset.prod_pos fun i hi => (Nat.prime_nth_prime i).pos
    exact lt_of_lt_of_le hq_prime.one_lt
      (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right u hP_pos) (Nat.dvd_gcd hq_div_u hq_div_P))


lemma D_decomp_final_v4 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) (u : ℕ) (hu : u ∈ D t n) :
  ∃ q ∈ D_primes t, ∃ m, u = q * m ∧ (m = 1 ∨ (Nat.Prime m ∧ p t ≤ m)) ∧ m ≤ p (t + 9) := by
    have := D_decomp_final_v3 209 n; aesop

lemma D_subset_D_plus_final_v4 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) : D t n ⊆ D_plus t := by
  exact D_subset_D_plus_final t n h_t h_n

lemma card_D_plus_final_v4 (t : ℕ) (h_t : t = 209) : (D_plus t).card ≤ 35 := by
  subst h_t; exact card_D_plus_final_v3 _ rfl;

lemma card_C_209_final_v4 (t : ℕ) (h_t : t = 209) : (C t).card = 36 := by
  -- Apply the lemma that states the cardinality of C t is 36 when t is 209.
  apply card_C_209_final_v3 t h_t


/--
Say a set of natural numbers is `k`-weakly divisible if any `k+1` elements
of `A` are not relatively prime.
-/
def WeaklyDivisible (k : ℕ) (A : Finset ℕ) : Prop :=
    ∀ s ∈ A.powersetCard (k + 1), ¬ Set.Pairwise s Nat.Coprime

/--
`MaxWeaklyDivisible N k` is the size of the largest k-weakly divisible subset of `{1,..., N}`
-/
noncomputable def MaxWeaklyDivisible (N k : ℕ) : ℕ :=
  sSup { n : ℕ |
    ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧
      WeaklyDivisible k A ∧
      A.card = n }

/--
`FirstPrimesMultiples N k` is the set of numbers in `{1,..., N}` that are
a multiple of one of the first `k` primes.
-/
noncomputable def FirstPrimesMultiples (N k : ℕ) : Finset ℕ :=
    (Finset.Icc 1 N).filter fun i => ∃ j < k, (j.nth Nat.Prime ∣ i)

/--
Suppose $A \subseteq \{1,\dots,N\}$ is such that there are no $k+1$ elements of $A$ which are
relatively prime. An example is the set of all multiples of the first $k$ primes.
Is this the largest such set?
-/
theorem erdos_56 :
  (∀ᵉ (N ≥ 2) (k > 0),
      N ≥ k.nth Nat.Prime →
      MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card) ↔
    False := by
  -- By definition of $A$, we know that $|A| = |B| + |C|$.
  have hA_card : (A 209 (p 209 * p 218)).card = (B 209 (p 209 * p 218)).card + (C 209).card := by
    rw [ ← Finset.card_union_of_disjoint ];
    · rfl;
    · exact B_disjoint_C 209 (p 209 * p 218)
  -- Since $|C| = 36$ and $|D| \leq 35$, we have $|A| = |B| + |C| > |B| + |D| = |E|$.
  have hA_gt_E : (A 209 (p 209 * p 218)).card > (FirstPrimesMultiples (p 209 * p 218) 212).card := by
    -- Substitute hA_card and hE_card into the goal.
    rw [hA_card, show (FirstPrimesMultiples (p 209 * p 218) 212).card = (B 209 (p 209 * p 218)).card + (D 209 (p 209 * p 218)).card from ?_];
    · have hD_lt_C : (D 209 (p 209 * p 218)).card < (C 209).card := by
        refine' lt_of_le_of_lt ( Finset.card_le_card ( D_subset_D_plus_final_v4 _ _ rfl rfl ) ) _;
        exact lt_of_le_of_lt ( card_D_plus_final_v4 _ rfl ) ( by rw [ card_C_209_final_v4 _ rfl ] ; norm_num );
      exact Nat.add_lt_add_left hD_lt_C (B 209 (p 209 * p 218)).card
    · -- By definition of $B$ and $D$, we know that $B \cup D = \text{FirstPrimesMultiples}(N, k)$.
      have h_union : B 209 (p 209 * p 218) ∪ D 209 (p 209 * p 218) = FirstPrimesMultiples (p 209 * p 218) 212 := by
        ext; simp [B, D, FirstPrimesMultiples];
        unfold E; aesop;
        · -- Since $a$ is divisible by some prime in the first 208 primes, we can find such a $j$.
          obtain ⟨j, hj⟩ : ∃ j < 208, Nat.nth Nat.Prime j ∣ a := by
            contrapose! right;
            refine' Nat.le_of_eq _;
            refine' Nat.Coprime.prod_right fun i hi => _;
            exact Nat.Coprime.symm ( Nat.Prime.coprime_iff_not_dvd ( Nat.prime_nth_prime i ) |>.2 ( right i ( Finset.mem_range.mp hi ) ) );
          exact ⟨ j, by linarith, hj.2 ⟩;
        · contrapose! right;
          refine' Nat.le_of_eq ( Nat.coprime_prod_right_iff.mpr _ );
          exact fun i hi => Nat.Coprime.symm <| Nat.Prime.coprime_iff_not_dvd ( Nat.prime_nth_prime i ) |>.2 <| right i <| Finset.mem_range.mp hi;
        · refine' Or.inr ( lt_of_lt_of_le ( Nat.Prime.one_lt ( Nat.prime_nth_prime w ) ) ( Nat.le_of_dvd ( Nat.gcd_pos_of_pos_left _ left ) ( Nat.dvd_gcd right ( dvd_trans ( by norm_num ) ( Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr left_1 ) ) ) ) ) );
      rw [ ← h_union, Finset.card_union_of_disjoint ];
      unfold B D; aesop;
      rw [ Finset.disjoint_left ] ; aesop;
      unfold E B at *; aesop;
  -- Since $A$ is a $k$-weakly divisible subset and its size is larger than $E$'s, this implies that $MaxWeaklyDivisible N k$ is at least as large as $A$'s size.
  have h_max_ge_A : MaxWeaklyDivisible (p 209 * p 218) 212 ≥ (A 209 (p 209 * p 218)).card := by
    apply le_csSup;
    · exact ⟨ _, fun n hn => hn.choose_spec.2.2 ▸ Finset.card_le_card hn.choose_spec.1 ⟩;
    · refine' ⟨ A 209 ( p 209 * p 218 ), _, _, rfl ⟩;
      · simp +zetaDelta at *;
        apply Finset.union_subset;
        · exact Finset.filter_subset _ _;
        · apply C_subset_n;
          · exact satisfies_H_209
          · exact satisfies_H_209.1.le;
      · -- Since $A$ is constructed as the union of $B$ and $C$, and we've shown that both $B$ and $C$ have no $k+1$ pairwise coprime elements, their union should also have this property.
        have hA_weakly_divisible : has_no_k_plus_1_coprime (A 209 (p 209 * p 218)) 212 := by
          apply A_no_k_plus_1_final;
          · exact satisfies_H_209
          · exact B_disjoint_C 209 (p 209 * p 218)
        intro s hs; specialize hA_weakly_divisible s; aesop;
  contrapose! hA_gt_E;
  have h_max_ge_A : MaxWeaklyDivisible (p 209 * p 218) 212 = (FirstPrimesMultiples (p 209 * p 218) 212).card := by
    apply hA_gt_E.elim;
    · aesop;
      apply a;
      · -- Since $p$ is the nth prime, and primes are always greater than or equal to 2, multiplying two primes will definitely give a number that's at least 2*2=4. So, 2 ≤ 4, which is true.
        have h_prime_ge_two : ∀ n, 2 ≤ Nat.nth Nat.Prime n := by
          exact fun n => Nat.Prime.two_le ( Nat.prime_nth_prime n );
        exact le_trans ( by norm_num ) ( Nat.mul_le_mul ( h_prime_ge_two _ ) ( h_prime_ge_two _ ) );
      · norm_num;
      · unfold p;
        refine' le_trans _ ( Nat.mul_le_mul ( Nat.nth_monotone _ <| show 208 ≥ 208 by norm_num ) ( Nat.nth_monotone _ <| show 217 ≥ 212 by norm_num ) );
        · exact le_mul_of_one_le_left ( Nat.zero_le _ ) ( Nat.Prime.pos ( by norm_num ) );
        · exact Nat.infinite_setOf_prime;
        · exact Nat.infinite_setOf_prime;
    · tauto;
  linarith

#print axioms erdos_56
-- 'Erdos56.erdos_56' depends on axioms: [propext, Classical.choice, Quot.sound]

end

end Erdos56
