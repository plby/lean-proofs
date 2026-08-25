"""Reproduce the proper-divisor data and the Lean certificate assembly.

Run with --check to compare generated text with the checked-in files.
This script is not trusted by the proof: Lean checks every divisor, rounded
integer multiplication, and final rational comparison in its kernel.
"""

import argparse
from math import isqrt
from pathlib import Path


def generate() -> dict[str, str]:
    limit = 131072
    factors = [0] * (limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if factors[p] == 0:
            for n in range(p * p, limit + 1, p):
                if factors[n] == 0:
                    factors[n] = p

    outputs = {}
    upper = 10**12
    rows = []
    chunks = []
    for index, start in enumerate(range(2, limit + 1, 512)):
        data = factors[start : min(start + 512, limit + 1)]
        old = upper
        for n, divisor in enumerate(data, start):
            if divisor == 0:
                upper = (upper * n + n - 2) // (n - 1)
            else:
                assert 1 < divisor < n and n % divisor == 0
        name = f"productData{index:03d}"
        entries = ",\n    ".join(
            ", ".join(map(str, data[j : j + 32])) for j in range(0, len(data), 32)
        )
        rows.append(f"""def {name} : List ℕ :=
  [{entries}]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem {name}_checked :
    roundedProductCertificate {start} {old} {name} = some {upper} := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem {name}_length : {name}.length = {len(data)} := by decide
""")
        chunks.append(index)
        if len(rows) == 16 or start + 512 > limit:
            batch = index // 16
            outputs[f"ProductData/Block{batch:02d}.lean"] = (
                "import ErdosProblems.Erdos490.ProductCertificate\n\n"
                "/-! Generated proper-divisor data. Every certificate is kernel checked. -/\n\n"
                "set_option linter.style.longLine false\n"
                "set_option linter.style.setOption false\n\n"
                "namespace Erdos490\n\n" + "\n".join(rows) + "\nend Erdos490\n"
            )
            rows = []

    assert upper == 20992098037658
    assert upper < 211 * 10**11
    assembly = "".join(
        f"import ErdosProblems.Erdos490.ProductData.Block{batch:02d}\n"
        for batch in range(16)
    )
    assembly += """
namespace Erdos490

theorem reciprocalPrefix_131071_lt : reciprocalPrefix 131071 < (211 / 10 : ℝ) := by
  have h0 : (1000000000000 : ℝ) * reciprocalPrefix 0 ≤ 1000000000000 := by
    norm_num [reciprocalPrefix]
"""
    for index in chunks:
        assembly += (
            f"  have h{index + 1} := certificate_prefix_step h{index} productData{index:03d}_checked\n"
            f"  simp only [productData{index:03d}_length, Nat.reduceAdd] at h{index + 1}\n"
        )
    assembly += """  norm_num at h256
  linarith

#print axioms reciprocalPrefix_131071_lt

end Erdos490
"""
    outputs["PrimeProductBound.lean"] = assembly
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify without writing")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    outputs = generate()
    for relative, expected in outputs.items():
        path = root / relative
        if args.check:
            if not path.exists() or path.read_text() != expected:
                raise SystemExit(f"Certificate differs: {path}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected)
    print(f"{'Checked' if args.check else 'Generated'} {len(outputs)} certificate files.")


if __name__ == "__main__":
    main()
