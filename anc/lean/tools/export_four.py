"""Export the direct four-point certificate; Lean checks all exported witnesses.

Reuses the five-point matrix checker. NumPy proposes a rational Gram matrix;
its residual diagonal dominance, the cover, and all pattern scores are proved
by `decide +kernel`. Run with a Python environment containing NumPy.
"""
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "proofs/s3/0.400695372__c2"))
from field_r import K, r_enclosure

OUT = ROOT / "lean/Fast/Four"


def rat(value):
    v = Q(value)
    if v.denominator == 1:
        return str(v.numerator) if v >= 0 else f"({v.numerator})"
    return f"(({v.numerator} : Rat) / {v.denominator})"


def fk(value):
    return "⟨" + ", ".join(rat(v) for v in K(value).v) + "⟩"


def arr(values):
    return "#[" + ", ".join(values) + "]"


def lst(values):
    return "[" + ", ".join(values) + "]"


def mat(values):
    return arr([arr([fk(v) for v in row]) for row in values])


def bits(pattern):
    return sum(1 << i for i, c in enumerate(pattern) if c == "+")


def main():
    cert = json.loads((ROOT / "proofs/s3/0.400695372__c2/cert_exact.json").read_text())
    cover = json.loads((ROOT / "proofs/s3/0.400695372__c2/cover_n4.json").read_text())
    assert cert["cuts"] == cover["cuts"] == ["7/6", "3/2", "2"]
    lo, hi = r_enclosure(100)

    def lower(v):
        return v.v[0] + sum(a * (lo**i if a >= 0 else hi**i)
                            for i, a in enumerate(v.v[1:], 1))

    def upper(v):
        return v.v[0] + sum(a * (hi**i if a >= 0 else lo**i)
                            for i, a in enumerate(v.v[1:], 1))

    source = ["import Fast.Four.Basic", "set_option maxRecDepth 10000",
              "namespace Fast.Four.Data",
              f"def encLo : Int := {int(lo * 2**100)}",
              f"def encHi : Int := {int(hi * 2**100)}",
              "def encM : Nat := 100",
              "def low : Rat := (encLo : Rat) / 2^encM",
              "def high : Rat := (encHi : Rat) / 2^encM"]
    for bi, b in enumerate(cert["blocks"]):
        assert (b["t"], b["f"]) == (2, 3)
        W = [[K(v) for v in row] for row in b["W"]]
        Y = [[K(v) for v in row] for row in b["Y"]]
        k = len(Y)
        WY = [[sum((a * c for a, c in zip(row, col)), K(0))
               for col in zip(*Y)] for row in W]
        expanded = [[sum((a * c for a, c in zip(row, col)), K(0))
                     for col in W] for row in WY]
        Yn = np.array([[float(v) for v in row] for row in Y])
        margin = float(np.linalg.eigvalsh(Yn)[0]) / 2
        assert margin > 0
        Gfloat = np.linalg.cholesky(Yn - margin * np.eye(k))
        den = 10**10
        G = [[round(float(v) * den) for v in row] for row in Gfloat]
        residual = [[Y[i][j] - Q(sum(a * c for a, c in zip(G[i], G[j])), den**2)
                     for j in range(k)] for i in range(k)]
        assert all(lower(residual[i][i]) >
                   sum(max(-lower(residual[i][j]), upper(residual[i][j]))
                       for j in range(k) if j != i) for i in range(k))
        flags = [3 * bits(p) + [[0, 1], [0, 2], [1, 2]].index(marks)
                 for p, marks in b["flags"]]
        sparse = arr([lst([f"({j}, {fk(v)})" for j, v in enumerate(row) if v])
                      for row in W])
        source.append(f"""def block{bi} : Block := {{
  roots := 2, flagSize := 3, ty := {bits(b['type'])}
  flags := {arr(list(map(str, flags)))}
  basis := {sparse}
  matrix := {mat(Y)}
  expanded := {mat(expanded)}
  gram := {arr([lst([str(v) if v >= 0 else f'({v})' for v in row]) for row in G])}
  gramDen := {den}
}}""")
    source.append("def blocks : Array Block := " +
                  arr([f"block{i}" for i in range(len(cert["blocks"]))]))
    patterns = {p: i for i, p in enumerate(cover["patterns"])}
    source.append("def patterns : Array Nat := " +
                  arr([str(bits(p)) for p in patterns]))
    # The JSON forms are rational; Lean uses positive integer multiples.
    scales = [Q(6), Q(2), Q(1)] * 6 + [Q(1), Q(1)]

    def tree(prefix):
        if prefix in patterns:
            return f"(.retained {patterns[prefix]})"
        if prefix in cover["pruned"]:
            w = {int(i): Q(v) / scales[int(i)]
                 for i, v in cover["pruned"][prefix].items()}
            den = math.lcm(*(v.denominator for v in w.values()))
            ints = {i: int(v * den) for i, v in w.items()}
            g = math.gcd(*ints.values())
            return "(.excluded " + lst([f"({i},{v//g})" for i, v in ints.items()]) + ")"
        assert len(prefix) < 20
        return "(.branch " + tree(prefix + "+") + " " + tree(prefix + "-") + ")"

    source += ["def cover : Cover := " + tree(""),
               "def endpointOk (p : Pattern) : Bool :=\n"
               "  decide (0 ≤ lower low high (K.bstar.sub (score blocks p)))",
               "end Fast.Four.Data"]
    (OUT / "Data.lean").write_text("\n\n".join(source) + "\n")
    checks = OUT / "Checks"
    checks.mkdir(exist_ok=True)
    imports = []
    header = ["import Fast.Four.Data", "set_option maxRecDepth 10000",
              "set_option maxHeartbeats 0", "namespace Fast.Four.Checked"]

    def emit(name, declarations):
        imports.append("import Fast.Four.Checks." + name)
        (checks / (name + ".lean")).write_text(
            "\n\n".join(header + declarations + ["end Fast.Four.Checked"]) + "\n")

    def checked(name, expr):
        return f"theorem {name} : {expr} = true := by decide +kernel"

    emit("Base", [checked("enclosure", "enclosureOk Data.encLo Data.encHi Data.encM")] +
         [checked(f"shape{i}", f"blockShape Data.block{i}") for i in range(4)])
    emit("Cover", [checked("cover", "coverOk Data.patterns Data.cover 0 0")])
    aggregates = []

    def family(name, expressions, statement, batch=4):
        names = [f"{name}_{i}" for i in range(len(expressions))]
        for i in range(0, len(expressions), batch):
            emit(name.capitalize() + str(i // batch),
                 [checked(names[j], expressions[j])
                  for j in range(i, min(i + batch, len(expressions)))])
        chain = "true"
        for expr in reversed(expressions):
            chain = f"({expr} && {chain})"
        aggregates.append(f"theorem {name} : {statement} = true := by\n"
                          f"  change {chain} = true\n  simp only [" +
                          ", ".join(names) + ", Bool.true_and]")

    for bi, b in enumerate(cert["blocks"]):
        family(f"psd{bi}", [f"psdRow Data.low Data.high Data.block{bi} {i}"
                           for i in range(len(b["Y"]))],
               f"(List.range {len(b['Y'])}).all (psdRow Data.low Data.high Data.block{bi})")
        family(f"expanded{bi}", [f"expandedRow Data.block{bi} {i}"
                                for i in range(len(b["W"]))],
               f"(List.range {len(b['W'])}).all (expandedRow Data.block{bi})")
    # One process per score releases the kernel's large rational caches.
    family("endpoints", [f"Data.endpointOk Data.patterns[{i}]!"
                         for i in range(len(patterns))],
           "Data.patterns.toList.all Data.endpointOk", batch=1)
    (OUT / "Checked.lean").write_text("\n".join(imports) + "\n\n" +
                                     "\n\n".join(header[1:] + aggregates +
                                                  ["end Fast.Four.Checked"]) + "\n")
    print("Exported", len(patterns), "patterns,", len(imports), "kernel check modules")


if __name__ == "__main__":
    main()
