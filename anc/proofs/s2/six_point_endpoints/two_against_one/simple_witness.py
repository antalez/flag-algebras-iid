"""A short rational certificate improving the draft's bound at c=8/5."""
from fractions import Fraction as Q
import json
from pathlib import Path

from search import events, exact_value


def certificate():
    c = Q(8, 5)
    support = list(map(Q, ["0", ".63", ".79", ".89", ".96", "1"]))
    masses = list(map(Q, [".440669", ".294984", ".077121", ".059048", ".059048", ".069130"]))
    assert sum(masses) == 1
    terms, slack = events(support, c)
    f = exact_value(terms, masses)
    value = f/(1-masses[0]**3)
    rho = Q(1, 1000)
    assert 2*rho < slack and c*rho < support[1]
    assert value > Q("0.4627479964")
    law = {"support_exact": list(map(str, support)), "masses_exact": list(map(str, masses)),
           "base_exact": str(f), "value_exact": str(value), "value": float(value),
           "rho_exact": str(rho), "slack_exact": str(slack)}
    return {"c": str(c), "laws": [law]}


if __name__ == "__main__":
    result = certificate()
    path = Path(__file__).parent/"results"/"simple_c8_5.json"
    path.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
