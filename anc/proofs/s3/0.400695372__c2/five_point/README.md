# Earlier five-point four-roll certificate

These proof inputs and verifier modules were copied unchanged from
`anc/search/graph_experiment/four_roll/` to make verification independent
of the search tree. The manuscript's direct four-point certificate remains
in the parent directory; this bundle supports the retained five-point Lean route.

The certificate uses pair cutoff 2 and near-optimal-law constraints to prove
the same four-roll optimum. The JSON inputs are the complete pattern cover
and exact algebraic certificate, not numerical solver checkpoints.

Verify using Python's standard library, from the repository root:

```sh
python3 anc/proofs/s3/0.400695372__c2/five_point/verify_field_certificate.py
```

Run the corruption/regression checks from this directory:

```sh
python3 -m unittest test_field_certificate
```

`anc/lean/tools/export_five.py` reads these inputs to regenerate the existing
Lean data. `anc/lean/tools/check_five_assembly.py` reads this cover to enumerate
the finite assembly checks. Neither tool needs `anc/search/`.
