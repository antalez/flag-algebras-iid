"""Exact algebraic endpoint coverage at phi, using the shared Farkas engine."""
from functools import partial
import endpoint_c4 as engine

POLY = [-1, -1, 1]
isolate = partial(engine.isolate, polynomial=POLY)
sign_at_root = partial(engine.sign_at_root, polynomial=POLY)
verify_ray = partial(engine.verify_ray, polynomial=POLY)
reconstruct = partial(engine.reconstruct, polynomial=POLY)
verify_endpoint = partial(engine.verify_endpoint, polynomial=POLY)

if __name__ == '__main__':
    engine.main(polynomial=POLY)
