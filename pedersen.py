#!/usr/bin/env python3

# WARNING: This implementation may contain bugs and has not been audited. 
# It is only for educational purposes. DO NOT use it in production.


from pypcs.curve import Fp, Fr, ec_mul, G1Point
import random

# WARNING: 
#   1. For demonstration, we deliberately use an insecure random number 
#      generator, random.Random. To generate secure randomness, use 
#      the standard library `secrets` instead.
#        
#      See more here: https://docs.python.org/3/library/secrets.html
#
#   2. We should have used hash-to-curve to generate the base points.
#      But here we use a trusted setup for demonstration and testing purposes.
#
#      See more here: https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-hash-to-curve-11

class PedersenCommitment:
    pp: tuple[list[G1Point], G1Point]

    def __init__(self, pp: tuple[list[G1Point], G1Point]):
        vec_G, H = pp
        if not isinstance(vec_G, list):
            raise ValueError("pp.G must be a list of G1Point")
        if not isinstance(H, G1Point):
            raise ValueError("pp.H must be a G1Point")
        self.pp = pp

    # NOTE: Insecure setup, please DON'T use it in production.
    @classmethod
    def setup(cls, n: int) -> "PedersenCommitment":
        vec_G = []
        rnd_gen = random.Random("vector-pedersen-setup")
        for _ in range(n):
            s = Fr.rand(rnd_gen)
            vec_G.append(ec_mul(G1Point.ec_gen_group1(), s))
        s = Fr.rand(rnd_gen)
        H = ec_mul(G1Point.ec_gen_group1(), s)
        return cls((vec_G, H))

    def commit(self, vs: list[Fr], rng: random.Random) -> G1Point:
        assert len(self.pp[0]) > len(vs)
        assert isinstance(rng, random.Random), f"rng must be a random.Random, but got {type(rng)}"
        cm = G1Point.zero()
        r = Fr.rand(rng)
        for i in range(len(vs)):
            cm += ec_mul(self.pp[0][i], vs[i])
        return cm + ec_mul(self.pp[1], r)
    
    def commit_with_blinder(self, vs: list[Fr], r: Fr) -> G1Point:
        assert len(self.pp[0]) > len(vs)
        cm = G1Point.zero()
        for i in range(len(vs)):
            cm += ec_mul(self.pp[0][i], vs[i])
        return cm + ec_mul(self.pp[1], r)

    def open(self, cm: G1Point, vs: list[Fr], r: Fr) -> bool:
        cm2 = self.commit_with_blinder(vs, r)
        return cm == cm2

    def commit_without_blinder(self, vs: list[Fr]) -> G1Point:
        assert len(self.pp[0]) > len(vs)
        cm = G1Point.zero()
        for i in range(len(vs)):
            cm += ec_mul(self.pp[0][i], vs[i])
        return cm

    def open_without_blinder(self, cm: G1Point, vs: list[Fr]) -> bool:
        cm2 = self.commit_without_blinder(vs)
        return cm == cm2
    
    @classmethod
    def commit_with_pp(cls, new_pp: list[G1Point], vs: list[Fr]) -> G1Point:
        assert len(new_pp) >= len(vs), f"len(new_pp): {len(new_pp)} < len(vs): {len(vs)}"
        cm = G1Point.zero()
        for i in range(len(vs)):
            cm += ec_mul(new_pp[i], vs[i])
        return cm

    @classmethod
    def open_with_pp(cls, new_pp: list[G1Point], cm: G1Point, vs: list[Fr]) -> bool:
        cm2 = cls.commit_with_pp(new_pp, vs)
        return cm == cm2
    
def test_pedersen():
    cms = PedersenCommitment.setup(20)
    vs = [Fr.rand() for _ in range(10)]
    r = Fr.rand()
    cm = cms.commit_with_blinder(vs, r)
    cm_without_blinder = cms.commit_without_blinder(vs)
    assert cms.open(cm, vs, r)
    assert cms.open_without_blinder(cm_without_blinder, vs)
    print("✅ Pedersen Commitment Test Passed")

    cm2 = PedersenCommitment.commit_with_pp(cms.pp[0][:11], vs)
    assert PedersenCommitment.open_with_pp(cms.pp[0][:11], cm2, vs)
    print("✅ Pedersen Commitment with new pp Test Passed")

if __name__ == "__main__":
    test_pedersen()