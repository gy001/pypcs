from pypcs.curve import Fp, Fr, ec_mul, G1Point

import random

class PedersenCommitment:
    pp: list[G1Point]

    def __init__(self, pp: list[G1Point]):
        if not isinstance(pp, list):
            raise ValueError("pp must be a list of G1Point")
        self.pp = pp

    @classmethod
    def setup(cls, n: int) -> "PedersenCommitment":
        pp = []
        rnd_gen = random.Random("vector-pedersen-setup")
        for _ in range(n):
            s = Fr.rand(rnd_gen)
            pp.append(ec_mul(G1Point.ec_gen_group1(), s))
        return cls(pp)

    def commit(self, vs: list[Fr], r: Fr) -> G1Point:
        assert len(self.pp) > len(vs)
        cm = G1Point.zero()
        for i in range(len(vs)):
            cm += ec_mul(self.pp[i], vs[i])
        return cm + ec_mul(self.pp[-1], r)

    def open(self, cm: G1Point, vs: list[Fr], r: Fr) -> bool:
        cm2 = self.commit(vs, r)
        return cm == cm2

    def commit_without_blinder(self, vs: list[Fr]) -> G1Point:
        assert len(self.pp) > len(vs)
        cm = G1Point.zero()
        for i in range(len(vs)):
            cm += ec_mul(self.pp[i], vs[i])
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
    cm = cms.commit(vs, r)
    cm_without_blinder = cms.commit_without_blinder(vs)
    assert cms.open(cm, vs, r)
    assert cms.open_without_blinder(cm_without_blinder, vs)
    print("✅ Pedersen Commitment Test Passed")

    cm2 = PedersenCommitment.commit_with_pp(cms.pp[:11], vs)
    assert PedersenCommitment.open_with_pp(cms.pp[:11], cm2, vs)
    print("✅ Pedersen Commitment with new pp Test Passed")

if __name__ == "__main__":
    test_pedersen()