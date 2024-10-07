from pypcs.curve import Fp, Fr, ec_mul, G1Point
import random

def setup(n: int) -> list[G1Point]:
    pp = []
    rnd_gen = random.Random("vector-pedersen-setup")
    for i in range(n):
        s = Fr.rand(rnd_gen)
        pp.append(ec_mul(G1Point.ec_gen_group1(), s))
    
    return pp

def commit(pp: list[G1Point], vs: list[Fr], r: Fr) -> G1Point:
    assert len(pp) > len(vs)
    cm = G1Point.zero()
    for i in range(len(vs)):
        cm += ec_mul(pp[i], vs[i])
    return cm + ec_mul(pp[-1], r)

def open(pp: list[G1Point], cm: G1Point, vs: list[Fr], r: Fr) -> bool:
    cm2 = commit(pp, vs, r)
    return cm == cm2

pp = setup(20)

class Prover:
    ks: list[Fr]
    blinder: Fr
    r: tuple[Fr, Fr]
    cm_ks: G1Point

    def __init__(self, ks: list[Fr]):
        self.ks = ks
        self.rnd_gen = random.Random("schnorr-prover")
        self.blinder = Fr.rand(self.rnd_gen)
        self.cm_ks = commit(pp, ks, self.blinder)

    def round1(self) -> G1Point:
        rs = Fr.rands(self.rnd_gen, len(self.ks))
        rr = Fr.rand(self.rnd_gen)
        self.rs = rs
        self.rr = rr
        R = commit(pp, rs, rr)
        return R

    def round3(self, c: Fr) -> tuple[list[Fr], Fr]:
        zs = [self.rs[i] + c * self.ks[i] for i in range(len(self.ks))]
        zz = self.rr + c * self.blinder
        return zs, zz

class Verifier:
    cm_ks: G1Point
    rnd_gen: random.Random

    def __init__(self, cm: G1Point):
        self.cm_ks = cm
        self.rnd_gen = random.Random("schnorr-verifier")

    def round2(self, R: G1Point) -> Fr:
        c = Fr.rand(self.rnd_gen)
        return c
    
    def verify(self, R: G1Point, c: Fr, z: tuple[list[Fr], Fr]) -> bool:
        return commit(pp, z[0], z[1]) == R + ec_mul(self.cm_ks, c)
    

def run_schnorr(prover: Prover, verifier: Verifier) -> bool:

    R = prover.round1()
    c = verifier.round2(R)
    z = prover.round3(c)
    return verifier.verify(R, c, z)

def simulate(prover_pk: G1Point, verifier: Verifier) -> Fr:

    r = Fr(1)
    R = commit(pp, [r], r)

    st = verifier.rnd_gen.getstate()
    c = verifier.round2(R)

    rng = random.Random("schnorr-sim")
    z_star = [Fr.rand(rng) for _ in range(len(prover.ks))]
    z_star_r = Fr.rand(rng)
    Z_star = commit(pp, z_star, z_star_r)

    R_star = Z_star - ec_mul(prover_pk, c)
    verifier.rnd_gen.setstate(st)
    c_star = verifier.round2(R_star)

    assert c == c_star

    return verifier.verify(R_star, c, (z_star, z_star_r))

def extract(prover: Prover) -> Fr:
    rng = random.Random("schnorr-extract")

    R = prover.round1()
    c = Fr.rand(rng)
    zz, zr = prover.round3(c)
    c_star = Fr.rand(rng)
    z_star, z_star_r = prover.round3(c_star)
    ks = [((z_star[i] - zz[i]) / (c_star - c)) for i in range(len(prover.ks))]
    return ks

if __name__ == "__main__":
    ks = [Fr(31), Fr(32), Fr(33), Fr(34), Fr(35)]
    print(f"ks: {ks}")

    prover = Prover(ks)
    verifier = Verifier(prover.cm_ks)

    print(f"protocol? : {run_schnorr(prover, verifier)}")

    print(f"simulator? : {simulate(prover.cm_ks, verifier)}")

    print(f"extractor? : {extract(Prover(ks))}")