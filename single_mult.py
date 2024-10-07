from pypcs.curve import Fp, Fr, ec_mul, G1Point
import random

def setup() -> tuple[G1Point, G1Point]:
    s = Fr.rand(random.Random("pedersen-commitment-setup"))
    return G1Point.ec_gen_group1(), ec_mul(G1Point.ec_gen_group1(), s)

def commit(pp: tuple[G1Point, G1Point], a: Fr, r: Fr) -> G1Point:
    # print(f"a={a}")
    return ec_mul(pp[0], a) + ec_mul(pp[1], r)

def open(pp: tuple[G1Point, G1Point], cm: G1Point, a: Fr, r: Fr) -> bool:
    return cm == commit(pp, a, r)

pp = setup()

class Prover:
    a: Fr
    b: Fr
    c: Fr
    A: G1Point
    B: G1Point
    C: G1Point

    def __init__(self, a: Fr, b: Fr, c: Fr):
        self.a = a
        self.b = b
        self.c = c
        self.rnd_gen = random.Random("schnorr-prover")
        self.a_blinder = Fr.rand(self.rnd_gen)
        self.b_blinder = Fr.rand(self.rnd_gen)
        self.c_blinder = Fr.rand(self.rnd_gen)
        self.A = commit(pp, a, self.a_blinder)
        self.B = commit(pp, b, self.b_blinder)
        self.C = commit(pp, c, self.c_blinder)

    def round1(self) -> tuple[G1Point, G1Point, G1Point]:
        ra = Fr.rand(self.rnd_gen)
        ra_r = Fr.rand(self.rnd_gen)
        rb = Fr.rand(self.rnd_gen)
        rb_r = Fr.rand(self.rnd_gen)
        rt = Fr.rand(self.rnd_gen)
        
        Ra = commit(pp, ra, ra_r)
        Rb = commit(pp, rb, rb_r)
        Rt = ec_mul(self.B, ra) + commit(pp, Fr.zero(), -rt)
        self.r = (ra, rb, rt, ra_r, rb_r)
        return (Ra, Rb, Rt)

    def round3(self, e: Fr) -> tuple[Fr, Fr, Fr, Fr, Fr]:
        za = self.r[0] + e * self.a
        zb = self.r[1] + e * self.b
        za_r = self.r[3] + e * self.a_blinder
        zb_r = self.r[4] + e * self.b_blinder
        zt_r = self.r[2] + e * (self.a * self.b_blinder - self.c_blinder)

        return (za, zb, za_r, zb_r, zt_r)

class Verifier:
    pk: G1Point
    rnd_gen: random.Random

    def __init__(self, A: G1Point, B: G1Point, C: G1Point):
        self.A = A
        self.B = B
        self.C = C
        self.rnd_gen = random.Random("schnorr-verifier")

    def round2(self, R: tuple[G1Point, G1Point, G1Point]) -> Fr:
        e = Fr.rand(self.rnd_gen)
        return e
    
    def verify(self, R: tuple[G1Point, G1Point, G1Point], e: Fr, zs: tuple[Fr, Fr, Fr, Fr, Fr]) -> bool:
        Ra = R[0]
        Rb = R[1]
        Rt = R[2]
        cond0 = commit(pp, zs[0], zs[2]) ==  ec_mul(self.A, e) + Ra 
        cond1 = commit(pp, zs[1], zs[3]) ==  ec_mul(self.B, e) + Rb 
        cond2 = ec_mul(self.B, zs[0]) ==  ec_mul(self.C, e) + Rt + commit(pp, Fr.zero(), zs[4])
        print(f"cond0: {cond0}")
        print(f"cond1: {cond1}")
        print(f"cond2: {cond2}")
        return cond0 and cond1 and cond2
    

def run_schnorr(prover: Prover, verifier: Verifier) -> bool:

    R = prover.round1()
    c = verifier.round2(R)
    z = prover.round3(c)
    return verifier.verify(R, c, z)

def simulate(prover_pk: G1Point, verifier: Verifier) -> Fr:

    r = Fr(1)
    R = commit(pp, r, r)

    st = verifier.rnd_gen.getstate()
    c = verifier.round2(R)

    rng = random.Random("schnorr-sim")
    z_star_0 = Fr.rand(rng)
    z_star_1 = Fr.rand(rng)
    Z_star = commit(pp, z_star_0, z_star_1)

    R_star = Z_star - ec_mul(prover_pk, c)
    verifier.rnd_gen.setstate(st)
    c_star = verifier.round2(R_star)

    assert c == c_star

    return verifier.verify(R_star, c, (z_star_0, z_star_1))

def extract(prover: Prover) -> Fr:
    rng = random.Random("schnorr-extract")


    R = prover.round1()
    c = Fr.rand(rng)
    z = prover.round3(c)
    c_star = Fr.rand(rng)
    z_star = prover.round3(c_star)
    sk = (z_star[0] - z[0]) / (c_star - c)
    return sk


if __name__ == "__main__":
    a = Fr(4)
    b = Fr(5)
    c = Fr(20)

    prover = Prover(a, b, c)
    verifier = Verifier(prover.A, prover.B, prover.C)

    print(f"Fr(2)={Fr(2)}")
    print(f"Fr(-2)={Fr(-2)}")

    print(f"protocol? : {run_schnorr(prover, verifier)}")

    # print(f"simulator? : {simulate(prover.pk, verifier)}")

    # print(f"extractor? : {extract(Prover(sk))}")