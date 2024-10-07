from pypcs.curve import Fp, Fr, ec_mul, G1Point
import random

# (HV) Computational Zero-Knowledge Schnorr Protocol

def commit(a: Fr) -> G1Point:
    """

       Computationally hiding
       Statistically binding
    """
    # print(f"a={a}")
    return ec_mul(G1Point.ec_gen_group1(), a)

class Prover:
    sk: Fr
    r: Fr

    def __init__(self, sk: Fr):
        self.sk = sk
        self.pk = commit(sk)
        self.rnd_gen = random.Random("schnorr-prover")

    def round1(self) -> G1Point:
        r = Fr.rand(self.rnd_gen)
        self.r = r
        R = commit(r)
        return R

    def round3(self, c: Fr) -> tuple[Fr, G1Point]:
        z = self.r + c * self.sk
        return z

class Verifier:
    pk: G1Point
    rnd_gen: random.Random

    def __init__(self, pk: G1Point):
        self.pk = pk
        self.rnd_gen = random.Random("schnorr-verifier")

    def round2(self, R: G1Point) -> Fr:
        c = Fr.rand(self.rnd_gen)
        return c
    
    def verify(self, R: G1Point, c: Fr, z: Fr) -> bool:
        """

            [z] ?= [r] + c * sk
        """
        return commit(z) == R + ec_mul(self.pk, c)
    

def run_schnorr(sk: Fr) -> bool:
    prover = Prover(sk)
    verifier = Verifier(prover.pk)

    R = prover.round1()
    c = verifier.round2(R)
    z = prover.round3(c)
    return verifier.verify(R, c, z)

def simulate(prover_pk: G1Point, verifier: Verifier) -> Fr:

    # 1 simulator does Round 1 of prover
    r = Fr(1)
    R = commit(r)

    # 2. simulator invoke Round 2 of verifier
    st = verifier.rnd_gen.getstate()
    c = verifier.round2(R)

    # 3. simulator does Round 3 of prover
    z_star = Fr.rand(random.Random("schnorr-sim"))
    Z_star = commit(z_star)

    R_star = Z_star - ec_mul(prover_pk, c)
    verifier.rnd_gen.setstate(st)
    c_star = verifier.round2(R_star)

    assert c == c_star

    return verifier.verify(R_star, c, z_star)

def extract(prover: Prover) -> Fr:
    rng = random.Random("schnorr-extract")

    R = prover.round1()
    c = Fr.rand(rng)
    z = prover.round3(c)
    c_star = Fr.rand(rng)
    z_star = prover.round3(c_star)
    sk = (z_star - z) / (c_star - c)
    return sk



if __name__ == "__main__":
    sk = Fr(31)
    print(f"sk: {sk}")
    print(f"pk: {commit(sk)}")
    print(f"?: {run_schnorr(sk)}")
    print(f"?: {simulate(commit(sk), Verifier(commit(sk)))}")
    print(f"?: {extract(Prover(sk))}")