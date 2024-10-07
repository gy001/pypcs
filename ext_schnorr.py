from pypcs.curve import Fp, Fr, ec_mul, G1Point
import random

from merlin.merlin_transcript import MerlinTranscript

# (HV) Perfect Zero-Knowledge Schnorr Protocol

def setup() -> tuple[G1Point, G1Point]:
    s = Fr.rand(random.Random("pedersen-commitment-setup"))
    return G1Point.ec_gen_group1(), ec_mul(G1Point.ec_gen_group1(), s)

# Pedersen Commitment 
#  [a]

def commit(pp: tuple[G1Point, G1Point], a: Fr, r: Fr) -> G1Point:
    """
        Perfectly hiding
        Computationally binding
    """


    # print(f"a={a}")
    return ec_mul(pp[0], a) + ec_mul(pp[1], r)

def open(pp: tuple[G1Point, G1Point], cm: G1Point, a: Fr, r: Fr) -> bool:
    return cm == commit(pp, a, r)

pp = setup()

class Prover:
    sk: Fr
    r: Fr

    def __init__(self, sk: Fr):
        self.sk = sk
        self.rnd_gen = random.Random("schnorr-prover")
        self.blinder = Fr.rand(self.rnd_gen)
        self.pk = commit(pp, sk, self.blinder)

    def round1(self) -> G1Point:
        r0 = Fr.rand(self.rnd_gen)
        r1 = Fr.rand(self.rnd_gen)
        self.r = (r0, r1)
        R = commit(pp, r0, r1)
        return R

    def round3(self, c: Fr) -> tuple[Fr, Fr]:
        z0 = self.r[0] + c * self.sk
        z1 = self.r[1] + c * self.blinder
        return z0, z1

class Verifier:
    pk: G1Point
    rnd_gen: random.Random

    def __init__(self, pk: G1Point):
        self.pk = pk
        self.rnd_gen = random.Random("schnorr-verifier")

    def round2(self, R: G1Point) -> Fr:
        c = Fr.rand(self.rnd_gen)
        return c
    
    def verify(self, R: G1Point, c: Fr, z: tuple[Fr, Fr]) -> bool:
        return commit(pp, z[0], z[1]) == R + ec_mul(self.pk, c)
    

def run_schnorr(prover: Prover, verifier: Verifier) -> bool:

    R = prover.round1()
    c = verifier.round2(R)
    z = prover.round3(c)
    return verifier.verify(R, c, z)


def run_schnorr_non_interactive(prover: Prover) -> bool:

    transcript = MerlinTranscript(b"schnorr")
    transcript.append_message(b"pk", str(prover.pk).encode())

    R = prover.round1()

    transcript.append_message(b"R", str(R).encode())

    c_bytes = transcript.challenge_bytes(b"challenge", 32)
    c = Fr(int.from_bytes(c_bytes, "big"))

    z = prover.round3(c)

    print(f"len(c_bytes)={len(c_bytes)}")
    print(f"c={c}")

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
    sk = Fr(31)
    print(f"sk: {sk}")

    prover = Prover(sk)
    verifier = Verifier(prover.pk)

    print(f"protocol? : {run_schnorr(prover, verifier)}")

    print(f"run_schnorr_non_interactive(prover) : {run_schnorr_non_interactive(prover)}")

    print(f"simulator? : {simulate(prover.pk, verifier)}")

    print(f"extractor? : {extract(Prover(sk))}")